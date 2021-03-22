//! Powerful for avoiding N+1 queries with async/await, based on the DataLoader pattern.
//!
//! data_loader batches loads which occur during a single "poll", without requiring an artificial delay.
//!
//! Design inspired by https://github.com/exAspArk/batch-loader and https://github.com/graphql/dataloader
//!
//! # Usage
//!
//! ```
//! use async_dataloader::{def_batch_loader, batched};
//!
//! def_batch_loader! {
//!     pub async fn loader(inputs: u64) -> String {
//!         inputs.map(|input| {
//!              input.to_string()
//!         })
//!     }
//! }
//!
//! # futures::executor::block_on(async {
//! batched(async {
//!     assert_eq!(*loader(1).await, "1".to_owned());
//! }).await
//! # })
//! ```


use std::{any::{Any, TypeId}, cell::{RefCell, RefMut}, collections::{HashMap}, future::Future, marker::PhantomData, pin::Pin, rc::Rc, task::{Poll}, unreachable};

use futures::{FutureExt};
use futures::channel::oneshot;
use slab::Slab;


/// Allows using batch loaders from within the passed future.
pub fn batched<F: Future>(fut: F) -> Batched<F> {
    Batched {
        fut,
        batch_futures: Slab::new(),
        ctx: Rc::new(RefCell::new(BatchContext {
            accumulating: HashMap::new(),
            postpone_loading: 0,
            user_ctx: HashMap::new()
        }))
    }
}

type ResultSender = futures::channel::oneshot::Sender<Box<dyn Any>>;

#[doc(hidden)]
pub mod __internal {
    use std::{future::Future, pin::Pin, task::Poll};

    use super::{ResultSender};

    pub struct LoadBatch<Outputs: Iterator, F: Future<Output = Outputs>> {
        pub fut: F,
        pub result_senders: Vec<ResultSender>
    }

    impl<Outputs: Iterator, F: Future<Output = Outputs>> Future for LoadBatch<Outputs, F> where Outputs::Item: 'static {
        type Output = ();

        fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
            let fut;
            let senders;

            unsafe {
                let this = self.get_unchecked_mut();

                senders = &mut this.result_senders;
                fut = Pin::new_unchecked(&mut this.fut);
            };

            // check if no one cares for the results of this batch
            if senders.iter().all(|res| res.is_canceled() ) { return Poll::Ready(()) }

            match fut.poll(cx) {
                Poll::Ready(outputs) => {
                    for (output, sender) in outputs.zip(senders.drain(..)) {
                        let _ = sender.send(Box::new(output));
                    }
                    Poll::Ready(())
                }
                Poll::Pending => Poll::Pending
            }
        }
    }
}

/// Define a batch loader
#[macro_export]
macro_rules! def_batch_loader {
    (
        $(#[$attr:meta])*
        $vis:vis async fn $name:ident($inputs:ident: $input_ty:ty) -> $output_ty:ty $block:block
    ) => {
        $(#[$attr])* $vis fn $name( input: $input_ty ) -> $crate::BatchLoad::<$input_ty, $output_ty> {
            // A type-erased load function, which conforms to LoadFn
            fn load_batch( batch: $crate::Batch ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()>>> {
                // The user-provided batch loader
                #[inline(always)]
                async fn loader(
                    $inputs: impl Iterator<Item = Box<$input_ty>>
                ) -> impl Iterator<Item = $output_ty> $block

                // Downcast inputs to the expected type.
                let inputs = batch.inputs.into_iter().map(|input| {
                    // It should be impossible to pass in an input of the wrong type through the public API
                    input.downcast::<$input_ty>().unwrap()
                });

                let fut = $crate::__internal::LoadBatch {
                    fut: loader(inputs),
                    result_senders: batch.result_senders
                };

                // Call load_batch, then return the future as a Pin<Box<dyn Future<Output = ()>>>
                Box::pin(fut)
            }

            $crate::BatchLoad::New {
                load_fn: load_batch,
                input: Box::new(input),
                phantom: std::marker::PhantomData
            }
        }
    };
}

type LoadFn = fn ( Batch ) -> Pin<Box<dyn Future<Output = ()>>>;

/// Context provided when executing within a batched() future.
pub struct BatchContext {
    accumulating: HashMap<LoadFn, Batch>,

    postpone_loading: usize,

    user_ctx: HashMap<TypeId, Box<dyn Any>>
}

impl BatchContext {
    /// Provide context of a given type. Exactly one value per type may be stored.
    pub fn set_ctx(&mut self, val: Box<dyn Any>) -> Option<Box<dyn Any>> {
        self.user_ctx.insert((*val).type_id(), val)
    }
    /// Get context of a given type. Exactly one value per type may be stored.
    pub fn get_ctx<T: Any>(&self) -> Option<&T> {
        self.user_ctx.get(&TypeId::of::<T>()).map(|a| a.downcast_ref().unwrap())
    }
    /// Get context of a given type. Exactly one value per type may be stored.
    pub fn mut_ctx<'a, T: Any>(&'a mut self) -> Option<&'a mut T> {
        self.user_ctx.get_mut(&TypeId::of::<T>()).map(|a| a.downcast_mut().unwrap())
    }
}

thread_local! {
    static BATCH_CONTEXT: RefCell<Option<Rc<RefCell<BatchContext>>>> = RefCell::new(None);
}

// Batched inputs and result senders
#[doc(hidden)]
pub struct Batch {
    pub inputs: Vec<Box<dyn Any>>,
    pub result_senders: Vec<ResultSender>
}

impl Batch {
    fn empty() -> Self {
        Batch { inputs: vec![], result_senders: vec![] }
    }
    fn push(&mut self, input: Box<dyn Any>, result: ResultSender) {
        self.inputs.push(input);
        self.result_senders.push(result);
    }
}

/// Future returned by a batch loader
pub enum BatchLoad<Input, Output: ?Sized> {
    New {
        load_fn: LoadFn,
        input: Box<Input>,
        phantom: PhantomData<Box<Output>>
    },
    Pending(oneshot::Receiver<Box<dyn Any>>)
}

impl<Input: 'static, Output: ?Sized> BatchLoad<Input, Output> {
    /// Schedules this input to be loaded within the current batch context.
    ///
    /// Rust futures are lazy, meaning they have do nothing until polled.
    /// Calling this method will cause the load to be added to the next batch,
    /// even if it the future is not polled until later.
    pub fn schedule(&mut self) {
        if let Self::New {..} = self {
            let (tx, rx) = futures::channel::oneshot::channel();

            match std::mem::replace(self, BatchLoad::Pending(rx)) {
                Self::New { load_fn, input, .. } => {
                    with_batch_ctx(|ctx| {
                        let batch = ctx.accumulating.entry(load_fn).or_insert(Batch::empty());

                        batch.push(input, tx);
                    });
                },
                _ => unreachable!()
            };
        }
    }
}

impl<Input: 'static, Output: 'static> Future for BatchLoad<Input, Output> {
    type Output = Box<Output>;

    #[track_caller]
    #[inline]
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();

        if let Self::New {..} = this {
            this.schedule();
        }

        let rx = if let Self::Pending(rx) = this { rx } else { unreachable!() };

        let poll = rx.poll_unpin(cx).map(|res| res.expect("Batch loading context was cancelled"));

        poll.map(|val| {
            val.downcast().unwrap()
        })
    }
}

/// A Future which provides a BatchContext to its child while executing
pub struct Batched<F: Future> {
    fut: F,

    ctx: Rc<RefCell<BatchContext>>,

    batch_futures: Slab<Pin<Box<dyn Future<Output = ()>>>>
}

impl<F: Future> Batched<F> {
    /// Access the BatchContext from outside of async execution
    pub fn ctx<'a>(&'a mut self) -> RefMut<'a, BatchContext> {
        self.ctx.borrow_mut()
    }
}

/// Provides the batch context through thread local storage
#[inline]
fn provide_batch_ctx<T>(ctx: Rc<RefCell<BatchContext>>, cb: impl FnOnce() -> T) -> T {
    let existing_ctx = BATCH_CONTEXT.with(|cell| {
        cell.replace(Some(ctx))
    });

    let val = (cb)();

    BATCH_CONTEXT.with(|cell| {
        cell.replace(existing_ctx)
    });

    val
}

/// Retrieves the batch context from thread local storage
pub fn with_batch_ctx<T>(cb: impl FnOnce(&mut BatchContext) -> T) -> T {
    BATCH_CONTEXT.with(|cell| {
        let ctx = cell.borrow();
        let ctx = ctx.as_ref().expect("Tried to call a batched loader outside of a batching context.");
        let mut ctx = (&*ctx).borrow_mut();
        cb(&mut ctx)
    })
}


#[doc(hidden)]
pub struct DelayGuard<'a>( PhantomData<Rc<RefCell<&'a ()>>> );

impl<'a> Drop for DelayGuard<'a> {
    fn drop(&mut self) {
        with_batch_ctx(|ctx| {
            ctx.postpone_loading -= 1;
        });
    }
}

/// Provides a guard which prevents loading new batches until dropped.
///
/// ```
/// # use async_dataloader::{*};
/// # use futures::FutureExt;
/// #
/// # futures::executor::block_on(async {
/// #
/// #
/// # async fn yield_now() {
/// #     struct YieldNow {
/// #         yielded: bool,
/// #     }
/// #
/// #     impl std::future::Future for YieldNow {
/// #         type Output = ();
/// #         fn poll(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
/// #             if self.yielded {
/// #                 std::task::Poll::Ready(())
/// #             } else {
/// #                 cx.waker().wake_by_ref();
/// #                 self.yielded = true;
/// #                 std::task::Poll::Pending
/// #             }
/// #         }
/// #     }
/// #
/// #     YieldNow { yielded: false }.await;
/// # }
///
/// def_batch_loader! {
///     pub async fn loader(inputs: u64) -> (Vec<u64>, String) {
///         let inputs: Vec<_> = inputs.map(|a| *a).collect();
///         let inputs_copy = inputs.clone();
///
///         inputs.into_iter().map(move |input| {
///             (inputs_copy.clone(), input.to_string())
///         })
///     }
/// }
///
/// batched(async {
///     let mut one = loader(1);
///     let mut two = loader(2);
///     let mut three = loader(3);
///
///     one.schedule();
///
///     // yielding without delay_loading_batches will cause the batch to load
///     yield_now().await;
///
///     assert_eq!(one.await, Box::new((vec![1], "1".to_owned())));
///
///     // delay_loading_batches enables accumulating batches across yields
///     let guard = delay_loading_batches();
///     two.schedule();
///     yield_now().await;
///     drop(guard);
/// 
///     let three = three.await;
/// 
///     assert_eq!(three, Box::new((vec![2, 3], "3".to_owned())));
/// }).await;
/// # });
/// ```
/// ## Panics
///
/// Must be called from within a batched() context.
pub fn delay_loading_batches<'a>() -> DelayGuard<'a> {
    with_batch_ctx(|ctx| {
        ctx.postpone_loading += 1;
    });
    DelayGuard(PhantomData)
}

impl<F: Future> Drop for Batched<F> {
    fn drop(&mut self) {
        provide_batch_ctx(self.ctx.clone(), move || {
            let Self { .. } = self;
        });
    }
}

impl<F: Future> Future for Batched<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
        let fut;
        let batch_futures;
        let ctx;

        unsafe {
            let this = self.get_unchecked_mut();

            batch_futures = &mut this.batch_futures;
            fut = Pin::new_unchecked(&mut this.fut);
            ctx = &this.ctx;
        };

        let poll = provide_batch_ctx(ctx.clone(), || {
            let poll = fut.poll(cx);

            let mut ready_futures = vec![];
            
            for (idx, batch_fut) in batch_futures.iter_mut() {
                match batch_fut.as_mut().poll(cx) {
                    Poll::Ready(_) => ready_futures.push(idx),
                    Poll::Pending => { }
                }
            }

            for idx in ready_futures {
                batch_futures.remove(idx);
            }

            poll
        });

        loop {
            let batches = {
                let mut ctx = (**ctx).borrow_mut();

                if ctx.accumulating.is_empty() { break }

                if ctx.postpone_loading > 0 { break }

                std::mem::replace(&mut ctx.accumulating, HashMap::new())
            };

            provide_batch_ctx(ctx.clone(), || {
                for (loader, batch) in batches.into_iter() {
                    let mut fut = (loader)(batch);

                    if let Poll::Pending = fut.as_mut().poll(cx) {
                        batch_futures.insert(fut);
                    }
                }
            })
        }

        match poll {
            Poll::Ready(val) if batch_futures.is_empty() => {
                Poll::Ready(val)
            },
            _ => Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests {
    async fn yield_now() {
        struct YieldNow {
            yielded: bool,
        }

        impl std::future::Future for YieldNow {
            type Output = ();
            fn poll(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
                if self.yielded {
                    std::task::Poll::Ready(())
                } else {
                    cx.waker().wake_by_ref();
                    self.yielded = true;
                    std::task::Poll::Pending
                }
            }
        }

        YieldNow { yielded: false }.await;
    }

    use super::{batched, def_batch_loader, delay_loading_batches};
    use futures::{FutureExt};

    def_batch_loader! {
        /// Hello there!
        pub async fn load_foobar_batched(inputs: u64) -> (Vec<u64>, String) {
            let inputs: Vec<_> = inputs.map(|a| *a).collect();
            let inputs_copy = inputs.clone();

            yield_now().await;

            inputs.into_iter().map(move |input| {
                (inputs_copy.clone(), input.to_string())
            })
        }
    }

    #[test]
    fn test() {
        futures::executor::block_on(async {
            batched(async {
                let fifty_four = load_foobar_batched(54).fuse();
                let thirty_two = load_foobar_batched(32).fuse();

                futures::pin_mut!(fifty_four, thirty_two);

                futures::select_biased! {
                    tt = thirty_two => {
                        assert_eq!(tt, Box::new((vec![32, 54], "32".to_owned())));
                    },
                    ff = fifty_four => {
                        assert_eq!(ff, Box::new((vec![32, 54], "54".to_owned())));
                    }
                }
            }).await;
        });
    }

    #[test]
    fn test_schedule() {
        futures::executor::block_on(async {
            batched(async {
                assert_eq!(load_foobar_batched(12).await, Box::new((vec![12], "12".to_owned())));

                let mut fifty_four = load_foobar_batched(54);
                let thirty_two = load_foobar_batched(32);
                
                fifty_four.schedule();

                assert_eq!(thirty_two.await, Box::new((vec![54, 32], "32".to_owned())));
                assert_eq!(fifty_four.await, Box::new((vec![54, 32], "54".to_owned())));
            }).await;
        });
    }


    #[test]
    fn test_ctx() {
        futures::executor::block_on(async {
            struct Count(usize);

            def_batch_loader! {
                pub async fn counter(inputs: &'static str) -> (&'static str, usize) {
                    inputs.map(|input| {
                        let count = super::with_batch_ctx(|ctx| {
                            let count = ctx.mut_ctx::<Count>().unwrap();

                            count.0 += 1;

                            count.0
                        });

                        (*input, count)
                    })
                }
            }

            let mut scope = batched(async {
                assert_eq!( counter("hello").await, Box::new(("hello", 1)) );
                assert_eq!( counter("hello there").await, Box::new(("hello there", 2)) );
            });
            
            scope.ctx().set_ctx(Box::new(Count(0)));

            scope.await;
        });
    }

    #[test]
    fn test_drop_delay() {
        futures::executor::block_on(async {
            batched(async {
                let one = load_foobar_batched(1).fuse();

                futures::pin_mut!(one);

                futures::select_biased! {
                    one = one => {
                        assert_eq!(one, Box::new((vec![1], "1".to_owned())));
                    }
                }

                pub struct PendingOnce {
                    is_ready: bool,
                }

                impl std::future::Future for PendingOnce {
                    type Output = ();
                    fn poll(mut self: std::pin::Pin<&mut Self>, _: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
                        if self.is_ready {
                            std::task::Poll::Ready(())
                        } else {
                            self.is_ready = true;
                            std::task::Poll::Pending
                        }
                    }
                }

                let _ = delay_loading_batches();
            }).await;
        });
    }
}