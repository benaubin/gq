# async_dataloader

Powerful tool for avoiding N+1 queries using async/await, based on the DataLoader pattern.

data_loader batches loads which occur during a single "poll" - no artifical delay required.

Design inspired by https://github.com/exAspArk/batch-loader and https://github.com/graphql/dataloader