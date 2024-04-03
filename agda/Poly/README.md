# Developments of System F

## Principles

* Unsolved existential variables never appear in the typing

We achive this by seperating the contexts between subtyping and typing. This could be helpful to define the contexts in declarative typing.

* We should try to avoid the subtituition (but not ideal now)

## Environment Replacement d

```
[Int -> Int/b] (a = Int, b = a -> Int)
```



