# Developments of System F

## Principles

* Unsolved existential variables never appear in the typing

We achive this by seperating the contexts between subtyping and typing. This could be helpful to define the contexts in declarative typing.

* We should try to avoid the subtituition (but not ideal now)

## Environment Replacement

```
[Int -> Int/b] (a = Int, b = a -> Int)
```



## Examples of Decl

### `id [Int] 1`

```
T = id : forall a. a -> a
```

```
T |-0 id : forall a. a -> a     T |-(St S 0) forall a. a -> a  <: Int -> Int
------------------------------------------------------------------------- Sub
T |-(St S 0) id : Int -> Int
---------------------------------- TApp
T |-(S 0) id [Int] : Int -> Int
----------------------------------- App
T |-0 id [Int] 1 : Int
```

### `idv [Int] 1`

```
idv = /\X. (\x. x : X -> X)
```

```
--------------------------------------------------
., X = Int |- S 0 (\x. x : X -> X) : X -> X
------------------------------------------------------------------------- TAbs
. |-(St S 0) /\X. (\x. x : X -> X) : Int -> Int
------------------------------------------------- TApp
. |-(S 0) idv [Int] : Int -> Int
----------------------------------- App
. |-0 idv [Int] 1
```

### `map`

```
map = /\a. /\b. (\f. \x. f x : (a -> b) -> a -> b)

map id 1
```

### greedy gussing

-- equal constraint -- greedy is true

-- join and meet -- greedy can be false

 but my system is equal constraint

```
f x succ

f : forall a. a -> (a -> a) -> a
```

### impredicative

```
id idv
```

### Missing cases

```
(Int -> Int) -> Int <: (forall a. a -> a) -> Int
```

### Some Justificaitions

we forbid the cases

```
(/\a. (\x. x)) [Int] 1
```

since `/\a. (\x. x)` cannot infer.  

This is because it's hard to accept `(/\a. (\x. x)) [Int] 1` and reject `(/\a. (\x. x + 1)) [Int] 1`

