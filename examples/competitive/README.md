# Competitive Programming Examples in Once

Classic problems, written the way Once writes algorithms: as folds over data, not loops. Once has no
strings yet, so each program reports its answer as its exit code.

| File | Problem | Exit code |
|---|---|---|
| `fizzbuzz.once` | How many of 1..15 print Fizz, Buzz or FizzBuzz | 7 |

```bash
once build examples/competitive/fizzbuzz.once -o fizzbuzz
./fizzbuzz; echo $?
```

## Once's Approach to Algorithms

Once is a categorical language: computation is composition of morphisms rather than statements.

### Branching
There is no `if-then-else`. A comparison is a `Bool = Unit + Unit`, and `case` takes it apart:
```once
bit : Unit + Unit -> Int
bit = case no yes          -- no _ = 0, yes _ = 1

hit i = bit (i % 3 == 0) + bit (i % 5 == 0) - bit (i % 15 == 0)
```

### Recursion
There is no general recursion. Data is an initial algebra (`Mu`) and is consumed by its fold (`cata`),
which always terminates:
```once
-- Natural numbers: Mu (K Unit + Id)
zero : Mu (K Unit + Id)
zero = In (inl unit)

suc : Mu (K Unit + Id) -> Mu (K Unit + Id)
suc n = In (inr n)

-- A fold: one case for zero, one for a successor
count : Mu (K Unit + Id) -> Int * Int
count = cata (case start step)
```

### No Mutation
All computation is pure: values flow through composition and are never modified in place.
