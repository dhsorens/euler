import EulerComp.Lists
-- for arithmetic

-- sqrt
def sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (n / 2)
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`.

  By default this well-founded recursion would be irreducible.
  This prevents use `decide` to resolve `Nat.sqrt n` for small values of `n`,
  so we mark this as `@[semireducible]`. -/
  @[semireducible] iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
  termination_by guess


-- is
def is_square (n : Nat) : Bool :=
  let sq := sqrt n
  sq^2 == n

#eval is_square 4 -- true
#eval is_square 5 -- false

-- pythagorean triples
structure triple where
  a : Nat
  b : Nat
  c : Nat
  deriving Repr

def is_pythagorean_triple (trip : triple) : Bool :=
  trip.a^2 + trip.b^2 == trip.c^2

-- takes a list of numbers and returns all pythagorean triples
def pyth_trips (candidates: List Nat) : List (triple) :=
  let as := candidates
  as.foldl
    (fun acc a =>
      let bs := candidates.filter (fun x => x > a)
      let b_trips := bs.foldl
        (fun acc b =>
          let cs := candidates.filter (fun x => x > b)
          let c_trips := cs.foldl
            (fun acc c =>
              let trip : triple := {a := a, b := b, c := c}
              if is_pythagorean_triple trip then trip :: acc
              else acc)
            []
          acc ++ c_trips)
        []
      acc ++ b_trips)
    []

#eval pyth_trips (list_range_pos 5)

-- factorial
def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else
  n * factorial (n - 1)

#eval factorial 5 -- 120
#eval factorial 0 -- 1
#eval factorial 1 -- 1
#eval factorial 10 -- 3628800
#eval factorial 100


-- divisors

-- divisors
def divisors_rec (n k : Nat) (acc : List Nat) : List Nat :=
  if k = 0 then acc else
  divisors_rec n (k - 1) (if n % k = 0 then (k :: acc) else acc)

def divisors (n : Nat) : List Nat :=
  divisors_rec n n []

def divisors_proper (n : Nat) : List Nat :=
  (divisors n).filter (fun x => x < n)

#eval divisors 15
#eval divisors_proper 15
#eval divisors 28
#eval divisors 5000000

def divisors_count_rec (n k acc : Nat) : Nat :=
  if k = 0 then acc else
  divisors_count_rec n (k - 1) (if n % k = 0 then acc + 1 else acc)

def divisors_count (n : Nat) : Nat :=
  divisors_count_rec n n 0

#eval divisors_count 15
#eval divisors_count 28


-- amicable numbers
def d (n : Nat) : Nat :=
  divisors_proper n |> List.sum

#eval d 220 -- 284
#eval d 284 -- 220

def are_amicable (n m : Nat) : Bool :=
  d n == m && d m == n && n != m

#eval are_amicable 220 284 -- true


-- deficient and abundant sums
def is_abundant (n : Nat) : Bool :=
  d n > n

def is_perfect (n : Nat) : Bool :=
  d n == n

def is_deficient (n : Nat) : Bool :=
  d n < n

--
def possible_sums (l1 l2 : List Nat) : List Nat :=
  l1.foldl
    (fun acc x =>
      l2.foldl
        (fun acc y => (x + y) :: acc)
        acc)
    []

#eval possible_sums [1, 2, 3] [4, 5, 6]
