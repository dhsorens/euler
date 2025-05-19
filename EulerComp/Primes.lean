import EulerComp.Global
import EulerComp.Arith

-- calculate if a natural number is prime
def is_prime_rec (n : Nat) (acc : Nat) : Bool :=
  if n = 1 || n = 0 then false else
  if n = 2 then true else
  if n % 2 = 0 then false else
  -- acc has to start at 3
  if acc < (sqrt n) + 1 then
    if n % acc = 0 then false
    else is_prime_rec n (acc + 2)
  else true

def is_prime (n : Nat) : Bool := is_prime_rec n 3

#eval is_prime 11 -- true
#eval is_prime 12 -- false
#eval is_prime 2 -- true
#eval is_prime 1 -- false
#eval is_prime 7927 -- true

-- prove is_prime to be correct
def is_prime_prop (n : Nat) : Prop := ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

theorem is_prime_correct (n : Nat) (h_nonzero : n > 0) :
  is_prime n = true ↔ is_prime_prop n := by
  constructor
  -- is_prime → is_prime_prop
  . intro h_comp
    unfold is_prime_prop
    intro m h
    induction n with
    | zero => simp at h_nonzero
    | succ n' ih =>

      sorry
  -- is_prime_prop → is_prime
  . intro h_prop

    sorry


-- find prime factors of a number, output a list
def prime_factors_rec (n k : Nat) (acc : List Nat) : List Nat :=
  if k = 0 then acc else
  if n % k = 0 && is_prime k then prime_factors_rec n (k-1) (k::acc)
  else prime_factors_rec n (k-1) acc

def prime_factors (n : Nat) : List Nat :=
  prime_factors_rec n (sqrt n + 1) []

#eval prime_factors 13195
#eval prime_factors 9

-- find the nth prime number
def nth_prime_rec (counter nth gas : Nat) : Nat :=
  if gas = 0 then 0 else
  if nth = 0 then counter - 1 else
  if is_prime counter
  then nth_prime_rec (counter + 1) (nth - 1) (gas - 1)
  else nth_prime_rec (counter + 1) nth       (gas - 1)

def nth_prime (nth : Nat) : Nat := nth_prime_rec 2 nth gas

-- find prime numbers up to a limit
def primes_up_to_rec (k : Nat) (acc : List Nat) : List Nat :=
  if k = 0 then acc else
  primes_up_to_rec (k - 1) (if is_prime k then (k :: acc) else acc)

def primes_up_to (lim : Nat) : List Nat :=
  primes_up_to_rec lim []

#eval primes_up_to 100
-- #eval primes_up_to 1000000

def primes_up_to_strict (lim : Nat) : List Nat :=
  primes_up_to_rec (lim - 1) []

#eval primes_up_to_strict 11

-- find prime numbers in a range
def primes_in_range_rec (low k : Nat) (acc : List Nat) : List Nat :=
  if k ≤ low then acc else
  primes_in_range_rec low (k - 1) (if is_prime k then (k :: acc) else acc)

def primes_in_range (low high : Nat) : List Nat :=
  primes_in_range_rec low high []

#eval primes_in_range 10 20
