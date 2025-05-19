import EulerComp.Global

-- generate the Fibonacci sequence up to `limit`
def fib_list_rec (limit gas : Nat) (acc : List Nat) : List Nat :=
  if gas = 0 then [0] else -- for termination
  match acc with
  | x :: y :: xs =>
    let z := x + y
    if z <= limit then fib_list_rec limit (gas - 1) (z :: acc)
    else acc
  | _ => acc

def fib_list (limit : Nat) : List Nat :=
  fib_list_rec limit gas [2, 1]

-- generate triangular numbers as a list
def triangle_list_rec (counter : Nat) (acc : List Nat) : List Nat :=
  if counter ≤ 1 then acc else
  triangle_list_rec (counter - 1) ((List.range counter).sum :: acc)

def triangle_list (counter : Nat) : List Nat :=
  triangle_list_rec counter []

#eval List.range 10
#eval triangle_list 10

-- generate the nth triangular number
def nth_triangular_num (nth : Nat) : Nat :=
  (List.range (nth + 1)).sum

#eval nth_triangular_num 3
#eval nth_triangular_num 10


-- Collatz sequence
def collatz_rec (n gas : Nat) : Nat :=
  if gas = 0 then 0 else
  if n = 1 then n else
  let next :=
    if n % 2 == 0 then n / 2
    else 3 * n + 1
  collatz_rec next (gas - 1)

def collatz (n : Nat) : Nat :=
  collatz_rec n gas

#eval collatz 200

-- collatz sequence length
def collatz_length_rec (n gas acc : Nat) : Option Nat :=
  if gas = 0 then none else
  if n = 1 then some acc else
  let next :=
    if n % 2 == 0 then n / 2
    else 3 * n + 1
  collatz_length_rec next (gas - 1) (acc + 1)

def collatz_length (n : Nat) : Option Nat :=
  collatz_length_rec n gas 1

#eval collatz_length 13 -- 10
#eval collatz_length 1 -- 1

-- pythagorean triplet
