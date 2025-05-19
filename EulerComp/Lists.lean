import EulerComp.Global

-- list range, positives only
def list_range_pos (n : Nat) : List Nat :=
  (List.range n).map (fun x => x + 1)

-- sort a list of natural numbers
def nat_sort_up (l : List Nat) : List Nat :=
  List.mergeSort l (fun (x y : Nat) => x ≤ y)

def nat_sort_down (l : List Nat) : List Nat :=
  List.mergeSort l (fun (x y : Nat) => x ≥ y)

#eval nat_sort_up [3, 2, 1, 4, 5]
#eval nat_sort_down [3, 2, 1, 4, 5]

-- max, min
def nat_max (l : List Nat) : Nat :=
  l.foldl (fun acc x => if x > acc then x else acc) 0

#eval nat_max [1, 3, 2, 10, 10, 11, 1, 22, 1]

-- palindromes
def is_palindrome (n : Nat) : Bool :=
  let str := toString n
  str.toList == str.toList.reverse

#eval is_palindrome 121 -- true
#eval is_palindrome 123 -- false
#eval is_palindrome 12321 -- true
#eval is_palindrome 1234321 -- true
#eval is_palindrome 123456 -- false

def testing (l : List Nat) : Nat :=
  l.foldl (fun acc x => acc + x) 0
#eval testing [1, 2, 3, 4, 5] -- 15

-- find the largest palindrome from products in a list
def largest_palindrome (l : List Nat) : Nat :=
  l.foldl
    (fun acc x =>
      let inner := l.foldl
        (fun acc y =>
          let prod := x * y
          if is_palindrome prod then
            if prod > acc then prod else acc
          else acc)
        0
      if inner > acc then inner else acc)
    0

#eval largest_palindrome [1, 2, 3, 4, 5] -- 0

-- given a list of numbers (strings), find the largest n adjacent product
def num_to_digs (n : Nat) : List Nat :=
  let str := toString n
  str.toList.map (fun x => x.toString.toInt!.toNat)

def sum_of_digits (n : Nat) : Nat := (num_to_digs n).sum

def largest_adj_prod_rec (l : List Nat) (acc gas : Nat) : Nat :=
  if gas = 0 then acc else
  match l with
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: _ =>
    let prod := a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13
    if prod > acc
    then largest_adj_prod_rec (l.tail) prod (gas - 1)
    else largest_adj_prod_rec (l.tail) acc  (gas - 1)
  | _ => acc

def largest_adj_prod (n : Nat) : Nat :=
  let nats := num_to_digs n
  largest_adj_prod_rec nats 0 gas

-- grid arithmetic

-- row, column (start counting at zero)
def col_get (l : List Nat) (index : Nat) : Option Nat := do
  if index = 0 then l.head? else
  let tl ← l.tail?
  col_get tl (index - 1)

def row_get (rows : List (List Nat)) (row : Nat) : Option (List Nat) := do
  if row = 0 then rows.head? else
  let tl ← rows.tail?
  row_get tl (row - 1)

def grid_get (grid : List (List Nat)) (row col : Nat) : Option Nat := do
  let row_res ← row_get grid row
  col_get row_res col

-- moving in a grid, collect the product
inductive GridDirection where
  | Right
  | Down
  | RightDown
  | LeftDown

def grid_accum_rect (grid : List (List Nat)) (row col q accum : Nat)
  (dir : GridDirection) : Option Nat := do
  if q = 0 then some accum else
  let x ← grid_get grid row col
  match dir with
  | .Right =>     grid_accum_rect grid row (col + 1) (q - 1) (accum * x) dir
  | .Down =>      grid_accum_rect grid (row + 1) col (q - 1) (accum * x) dir
  | .RightDown => grid_accum_rect grid (row + 1) (col + 1) (q - 1) (accum * x) dir
  | .LeftDown =>  grid_accum_rect grid (row + 1) (col - 1) (q - 1) (accum * x) dir

def accum_right (grid : List (List Nat)) (row col qty_accum : Nat) : Option Nat := do
  grid_accum_rect grid row col qty_accum 1 .Right

def accum_down (grid : List (List Nat)) (row col qty_accum : Nat) : Option Nat := do
  grid_accum_rect grid row col qty_accum 1 .Down

def accum_down_right (grid : List (List Nat)) (row col qty_accum : Nat) : Option Nat := do
  grid_accum_rect grid row col qty_accum 1 .RightDown

def accum_down_left (grid : List (List Nat)) (row col qty_accum : Nat) : Option Nat := do
  grid_accum_rect grid row col qty_accum 1 .LeftDown

--
def grid_accum (grid : List (List Nat)) (row col qty_accum : Nat) : Option Nat := do
  let right ← accum_right grid row col qty_accum
  let down ← accum_down grid row col qty_accum
  let down_right ← accum_down_right grid row col qty_accum
  let down_left ← accum_down_left grid row col qty_accum
  nat_max [right, down, down_right, down_left]

def grid_accum_exact (grid : List (List Nat)) (row col qty_accum : Nat) : Nat :=
  match grid_accum grid row col qty_accum with | some res => res | none => 0

-- grid_indices : generate a grid of size n x m whose entries are indices
structure grid_index where
  row : Nat
  col : Nat
  deriving Repr

def grid_of_indices (r c : Nat) : List (List grid_index) :=
  let rows := List.range r
  let cols := List.range c
  rows.map (fun r => cols.map (fun c => {row := r, col := c}))

def grid_indices (r c : Nat) : List grid_index :=
  (grid_of_indices r c).flatten

#eval grid_of_indices 4 1
#eval grid_indices 5 5

def grid_to_indices_rect (r : Nat)
  (grid : List (List Nat)) (acc : List (List grid_index)) : List (List grid_index) :=
  match grid with
  | [] => acc
  | row :: rows =>
    let cols := List.range (row.length)
    let indices := cols.map (fun c => {row := r, col := c})
    let new_acc := acc ++ [indices]
    grid_to_indices_rect (r + 1) rows new_acc

def grid_to_indices (grid : List (List Nat)) : List (List grid_index) :=
  grid_to_indices_rect 0 grid []

--
def grid_iter (grid : List (List Nat)) (f : (List (List Nat)) → Nat → Nat → Nat → Nat) (q : Nat) :=
  let r := grid.length
  let c := grid.head!.length
  let indices := grid_indices r c
  indices.foldl
    (fun acc index => let res := f grid index.row index.col q
      if res > acc then res else acc)
    0

-- lattice
-- def counting_routes


-- triangle grids
def tri_reachable (i : grid_index) : List grid_index :=
  let r1 := {row := i.row + 1, col := i.col}
  let r2 := {row := i.row + 1, col := i.col + 1}
  [r1, r2]

-- traverse a triangle grid
-- def tri_traverse_rect (i : grid_index) (grid : List (List Nat)) (acc : Nat) : Option Nat := do
--   let this ← grid_get grid i.row i.col
--   let new_acc := acc + this
--   --
