import EulerComp

def main : IO Unit :=

  let coins := [200,100,50,20,10,5,2,1]

  let res := count_sum_combinations gas 200 coins
  IO.println s!"{res}"
