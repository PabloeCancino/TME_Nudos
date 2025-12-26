import TMENudos.TCN_03_Matchings

open KnotTheory PerfectMatching

def check (M : PerfectMatching) : Bool :=
  decide (hasR2Pair M)

def main : IO Unit := do
  IO.println (check matching1)
  IO.println (check matching2)
  IO.println (check matching3)
  IO.println (check matching4)

#eval main
