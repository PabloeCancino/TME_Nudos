import Mathlib.Data.ZMod.Basic

example (h : (0 : ZMod 6) = 1) : False := by
  cases h

example (h : (0 : ZMod 6) = 1) : False := by
  contradiction

example (h : (0 : ZMod 6) = 1) : False := by
  decide
