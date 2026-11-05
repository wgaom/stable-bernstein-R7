import Mathlib.Data.Rat.Defs

namespace R7

structure Parameters where
  m11 : ℚ
  m12 : ℚ
  m22 : ℚ
  c3 : ℚ
  c4 : ℚ
  c6 : ℚ
  c7 : ℚ
  c8 : ℚ
  c10 : ℚ
  c11 : ℚ
  c12 : ℚ
  c13 : ℚ
  c14 : ℚ
  deriving DecidableEq

def terminalParameters : Parameters :=
  { m11 := (0), m12 := (0), m22 := (151/25), c3 := (267/100), c4 := (0), c6 := (13/25), c7 := (-209/50), c8 := (0), c10 := (-5/4), c11 := (37/100), c12 := (99/50), c13 := (0), c14 := (0) }

end R7
