import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MilBook.Common

#check TopologicalSpace

open Nat

#check 2 + 2

def f (x: ℕ) := 
  x + 3

/-
f (x : ℕ) : ℕ
-/
#check f

/-
2 + 2 = 4 : Prop
-/
#check 2 + 2 = 4


def FermatLastTheorem := 
  ∀ x y z n : ℕ, 
    n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

theorem easy : 2 + 2 = 4 := 
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard


