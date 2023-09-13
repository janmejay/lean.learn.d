import Mathlib.Tactic

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩


example : ∀ m n : ℕ, Even n → Even (m * n) := 
  fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  ring

example : ∀ m n : Nat, Even n → Even (m * n)  := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a]
  rw [mul_assoc]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c]
  rw [mul_assoc]
  rw [mul_comm a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- using no args -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

/- using 1 arg -/
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [<- mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp': d = a * b) : c = 0 := by
  rw [hyp]
  rw [mul_comm]
  rw [← hyp']
  rw [sub_self]

