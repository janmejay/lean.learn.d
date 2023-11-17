-- Propositions and Proofs (Ch. 3)

variable (p q r : Prop)

-- fool around
example : (p → q) → ¬q → ¬p :=
  fun (hpq: p → q) (hnq: ¬q) =>
    fun (hp: p) => show False from (hnq (hpq hp))

example: p → ¬p → q :=
  fun (hp: p) (hnp: ¬p) => False.elim (hnp hp)

example: p → ¬p → q :=
  fun (hp: p) (hnp: ¬p) => absurd hp hnp

example: ¬p → q → (q → p) → r :=
  fun (hnp: ¬p) (hq: q) (hqp: q → p) =>
    absurd (hqp hq) hnp

-- 1
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (h : p ∧ q) => ⟨h.right, h.left⟩)
    (fun (h : q ∧ p) => ⟨h.right, h.left⟩)

-- 2
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (h : p ∨ q) =>
      (Or.elim h
        (fun (hp : p) => Or.inr hp)
        (fun (hq : q) => Or.inl hq)))
    (fun (h : q ∨ p) =>
      (Or.elim h
        (fun (hq : q) => Or.inr hq)
        (fun (hp : p) => Or.inl hp)))

-- 3
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (h : (p ∧ q) ∧ r) => ⟨h.left.left, ⟨ h.left.right, h.right⟩⟩)
    (fun (h : p ∧ (q ∧ r)) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)


-- 4
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h =>
      Or.elim h
        (fun hpq =>
          Or.elim hpq
            (fun hp => Or.inl hp)
            (fun hq => Or.inr (Or.inl hq)))
        (fun hr => Or.inr (Or.inr hr)))
    (fun h =>
      Or.elim h
        (fun hp => Or.inl (Or.inl hp))
        (fun hqr =>
          Or.elim hqr
            (fun hq => Or.inl (Or.inr hq))
            (fun hr => Or.inr hr)))

-- 5
example: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun (h: (p ∧ (q ∨ r))) =>
      Or.elim h.right
        (fun (hq: q) => Or.inl ⟨h.left, hq⟩)
        (fun (hr: r) => Or.inr ⟨h.left, hr⟩))
    (fun (h: (p ∧ q) ∨ (p ∧ r)) =>
      Or.elim h
        (fun (hpq: (p ∧ q)) => ⟨hpq.left, Or.inl hpq.right⟩)
        (fun (hpr: (p ∧ r)) => ⟨hpr.left, Or.inr hpr.right⟩))

-- 6
example: p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
    (fun (h: (p ∨ (q ∧ r))) =>
      Or.elim h
        (fun (hp: p) => ⟨Or.inl hp, Or.inl hp⟩)
        (fun (hqr: (q ∧ r)) => ⟨Or.inr hqr.left, Or.inr hqr.right⟩)),
    (fun (h: (p ∨ q) ∧ (p ∨ r)) =>
      Or.elim h.left
        (fun (hp: p) => Or.inl hp)
        (fun (hq: q) =>
          Or.elim h.right
            Or.inl
            (fun (hr : r) => Or.inr ⟨hq, hr⟩)))⟩


-- 7
example: (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    (fun (hpqr: (p → q → r)) (hpq: (p ∧ q)) =>
      hpqr hpq.left hpq.right),
    (fun (hpqr: (p ∧ q → r)) =>
      (fun (hp: p) (hq: q) => hpqr ⟨hp, hq⟩))⟩

-- 8
example: ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    (fun (hpq₂r: (p ∨ q → r)) =>
      ⟨
        (fun (hp: p) => hpq₂r (Or.inl hp)),
        (fun (hq : q) => hpq₂r (Or.inr hq))⟩),
    (fun (h: (p → r) ∧ (q → r)) (hpq: p ∨ q) =>
      Or.elim hpq h.left h.right)⟩

-- 9
example: ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    (fun (hnpq: ¬(p ∨ q)) =>
      ⟨
        (fun (hp: p) => show False from hnpq (Or.inl hp)),
        (fun (hq: q) => show False from hnpq (Or.inr hq))⟩),
    (fun (hnpnq: (¬p ∧ ¬q)) =>
      (fun (hpq: p ∨ q) =>
        Or.elim hpq
          (fun (hp: p) => show False from hnpnq.left hp)
          (fun (hq: q) => show False from hnpnq.right hq)))⟩

-- 10
example: ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun (h: ¬p ∨ ¬q) =>
    Or.elim h
      (fun (hnp: ¬p) =>
        fun (hn: p ∧ q) => show False from (hnp hn.left))
      (fun (hnq: ¬q) =>
        fun (hn: p ∧ q) => show False from (hnq hn.right)))

-- 11
example: ¬(p ∧ ¬p) :=
  fun (h: p ∧ ¬p) => show False from h.right h.left

-- 12
example: p ∧ ¬q → ¬(p → q) :=
  fun (h: p ∧ ¬q) =>
    fun (hn: p → q) => show False from h.right (hn h.left)

-- 13
example: ¬p → (p -> q) :=
  fun (hnp: ¬p) =>
    fun (hp: p) => absurd hp hnp

-- 14
example: (¬p ∨ q) → (p → q) :=
  fun (h: ¬p ∨ q) =>
    fun (hp: p) =>
      Or.elim h
        (fun (hnp: ¬p) => absurd hp hnp)
        id

-- 15
example: (p ∨ False) ↔ p :=
  ⟨
    (fun (h: p ∨ False) =>
      Or.elim h
        id
        False.elim),
    (fun (hp: p) => Or.inl hp)⟩

-- 16
example: (p ∧ False) ↔ False :=
  ⟨
    fun (h: p ∧ False) => h.right,
    False.elim⟩

-- 17
example: (p → q) → (¬q → ¬p) :=
  fun (hpq: p -> q) (hnq: ¬q) =>
    (fun (hp: p) => show False from hnq (hpq hp))

-- Classical exercises

open Classical

theorem dne {p : Prop} (h: ¬¬p) : p :=
  Or.elim (em p)
    id
    (fun (hnp: ¬p) => absurd hnp h)

-- Classical 1
theorem not_or {x y: Prop} (hnx: ¬x) (hny: ¬y) : ¬(x ∨ y) :=
  (fun (h: x ∨ y) =>
    Or.elim h
      (fun (hx: x) => absurd hx hnx)
      (fun (hy: y) => absurd hy hny))

example: (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun (h: p → (q ∨ r)) =>
    Or.elim (em q)
      (fun (hq: q) => Or.inl (fun (_: p) => hq))
      (fun (hnq: ¬q) =>
        Or.elim (em r)
          (fun (hr: r) => Or.inr (fun (_: p) => hr))
          (fun (hnr: ¬r) =>
            Or.inl
              (fun (hp: p) => absurd (h hp) (not_or hnq hnr))))

-- Classical 2
example: ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun (h: ¬(p ∧ q)) =>
    Or.elim (em p)
      (fun (hp: p) =>
        Or.inr (fun (hq: q) => show False from h ⟨hp, hq⟩))
      Or.inl

-- Classical 3
example: ¬(p → q) → (p ∧ ¬q) :=
  λ h : ¬(p → q) =>
    (em q).elim
      (λ hq : q => absurd (λ _: p => hq) h)
      (λ hnq : ¬q =>
        (em p).elim
          (λ hp : p => ⟨hp, hnq⟩)
          (λ hnp : ¬p =>
            absurd (λ hp : p => absurd hp hnp) h))

example: ¬(p → q) → (p ∧ ¬q) :=
  λ h : ¬(p → q) =>
      (em p).elim
        (λ (hp: p) =>
          ⟨
            hp,
            (λ (hq: q) => show False from h (λ _ : p => hq))
          ⟩)
      (λ (hnp: ¬p) =>  absurd (λ hp : p => absurd hp hnp) h)

-- Classical 4
example : (p → q) → (¬p ∨ q) :=
  λ h : p -> q =>
    (em p).elim
      (λ hp : p => Or.inr (h hp))
      (λ hnp : ¬p => Or.inl hnp)

-- Classical 5
example : (¬q → ¬p) -> (p → q) :=
  λ h : (¬q -> ¬p) =>
    (em q).elim
      (λ hq : q => (λ _: p => hq))
      (λ hnq : ¬q => (λ hp : p => absurd hp (h hnq)))

-- Classical 6
example : p ∨ ¬p := (em p)

-- Classical 7
example : (((p → q) → p) → p) :=
  λ h : ((p -> q) -> p) =>
    (em p).elim
      id
      (λ hnp : ¬p =>
        absurd (h (λ hp : p => absurd hp hnp)) hnp)

-- Without classical
example : ¬(p ↔ ¬p) :=
  λ h : p ↔ ¬p  =>
    let hnp : ¬p := (λ hp : p => absurd hp (h.mp hp))
    absurd (h.mpr hnp) hnp

-- from dne to em
example: (p ∨ ¬p) :=
  dne
    λ (h: ¬(p ∨ ¬p)) =>
      have hnp : ¬p := (λ (hp: p) =>  absurd (show (p ∨ ¬p) from Or.inl hp) h)
      have hn : (p ∨ ¬p) := Or.inr hnp
      absurd hn h

------------------------------
-- Chapter 4
------------------------------

section
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  λ h : ∀ x : α, p x ∧ q x =>
  λ y : α =>
  show p y from (h y).left

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab: r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc


variable (α: Type) (r : α → α → Prop)
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab: r a b) (hbc : r b c)

#check trans_r
#check refl_r
#check symm_r
#check trans_r hab
#check trans_r hab hbc

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  (trans_r (trans_r hab (symm_r hcb)) hcd)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  have : r b c := (symm_r hcb)
  have : r a c := (trans_r hab this)
  show r a d from (trans_r this hcd)

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd: c = d)

example : a = d :=
  calc
    a = b := hab
    b = c := (Eq.symm hcb)
    c = d := hcd

example : a = d := (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1.subst h2

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Prop)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y := (x + y).mul_add  x y
  have h₂ : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x  y x) ▸ (Nat.add_mul x  y y) ▸ h₁
  h₂.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

variable (a b c d e : Nat)
variable (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d)

theorem T : a = e :=
  calc a
    _ = b := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e := h4.symm

theorem T' : a = e :=
  calc a
    _ = b := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e := by rw [h4]

theorem T'' : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

theorem T''' : a = e :=
  by simp [h4, h1, h2, h3, Nat.add_comm]

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc a
    _ = b := h1
    _ ≤ c := h2
    _ < c + 1 := Nat.lt_succ_self c
    _ < d := h3

end

section divide_trans
def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨kx, hxy⟩ := h₁
  let ⟨ky, hyz⟩ := h₂
  ⟨kx * ky, by rw [Nat.mul_comm kx, Nat.mul_assoc ky, hxy, hyz]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    divides x y := h₁
    _ = z := h₂
    divides _ (2 * z) := divides_mul ..

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    x ∣ y := h₁
    _ = z := h₂
    _ ∣ (2 * z) := divides_mul ..

end divide_trans

section calc_x_plus_y_sq

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y := Nat.mul_add ..
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [
    Nat.add_mul,
    Nat.mul_add,
    Nat.mul_add,
    ←Nat.add_assoc,
    Nat.add_assoc (x * x),
    Nat.add_comm (x * y),
    ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [
    Nat.mul_add,
    Nat.add_mul,
    Nat.add_mul,
    ←Nat.add_assoc
  ]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

end calc_x_plus_y_sq

section exist_quant

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example : ∃ x : Nat, x > 0 :=
  have h : 5 > 0 := Nat.succ_pos 4
  ⟨5, h⟩

example : ∃ x : Nat, x > 0 :=
  ⟨5, Nat.succ_pos 4⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, ⟨hxy, hyz⟩⟩

#check Exists.intro

variable (g : Nat -> Nat -> Nat)
variable (hg : g 0 0 = 0)
theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true
#print gex1
#print gex2
#print gex3
#print gex4

set_option pp.explicit false

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  h.elim λ w => λ hp => ⟨w, hp.right, hp.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, ⟨hw.right, hw.left⟩⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hwl, hwr⟩ => ⟨w, ⟨hwr, hwl⟩⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨hw, hpl, hpr⟩ := h
  ⟨hw, hpr, hpl⟩

example : (h : ∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hl, hr⟩ => ⟨w, hr, hl⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2: is_even b) : is_even (a + b) :=
  let ⟨w1, h1p⟩ := h1
  let ⟨w2, h2p⟩ := h2
  ⟨w1 + w2,
    (calc a + b
      _ = 2 * w1 + 2 * w2 := by rw [h1p, h2p]
      _ = 2 * (w1 + w2) := by rw [Nat.mul_add])⟩

theorem even_plus_even1 (h1 : is_even a) (h2: is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, h1p⟩, ⟨w2, h2p⟩ => ⟨w1 + w2, by rw [h1p, h2p, Nat.mul_add]⟩

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (λ (h1: ¬ ∃ x, p x) =>
      have h2 : ∀ x, ¬ p x :=
        λ x =>
          λ (h3 : p x) =>
            have h4: ∃ x, p x := ⟨x, h3⟩
            show False from h1 h4
      show False from h h2)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    λ (h1 : ¬ ∃ x, p x) =>
      suffices h2 : ∀ x, ¬ p x from (show False from h h2)
      λ x =>
        λ (h3 : p x) =>
          show False from h1 ⟨x, h3⟩

end exist_quant

section proof_language_intro

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  Nat.le_trans (by assumption) (h 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0)  (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

example (n : Nat) : Nat := ‹Nat›

end proof_language_intro

section chapter4_exercises

variable (α : Type) (p q : α → Prop)

-- 1

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨
    λ h => ⟨λ k => (h k).left, λ k => (h k).right⟩,
    λ h => λ k => ⟨(h.left k), (h.right k)⟩
  ⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h₀ => λ h₁ => λ k => (h₀ k) (h₁ k)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h => λ k => h.elim (λ hp => Or.inl (hp k)) (λ hq => Or.inr (hq k))

-- 2

variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  λ ht => ⟨λ h => (h ht), λ hr => λ _ => hr⟩

open Classical

variable (px_or_r₁ : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r :=
  λ h =>
    (em r).elim
      (λ hr => Or.inr hr)
      (λ hnr => Or.inl (λ k => (h k).elim id (λ hr => absurd hr hnr))))

variable (px_or_r₂ : (∀ x, p x) ∨ r → (∀ x, p x ∨ r) :=
  λ h =>
    h.elim
      (λ hpx => λ k => Or.inl (hpx k))
      (λ hr => λ _ => Or.inr hr))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := ⟨px_or_r₁, px_or_r₂⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨
    λ h => λ hr => λ k => (h k) hr,
    λ hrpx => λ (k : α) => λ (hr : r) => ((hrpx hr) k)
  ⟩

-- 3; barber's paradox

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hb := (h barber)
  have k : (¬shaves barber barber) := λ hsbb => show False from (hb.mp hsbb) hsbb
  show False from k (hb.mpr k)

-- 4

def even(n : Nat) : Prop := ∃ x : Nat, n = 2 * x

def prime(n : Nat) : Prop := ¬ ∃ x k : Nat, x > 1 ∧ x * k = n

def infinitely_many_primes : Prop := ∃ n m : Nat, n > m ∧ prime m ∧ prime n

def Fermat_prime(n : Nat) : Prop := ∃ x, n = 2^(2^x) + 1 ∧ prime n

def infinitely_many_Fermat_primes : Prop :=
  ∃ n m : Nat,
    Fermat_prime n ∧
    Fermat_prime m ∧
    n > m

def goldbach_conjecture : Prop :=
  ∀ s : Nat, s ≥ 4 → ∃ m n : Nat, prime m ∧ prime n ∧ m + n = s

def Goldbach's_week_conjecture : Prop :=
  ∀ s : Nat, s > 5 → ∃ m n p : Nat, prime m ∧ prime n ∧ prime p ∧ m + n + p = s

def Fermat's_last_theorem : Prop :=
  ¬ ∃ n x y z : Nat,
    n > 2 ∧
    (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    x ^ n + y ^ n = z ^ n

-- 5

example : (∃ x : α, r) → r :=
  λ h =>
    let ⟨_, hr⟩ := h
    hr

example (a : α) : r → (∃ x : α, r) := λ hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨
    λ ⟨w, h⟩ => ⟨⟨w, h.left⟩, h.right⟩,
    λ ⟨⟨w, hpx⟩, hr⟩ => ⟨w, ⟨hpx, hr⟩⟩
  ⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨
    λ ⟨w, h⟩ => h.elim (λ hpx => Or.inl ⟨w, hpx⟩) (λ hqx => Or.inr ⟨w, hqx⟩),
    λ h => h.elim (λ ⟨w, hpx⟩ => ⟨w, Or.inl hpx⟩) (λ ⟨w, hqx⟩ => ⟨w, Or.inr hqx⟩)
  ⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨
    λ h =>
      λ (hnt: ∃ x, ¬ p x) =>
        let ⟨w, hnpx⟩ := hnt
        show False from hnpx (h w),
    λ hr : ¬ ∃ x, ¬ p x =>
      λ (x : α) =>
        have h_nn : ¬¬ p x :=
          λ (hp : ¬ p x) =>
            have h_e_npx : ∃ x, ¬ p x := ⟨x, hp⟩
            show False from  hr h_e_npx
        dne h_nn
  ⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨
    λ ⟨w, h⟩ =>
      byContradiction
        λ hnr : ¬¬(∀ x, ¬ p x) =>
          show False from ((dne hnr) w) h,
    λ h : ¬ (∀ x, ¬ p x) =>
      byContradiction
        λ hnp : ¬ (∃ x, p x) =>
          have h_never_px : ∀ x, ¬ p x :=
            λ x : α =>
              λ hp : p x =>
                show False from hnp ⟨x, hp⟩
        show False from h h_never_px
  ⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨
    λ h : ¬ ∃ x, p x =>
      λ x : α =>
        λ hpx : p x =>
          show False from h ⟨x, hpx⟩,
    λ h : ∀ x, ¬ p x =>
      byContradiction
        λ hlnn : ¬¬ ∃ x, p x =>
          have ⟨w, hp⟩ := dne hlnn
          show False from (h w) hp
  ⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨
    λ h : ¬ ∀ x, p x =>
      byContradiction
        λ hn : ¬ ∃ x, ¬ p x =>
          have h_all_px : ∀ x, p x :=
            λ x : α =>
              have hnnp :=
                λ hnp : ¬ p x =>
                  show False from hn ⟨x, hnp⟩
              (dne hnnp)
          show False from h h_all_px,
    λ ⟨w, hnp⟩ =>
      byContradiction
        λ hn : ¬ ¬ ∀ x, p x =>
          show False from hnp ((dne hn) w)
  ⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨
    λ h =>
      λ ⟨w, hp⟩ =>
        ((h w) hp),
    λ h =>
      λ x : α =>
        λ hp : p x =>
          have hep : ∃ x, p x := ⟨x, hp⟩
          (h hep)
  ⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  ⟨
    λ h : ∃ x, p x → r =>
      λ hth : ∀ x, p x =>
        let ⟨w, hpr⟩ := h
        let hpw : p w := (hth w)
        (hpr hpw),
    λ h : (∀ x, p x) → r =>
      (em (∀ x, p x)).elim
        (λ hp : ∀ x, p x =>
          have hr : r := h hp
          have hpr : p a → r := (λ _ : p a => hr)
          show (∃ x, p x → r) from ⟨a, hpr⟩)
        (λ hnap : ¬ ∀ x, p x =>
          byContradiction
            λ hnl : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                  byContradiction
                    λ hnpx : ¬ p x =>
                      have hl : ∃ x, p x → r :=
                        ⟨x, λ hpx : p x => absurd hpx hnpx⟩
                      show False from hnl hl
              show False from hnap hap)
  ⟩

end chapter4_exercises
