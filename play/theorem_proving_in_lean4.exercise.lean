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
