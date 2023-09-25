-- Propositions and Proofs (Ch. 3)

variable (p q r : Prop)

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

