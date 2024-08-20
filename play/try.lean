inductive Ftree (β : Type _) where
  | file
  | dir (children: List (Ftree β))
  deriving Repr

inductive AllRU (p : β → Prop) : Ftree β → Prop
  | file : AllRU p .file
  | dir :
    AllRU p dir →
    p key value →
    ForallTree p right →
    ForallTree p (.node left key value right)


inductive list (α : Type _)
| nil  : list
| cons : α → list → list

namespace list

variable {α : Type}

notation (name := cons) h :: t  := cons h t

def append (s t : list α) : list α :=
list.rec t (λ x l u, x::u) s

notation (name := append) s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) :
  x::s ++ t = x::(s ++ t) := rfl

end list
