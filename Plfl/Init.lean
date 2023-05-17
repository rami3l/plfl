import Mathlib.Logic.IsEmpty

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))

/--
`PDecidable` is like `Decidable`, but allows arbitrary sorts.
-/
abbrev PDecidable α := IsEmpty α ⊕' α

namespace PDecidable
  def toDecidable : PDecidable α → Decidable (Nonempty α) := by
    intro
    | .inr a => right; exact ⟨a⟩
    | .inl na => left; simpa
end PDecidable

instance [Repr α] : Repr (PDecidable α) where
  reprPrec da n := match da with
  | .inr a => ".inr " ++ reprPrec a n
  | .inl _ => ".inl _"

theorem congr_arg₃
(f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
(hx : x = x') (hy : y = y') (hz : z = z')
: f x y z = f x' y' z'
:= by subst hx hy hz; rfl
