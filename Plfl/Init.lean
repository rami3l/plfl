import Std.Data.List.Lemmas

import Mathlib.Data.Vector
import Mathlib.Logic.IsEmpty
import Mathlib.Tactic

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))

/--
`Decidable'` is like `Decidable`, but allows arbitrary sorts.
-/
abbrev Decidable' α := IsEmpty α ⊕' α

namespace Decidable'
  def toDecidable : Decidable' α → Decidable (Nonempty α) := by
    intro
    | .inr a => right; exact ⟨a⟩
    | .inl na => left; simpa
end Decidable'

instance [Repr α] : Repr (Decidable' α) where
  reprPrec da n := match da with
  | .inr a => ".inr " ++ reprPrec a n
  | .inl _ => ".inl _"

/--
`Iff'` is like `Iff`, but allows arbitrary sorts.
-/
abbrev Iff' a b := a → b × b → a

infix:20 " ↔'" => Iff'

theorem congr_arg₃
(f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
(hx : x = x') (hy : y = y') (hz : z = z')
: f x y z = f x' y' z'
:= by subst hx hy hz; rfl

namespace Vector
  def dropLast (v : Vector α n) : Vector α (n - 1) := by
    exists v.1.dropLast; simp only [List.length_dropLast, Vector.length_val]

  theorem get_dropLast (v : Vector α (n + 1)) (i : Fin n)
  : v.dropLast.get i = v.get i.1
  := by
    simp only [
      Vector.get, dropLast, v.1.dropLast_eq_take,
      Vector.length_val, Nat.pred_succ, Fin.coe_eq_castSucc
    ]
    change List.get _ _ = List.get _ _; rw [←List.get_take]
    · rfl
    · simp only [Fin.is_lt]
end Vector
