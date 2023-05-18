-- https://plfa.github.io/Untyped/

import Plfl.Init

import Mathlib.Tactic

set_option tactic.simp.trace true

namespace Untyped

-- https://plfa.github.io/Untyped/#types
inductive Ty where
/-- Native natural type made of 𝟘 and ι. -/
| star: Ty
deriving BEq, DecidableEq, Repr

namespace Notations
  scoped notation " ✶ " => Ty.star
end Notations

open Notations

-- https://plfa.github.io/Untyped/#exercise-type-practice
instance : Ty ≃ Unit where
  toFun _ := ()
  invFun _ := ✶
  left_inv := by simp only [Function.LeftInverse, implies_true]
  right_inv := by simp only

instance : Unique Ty where
  default := ✶
  uniq := by simp

-- https://plfa.github.io/DeBruijn/#contexts
abbrev Context : Type := List Ty

namespace Context
  abbrev snoc (Γ : Context) (a : Ty) : Context := a :: Γ
  abbrev lappend (Γ : Context) (Δ : Context) : Context := Δ ++ Γ
end Context

namespace Notations
  open Context

  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚ " => snoc
  scoped infixl:45 "‚‚ " => lappend
end Notations

-- https://plfa.github.io/Untyped/#exercise-context%E2%84%95-practice
instance : Context ≃ ℕ where
  toFun := List.length
  invFun := (List.replicate · ✶)
  left_inv := by
    unfold Function.LeftInverse; intro x; simp only
    sorry
  right_inv := by sorry


-- https://plfa.github.io/DeBruijn/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ‚ t) t
| s : Lookup Γ t → Lookup (Γ‚ t') t
deriving DecidableEq, Repr

namespace Notations
  open Lookup

  scoped infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  scoped syntax "get_elem" (ppSpace term) : tactic
  scoped macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic| exact Lookup.z)
  | n+1 => `(tactic| apply Lookup.s; get_elem $(Lean.quote n))

  scoped macro " ♯ " n:term:90 : term => `(by get_elem $n)
end Notations

