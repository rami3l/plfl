-- https://plfa.github.io/BigStep/

import Plfl.Init
import Plfl.Untyped
import Plfl.Untyped.Substitution

import Mathlib.Tactic

namespace BigStep

open Untyped (Context)
open Untyped.Notation

-- https://plfa.github.io/BigStep/#environments
/--
A closure in call-by-name is a term paired with its environment.
-/
inductive Clos : Type where
| clos : ∀ {Γ}, (m : Γ ⊢ ✶) → ((Γ ∋ ✶) → Clos) → Clos

/--
An environment in call-by-name is a map from variables to closures.
-/
abbrev ClosEnv (Γ : Context) := (Γ ∋ ✶) → Clos

instance : EmptyCollection (ClosEnv ∅) where emptyCollection := by intro.

def ClosEnv.tail (γ : ClosEnv Γ) (c : Clos) : ClosEnv (Γ‚ ✶)
| .z => c
| .s i => γ i

namespace Notation
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚' " => ClosEnv.tail
end Notation

open Notation

inductive Eval : ClosEnv Γ → (Γ ⊢ ✶) → Clos → Type where
| var : γ i = .clos m δ → Eval δ m v → Eval γ (` i) v
| lam : Eval γ (ƛ m) (.clos (ƛ m) γ)
| ap : Eval γ l (.clos (ƛ n) δ) → Eval (δ‚' .clos m γ) n v → Eval γ (l □ m) v

namespace Notation
  scoped notation:40 γ " ⊢ " m " ⇓ " c:51 => Eval γ m c
end Notation

-- https://plfa.github.io/BigStep/#exercise-big-step-eg-practice
example
: γ ⊢ (ƛ ƛ #1) $ (ƛ #0 □ #0) $ (ƛ #0 □ #0)
-- (λ x y => x) ((λ f => f f) (λ f => f f)) ⇓ (λ y => ((λ f => f f) (λ f => f f)))
⇓ .clos (ƛ #1) (γ‚' .clos ((ƛ #0 □ #0) $ (ƛ #0 □ #0)) γ)
:= .ap .lam .lam

-- https://plfa.github.io/BigStep/#the-big-step-semantics-is-deterministic
