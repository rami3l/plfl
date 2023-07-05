-- https://plfa.github.io/Denotational/

import Plfl.Init
import Plfl.Untyped

import Mathlib.Tactic

namespace Denotational

-- https://plfa.github.io/Denotational/#values
inductive Value : Type where
/-- No information is provided about the computation. -/
| bot : Value
/-- A single input-output mapping, from the first term to the second. -/
| fn : Value → Value → Value
/-- A function that maps inputs to outputs according to both terms. -/
| conj : Value → Value → Value
deriving BEq, DecidableEq, Repr

namespace Notation
  instance : Bot Value where bot := .bot
  instance : Sup Value where sup := .conj

  scoped infixr:70 " ⇾ " => Value.fn
end Notation

open Notation

inductive Subset : Value → Value → Type where
| bot : Subset ⊥ v
| conjL : Subset v u → Subset w u → Subset (v ⊔ w) u
| conjR₁ : Subset u v → Subset u (v ⊔ w)
| conjR₂ : Subset u w → Subset u (v ⊔ w)
| trans : Subset u v → Subset v w → Subset u w
| fn : Subset v' v → Subset w w' → Subset (v ⇾ w) (v' ⇾ w')
| dist : Subset (v ⇾ (w ⊔ w')) ((v ⇾ w) ⊔ (v ⇾ w'))

namespace Notation
  scoped infix:40 " ⊑ " => Subset
end Notation

instance : Trans Subset Subset Subset where trans := .trans

@[refl]
theorem Subset.refl : v ⊑ v := match v with
| ⊥ => .bot
| _ ⇾ _ => .fn refl refl
| .conj _ _ => .conjL (.conjR₁ refl) (.conjR₂ refl)

/-- The `⊔` operation is monotonic with respect to `⊑`. -/
@[simp]
theorem subset_subset (d₁ : v ⊑ v') (d₂ : w ⊑ w') : v ⊔ w ⊑ v' ⊔ w' :=
  .conjL (.conjR₁ d₁) (.conjR₂ d₂)

@[simp]
theorem conj_fn_conj : (v ⊔ v') ⇾ (w ⊔ w') ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := calc
  _ ⊑ ((v ⊔ v') ⇾ w) ⊔ ((v ⊔ v') ⇾ w') := .dist
  _ ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := open Subset in by
    apply subset_subset <;> refine .fn ?_ .refl
    · apply conjR₁; rfl
    · apply conjR₂; rfl

@[simp]
theorem conj_subset₁ : u ⊔ v ⊑ w → u ⊑ w := by intro
| .conjL h _ => exact h
| .conjR₁ h => refine .conjR₁ ?_; exact conj_subset₁ h
| .conjR₂ h => refine .conjR₂ ?_; exact conj_subset₁ h
| .trans h h' => refine .trans ?_ h'; exact conj_subset₁ h

@[simp]
theorem conj_subset₂ : u ⊔ v ⊑ w → v ⊑ w := by intro
| .conjL _ h => exact h
| .conjR₁ h => refine .conjR₁ ?_; exact conj_subset₂ h
| .conjR₂ h => refine .conjR₂ ?_; exact conj_subset₂ h
| .trans h h' => refine .trans ?_ h'; exact conj_subset₂ h

-- https://plfa.github.io/Denotational/#environments
