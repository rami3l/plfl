-- https://plfa.github.io/Adequacy/

import Plfl.Init
import Plfl.Untyped.BigStep
import Plfl.Untyped.Denotational.Soundness

namespace Adequacy

open Untyped Untyped.Notation
open Untyped.Subst
open BigStep
open Denotational Denotational.Notation

/-- `GtFn u` means that it is "greater than" a certain `.fn` value. -/
def GtFn (u : Value) : Prop := ∃ v w, v ⇾ w ⊑ u

namespace GtFn
  theorem sub (gt : GtFn u) (lt : u ⊑ u') : GtFn u' :=
    let ⟨v, w, lt'⟩ := gt; ⟨v, w, lt'.trans lt⟩

  theorem bot : ¬ GtFn ⊥ := by
    sorry
    -- intro ⟨v, w, lt⟩; have := sub_inv_fun lt
end GtFn

namespace Notation
end Notation

open Notation

-- open Substitution (ids sub_ids)
-- open Soundness (soundness)
