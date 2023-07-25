-- https://plfa.github.io/Adequacy/

import Plfl.Init
import Plfl.Untyped.BigStep
import Plfl.Untyped.Denotational.Soundness

namespace Adequacy

open Untyped Untyped.Notation
open Untyped.Subst
open BigStep
open Denotational Denotational.Notation

-- https://plfa.github.io/Adequacy/#the-property-of-being-greater-or-equal-to-a-function
/-- `GtFn u` means that it is "greater than" a certain function value. -/
def GtFn (u : Value) : Prop := ∃ v w, v ⇾ w ⊑ u

/-- If `u` is greater than a function, then an even greater value `u'` is too. -/
theorem GtFn.sub (gt : GtFn u) (lt : u ⊑ u') : GtFn u' :=
  let ⟨v, w, lt'⟩ := gt; ⟨v, w, lt'.trans lt⟩

/-- `⊥` is never greater than a function. -/
lemma not_gtFn_bot : ¬ GtFn ⊥
| ⟨v, w, lt⟩ => by
  have ⟨_, f, s, _⟩ := sub_inv_fn lt; have ⟨_, _, i⟩ := elem_of_allFn f; cases s i

/-- If the join of two values is greater than a function, then at least one of them is too. -/
theorem GtFn.conj (gt : GtFn (u ⊔ v)) : GtFn u ∨ GtFn v := by
  have ⟨_, _, lt⟩ := gt; have ⟨_, f, s, _⟩ := sub_inv_fn lt; have ⟨v, w, i⟩ := elem_of_allFn f
  refine Or.imp ?inl ?inr <| s i <;> (intro i'; exists v, w; exact sub_of_elem i')

/-- If neither of the two values is greater than a function, then nor is their join. -/
lemma not_gtFn_conj (ngt : ¬ GtFn u) (ngt' : ¬ GtFn v) : ¬ GtFn (u ⊔ v) := by
  intro gtuv; exfalso; exact (gtuv.conj).elim ngt ngt'

namespace Notation
end Notation

open Notation

-- open Substitution (ids sub_ids)
-- open Soundness (soundness)
