-- https://plfa.github.io/Adequacy/

import Plfl.Init
import Plfl.Untyped.BigStep
import Plfl.Untyped.Denotational.Soundness

namespace Adequacy

open Untyped Untyped.Notation
open Untyped.Subst
open BigStep BigStep.Notation
open Denotational Denotational.Notation

-- https://plfa.github.io/Adequacy/#the-property-of-being-greater-or-equal-to-a-function
/-- `GtFn u` means that it is "greater than" a certain function value. -/
def GtFn (u : Value) : Prop := ∃ v w, v ⇾ w ⊑ u

/-- If `u` is greater than a function, then an even greater value `u'` is too. -/
lemma GtFn.sub (gt : GtFn u) (lt : u ⊑ u') : GtFn u' :=
  let ⟨v, w, lt'⟩ := gt; ⟨v, w, lt'.trans lt⟩

/-- `⊥` is never greater than a function. -/
lemma not_gtFn_bot : ¬ GtFn ⊥
| ⟨v, w, lt⟩ => by
  have ⟨_, f, s, _⟩ := sub_inv_fn lt; have ⟨_, _, i⟩ := elem_of_allFn f; cases s i

/-- If the join of two values is greater than a function, then at least one of them is too. -/
lemma GtFn.conj (gt : GtFn (u ⊔ v)) : GtFn u ∨ GtFn v := by
  have ⟨_, _, lt⟩ := gt; have ⟨_, f, s, _⟩ := sub_inv_fn lt; have ⟨v, w, i⟩ := elem_of_allFn f
  refine Or.imp ?inl ?inr <| s i <;> (intro i'; exists v, w; exact sub_of_elem i')

/-- If neither of the two values is greater than a function, then nor is their join. -/
lemma not_gtFn_conj (ngt : ¬ GtFn u) (ngt' : ¬ GtFn v) : ¬ GtFn (u ⊔ v) := by
  intro gtuv; exfalso; exact gtuv.conj |>.elim ngt ngt'

/--
If the join of two values is not greater than a function,
then neither of them is individually.
-/
lemma not_gtFn_conj_inv (ngtuv : ¬ GtFn (u ⊔ v)) : ¬ GtFn u ∧ ¬ GtFn v := by
  by_contra h; simp_all only [not_and, not_not]
  have ngtu := ngtuv ∘ (GtFn.sub · <| .conjR₁ .refl)
  have ngtv := ngtuv ∘ (GtFn.sub · <| .conjR₂ .refl)
  exact h ngtu |> ngtv

lemma not_gtFn_conj_iff : (¬ GtFn u ∧ ¬ GtFn v) ↔ ¬ GtFn (u ⊔ v) :=
  ⟨(λ nn => not_gtFn_conj nn.1 nn.2), not_gtFn_conj_inv⟩

theorem GtFn.dec (v : Value) : Decidable (GtFn v) := by induction v with
| bot => left; exact not_gtFn_bot
| fn v w => right; exists v, w
| conj _ _ ih ih' => cases ih with
  | isTrue h => right; have ⟨v, w, lt⟩ := h; exists v, w; exact lt.conjR₁
  | isFalse h => cases ih' with
    | isTrue h' => right; have ⟨v, w, lt⟩ := h'; exists v, w; exact lt.conjR₂
    | isFalse h' => left; exact not_gtFn_conj h h'

-- https://plfa.github.io/Adequacy/#relating-values-to-closures
mutual
  def 𝕍 : Value → Clos → Prop
  | _, .clos (` _) _ => ⊥
  | _, .clos (_ □ _) _ => ⊥
  | ⊥, .clos (ƛ _) _ => ⊤
  | v ⇾ w, .clos (ƛ n) γ =>
    have : sizeOf w < 1 + sizeOf v + sizeOf w := by simp_arith; apply Nat.zero_le
    ∀ c, 𝔼 v c → GtFn w → ∃ c', (γ‚' c ⊢ n ⇓ c') ∧ 𝕍 w c'
  | .conj u v, c@(.clos (ƛ _) _) =>
    have : sizeOf v < 1 + sizeOf u + sizeOf v := by simp_arith; apply Nat.zero_le
    𝕍 u c ∧ 𝕍 v c

  def 𝔼 : Value → Clos → Prop
  | v, .clos m γ' => GtFn v → ∃ c, (γ' ⊢ m ⇓ c) ∧ 𝕍 v c
end
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Termination.20of.20mutual.20recursive.20defs.20with.20a.20.22shorthand.22.3F/near/378733953
termination_by
  𝕍 v c => (sizeOf v, 0)
  𝔼 v c => (sizeOf v, 1)


-- namespace Notation
-- end Notation

-- open Notation

-- open Soundness (soundness)
