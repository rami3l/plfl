-- https://plfa.github.io/Adequacy/

import Plfl.Init
import Plfl.Untyped.BigStep
import Plfl.Untyped.Denotational.Soundness

namespace Adequacy

open Untyped Untyped.Notation
open Untyped.Subst
open BigStep BigStep.Notation
open Denotational Denotational.Notation
open Soundness (soundness)

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
  /--
  `𝕍 v c` will hold when:
  - `c` is in WHNF (i.e. is a λ-abstraction);
  - `v` is a function;
  - `c`'s body evaluates according to `v`.
  -/
  def 𝕍 : Value → Clos → Prop
  | _, .clos (` _) _ => ⊥
  | _, .clos (_ □ _) _ => ⊥
  | ⊥, .clos (ƛ _) _ => ⊤
  | vw@(v ⇾ w), .clos (ƛ n) γ =>
    have : sizeOf w < sizeOf vw := by subst_vars; simp
    ∀ {c}, 𝔼 v c → GtFn w → ∃ c', (γ‚' c ⊢ n ⇓ c') ∧ 𝕍 w c'
  | uv@(.conj u v), c@(.clos (ƛ _) _) =>
    have : sizeOf v < sizeOf uv := by subst_vars; simp
    𝕍 u c ∧ 𝕍 v c

  /--
  `𝔼 v c` will hold when:
  - `v` is greater than a function value;
  - `c` evaluates to a closure `c'` in WHNF;
  - `𝕍 v c` holds.
  -/
  def 𝔼 : Value → Clos → Prop
  | v, .clos m γ' => GtFn v → ∃ c, (γ' ⊢ m ⇓ c) ∧ 𝕍 v c
end
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Termination.20of.20mutual.20recursive.20defs.20with.20a.20.22shorthand.22.3F/near/378733953
termination_by
  𝕍 v c => (sizeOf v, 0)
  𝔼 v c => (sizeOf v, 1)

/-- `𝔾` relates `γ` to `γ'` if the corresponding values and closures are related by `𝔼` -/
def 𝔾 (γ : Env Γ) (γ' : ClosEnv Γ) : Prop := ∀ {x : Γ ∋ ✶}, 𝔼 (γ x) (γ' x)

/-- The proof of a term being in Weak-Head Normal Form. -/
def WHNF (t : Γ ⊢ a) : Prop := ∃ n : Γ‚ ✶ ⊢ ✶, t = (ƛ n)

/-- A closure in a 𝕍 relation must be in WHNF. -/
lemma WHNF.of_𝕍 (vc : 𝕍 v (.clos m γ)) : WHNF m := by
  cases m with (simp [𝕍] at vc; try contradiction) | lam n => exists n

lemma 𝕍.conj (uc : 𝕍 u c) (vc : 𝕍 v c) : 𝕍 (u ⊔ v) c := by
  let .clos m γ := c; cases m with (simp [𝕍] at *; try contradiction)
  | lam => unfold 𝕍; exact ⟨uc, vc⟩

lemma 𝕍.of_not_gtFn (nf : ¬ GtFn v) : 𝕍 v (.clos (ƛ n) γ') := by induction v with unfold 𝕍
| bot => triv
| fn v w => exfalso; apply nf; exists v, w
| conj _ _ ih ih' => exact not_gtFn_conj_inv nf |>.imp ih ih'

mutual
  lemma 𝕍.sub {v v'} (vvc : 𝕍 v c) (lt : v' ⊑ v) : 𝕍 v' c := by
    let .clos m γ := c; cases m with (simp [𝕍] at *; try contradiction) | lam m =>
      rename_i Γ; induction lt generalizing Γ with
      | bot => triv
      | conjL lt lt' ih ih' => unfold 𝕍; exact ⟨ih _ _ _ vvc, ih' _ _ _ vvc⟩
      | conjR₁ lt ih => apply ih; unfold 𝕍 at vvc; exact vvc.1
      | conjR₂ lt ih => apply ih; unfold 𝕍 at vvc; exact vvc.2
      | trans lt lt' ih ih' => apply_rules [ih, ih']
      | @fn v₂ v₁ w₁ w₂ lt lt' ih ih' =>
        unfold 𝕍 at vvc ⊢; intro c evc gtw
        have : sizeOf v₁ + sizeOf v₂ < sizeOf v + sizeOf v' := by
          -- change _ < sizeOf (v₁ ⇾ w₁) + sizeOf (v₂ ⇾ w₂)
          sorry
        have ⟨c', ec', h⟩ := vvc (evc.sub lt) (gtw.sub lt'); exists c', ec'
        let .clos m γ := c'; have ⟨m', h'⟩ := WHNF.of_𝕍 h; subst h'; exact ih' _ _ _ h
      | dist => sorry

  lemma 𝔼.sub (evc : 𝔼 v c) (lt : v' ⊑ v) : 𝔼 v' c := by
    let .clos m γ := c; simp only [𝔼] at *; intro gtv'
    have ⟨c, ec, vvc⟩ := evc <| gtv'.sub lt; exists c, ec; exact vvc.sub lt
end
termination_by
  𝕍.sub => (sizeOf v + sizeOf v', 0)
  𝔼.sub => (sizeOf v + sizeOf v', 1)

#print Value.fn.sizeOf_spec
