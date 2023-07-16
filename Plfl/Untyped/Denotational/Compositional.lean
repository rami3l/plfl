-- https://plfa.github.io/Compositional/

import Plfl.Init
import Plfl.Untyped.Denotational

namespace Compositional

open Untyped.Notation
open Denotational
open Denotational.Notation

-- https://plfa.github.io/Compositional/#equation-for-lambda-abstraction
def ℱ (d : Denot (Γ‚ ✶)) : Denot Γ
| _, ⊥ => ⊤
| γ, v ⇾ w => d (γ`‚ v) w
| γ, .conj u v => ℱ d γ u ∧ ℱ d γ v

lemma sub_ℱ (d : ℱ (ℰ n) γ v) (lt : u ⊑ v) : ℱ (ℰ n) γ u := by induction lt with
| bot => triv
| conjL _ _ ih ih' => exact ⟨ih d, ih' d⟩
| conjR₁ _ ih => exact ih d.1
| conjR₂ _ ih => exact ih d.2
| trans _ _ ih ih' => exact ih (ih' d);
| fn lt lt' => exact .sub (up_env d lt) lt'
| dist => exact .conj d.1 d.2

lemma ℱ_ℰ (d : ℰ (ƛ n) γ v) : ℱ (ℰ n) γ v := by
  generalize hx : (ƛ n) = x at *
  induction d with try injection hx
  | fn d => subst_vars; exact d
  | bot => triv
  | conj _ _ ih ih' => exact ⟨ih hx, ih' hx⟩
  | sub _ lt ih => exact sub_ℱ (ih hx) lt

theorem lam_inv (d : γ ⊢ ƛ n ⇓ v ⇾ v') : (γ`‚ v) ⊢ n ⇓ v' := ℱ_ℰ d

lemma ℰ_lam (d : ℱ (ℰ n) γ v) : ℰ (ƛ n) γ v := match v with
| .bot => .bot
| .fn _ _ => .fn d
| .conj _ _ => (ℰ_lam d.1).conj (ℰ_lam d.2)

theorem lam_equiv : ℰ (ƛ n) = ℱ (ℰ n) := by ext; exact ⟨ℱ_ℰ, ℰ_lam⟩

-- https://plfa.github.io/Compositional/#equation-for-function-application
abbrev 𝒜 (d d' : Denot Γ) : Denot Γ | γ, w => (w ⊑ ⊥) ∨ (∃ v, d γ (v ⇾ w) ∧ d' γ v)

namespace Notation
  scoped infixl:70 " ● " => 𝒜
end Notation

open Notation

lemma 𝒜_ℰ (d : ℰ (l □ m) γ v) : (ℰ l ● ℰ m) γ v := by
  generalize hx : l □ m = x at *
  induction d with try injection hx
  | bot => left; rfl
  | ap d d' => subst_vars; right; rename_i v' _ _ _ _; exists v'
  | sub _ lt ih => match ih hx with
    | .inl lt' => left; exact lt.trans lt'
    | .inr ⟨v', efv', ev'⟩ => right; refine ⟨v', efv'.sub ?_, ev'⟩; exact .fn .refl lt
  | conj _ _ ih ih' => match ih hx, ih' hx with
    | .inl lt, .inl lt' => left; exact lt.conjL lt'
    | .inl lt, .inr ⟨v', efv', ev'⟩ =>
        right; refine ⟨v', efv'.sub ?_, ev'⟩; refine .fn .refl ?_
        refine .conjL ?_ .refl; exact sub_of_sub_bot lt
    | .inr ⟨v', efv', ev'⟩, .inl lt =>
        right; refine ⟨v', efv'.sub ?_, ev'⟩; refine .fn .refl ?_
        refine .conjL .refl ?_; exact sub_of_sub_bot lt
    | .inr ⟨v', efv', ev'⟩, .inr ⟨v'', efv'', ev''⟩ =>
        right; refine ⟨v' ⊔ v'', ?_, ev'.conj ev''⟩
        exact (efv'.conj efv'').sub fn_conj_sub_conj_fn

lemma ℰ_ap : (ℰ l ● ℰ m) γ v → ℰ (l □ m) γ v
| .inl lt => .sub .bot lt
| .inr ⟨_, efv, ev⟩ => efv.ap ev

theorem ap_equiv : ℰ (l □ m) = (ℰ l ● ℰ m) := by ext; exact ⟨𝒜_ℰ, ℰ_ap⟩

abbrev 𝒱 (i : Γ ∋ ✶) (γ : Env Γ) (v : Value) : Prop := v ⊑ γ i

theorem var_inv (d : ℰ (` i) γ v) : 𝒱 i γ v := by
  generalize hx : (` i) = x at *
  induction d with try injection hx
  | var => subst_vars; rfl
  | bot => exact .bot
  | conj _ _ ih ih' => exact (ih hx).conjL (ih' hx)
  | sub _ lt ih => exact lt.trans (ih hx)

theorem var_equiv : ℰ (` i) = 𝒱 i := by ext; exact ⟨var_inv, .sub .var⟩

-- https://plfa.github.io/Compositional/#congruence

-- Congruence Lemmas

-- Nothing to do!
-- Since we chose to use `=` instead of `≃` in `Denotational`,
-- everything is handled automagically!
