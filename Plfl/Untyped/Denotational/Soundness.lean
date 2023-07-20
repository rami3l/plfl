-- https://plfa.github.io/Soundness/

import Plfl.Init
import Plfl.Untyped.Denotational.Compositional

namespace Soundness

open Untyped Untyped.Notation
open Untyped.Subst
open Substitution (Rename Subst)
open Denotational Denotational.Notation
open Compositional Compositional.Notation

-- https://plfa.github.io/Soundness/#simultaneous-substitution-preserves-denotations
namespace Env
  /--
  `Eval δ σ γ` means that for every variable `i`,
  `σ i` results in the same value as the one for `i` in the original environment `γ`.
  -/
  abbrev Eval (δ : Env Δ) (σ : Subst Γ Δ) (γ : Env Γ) : Prop := ∀ (i : Γ ∋ ✶), δ ⊢ σ i ⇓ γ i
end Env

namespace Notation
  scoped notation:30 δ " `⊢ " σ " ⇓ " γ:51 => Env.Eval δ σ γ
end Notation

open Notation

section
  variable {γ : Env Γ} {δ : Env Δ}

  lemma subst_ext (σ : Subst Γ Δ) (d : δ `⊢ σ ⇓ γ) : δ`‚ v `⊢ exts σ ⇓ (γ`‚ v)
  | .z => .var
  | .s i => rename_pres .s (λ _ => .refl) (d i)

  /-- The result of evaluation is conserved after simultaneous substitution. -/
  theorem subst_pres (σ : Subst Γ Δ) (s : δ `⊢ σ ⇓ γ) (d : γ ⊢ m ⇓ v)
  : δ ⊢ subst σ m ⇓ v
  := by induction d generalizing Δ with
  | var => apply s
  | ap _ _ ih ih'=> exact (ih σ s).ap (ih' σ s)
  | fn _ ih => refine .fn ?_; apply ih (exts σ); exact subst_ext σ s
  | bot => exact .bot
  | conj _ _ ih ih' => exact (ih σ s).conj (ih' σ s)
  | sub _ lt ih => exact (ih σ s).sub lt

  -- https://plfa.github.io/Soundness/#single-substitution-preserves-denotations
  /-- The result of evaluation is conserved after single substitution. -/
  theorem subst₁_pres (dn : γ`‚ v ⊢ n ⇓ w) (dm : γ ⊢ m ⇓ v) : γ ⊢ n ⇷ m ⇓ w
  := subst_pres (subst₁σ m) (λ | .z => dm | .s _ => .var) dn

  -- https://plfa.github.io/Soundness/#reduction-preserves-denotations
  theorem reduction_pres (d : γ ⊢ m ⇓ v) (r : m —→ n) : γ ⊢ n ⇓ v := by induction d with
  | var => contradiction
  | bot => exact .bot
  | fn _ ih => cases r with | lamζ r => exact (ih r).fn
  | conj _ _ ih ih' => exact (ih r).conj (ih' r)
  | sub _ lt ih => exact (ih r).sub lt
  | ap d d' ih ih' => cases r with
    | apξ₁ r => exact (ih r).ap d'
    | apξ₂ r => exact d.ap (ih' r)
    | lamβ => exact subst₁_pres (lam_inv d) d'

  -- https://plfa.github.io/Soundness/#renaming-reflects-meaning
  theorem rename_reflect {ρ : Rename Γ Δ} (lt : δ ∘ ρ `⊑ γ) (d : δ ⊢ rename ρ m ⇓ v)
  : γ ⊢ m ⇓ v
  := by
    generalize hx : rename ρ m = x at *
    induction d generalizing Γ with
    | bot => exact .bot
    | var => cases m with (injection hx; try subst_vars)
      | var i => exact .sub .var <| (var_inv .var).trans (lt i)
    | ap _ _ ih ih' => cases m with injection hx
      | ap => rename_i hx hx'; exact (ih lt hx).ap (ih' lt hx')
    | fn _ ih => cases m with injection hx
      | lam => refine .fn ?_; apply ih (ρ := ext ρ) (ext_sub' ρ lt); trivial
    | conj _ _ ih ih' => exact (ih lt hx).conj (ih' lt hx)
    | sub _ lt' ih => exact (ih lt hx).sub lt'

  theorem rename_shift_reflect (d : γ`‚ v' ⊢ shift m ⇓ v) : γ ⊢ m ⇓ v :=
    rename_reflect (by rfl) d
end
