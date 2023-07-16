-- https://plfa.github.io/Soundness/

import Plfl.Init
import Plfl.Untyped.Denotational.Compositional

namespace Soundness

namespace Compositional

open Untyped Untyped.Notation
open Untyped.Subst
open Substitution
open Denotational Denotational.Notation
open Compositional Compositional.Notation

-- https://plfa.github.io/Soundness/#simultaneous-substitution-preserves-denotations

namespace Env
  abbrev Eval (δ : Env Δ) (σ : Subst Γ Δ) (γ : Env Γ) : Prop := ∀ (i : Γ ∋ ✶), δ ⊢ σ i ⇓ γ i
end Env

namespace Notation
  scoped notation:30 δ " `⊢ " σ " ⇓ " γ:51 => Env.Eval δ σ γ
end Notation

open Notation

lemma subst_ext {γ : Env Γ} {δ : Env Δ} (σ : Subst Γ Δ) (d : δ `⊢ σ ⇓ γ)
: δ`‚ v `⊢ exts σ ⇓ (γ`‚ v)
| .z => .var
| .s i => rename_pres .s (λ _ => .refl) (d i)
