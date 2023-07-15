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

theorem sub_ℱ (d : ℱ (ℰ n) γ v) (lt : u ⊑ v) : ℱ (ℰ n) γ u := by
  induction lt with
  | bot => exact True.intro
  | conjL _ _ ih ih' => exact ⟨ih d, ih' d⟩
  | conjR₁ _ ih => exact ih d.1
  | conjR₂ _ ih => exact ih d.2
  | trans _ _ ih ih' => exact ih (ih' d);
  | fn lt lt' => exact .sub (up_env d lt) lt'
  | dist => exact .conj d.1 d.2

theorem ℱ_ℰ (d : ℰ (ƛ n) γ v) : ℱ (ℰ n) γ v := by
  generalize hx : (ƛ n) = x at *
  induction d with try injection hx
  | fn d => subst_vars; exact d
  | bot => exact True.intro
  | conj _ _ ih ih' => exact ⟨ih hx, ih' hx⟩
  | sub _ lt ih => exact sub_ℱ (ih hx) lt
