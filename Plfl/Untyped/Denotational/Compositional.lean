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

theorem sub_ℱ (d : ℱ (ℰ n) γ v) : u ⊑ v → ℱ (ℰ n) γ u
| .bot => True.intro
| .conjL lt lt' => ⟨sub_ℱ d lt, sub_ℱ d lt'⟩
| .conjR₁ lt => sub_ℱ d.1 lt
| .conjR₂ lt => sub_ℱ d.2 lt
| .trans lt lt' => sub_ℱ (sub_ℱ d lt') lt
| .fn lt lt' => .sub (up_env d lt) lt'
| .dist => .conj d.1 d.2

-- theorem ℱ_ℰ {γ : Env Γ} (d : ℰ (ƛ n) γ v) : ℱ (ℰ n) γ v := by induction d with
-- | fn d => exact d
-- | bot => exact True.intro
-- | conj d d' => exact ⟨ℱ_ℰ d, ℱ_ℰ d'⟩
-- | sub d lt => exact sub_ℱ (ℱ_ℰ d) lt
