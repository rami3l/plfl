-- https://plfa.github.io/Substitution/#plfa_plfa-part2-Substitution-2341

import Plfl.Init
import Plfl.Untyped

import Mathlib.Tactic

set_option tactic.simp.trace true

namespace Substitution

open Untyped Notation

variable {Γ Δ Φ : Context}

abbrev Rename (Γ Δ) := ∀ {a : Ty}, Γ ∋ a → Δ ∋ a
abbrev Subst (Γ Δ) := ∀ {a : Ty}, Γ ∋ a → Δ ⊢ a

-- https://plfa.github.io/Substitution/#the-%CF%83-algebra-of-substitution
abbrev ids : Subst Γ Γ := .var
abbrev shift : Subst Γ (Γ‚ a) := .var ∘ .s

abbrev cons (m : Δ ⊢ a) (σ : Subst Γ Δ) : Subst (Γ‚ a) Δ
| _, .z => m
| _, .s x => σ x

abbrev seq (σ : Subst Γ Δ) (τ : Subst Δ Φ) : Subst Γ Φ := ⟪τ⟫ ∘ σ

namespace Notation
  infixr:60 " ⦂⦂ " => cons
  infix:50 " ⨟ " => seq
end Notation

open Notation

-- https://plfa.github.io/Substitution/#relating-the-σ-algebra-and-substitution-functions
def ren (ρ : Rename Γ Δ) : Subst Γ Δ := ids ∘ ρ

-- https://plfa.github.io/Substitution/#proofs-of-sub-head-sub-tail-sub-η-z-shift-sub-idl-sub-dist-and-sub-app
@[simp] theorem subst_head {m : Δ ⊢ a} {σ : Subst Γ Δ} : ⟪m ⦂⦂ σ⟫ (` .z) = m := rfl
@[simp] theorem subst_tail {m : Δ ⊢ a} {σ : Subst Γ Δ} : (shift ⨟ m ⦂⦂ σ) = σ (a := b) := rfl
