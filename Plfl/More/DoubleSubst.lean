-- https://plfa.github.io/More/#exercise-double-subst-stretch

-- Adapted from <https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda>.

import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

open Term

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L104
@[simp]
lemma subst₁_shift : (t' : Γ ⊢ b) ⇴ (rename .s (t : Γ ⊢ a)) = t := by
  sorry
  -- simp_all; cases t <;> try trivial
  -- · case lam n => simp_all; apply congr_arg lam; sorry

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L161
@[simp]
lemma exts_subst_compose
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a} {σ' : ∀ {a}, Δ ∋ a → Ε ⊢ a} (t : Γ‚ b ∋ a)
: subst (exts σ') (exts σ t) = exts ((subst σ') ∘ σ) t
:= by
  sorry

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L170
@[simp]
lemma subst_subst_compose
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a} {σ' : ∀ {a}, Δ ∋ a → Ε ⊢ a} (t : Γ ⊢ a)
: subst σ' (subst σ t) = subst ((subst σ') ∘ σ) t
:= by
  cases t with try trivial
  | lam t =>
    rename_i b a; apply congrArg lam
    have := subst_subst_compose (σ := exts σ) (σ' := exts σ') t
    rw [this]; congr; ext; apply exts_subst_compose

theorem double_subst
: subst₂ (v : Γ ⊢ a) (w : Γ ⊢ b) (n : Γ‚ a‚ b ⊢ c)
= v ⇴ rename .s w ⇴ n
:= by
  cases n <;> first | trivial | simp_all; congr; ext; aesop
