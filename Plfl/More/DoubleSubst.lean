-- https://plfa.github.io/More/#exercise-double-subst-stretch

-- Adapted from <https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda>.

import Plfl
import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

open Term

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L104
@[simp]
lemma subst₁_shift : (t' : Γ ⊢ b) ⇴ shift (t : Γ ⊢ a) = t := by
  sorry
  -- simp_all; cases t <;> try trivial
  -- · case lam n => simp_all; apply congr_arg lam; sorry

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L154
@[simp]
lemma shift_subst
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a}
(t : Γ ⊢ a)
: subst (exts (b := b) σ) (shift t) = shift (subst σ t)
:= by
  sorry
  -- cases t with
  -- | var => trivial
  -- | lam t =>
  --   apply congr_arg lam
  --   have := shift_subst (b := b) (σ := exts σ) t
  --   unfold shift at this

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L161
@[simp]
lemma exts_subst_compose
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a} {σ' : ∀ {a}, Δ ∋ a → Ε ⊢ a}
(i : Γ‚ b ∋ a)
: subst (exts σ') (exts σ i) = exts (subst σ' ∘ σ) i
:= by
  match i with
  | .z => trivial
  | .s i => exact shift_subst (σ i)

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L170
@[simp]
lemma subst_subst_compose
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a} {σ' : ∀ {a}, Δ ∋ a → Ε ⊢ a}
(t : Γ ⊢ a)
: subst σ' (subst σ t) = subst (subst σ' ∘ σ) t
:= by
  match t with
  | ` t => trivial
  | ƛ t =>
    apply congr_arg lam
    rw [subst_subst_compose (σ := exts σ) (σ' := exts σ') t]
    congr; ext; apply exts_subst_compose
  | l □ m => apply congr_arg₂ ap <;> apply subst_subst_compose
  | 𝟘 => trivial
  | ι t => apply congr_arg succ; apply subst_subst_compose
  | 𝟘? l m n =>
    apply congr_arg₃ case <;> try apply subst_subst_compose
    · conv_lhs =>
      rw [subst_subst_compose (σ := exts σ) (σ' := exts σ') n]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_compose t]
  | μ t =>
    apply congr_arg mu
    have := subst_subst_compose (σ := exts σ) (σ' := exts σ') t
    rw [this]; congr; ext; apply exts_subst_compose
  | .prim t => trivial
  | .mulP m n => apply congr_arg₂ mulP <;> apply subst_subst_compose
  | .let m n =>
    apply congr_arg₂ «let»
    · apply subst_subst_compose
    · conv_lhs =>
      rw [subst_subst_compose (σ := exts σ) (σ' := exts σ') n]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_compose t]
  | .prod m n => apply congr_arg₂ prod <;> apply subst_subst_compose
  | .fst t => apply congr_arg fst; apply subst_subst_compose
  | .snd t => apply congr_arg snd; apply subst_subst_compose
  | .left t => apply congr_arg left; apply subst_subst_compose
  | .right t => apply congr_arg right; apply subst_subst_compose
  | .caseSum s l r =>
    apply congr_arg₃ caseSum <;> try apply subst_subst_compose
    · conv_lhs =>
      rw [subst_subst_compose (σ := exts σ) (σ' := exts σ') l]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_compose t]
    · conv_lhs =>
      rw [subst_subst_compose (σ := exts σ) (σ' := exts σ') r]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_compose t]
  | .caseVoid v => apply congr_arg caseVoid; apply subst_subst_compose
  | ◯ => trivial
  | .nil => trivial
  | .cons m n => apply congr_arg₂ cons <;> apply subst_subst_compose
  | .caseList l m n =>
    apply congr_arg₃ caseList <;> try apply subst_subst_compose
    · rw [subst_subst_compose (σ := exts (exts σ)) (σ' := exts (exts σ')) n]
      congr; ext _ t; rw [Function.comp_apply, exts_subst_compose t]
      congr; ext _ t; rw [Function.comp_apply, exts_subst_compose t]

theorem double_subst
: subst₂ (v : Γ ⊢ a) (w : Γ ⊢ b) (n : Γ‚ a‚ b ⊢ c)
= v ⇴ rename .s w ⇴ n
:= by
  cases n <;> first | trivial | simp_all; congr; ext; aesop
