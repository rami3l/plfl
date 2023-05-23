-- https://plfa.github.io/Substitution/#plfa_plfa-part2-Substitution-2341

import Plfl.Init
import Plfl.Untyped

import Mathlib.Tactic

namespace Substitution

open Untyped Notation

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
open Subst

-- https://plfa.github.io/Substitution/#relating-the-σ-algebra-and-substitution-functions
def ren (ρ : Rename Γ Δ) : Subst Γ Δ := ids ∘ ρ

section
  variable {m : Δ ⊢ a} {σ : Subst Γ Δ} {τ : Subst Δ Φ}

  -- https://plfa.github.io/Substitution/#proofs-of-sub-head-sub-tail-sub-η-z-shift-sub-idl-sub-dist-and-sub-app
  @[simp] theorem sub_head : ⟪m ⦂⦂ σ⟫ (` .z) = m := rfl
  @[simp] theorem sub_tail : (shift ⨟ m ⦂⦂ σ) = σ (a := b) := rfl
  @[simp] theorem sub_η {σ : Subst (Γ‚ a) Δ} : (⟪σ⟫ (` .z) ⦂⦂ (shift ⨟ σ)) = σ (a := b) := by ext i; cases i <;> rfl
  @[simp] theorem z_shift : ((` .z) ⦂⦂ shift) = @ids (Γ‚ a) b := by ext i; cases i <;> rfl
  @[simp] theorem sub_ids_seq : (ids ⨟ σ) = σ (a := a) := rfl
  @[simp] theorem sub_ap {l m : Γ ⊢ ✶} : ⟪σ⟫ (l □ m) = (⟪σ⟫ l) □ (⟪σ⟫ m) := rfl
  @[simp] theorem sub_dist : @Eq (Γ‚ a ∋ b → Φ ⊢ b) ((m ⦂⦂ σ) ⨟ τ) ((⟪τ⟫ m) ⦂⦂ (σ ⨟ τ)) := by ext i; cases i <;> rfl
end

-- https://plfa.github.io/Substitution/#interlude-congruences
/-
Nothing to do.
-/

section
  variable {m : Γ ⊢ a} {σ : Subst Γ Δ} {ρ : Rename Γ Δ}

  -- https://plfa.github.io/Substitution/#relating-rename-exts-ext-and-subst-zero-to-the-%CF%83-algebra
  @[simp] theorem ren_ext : @Eq (Γ‚ b ∋ c → Δ‚ b ⊢ c) (ren (ext ρ)) (exts (ren ρ)) := by ext i; cases i <;> rfl
  @[simp] theorem ren_shift : @Eq (Γ ∋ a → Γ‚ b ⊢ a) (ren .s) shift := by congr

  @[simp]
  theorem rename_subst_ren {Γ Δ} {ρ : Rename Γ Δ} {m : Γ ⊢ a} : rename ρ m = ⟪ren ρ⟫ m := by
    match m with
    | ` _ => rfl
    | ƛ n => apply congr_arg Term.lam; rw [rename_subst_ren]; congr; funext _; exact ren_ext
    | l □ m => simp only [sub_ap]; apply congr_arg₂ Term.ap <;> exact rename_subst_ren

  @[simp] theorem rename_shift : @Eq (Γ‚ b ⊢ a) (rename .s m) (⟪shift⟫ m) := by simp only [rename_subst_ren]; congr

  @[simp]
  theorem exts_cons_shift : exts (a := a) (b := b) σ = (` .z ⦂⦂ (σ ⨟ shift)) := by
    ext i; cases i <;> simp only [exts, rename_subst_ren, ren_shift]; rfl

  @[simp]
  theorem ext_cons_z_shift : @Eq (Γ‚ b ∋ a → Δ‚ b ⊢ a) (ren (ext ρ)) (` .z ⦂⦂ (ren ρ ⨟ shift)) := by
    ext i; cases i <;> simp only [ren_ext, exts, rename_subst_ren, ren_shift]; rfl

  @[simp] theorem subst_z_cons_ids : @Eq (Γ‚ b ∋ a → Γ ⊢ a) (subst₁σ m) (m ⦂⦂ ids) := by ext i; cases i <;> rfl

  -- https://plfa.github.io/Substitution/#proofs-of-sub-abs-sub-id-and-rename-id
  @[simp]
  theorem sub_lam {σ : Subst Γ Δ} {n : Γ‚ ✶ ⊢ ✶} : ⟪σ⟫ (ƛ n) = (ƛ ⟪(` .z) ⦂⦂ (σ ⨟ shift)⟫ n) := by
    change (ƛ ⟪exts σ⟫ n) = _; congr; funext _; exact exts_cons_shift

  @[simp] theorem exts_ids : @Eq (Γ‚ b ∋ a → _) (exts ids) ids := by ext i; cases i <;> rfl

  @[simp]
  theorem sub_ids {Γ} {m : Γ ⊢ a} : ⟪ids (Γ := Γ)⟫ m = m := by
    match m with
    | ` _ => rfl
    | ƛ n => apply congr_arg Term.lam; convert sub_ids; exact exts_ids
    | l □ m => simp only [sub_ap]; apply congr_arg₂ Term.ap <;> exact sub_ids

  @[simp] theorem rename_id : rename (λ {a} x => x) m = m := by convert sub_ids; ext; simp only [rename_subst_ren, ren]; congr

  -- https://plfa.github.io/Substitution/#proof-of-sub-idr
  @[simp] theorem sub_seq_ids : @Eq (Γ ∋ a → Δ ⊢ a) (σ ⨟ ids) σ := by ext; simp only [Function.comp_apply, sub_ids]
end

section
  variable {m : Γ ⊢ a} {ρ : Rename Δ Φ} {ρ' : Rename Γ Δ}

  -- https://plfa.github.io/Substitution/#proof-of-sub-sub
  @[simp] theorem comp_ext : @Eq (Γ‚ b ∋ a → _) ((ext ρ) ∘ (ext ρ')) (ext (ρ ∘ ρ')) := by ext i; cases i <;> rfl

  @[simp]
  theorem comp_rename {Γ Δ Φ} {m : Γ ⊢ a} {ρ : Rename Δ Φ} {ρ' : Rename Γ Δ}
  : rename ρ (rename ρ' m) = rename (ρ ∘ ρ') m := by
     match m with
    | ` _ => rfl
    | ƛ n => apply congr_arg Term.lam; convert comp_rename; exact comp_ext.symm
    | l □ m => apply congr_arg₂ Term.ap <;> exact comp_rename

  @[simp]
  theorem comm_subst_rename {Γ Δ} {σ : Subst Γ Δ} {ρ : ∀ {Γ}, Rename Γ (Γ‚ ✶)}
  (r : ∀ {x : Γ ∋ ✶}, exts σ (ρ x) = rename ρ (σ x)) {m : Γ ⊢ ✶}
  : ⟪exts (b := ✶) σ⟫ (rename ρ m) = rename ρ (⟪σ⟫ m)
  := by
    match m with
    | ` _ => exact r
    | l □ m => apply congr_arg₂ Term.ap <;> exact comm_subst_rename r
    | ƛ n =>
      apply congr_arg Term.lam

      let ρ' : ∀ {Γ}, Rename Γ (Γ‚ ✶) := by intro
      | [] => intro; intro.
      | ✶ :: Γ => intro; exact ext ρ

      apply comm_subst_rename (Γ := Γ‚ ✶) (Δ := Δ‚ ✶) (σ := exts σ) (ρ := ρ') (m := n); intro
      | .z => rfl
      | .s x => calc exts (exts σ) (ρ' (.s x))
        _ = rename .s (exts σ (ρ x)) := rfl
        _ = rename .s (rename ρ (σ x)) := by rw [r]
        _ = rename (.s ∘ ρ) (σ x) := comp_rename
        _ = rename (ext ρ ∘ .s) (σ x) := by congr
        _ = rename (ext ρ) (rename .s (σ x)) := comp_rename.symm
        _ = rename ρ' (exts σ (.s x)) := rfl
end
