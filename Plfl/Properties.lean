-- https://plfa.github.io/Properties/

import Mathlib.CategoryTheory.Iso

import Plfl.Lambda

set_option tactic.simp.trace true

open Context Context.IsTy Term.Reduce
open Sum

-- https://plfa.github.io/Properties/#values-do-not-reduce
private def Value.not_reduce' : Value m → (Σ n, m —→ n) → False := by
  intro v; intro ⟨n, hn⟩
  cases v <;> try contradiction
  · rename_i v'; cases hn
    · rename_i n n' hn'; exact not_reduce' v' ⟨n', hn'⟩

@[simp]
theorem Value.not_reduce : Value m → IsEmpty (Σ n, m —→ n) :=
  Function.isEmpty (β := False) ∘ not_reduce'

@[simp]
theorem Reduce.not_value : m —→ n → IsEmpty (Value m) := by
  intro h; apply Function.isEmpty (β := False); intro v;
  apply Value.not_reduce'
  · trivial
  · exact ⟨n, h⟩

-- https://plfa.github.io/Properties/#exercise-canonical--practice
inductive Canonical : Term → Ty → Type where
| can_lam : (∅ :< x ⦂ tx ⊢ n ⦂ tn) → Canonical (ƛ x : n) (tx =⇒ tn)
| can_zero : Canonical 𝟘 ℕt
| can_succ : Canonical n ℕt → Canonical (ι n) ℕt

namespace Canonical
  @[simp]
  def ofIsTy : (∅ ⊢ m ⦂ t) → Value m → Canonical m t
  | ty_lam l, Value.lam => can_lam l
  | ty_zero, V𝟘 => can_zero
  | ty_succ t, Value.succ m => can_succ <| ofIsTy t m

  @[simp]
  def well_typed_hom : Canonical v t → (∅ ⊢ v ⦂ t) × Value v := by
    intro
    | can_lam h => exact ⟨ty_lam h, Value.lam⟩
    | can_zero => exact ⟨ty_zero, V𝟘⟩
    | can_succ h => have ⟨ty, v⟩ := well_typed_hom h; exact ⟨ty_succ ty, Value.succ v⟩

  @[simp]
  def well_typed_inv : (∅ ⊢ v ⦂ t) × Value v → Canonical v t := by
    intro
    | ⟨ty_lam ty, Value.lam⟩ => exact can_lam ty
    | ⟨ty_zero, Value.zero⟩ => exact can_zero
    | ⟨ty_succ ty, Value.succ v⟩ => apply can_succ; exact well_typed_inv ⟨ty, v⟩

  def well_typed_hom_inv_id {v t} : @well_typed_inv v t ∘ well_typed_hom = id := by
    funext c; cases c <;> simp_all
    · rename_i v' c'; have := @well_typed_hom_inv_id v' ℕt
      apply_fun (· c') at this; trivial

  def well_typed_inv_hom_id {v t} : @well_typed_hom v t ∘ well_typed_inv = id := by
    funext c; match c with
    | ⟨ty_lam ty, Value.lam⟩ => simp_all
    | ⟨ty_zero, Value.zero⟩ => simp_all
    | ⟨ty_succ ty, Value.succ n⟩ =>
        rename_i v'; have := @well_typed_inv_hom_id v' ℕt;
        rw [Function.comp_apply, well_typed_inv, well_typed_hom]; split
        · simp_all; apply_fun (· (ty, n)) at this; simp_all

  /--
  The Canonical forms are exactly the well-typed values.
  -/
  @[simp]
  instance well_typed : Canonical v t ≅ (∅ ⊢ v ⦂ t) × Value v where
    hom := well_typed_hom
    inv := well_typed_inv
    hom_inv_id := well_typed_hom_inv_id
    inv_hom_id := well_typed_inv_hom_id
end Canonical

-- https://plfa.github.io/Properties/#progress
/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
@[aesop safe [constructors, cases]]
inductive Progress (m : Term) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m
--^ In general, the rule of thumb is to consider the easy case (`step`) before the hard case (`done`) for easier proofs.

namespace Progress
  @[simp]
  def ofIsTy : (∅ ⊢ m ⦂ t) → Progress m := by
    intro
    | ty_var _ => contradiction
    | ty_lam _ => exact done Value.lam
    | ty_ap jl jm => cases ofIsTy jl with
      | step => apply step; · apply ap_ξ₁; trivial
      | done vl => cases ofIsTy jm with
        | step => apply step; apply ap_ξ₂ <;> trivial
        | done => cases vl with
          | lam => apply step; apply lam_β; trivial
          | _ => contradiction
    | ty_zero => exact done V𝟘
    | ty_succ j => cases ofIsTy j with
      | step => apply step; apply succ_ξ; trivial
      | done => apply done; apply Value.succ; trivial
    | ty_case jl jm jn => cases ofIsTy jl with
      | step => apply step; apply case_ξ; trivial
      | done vl => cases vl with
        | lam => trivial
        | zero => exact step zero_β
        | succ => apply step; apply succ_β; trivial
    | ty_mu _ => exact step mu_β
end Progress

-- https://plfa.github.io/Properties/#exercise-value-practice
@[simp]
def IsTy.is_value : (∅ ⊢ m ⦂ t) → Decidable (Nonempty (Value m)) := by
  intro j; cases Progress.ofIsTy j
  · rename_i n r; have := Reduce.not_value r; apply isFalse; simp_all
  · exact isTrue ⟨by trivial⟩

@[simp]
def Progress' (m : Term) : Type := Value m ⊕ Σ n, m —→ n

namespace Progress'
  -- https://plfa.github.io/Properties/#exercise-progress-practice
  @[simp]
  def ofIsTy : (∅ ⊢ m ⦂ t) → Progress' m := by
    intro
    | ty_var _ => contradiction
    | ty_lam _ => exact inl Value.lam
    | ty_ap jl jm => match ofIsTy jl with
      | inr ⟨n, r⟩ => exact inr ⟨_, ap_ξ₁ r⟩
      | inl vl => match ofIsTy jm with
        | inr ⟨n, r⟩ => apply inr; exact ⟨_, ap_ξ₂ vl r⟩
        | inl _ => cases Canonical.ofIsTy jl vl with
          | can_lam => apply inr; refine ⟨_, lam_β ?_⟩; trivial
    | ty_zero => exact inl V𝟘
    | ty_succ j => match ofIsTy j with
      | inl v => apply inl; exact Value.succ v
      | inr ⟨n, r⟩ => exact inr ⟨_, succ_ξ r⟩
    | ty_case jl jm jn => match ofIsTy jl with
      | inr ⟨n, r⟩ => exact inr ⟨_, case_ξ r⟩
      | inl vl => cases vl with
        | lam => trivial
        | zero => exact inr ⟨_, zero_β⟩
        | succ v => exact inr ⟨_, succ_β v⟩
    | ty_mu _ => exact inr ⟨_, mu_β⟩
end Progress'

namespace Progress
  -- https://plfa.github.io/Properties/#exercise-progress--practice
  @[simp] def sum_hom : Progress m → Progress' m | step r => inr ⟨_, r⟩ | done v => inl v
  @[simp] def sum_inv : Progress' m → Progress m | inl v => done v | inr ⟨_, r⟩ => step r

  instance sum_iso : Progress m ≅ Progress' m where
    hom := sum_hom
    inv := sum_inv
    hom_inv_id : sum_inv ∘ sum_hom = id := by funext x; aesop
    inv_hom_id : sum_hom ∘ sum_inv = id := by funext x; aesop
end Progress

-- https://plfa.github.io/Properties/#renaming
namespace Renaming
  open Lookup

  /--
  If one context maps to another, the mapping holds after adding the same variable to both contexts.
  -/
  lemma ext
  : (∀ {x tx}, (Γ ∋ x ⦂ tx) → (Δ ∋ x ⦂ tx))
  → (∀ {x y tx ty}, (Γ :< y ⦂ ty ∋ x ⦂ tx) → (Δ :< y ⦂ ty ∋ x ⦂ tx))
  := by
    intro ρ _ _ _ _; intro
    | z => exact z
    | s nxy lx => exact s nxy <| ρ lx

  theorem rename
  : (∀ {x t}, (Γ ∋ x ⦂ t) → (Δ ∋ x ⦂ t))
  → (∀ {m t}, (Γ ⊢ m ⦂ t) → (Δ ⊢ m ⦂ t))
  := by
    intro ρ _ _; intro
    | ty_var j => apply ty_var; exact ρ j
    | ty_lam j => apply ty_lam; exact rename (ext ρ) j
    | ty_ap jl jm =>
        apply ty_ap
        · exact rename ρ jl
        · exact rename ρ jm
    | ty_zero => apply ty_zero
    | ty_succ j => apply ty_succ; exact rename ρ j
    | ty_case jl jm jn =>
        apply ty_case
        · exact rename ρ jl
        · exact rename ρ jm
        · exact rename (ext ρ) jn
    | ty_mu j => apply ty_mu; exact rename (ext ρ) j
end Renaming
