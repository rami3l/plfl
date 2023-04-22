-- https://plfa.github.io/Properties/

import Mathlib.CategoryTheory.Iso

import Plfl.Lambda

set_option tactic.simp.trace true

open Context Context.IsTy

-- https://plfa.github.io/Properties/#values-do-not-reduce
theorem Value.not_reduce' : Value m → (Σ n, m —→ n) → False := by
  intro v; intro ⟨n, hn⟩
  cases v <;> try contradiction
  · rename_i v'; cases hn
    · rename_i n n' hn'; exact not_reduce' v' ⟨n', hn'⟩

theorem Value.not_reduce : Value m → IsEmpty (Σ n, m —→ n) :=
  Function.isEmpty (β := False) ∘ not_reduce'

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

  def hom_inv_id {v t} : @well_typed_inv v t ∘ well_typed_hom = id := by
    funext c; cases c <;> simp_all
    · rename_i v' c'; have := @hom_inv_id v' ℕt; apply_fun (· c') at this; trivial

  def inv_hom_id {v t} : @well_typed_hom v t ∘ well_typed_inv = id := by
    funext c; match c with
    | ⟨ty_lam ty, Value.lam⟩ => simp_all
    | ⟨ty_zero, Value.zero⟩ => simp_all
    | ⟨ty_succ ty, Value.succ n⟩ =>
        rename_i v'; have := @inv_hom_id v' ℕt;
        rw [Function.comp_apply, well_typed_inv, well_typed_hom]; split
        · simp_all; apply_fun (· (ty, n)) at this; simp_all

  /--
  The Canonical forms are exactly the well-typed values.
  -/
  instance well_typed : Canonical v t ≅ (∅ ⊢ v ⦂ t) × Value v where
    hom := well_typed_hom
    inv := well_typed_inv
    hom_inv_id := hom_inv_id
    inv_hom_id := inv_hom_id
end Canonical

-- https://plfa.github.io/Properties/#progress
