-- https://plfa.github.io/BigStep/

import Plfl.Init
import Plfl.Untyped
import Plfl.Untyped.Substitution

import Mathlib.Tactic

namespace BigStep

open Untyped (Context)
open Untyped.Notation
open Substitution (Subst ids sub_ids)

-- https://plfa.github.io/BigStep/#environments
/--
A closure in call-by-name is a term paired with its environment.
-/
inductive Clos : Type where
| clos : ∀ {Γ}, (m : Γ ⊢ ✶) → ((Γ ∋ ✶) → Clos) → Clos

/--
An environment in call-by-name is a map from variables to closures.
-/
abbrev ClosEnv (Γ : Context) := (Γ ∋ ✶) → Clos

instance : EmptyCollection (ClosEnv ∅) where emptyCollection := by intro.

def ClosEnv.tail (γ : ClosEnv Γ) (c : Clos) : ClosEnv (Γ‚ ✶)
| .z => c
| .s i => γ i

namespace Notation
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚' " => ClosEnv.tail
end Notation

open Notation

inductive Eval : ClosEnv Γ → (Γ ⊢ ✶) → Clos → Type where
| var : γ i = .clos m δ → Eval δ m v → Eval γ (` i) v
| lam : Eval γ (ƛ m) (.clos (ƛ m) γ)
| ap : Eval γ l (.clos (ƛ n) δ) → Eval (δ‚' .clos m γ) n v → Eval γ (l □ m) v

namespace Notation
  scoped notation:40 γ " ⊢ " m " ⇓ " c:51 => Eval γ m c
end Notation

-- https://plfa.github.io/BigStep/#exercise-big-step-eg-practice
example
: γ ⊢ (ƛ ƛ #1) $ (ƛ #0 □ #0) $ (ƛ #0 □ #0)
-- (λ x y => x) ((λ f => f f) (λ f => f f)) ⇓ (λ y => ((λ f => f f) (λ f => f f)))
⇓ .clos (ƛ #1) (γ‚' .clos ((ƛ #0 □ #0) $ (ƛ #0 □ #0)) γ)
:= .ap .lam .lam

-- https://plfa.github.io/BigStep/#the-big-step-semantics-is-deterministic
@[simp]
theorem Eval.determ : γ ⊢ m ⇓ v → γ ⊢ m ⇓ v' → v = v' := by intro
| .lam, .lam => rfl
| .var h mc, .var h' mc' =>
  injection h.symm.trans h'; rename_i h hh hh'; subst h; rw [←hh.eq, ←hh'.eq] at mc'
  exact mc.determ mc'
| .ap mc mc₁, .ap mc' mc₁' =>
  have := mc.determ mc'; injection this
  rename_i h hh hh'; subst h; rw [←hh'.eq] at mc₁'
  injection hh; rename_i h; rw [←h] at mc₁'
  exact mc₁.determ mc₁'

-- https://plfa.github.io/BigStep/#big-step-evaluation-implies-beta-reduction-to-a-lambda
noncomputable def Clos.equiv : Clos → (∅ ⊢ ✶) → Type
| .clos (Γ := Γ) m γ, n =>
  Σ (σ : Subst Γ ∅), PProd (∀ i, Clos.equiv (γ i) (σ i)) (n = ⟪σ⟫ m)

abbrev ClosEnv.equiv (γ : ClosEnv Γ) (σ : Subst Γ ∅) : Type :=
  ∀ i, Clos.equiv (γ i) (σ i)

namespace Notation
  -- The default precedence in Agda is 20.
  -- See: <https://agda.readthedocs.io/en/v2.6.1/language/mixfix-operators.html#precedence>
  scoped infix:20 " ~~ " => Clos.equiv
  scoped infix:20 " ~~ₑ " => ClosEnv.equiv
end Notation

section
  open Untyped.Subst
  open Substitution

  @[simp] lemma ClosEnv.empty_equiv_ids : ∅ ~~ₑ ids := by intro.

  @[simp]
  abbrev ext_subst (σ : Subst Γ Δ) (n : Δ ⊢ ✶) : Subst (Γ‚ ✶) Δ :=
    ⟪subst₁σ n⟫ ∘ exts σ

  @[simp]
  lemma subst₁σ_exts {σ : Subst Γ Δ} {m : Δ ⊢ b} {i : Γ ∋ ✶}
  : (ext_subst σ m) (.s i) = σ i
  := by simp only [subst₁σ_exts_cons]

  @[simp]
  theorem ClosEnv.ext {γ : ClosEnv Γ} {σ : Subst Γ ∅} {n : ∅ ⊢ ✶}
  (ee : γ ~~ₑ σ) (e : v ~~ n) : (γ‚' v ~~ₑ ext_subst σ n)
  := by intro
  | .z => exact e
  | .s i => simp only [subst₁σ_exts]; exact ee i

  @[simp]
  theorem Eval.closEnv_equiv {γ : ClosEnv Γ} {σ : Subst Γ ∅} {m : Γ ⊢ ✶}
  (ev : γ ⊢ m ⇓ v) (ee : γ ~~ₑ σ)
  : Σ (n : ∅ ⊢ ✶), PProd (⟪σ⟫ m —↠ n) (v ~~ n)
  := open Untyped.Reduce in by match ev with
  | .lam => rename_i n; exists ⟪σ⟫ (ƛ n), by rfl, σ, ee
  | .var h ev =>
    rename_i i; have := ee i; rw [h] at this; have ⟨τ, eeτ, hτ⟩ := this
    have ⟨n, rn, en⟩ := ev.closEnv_equiv eeτ; rw [←hτ] at rn; exists n, rn
  | .ap ev ev' =>
    have ⟨n, rn, τ, eeτ, hτ⟩ := ev.closEnv_equiv ee; subst hτ
    have ⟨n', rn', en'⟩ := ev'.closEnv_equiv (ClosEnv.ext eeτ ⟨σ, ee, rfl⟩)
    refine ⟨n', ?_, en'⟩; simp only [sub_ap]; rename_i n _ m
    apply (ap_congr₁ rn).trans; unfold ext_subst at rn'
    calc ⟪τ⟫ (ƛ n) □ ⟪σ⟫ m
      _ = (ƛ (⟪exts τ⟫ n)) □ ⟪σ⟫ m := rfl
      _ —→ ⟪subst₁σ (⟪σ⟫ m)⟫ (⟪exts τ⟫ n) := lamβ
      _ = ⟪⟪subst₁σ (⟪σ⟫ m)⟫ ∘ exts τ⟫ n := Substitution.sub_sub
      _ —↠ n' := rn'
end
