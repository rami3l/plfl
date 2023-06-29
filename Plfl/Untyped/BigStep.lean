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
An environment in call-by-name is a mapping from variables to closures.
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
noncomputable def Clos.Equiv : Clos → (∅ ⊢ ✶) → Type
| .clos (Γ := Γ) m γ, n =>
  Σ (σ : Subst Γ ∅), PProd (∀ i, Clos.Equiv (γ i) (σ i)) (n = ⟪σ⟫ m)

abbrev ClosEnv.Equiv (γ : ClosEnv Γ) (σ : Subst Γ ∅) : Type :=
  ∀ i, Clos.Equiv (γ i) (σ i)

namespace Notation
  -- The default precedence in Agda is 20.
  -- See: <https://agda.readthedocs.io/en/v2.6.1/language/mixfix-operators.html#precedence>
  scoped infix:20 " ~~ " => Clos.Equiv
  scoped infix:20 " ~~ₑ " => ClosEnv.Equiv
end Notation

section
  open Untyped.Subst
  open Substitution

  @[simp] lemma ClosEnv.empty_equiv_ids : ∅ ~~ₑ ids := by intro.

  @[simp]
  abbrev ext_subst (σ : Subst Γ Δ) (n : Δ ⊢ ✶) : Subst (Γ‚ ✶) Δ :=
    (n ⇸ ·) ∘ exts σ

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
  theorem Eval.closEnvEquiv {γ : ClosEnv Γ} {σ : Subst Γ ∅} {m : Γ ⊢ ✶}
  (ev : γ ⊢ m ⇓ v) (ee : γ ~~ₑ σ)
  : Σ (n : ∅ ⊢ ✶), PProd (⟪σ⟫ m —↠ n) (v ~~ n)
  := open Untyped.Reduce in by match ev with
  | .lam => rename_i n; exists ⟪σ⟫ (ƛ n), by rfl, σ, ee
  | .var h ev =>
    rename_i i; have := ee i; rw [h] at this; have ⟨τ, eeτ, hτ⟩ := this
    have ⟨n, rn, en⟩ := ev.closEnvEquiv eeτ; rw [←hτ] at rn; exists n, rn
  | .ap ev ev' =>
    have ⟨n, rn, τ, eeτ, hτ⟩ := ev.closEnvEquiv ee; subst hτ
    have ⟨n', rn', en'⟩ := ev'.closEnvEquiv (ClosEnv.ext eeτ ⟨σ, ee, rfl⟩)
    refine ⟨n', ?_, en'⟩; simp only [sub_ap]; rename_i n _ m
    apply (ap_congr₁ rn).trans; unfold ext_subst at rn'
    calc ⟪τ⟫ (ƛ n) □ ⟪σ⟫ m
      _ = (ƛ (⟪exts τ⟫ n)) □ ⟪σ⟫ m := rfl
      _ —→ ⟪subst₁σ (⟪σ⟫ m)⟫ (⟪exts τ⟫ n) := lamβ
      _ = ⟪⟪subst₁σ (⟪σ⟫ m)⟫ ∘ exts τ⟫ n := Substitution.sub_sub
      _ —↠ n' := rn'

  /--
  If call-by-name can produce a value,
  then the program can be reduced to a λ-abstraction via β-rules.
  -/
  @[simp]
  theorem Eval.cbn_reduce {m : ∅ ⊢ ✶} {δ : ClosEnv Δ} {n' : Δ‚ ✶ ⊢ ✶}
  (ev : ∅ ⊢ m ⇓ .clos (ƛ n') δ)
  : ∃ (n : ∅‚ ✶ ⊢ ✶), m —↠ ƛ n
  := by
    have ⟨n, rn, σ, _, h⟩ := ev.closEnvEquiv ClosEnv.empty_equiv_ids
    subst h; rw [sub_ids] at rn; exists ⟪exts σ⟫ n'
end

-- https://plfa.github.io/BigStep/#exercise-big-alt-implies-multi-practice
namespace BySubst

-- https://github.com/L-TChen/ModalTypeTheory/blob/a4d3cf67236716fa324daa3e5a929f38a33c39e9/src/STLC/BigStep.agda#L96-L121
-- https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf
inductive Eval : (Γ ⊢ ✶) → (Γ ⊢ ✶) → Type where
-- Hmmm, it's all ƛ's after all?
| lam : ∀ {n : ∅‚ ✶ ⊢ ✶}, Eval (ƛ n) (ƛ n)
| ap : Eval l (ƛ m) → Eval (m ⇷ n) v → Eval (l □ n) v

namespace Notation
  scoped infix:50 " ⇓' "=> Eval
end Notation

open Notation

@[simp]
theorem Eval.determ : m ⇓' v → m ⇓' v' → v = v' := by intro
| .lam, .lam => rfl
| .ap mc mc₁, .ap mc' mc₁' =>
  have := mc.determ mc'; injection this; subst_vars; exact mc₁.determ mc₁'

open Untyped.Reduce
open Untyped.Subst

/--
If call-by-name can produce a value,
then the program can be reduced to a λ-abstraction via β-rules.
-/
@[simp]
theorem Eval.cbn_reduce {n : ∅‚ ✶ ⊢ ✶} (ev : m ⇓' (ƛ n)) : m —↠ ƛ n := by
  match ev with
  | .lam => rfl
  | .ap evl evmn' =>
    rename_i l m n'
    have rl := cbn_reduce evl; have rmn' := cbn_reduce evmn'
    calc l □ n'
      _ —↠ (ƛ m) □ n' := ap_congr₁ rl
      _ —→ m ⇷ n' := lamβ
      _ —↠ (ƛ n) := rmn'
