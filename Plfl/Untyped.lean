-- https://plfa.github.io/Untyped/

import Plfl.Init

import Mathlib.Tactic

set_option tactic.simp.trace true

namespace Untyped

-- https://plfa.github.io/Untyped/#types
inductive Ty where
/-- Native natural type made of 𝟘 and ι. -/
| star: Ty
deriving BEq, DecidableEq, Repr

namespace Notation
  scoped notation " ✶ " => Ty.star
end Notation

open Notation

-- https://plfa.github.io/Untyped/#exercise-type-practice
instance : Ty ≃ Unit where
  toFun _ := ()
  invFun _ := ✶
  left_inv := by simp only [Function.LeftInverse, implies_true]
  right_inv := by simp only

instance : Unique Ty where
  default := ✶
  uniq := by simp

-- https://plfa.github.io/Untyped/#contexts
abbrev Context : Type := List Ty

namespace Context
  abbrev snoc (Γ : Context) (a : Ty) : Context := a :: Γ
  abbrev lappend (Γ : Context) (Δ : Context) : Context := Δ ++ Γ
end Context

namespace Notation
  open Context

  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚ " => snoc
  scoped infixl:45 "‚‚ " => lappend
end Notation

-- https://plfa.github.io/Untyped/#exercise-context%E2%84%95-practice
instance Context.equiv_nat : Context ≃ ℕ where
  toFun := List.length
  invFun := (List.replicate · ✶)
  left_inv := left_inv
  right_inv := by intro; simp only [List.length_replicate]
  where
    left_inv := by intro
    | [] => trivial
    | ✶ :: ss => calc List.replicate (✶ :: ss).length ✶
      _ = List.replicate (ss.length + 1) ✶ := by rw [List.length_cons ✶ ss]
      _ = ✶ :: List.replicate ss.length ✶ := by rw [List.replicate_succ ✶ ss.length]
      _ = ✶ :: ss := by have := left_inv ss; simp_all only

instance : Coe ℕ Context where coe := Context.equiv_nat.invFun

-- https://plfa.github.io/Untyped/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ‚ t) t
| s : Lookup Γ t → Lookup (Γ‚ t') t
deriving DecidableEq, Repr

namespace Notation
  open Lookup

  scoped infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  scoped syntax "get_elem" (ppSpace term) : term
  scoped macro_rules | `(term| get_elem $n) => match n.1.toNat with
  | 0 => `(term| Lookup.z)
  | n+1 => `(term| Lookup.s (get_elem $(Lean.quote n)))

  scoped macro " ♯" n:term:90 : term => `(get_elem $n)
end Notation

-- https://plfa.github.io/Untyped/#terms-and-the-scoping-judgment
inductive Term : Context → Ty → Type where
-- Lookup
| var : Γ ∋ a → Term Γ a
-- Lambda
| lam : Term (Γ‚ ✶ /- a -/) ✶ /- b -/ → Term Γ ✶ /- (a =⇒ b) -/
| ap : Term Γ ✶ /- (a =⇒ b) -/ → Term Γ ✶ /- a -/ → Term Γ ✶ /- b -/
deriving DecidableEq, Repr

namespace Notation
  open Term

  scoped infix:40 " ⊢ " => Term

  scoped prefix:50 " ƛ " => lam
  -- scoped prefix:50 " μ " => mu
  -- scoped notation " 𝟘? " => case
  scoped infixr:min " $ " => ap
  scoped infixl:70 " □ " => ap
  -- scoped infixl:70 " ⋄ "   => mulP
  -- scoped prefix:80 " ι " => succ
  scoped prefix:90 " ` " => var

  -- scoped notation " 𝟘 " => zero
  -- scoped notation " ◯ " => unit

  -- https://plfa.github.io/Untyped/#writing-variables-as-numerals
  scoped macro " #" n:term:90 : term => `(`♯$n)
end Notation

-- https://plfa.github.io/Untyped/#test-examples
namespace Term
  abbrev twoC : Γ ⊢ ✶ := ƛ ƛ (#1 $ #1 $ #0)
  abbrev fourC : Γ ⊢ ✶ := ƛ ƛ (#1 $ #1 $ #1 $ #1 $ #0)
  abbrev addC : Γ ⊢ ✶ := ƛ ƛ ƛ ƛ (#3 □ #1 $ #2 □ #1 □ #0)
  abbrev four'C : Γ ⊢ ✶ := addC □ twoC □ twoC
end Term

namespace Subst
  -- https://plfa.github.io/Untyped/#renaming
  /--
  If one context maps to another,
  the mapping holds after adding the same variable to both contexts.
  -/
  @[simp]
  def ext : (∀ {a}, Γ ∋ a → Δ ∋ a) → Γ‚ b ∋ a → Δ‚ b ∋ a := by
    intro ρ; intro
    | .z => exact .z
    | .s x => refine .s ?_; exact ρ x

  /--
  If one context maps to another,
  then the type judgements are the same in both contexts.
  -/
  def rename : (∀ {a}, Γ ∋ a → Δ ∋ a) → Γ ⊢ a → Δ ⊢ a := by
    intro ρ; intro
    | ` x => exact ` (ρ x)
    | ƛ n => exact ƛ (rename (ext ρ) n)
    | l □ m => exact rename ρ l □ rename ρ m

  abbrev shift : Γ ⊢ a → Γ‚ b ⊢ a := rename .s

  -- https://plfa.github.io/Untyped/#simultaneous-substitution
  @[simp]
  def exts : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ‚ b ∋ a → Δ‚ b ⊢ a := by
    intro σ; intro
    | .z => exact `.z
    | .s x => apply shift; exact σ x

  /--
  General substitution for multiple free variables.
  If the variables in one context maps to some terms in another,
  then the type judgements are the same before and after the mapping,
  i.e. after replacing the free variables in the former with (expanded) terms.
  -/
  def subst : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ ⊢ a → Δ ⊢ a := by
    intro σ; intro
    | ` i => exact σ i
    | ƛ n => exact ƛ (subst (exts σ) n)
    | l □ m => exact subst σ l □ subst σ m

  -- https://plfa.github.io/Untyped/#single-substitution
  abbrev subst₁σ (v : Γ ⊢ b) : ∀ {a}, Γ‚ b ∋ a → Γ ⊢ a := by
    introv; intro
    | .z => exact v
    | .s x => exact ` x

  /--
  Substitution for one free variable `v` in the term `n`.
  -/
  @[simp]
  abbrev subst₁ (v : Γ ⊢ b) (n : Γ‚ b ⊢ a) : Γ ⊢ a := by
    refine subst ?_ n; exact subst₁σ v
end Subst

open Subst

namespace Notation
  scoped infixr:90 " ⇸ " => subst₁
  scoped infixl:90 " ⇷ " => flip subst₁
end Notation

-- https://plfa.github.io/Untyped/#neutral-and-normal-terms
mutual
  inductive Neutral : Γ ⊢ a → Type
  | var : (x : Γ ∋ a) → Neutral (` x)
  | ap : Neutral l → Normal m → Neutral (l □ m)
  deriving Repr

  inductive Normal : Γ ⊢ a → Type
  | norm : Neutral m → Normal m
  | lam : Normal n → Normal (ƛ n)
  deriving Repr
end

-- instance : Coe (Neutral t) (Normal t) where coe := .norm

namespace Notation
  open Neutral Normal

  scoped prefix:60 " ′" => norm
  scoped macro " #′" n:term:90 : term => `(var (♯$n))

  scoped prefix:50 " ƛ " => lam
  scoped infixr:min " $ " => ap
  scoped infixl:70 " □ " => ap
  scoped prefix:90 " ` " => var
end Notation

example : Normal (Term.twoC (Γ := ∅)) := ƛ ƛ (′#′1 □ (′#′1 □ (′#′0)))

-- https://plfa.github.io/Untyped/#reduction-step

-- https://plfa.github.io/Untyped/#reflexive-and-transitive-closure

-- https://plfa.github.io/Untyped/#example-reduction-sequence

-- https://plfa.github.io/Untyped/#progress

-- https://plfa.github.io/Untyped/#evaluation

-- https://plfa.github.io/Untyped/#example

-- https://plfa.github.io/Untyped/#naturals-and-fixpoint

-- https://plfa.github.io/Untyped/#multi-step-reduction-is-transitive

-- https://plfa.github.io/Untyped/#multi-step-reduction-is-a-congruence
