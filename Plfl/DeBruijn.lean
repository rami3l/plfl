-- https://plfa.github.io/DeBruijn/

import Mathlib.Tactic

set_option tactic.simp.trace true

-- Sorry, nothing is inherited from previous chapters here. We have to start over.

-- https://plfa.github.io/DeBruijn/#types
inductive Ty where
| nat : Ty
| fn : Ty → Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Ty
  notation "ℕt" => nat
  infixr:70 " =⇒ " => fn

  example : Ty := (ℕt =⇒ ℕt) =⇒ ℕt

  @[simp]
  theorem t_to_t'_ne_t (t t' : Ty) : (t =⇒ t') ≠ t := by
    by_contra h; match t with
    | nat => trivial
    | fn ta tb => injection h; have := t_to_t'_ne_t ta tb; contradiction
end Ty

-- https://plfa.github.io/DeBruijn/#contexts
abbrev Context : Type := List Ty

open List

namespace Context
  abbrev snoc : Context → Ty → Context := flip (· :: ·)
  infixl:50 " :< " => snoc
end Context

-- https://plfa.github.io/DeBruijn/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ :< t) t
| s : Lookup Γ t → Lookup (Γ :< t') t
deriving DecidableEq, Repr

namespace Lookup
  infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.z)
  | n+1 => `(tactic| apply Lookup.s; get_elem $(Lean.quote n))

  macro " ♯ " n:term:90 : term => `(by get_elem $n)

  example : ∅ :< ℕt =⇒ ℕt :< ℕt ∋ ℕt := .z
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ∋ ℕt := ♯0
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ∋ ℕt =⇒ ℕt := .s .z
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ∋ ℕt =⇒ ℕt := ♯1
end Lookup

-- https://plfa.github.io/DeBruijn/#terms-and-the-typing-judgment
/--
A term with typing judgement embedded in itself.
-/
inductive Term : Context → Ty → Type where
| var : Γ ∋ a → Term Γ a
| lam : Term (Γ :< a) b → Term Γ (a =⇒ b)
| ap : Term Γ (a =⇒ b) → Term Γ a → Term Γ b
| zero : Term Γ ℕt
| succ : Term Γ ℕt → Term Γ ℕt
| case : Term Γ ℕt → Term Γ a → Term (Γ :< ℕt) a → Term Γ a
| mu : Term (Γ :< a) a → Term Γ a
deriving DecidableEq, Repr

namespace Term
  infix:40 " ⊢ " => Term

  prefix:50 " ƛ " => lam
  prefix:50 " μ " => mu
  notation " 𝟘? " => case
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  prefix:80 " ι " => succ
  prefix:90 " ` " => var
  notation " 𝟘 " => zero

  -- https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
  macro " # " n:term:90 : term => `(`♯$n)

  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt := #0
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt =⇒ ℕt := #1
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt := #1 $ #0
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt := #1 $ #1 $ #0
  example : ∅ :< ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
  example : ∅ ⊢ (ℕt =⇒ ℕt) =⇒ ℕt =⇒ ℕt := ƛ ƛ (#1 $ #1 $ #0)

  @[simp]
  def ofNat : ℕ → Term Γ ℕt
  | 0 => zero
  | n + 1 => succ <| ofNat n

  instance : Coe ℕ (Term Γ ℕt) where coe := ofNat
  instance : OfNat (Term Γ ℕt) n where ofNat := ofNat n

  -- https://plfa.github.io/DeBruijn/#test-examples
  example : Γ ⊢ ℕt := ι ι 𝟘
  example : Γ ⊢ ℕt := 2

  abbrev add : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) (#0) (ι (#3 □ #0 □ #1)))

  example : Γ ⊢ ℕt := add □ 2 □ 2

  /--
  The Church numeral Ty.
  -/
  abbrev Ch (t : Ty) : Ty := (t =⇒ t) =⇒ t =⇒ t

  abbrev succC : Γ ⊢ ℕt =⇒ ℕt := ƛ #0
  abbrev twoC : Γ ⊢ Ch a := ƛ ƛ (#1 $ #1 $ #0)
  abbrev addC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ #1 $ #2 □ #1 □ #0)
  example : Γ ⊢ ℕt := addC □ twoC □ twoC □ succC □ 𝟘

  -- https://plfa.github.io/DeBruijn/#exercise-mul-recommended
  abbrev mulC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ (#2 □ #1) □ #0)
end Term

-- https://plfa.github.io/DeBruijn/#renaming
