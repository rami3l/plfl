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
deriving DecidableEq

namespace Lookup
  infix:40 " ∋ " => Lookup

  def getElem {Γ : Context} (n : Fin (Γ.length)) : Γ ∋ Γ[n] :=
    match Γ, n with
    | _ :: _, ⟨0, _⟩ => .z
    | _ :: _, ⟨n + 1, h⟩ => .s (getElem ⟨n, Nat.le_of_succ_le_succ h⟩)

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  macro " ♯ " n:term:90 : term => `(getElem ⟨$n, by trivial⟩)

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
deriving DecidableEq

namespace Term
  infix:40 " ⊢ " => Term

  prefix:50 " ƛ " => lam
  prefix:50 " μ " => mu
  notation:max " 𝟘? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  prefix:80 " ι " => succ
  prefix:90 " ` " => var
  notation " 𝟘 " => zero

  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt := `♯0
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt =⇒ ℕt := `♯1
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ⊢ ℕt := `♯1 □ `♯0
end Term
