-- https://plfa.github.io/DeBruijn/

import Mathlib.Tactic

set_option tactic.simp.trace true

-- Sorry, nothing is inherited from previous chapters here. We have to start over.


-- infix  4 _⊢_
-- infix  4 _∋_
-- infixl 5 _,_
-- infixr 7 _⇒_
-- infix  5 ƛ_
-- infix  5 μ_
-- infixl 7 _·_
-- infix  8 `suc_
-- infix  9 `_
-- infix  9 S_
-- infix  9 #_

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

namespace Context
  abbrev nil : Context := []

  abbrev snoc : Context → Ty → Context := flip (· :: ·)
  infixl:50 " :< " => snoc

  abbrev has_member (ts : Context) (t : Ty) : Prop := t ∈ ts
  infix:40 " ∋ " => has_member
end Context

-- https://plfa.github.io/DeBruijn/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ :< t) t
| s : Lookup Γ t → Lookup (Γ :< t') t

namespace Lookup
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ∋ ℕt := by trivial
  example : ∅ :< ℕt =⇒ ℕt :< ℕt ∋ ℕt =⇒ ℕt := by trivial
end Lookup

-- Using Elixir notation instead of the native #1...
-- example := &1
