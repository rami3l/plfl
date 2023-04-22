-- https://plfa.github.io/Properties/

import Plfl.Lambda

-- https://plfa.github.io/Properties/#values-do-not-reduce
theorem Value.not_reduce' : Value m → (Σ n, m —→ n) → False
:= open Term.Reduce in by
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
section canonical
-- Well-typed values must take one of a small number of canonical forms, which provide an analogue of the Value relation that relates values to their types. A lambda expression must have a function type, and a zero or successor expression must be a natural. Further, the body of a function must be well typed in a context containing only its bound variable, and the argument of successor must itself be canonical:
-- infix  4 Canonical_⦂_

-- data Canonical_⦂_ : Term → Type → Set where

--   C-ƛ : ∀ {x A N B}
--     → ∅ , x ⦂ A ⊢ N ⦂ B
--       -----------------------------
--     → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

--   C-zero :
--       --------------------
--       Canonical `zero ⦂ `ℕ

--   C-suc : ∀ {V}
--     → Canonical V ⦂ `ℕ
--       ---------------------
--     → Canonical `suc V ⦂ `ℕ
-- Show that Canonical V ⦂ A is isomorphic to (∅ ⊢ V ⦂ A) × (Value V), that is, the canonical forms are exactly the well-typed values.
inductive Canonical : Term → Ty → Type where
| can_lam : (∅ :< x ⦂ tx ⊢ n ⦂ tn) → Canonical (ƛ x : n) (tx =⇒ tn)
| can_zero : Canonical 𝟘 ℕt
| can_succ : Canonical n ℕt → Canonical (ι n) ℕt
end canonical

-- https://plfa.github.io/Properties/#progress
