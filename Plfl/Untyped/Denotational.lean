-- https://plfa.github.io/Denotational/

import Plfl.Init
import Plfl.Untyped

import Mathlib.Tactic

namespace Denotational

-- https://plfa.github.io/Denotational/#values
inductive Value : Type where
/-- No information is provided about the computation. -/
| bot : Value
/-- A single input-output mapping, from the first term to the second. -/
| fn : Value → Value → Value
/-- A function that maps inputs to outputs according to both terms. -/
| conj : Value → Value → Value
deriving BEq, DecidableEq, Repr

namespace Notation
  instance : Bot Value where bot := .bot
  instance : Sup Value where sup := .conj

  scoped infixr:70 " ⇾ " => Value.fn
end Notation

open Notation

inductive Subset : Value → Value → Type where
| bot : Subset ⊥ v
| conjL : Subset v u → Subset w u → Subset (v ⊔ w) u
| conjR₁ : Subset u v → Subset u (v ⊔ w)
| conjR₂ : Subset u w → Subset u (v ⊔ w)
| trans : Subset u v → Subset v w → Subset u w
| fn : Subset v' v → Subset w w' → Subset (v ⇾ w) (v' ⇾ w')
| dist : Subset (v ⇾ (w ⊔ w')) ((v ⇾ w) ⊔ (v ⇾ w'))

namespace Notation
  scoped infix:40 " ⊑ " => Subset
end Notation

instance : Trans Subset Subset Subset where trans := .trans

@[refl]
def Subset.refl : v ⊑ v := match v with
| ⊥ => .bot
| _ ⇾ _ => .fn refl refl
| .conj _ _ => .conjL (.conjR₁ refl) (.conjR₂ refl)

/-- The `⊔` operation is monotonic with respect to `⊑`. -/
@[simp]
def subset_subset (d₁ : v ⊑ v') (d₂ : w ⊑ w') : v ⊔ w ⊑ v' ⊔ w' :=
  .conjL (.conjR₁ d₁) (.conjR₂ d₂)

@[simp]
def conj_fn_conj : (v ⊔ v') ⇾ (w ⊔ w') ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := calc
  _ ⊑ ((v ⊔ v') ⇾ w) ⊔ ((v ⊔ v') ⇾ w') := .dist
  _ ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := open Subset in by
    apply subset_subset <;> refine .fn ?_ .refl
    · apply conjR₁; rfl
    · apply conjR₂; rfl

@[simp]
def conj_subset₁ : u ⊔ v ⊑ w → u ⊑ w := by intro
| .conjL h _ => exact h
| .conjR₁ h => refine .conjR₁ ?_; exact conj_subset₁ h
| .conjR₂ h => refine .conjR₂ ?_; exact conj_subset₁ h
| .trans h h' => refine .trans ?_ h'; exact conj_subset₁ h

@[simp]
def conj_subset₂ : u ⊔ v ⊑ w → v ⊑ w := by intro
| .conjL _ h => exact h
| .conjR₁ h => refine .conjR₁ ?_; exact conj_subset₂ h
| .conjR₂ h => refine .conjR₂ ?_; exact conj_subset₂ h
| .trans h h' => refine .trans ?_ h'; exact conj_subset₂ h

open Untyped (Context)
open Untyped.Notation

-- https://plfa.github.io/Denotational/#environments
/--
An `Env` gives meaning to a term's free vars by mapping vars to values.
-/
abbrev Env (Γ : Context) : Type := ∀ (_ : Γ ∋ ✶), Value

namespace Env
  instance : EmptyCollection (Env ∅) where emptyCollection := by intro.

  abbrev snoc (γ : Env Γ) (v : Value) : Env (Γ‚ ✶)
  | .z => v
  | .s i => γ i
end Env

namespace Notation
  scoped notation "`∅" => (∅ : Env ∅)

  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "`‚ " => Env.snoc
end Notation

namespace Env
  -- * I could have used Lisp jargons `cdr` and `car` here,
  -- * instead of the Haskell ones below...
  abbrev init (γ : Env (Γ‚ ✶)) : Env Γ := (γ ·.s)
  abbrev last (γ : Env (Γ‚ ✶)) : Value := γ .z

  @[simp]
  theorem init_last (γ : Env (Γ‚ ✶)) : γ = (γ.init`‚ γ.last) := by
    ext x; cases x <;> rfl

  /-- We extend the `⊑` relation point-wise to `Env`s. -/
  abbrev Subset (γ δ : Env Γ) : Type := ∀ (x : Γ ∋ ✶), γ x ⊑ δ x
  abbrev conj (γ δ : Env Γ) : Env Γ | x => γ x ⊔ δ x
end Env

namespace Notation
  instance : Bot (Env Γ) where bot _ := ⊥
  instance : Sup (Env γ) where sup := Env.conj

  scoped infix:40 " `⊑ " => Env.Subset
end Notation

namespace Env.Subset
  @[refl] def refl : γ `⊑ γ | _ => .refl
  @[simp] def conjR₁ (γ δ : Env Γ) : γ `⊑ (γ ⊔ δ) | _ => .conjR₁ .refl
  @[simp] def conjR₂ (γ δ : Env Γ) : δ `⊑ (γ ⊔ δ) | _ => .conjR₂ .refl
end Env.Subset

-- https://plfa.github.io/Denotational/#denotational-semantics
/--
`Eval γ m v` means that evaluating the term `m` in the environment `γ` gives `v`.
-/
inductive Eval : Env Γ → (Γ ⊢ ✶) → Value → Type where
| var : Eval γ (` i) (γ i)
| fnElim : Eval γ l (v ⇾ w) → Eval γ m v → Eval γ (l □ m) w
| fnIntro : Eval (γ`‚ v) n w → Eval γ (ƛ n) (v ⇾ w)
| botIntro : Eval γ m ⊥
| conjIntro : Eval γ m v → Eval γ m w → Eval γ m (v ⊔ w)
| sub : Eval γ m v → w ⊑ v → Eval γ m w

namespace Notation
  scoped notation:30 γ " ⊢ " m " ⇓ " v:51 => Eval γ m v
end Notation

/--
Relaxation of table lookup in application,
allowing an argument to match an input entry if the latter is less than the former.
-/
def Eval.fnElimSub (d₁ : γ ⊢ l ⇓ v₁ ⇾ w) (d₂ : γ ⊢ m ⇓ v₂) (lt : v₁ ⊑ v₂)
: γ ⊢ l □ m ⇓ w
:= d₁.fnElim <| d₂.sub lt

namespace Example
  open Untyped.Term (id delta omega twoC addC)
  open Eval

  -- `id` can be seen as a mapping table for both `⊥ ⇾ ⊥` and `(⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥)`.
  def denotId₁ : γ ⊢ id ⇓ ⊥ ⇾ ⊥ := .fnIntro .var
  def denotId₂ : γ ⊢ id ⇓ (⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥) := .fnIntro .var

  -- `id` also produces a table containing both of the previous tables.
  def denotId₃ : γ ⊢ id ⇓ (⊥ ⇾ ⊥) ⊔ ((⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥)) :=
    denotId₁.conjIntro denotId₂

  -- Oops, self application!
  def denotIdApId : `∅ ⊢ id □ id ⇓ v ⇾ v := .fnElim (.fnIntro .var) (.fnIntro .var)

  -- In `def twoC f u := f (f u)`,
  -- `f`'s table must include two entries, both `u ⇾ v` and `v ⇾ w`.
  -- `twoC` then merges those two entries into one: `u ⇾ w`.
  def denotTwoC : `∅ ⊢ twoC ⇓ (u ⇾ v ⊔ v ⇾ w) ⇾ u ⇾ w := by
    apply fnIntro; apply fnIntro; apply fnElim
    · apply sub .var; exact .conjR₂ .refl
    · apply fnElim
      · apply sub .var; exact .conjR₁ .refl
      · exact .var

  def denotDelta : `∅ ⊢ delta ⇓ (v ⇾ w ⊔ v) ⇾ w := by
    apply fnIntro; apply fnElim (v := v) <;> apply sub .var
    · exact .conjR₁ .refl
    · exact .conjR₂ .refl

  example : `∅ ⊢ omega ⇓ ⊥ := by
    apply fnElim denotDelta; apply conjIntro
    · exact fnIntro (v := ⊥) .botIntro
    · exact .botIntro

  def denotOmega : `∅ ⊢ omega ⇓ ⊥ := .botIntro

  -- https://plfa.github.io/Denotational/#exercise-denot-plus%E1%B6%9C-practice

  -- For `def addC m n u v := (m u) (n u v)` we have the following mapping table:
  -- · n u v = w
  -- · m u w = x

  def denotAddC
  : let m := u ⇾ w ⇾ x
    let n := u ⇾ v ⇾ w
    `∅ ⊢ addC ⇓ m ⇾ n ⇾ u ⇾ v ⇾ x
  := by apply_rules [fnIntro, fnElim, var]
end Example

-- https://plfa.github.io/Denotational/#denotations-and-denotational-equality
/--
A denotational semantics can be seen as a function from a term
to some relation between `Env`s and `Value`s.
-/
abbrev Denot (Γ : Context) : Type 1 := Env Γ → Value → Type

def ℰ (m : Γ ⊢ ✶) : Denot Γ | γ, v => γ ⊢ m ⇓ v
