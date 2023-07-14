-- https://plfa.github.io/Untyped/

import Plfl.Init

import Mathlib.Tactic

namespace Untyped

-- https://plfa.github.io/Untyped/#types
inductive Ty where
| star: Ty
deriving BEq, DecidableEq, Repr

namespace Notation
  scoped notation "✶" => Ty.star
end Notation

open Notation

-- https://plfa.github.io/Untyped/#exercise-type-practice
instance : Ty ≃ Unit where
  toFun _ := ()
  invFun _ := ✶
  left_inv _ := by simp only
  right_inv _ := by simp only

instance : Unique Ty where
  default := ✶
  uniq := by simp only [implies_true]

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
deriving DecidableEq

namespace Notation
  open Lookup

  scoped infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  scoped syntax "get_elem" (ppSpace term) : term
  scoped macro_rules | `(term| get_elem $n) => match n.1.toNat with
  | 0 => `(term| Lookup.z)
  | n+1 => `(term| Lookup.s (get_elem $(Lean.quote n)))

  scoped macro "♯" n:term:90 : term => `(get_elem $n)
end Notation

def Lookup.toNat : (Γ ∋ a) → ℕ
| .z => 0
| .s i => i.toNat + 1

instance : Repr (Γ ∋ a) where reprPrec i n := "♯" ++ reprPrec i.toNat n

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

  scoped prefix:50 "ƛ " => lam
  scoped infixr:min " $ " => ap
  scoped infixl:70 " □ " => ap
  scoped prefix:90 "` " => var

  -- https://plfa.github.io/Untyped/#writing-variables-as-numerals
  scoped macro "#" n:term:90 : term => `(`♯$n)
end Notation

namespace Term
  -- https://plfa.github.io/Untyped/#test-examples
  abbrev twoC : Γ ⊢ ✶ := ƛ ƛ (#1 $ #1 $ #0)
  abbrev fourC : Γ ⊢ ✶ := ƛ ƛ (#1 $ #1 $ #1 $ #1 $ #0)
  abbrev addC : Γ ⊢ ✶ := ƛ ƛ ƛ ƛ (#3 □ #1 $ #2 □ #1 □ #0)
  abbrev fourC' : Γ ⊢ ✶ := addC □ twoC □ twoC

  def church (n : ℕ) : Γ ⊢ ✶ := ƛ ƛ applyN n
  where
    applyN
    | 0 => #0
    | n + 1 => #1 □ applyN n
end Term

namespace Subst
  -- https://plfa.github.io/Untyped/#renaming
  /--
  If one context maps to another,
  the mapping holds after adding the same variable to both contexts.
  -/
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
  abbrev subst₁ (v : Γ ⊢ b) (n : Γ‚ b ⊢ a) : Γ ⊢ a := by
    refine subst ?_ n; exact subst₁σ v
end Subst

open Subst

namespace Notation
  scoped infixr:90 " ⇸ " => subst₁
  scoped infixl:90 " ⇷ " => flip subst₁

  scoped macro " ⟪" σ:term "⟫ " : term => `(subst $σ)
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

  scoped prefix:60 " ′" => Normal.norm
  scoped macro "#′" n:term:90 : term => `(var (♯$n))

  scoped prefix:50 "ƛₙ " => lam
  scoped infixr:min " $ₙ " => ap
  scoped infixl:70 " □ₙ " => ap
  scoped prefix:90 "`ₙ " => var
end Notation

example : Normal (Term.twoC (Γ := ∅)) := ƛₙ ƛₙ (′#′1 □ₙ (′#′1 □ₙ (′#′0)))

-- https://plfa.github.io/Untyped/#reduction-step
/--
`Reduce t t'` says that `t` reduces to `t'` via a given step.

_Note: This time there's no need to generate data out of `Reduce t t'`,
so it can just be a `Prop`._
-/
inductive Reduce : (Γ ⊢ a) → (Γ ⊢ a) → Prop where
| lamβ : Reduce ((ƛ n) □ v) (n ⇷ v)
| lamζ : Reduce n n' → Reduce (ƛ n) (ƛ n')
| apξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
| apξ₂ : Reduce m m' → Reduce (v □ m) (v □ m')

-- https://plfa.github.io/Untyped/#exercise-variant-1-practice
inductive Reduce' : (Γ ⊢ a) → (Γ ⊢ a) → Type where
| lamβ : Normal (ƛ n) → Normal v → Reduce' ((ƛ n) □ v) (n ⇷ v)
| lamζ : Reduce' n n' → Reduce' (ƛ n) (ƛ n')
| apξ₁ : Reduce' l l' → Reduce' (l □ m) (l' □ m)
| apξ₂ : Normal v → Reduce' m m' → Reduce' (v □ m) (v □ m')

-- https://plfa.github.io/Untyped/#exercise-variant-2-practice
inductive Reduce'' : (Γ ⊢ a) → (Γ ⊢ a) → Type where
| lamβ : Reduce'' ((ƛ n) □ (ƛ v)) (n ⇷ (ƛ v))
| apξ₁ : Reduce'' l l' → Reduce'' (l □ m) (l' □ m)
| apξ₂ : Reduce'' m m' → Reduce'' (v □ m) (v □ m')
/-
Reduction of `four''C` under this variant might go as far as
`ƛ ƛ (twoC □ #1 $ (twoC □ #1 □ #0))` and get stuck,
since the next step uses `lamζ` which no longer exists.
-/

-- https://plfa.github.io/Untyped/#reflexive-and-transitive-closure
/--
A reflexive and transitive closure,
defined as a sequence of zero or more steps of the underlying relation `—→`.

_Note: Since `Reduce t t' : Prop`, `Clos` can be defined directly from `Reduce`._
-/
abbrev Reduce.Clos {Γ a} := Relation.ReflTransGen (α := Γ ⊢ a) Reduce

namespace Notation
  -- https://plfa.github.io/DeBruijn/#reflexive-and-transitive-closure
  scoped infix:40 " —→ " => Reduce
  scoped infix:20 " —↠ " => Reduce.Clos
end Notation

namespace Reduce.Clos
  @[refl] abbrev refl : m —↠ m := .refl
  abbrev tail : (m —↠ n) → (n —→ n') → (m —↠ n') := .tail
  abbrev head : (m —→ n) → (n —↠ n') → (m —↠ n') := .head
  abbrev single : (m —→ n) → (m —↠ n) := .single

  instance : Coe (m —→ n) (m —↠ n) where coe r := .single r

  instance : Trans (α := Γ ⊢ a) Clos Clos Clos where trans := .trans
  instance : Trans (α := Γ ⊢ a) Clos Reduce Clos where trans c r := c.tail r
  instance : Trans (α := Γ ⊢ a) Reduce Reduce Clos where trans r r' := .tail r r'
  instance : Trans (α := Γ ⊢ a) Reduce Clos Clos where trans r c := .head r c
end Reduce.Clos

namespace Reduce
  -- https://plfa.github.io/Untyped/#example-reduction-sequence
  open Term

  example : fourC' (Γ := ∅) —↠ fourC := calc addC □ twoC □ twoC
    _ —→ (ƛ ƛ ƛ (twoC □ #1 $ (#2 □ #1 □ #0))) □ twoC := by apply_rules [apξ₁, lamβ]
    _ —→ ƛ ƛ (twoC □ #1 $ (twoC □ #1 □ #0)) := by exact lamβ
    _ —→ ƛ ƛ ((ƛ (#2 $ #2 $ #0)) $ (twoC □ #1 □ #0)) := by apply_rules [lamζ, apξ₁, lamβ]
    _ —→ ƛ ƛ (#1 $ #1 $ (twoC □ #1 □ #0)) := by apply_rules [lamζ, lamβ]
    _ —→ ƛ ƛ (#1 $ #1 $ ((ƛ (#2 $ #2 $ #0)) □ #0)) := by apply_rules [lamζ, apξ₁, apξ₂, lamβ]
    _ —→ ƛ ƛ (#1 $ #1 $ #1 $ #1 $ #0) := by apply_rules [lamζ, apξ₁, apξ₂, lamβ]
end Reduce

-- https://plfa.github.io/Untyped/#progress
/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
inductive Progress (m : Γ ⊢ a) where
| step : (m —→ n) → Progress m
| done : Normal m → Progress m

/--
If a term is well-scoped, then it satisfies progress.
-/
def Progress.progress : (m : Γ ⊢ a) → Progress m := open Reduce in by
  intro
  | ` x => apply done; exact ′`ₙ x
  | ƛ n =>
    have : sizeOf n < sizeOf (ƛ n) := by simp only [
      Term.lam.sizeOf_spec, lt_add_iff_pos_left, add_pos_iff, true_or
    ]
    match progress n with
    | .done n => apply done; exact ƛₙ n
    | .step n => apply step; exact lamζ n
  | ` x □ m =>
    have : sizeOf m < sizeOf (` x □ m) := by simp only [
      Term.ap.sizeOf_spec, Term.var.sizeOf_spec, Ty.star.sizeOf_spec,
      lt_add_iff_pos_left, add_pos_iff, true_or, or_self
    ]
    match progress m with
    | .done m => apply done; exact ′`ₙx □ₙ m
    | .step m => apply step; exact apξ₂ m
  | (ƛ n) □ m => apply step; exact lamβ
  | l@(_ □ _) □ m =>
    have : sizeOf l < sizeOf (l □ m) := by simp_arith
    match progress l with
    | .step l => simp_all only [namedPattern]; apply step; exact apξ₁ l
    | .done (′l') =>
      simp_all only [namedPattern]; rename_i h; simp only [h.symm, Term.ap.sizeOf_spec]
      have : sizeOf m < sizeOf (l □ m) := by
        aesop_subst h
        simp only [Term.ap.sizeOf_spec, lt_add_iff_pos_left, add_pos_iff, true_or, or_self]
      match progress m with
      | .done m => apply done; exact ′l' □ₙ m
      | .step m => apply step; exact apξ₂ m

open Progress (progress)

-- https://plfa.github.io/Untyped/#evaluation
inductive Result (n : Γ ⊢ a) where
| done (val : Normal n)
| dnf
deriving Repr

inductive Steps (l : Γ ⊢ a) where
| steps : ∀{n : Γ ⊢ a}, (l —↠ n) → Result n → Steps l

def eval (gas : ℕ) (l : ∅ ⊢ a) : Steps l :=
  if gas = 0 then
    ⟨.refl, .dnf⟩
  else
    match progress l with
    | .done v => .steps .refl <| .done v
    | .step r =>
      let ⟨rs, res⟩ := eval (gas - 1) (by trivial)
      ⟨Trans.trans r rs, res⟩

namespace Term
  abbrev id : Γ ⊢ ✶ := ƛ #0
  abbrev delta : Γ ⊢ ✶ := ƛ #0 □ #0
  abbrev omega : Γ ⊢ ✶ := delta □ delta

  -- https://plfa.github.io/Untyped/#naturals-and-fixpoint
  /-
  The Scott encoding:
  zero := λ _ z => z
  succ n := λ s _ => s n

  e.g. one = succ zero
          = λ s _ => s zero
          = λ s _ => s (λ _ z => z)
  -/
  abbrev zeroS : Γ ⊢ ✶ := ƛ ƛ #0
  abbrev succS (m : Γ ⊢ ✶) : Γ ⊢ ✶ := (ƛ ƛ ƛ (#1 □ #2)) □ m
  abbrev caseS (l : Γ ⊢ ✶) (m : Γ ⊢ ✶) (n : Γ‚ ✶ ⊢ ✶) : Γ ⊢ ✶ := l □ (ƛ n) □ m

  /--
  The Y combinator: `Y f := (λ x => f (x x)) (λ x => f (x x))`
  -/
  abbrev mu (n : Γ‚ ✶ ⊢ ✶) : Γ ⊢ ✶ := (ƛ (ƛ (#1 $ #0 $ #0)) □ (ƛ (#1 $ #0 $ #0))) □ (ƛ n)
end Term

namespace Notation
  open Term

  scoped prefix:50 "μ " => mu
  scoped prefix:80 "ι " => succS
  scoped notation "𝟘" => zeroS
  scoped notation "𝟘? " => caseS
end Notation

-- https://plfa.github.io/Untyped/#example
section examples
  open Term

  abbrev addS : Γ ⊢ ✶ := μ ƛ ƛ (𝟘? (#1) (#0) (ι (#3 □ #0 □ #1)))

  -- https://plfa.github.io/Untyped/#exercise-multiplication-untyped-recommended
  abbrev mulS : Γ ⊢ ✶ := μ ƛ ƛ (𝟘? (#1) 𝟘 (addS □ #1 $ #3 □ #0 □ #1))

  abbrev oneS : Γ ⊢ ✶ := ι 𝟘

  abbrev twoS : Γ ⊢ ✶ := ι ι 𝟘
  abbrev twoS'' : Γ ⊢ ✶ := mulS □ twoS □ oneS

  abbrev fourS : Γ ⊢ ✶ := ι ι twoS
  abbrev fourS' : Γ ⊢ ✶ := addS □ twoS □ twoS
  abbrev fourS'' : Γ ⊢ ✶ := mulS □ twoS □ twoS

  abbrev evalRes (l : ∅ ⊢ a) (gas := 100) := (eval gas l).3

  #eval evalRes (gas := 3) fourC'
  #eval evalRes fourC'

  #eval evalRes oneS

  #eval evalRes twoS
  #eval evalRes twoS''

  #eval evalRes fourS
  #eval evalRes fourS'
  #eval evalRes fourS''
end examples

-- https://plfa.github.io/Untyped/#multi-step-reduction-is-transitive

/-
Nothing to do.
The `Trans` instance has been automatically generated by `Relation.ReflTransGen`.
See: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html#Relation.instIsTransReflTransGen>
-/

-- https://plfa.github.io/Untyped/#multi-step-reduction-is-a-congruence
/--
LEAN is being a bit weird here.
Default structural recursion cannot be used since it depends on sizeOf,
however this won't work for `Prop`.
We have to find another way.
-/
theorem Reduce.ap_congr₁ (rs : l —↠ l') : (l □ m) —↠ (l' □ m) := by
  refine rs.head_induction_on .refl ?_
  · introv; intro r _ rs; refine .head ?_ rs; exact apξ₁ r


theorem Reduce.ap_congr₂ (rs : m —↠ m') : (l □ m) —↠ (l □ m') := by
  refine rs.head_induction_on .refl ?_
  · introv; intro r _ rs; refine .head ?_ rs; exact apξ₂ r

theorem Reduce.lam_congr (rs : n —↠ n') : (ƛ n —↠ ƛ n') := by
  refine rs.head_induction_on .refl ?_
  · introv; intro r _ rs; refine .head ?_ rs; exact lamζ r
