-- https://plfa.github.io/More/

import Plfl

import Mathlib.Tactic

set_option tactic.simp.trace true

-- This module was adapted based on the original one for <https://plfa.github.io/DeBruijn/>.

-- https://plfa.github.io/More/#types
inductive Ty where
/-- Native natural type made of 𝟘 and ι. -/
| nat : Ty
/-- Primitive natural type, a simple wrapper around LEAN's own ℕ type. -/
| natP : Ty
/-- Product type. -/
| prod : Ty → Ty → Ty
/-- Sum type. -/
| sum : Ty → Ty → Ty
/-- Arrow type. -/
| fn : Ty → Ty → Ty
/-- Unit type. -/
| unit : Ty
/-- Void type. -/
| void : Ty
/-- List type. -/
| list : Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Ty
  notation "ℕt" => nat
  notation "ℕp" => natP

  -- Operator overloadings for `prod` and `sum` types.
  instance : HMul Ty Ty Ty where hMul := prod
  instance : HAdd Ty Ty Ty where hAdd := sum

  infixr:70 " =⇒ " => fn
  notation " ◯ " => unit
  notation " ∅ " => void

  example : Ty := (ℕt =⇒ ℕt) =⇒ ℕt
  example : Ty := ℕp * ℕt

  @[simp]
  theorem t_to_t'_ne_t (t t' : Ty) : (t =⇒ t') ≠ t := by
    by_contra h; match t with
    | nat => trivial
    | fn ta tb => injection h; have := t_to_t'_ne_t ta tb; contradiction
end Ty

-- https://plfa.github.io/DeBruijn/#contexts
abbrev Context : Type := List Ty

namespace Context
  abbrev snoc : Context → Ty → Context := flip (· :: ·)
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  infixl:50 " ‚ " => snoc
end Context

-- https://plfa.github.io/DeBruijn/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ‚ t) t
| s : Lookup Γ t → Lookup (Γ‚ t') t
deriving DecidableEq, Repr

namespace Lookup
  infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.z)
  | n+1 => `(tactic| apply Lookup.s; get_elem $(Lean.quote n))

  macro " ♯ " n:term:90 : term => `(by get_elem $n)

  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt := .z
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt := ♯0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt =⇒ ℕt := .s .z
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt =⇒ ℕt := ♯1
end Lookup

-- https://plfa.github.io/DeBruijn/#terms-and-the-typing-judgment
/--
A term with typing judgement embedded in itself.
-/
inductive Term : Context → Ty → Type where
-- Lookup
| var : Γ ∋ a → Term Γ a
-- Lambda
| lam : Term (Γ‚ a) b → Term Γ (a =⇒ b)
| ap : Term Γ (a =⇒ b) → Term Γ a → Term Γ b
-- Native natural
| zero : Term Γ ℕt
| succ : Term Γ ℕt → Term Γ ℕt
| case : Term Γ ℕt → Term Γ a → Term (Γ‚ ℕt) a → Term Γ a
-- Fixpoint
| mu : Term (Γ‚ a) a → Term Γ a
-- Primitive natural
| prim : ℕ → Term Γ ℕp
| mulP : Term Γ ℕp → Term Γ ℕp → Term Γ ℕp
-- Let expression
| let : Term Γ a → Term (Γ‚ a) b → Term Γ b
-- Product
| prod : Term Γ a → Term Γ b → Term Γ (a * b)
| fst : Term Γ (a * b) → Term Γ a
| snd : Term Γ (a * b) → Term Γ b
-- Product (alternative formulation)
-- | caseProd : Term Γ (a * b) → Term (Γ‚ a‚ b) c → Term Γ c
-- Sum
| left : Term Γ a → Term Γ (a + b)
| right : Term Γ b → Term Γ (a + b)
| caseSum : Term Γ (a + b) → Term (Γ‚ a) c → Term (Γ‚ b) c → Term Γ c
-- Void
| caseVoid : Term Γ ∅ → Term Γ a
-- Unit
| unit : Term Γ ◯
-- List
| nil : Term Γ (.list a)
| cons : Term Γ a → Term Γ (.list a) → Term Γ (.list a)
| caseList : Term Γ (.list a) → Term Γ b → Term (Γ‚ a‚ .list a) b → Term Γ b
deriving DecidableEq, Repr

namespace Term
  infix:40 " ⊢ " => Term

  prefix:50 " ƛ " => lam
  prefix:50 " μ " => mu
  notation " 𝟘? " => case
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  infixl:70 " ⋄ "   => mulP
  prefix:80 " ι " => succ
  prefix:90 " ` " => var

  notation " 𝟘 " => zero
  notation " ◯ " => unit

  -- https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
  macro " # " n:term:90 : term => `(`♯$n)

  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt =⇒ ℕt := #1
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #1 $ #0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #1 $ #1 $ #0
  example : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
  example : ∅ ⊢ (ℕt =⇒ ℕt) =⇒ ℕt =⇒ ℕt := ƛ ƛ (#1 $ #1 $ #0)

  @[simp]
  def ofNat : ℕ → Γ ⊢ ℕt
  | 0 => zero
  | n + 1 => succ <| ofNat n

  instance : Coe ℕ (Γ ⊢ ℕt) where coe := ofNat
  instance : OfNat (Γ ⊢ ℕt) n where ofNat := ofNat n

  -- https://plfa.github.io/DeBruijn/#test-examples
  example : Γ ⊢ ℕt := ι ι 𝟘
  example : Γ ⊢ ℕt := 2

  @[simp] abbrev add : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) (#0) (ι (#3 □ #0 □ #1)))
  @[simp] abbrev mul : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) 𝟘 (add □ #1 $ #3 □ #0 □ #1))

  example : Γ ⊢ ℕt := add □ 2 □ 2

  /--
  The Church numeral Ty.
  -/
  abbrev Ch (t : Ty) : Ty := (t =⇒ t) =⇒ t =⇒ t

  @[simp] abbrev succC : Γ ⊢ ℕt =⇒ ℕt := ƛ ι #0
  @[simp] abbrev twoC : Γ ⊢ Ch a := ƛ ƛ (#1 $ #1 $ #0)
  @[simp] abbrev addC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ #1 $ #2 □ #1 □ #0)
  example : Γ ⊢ ℕt := addC □ twoC □ twoC □ succC □ 𝟘

  -- https://plfa.github.io/DeBruijn/#exercise-mul-recommended
  @[simp] abbrev mulC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ (#2 □ #1) □ #0)

  -- https://plfa.github.io/More/#example
  example : ∅ ⊢ ℕp =⇒ ℕp := ƛ #0 ⋄ #0 ⋄ #0
end Term

-- https://plfa.github.io/DeBruijn/#renaming
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
@[simp]
def rename : (∀ {a}, Γ ∋ a → Δ ∋ a) → Γ ⊢ a → Δ ⊢ a := by
  intro ρ; intro
  | ` x => exact ` (ρ x)
  | ƛ n => exact ƛ (rename (ext ρ) n)
  | l □ m => exact rename ρ l □ rename ρ m
  | 𝟘 => exact 𝟘
  | ι n => exact ι (rename ρ n)
  | 𝟘? l m n => exact 𝟘? (rename ρ l) (rename ρ m) (rename (ext ρ) n)
  | μ n => exact μ (rename (ext ρ) n)
  | .prim n => exact .prim n
  | m ⋄ n => exact rename ρ m ⋄ rename ρ n
  | .let m n => exact .let (rename ρ m) (rename (ext ρ) n)
  | .prod m n => exact .prod (rename ρ m) (rename ρ n)
  | .fst n => exact .fst (rename ρ n)
  | .snd n => exact .snd (rename ρ n)
  | .left n => exact .left (rename ρ n)
  | .right n => exact .right (rename ρ n)
  | .caseSum s l r => exact .caseSum (rename ρ s) (rename (ext ρ) l) (rename (ext ρ) r)
  | .caseVoid v => exact .caseVoid (rename ρ v)
  | ◯ => exact ◯
  | .nil => exact .nil
  | .cons m n => exact .cons (rename ρ m) (rename ρ n)
  | .caseList l m n => exact .caseList (rename ρ l) (rename ρ m) (rename (ext (ext ρ)) n)

example
: let m : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
  let m' : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#2 $ #2 $ #0)
  rename .s m = m'
:= rfl

-- https://plfa.github.io/DeBruijn/#simultaneous-substitution
/--
If the variables in one context maps to some terms in another,
the mapping holds after adding the same variable to both contexts.
-/
@[simp]
def exts : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ‚ b ∋ a → Δ‚ b ⊢ a := by
  intro σ; intro
  | .z => exact `.z
  | .s x => apply rename .s; exact σ x

/--
General substitution for multiple free variables.
If the variables in one context maps to some terms in another,
then the type judgements are the same before and after the mapping,
i.e. after replacing the free variables in the former with (expanded) terms.
-/
@[simp]
def subst : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ ⊢ a → Δ ⊢ a := by
  intro σ; intro
  | ` x => exact σ x
  | ƛ n => exact ƛ (subst (exts σ) n)
  | l □ m => exact subst σ l □ subst σ m
  | 𝟘 => exact 𝟘
  | ι n => exact ι (subst σ n)
  | 𝟘? l m n => exact 𝟘? (subst σ l) (subst σ m) (subst (exts σ) n)
  | μ n => exact μ (subst (exts σ) n)
  | .prim n => exact .prim n
  | m ⋄ n => exact subst σ m ⋄ subst σ n
  | .let m n => exact .let (subst σ m) (subst (exts σ) n)
  | .prod m n => exact .prod (subst σ m) (subst σ n)
  | .fst n => exact .fst (subst σ n)
  | .snd n => exact .snd (subst σ n)
  | .left n => exact .left (subst σ n)
  | .right n => exact .right (subst σ n)
  | .caseSum s l r => exact .caseSum (subst σ s) (subst (exts σ) l) (subst (exts σ) r)
  | .caseVoid v => exact .caseVoid (subst σ v)
  | ◯ => exact ◯
  | .nil => exact .nil
  | .cons m n => exact .cons (subst σ m) (subst σ n)
  | .caseList l m n => exact .caseList (subst σ l) (subst σ m) (subst (exts (exts σ)) n)

/--
Substitution for one free variable `v` in the term `n`.
-/
abbrev subst₁ (v : Γ ⊢ b) (n : Γ‚ b ⊢ a) : Γ ⊢ a := by
  refine subst ?_ n; introv; intro
  | .z => exact v
  | .s x => exact ` x

/--
Substitution for one two variable `v` and `w'` in the term `n`.
-/
abbrev subst₂ (v : Γ ⊢ b) (w : Γ ⊢ c) (n : Γ‚ b‚ c ⊢ a) : Γ ⊢ a := by
  refine subst ?_ n; introv; intro
  | .z => exact w
  | .s .z => exact v
  | .s (.s x) => exact ` x

infixr:90 " ⇴ " => subst₁
infixl:90 " ⬰ " => flip subst₁

-- https://plfa.github.io/More/#exercise-double-subst-stretch
theorem double_subst : subst₂ v w n = n ⬰ rename .s w ⬰ v := sorry

example
: let m : ∅ ⊢ ℕt =⇒ ℕt := ƛ (ι #0)
  let m' : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
  let n : ∅ ⊢ ℕt =⇒ ℕt := ƛ (ƛ ι #0) □ ((ƛ ι #0) □ #0)
  m ⇴ m' = n
:= rfl

example
: let m : ∅‚ ℕt =⇒ ℕt ⊢ ℕt := #0 $ 𝟘
  let m' : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ (ℕt =⇒ ℕt) =⇒ ℕt := ƛ (#0 $ #1)
  let n : ∅‚ ℕt =⇒ ℕt ⊢ (ℕt =⇒ ℕt) =⇒ ℕt := ƛ (#0 $ #1 $ 𝟘)
  m ⇴ m' = n
:= rfl

inductive Value : Γ ⊢ a → Type where
| lam : Value (ƛ (n : Γ‚ a ⊢ b))
| zero : Value 𝟘
| succ : Value n → Value (ι n)
| prim : (n : ℕ) → Value (@Term.prim Γ n)
| prod : Value (v : Γ ⊢ a) → Value (w : Γ ⊢ b) → Value (.prod v w)
| left : Value v → Value (.left a)
| right : Value v → Value (.right a)
| unit : Value ◯
| nil : Value .nil
| cons : Value (v : Γ ⊢ a) → Value (vs : Γ ⊢ .list a) → Value (.cons v vs)
deriving DecidableEq, Repr

namespace Value
  notation " V𝟘 " => zero

  @[simp]
  def ofNat : (n : ℕ) → @Value Γ ℕt (Term.ofNat n)
  | 0 => V𝟘
  | n + 1 => succ <| ofNat n
end Value

-- https://plfa.github.io/DeBruijn/#reduction
/--
`Reduce t t'` says that `t` reduces to `t'`.
-/
inductive Reduce : (Γ ⊢ a) → (Γ ⊢ a) → Type where
| lamβ : Value v → Reduce ((ƛ n) □ v) (n ⬰ v)
| apξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
| apξ₂ : Value v → Reduce m m' → Reduce (v □ m) (v □ m')
| zeroβ : Reduce (𝟘? 𝟘 m n) m
| succβ : Value v → Reduce (𝟘? (ι v) m n) (n ⬰ v)
| succξ : Reduce m m' → Reduce (ι m) (ι m')
| caseξ : Reduce l l' → Reduce (𝟘? l m n) (𝟘? l' m n)
| muβ : Reduce (μ n) (n ⬰ (μ n))
-- https://plfa.github.io/More/#reduction
| mulPξ₁ : Reduce l l' → Reduce (l ⋄ m) (l' ⋄ m)
| mulPξ₂ : Reduce m m' → Reduce (l ⋄ m) (l ⋄ m')
| mulPδ : Reduce ((.prim c) ⋄ (.prim d)) (.prim (c * d))
-- https://plfa.github.io/More/#reduction-1
| letξ : Reduce m m' → Reduce (.let m n) (.let m' n)
| letβ : Value w → Reduce (.let v n) (n ⬰ v)
-- https://plfa.github.io/More/#reduction-2
| prodξ₁ : Reduce m m' → Reduce (.prod m n) (.prod m' n)
| prodξ₂ : Reduce n n' → Reduce (.prod m n) (.prod m n')
| fstξ : Reduce l l' → Reduce (.fst l) (.fst l')
| fstβ : Value v → Value w → Reduce (.fst (.prod v w)) v
| sndξ : Reduce l l' → Reduce (.snd l) (.snd l')
| sndβ : Value v → Value w → Reduce (.snd (.prod v w)) w
-- https://plfa.github.io/More/#reduction-3
-- | caseProdξ : Reduce l l' → Reduce (.caseProd l m) (.caseProd l' m)
-- | caseProdβ
-- : Value (v : Γ ⊢ a)
-- → Value (w : Γ ⊢ b)
-- → Reduce (.caseProd (.prod v w) (m : Γ‚ a‚ b ⊢ c)) (subst₂ v w m)
-- https://plfa.github.io/More/#reduction-4
| caseSumξ : Reduce s s' → Reduce (.caseSum s l r) (.caseSum s' l r)
| leftξ : Reduce m m' → Reduce (.left m) (.left m')
| leftβ : Value v → Reduce (.caseSum (.left v) l r) (l ⬰ v)
| rightξ : Reduce m m' → Reduce (.right m) (.right m')
| rightβ : Value v → Reduce (.caseSum (.right v) l r) (l ⬰ v)
-- https://plfa.github.io/More/#reduction-8
| caseListξ : Reduce l l' → Reduce (.caseList l m n) (.caseList l' m n)
| nilβ : Reduce (.caseList .nil m n) m
| consξ₁ : Reduce m m' → Reduce (.cons m n) (.cons m' n)
| consξ₂ : Reduce n n' → Reduce (.cons v n) (.cons v n')
| consβ : Reduce (.caseList (.cons v w) m n) (subst₂ v w n)
deriving Repr

infix:40 " —→ " => Reduce

namespace Reduce
  -- https://plfa.github.io/DeBruijn/#reflexive-and-transitive-closure
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  inductive Clos : (Γ ⊢ a) → (Γ ⊢ a) → Type where
  | nil : Clos m m
  | cons : (l —→ m) → Clos m n → Clos l n
  deriving Repr

  infix:20 " —↠ " => Clos

  namespace Clos
    @[simp]
    def length : (m —↠ n) → Nat
    | nil => 0
    | cons _ cdr => 1 + cdr.length

    @[simp] abbrev one (car : m —→ n) : (m —↠ n) := cons car nil
    instance : Coe (m —→ n) (m —↠ n) where coe := one

    @[simp]
    def trans : (l —↠ m) → (m —↠ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance : Trans (α := Γ ⊢ a) Clos Clos Clos where
      trans := trans

    instance : Trans (α := Γ ⊢ a) Reduce Clos Clos where
      trans := cons

    instance : Trans (α := Γ ⊢ a) Reduce Reduce Clos where
      trans c c' := cons c <| cons c' nil

    @[simp]
    def transOne : (l —↠ m) → (m —→ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance : Trans (α := Γ ⊢ a) Clos Reduce Clos where
      trans := transOne
  end Clos

  open Term

  -- https://plfa.github.io/DeBruijn/#examples
  example : twoC □ succC □ @zero ∅ —↠ 2 := calc
    twoC □ succC □ 𝟘
    _ —→ (ƛ (succC $ succC $ #0)) □ 𝟘 := by apply apξ₁; apply lamβ; exact Value.lam
    _ —→ (succC $ succC $ 𝟘) := by apply lamβ; exact V𝟘
    _ —→ succC □ 1 := by apply apξ₂; apply Value.lam; exact lamβ V𝟘
    _ —→ 2 := by apply lamβ; exact Value.ofNat 1
end Reduce

-- https://plfa.github.io/DeBruijn/#values-do-not-reduce
@[simp]
def Value.emptyReduce : Value m → ∀ {n}, IsEmpty (m —→ n) := by
  introv v; is_empty; intro r
  cases v <;> try contradiction
  · case succ v => cases r; · case succξ => apply (emptyReduce v).false; trivial

@[simp]
def Reduce.emptyValue : m —→ n → IsEmpty (Value m) := by
  intro r; is_empty; intro v
  have : ∀ {n}, IsEmpty (m —→ n) := Value.emptyReduce v
  exact this.false r

/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
@[aesop safe [constructors, cases]]
inductive Progress (m : ∅ ⊢ a) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m

@[simp]
def progress : (m : ∅ ⊢ a) → Progress m := open Progress Reduce in by
  intro
  | ` _ => contradiction
  | ƛ _ => exact .done .lam
  | l □ m => cases progress l with
    | step => apply step; apply apξ₁; trivial
    | done l => cases progress m with
      | step => apply step; apply apξ₂ <;> trivial
      | done => cases l with
        | lam => apply step; apply lamβ; trivial
  | 𝟘 => exact .done V𝟘
  | ι n => cases progress n with
    | step => apply step; apply succξ; trivial
    | done => apply done; apply Value.succ; trivial
  | 𝟘? l m n => cases progress l with
    | step => apply step; apply caseξ; trivial
    | done v => cases v with
      | zero => exact .step zeroβ
      | succ => apply step; apply succβ; trivial
  | μ _ => exact .step muβ
  | .prim n => exact .done (.prim n)
  | m ⋄ n => cases progress m with
    | step => apply step; apply mulPξ₁; trivial
    | done m => cases progress n with
      | step => apply step; apply mulPξ₂; trivial
      | done n => cases m; cases n; exact .step mulPδ
  | .let m n => sorry
  | .prod m n => sorry
  | .fst n => sorry
  | .snd n => sorry
  | .left n => sorry
  | .right n => sorry
  | .caseSum s l r => sorry
  | .caseVoid v => sorry
  | ◯ => exact .done .unit
  | .nil => exact .done .nil
  | .cons m n => sorry
  | .caseList l m n => sorry

inductive Result (n : Γ ⊢ a) where
| done (val : Value n)
| dnf
deriving BEq, DecidableEq, Repr

inductive Steps (l : Γ ⊢ a) where
| steps : ∀{n : Γ ⊢ a}, (l —↠ n) → Result n → Steps l
deriving Repr

@[simp]
def eval (gas : ℕ) (l : ∅ ⊢ a) : Steps l :=
  if gas = 0 then
    ⟨.nil, .dnf⟩
  else
    match progress l with
    | .done v => .steps .nil <| .done v
    | .step r =>
      let ⟨rs, res⟩ := eval (gas - 1) (by trivial)
      ⟨.cons r rs, res⟩

section examples
  open Term

  -- def x : ℕ := x + 1
  abbrev succμ : ∅ ⊢ ℕt := μ ι #0

  #eval eval 3 succμ |> (·.3)
  #eval eval 100 (add □ 2 □ 2) |> (·.3)
  #eval eval 100 (mul □ 2 □ 3) |> (·.3)
end examples
