-- https://plfa.github.io/Lambda/

import Mathlib.Tactic

open String

def Sym : Type := String deriving BEq, DecidableEq, Repr

-- https://plfa.github.io/Lambda/#syntax-of-terms
inductive Term where
| var : Sym → Term
| lam : Sym → Term → Term
| ap : Term → Term → Term
| zero : Term
| succ : Term → Term
| case : Term → Term → Sym → Term → Term
| mu : Sym → Term → Term
deriving BEq, DecidableEq, Repr

namespace Term
  notation:50 " ƛ " v " : " d => lam v d
  notation:50 " μ " v " : " d => mu v d
  notation:max " ? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  prefix:80 " ι " => succ
  prefix:90 " ` " => var

  @[simp] def o : Term := zero

  example : Term := `"foo"
  example : Term := ? `"bar" [zero: o |succ "n" : ι o]

  @[simp] def one : Term := ι o
  @[simp] def two : Term := ι ι o

  @[simp] def add : Term := μ "+" : ƛ "m" : ƛ "n" : ? `"m" [zero: `"n" |succ "m": ι (`"+" □ `"m" □ `"n")]
  -- https://plfa.github.io/Lambda/#exercise-mul-recommended
  @[simp] def mul : Term := μ "*" : ƛ "m" : ƛ "n" : ? `"m" [zero: o |succ "m": `"+" □ `"n" $ `"*" □ `"m" □ `"n"]

  -- Church encoding...
  @[simp] def succ_c : Term := ƛ "n" : ι `"n"
  @[simp] def one_c : Term := ƛ "s" : ƛ "z" : `"s" $ `"z"
  @[simp] def two_c : Term := ƛ "s" : ƛ "z" : `"s" $ `"s" $ `"z"
  @[simp] def add_c : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" □ `"s" $ `"n" □ `"s" □ `"z"
  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice
  @[simp] def mul_c : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" $ `"n" □ `"s" □ `"z"
end Term

-- https://plfa.github.io/Lambda/#values
inductive Value : Term → Type where
| lam : Value (ƛ v : d)
| zero: Value o
| succ: Value n → Value (ι n)
deriving BEq, DecidableEq, Repr

namespace Value
  @[simp] def o : Value Term.o := zero

  def of_nat : ℕ → Σ n, Value n
  | 0 => ⟨Term.o, o⟩
  | n + 1 => let ⟨tn, vn⟩ := of_nat n; ⟨ι tn, succ vn⟩
end Value

-- https://plfa.github.io/Lambda/#substitution
namespace Term
  /--
  `x.subst y v` substitutes term `v` for all free occurrences of variable `y` in term `x`.
  -/
  @[simp]
  def subst : Term → Sym → Term → Term
  | ` x, y, v => if x = y then v else ` x
  | ƛ x : n, y, v => if x = y then ƛ x : n else ƛ x : n.subst y v
  | ap l m, y, v => l.subst y v $ m.subst y v
  -- `.o` means that `o` is not a new binding, but a constant.
  -- See: https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html?highlight=inac#inaccessible-patterns
  | .o, _, _ => o
  | ι n, y, v => ι (n.subst y v)
  | ? l [zero: m |succ x: n], y, v => if x = y
      then ? l.subst y v [zero: m.subst y v |succ x: n]
      else ? l.subst y v [zero: m.subst y v |succ x: n.subst y v]
  | μ x : n, y, v => if x = y then μ x : n else μ x : n.subst y v

  notation:90 x " [ " y " := " v " ] " => subst x y v

  -- https://plfa.github.io/Lambda/#examples
  example
  : (ƛ "z" : `"s" □ `"s" □ `"z")["s" := succ_c]
  = (ƛ "z" : succ_c □ succ_c □ `"z") := rfl

  example : (succ_c □ succ_c □ `"z")["z" := o] = succ_c □ succ_c □ o := rfl
  example : (ƛ "x" : `"y")["y" := o] = (ƛ "x" : o) := rfl
  example : (ƛ "x" : `"x")["x" := o] = (ƛ "x" : `"x") := rfl
  example : (ƛ "y" : `"y")["x" := o] = (ƛ "y" : `"y") := rfl

  -- https://plfa.github.io/Lambda/#quiz
  example
  : (ƛ "y" : `"x" $ ƛ "x" : `"x")["x" := o]
  = (ƛ "y" : o $ ƛ "x" : `"x")
  := rfl

  -- https://plfa.github.io/Lambda/#reduction
  /--
  `Reduce t t'` says that `t` reduces to `t'`.
  -/
  inductive Reduce : Term → Term → Type where
  | lam_β : Value v → Reduce ((ƛ x : n) □ v) (n[x := v])
  | ap_ξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
  | ap_ξ₂ : Value v → Reduce m m' → Reduce (v □ m) (v □ m')
  | zero_β : Reduce (? o [zero: m |succ x : n]) m
  | succ_β : Value v → Reduce (? ι v [zero: m |succ x : n]) (n[x := v])
  | succ_ξ : Reduce m m' → Reduce (ι m) (ι m')
  | case_ξ : Reduce l l' → Reduce (? l [zero: m |succ x : n]) (? l' [zero: m |succ x : n])
  | mu_β : Reduce (μ x : m) (m[x := μ x : m])

  infix:40 " —→ " => Reduce
end Term

namespace Term.Reduce
  -- https://plfa.github.io/Lambda/#quiz-1
  example : (ƛ "x" : `"x") □ (ƛ "x" : `"x") —→ (ƛ "x" : `"x") := by
    apply lam_β; exact Value.lam

  example : (ƛ "x" : `"x") □ (ƛ "x" : `"x") □ (ƛ "x" : `"x") —→ (ƛ "x" : `"x") □ (ƛ "x" : `"x") := by
    apply ap_ξ₁; apply lam_β; exact Value.lam

  example : two_c □ succ_c □ o —→ (ƛ "z" : succ_c $ succ_c $ `"z") □ o := by
    unfold two_c; apply ap_ξ₁; apply lam_β; exact Value.lam

  -- https://plfa.github.io/Lambda/#reflexive-and-transitive-closure
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  inductive Clos : Term → Term → Type where
  | nil : Clos m m
  | cons : (l —→ m) → Clos m n → Clos l n

  infix:20 " —↠ " => Clos

  namespace Clos
    @[simp]
    def length : (m —↠ n) → Nat
    | nil => 0
    | cons _ cdr => 1 + cdr.length

    @[simp] def one (car : m —→ n) : (m —↠ n) := cons car nil

    @[simp]
    def trans : (l —↠ m) → (m —↠ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance is_trans : Trans Clos Clos Clos where
      trans := trans
  end Clos

  inductive Clos' : Term → Term → Type where
  | refl : Clos' m m
  | step : (m —→ n) → Clos' m n
  | trans : Clos' l m → Clos' m n → Clos' l n

  infix:20 " —↠' " => Clos'

  @[simp]
  def Clos.to_clos' : (m —↠ n) → (m —↠' n) := by
    intro
    | nil => exact Clos'.refl
    | cons h h' => exact Clos'.trans (Clos'.step h) h'.to_clos'

  @[simp]
  def Clos'.to_clos : (m —↠' n) → (m —↠ n) := by
    intro
    | refl => exact Clos.nil
    | step h => exact Clos.one h
    | trans h h' => apply Clos.trans <;> (apply to_clos; assumption)

  -- https://plfa.github.io/Lambda/#exercise-practice
  lemma Clos.to_clos'_left_inv : ∀ {x : m —↠ n}, x.to_clos'.to_clos = x := by
    intro
    | nil => rfl
    | cons car cdr => simp_all; exact to_clos'_left_inv (x := cdr)

  lemma Clos.to_clos'_inj
  : @Function.Injective (m —↠ n) (m —↠' n) Clos.to_clos'
  := by
    unfold Function.Injective
    intro a b h
    have : a.to_clos'.to_clos = b.to_clos'.to_clos := by simp_all
    rwa [←Clos.to_clos'_left_inv (x := a), ←Clos.to_clos'_left_inv (x := b)]

  instance Clos.embeds_in_clos' : (m —↠ n) ↪ (m —↠' n) where
    toFun := to_clos'
    inj' := to_clos'_inj
end Reduce

-- https://plfa.github.io/Lambda/#confluence
section confluence
  open Term.Reduce Term.Reduce.Clos

  -- `Σ` is used instead of `∃` because it's a `Type` that exists, not a `Prop`.
  def Diamond : Type := ∀ ⦃l m n⦄, (l —→ m) → (l —→ n) → (Σ p, (m —↠ p) × (n —↠ p))
  def Confluence : Type := ∀ ⦃l m n⦄, (l —↠ m) → (l —↠ n) → (Σ p, (m —↠ p) × (n —↠ p))
  def Deterministic : Prop := ∀ ⦃l m n⦄, (l —→ m) → (l —→ n) → (m = n)

  theorem Deterministic.to_diamond : Deterministic → Diamond := by
    unfold Deterministic Diamond; intro h l m n lm ln
    have heq := h lm ln; simp_all
    exists n; exact ⟨nil, nil⟩

  theorem Deterministic.to_confluence : Deterministic → Confluence
  | h, l, m, n, lm, ln => by match lm, ln with
    | nil, nil => exists n; exact ⟨ln, ln⟩
    | nil, c@(cons _ _) => exists n; exact ⟨c, nil⟩
    | c@(cons _ _), nil => exists m; exact ⟨nil, c⟩
    | cons car cdr, cons car' cdr' =>
      have := h car car'; subst this; simp_all
      exact to_confluence h cdr cdr'
end confluence

-- https://plfa.github.io/Lambda/#examples-1
section examples
  open Term.Reduce Term.Reduce.Clos

  example : two_c □ succ_c □ o —↠ two := calc
    two_c □ succ_c □ o
    -- `Clos.one` means that we are reducing just by a single step.
    _ —↠ (ƛ "z" : succ_c $ succ_c $ `"z") □ o := Clos.one <| by apply ap_ξ₁; apply lam_β; exact Value.lam
    _ —↠ (succ_c $ succ_c $ o) := Clos.one <| by apply lam_β; exact Value.zero
    _ —↠ succ_c □ one := Clos.one <| by apply ap_ξ₂; apply Value.lam; apply lam_β; exact Value.zero
    _ —↠ two := Clos.one <| by apply lam_β; exact (Value.of_nat 1).2

  -- https://plfa.github.io/Lambda/#exercise-plus-example-practice
  example : add □ one □ one —↠ two := calc
    add □ one □ one
    _ —↠ (ƛ "m" : ƛ "n" : ? `"m" [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ one □ one
      := Clos.one <| by apply ap_ξ₁; apply ap_ξ₁; apply mu_β
    _ —↠ (ƛ "n" : ? one [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ one
      := Clos.one <| by apply ap_ξ₁; apply lam_β; exact (Value.of_nat 1).2
    _ —↠ ? one [zero: one |succ "m": ι (add □ `"m" □ one)]
      := Clos.one <| lam_β (Value.of_nat 1).2
    _ —↠ ι (add □ o □ one)
      := Clos.one <| succ_β Value.o
    _ —↠ ι ((ƛ "m" : ƛ "n" : ? `"m" [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ o □ one)
      := Clos.one <| by apply succ_ξ; apply ap_ξ₁; apply ap_ξ₁; apply mu_β
    _ —↠ ι ((ƛ "n" : ? o [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ one)
      := Clos.one <| by apply succ_ξ; apply ap_ξ₁; apply lam_β; exact Value.o
    _ —↠ ι (? o [zero: one |succ "m": ι (add □ `"m" □ one)])
      := Clos.one <| by apply succ_ξ; apply lam_β; exact (Value.of_nat 1).2
    _ —↠ ι one := Clos.one <| succ_ξ zero_β
end examples

-- https://plfa.github.io/Lambda/#syntax-of-types
inductive Ty where
| nat
| fn : Ty → Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Ty
  notation "ℕt" => nat
  infixr:70 " -→ " => fn

  example : Ty := (ℕt -→ ℕt) -→ ℕt

  @[simp]
  theorem t_to_t'_ne_t (t t' : Ty) : (t -→ t') ≠ t := by
    by_contra h; match t with
    | nat => trivial
    | fn ta tb => injection h; have := t_to_t'_ne_t ta tb; contradiction
end Ty

-- https://plfa.github.io/Lambda/#contexts
def Context : Type := List (Sym × Ty)

namespace Context
  open Term

  def nil : Context := []
  def extend : Context → Sym → Ty → Context | c, s, ts => ⟨s, ts⟩ :: c

  notation " ∅ " => nil

  -- The goal is to make `_:<_⦂_` work like an `infixl`.
  -- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html#From-Precedence-to-Binding-Power
  notation:50 c " :< " s:51 " ⦂ " t:51 => extend c s t

  example {Γ : Context} {s : Sym} {ts : Ty} : Context := Γ :< s ⦂ ts

  -- https://plfa.github.io/Lambda/#lookup-judgment
  /--
  A lookup judgement.
  `Lookup c s ts` means that `s` is of type `ts` by _looking up_ the context `c`.
  -/
  inductive Lookup : Context → Sym → Ty → Type where
  | z : Lookup (Γ :< x ⦂ tx) x tx
  | s : x ≠ y → Lookup Γ x tx → Lookup (Γ :< y ⦂ ty) x tx
  deriving DecidableEq

  notation:40 c " ∋ " s " ⦂ " t => Lookup c s t

  example
  : ∅ :< "x" ⦂ ℕt -→ ℕt :< "y" ⦂ ℕt :< "z" ⦂ ℕt
  ∋ "x" ⦂ ℕt -→ ℕt
  := open Lookup in by
    apply s _; apply s _; apply z; repeat trivial

  -- https://plfa.github.io/Lambda/#lookup-is-functional
  @[simp]
  theorem Lookup.functional : (Γ ∋ x ⦂ tx) → (Γ ∋ x ⦂ tx') → tx = tx' := by
    intro
    | z, z => rfl
    | z, s _ e => trivial
    | s _ e, z => trivial
    | s _ e, s _ e' => exact functional e e'

  -- https://plfa.github.io/Lambda/#typing-judgment
  /--
  A general typing judgement.
  `IsTy c t tt` means that `t` can be inferred to be of type `tt` in the context `c`.
  -/
  inductive IsTy : Context → Term → Ty → Type where
  | var : (Γ ∋ x ⦂ tx) → IsTy Γ (` x) tx
  | lam : IsTy (Γ :< x ⦂ tx) n tn → IsTy Γ (ƛ x : n) (tx -→ tn)
  | ap : IsTy Γ l (tx -→ tn) → IsTy Γ x tx → IsTy Γ (l □ x) tn
  | zero : IsTy Γ o ℕt
  | succ : IsTy Γ n ℕt → IsTy Γ (ι n) ℕt
  | case : IsTy Γ l ℕt → IsTy Γ m t → IsTy (Γ :< x ⦂ ℕt) n t → IsTy Γ (? L [zero: m |succ x: n]) t
  | mu : IsTy (Γ :< x ⦂ t) m t → IsTy Γ (μ x : m) t
  deriving DecidableEq

  notation:40 c " ⊢ " t " ⦂ " tt => IsTy c t tt

  /--
  `NoTy c t` means that `t` cannot be inferred to be any type in the context `c`.
  -/
  @[simp] def NoTy (c : Context) (t : Term) : Prop := IsEmpty (Σ tt, c ⊢ t ⦂ tt)

  infix:40 " ⊬ " => NoTy

  -- https://plfa.github.io/Lambda/#quiz-2
  lemma twice_ty : Γ ⊢ (ƛ "s" : `"s" $ `"s" $ o) ⦂ ((ℕt -→ ℕt) -→ ℕt) := by
    apply IsTy.lam; apply IsTy.ap <| IsTy.var Lookup.z
    apply IsTy.ap; exact IsTy.var Lookup.z; exact IsTy.zero

  theorem two_ty : Γ ⊢ (ƛ "s" : `"s" $ `"s" $ o) □ succ_c ⦂ ℕt := by
    apply IsTy.ap twice_ty
    apply IsTy.lam; apply IsTy.succ; exact IsTy.var Lookup.z

  -- https://plfa.github.io/Lambda/#derivation
  theorem two_c_ty : Γ ⊢ two_c ⦂ (t -→ t) -→ t -→ t := open Lookup in by
    apply IsTy.lam; apply IsTy.lam; apply IsTy.ap
    · exact IsTy.var (s (by trivial) z)
    · apply IsTy.ap
      · exact IsTy.var (s (by trivial) z)
      · exact IsTy.var z
end Context

section examples
  open Context

  -- https://plfa.github.io/Lambda/#non-examples
  example : ∅ ⊬ o □ one := by
    by_contra h; simp_all
    let ⟨t, ht⟩ := h; cases ht.some
    contradiction

  example : ∅ ⊬ ƛ "x" : `"x" □ `"x" := by
    by_contra h; simp_all
    let ⟨t, ⟨ht⟩⟩ := h
    let IsTy.lam (IsTy.ap (IsTy.var hx) (IsTy.var hx')) := ht
    have := Lookup.functional hx hx'; simp_all

    -- https://plfa.github.io/Lambda/#quiz-3
    example : ∅ :< "y" ⦂ ℕt -→ ℕt :< "x" ⦂ ℕt ⊢ `"y" □ `"x" ⦂ ℕt := open Lookup in by
      apply IsTy.ap
      · exact IsTy.var (s (by trivial) z)
      · exact IsTy.var z

    example : ∅ :< "y" ⦂ ℕt -→ ℕt :< "x" ⦂ ℕt ⊬ `"x" □ `"y" := by
      by_contra h; simp_all
      let ⟨t, ⟨ht⟩⟩ := h
      cases ht; rename_i hy hx; cases hx; rename_i ty hx; cases hx; contradiction

    example : ∅ :< "y" ⦂ ℕt -→ ℕt ⊢ ƛ "x" : `"y" □ `"x" ⦂ ℕt -→ ℕt := open Lookup in by
      apply IsTy.lam; apply IsTy.ap
      · exact IsTy.var (s (by trivial) z)
      · exact IsTy.var z

    -- example : ∅ :< "x" ⦂ A ⊢ `"x" □ `"x" ⦂ B

    example
    : ∅ :< "x" ⦂ ℕt -→ ℕt :< "y" ⦂ ℕt -→ ℕt
    ⊢ ƛ "z" : (`"x" $ `"y" $ `"z") ⦂ ℕt -→ ℕt
    := open Lookup in by
      apply IsTy.lam; apply IsTy.ap
      · exact IsTy.var <| s (by trivial) <| s (by trivial) z
      · apply IsTy.ap
        · exact IsTy.var (s (by trivial) z)
        · exact IsTy.var z

    -- https://plfa.github.io/Lambda/#exercise-mul-recommended-1

    -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice-1
end examples
