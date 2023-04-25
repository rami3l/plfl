-- https://plfa.github.io/Lambda/

import Mathlib.Tactic

set_option tactic.simp.trace true

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
  notation:max " 𝟘? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  prefix:80 " ι " => succ
  prefix:90 " ` " => var
  notation " 𝟘 " => zero

  example : Term := `"foo"
  example : Term := 𝟘? `"bar" [zero: 𝟘 |succ "n" : ι 𝟘]

  @[simp]
  def ofNat | 0 => zero | n + 1 => succ <| ofNat n
  instance : Coe ℕ Term where coe := ofNat
  instance : OfNat Term n where ofNat := ofNat n

  example : Term := 1
  example : Term := 42

  abbrev add : Term := μ "+" : ƛ "m" : ƛ "n" : 𝟘? `"m" [zero: `"n" |succ "m": ι (`"+" □ `"m" □ `"n")]
  -- https://plfa.github.io/Lambda/#exercise-mul-recommended
  abbrev mul : Term := μ "*" : ƛ "m" : ƛ "n" : 𝟘? `"m" [zero: 𝟘 |succ "m": add □ `"n" $ `"*" □ `"m" □ `"n"]

  -- Church encoding...
  abbrev succ_c : Term := ƛ "n" : ι `"n"
  abbrev one_c : Term := ƛ "s" : ƛ "z" : `"s" $ `"z"
  abbrev two_c : Term := ƛ "s" : ƛ "z" : `"s" $ `"s" $ `"z"
  abbrev add_c : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" □ `"s" $ `"n" □ `"s" □ `"z"
  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice
  abbrev mul_c : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" □ (`"n" □ `"s") □ `"z"
end Term

-- https://plfa.github.io/Lambda/#values
inductive Value : Term → Type where
| lam : Value (ƛ v : d)
| zero: Value 𝟘
| succ: Value n → Value (ι n)
deriving BEq, DecidableEq, Repr

namespace Value
  notation " V𝟘 " => zero

  @[simp]
  def ofNat : (n : ℕ) → Value (Term.ofNat n)
  | 0 => V𝟘
  | n + 1 => succ <| ofNat n

  -- instance : CoeDep ℕ n (Value ↑n) where coe := ofNat n
  -- instance : OfNat (Value (Term.ofNat n)) n where ofNat := ofNat n
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
  | 𝟘, _, _ => 𝟘
  | ι n, y, v => ι (n.subst y v)
  | 𝟘? l [zero: m |succ x: n], y, v => if x = y
      then 𝟘? l.subst y v [zero: m.subst y v |succ x: n]
      else 𝟘? l.subst y v [zero: m.subst y v |succ x: n.subst y v]
  | μ x : n, y, v => if x = y then μ x : n else μ x : n.subst y v

  notation:90 x " [ " y " := " v " ] " => subst x y v

  -- https://plfa.github.io/Lambda/#examples
  example
  : (ƛ "z" : `"s" □ `"s" □ `"z")["s" := succ_c]
  = (ƛ "z" : succ_c □ succ_c □ `"z") := rfl

  example : (succ_c □ succ_c □ `"z")["z" := 𝟘] = succ_c □ succ_c □ 𝟘 := rfl
  example : (ƛ "x" : `"y")["y" := 𝟘] = (ƛ "x" : 𝟘) := rfl
  example : (ƛ "x" : `"x")["x" := 𝟘] = (ƛ "x" : `"x") := rfl
  example : (ƛ "y" : `"y")["x" := 𝟘] = (ƛ "y" : `"y") := rfl

  -- https://plfa.github.io/Lambda/#quiz
  example
  : (ƛ "y" : `"x" $ ƛ "x" : `"x")["x" := 𝟘]
  = (ƛ "y" : 𝟘 $ ƛ "x" : `"x")
  := rfl

  -- https://plfa.github.io/Lambda/#reduction
  /--
  `Reduce t t'` says that `t` reduces to `t'`.
  -/
  inductive Reduce : Term → Term → Type where
  | lam_β : Value v → Reduce ((ƛ x : n) □ v) (n[x := v])
  | ap_ξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
  | ap_ξ₂ : Value v → Reduce m m' → Reduce (v □ m) (v □ m')
  | zero_β : Reduce (𝟘? 𝟘 [zero: m |succ x : n]) m
  | succ_β : Value v → Reduce (𝟘? ι v [zero: m |succ x : n]) (n[x := v])
  | succ_ξ : Reduce m m' → Reduce (ι m) (ι m')
  | case_ξ : Reduce l l' → Reduce (𝟘? l [zero: m |succ x : n]) (𝟘? l' [zero: m |succ x : n])
  | mu_β : Reduce (μ x : m) (m[x := μ x : m])
  deriving Repr

  infix:40 " —→ " => Reduce
end Term

namespace Term.Reduce
  -- https://plfa.github.io/Lambda/#quiz-1
  example : (ƛ "x" : `"x") □ (ƛ "x" : `"x") —→ (ƛ "x" : `"x") := by
    apply lam_β; exact Value.lam

  example : (ƛ "x" : `"x") □ (ƛ "x" : `"x") □ (ƛ "x" : `"x") —→ (ƛ "x" : `"x") □ (ƛ "x" : `"x") := by
    apply ap_ξ₁; apply lam_β; exact Value.lam

  example : two_c □ succ_c □ 𝟘 —→ (ƛ "z" : succ_c $ succ_c $ `"z") □ 𝟘 := by
    unfold two_c; apply ap_ξ₁; apply lam_β; exact Value.lam

  -- https://plfa.github.io/Lambda/#reflexive-and-transitive-closure
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  inductive Clos : Term → Term → Type where
  | nil : Clos m m
  | cons : (l —→ m) → Clos m n → Clos l n
  deriving Repr

  infix:20 " —↠ " => Clos

  namespace Clos
    @[simp]
    def length : (m —↠ n) → Nat
    | nil => 0
    | cons _ cdr => 1 + cdr.length

    abbrev one (car : m —→ n) : (m —↠ n) := cons car nil
    instance : Coe (m —→ n) (m —↠ n) where coe := one

    @[simp]
    def trans : (l —↠ m) → (m —↠ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance isTrans : Trans Clos Clos Clos where
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
    | step h => exact ↑h
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
    apply_fun Clos'.to_clos at h
    rwa [←to_clos'_left_inv (x := a), ←to_clos'_left_inv (x := b)]

  instance Clos.embeds_in_clos' : (m —↠ n) ↪ (m —↠' n) where
    toFun := to_clos'
    inj' := to_clos'_inj
end Term.Reduce

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
      have := h car car'; subst this
      exact to_confluence h cdr cdr'
end confluence

-- https://plfa.github.io/Lambda/#examples-1
section examples
  open Term Term.Reduce Term.Reduce.Clos

  example : two_c □ succ_c □ 𝟘 —↠ 2 := calc
    two_c □ succ_c □ 𝟘
    -- `Clos.one` means that we are reducing just by a single step.
    _ —↠ (ƛ "z" : succ_c $ succ_c $ `"z") □ 𝟘 := Clos.one <| by apply ap_ξ₁; apply lam_β; exact Value.lam
    _ —↠ (succ_c $ succ_c $ 𝟘) := Clos.one <| by apply lam_β; exact Value.zero
    _ —↠ succ_c □ 1 := Clos.one <| by apply ap_ξ₂; apply Value.lam; apply lam_β; exact Value.zero
    _ —↠ 2 := Clos.one <| by apply lam_β; exact Value.ofNat 1

  -- https://plfa.github.io/Lambda/#exercise-plus-example-practice
  example : add □ 1 □ 1 —↠ 2 := calc
    add □ 1 □ 1
    _ —↠ (ƛ "m" : ƛ "n" : 𝟘? `"m" [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ 1 □ 1
      := Clos.one <| by apply ap_ξ₁; apply ap_ξ₁; apply mu_β
    _ —↠ (ƛ "n" : 𝟘? 1 [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ 1
      := Clos.one <| by apply ap_ξ₁; apply lam_β; exact Value.ofNat 1
    _ —↠ 𝟘? 1 [zero: 1 |succ "m": ι (add □ `"m" □ 1)]
      := Clos.one <| lam_β <| Value.ofNat 1
    _ —↠ ι (add □ 𝟘 □ 1)
      := Clos.one <| succ_β Value.zero
    _ —↠ ι ((ƛ "m" : ƛ "n" : 𝟘? `"m" [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ 𝟘 □ 1)
      := Clos.one <| by apply succ_ξ; apply ap_ξ₁; apply ap_ξ₁; apply mu_β
    _ —↠ ι ((ƛ "n" : 𝟘? 𝟘 [zero: `"n" |succ "m": ι (add □ `"m" □ `"n")]) □ 1)
      := Clos.one <| by apply succ_ξ; apply ap_ξ₁; apply lam_β; exact V𝟘
    _ —↠ ι (𝟘? 𝟘 [zero: 1 |succ "m": ι (add □ `"m" □ 1)])
      := Clos.one <| by apply succ_ξ; apply lam_β; exact Value.ofNat 1
    _ —↠ 2 := Clos.one <| succ_ξ zero_β
end examples

-- https://plfa.github.io/Lambda/#syntax-of-types
inductive Ty where
| nat
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
  @[aesop safe [constructors, cases]]
  inductive Lookup : Context → Sym → Ty → Type where
  | z : Lookup (Γ :< x ⦂ tx) x tx
  | s : x ≠ y → Lookup Γ x tx → Lookup (Γ :< y ⦂ ty) x tx
  deriving DecidableEq

  notation:40 c " ∋ " s " ⦂ " t:51 => Lookup c s t

  example
  : ∅ :< "x" ⦂ ℕt =⇒ ℕt :< "y" ⦂ ℕt :< "z" ⦂ ℕt
  ∋ "x" ⦂ ℕt =⇒ ℕt
  := open Lookup in by
    apply s _; apply s _; apply z; repeat trivial

  -- https://plfa.github.io/Lambda/#lookup-is-functional
  @[simp]
  theorem Lookup.functional : Γ ∋ x ⦂ tx → Γ ∋ x ⦂ tx' → tx = tx' := by
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
  | ty_var : Γ ∋ x ⦂ tx → IsTy Γ (` x) tx
  | ty_lam : IsTy (Γ :< x ⦂ tx) n tn → IsTy Γ (ƛ x : n) (tx =⇒ tn)
  | ty_ap : IsTy Γ l (tx =⇒ tn) → IsTy Γ x tx → IsTy Γ (l □ x) tn
  | ty_zero : IsTy Γ 𝟘 ℕt
  | ty_succ : IsTy Γ n ℕt → IsTy Γ (ι n) ℕt
  | ty_case : IsTy Γ l ℕt → IsTy Γ m t → IsTy (Γ :< x ⦂ ℕt) n t → IsTy Γ (𝟘? l [zero: m |succ x: n]) t
  | ty_mu : IsTy (Γ :< x ⦂ t) m t → IsTy Γ (μ x : m) t
  deriving DecidableEq

  notation:40 c " ⊢ " t " ⦂ " tt:51 => IsTy c t tt

  /--
  `NoTy c t` means that `t` cannot be inferred to be any type in the context `c`.
  -/
  abbrev NoTy (c : Context) (t : Term) : Prop := ∀ {tt}, IsEmpty (c ⊢ t ⦂ tt)

  infix:40 " ⊬ " => NoTy

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/tactics.md#tactics-by-macro-expansion
  /--
  `lookup_var` validates the type of a variable by looking it up in the current context.
  This tactic fails when the lookup fails.
  -/
  syntax "lookup_var" : tactic
  macro_rules
  | `(tactic| lookup_var) =>
    `(tactic| apply IsTy.ty_var; repeat (first | apply Lookup.s (by trivial) | exact Lookup.z))

  -- Inform `trivial` of our new tactic.
  macro_rules | `(tactic| trivial) => `(tactic| lookup_var)

  open IsTy

  -- https://plfa.github.io/Lambda/#quiz-2
  lemma twice_ty : Γ ⊢ (ƛ "s" : `"s" $ `"s" $ 𝟘) ⦂ ((ℕt =⇒ ℕt) =⇒ ℕt) := by
    apply ty_lam; apply ty_ap
    · trivial
    · apply ty_ap
      · trivial
      · exact ty_zero

  theorem two_ty : Γ ⊢ (ƛ "s" : `"s" $ `"s" $ 𝟘) □ succ_c ⦂ ℕt := by
    apply ty_ap twice_ty
    · apply ty_lam; apply ty_succ; trivial

  -- https://plfa.github.io/Lambda/#derivation
  abbrev NatC (t : Ty) : Ty := (t =⇒ t) =⇒ t =⇒ t

  theorem two_c_ty : Γ ⊢ two_c ⦂ NatC t := by
    apply ty_lam; apply ty_lam; apply ty_ap
    · trivial
    · apply ty_ap <;> trivial

  def add_ty : Γ ⊢ add ⦂ ℕt =⇒ ℕt =⇒ ℕt := by
    apply ty_mu; apply ty_lam; apply ty_lam; apply ty_case <;> try trivial
    · apply ty_succ; apply ty_ap <;> try trivial
      · apply ty_ap <;> trivial

  theorem add_c_ty : Γ ⊢ add_c ⦂ NatC t =⇒ NatC t =⇒ NatC t := by
    repeat apply ty_lam <;> try trivial
    · repeat apply ty_ap <;> try trivial

  -- https://plfa.github.io/Lambda/#exercise-mul-recommended-1
  def mul_ty : Γ ⊢ mul ⦂ ℕt =⇒ ℕt =⇒ ℕt := by
    -- TODO: Can we simplify this𝟘?
    apply ty_mu; apply ty_lam; apply ty_lam; apply ty_case
    · trivial
    · exact ty_zero
    · apply ty_ap
      · apply ty_ap <;> try trivial
        · apply ty_mu; apply ty_lam; apply ty_lam; apply ty_case <;> try trivial
          · apply ty_succ; apply ty_ap <;> try trivial
            · apply ty_ap <;> trivial
      · repeat apply ty_ap; repeat trivial

  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice-1
  theorem mul_c_ty : Γ ⊢ mul_c ⦂ NatC t =⇒ NatC t =⇒ NatC t := by
    repeat apply ty_lam <;> try trivial
    · repeat apply ty_ap <;> try trivial
end Context

section examples
  open Term Context Lookup IsTy

  -- https://plfa.github.io/Lambda/#non-examples
  example : ∅ ⊬ 𝟘 □ 1 := by
    by_contra h; simp_all; cases h.some; contradiction

  abbrev ill_lam := ƛ "x" : `"x" □ `"x"

  lemma nty_ill_lam : ∅ ⊬ ill_lam := by
    by_contra h; simp_all
    let ty_lam (ty_ap (ty_var hx) (ty_var hx')) := h.some
    have := Lookup.functional hx hx'; simp_all

  -- https://plfa.github.io/Lambda/#quiz-3
  example : ∅ :< "y" ⦂ ℕt =⇒ ℕt :< "x" ⦂ ℕt ⊢ `"y" □ `"x" ⦂ ℕt := by
    apply ty_ap <;> trivial

  example : ∅ :< "y" ⦂ ℕt =⇒ ℕt :< "x" ⦂ ℕt ⊬ `"x" □ `"y" := by
    by_contra h; simp_all
    let ⟨ht⟩ := h
    cases ht; rename_i hy hx
    · cases hx; rename_i ty hx
      · cases hx; contradiction

  example : ∅ :< "y" ⦂ ℕt =⇒ ℕt ⊢ ƛ "x" : `"y" □ `"x" ⦂ ℕt =⇒ ℕt := by
    apply ty_lam; apply ty_ap <;> trivial

  example : ∅ :< "x" ⦂ tx ⊬ `"x" □ `"x" := by
    by_contra h; simp_all
    let ⟨ht⟩ := h
    cases ht; rename_i hx
    · cases hx; rename_i hx
      · cases hx <;> contradiction

  example
  : ∅ :< "x" ⦂ ℕt =⇒ ℕt :< "y" ⦂ ℕt =⇒ ℕt
  ⊢ ƛ "z" : (`"x" $ `"y" $ `"z") ⦂ ℕt =⇒ ℕt
  := by
    apply ty_lam; apply ty_ap <;> try trivial
    · apply ty_ap <;> trivial
end examples
