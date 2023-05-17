-- https://plfa.github.io/Inference/

import Plfl.Init
import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

namespace Inference

-- https://plfa.github.io/Inference/#syntax
open String

def Sym : Type := String deriving BEq, DecidableEq, Repr

inductive Ty where
/-- Native natural type made of 𝟘 and ι. -/
| nat : Ty
/-- Arrow type. -/
| fn : Ty → Ty → Ty
/-- Product type. -/
| prod: Ty → Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Notations
  open Ty

  scoped notation "ℕt" => nat
  scoped infixr:70 " =⇒ " => fn

  instance : Mul Ty where mul := .prod
end Notations

open Notations

abbrev Context : Type := List (Sym × Ty)

namespace Context
  abbrev extend (c : Context) (s : Sym) (t : Ty) : Context := ⟨s, t⟩ :: c
end Context

namespace Notation
  open Context

 -- The goal is to make `_‚_⦂_` work like an `infixl`.
  -- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html#From-Precedence-to-Binding-Power
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  notation:50 c "‚ " s:51 " ⦂ " t:51 => extend c s t
end Notation

open Notation

/-
An attribute is said to be Synthesized,
if its parse tree node value is determined by the attribute value at its *child* nodes.

An attribute is said to be Inherited,
if its parse tree node value is determined by the attribute value at its *parent and/or siblings*.

<https://www.geeksforgeeks.org/differences-between-synthesized-and-inherited-attributes/>
-/

mutual
  /--
  A term with synthesized types.
  The main term in an eliminator is typed via synthesis.
  -/
  inductive TermS where
  | var : Sym → TermS
  | ap : TermS → TermI → TermS
  | prod : TermS → TermS → TermS
  | syn : TermI → Ty → TermS
  deriving BEq, Repr
  -- * `DecidableEq` derivations are not yet supported in `mutual` blocks.
  -- See: <https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.22default.20handlers.22.20when.20deriving.20DecidableEq/near/275722237>

  /--
  A term with inherited types.
  Constructors are typed via inheritance.
  -/
  inductive TermI where
  | lam : Sym → TermI → TermI
  | zero : TermI
  | succ : TermI → TermI
  | case : TermS → TermI → Sym → TermI → TermI
  | mu : Sym → TermI → TermI
  | fst : TermS → TermI
  | snd : TermS → TermI
  | inh : TermS → TermI
  deriving BEq, Repr
end

namespace Notation
  open TermS TermI

  scoped notation:50 " ƛ " v " : " d => lam v d
  scoped notation:50 " μ " v " : " d => mu v d
  scoped notation:max " 𝟘? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  scoped infixr:min " $ " => ap
  -- scoped infix:60 " ↓ " => syn
  -- scoped postfix:60 "↑ " => inh
  scoped infixl:70 " □ " => ap
  scoped prefix:80 " ι " => succ
  scoped prefix:90 " ` " => var
  scoped notation " 𝟘 " => zero
end Notation

-- https://plfa.github.io/Inference/#example-terms
abbrev two : TermI := ι ι 𝟘

-- * The coercion can only happen in this direction,
-- since the other direction requires an extra type annotation.
instance : Coe TermS TermI where coe := TermI.inh

@[simp] abbrev TermI.the := TermS.syn

abbrev add : TermS :=
  (μ "+" : ƛ "m" : ƛ "n" :
    𝟘? `"m"
      [zero: `"n"
      |succ "m" : ι (`"+" □ `"m" □ `"n")]
  ).the (ℕt =⇒ ℕt =⇒ ℕt)

abbrev mul : TermS :=
  (μ "*" : ƛ "m" : ƛ "n" :
    𝟘? `"m"
    [zero: 𝟘
    |succ "m": add □ `"n" $ `"*" □ `"m" □ `"n"]
  ).the (ℕt =⇒ ℕt =⇒ ℕt)

-- Note that the typing is only required for `add` due to the rule for `ap`.
abbrev four : TermS := add □ two □ two

/--
The Church numeral Ty.
-/
@[simp] abbrev Ch (t : Ty := ℕt) : Ty := (t =⇒ t) =⇒ t =⇒ t

-- Church encoding...
abbrev succC : TermI := ƛ "n" : ι `"n"
abbrev oneC : TermI := ƛ "s" : ƛ "z" : `"s" $ `"z"
abbrev twoC : TermI := ƛ "s" : ƛ "z" : `"s" $ `"s" $ `"z"
abbrev addC : TermS :=
  (ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" □ `"s" $ `"n" □ `"s" □ `"z"
  ).the (Ch =⇒ Ch =⇒ Ch)
-- Note that the typing is only required for `addC` due to the rule for `ap`.
abbrev four' : TermS := addC □ twoC □ twoC □ succC □ 𝟘

-- https://plfa.github.io/Inference/#bidirectional-type-checking
/--
A lookup judgement.
`Lookup c s ts` means that `s` is of type `ts` by _looking up_ the context `c`.
-/
inductive Context.Lookup : Context → Sym → Ty → Type where
| z : Lookup (Γ‚ x ⦂ a) x a
| s : x ≠ y → Lookup Γ x a → Lookup (Γ‚ y ⦂ b) x a
deriving DecidableEq

namespace Context.Lookup
  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/tactics.md#tactics-by-macro-expansion
  /--
  `elem` validates the type of a variable by looking it up in the current context.
  This tactic fails when the lookup fails.
  -/
  scoped syntax "elem" : tactic
  macro_rules
  | `(tactic| elem) =>
    `(tactic| repeat (first | apply Lookup.s (by trivial) | exact Lookup.z))

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  scoped syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic| exact Lookup.z)
  | n+1 => `(tactic| apply Lookup.s (by trivial); get_elem $(Lean.quote n))
end Context.Lookup

export Context (Lookup)
open Context (Lookup)

namespace Notation
  open Context Lookup

  scoped notation:40 c " ∋ " s " ⦂ " t:51 => Lookup c s t
  scoped macro " ♯ " n:term:90 : term => `(by get_elem $n)
end Notation

mutual
  /--
  Typing of `TermS` terms.
  -/
  inductive TyS : Context → TermS → Ty → Type where
  | var : Γ ∋ x ⦂ a → TyS Γ (` x) a
  | ap: TyS Γ l (a =⇒ b) → TyI Γ m a → TyS Γ (l □ m) b
  | prod: TyS Γ m a → TyS Γ n b → TyS Γ (.prod m n) (a * b)
  | syn : TyI Γ m a → TyS Γ (m.the a) a

  /--
  Typing of `TermI` terms.
  -/
  inductive TyI : Context → TermI → Ty → Type where
  | lam : TyI (Γ‚ x ⦂ a) n b → TyI Γ (ƛ x : n) (a =⇒ b)
  | zero : TyI Γ 𝟘 ℕt
  | succ : TyI Γ m ℕt → TyI Γ (ι m) ℕt
  | case
  : TyS Γ l ℕt → TyI Γ m a → TyI (Γ‚ x ⦂ ℕt) n a
  → TyI Γ (𝟘? l [zero: m |succ x : n]) a
  | mu : TyI (Γ‚ x ⦂ a) n a → TyI Γ (μ x : n) a
  | fst: TyS Γ mn (a * b) → TyI Γ (.fst mn) a
  | snd: TyS Γ mn (a * b) → TyI Γ (.snd mn) b
  | inh : TyS Γ m a → TyI Γ m a
end

instance : Coe (TyI Γ m a) (TyS Γ (m.the a) a) where coe := TyS.syn
instance : Coe (TyS Γ m a) (TyI Γ m a) where coe := TyI.inh

namespace Notation
  scoped notation:40 Γ " ⊢ " m " ↥ " a:51 => TyS Γ m a
  scoped notation:40 Γ " ⊢ " m " ↟ " a:51 => TyS Γ (TermS.syn m a) a
  scoped notation:40 Γ " ⊢ " m " ↧ " a:51 => TyI Γ m a
end Notation

abbrev twoTy : Γ ⊢ two ↟ ℕt := open TyS TyI in by
  apply_rules [syn, succ, zero]

abbrev addTy : Γ ⊢ add ↥ (ℕt =⇒ ℕt =⇒ ℕt) := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh]
  <;> elem

-- https://plfa.github.io/Inference/#bidirectional-mul
abbrev mulTy : Γ ⊢ mul ↥ (ℕt =⇒ ℕt =⇒ ℕt) := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addTy]
  <;> elem

abbrev twoCTy : Γ ⊢ twoC ↧ Ch := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh]
  <;> elem

abbrev addCTy : Γ ⊢ addC ↥ (Ch =⇒ Ch =⇒ Ch) := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh]
  <;> elem

-- https://plfa.github.io/Inference/#bidirectional-products
example : Γ ⊢ .prod (two.the ℕt) add ↥ ℕt * (ℕt =⇒ ℕt =⇒ ℕt)
:= open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    twoTy, addTy]
  <;> elem

example : Γ ⊢ .fst (.prod (two.the ℕt) add) ↟ ℕt
:= open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    twoTy]
  <;> elem

example : Γ ⊢ .snd (.prod (two.the ℕt) add) ↟ (ℕt =⇒ ℕt =⇒ ℕt)
:= open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addTy]
  <;> elem

-- https://plfa.github.io/Inference/#prerequisites

/-
Nothing to do. Relevant definitions have been derived.
-/

-- https://plfa.github.io/Inference/#unique-types
@[simp]
theorem Context.Lookup.unique (i : Γ ∋ x ⦂ a) (j : Γ ∋ x ⦂ b) : a = b := by
  cases i with try trivial
  | z => cases j <;> trivial
  | s => cases j with try trivial
    | s => apply unique <;> trivial

@[simp]
theorem TyS.unique (t : Γ ⊢ x ↥ a) (u : Γ ⊢ x ↥ b) : a = b := by
  match t with
  | .var i => cases u with | var j => apply Lookup.unique <;> trivial
  | .ap l _ => cases u with | ap l' _ => injection unique l l'
  | .prod m n => cases u with | prod m' n' => congr; exact unique m m'; exact unique n n'
  | .syn _ => cases u with | syn _ => trivial

-- https://plfa.github.io/Inference/#lookup-type-of-a-variable-in-the-context
lemma Context.Lookup.empty_ext_empty
: x ≠ y
→ IsEmpty (Σ a, Γ ∋ x ⦂ a)
→ IsEmpty (Σ a, Γ‚ y ⦂ b ∋ x ⦂ a)
:= by
  intro n ai; is_empty; intro ⟨a, i⟩; apply ai.false; exists a
  cases i <;> trivial

def Context.Lookup.lookup (Γ : Context) (x : Sym) : PDecidable (Σ a, Γ ∋ x ⦂ a) := by
  match Γ, x with
  | [], _ => left; is_empty; intro.
  | ⟨y, b⟩ :: Γ, x =>
    if h : x = y then
      right; subst h; exact ⟨b, .z⟩
    else match lookup Γ x with
    | .inr ⟨a, i⟩ => right; refine ⟨a, .s ?_ i⟩; trivial
    | .inl n => left; refine empty_ext_empty ?_ n; trivial

export Context.Lookup (lookup)
open Context.Lookup (lookup)

-- https://plfa.github.io/Inference/#promoting-negations
lemma TyS.empty_arg
: Γ ⊢ l ↥ a =⇒ b
→ IsEmpty (Γ ⊢ m ↧ a)
→ IsEmpty (Σ b', Γ ⊢ l □ m ↥ b')
:= by
  intro tl n; is_empty; intro ⟨b', .ap tl' tm'⟩
  injection tl.unique tl'; rename_i h _; apply n.false; rwa [←h] at tm'

lemma TyS.empty_switch : Γ ⊢ m ↥ a → a ≠ b → IsEmpty (Γ ⊢ m ↥ b) := by
  intro ta n; is_empty; intro tb; have := ta.unique tb; contradiction

mutual
  def TermS.infer (m : TermS) (Γ : Context) : PDecidable (Σ a, Γ ⊢ m ↥ a) := by
    match m with
    | ` x => match Lookup.lookup Γ x with
      | .inr ⟨a, i⟩ => right; exact ⟨a, .var i⟩
      | .inl n => left; is_empty; intro ⟨a, .var _⟩; apply n.false; exists a
    | l □ m => match l.infer Γ with
      | .inr ⟨a =⇒ b, tab⟩ => match m.infer Γ a with
        | .inr ta => right; exact ⟨b, .ap tab ta⟩
        | .inl n => left; exact tab.empty_arg n
      | .inr ⟨ℕt, t⟩ => left; is_empty; intro ⟨_, .ap tl _⟩; injection t.unique tl
      | .inr ⟨_ * _, t⟩ => left; is_empty; intro ⟨_, .ap tl _⟩; injection t.unique tl
      | .inl n => left; is_empty; intro ⟨a, .ap tl _⟩; rename_i b _; exact n.false ⟨b =⇒ a, tl⟩
    | .prod m n => match m.infer Γ, n.infer Γ with
      | .inr ⟨a, tm⟩, .inr ⟨b, tn⟩ => right; exact ⟨a * b, tm.prod tn⟩
      | .inr _, .inl nn => left; is_empty; intro ⟨_, tmn⟩; cases tmn; apply nn.false; constructor <;> trivial
      | .inl nm, _ => left; is_empty; intro ⟨_, .prod tm _⟩; apply nm.false; constructor <;> trivial
    | .syn m a => match m.infer Γ a with
      | .inr t => right; exact ⟨a, t⟩
      | .inl n => left; is_empty; intro ⟨a', t'⟩; cases t'; apply n.false; trivial

  def TermI.infer (m : TermI) (Γ : Context) (a : Ty) : PDecidable (Γ ⊢ m ↧ a) := by
    match m with
    | ƛ x : n => match a with
      | a =⇒ b => match n.infer (Γ‚ x ⦂ a) b with
        | .inr t => right; exact .lam t
        | .inl n => left; is_empty; intro (.lam t); exact n.false t
      | ℕt => left; is_empty; intro.
      | _ * _ => left; is_empty; intro.
    | 𝟘 => match a with
      | ℕt => right; exact .zero
      | _ =⇒ _ => left; is_empty; intro.
      | _ * _ => left; is_empty; intro.
    | ι n => match a with
      | ℕt => match n.infer Γ ℕt with
        | .inr t => right; exact .succ t
        | .inl n => left; is_empty; intro (.succ t); exact n.false t
      | _ =⇒ _ => left; is_empty; intro.
      | _ * _ => left; is_empty; intro.
    | .case l m x n => match l.infer Γ with
      | .inr ⟨ℕt, tl⟩ => match m.infer Γ a, n.infer (Γ‚ x ⦂ ℕt) a with
        | .inr tm, .inr tn => right; exact .case tl tm tn
        | .inl nm, _ => left; is_empty; intro (.case _ _ _); apply nm.false; trivial
        | .inr _, .inl nn => left; is_empty; intro (.case _ _ _); apply nn.false; trivial
      | .inr ⟨_ =⇒ _, tl⟩ => left; is_empty; intro (.case t _ _); injection t.unique tl
      | .inr ⟨_ * _, tl⟩ => left; is_empty; intro (.case t _ _); injection t.unique tl
      | .inl nl => left; is_empty; intro (.case _ _ _); apply nl.false; constructor <;> trivial
    | μ x : n => match n.infer (Γ‚ x ⦂ a) a with
      | .inr t => right; exact .mu t
      | .inl n => left; is_empty; intro (.mu t); exact n.false t
    | .fst m => match m.infer Γ with
      | .inr ⟨b * _, tm⟩ => if h : a = b then
          right; subst h; exact .fst tm
        else
          left; is_empty; intro (.fst t); injection t.unique tm; contradiction
      | .inr ⟨ℕt, tm⟩ => left; is_empty; intro (.fst t); injection t.unique tm
      | .inr ⟨_ =⇒ _, tm⟩ => left; is_empty; intro (.fst t); injection t.unique tm
      | .inl n => left; is_empty; intro (.fst t); apply n.false; constructor <;> trivial
    | .snd m => match m.infer Γ with
      | .inr ⟨_ * b, tm⟩ => if h : a = b then
          right; subst h; exact .snd tm
        else
          left; is_empty; intro (.snd t); injection t.unique tm; contradiction
      | .inr ⟨ℕt, tm⟩ => left; is_empty; intro (.snd t); injection t.unique tm
      | .inr ⟨_ =⇒ _, tm⟩ => left; is_empty; intro (.snd t); injection t.unique tm
      | .inl n => left; is_empty; intro (.snd t); apply n.false; constructor <;> trivial
    | .inh m => match m.infer Γ with
      | .inr ⟨b, tm⟩ => if h : a = b then
          right; subst h; exact .inh tm
        else
          left; rw [←Ne.def] at h; is_empty; intro (.inh _)
          apply (tm.empty_switch h.symm).false; trivial
      | .inl nm => left; is_empty; intro (.inh tm); apply nm.false; exists a
end
termination_by
  TermS.infer m Γ => sizeOf m
  TermI.infer n Γ a => sizeOf n

-- https://plfa.github.io/Inference/#testing-the-example-terms
abbrev fourTy : Γ ⊢ four ↥ ℕt := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addTy, twoTy]
  <;> elem

example : four.infer ∅ = .inr ⟨ℕt, fourTy⟩ := by rfl

abbrev four'Ty : Γ ⊢ four' ↥ ℕt := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addCTy, twoCTy]
  <;> elem

example : four'.infer ∅ = .inr ⟨ℕt, four'Ty⟩ := by rfl

abbrev four'': TermS := mul □ two □ two

abbrev four''Ty : Γ ⊢ four'' ↥ ℕt := open TyS TyI Context.Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addCTy, twoCTy]
  <;> elem

example : four''.infer ∅ = .inr ⟨ℕt, four''Ty⟩ := by rfl

-- https://plfa.github.io/Inference/#testing-the-error-cases

/-
Sadly this won't work for now due to limitations with mutual recursions.
See: <https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Proof.20of.20an.20inductive's.20variant.3F/near/358901115>
-/

-- example := show ((ƛ "x" : `"y").the (ℕt =⇒ ℕt)).infer ∅ = .inl _ by rfl

/-
This won't work either, probably due to similar reasons...
-/

-- instance : Decidable (Nonempty (Σ a, Γ ⊢ m ↥ a)) := (m.infer Γ).toDecidable

-- example := let m := (ƛ "x" : `"y").the (ℕt =⇒ ℕt); show IsEmpty (Σ a, ∅ ⊢ m ↥ a) by
--   rw [←not_nonempty_iff]; decide
