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
example : TermS := add □ two □ two

/--
The Church numeral Ty.
-/
abbrev Ch (t : Ty := ℕt) : Ty := (t =⇒ t) =⇒ t =⇒ t

-- Church encoding...
abbrev succC : TermI := ƛ "n" : ι `"n"
abbrev oneC : TermI := ƛ "s" : ƛ "z" : `"s" $ `"z"
abbrev twoC : TermI := ƛ "s" : ƛ "z" : `"s" $ `"s" $ `"z"
abbrev addC : TermS :=
  (ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" □ `"s" $ `"n" □ `"s" □ `"z"
  ).the (Ch =⇒ Ch =⇒ Ch)
-- Note that the typing is only required for `addC` due to the rule for `ap`.
example : TermS := addC □ twoC □ twoC □ 𝟘

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
  intro n ai; is_empty; intro ⟨a, i⟩; refine ai.false ⟨a, ?_⟩
  cases i <;> trivial

def Context.Lookup.lookup (Γ : Context) (x : Sym) : PDecidable (Σ a, Γ ∋ x ⦂ a) := by
  match Γ, x with
  | [], _ => right; is_empty; intro.
  | ⟨y, b⟩ :: Γ, x =>
    if h : x = y then
      left; subst h; exact ⟨b, .z⟩
    else match lookup Γ x with
    | .inl ⟨a, i⟩ => left; refine ⟨a, .s ?_ i⟩; trivial
    | .inr n => right; refine empty_ext_empty ?_ n; trivial

export Context.Lookup (lookup)
open Context.Lookup (lookup)

-- https://plfa.github.io/Inference/#promoting-negations
lemma TyS.empty_arg
: Γ ⊢ l ↥ a =⇒ b
→ IsEmpty (Γ ⊢ m ↧ a)
→ IsEmpty (Σ b', Γ ⊢ l □ m ↥ b')
:= by
  intro tl n; is_empty; intro ⟨b', .ap tl' tm'⟩
  injection TyS.unique tl tl'; rename_i h _; apply n.false; rwa [←h] at tm'

lemma TyS.empty_switch : Γ ⊢ m ↥ a → a ≠ b → IsEmpty (Γ ⊢ m ↥ b) := by
  intro ta n; is_empty; intro tb; have := TyS.unique ta tb; contradiction
