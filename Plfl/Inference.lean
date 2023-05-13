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
deriving BEq, DecidableEq, Repr

namespace Notations
  open Ty

  scoped notation "ℕt" => nat
  scoped infixr:70 " =⇒ " => fn
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

/--
A lookup judgement.
`Lookup c s ts` means that `s` is of type `ts` by _looking up_ the context `c`.
-/
inductive Context.Lookup : Context → Sym → Ty → Type where
| z : Lookup (Γ‚ x ⦂ tx) x tx
| s : x ≠ y → Lookup Γ x tx → Lookup (Γ‚ y ⦂ ty) x tx
deriving DecidableEq

namespace Notation
  notation:40 c " ∋ " s " ⦂ " t:51 => Context.Lookup c s t
end Notation

mutual
  /--
  A term with synthesized types.
  The main term in an eliminator is typed via synthesis.
  -/
  inductive TermS where
  | var : Sym → TermS
  | ap : TermS → TermI → TermS
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
  | inh : TermS → TermI
  deriving BEq, Repr
end

namespace Notation
  open TermS TermI

  scoped notation:50 " ƛ " v " : " d => lam v d
  scoped notation:50 " μ " v " : " d => mu v d
  scoped notation:max " 𝟘? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  scoped infixr:min " $ " => ap
  scoped infix:60 " ↓ " => syn
  scoped postfix:60 "↑ " => inh
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

abbrev add : TermS :=
  (μ "p" : ƛ "m" : ƛ "n" :
    𝟘? (`"m")
    [zero: `"n"
    |succ "m" : ι (`"p" □ (`"m") □ (`"n"))]
  ) ↓ (ℕt =⇒ ℕt =⇒ ℕt)
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
  (ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" □ `"s" $ `"n" □ `"s" □ `"z")
  ↓ (Ch =⇒ Ch =⇒ Ch)
-- Note that the typing is only required for `addC` due to the rule for `ap`.
example : TermS := addC □ twoC □ twoC □ 𝟘
