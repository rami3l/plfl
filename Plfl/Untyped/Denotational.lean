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

namespace Value
  inductive Subset : Value → Value → Type where
  | bot : Subset ⊥ v
  | conjL : Subset v u → Subset w u → Subset (v ⊔ w) u
  | conjR₁ : Subset u v → Subset u (v ⊔ w)
  | conjR₂ : Subset u w → Subset u (v ⊔ w)
  | trans : Subset u v → Subset v w → Subset u w
  | fn : Subset v' v → Subset w w' → Subset (v ⇾ w) (v' ⇾ w')
  | dist : Subset (v ⇾ (w ⊔ w')) ((v ⇾ w) ⊔ (v ⇾ w'))

  instance : Trans Subset Subset Subset where trans := .trans
end Value
