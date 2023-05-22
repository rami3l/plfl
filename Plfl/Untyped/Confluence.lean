-- https://plfa.github.io/Confluence/

import Plfl.Init
import Plfl.Untyped

import Mathlib.Tactic

set_option tactic.simp.trace true

namespace Confluence

open Untyped Untyped.Notation

-- https://plfa.github.io/Confluence/#parallel-reduction
/--
Parallel reduction.
-/
inductive PReduce : (Γ ⊢ a) → (Γ ⊢ a) → Prop where
| var : PReduce (` x) (` x)
| lamβ : PReduce n n' → PReduce v v' → PReduce ((ƛ n) □ v) (n' ⇷ v')
| lamζ : PReduce n n' → PReduce (ƛ n) (ƛ n')
| apξ : PReduce l l' → PReduce m m' → PReduce (l □ m) (l' □ m')

namespace PReduce
  @[refl]
  theorem refl (m : Γ ⊢ a) : PReduce m m := by
    match m with
    | ` i => exact .var
    | ƛ n => apply lamζ; apply refl
    | l □ m => apply apξ <;> apply refl

  abbrev Clos {Γ a} := Relation.TransGen (α := Γ ⊢ a) PReduce
end PReduce

namespace Notation
  scoped infix:20 " ⇛ " => PReduce
  scoped infix:20 " ⇛* " => PReduce.Clos
end Notation

open Notation

namespace PReduce
  instance : IsRefl (Γ ⊢ a) PReduce where refl := .refl

  instance : Coe (m ⇛ n) (m ⇛* n) where coe := .single

  instance : Trans (α := Γ ⊢ a) Clos Clos Clos where trans := .trans
  instance : Trans (α := Γ ⊢ a) Clos PReduce Clos where trans c r := c.tail r
  instance : Trans (α := Γ ⊢ a) PReduce PReduce Clos where trans r r' := .tail r r'
  instance : Trans (α := Γ ⊢ a) PReduce Clos Clos where trans r c := .head r c
end PReduce
