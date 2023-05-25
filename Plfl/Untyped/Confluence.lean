-- https://plfa.github.io/Confluence/

import Plfl.Init
import Plfl.Untyped
import Plfl.Untyped.Substitution

import Mathlib.Tactic

namespace Confluence

open Untyped.Notation

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

  abbrev Clos {Γ a} := Relation.ReflTransGen (α := Γ ⊢ a) PReduce
end PReduce

namespace Notation
  scoped infix:20 " ⇛ " => PReduce
  scoped infix:20 " ⇛* " => PReduce.Clos
end Notation

open Notation

namespace PReduce.Clos
  instance : Coe (m ⇛ n) (m ⇛* n) where coe := .single

  @[refl] abbrev refl : m ⇛* m := .refl
  abbrev tail : (m ⇛* n) → (n ⇛ n') → (m ⇛* n') := .tail
  abbrev head : (m ⇛ n) → (n ⇛* n') → (m ⇛* n') := .head
  abbrev single : (m ⇛ n) → (m ⇛* n) := .single
end PReduce.Clos

namespace PReduce
  instance : IsRefl (Γ ⊢ a) PReduce where refl := .refl

  instance : Trans (α := Γ ⊢ a) Clos Clos Clos where trans := .trans
  instance : Trans (α := Γ ⊢ a) Clos PReduce Clos where trans c r := c.tail r
  instance : Trans (α := Γ ⊢ a) PReduce PReduce Clos where trans r r' := .tail r r'
  instance : Trans (α := Γ ⊢ a) PReduce Clos Clos where trans r c := .head r c

  -- https://plfa.github.io/Confluence/#equivalence-between-parallel-reduction-and-reduction
  def fromReduce {Γ a} {m n : Γ ⊢ a} : m —→ n → (m ⇛ n) := by intro
  | .lamβ => refine .lamβ ?rn ?rv <;> rfl
  | .lamζ rn => refine .lamζ ?_; exact fromReduce rn
  | .apξ₁ rl => refine .apξ ?_ (by rfl); exact fromReduce rl
  | .apξ₂ rm => refine .apξ (by rfl) ?_; exact fromReduce rm

  def toReduceClos : (m ⇛ n) → (m —↠ n) := open Untyped.Reduce in by intro
  | .var => rfl
  | .lamβ rn rv => rename_i n n' v v'; calc (ƛ n) □ v
    _ —↠ (ƛ n') □ v := by refine ap_congr₁ (toReduceClos ?_); exact .lamζ rn
    _ —↠ (ƛ n') □ v' := ap_congr₂ rv.toReduceClos
    _ —→ n' ⇷ v' := .lamβ
  | .lamζ rn => apply lam_congr; exact rn.toReduceClos
  | .apξ rl rm => rename_i l l' m m'; calc l □ m
    _ —↠ l' □ m := ap_congr₁ rl.toReduceClos
    _ —↠ l' □ m' := ap_congr₂ rm.toReduceClos
end PReduce

instance : (m ⇛* n) ≃ (m —↠ n) where
  toFun (rs : m ⇛* n) : m —↠ n := by
    refine .head_induction_on rs ?_ ?_
    · rfl
    · introv; intro r _ rs; refine .trans ?_ rs; exact r.toReduceClos

  invFun (rs : m —↠ n) : m ⇛* n := by
    refine .head_induction_on rs ?_ ?_
    · rfl
    · introv; intro r _ rs; refine .head ?_ rs; exact .fromReduce r

  left_inv _ := by simp only
  right_inv _ := by simp only

open Untyped.Subst
open Substitution

-- https://plfa.github.io/Confluence/#substitution-lemma-for-parallel-reduction
abbrev par_subst (σ : Subst Γ Δ) (σ' : Subst Γ Δ) := ∀ {a} {x : Γ ∋ a}, σ x ⇛ σ' x

section
  @[simp]
  lemma par_rename {ρ : Rename Γ Δ} {m m' : Γ ⊢ a} : (m ⇛ m') → (rename ρ m ⇛ rename ρ m')
  := open PReduce in by intro
  | .var => exact .var
  | .lamζ rn => apply lamζ; apply par_rename; trivial
  | .apξ rl rm => apply apξ <;> (apply par_rename; trivial)
  | .lamβ rn rv =>
    rename_i n n' v v'; have rn' := par_rename (ρ := ext ρ) rn; have rv' := par_rename (ρ := ρ) rv
    have := lamβ rn' rv'; rwa [rename_subst_comm] at this

  @[simp]
  theorem par_subst_exts {σ τ : Subst Γ Δ} (s : par_subst σ τ)
  : ∀ {b}, par_subst (exts (b := b) σ) (exts τ)
  := by
    intro _ _; intro
    | .z => exact .var
    | .s i => exact par_rename s
end
