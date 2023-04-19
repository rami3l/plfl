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
  -- " · " is `infixl` in the book, but here we choose to use `infixr`.
  infixr:70 " $ " => ap
  prefix:80 " ι " => succ
  prefix:90 " ` " => var

  def o : Term := zero

  example : Term := `"foo"
  example : Term := ? `"bar" [zero: o |succ "n" : ι o]

  def one : Term := ι o
  def two : Term := ι ι o

  def add : Term := μ "+" : ƛ "m" : ƛ "n" : ? `"m" [zero: `"n" |succ "m": ι ((`"+" $ `"m") $ `"n")]
  -- https://plfa.github.io/Lambda/#exercise-mul-recommended
  def mul : Term := μ "*" : ƛ "m" : ƛ "n" : ? `"m" [zero: o |succ "m": (`"+" $ `"n") $ ((`"*" $ `"m") $ `"n")]

  -- Church encoding...
  def one_c : Term := ƛ "s" : ƛ "z" : `"s" $ `"z"
  def two_c : Term := ƛ "s" : ƛ "z" : `"s" $ `"s" $ `"z"
  def succ_c : Term := ƛ "n" : ι `"n"
  def add_c : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : (`"m" $ `"s") $ ((`"n" $ `"s") $ `"z")
  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice
  def mul_c : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : `"m" $ (`"n" $ `"s") $ `"z"
end Term

-- https://plfa.github.io/Lambda/#values
inductive Value : Term → Prop where
| lam : Value (ƛ v : d)
| zero: Value o
| succ: Value n → Value (ι n)

-- https://plfa.github.io/Lambda/#substitution
namespace Term
  /--
  `x.subst y v` substitutes term `v` for all free occurrences of variable `y` in term `x`.
  -/
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
  : (ƛ "z" : (`"s" $ `"s") $ `"z")["s" := succ_c]
  = (ƛ "z" : (succ_c $ succ_c) $ `"z") := rfl

  example : ((succ_c $ succ_c) $ `"z")["z" := o] = (succ_c $ succ_c) $ o := rfl
  example : (ƛ "x" : `"y")["y" := o] = (ƛ "x" : o) := rfl
  example : (ƛ "x" : `"x")["x" := o] = (ƛ "x" : `"x") := rfl
  example : (ƛ "y" : `"y")["x" := o] = (ƛ "y" : `"y") := rfl

  -- https://plfa.github.io/Lambda/#quiz
  example
  : (ƛ "y" : `"x" $ (ƛ "x" : `"x"))["x" := o]
  = (ƛ "y" : o $ (ƛ "x" : `"x"))
  := rfl

  -- https://plfa.github.io/Lambda/#reduction
  /--
  `Reduce t t'` says that `t` reduces to `t'`.
  -/
  inductive Reduce : Term → Term → Prop where
  | ξ_ap₁ : Reduce l l' → Reduce (l $ m) (l' $ m)
  | ξ_ap₂ : Value v → Reduce m m' → Reduce (v $ m) (v $ m')
  | β_lam : Value v → Reduce ((ƛ x : n) $ v) (n[x := v])
  | ξ_succ : Reduce m m' → Reduce (ι m) (ι m')
  | ξ_case : Reduce l l' → Reduce (? l [zero: m |succ x : n]) (? l' [zero: m |succ x : n])
  | β_zero : Reduce (? o [zero: m |succ x : n]) m
  | β_succ : Value v → Reduce (? ι v [zero: m |succ x : n]) (n[x := v])
  | β_mu : Reduce (μ x : m) (m[x := μ x : m])

  infix:40 " —→ " => Reduce
end Term

namespace Term.Reduce
  -- https://plfa.github.io/Lambda/#quiz-1
  example : ((ƛ "x" : `"x") $ (ƛ "x" : `"x")) —→ (ƛ "x" : `"x") := by
    apply β_lam; exact Value.lam

  example
  : (((ƛ "x" : `"x") $ (ƛ "x" : `"x")) $ (ƛ "x" : `"x"))
  —→ ((ƛ "x" : `"x") $ (ƛ "x" : `"x"))
  := by
    apply ξ_ap₁; apply β_lam; exact Value.lam

  example
  : ((two_c $ succ_c) $ o)
  —→ ((ƛ "z" : succ_c $ succ_c $ `"z") $ o)
  := by
    unfold two_c; apply ξ_ap₁; apply β_lam; exact Value.lam

  -- https://plfa.github.io/Lambda/#reflexive-and-transitive-closure
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  inductive Clos : Term → Term → Prop where
  | step : (m —→ n) → Clos m n
  | refl : Clos m m
  | trans : Clos l m → Clos m n → Clos l n

  infix:20 " —↠ " => Clos

  instance preorder : Preorder Term where
    le := Clos
    le_refl := by simp [Clos.refl]
    le_trans := by intros; apply Clos.trans <;> trivial
end Reduce
