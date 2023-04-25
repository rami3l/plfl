-- https://plfa.github.io/Properties/

import Mathlib.CategoryTheory.Iso

import Plfl.Lambda

set_option tactic.simp.trace true

open Context Context.IsTy Term.Reduce
open Sum

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))

-- https://plfa.github.io/Properties/#values-do-not-reduce
@[simp]
def Value.not_reduce : Value m → ∀ {n}, IsEmpty (m —→ n) := by
  introv v; is_empty; intro r
  cases v <;> try contradiction
  · case succ v => cases r; · case succ_ξ => apply (not_reduce v).false; trivial

@[simp]
def Reduce.not_value : m —→ n → IsEmpty (Value m) := by
  intro r; is_empty; intro v
  have : ∀ {n}, IsEmpty (m —→ n) := Value.not_reduce v
  exact this.false r

-- https://plfa.github.io/Properties/#exercise-canonical--practice
inductive Canonical : Term → Ty → Type where
| can_lam : (∅ :< x ⦂ tx ⊢ n ⦂ tn) → Canonical (ƛ x : n) (tx =⇒ tn)
| can_zero : Canonical 𝟘 ℕt
| can_succ : Canonical n ℕt → Canonical (ι n) ℕt

namespace Canonical
  @[simp]
  def ofIsTy : (∅ ⊢ m ⦂ t) → Value m → Canonical m t
  | ty_lam l, Value.lam => can_lam l
  | ty_zero, V𝟘 => can_zero
  | ty_succ t, Value.succ m => can_succ <| ofIsTy t m

  @[simp]
  def well_typed_hom : Canonical v t → (∅ ⊢ v ⦂ t) × Value v := by
    intro
    | can_lam h => exact ⟨ty_lam h, Value.lam⟩
    | can_zero => exact ⟨ty_zero, V𝟘⟩
    | can_succ h => have ⟨ty, v⟩ := well_typed_hom h; exact ⟨ty_succ ty, Value.succ v⟩

  @[simp]
  def well_typed_inv : (∅ ⊢ v ⦂ t) × Value v → Canonical v t := by
    intro
    | ⟨ty_lam ty, Value.lam⟩ => exact can_lam ty
    | ⟨ty_zero, Value.zero⟩ => exact can_zero
    | ⟨ty_succ ty, Value.succ v⟩ => apply can_succ; exact well_typed_inv ⟨ty, v⟩

  def well_typed_hom_inv_id {v t} : @well_typed_inv v t ∘ well_typed_hom = id := by
    funext c; cases c <;> simp_all
    · rename_i v' c'; have := @well_typed_hom_inv_id v' ℕt
      apply_fun (· c') at this; trivial

  def well_typed_inv_hom_id {v t} : @well_typed_hom v t ∘ well_typed_inv = id := by
    funext c; match c with
    | ⟨ty_lam ty, Value.lam⟩ => simp_all
    | ⟨ty_zero, Value.zero⟩ => simp_all
    | ⟨ty_succ ty, Value.succ n⟩ =>
        rename_i v'; have := @well_typed_inv_hom_id v' ℕt;
        rw [Function.comp_apply, well_typed_inv, well_typed_hom]; split
        · simp_all; apply_fun (· (ty, n)) at this; simp_all

  /--
  The Canonical forms are exactly the well-typed values.
  -/
  @[simp]
  instance well_typed : Canonical v t ≅ (∅ ⊢ v ⦂ t) × Value v where
    hom := well_typed_hom
    inv := well_typed_inv
    hom_inv_id := well_typed_hom_inv_id
    inv_hom_id := well_typed_inv_hom_id
end Canonical

def canonical : (∅ ⊢ m ⦂ t) → Value m → Canonical m t := Canonical.ofIsTy

-- https://plfa.github.io/Properties/#progress
/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
@[aesop safe [constructors, cases]]
inductive Progress (m : Term) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m
--^ In general, the rule of thumb is to consider the easy case (`step`) before the hard case (`done`) for easier proofs.

namespace Progress
  @[simp]
  def ofIsTy : (∅ ⊢ m ⦂ t) → Progress m := by
    intro
    | ty_var _ => contradiction
    | ty_lam _ => exact done Value.lam
    | ty_ap jl jm => cases ofIsTy jl with
      | step => apply step; · apply ap_ξ₁; trivial
      | done vl => cases ofIsTy jm with
        | step => apply step; apply ap_ξ₂ <;> trivial
        | done => cases vl with
          | lam => apply step; apply lam_β; trivial
          | _ => contradiction
    | ty_zero => exact done V𝟘
    | ty_succ j => cases ofIsTy j with
      | step => apply step; apply succ_ξ; trivial
      | done => apply done; apply Value.succ; trivial
    | ty_case jl jm jn => cases ofIsTy jl with
      | step => apply step; apply case_ξ; trivial
      | done vl => cases vl with
        | lam => trivial
        | zero => exact step zero_β
        | succ => apply step; apply succ_β; trivial
    | ty_mu _ => exact step mu_β
end Progress

def progress : (∅ ⊢ m ⦂ t) → Progress m := Progress.ofIsTy

-- https://plfa.github.io/Properties/#exercise-value-practice
@[simp]
def IsTy.is_value : (∅ ⊢ m ⦂ t) → Decidable (Nonempty (Value m)) := by
  intro j; cases progress j
  · rename_i n r; have := Reduce.not_value r; apply isFalse; simp_all
  · exact isTrue ⟨by trivial⟩

@[simp]
def Progress' (m : Term) : Type := Value m ⊕ Σ n, m —→ n

namespace Progress'
  -- https://plfa.github.io/Properties/#exercise-progress-practice
  @[simp]
  def ofIsTy : (∅ ⊢ m ⦂ t) → Progress' m := by
    intro
    | ty_var _ => contradiction
    | ty_lam _ => exact inl Value.lam
    | ty_ap jl jm => match ofIsTy jl with
      | inr ⟨n, r⟩ => exact inr ⟨_, ap_ξ₁ r⟩
      | inl vl => match ofIsTy jm with
        | inr ⟨n, r⟩ => apply inr; exact ⟨_, ap_ξ₂ vl r⟩
        | inl _ => cases canonical jl vl with
          | can_lam => apply inr; refine ⟨_, lam_β ?_⟩; trivial
    | ty_zero => exact inl V𝟘
    | ty_succ j => match ofIsTy j with
      | inl v => apply inl; exact Value.succ v
      | inr ⟨n, r⟩ => exact inr ⟨_, succ_ξ r⟩
    | ty_case jl jm jn => match ofIsTy jl with
      | inr ⟨n, r⟩ => exact inr ⟨_, case_ξ r⟩
      | inl vl => cases vl with
        | lam => trivial
        | zero => exact inr ⟨_, zero_β⟩
        | succ v => exact inr ⟨_, succ_β v⟩
    | ty_mu _ => exact inr ⟨_, mu_β⟩
end Progress'

namespace Progress
  -- https://plfa.github.io/Properties/#exercise-progress--practice
  @[simp] def sum_hom : Progress m → Progress' m | step r => inr ⟨_, r⟩ | done v => inl v
  @[simp] def sum_inv : Progress' m → Progress m | inl v => done v | inr ⟨_, r⟩ => step r

  instance sum_iso : Progress m ≅ Progress' m where
    hom := sum_hom
    inv := sum_inv
    hom_inv_id : sum_inv ∘ sum_hom = id := by funext x; aesop
    inv_hom_id : sum_hom ∘ sum_inv = id := by funext x; aesop
end Progress

-- https://plfa.github.io/Properties/#renaming
namespace Renaming
  open Lookup

  /--
  If one context maps to another, the mapping holds after adding the same variable to both contexts.
  -/
  @[simp]
  def ext
  : (∀ {x tx}, (Γ ∋ x ⦂ tx) → (Δ ∋ x ⦂ tx))
  → (∀ {x y tx ty}, (Γ :< y ⦂ ty ∋ x ⦂ tx) → (Δ :< y ⦂ ty ∋ x ⦂ tx))
  := by
    introv ρ; intro
    | z => exact z
    | s nxy lx => exact s nxy <| ρ lx

  @[simp]
  def rename
  : (∀ {x t}, (Γ ∋ x ⦂ t) → (Δ ∋ x ⦂ t))
  → (∀ {m t}, (Γ ⊢ m ⦂ t) → (Δ ⊢ m ⦂ t))
  := by
    introv ρ; intro
    | ty_var j => apply ty_var; exact ρ j
    | ty_lam j => apply ty_lam; exact rename (ext ρ) j
    | ty_ap jl jm =>
        apply ty_ap
        · exact rename ρ jl
        · exact rename ρ jm
    | ty_zero => apply ty_zero
    | ty_succ j => apply ty_succ; exact rename ρ j
    | ty_case jl jm jn =>
        apply ty_case
        · exact rename ρ jl
        · exact rename ρ jm
        · exact rename (ext ρ) jn
    | ty_mu j => apply ty_mu; exact rename (ext ρ) j

  @[simp]
  def Lookup.weaken : (∅ ∋ m ⦂ t) → (Γ ∋ m ⦂ t) := by
    intro.

  @[simp]
  def weaken : (∅ ⊢ m ⦂ t) → (Γ ⊢ m ⦂ t) := by
    intro j; refine rename ?_ j; exact Lookup.weaken

  @[simp]
  def drop
  : (Γ :< x ⦂ t' :< x ⦂ t ⊢ y ⦂ u)
  → (Γ :< x ⦂ t ⊢ y ⦂ u)
  := by
    intro j; refine rename ?_ j
    intro y u j; cases j
    · exact z
    · case s j =>
      cases j
      · contradiction
      · case s j => refine s ?_ j; trivial

  @[simp]
  def Lookup.swap
  : (x ≠ x') → (Γ :< x' ⦂ t' :< x ⦂ t ∋ y ⦂ u)
  → (Γ :< x ⦂ t :< x' ⦂ t' ∋ y ⦂ u)
  := by
    intro n j; cases j
    · exact s n z
    · case s j =>
      cases j
      · exact z
      · apply s
        · trivial
        · apply s <;> trivial

  @[simp]
  def swap
  : (x ≠ x') → (Γ :< x' ⦂ t' :< x ⦂ t ⊢ y ⦂ u)
  → (Γ :< x ⦂ t :< x' ⦂ t' ⊢ y ⦂ u)
  := by
    intro n j; refine rename ?_ j; introv; exact Lookup.swap n
end Renaming

-- https://plfa.github.io/Properties/#substitution
@[simp]
def subst
: (∅ ⊢ y ⦂ t) → (Γ :< x ⦂ t ⊢ n ⦂ u)
→ (Γ ⊢ n[x := y] ⦂ u)
:= open Renaming in by
  intro j; intro
  | ty_var k =>
    rename_i y; by_cases y = x <;> simp_all
    · have := weaken (Γ := Γ) j; cases k <;> try trivial
    · cases k <;> simp_all; · repeat trivial
  | ty_lam k =>
    rename_i y _ _ _; by_cases y = x <;> (simp_all; apply ty_lam)
    · subst h; apply drop; trivial
    · apply subst j; exact swap (by trivial) k
  | ty_ap k l => apply ty_ap <;> (apply subst j; trivial)
  | ty_zero => exact ty_zero
  | ty_succ _ => apply ty_succ; apply subst j; trivial
  | ty_case k l m =>
    rename_i y _; by_cases y = x <;> simp_all
    · apply ty_case
      · apply subst j; exact k
      · apply subst j; exact l
      · subst h; exact drop m
    · apply ty_case <;> (apply subst j; try trivial)
      · exact swap (by trivial) m
  | ty_mu k =>
    rename_i y _; by_cases y = x <;> simp_all
    · subst h; apply ty_mu; exact drop k
    · apply ty_mu; apply subst j; exact swap (by trivial) k

-- https://plfa.github.io/Properties/#preservation
@[simp]
def preserve : (∅ ⊢ m ⦂ t) → (m —→ n) → (∅ ⊢ n ⦂ t) := by
  intro
  | ty_ap jl jm, lam_β _ => apply subst jm; cases jl; · trivial
  | ty_ap jl jm, ap_ξ₁ _ =>
    apply ty_ap <;> try trivial
    · apply preserve jl; trivial
  | ty_ap jl jm, ap_ξ₂ _ _ =>
    apply ty_ap <;> try trivial
    · apply preserve jm; trivial
  | ty_succ j, succ_ξ r => apply ty_succ; exact preserve j r
  | ty_case k l m, zero_β => trivial
  | ty_case k l m, succ_β _ => refine subst ?_ m; cases k; · trivial
  | ty_case k l m, case_ξ _ =>
      apply ty_case <;> try trivial
      · apply preserve k; trivial
  | ty_mu j, mu_β => refine subst ?_ j; apply ty_mu; trivial

-- https://plfa.github.io/Properties/#evaluation
inductive Result n where
| done (val : Value n)
| dnf
deriving BEq, DecidableEq, Repr

inductive Steps (l : Term) where
| steps : ∀{n : Term}, (l —↠ n) → Result n → Steps l
deriving Repr

open Result Steps

@[simp]
def eval (gas : ℕ) (j : ∅ ⊢ l ⦂ t) : Steps l := open Clos in
  if gas = 0 then
    ⟨nil, dnf⟩
  else
    match progress j with
    | Progress.done v => steps nil <| done v
    | Progress.step r =>
      let ⟨rs, res⟩ := eval (gas - 1) (preserve j r)
      ⟨cons r rs, res⟩

section examples
  open Term

  -- def x : ℕ := x + 1
  abbrev succ_μ := μ "x" : ι `"x"

  abbrev ty_succ_μ : ∅ ⊢ succ_μ ⦂ ℕt := by
    apply ty_mu; apply ty_succ; trivial

  #eval eval 3 ty_succ_μ |> (·.3)

  abbrev add_2_2 := add □ 2 □ 2

  abbrev two_ty : ∅ ⊢ 2 ⦂ ℕt := by
    iterate 2 (apply ty_succ)
    · exact ty_zero

  abbrev ty_add_2_2 : ∅ ⊢ add_2_2 ⦂ ℕt := by
    apply ty_ap
    · apply ty_ap
      · exact add_ty
      · iterate 2 (apply ty_succ)
        · exact ty_zero
    · iterate 2 (apply ty_succ)
      · exact ty_zero

  #eval eval 100 ty_add_2_2 |> (·.3)
end examples

section subject_expansion
  open Term

  -- https://plfa.github.io/Properties/#exercise-subject_expansion-practice
  example : IsEmpty (∀ {n t m}, (∅ ⊢ n ⦂ t) → (m —→ n) → (∅ ⊢ m ⦂ t)) := by
    by_contra; simp_all
    let ill_case := 𝟘? 𝟘 [zero: 𝟘 |succ "x" : add]
    have nty_ill : ∅ ⊬ ill_case := by
      by_contra; simp_all; rename_i t _ j
      cases t <;> (cases j; · contradiction)
    rename_i f; have := f 𝟘 ℕt ill_case ty_zero zero_β
    exact nty_ill.false this.some

  example : IsEmpty (∀ {n t m}, (∅ ⊢ n ⦂ t) → (m —→ n) → (∅ ⊢ m ⦂ t)) := by
    by_contra; simp_all
    let ill_ap := (ƛ "x" : 𝟘) □ ill_lam
    have nty_ill : ∅ ⊬ ill_ap := by
      by_contra; simp_all; rename_i t _ j
      cases t <;> (
        · cases j
          · rename_i j; cases j
            · apply nty_ill_lam.false <;> trivial
      )
    rename_i f; have := f 𝟘 ℕt ill_ap ty_zero (lam_β Value.lam)
    exact nty_ill.false this.some
end subject_expansion

-- https://plfa.github.io/Properties/#well-typed-terms-dont-get-stuck
abbrev Normal m := ∀ {n}, IsEmpty (m —→ n)
abbrev Stuck m := Normal m ∧ IsEmpty (Value m)

example : Stuck (` "x") := by
  unfold Stuck Normal; constructor
  · intro n; is_empty; intro.
  · is_empty; intro.

-- https://plfa.github.io/Properties/#exercise-unstuck-recommended
/--
No well-typed term can be stuck.
-/
@[simp]
def unstuck : (∅ ⊢ m ⦂ t) → IsEmpty (Stuck m) := by
  intro j; is_empty; simp_all
  intro n ns; cases progress j
  · case step s => exact n.false s
  · case done v => exact ns.false v

/--
After any number of steps, a well-typed term remains well typed.
-/
@[simp]
def preserves : (∅ ⊢ m ⦂ t) → (m —↠ n) → (∅ ⊢ n ⦂ t) := by
  intro j; intro
  | Clos.nil => trivial
  | Clos.cons car cdr => refine preserves ?_ cdr; exact preserve j car

/--
_Well-typed terms don't get stuck_ (WTTDGS):
starting from a well-typed term, taking any number of reduction steps leads to a term that is not stuck.
-/
@[simp]
def preserves_unstuck : (∅ ⊢ m ⦂ t) → (m —↠ n) → IsEmpty (Stuck n) := by
  intro j r; have := preserves j r; exact unstuck this

-- https://plfa.github.io/Properties/#reduction-is-deterministic
@[simp]
def Reduce.det : (m —→ n) → (m —→ n') → n = n' := by
  intro r r'; cases r
  · case lam_β =>
    cases r' <;> try trivial
    · case ap_ξ₂ => exfalso; rename_i v _ _ r; exact (Value.not_reduce v).false r
  · case ap_ξ₁ =>
    cases r' <;> try trivial
    · case ap_ξ₁ => simp_all; apply det <;> trivial
    · case ap_ξ₂ => exfalso; rename_i r _ v _; exact (Value.not_reduce v).false r
  · case ap_ξ₂ =>
    cases r' <;> try trivial
    · case lam_β => exfalso; rename_i r _ _ _ v; exact (Value.not_reduce v).false r
    · case ap_ξ₁ => exfalso; rename_i v _ _ r; exact (Value.not_reduce v).false r
    · case ap_ξ₂ => simp_all; apply det <;> trivial
  · case zero_β => cases r' <;> try trivial
  · case succ_β =>
    cases r' <;> try trivial
    · case case_ξ => exfalso; rename_i v _ r; exact (Value.not_reduce (Value.succ v)).false r
  · case succ_ξ => cases r'; · case succ_ξ => simp_all; apply det <;> trivial
  · case case_ξ =>
    cases r' <;> try trivial
    · case succ_β => exfalso; rename_i v r; exact (Value.not_reduce (Value.succ v)).false r
    · case case_ξ => simp_all; apply det <;> trivial
  · case mu_β => cases r'; try trivial

-- https://plfa.github.io/Properties/#quiz
/-
Suppose we add a new term zap with the following reduction rule

-------- β-zap
M —→ zap
and the following typing rule:

----------- ⊢zap
Γ ⊢ zap ⦂ A
Which of the following properties remain true in the presence of these rules? For each property, write either "remains true" or "becomes false." If a property becomes false, give a counterexample:

* Determinism

Becomes false.
The term `(ƛ x ⇒ `"x") □ 𝟘` can both be reduced via:
· ap_ξ₁, to zap □ 𝟘
· zep_β, to zap
... and they're not equal.

* Progress/Preservation

Remains true.
-/


-- https://plfa.github.io/Properties/#quiz-1
/-
Suppose instead that we add a new term foo with the following reduction rules:

------------------ β-foo₁
(λ x ⇒ ` x) —→ foo

----------- β-foo₂
foo —→ zero
Which of the following properties remain true in the presence of this rule? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample:

* Determinism

Becomes false.

The term `(ƛ x ⇒ `"x") □ 𝟘` can both be reduced via:
· ap_ξ₁, to foo □ 𝟘
· lam_β, to `"x"
... and they're not equal.

* Progress

Becomes false.
The term `(ƛ x ⇒ `"x") □ 𝟘` can be reduced via:
· ap_ξ₁ foo_β₁, to foo □ 𝟘
· then ap_ξ₁ foo_β₂, to 𝟘 □ 𝟘
... and now the term get's stuck.

* Preservation

Becomes false.
The term `(ƛ x ⇒ `"x") ⦂ ℕt =⇒ ℕt` can be reduced via:
· foo_β₁, to foo
· then foo_β₂, 𝟘 ⦂ ℕt
... and (ℕt =⇒ ℕt) ≠ ℕt

-/

-- https://plfa.github.io/Properties/#quiz-2
/-
Suppose instead that we remove the rule ξ·₁ from the step relation. Which of the following properties remain true in the absence of this rule? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample:

* Determinism/Preservation

Remains true.

* Progress

Becomes false.
The term `(ƛ x ⇒ `"x") □ 𝟘` is well-typed but gets stucked.
-/

-- https://plfa.github.io/Properties/#quiz-3
/-
We can enumerate all the computable function from naturals to naturals, by writing out all programs of type `ℕ ⇒ `ℕ in lexical order. Write fᵢ for the i’th function in this list.

NB: A ℕ → ℕ function can be seen as a stream of ℕ's, where the i'th ℕ stands for f(i).

Say we add a typing rule that applies the above enumeration to interpret a natural as a function from naturals to naturals:

Γ ⊢ L ⦂ `ℕ
Γ ⊢ M ⦂ `ℕ
-------------- _·ℕ_
Γ ⊢ L · M ⦂ `ℕ
And that we add the corresponding reduction rule:

fᵢ(m) —→ n
---------- δ
i · m —→ n
Which of the following properties remain true in the presence of these rules? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample:

* Determinism/Preservation

Remains true.
The only change is that the terms that were once stuck now might continue to progress.

* Progress

Becomes false.
Since a computable function can be partial, the reduction might not halt.
<https://en.wikipedia.org/wiki/Computable_function>

Are all properties preserved in this case? Are there any other alterations we would wish to make to the system?
-/
