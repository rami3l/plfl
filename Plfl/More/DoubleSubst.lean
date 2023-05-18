-- https://plfa.github.io/More/#exercise-double-subst-stretch

-- Adapted from <https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda>.

import Plfl.Init
import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

open More
open Term Subst Notation

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L50
/--
Applies `ext` repeatedly.
-/
def ext' (ρ : ∀ {a}, Γ ∋ a → Δ ∋ a) : Γ‚‚ Ε ∋ a → Δ‚‚ Ε ∋ a := by
  match Ε with
  | [] => exact ρ (a := a)
  | b :: Ε => exact ext (a := a) (b := b) (ext' (Ε := Ε) ρ)

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L56
/--
Applies `exts` repeatedly.
-/
def exts' (σ : ∀ {a}, Γ ∋ a → Δ ⊢ a) : Γ‚‚ Ε ∋ a → Δ‚‚ Ε ⊢ a := by
  match Ε with
  | [] => exact σ (a := a)
  | b :: Ε => exact exts (a := a) (b := b) (exts' (Ε := Ε) σ)

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L64
lemma exts_comp {ρ : ∀ {a}, Γ ∋ a → Δ ∋ a} {σ : ∀ {a}, Δ ∋ a → Ε ⊢ a} (i : Γ‚ b ∋ a)
: (exts σ) (ext ρ i) = exts (σ ∘ ρ) i
:= by cases i <;> rfl

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L87
lemma exts_var (i : Γ‚ b ∋ a) : exts var i = ` i := by cases i <;> rfl

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L73
lemma subst_comp {ρ : ∀ {a}, Γ ∋ a → Δ ∋ a} {σ : ∀ {a}, Δ ∋ a → Ε ⊢ a} (t : Γ ⊢ a)
: subst σ (rename ρ t) = subst (σ ∘ ρ) t
:= by
  match t with
  | ` i => triv
  | ƛ t =>
    apply congr_arg lam; rw [subst_comp t]
    conv_lhs => arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
  | l □ m => apply congr_arg₂ ap <;> apply subst_comp
  | 𝟘 => triv
  | ι t => apply congr_arg succ; apply subst_comp
  | 𝟘? l m n =>
    apply congr_arg₃ case <;> try apply subst_comp
    · rw [subst_comp n]
      conv_lhs => arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
  | μ t =>
    apply congr_arg mu; rw [subst_comp t]
    conv_lhs => arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
  | .prim t => triv
  | .mulP m n => apply congr_arg₂ mulP <;> apply subst_comp
  | .let m n =>
    apply congr_arg₂ «let» <;> try apply subst_comp
    · rw [subst_comp n]
      conv_lhs => arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
  | .prod m n => apply congr_arg₂ prod <;> apply subst_comp
  | .fst t => apply congr_arg fst; apply subst_comp
  | .snd t => apply congr_arg snd; apply subst_comp
  | .left t => apply congr_arg left; apply subst_comp
  | .right t => apply congr_arg right; apply subst_comp
  | .caseSum s l r =>
    apply congr_arg₃ caseSum <;> try apply subst_comp
    · rw [subst_comp l]
      conv_lhs => arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
    · rw [subst_comp r]
      conv_lhs => arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
  | .caseVoid v => apply congr_arg caseVoid; apply subst_comp
  | ◯ => triv
  | .nil => triv
  | .cons m n => apply congr_arg₂ cons <;> apply subst_comp
  | .caseList l m n =>
    apply congr_arg₃ caseList <;> try apply subst_comp
    · rw [subst_comp n]
      conv_lhs =>
        arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]
        arg 1; ext a t; simp only [Function.comp_apply, exts_comp t]

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L93
lemma subst_var (t : Γ ⊢ a) : subst var t = t := by
  match t with
  | ` i => apply congr_arg var; triv
  | ƛ t =>
    apply congr_arg lam
    conv_lhs => arg 1; ext a i; rw [exts_var i]
    exact subst_var t
  | l □ m => apply congr_arg₂ ap <;> apply subst_var
  | 𝟘 => triv
  | ι t => apply congr_arg succ; apply subst_var
  | 𝟘? l m n =>
    apply congr_arg₃ case <;> try apply subst_var
    · conv_lhs => arg 1; ext a i; rw [exts_var i]
      exact subst_var n
  | μ t =>
    apply congr_arg mu
    conv_lhs => arg 1; ext a i; rw [exts_var i]
    exact subst_var t
  | .prim t => triv
  | .mulP m n => apply congr_arg₂ mulP <;> apply subst_var
  | .let m n =>
    apply congr_arg₂ «let» <;> try apply subst_var
    · conv_lhs => arg 1; ext a i; rw [exts_var i]
      exact subst_var n
  | .prod m n => apply congr_arg₂ prod <;> apply subst_var
  | .fst t => apply congr_arg fst; apply subst_var
  | .snd t => apply congr_arg snd; apply subst_var
  | .left t => apply congr_arg left; apply subst_var
  | .right t => apply congr_arg right; apply subst_var
  | .caseSum s l r =>
    apply congr_arg₃ caseSum <;> try apply subst_var
    · conv_lhs => arg 1; ext a i; rw [exts_var i]
      exact subst_var l
    · conv_lhs => arg 1; ext a i; rw [exts_var i]
      exact subst_var r
  | .caseVoid v => apply congr_arg caseVoid; apply subst_var
  | ◯ => triv
  | .nil => triv
  | .cons m n => apply congr_arg₂ cons <;> apply subst_var
  | .caseList l m n =>
    apply congr_arg₃ caseList <;> try apply subst_var
    · conv_lhs => arg 1; ext a i; arg 1; ext a i; rw [exts_var i]
      conv_lhs => arg 1; ext a i; rw [exts_var i]
      exact subst_var n

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L104
@[simp]
theorem subst₁_shift : (t' : Γ ⊢ b) ⇸ shift (t : Γ ⊢ a) = t := by
  simp_all only [subst₁, subst₁σ, subst_comp]
  conv_lhs => arg 1; ext a t'; simp
  simp_all only [subst_var]

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L112
lemma insert_twice_idx {Γ Δ Ε : Context} {a b c : Ty} (i : Γ‚‚ Δ‚‚ Ε ∋ a)
: ext' (Ε := Ε)
    (.s (t' := c))
    (ext' (Ε := Ε) (ext' (Ε := Δ) (.s (t' := b))) i)
= ext' (ext (ext' .s)) (ext' .s i)
:= by
  match Ε, i with
  | [], _ => rfl
  | _ :: _, .z => rfl
  | d :: Ε, .s i => apply congr_arg Lookup.s; exact insert_twice_idx i

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L120
lemma insert_twice {Γ Δ Ε : Context} {a b c : Ty} (t : Γ‚‚ Δ‚‚ Ε ⊢ a)
: rename
    (ext' (Ε := Ε) (.s (t' := c)))
    (rename (ext' (Ε := Ε) (ext' (Ε := Δ) (.s (t' := b)))) t)
= (rename (ext' (ext (ext' .s))) (rename (ext' .s) t) : (Γ‚ b‚‚ Δ)‚ c‚‚ Ε ⊢ a)
:= by
  match t with
  | ` i => apply congr_arg var; exact insert_twice_idx i
  | ƛ t => apply congr_arg lam; rename_i a' b'; exact insert_twice (Ε := Ε‚ a') t
  | l □ m => apply congr_arg₂ ap <;> apply insert_twice
  | 𝟘 => triv
  | ι t => apply congr_arg succ; apply insert_twice
  | 𝟘? l m n =>
    apply congr_arg₃ case <;> try apply insert_twice
    · exact insert_twice (Ε := Ε‚ ℕt) n
  | μ t => apply congr_arg mu; exact insert_twice (Ε := Ε‚ a) t
  | .prim t => triv
  | .mulP m n => apply congr_arg₂ mulP <;> apply insert_twice
  | .let m n =>
    apply congr_arg₂ «let» <;> try apply insert_twice
    · rename_i a'; exact insert_twice (Ε := Ε‚ a') n
  | .prod m n => apply congr_arg₂ prod <;> apply insert_twice
  | .fst t => apply congr_arg fst; apply insert_twice
  | .snd t => apply congr_arg snd; apply insert_twice
  | .left t => apply congr_arg left; apply insert_twice
  | .right t => apply congr_arg right; apply insert_twice
  | .caseSum s l r =>
    apply congr_arg₃ caseSum <;> try apply insert_twice
    · rename_i a' b'; exact insert_twice (Ε := Ε‚ a') l
    · rename_i a' b'; exact insert_twice (Ε := Ε‚ b') r
  | .caseVoid v => apply congr_arg caseVoid; apply insert_twice
  | ◯ => triv
  | .nil => triv
  | .cons m n => apply congr_arg₂ cons <;> apply insert_twice
  | .caseList l m n =>
    apply congr_arg₃ caseList <;> try apply insert_twice
    · rename_i a'; exact insert_twice (Ε := Ε‚ a'‚ .list a') n

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L132
lemma insert_subst_idx
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a}
(i : Γ‚‚ Ε ∋ a)
: exts' (Ε := Ε) (exts (b := b) σ) (ext' .s i) = rename (ext' .s) (exts' σ i)
:= by
  match Ε, i with
  | [], i => rfl
  | _ :: _, .z => rfl
  | c :: Ε, .s i =>
    conv_lhs => arg 2; unfold ext' ext; simp
    conv_lhs => change shift (exts' (exts σ) (ext' .s i)); rw [insert_subst_idx i]
    conv_rhs => arg 2; unfold ext' ext; simp
    exact insert_twice (Ε := []) (@exts' Γ Δ Ε a σ i)

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L141
lemma insert_subst
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a}
(t : Γ‚‚ Ε ⊢ a)
: subst (exts' (Ε := Ε) (exts (b := b) σ)) (rename (ext' .s) t)
= rename (ext' .s) (subst (exts' σ) t)
:= by
  match t with
  | ` i => exact insert_subst_idx i
  | ƛ t => rename_i a b; apply congr_arg lam; exact insert_subst (Ε := Ε‚ a) t
  | l □ m => apply congr_arg₂ ap <;> apply insert_subst
  | 𝟘 => triv
  | ι t => apply congr_arg succ; apply insert_subst
  | 𝟘? l m n =>
    apply congr_arg₃ case <;> try apply insert_subst
    · exact insert_subst (Ε := Ε‚ ℕt) n
  | μ t => apply congr_arg mu; exact insert_subst (Ε := Ε‚ a) t
  | .prim t => triv
  | .mulP m n => apply congr_arg₂ mulP <;> apply insert_subst
  | .let m n =>
    apply congr_arg₂ «let» <;> try apply insert_subst
    · rename_i a'; exact insert_subst (Ε := Ε‚ a') n
  | .prod m n => apply congr_arg₂ prod <;> apply insert_subst
  | .fst t => apply congr_arg fst; apply insert_subst
  | .snd t => apply congr_arg snd; apply insert_subst
  | .left t => apply congr_arg left; apply insert_subst
  | .right t => apply congr_arg right; apply insert_subst
  | .caseSum s l r =>
    apply congr_arg₃ caseSum <;> try apply insert_subst
    · rename_i a' b'; exact insert_subst (Ε := Ε‚ a') l
    · rename_i a' b'; exact insert_subst (Ε := Ε‚ b') r
  | .caseVoid v => apply congr_arg caseVoid; apply insert_subst
  | ◯ => triv
  | .nil => triv
  | .cons m n => apply congr_arg₂ cons <;> apply insert_subst
  | .caseList l m n =>
    apply congr_arg₃ caseList <;> try apply insert_subst
    · rename_i a'; exact insert_subst (Ε := Ε‚ a'‚ .list a') n

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L154
lemma shift_subst
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a}
(t : Γ ⊢ a)
: subst (exts (b := b) σ) (shift t) = shift (subst σ t)
:= insert_subst (Ε := []) t

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L161
lemma exts_subst_comp
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a} {σ' : ∀ {a}, Δ ∋ a → Ε ⊢ a}
(i : Γ‚ b ∋ a)
: subst (exts σ') (exts σ i) = exts (subst σ' ∘ σ) i
:= by
  match i with
  | .z => triv
  | .s i => exact shift_subst (σ i)

-- https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda#L170
@[simp]
theorem subst_subst_comp
{σ : ∀ {a}, Γ ∋ a → Δ ⊢ a} {σ' : ∀ {a}, Δ ∋ a → Ε ⊢ a}
(t : Γ ⊢ a)
: subst σ' (subst σ t) = subst (subst σ' ∘ σ) t
:= by
  match t with
  | ` _ => triv
  | ƛ t =>
    apply congr_arg lam
    rw [subst_subst_comp (σ := exts σ) (σ' := exts σ') t]
    congr; ext; apply exts_subst_comp
  | l □ m => apply congr_arg₂ ap <;> apply subst_subst_comp
  | 𝟘 => triv
  | ι t => apply congr_arg succ; apply subst_subst_comp
  | 𝟘? l m n =>
    apply congr_arg₃ case <;> try apply subst_subst_comp
    · conv_lhs =>
      rw [subst_subst_comp (σ := exts σ) (σ' := exts σ') n]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_comp t]
  | μ t =>
    apply congr_arg mu
    have := subst_subst_comp (σ := exts σ) (σ' := exts σ') t
    rw [this]; congr; ext; apply exts_subst_comp
  | .prim t => triv
  | .mulP m n => apply congr_arg₂ mulP <;> apply subst_subst_comp
  | .let m n =>
    apply congr_arg₂ «let»
    · apply subst_subst_comp
    · conv_lhs =>
      rw [subst_subst_comp (σ := exts σ) (σ' := exts σ') n]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_comp t]
  | .prod m n => apply congr_arg₂ prod <;> apply subst_subst_comp
  | .fst t => apply congr_arg fst; apply subst_subst_comp
  | .snd t => apply congr_arg snd; apply subst_subst_comp
  | .left t => apply congr_arg left; apply subst_subst_comp
  | .right t => apply congr_arg right; apply subst_subst_comp
  | .caseSum s l r =>
    apply congr_arg₃ caseSum <;> try apply subst_subst_comp
    · conv_lhs =>
      rw [subst_subst_comp (σ := exts σ) (σ' := exts σ') l]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_comp t]
    · conv_lhs =>
      rw [subst_subst_comp (σ := exts σ) (σ' := exts σ') r]
      arg 1; ext tt t; rw [Function.comp_apply, exts_subst_comp t]
  | .caseVoid v => apply congr_arg caseVoid; apply subst_subst_comp
  | ◯ => triv
  | .nil => triv
  | .cons m n => apply congr_arg₂ cons <;> apply subst_subst_comp
  | .caseList l m n =>
    apply congr_arg₃ caseList <;> try apply subst_subst_comp
    · rw [subst_subst_comp (σ := exts (exts σ)) (σ' := exts (exts σ')) n]
      congr; ext _ t; rw [Function.comp_apply, exts_subst_comp t]
      congr; ext _ t; rw [Function.comp_apply, exts_subst_comp t]

theorem double_subst
: subst₂ (v : Γ ⊢ a) (w : Γ ⊢ b) (n : Γ‚ a‚ b ⊢ c)
= v ⇸ rename .s w ⇸ n
:= by
  cases n <;> first
  | triv
  | simp_all [subst₂, subst₁, subst₁σ]; congr; ext
    -- The following is generated by `aesop?`:
    simp_all only [Function.comp_apply]
    split
    · simp_all only [subst₁_shift]
    · simp_all only; rfl
    · simp_all only; rfl
