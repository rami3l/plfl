-- https://plfa.github.io/Bisimulation/

import Plfl
import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

-- https://plfa.github.io/Bisimulation/#simulation
inductive Sim : (Γ ⊢ a) → (Γ ⊢ a) → Type where
| var : Sim (` x)  (` x)
| lam : Sim n n' → Sim (ƛ n) (ƛ n')
| ap : Sim l l' → Sim m m' → Sim (l □ m) (l' □ m')
| let : Sim l l' → Sim m m' → Sim (.let l m) (.let l' m')
deriving BEq, DecidableEq, Repr

namespace Sim
  infix:40 " ~ " => Sim

  -- https://plfa.github.io/Bisimulation/#exercise-_-practice
  def fromEq {s : (m : Γ ⊢ a) ~ m'} : (m' = n) → (m ~ n) := by
    intro h; rwa [h] at s

  @[simp]
  theorem toEq {s : (m : Γ ⊢ a) ~ m'} : (m ~ n) → (m' = n) := by
    intro s'; match s, s' with
    | s, .var => cases s with
      | var => rfl
    | s, .lam s' => cases s with
      | lam s'' => simp only [toEq (s := s'') s']
    | s, .ap sl sm => cases s with
      | ap sl' sm' => simp only [toEq (s := sl') sl, toEq (s := sm') sm]
    | s, .let sl sm => cases s with
      | «let» sl' sm' => simp only [toEq (s := sl') sl, toEq (s := sm') sm]

  -- https://plfa.github.io/Bisimulation/#simulation-commutes-with-values
  @[simp]
  def commValue {m m' : Γ ⊢ a} : (m ~ m') → Value m → Value m'
  | .lam _, .lam => .lam

  -- https://plfa.github.io/Bisimulation/#exercise-val¹-practice
  @[simp]
  def commValue_inv {m m' : Γ ⊢ a} : (m ~ m') → Value m' → Value m
  | .lam _, .lam => .lam

  -- https://plfa.github.io/Bisimulation/#simulation-commutes-with-renaming
  @[simp]
  def commRename (ρ : ∀ {a}, Γ ∋ a → Δ ∋ a) {m m' : Γ ⊢ a}
  : m ~ m' → rename ρ m ~ rename ρ m'
  := by
    intro
    | .var => exact .var
    | .lam s => apply lam; exact commRename (ext ρ) s
    | .ap sl sm => apply ap; repeat (apply commRename ρ; trivial)
    | .let sl sm => apply «let»; repeat
      first | apply commRename ρ | apply commRename (ext ρ)
      trivial

  -- https://plfa.github.io/Bisimulation/#simulation-commutes-with-substitution
  @[simp]
  def commExts {σ σ' : ∀ {a}, Γ ∋ a → Δ ⊢ a}
  (gs : ∀ {a}, (x : Γ ∋ a) → σ x ~ σ' x)
  : (∀ {a b}, (x : Γ‚ b ∋ a) → exts σ x ~ exts σ' x)
  := by
    introv; match x with
    | .z => simp only [exts]; exact .var
    | .s x => simp only [exts]; apply commRename Lookup.s; apply gs

  @[simp]
  def commSubst {σ σ' : ∀ {a}, Γ ∋ a → Δ ⊢ a}
  (gs : ∀ {a}, (x : Γ ∋ a) → @σ a x ~ @σ' a x)
  {m m' : Γ ⊢ a}
  : m ~ m' → subst σ m ~ subst σ' m'
  := by
    intro
    | .var => apply gs
    | .lam s => apply lam; exact commSubst (commExts gs) s
    | .ap sl sm => apply ap; repeat (apply commSubst gs; trivial)
    | .let sl sm => apply «let»; repeat
      first | apply commSubst gs | apply commSubst (commExts gs)
      trivial

  @[simp]
  def commSubst₁ {m m' : Γ ⊢ b} {n n' : Γ‚ b ⊢ a}
  (sm : m ~ m') (sn : n ~ n') : m ⇴ n ~ m' ⇴ n'
  := by
    let σ {a} : Γ‚ b ∋ a → Γ ⊢ a := subst₁σ m
    let σ' {a} : Γ‚ b ∋ a → Γ ⊢ a := subst₁σ m'
    let gs {a} (x : Γ‚ b ∋ a) : (@σ a x) ~ (@σ' a x) := match x with
    | .z => sm
    | .s x => .var
    simp only [subst₁];
    exact commSubst (Γ := Γ‚ b) (Δ := Γ) (σ := σ) (σ' := σ') gs sn
end Sim

/-
Now we can actually prove that `Sim` is a real bisimulation by giving the construction
of the lower leg of the diagram from the upper leg and vice versa.
-/

open Sim Reduce

-- https://plfa.github.io/Bisimulation/#the-relation-is-a-simulation
/--
`Lower (n' := n') m n` stands for the leg
```txt
          n
          |
          ~
          |
m' - —→ - n'
```
-/
inductive Lower (m' n : Γ ⊢ a) where
| intro (sim : n ~ n') (red : m' —→ n')

def Lower.fromUpper {m m' n : Γ ⊢ a} (s : m ~ m') (r : m —→ n) : Lower m' n := by
  match s with
  | .ap sl sm => match r with
    | .lamβ v => cases sl with | lam sl =>
      constructor
      · apply commSubst₁ <;> trivial
      · apply lamβ; exact commValue sm v
    | .apξ₁ r =>
      have ⟨s', r'⟩ := fromUpper sl r; constructor
      · apply ap <;> trivial
      · apply apξ₁ r'
    | .apξ₂ v r =>
      have ⟨s', r'⟩ := fromUpper sm r; constructor
      · apply ap <;> trivial
      · refine apξ₂ ?_ r'; exact commValue sl v
  | .let sl sm => match r with
    | .letξ r =>
      have ⟨s', r'⟩ := fromUpper sl r; constructor
      · apply «let» <;> trivial
      · apply letξ; exact r'
    | .letβ v =>
      constructor
      · apply commSubst₁ <;> trivial
      · apply letβ; exact commValue sl v

-- https://plfa.github.io/Bisimulation/#exercise-sim¹-practice
/--
`Upper (m := m) m' n` stands for the leg
```txt
m - —→ - n
|
~
|
m'
```
-/
inductive Upper (m' n : Γ ⊢ a) where
| intro (sim : m ~ m') (red : m —→ n)

def Upper.fromLower {m m' n : Γ ⊢ a} (s : n ~ n') (r : m' —→ n') : Upper m' n := by
  cases s with
  | var =>
    rename_i i; refine ⟨?_, r⟩; sorry
  | lam s => sorry
  | ap sl sm => sorry
  | «let» sl sm => sorry
