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
  def commExts {σ σ' : ∀ {a}, Γ ∋ a → Δ ⊢ a}
  : (∀ {a}, (x : Γ ∋ a) → σ x ~ σ' x)
  → (∀ {a b}, (x : Γ‚ b ∋ a) → exts σ x ~ exts σ' x)
  := by
    intro s; introv; match x with
    | .z => simp only [exts]; exact .var
    | .s x => simp only [exts]; apply commRename Lookup.s; apply s
end Sim