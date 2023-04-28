-- https://plfa.github.io/More/#exercise-double-subst-stretch

import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

theorem double_subst
: subst₂ (v : Γ ⊢ a) (w : Γ ⊢ b) (n : Γ‚ a‚ b ⊢ c)
= v ⇴ rename .s w ⇴ n
:= by
  sorry
