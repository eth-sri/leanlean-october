module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A six-term scalar Young estimate

This elementary real-algebra leaf is independent of the PDE application.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

theorem young_eps
    (ε B g n : ℝ) (hε : 0 < ε) :
    B * g * n ≤ ε * g ^ 2 + (B ^ 2 / (4 * ε)) * n ^ 2 := by
  have hsq : 0 ≤ (2 * ε * g - B * n) ^ 2 := sq_nonneg _
  field_simp
  nlinarith

theorem abs_six_terms_le (s a b c e f : ℝ) :
    |(-s) - a - b - c + e + f| ≤ |s| + |a| + |b| + |c| + |e| + |f| := by
  calc
    |(-s) - a - b - c + e + f| ≤ |(-s) - a - b - c + e| + |f| :=
      abs_add_le _ _
    _ ≤ (|(-s) - a - b - c| + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|(-s) - a - b| + |c|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (((|(-s) - a| + |b|) + |c|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ ((((|-s| + |a|) + |b|) + |c|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ = |s| + |a| + |b| + |c| + |e| + |f| := by rw [abs_neg]

end HypoellipticAleksandrov.Parabolic.Dirichlet
