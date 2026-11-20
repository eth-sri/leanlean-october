module

public import GradedNear.Defs

/-!
# Zeros of a non-principal `L`-function in a closed disc are finite

`L(s, χ)` is entire for `χ ≠ 1` and not identically zero (it does not vanish at `s = 1`), so
its zeros are isolated and a compact disc contains finitely many.
-/

@[expose] public section

namespace GradedNear

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

lemma analyticOnNhd_LFunction (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
  fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z

lemma order_LFunction_ne_top (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
  intro h
  apply χ.LFunction_apply_one_ne_zero hχ
  simpa using congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
    fun z => (analyticOnNhd_LFunction hχ) z (Set.mem_univ z)).mp h) 1

theorem LFunction_zeros_finite (hχ : χ ≠ 1)
    (c : ℂ) (r : ℝ) :
    {ρ : ℂ | ‖c - ρ‖ ≤ r ∧ DirichletCharacter.LFunction χ ρ = 0}.Finite := by
  have h := (analyticOnNhd_LFunction hχ).preimage_zero_mem_codiscrete (χ.LFunction_apply_one_ne_zero hχ)
  convert (isCompact_closedBall c r).finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (Set.subset_univ _) h) using 1
  ext ρ; simp [Metric.mem_closedBall, dist_eq_norm']

end GradedNear
