module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaInverseJets
public import TaoTrudgianYang2025.BetaInverseStability

@[expose] public section

/-!
# Exact reference primitive and its reciprocal-exponent inverse

The logarithmic and power primitives are genuine zero-error model phases,
including every derivative order and both endpoints of [1,2].
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def referenceModelPrimitive (σ u : ℝ) : ℝ :=
  if σ = 1 then Real.log u else u^(1-σ)/(1-σ)

theorem referenceModelPrimitive_contDiffAt (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (referenceModelPrimitive σ) u := by
  unfold referenceModelPrimitive
  by_cases hσ : σ = 1
  · simpa only [hσ, ite_eq_left rfl, ite_true] using
      (Real.contDiffAt_log.mpr hu.ne' : ContDiffAt ℝ ∞ Real.log u)
  · simp only [ite_eq_right hσ]
    exact (Real.contDiffAt_rpow_const_of_ne hu.ne').div_const (1-σ)

theorem referenceModelPrimitive_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (referenceModelPrimitive σ) (u^(-σ)) u := by
  unfold referenceModelPrimitive
  by_cases hσ : σ = 1
  · subst σ
    simpa only [ite_eq_left rfl, ite_true, Real.rpow_neg_one] using
      Real.hasDerivAt_log hu.ne'
  · have hn : 1-σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
    simp only [ite_eq_right hσ]
    convert (Real.hasDerivAt_rpow_const (Or.inl hu.ne') (p := 1-σ)).div_const (1-σ) using 1
    rw [show 1-σ-1 = -σ by ring]
    field_simp

theorem referenceModelPrimitive_iteratedDeriv (σ : ℝ) {u : ℝ} (hu : 0 < u) (p : ℕ) :
    iteratedDeriv (p+1) (referenceModelPrimitive σ) u =
      iteratedDeriv p (modelPhase σ) u := by
  have he : deriv (referenceModelPrimitive σ) =ᶠ[𝓝 u] modelPhase σ := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with w hw
    exact (referenceModelPrimitive_hasDerivAt σ hw).deriv
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq p]

