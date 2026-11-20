module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Smoothness and locality of regularized adjoint tests -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

open HypoellipticAleksandrov Set Filter MeasureTheory
open scoped Topology

section
variable {n : ℕ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- The regularized adjoint of a smooth compact test is smooth. -/
theorem contDiff_regularizedAdjoint (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) {ψ : EvolutionVec n → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedAdjoint B b ε ψ) := by
  unfold regularizedAdjoint
  exact (contDiff_transportedAdjoint hB hb hψ).add
    (contDiff_const.mul (ContDiff.sum fun l _ =>
      contDiff_fderiv_apply (contDiff_fderiv_apply hψ (basisZ l)) (basisZ l)))

/-- The regularized adjoint vanishes outside the original test support. -/
theorem regularizedAdjoint_eq_zero_of_notMem_tsupport (ε : ℝ)
    (ψ : EvolutionVec n → ℝ) {x : EvolutionVec n} (hx : x ∉ tsupport ψ) :
    regularizedAdjoint B b ε ψ x = 0 := by
  have hzero (l : Fin n) :
      fderiv ℝ (fun y => fderiv ℝ ψ y (basisZ l)) x (basisZ l) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ (fun z => fderiv ℝ ψ z (basisZ l)) y (basisZ l))
    intro h
    exact hx (tsupport_evolution_fderiv_apply ψ (basisZ l)
      (tsupport_evolution_fderiv_apply _ (basisZ l) h))
  simp only [regularizedAdjoint,
    transportedAdjoint_eq_zero_of_notMem_tsupport ψ hx, hzero,
    Finset.sum_const_zero, mul_zero, add_zero]

/-- Uniform convergence on the compact outer cylinder passes the distributional identity
on the interior to the limit. The domains of the approximating equations may vary. -/
theorem weakRegularized_of_tendstoUniformlyOn (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    {U K : Set (KineticPoint n)} (hU : IsOpen U) (hUK : U ⊆ K) (hK : IsCompact K)
    {u : ℕ → KineticPoint n → ℝ} {f : KineticPoint n → ℝ} {ε C : ℝ}
    (hu : TendstoUniformlyOn u f atTop K)
    (hbd : ∀ᶠ j in atTop, ContinuousOn (u j) K ∧ ∀ p ∈ K, |u j p| ≤ C)
    (heq : ∀ᶠ j in atTop, ∃ D, U ⊆ D ∧ IsKineticWeakRegularizedSolution B b ε D (u j) 0) :
    IsKineticWeakRegularizedSolution B b ε U f 0 := by
  have hf := hu.continuousOn (hbd.mono (fun _ h => h.1)).frequently
  refine ⟨(hf.mono hUK).locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hc hs
  let φ (p : KineticPoint n) := regularizedAdjoint B b ε ψ ((evolutionHomeomorph n).symm p)
  have hφ : Continuous φ := (contDiff_regularizedAdjoint hB hb hψ ε).continuous.comp
    (evolutionHomeomorph n).symm.continuous
  have hfull (v : KineticPoint n → ℝ) (D : Set (KineticPoint n)) (hUD : U ⊆ D) :
      (∫ p in D, v p * φ p) = ∫ p, v p * φ p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp =>
      mul_eq_zero_of_right _ (regularizedAdjoint_eq_zero_of_notMem_tsupport ε ψ
        (fun hx => hp (hUD (by simpa using hs hx))))
  have hlim : Tendsto (fun j => ∫ p in K, u j p * φ p) atTop (𝓝 (∫ p in K, f p * φ p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
    · exact hbd.mono fun j hj => (hj.1.mul hφ.continuousOn).aestronglyMeasurable hK.measurableSet
    · refine hbd.mono fun j hj => ?_
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hj.2 p hp) (abs_nonneg _)
    · exact (continuous_const.mul hφ.abs).continuousOn.integrableOn_compact hK
    · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      exact (hu.tendsto_at hp).mul tendsto_const_nhds
  have hz : ∀ᶠ j in atTop, (∫ p in K, u j p * φ p) = 0 := by
    filter_upwards [heq] with j ⟨D, hUD, hD⟩
    rw [hfull _ K hUK, ← hfull _ D hUD]
    simpa only [Pi.zero_apply, zero_mul, integral_zero] using hD.2 ψ hψ hc (hs.trans fun _ hx => hUD hx)
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hz.mono fun _ hj => hj.symm))
  simpa only [Pi.zero_apply, zero_mul, integral_zero] using
    (hfull f U subset_rfl).trans ((hfull f K hUK).symm.trans h0)

end

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
