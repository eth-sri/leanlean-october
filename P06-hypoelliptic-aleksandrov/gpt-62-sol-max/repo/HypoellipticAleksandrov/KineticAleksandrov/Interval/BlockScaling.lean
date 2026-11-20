module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Block
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Scaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius

/-! # Kinetic scaling of the length-independent interval unit block -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Scaling

/-- Arbitrary nonzero frequencies conditions on their kinetic time scale. -/
theorem interval_frequency_blocks
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (E : IntervalEvolution lam Lam m Lb),
      ∀ (ξ : PDE.Vec 1), ξ ≠ 0 → ∀ (σ : ℝ) (v : E.domain),
      ∀ (ht : σ ≤ σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))),
      TV (intervalFourierKernel E.kernel σ
        (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v) ≤ 1 - δ := by
  obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ := unit_frequency_block_interval
    lam Lam m Lb hlam hlamLam hm hmLb
  refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
  intro E ξ hξ σ v ht
  obtain ⟨hrpos, hr2, hrunit⟩ := frequency_radius_identities hξ
  let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ)), hrpos⟩
  let D := scaledDomain (E.domain) v.1 r
  let hmap := mapsDomain_interval E.left E.right σ v.1 0 E.drift r
  let hDr := measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible E.lt v.1 r)
  let K' := KineticAffineScaling.pushKernel hmap E.kernel
  let S' := fiberOperator K' hDr
  have hr' := realizes_ofRadius_interval E.left E.right σ E.lt v.1 0 E.drift r E.realizes
  have hs' := scaled_interval_setting lam Lam m Lb E.left E.right σ E.lt E.coefficient E.drift E.setting v.1 r
  have hv' : (0 : PDE.Vec 1) ∈ movingDomain D stationary 0 := by
    rw [movingDomain_stationary]
    change v.1 + r.1 • (0 : PDE.Vec 1) ∈ E.domain
    simpa only [smul_zero, add_zero] using v.2
  let q' := movingQuery 0 L hL.le (0 : PDE.Vec 1) 0 hv'
  let ν' := fourierProjection K' q' (r.1 ^ 3 • ξ)
  have hν' := fourierProjection_spec K' q' (r.1 ^ 3 • ξ)
  let J := PDE.oneDimensionalAxisBox ((E.left - v.1 0) / r.1) ((E.right - v.1 0) / r.1)
  have hunit' (hsx : SourceSetting lam Lam m Lb J
      (scaledCoefficient E.coefficient σ v.1 r) (scaledDrift E.drift v.1 r))
      (hj : MeasurableSet J) (Sx : TerminalOperatorFamily J stationary)
      (Kx : MovingFiberKernel J stationary)
      (hx : RealizesTerminalEvolution J stationary hj
        (zIndependentCoefficient (scaledCoefficient E.coefficient σ v.1 r)) (scaledDrift E.drift v.1 r) Sx Kx) :=
    hunit ⟨_, _, scaled_interval_endpoints E.lt v.1 r, _, _, hsx, hj, Sx, Kx, hx⟩
      (r.1 ^ 3 • ξ) hrunit 0 0
  dsimp only [J, IntervalEvolution.domain] at hunit'
  rw [← scaledDomain_interval E.left E.right v.1 r] at hunit'
  have hνunit : IsFourierProjection K' (movingQuery 0 (0 + L)
      (by simpa only [zero_add] using hL.le) 0 0 hv') (r.1 ^ 3 • ξ) ν' := by
    simpa only [zero_add] using hν'
  have hbound := hunit' hs' hDr S' K' hr' hv' (by simpa only [zero_add] using hL.le) ν' hνunit
  let ν := intervalFourierKernel E.kernel σ
    (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v
  have hquery : KineticAffineScaling.queryMap hmap q' =
      movingQuery σ (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht v.1 0
        (by simpa only [movingDomain_stationary] using v.2) := by
    apply Subtype.ext
    change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
      v.1 + r.1 • (0 : PDE.Vec 1), (0 : PDE.Vec 1) +
        (r.1 ^ 2 * 0) • E.drift v.1 + r.1 ^ 3 • (0 : PDE.Vec 1)) = _
    change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
      v.1 + r.1 • (0 : PDE.Vec 1), (0 : PDE.Vec 1) +
        (r.1 ^ 2 * 0) • E.drift v.1 + r.1 ^ 3 • (0 : PDE.Vec 1)) =
      (σ, σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)), v.1, 0)
    simp only [mul_zero, add_zero, smul_zero, zero_smul]
    have hr2' : r.1 ^ 2 = PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)) := hr2
    rw [hr2', mul_comm L]
  have hν : IsFourierProjection E.kernel (KineticAffineScaling.queryMap hmap q') ξ ν := by
    rw [hquery]
    exact intervalFourierKernel_spec E.kernel _ _ ht ξ v
  have htv := (realizes_ofRadius_interval_fourier_tv E.left E.right σ E.lt v.1 0 E.drift r E.realizes hr'
    q' ξ ν ν' hν hν').2
  change (totalVariationNorm ν).toReal ≤ 1 - δ
  rw [htv]
  exact hbound

end HypoellipticAleksandrov.KineticAleksandrov.Interval
