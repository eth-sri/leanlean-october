module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Parabolic.Scaling
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.TietzeExtension
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothDerivatives
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Parabolic compression about the time midpoint and velocity centre. -/
def innerMap {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) (ρ : ℝ) :
    TimeVelocity N → TimeVelocity N :=
  parabolicAffine (t₀ - h + (1 - ρ ^ 2) * h / 2) v₀ ρ

/-- Strict compression sends the closed reference cylinder into the open source cylinder. -/
theorem innerMap_mapsTo
    {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Set.MapsTo (innerMap t₀ h v₀ ρ)
      (closedParabolicCylinder h (0 : PDE.Vec N))
      (krylovCylinder t₀ h v₀) := by
  intro z hz
  rcases hz with ⟨hztime, hzvel⟩
  have hr2 : ρ ^ 2 < 1 := by nlinarith
  have hmargin : 0 < (1 - ρ ^ 2) * h / 2 := by positivity
  change (t₀ - h < t₀ - h + (1 - ρ ^ 2) * h / 2 + ρ ^ 2 * z.1 ∧
    t₀ - h + (1 - ρ ^ 2) * h / 2 + ρ ^ 2 * z.1 < t₀) ∧ _
  constructor
  · constructor
    · nlinarith [sq_nonneg ρ, hztime.1]
    · nlinarith [mul_le_mul_of_nonneg_left hztime.2 (sq_nonneg ρ)]
  · change PDE.euclideanSqDist (v₀ + ρ • z.2) v₀ < 1 ^ 2
    have hd : PDE.euclideanSqDist (v₀ + ρ • z.2) v₀ =
        ρ ^ 2 * PDE.euclideanSqDist z.2 0 := by
      simp [PDE.euclideanSqDist, add_sub_cancel_left, PDE.vecNormSq_smul]
    rw [hd]
    exact (mul_le_mul_of_nonneg_left hzvel (sq_nonneg ρ)).trans_lt (by simpa using hr2)

/-- At radius one, the forward boundary maps to the original bottom and lateral faces. -/
theorem innerMap_one_boundary
    {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) :
    Set.MapsTo (innerMap t₀ h v₀ 1)
      (forwardParabolicBoundary h (0 : PDE.Vec N))
      (krylovParabolicBoundary t₀ h v₀) := by
  intro z hz
  have hm : innerMap t₀ h v₀ 1 z = (t₀ - h + z.1, v₀ + z.2) := by
    simp [innerMap, parabolicAffine, one_pow]
  rw [hm]
  rcases hz with hz | hz
  · left
    rcases hz with ⟨ht, hv⟩
    change z.1 = 0 at ht
    refine ⟨?_, ?_⟩
    · simpa [ht] using (Set.mem_singleton (t₀ - h))
    · simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist, add_sub_cancel_left] using hv
  · right
    rcases hz with ⟨ht, hv⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simpa [PDE.euclideanSphere, PDE.euclideanSqDist, add_sub_cancel_left] using hv

/-- Compression can approximate the uncompressed values uniformly on the closed cylinder. -/
theorem exists_innerMap_value_close
    {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    (u : TimeVelocity N → ℝ)
    (hu : ContinuousOn u (krylovClosedCylinder t₀ h v₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ z ∈ closedParabolicCylinder h (0 : PDE.Vec N),
        |u (innerMap t₀ h v₀ ρ z) - u (innerMap t₀ h v₀ 1 z)| ≤ ε := by
  let K := krylovClosedCylinder t₀ h v₀
  have hK : IsCompact K := isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall v₀ (by norm_num))
  let f : C(K, ℝ) := ⟨fun z => u z, hu.domRestrict⟩
  obtain ⟨g, hg⟩ := f.exists_extension' hK.isClosed.isClosedEmbedding_subtypeVal
  have hgeq (z : TimeVelocity N) (hz : z ∈ K) : g z = u z := congrFun hg ⟨z, hz⟩
  let K0 := closedParabolicCylinder h (0 : PDE.Vec N)
  have hK0 : IsCompact K0 := isCompact_closedParabolicCylinder h 0
  letI : CompactSpace K0 := isCompact_iff_compactSpace.mp hK0
  let F : ℝ → K0 → ℝ := fun ρ z => g (innerMap t₀ h v₀ ρ z)
  have hc : Continuous (Function.uncurry F) := by
    apply g.continuous.comp
    dsimp [F, innerMap, parabolicAffine]
    fun_prop
  have he' : ∀ᶠ ρ in 𝓝[<] 1, ∀ z : K0, dist (F 1 z) (F ρ z) < ε :=
    ((Metric.tendstoUniformly_iff.mp (hc.tendstoUniformly F 1)) ε hε).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ρ, hclose, hpos, hlt⟩ :=
    (he'.and (hp.and (self_mem_nhdsWithin : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ρ ∈ Iio 1))).exists
  refine ⟨ρ, hpos, hlt, fun z hz => ?_⟩
  have hzρ := innerMap_mapsTo t₀ h v₀ hh hpos hlt hz
  have hzρK : innerMap t₀ h v₀ ρ z ∈ K :=
    ⟨⟨hzρ.1.1.le, hzρ.1.2.le⟩, show PDE.euclideanSqDist _ v₀ ≤ 1 ^ 2 from hzρ.2.le⟩
  have hz1K : innerMap t₀ h v₀ 1 z ∈ K := by
    rcases hz with ⟨ht, hv⟩
    simp [innerMap, parabolicAffine, one_pow]
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist, add_sub_cancel_left] using hv
  have hdist := hclose ⟨z, hz⟩
  dsimp [F] at hdist
  rw [hgeq _ hzρK, hgeq _ hz1K, Real.dist_eq, abs_sub_comm] at hdist
  exact hdist.le


/-- The positive continuous residual is dominated in norm by an a.e. source. -/
theorem positive_residual_memLp_norm_le
    {N : ℕ} {Q : Set (TimeVelocity N)} (hQ : MeasurableSet Q)
    (a : TimeVelocity N → PDE.Mat N) (u f : TimeVelocity N → ℝ)
    (hg : AEStronglyMeasurable (residual a u) (volume.restrict Q))
    (hf : MemLp f (parabolicExponent N) (volume.restrict Q))
    (hsub : ∀ᵐ z ∂volume.restrict Q, residual a u z ≤ f z) :
    MemLp (fun z => max (residual a u z) 0) (parabolicExponent N)
        (volume.restrict Q) ∧
      parabolicLpNormOn N (fun z => max (residual a u z) 0) Q ≤
        parabolicLpNormOn N f Q := by
  have hm : AEStronglyMeasurable (fun z => max (residual a u z) 0)
      (volume.restrict Q) :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable hg
  have hb : ∀ᵐ z ∂volume.restrict Q, ‖max (residual a u z) 0‖ ≤ ‖f z‖ := by
    filter_upwards [hsub] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (hz.trans (le_abs_self _)) (abs_nonneg _)
  refine ⟨hf.of_le hm hb, ?_⟩
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_ae hm hb)

/-- Inward parabolic compression does not increase the amplified source norm. -/
theorem compressed_source_memLp_norm_le
    {N : ℕ} (hN : 1 ≤ N) (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (g : TimeVelocity N → ℝ)
    (hg : MemLp g (parabolicExponent N)
      (volume.restrict (krylovCylinder t₀ h v₀))) :
    MemLp (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z))
        (parabolicExponent N)
        (volume.restrict (parabolicInterior h (0 : PDE.Vec N))) ∧
      parabolicLpNormOn N (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z))
          (parabolicInterior h (0 : PDE.Vec N)) ≤
        parabolicLpNormOn N g (krylovCylinder t₀ h v₀) := by
  let S := parabolicInterior h (0 : PDE.Vec N)
  let J := innerMap t₀ h v₀ ρ '' S
  have hJ : J ⊆ krylovCylinder t₀ h v₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact innerMap_mapsTo t₀ h v₀ hh hρ hρ1
      (parabolicInterior_subset_closedParabolicCylinder h 0 hz)
  have hscale := parabolicELpNormOn_pullback_raw
    (t₀ - h + (1 - ρ ^ 2) * h / 2) v₀ hρ g S
  change parabolicELpNormOn N (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z)) S =
    ‖ρ ^ 2‖ₑ * (ENNReal.ofReal ((ρ ^ (N + 2))⁻¹) ^
      (1 / parabolicExponent N).toReal) * parabolicELpNormOn N g J at hscale
  have hfac : ‖ρ ^ 2‖ₑ * (ENNReal.ofReal ((ρ ^ (N + 2))⁻¹) ^
      (1 / parabolicExponent N).toReal) ≤ 1 := by
    rw [Real.enorm_eq_ofReal (sq_nonneg ρ), ENNReal.ofReal_rpow_of_nonneg
      (by positivity) ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (sq_nonneg ρ)]
    apply ENNReal.ofReal_le_one.mpr
    have hp : (1 / parabolicExponent N).toReal = 1 / ((N : ℝ) + 1) := by
      have hpval : parabolicExponent N = ((N + 1 : ℕ) : ℝ≥0∞) := by
        simp only [parabolicExponent, Nat.cast_add, Nat.cast_one]
      rw [hpval, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
      norm_num
    rw [hp, Real.inv_rpow (by positivity)]
    rw [← Real.rpow_natCast ρ (N + 2), ← Real.rpow_mul hρ.le,
      ← Real.rpow_neg hρ.le, ← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ]
    have he : 2 + -((N + 2 : ℝ) * (1 / ((N : ℝ) + 1))) =
        (N : ℝ) / ((N : ℝ) + 1) := by field_simp; ring
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at *
    rw [he]
    exact Real.rpow_le_one hρ.le hρ1.le (by positivity)
  have hnorm : parabolicELpNormOn N
      (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z)) S ≤
      parabolicELpNormOn N g J := by
    rw [hscale]
    exact (mul_le_mul_left hfac _).trans_eq (one_mul _)
  have hmem := hnorm.trans_lt (hg.mono_measure (Measure.restrict_mono hJ le_rfl))
  refine ⟨hmem, ?_⟩
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top
    (hnorm.trans (eLpNorm_mono_measure g (Measure.restrict_mono hJ le_rfl)))


/-- The scalar residual is continuous wherever the coefficient and selected jet are continuous. -/
theorem continuousOn_residual {N : ℕ} {V : Set (TimeVelocity N)}
    (a : TimeVelocity N → PDE.Mat N) (q : TimeVelocity N → ℝ)
    (ha : ContinuousOn a V) (hq : IsScalarC12On q V) :
    ContinuousOn (residual a q) V := by
  apply hq.continuousOn_scalarTimeDerivative.sub
  unfold matrixContraction
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro j _
  exact (((continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn ha)).mul
    ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hq.continuousOn_scalarSpatialHessian)))

/-- Smooth functions and continuous coefficients have a continuous scalar residual. -/
theorem continuous_residual {N : ℕ} (a : TimeVelocity N → PDE.Mat N)
    (q : TimeVelocity N → ℝ) (ha : Continuous a) (hq : ContDiff ℝ 2 q) :
    Continuous (residual a q) := by
  apply continuousOn_univ.mp
  exact continuousOn_residual a q ha.continuousOn (isScalarC12On_of_contDiff_two hq univ)

/-- A bounded coefficient contraction amplifies uniform selected-jet errors by a finite factor. -/
theorem residual_difference_le {N : ℕ} (a : PDE.Mat N)
    (q w : TimeVelocity N → ℝ) (z : TimeVelocity N) {δ M : ℝ}
    (hδ : 0 ≤ δ) (hM : (∑ i, ∑ j, |a i j|) ≤ M)
    (ht : |scalarTimeDerivative w z - scalarTimeDerivative q z| ≤ δ)
    (hh : ∀ i j, |scalarSpatialHessian w z i j - scalarSpatialHessian q z i j| ≤ δ) :
    |residual (fun _ => a) w z - residual (fun _ => a) q z| ≤ δ * (1 + M) := by
  have hmat : |matrixContraction a (scalarSpatialHessian w z) -
      matrixContraction a (scalarSpatialHessian q z)| ≤ δ * M := by
    simp only [matrixContraction, ← Finset.sum_sub_distrib, ← mul_sub]
    calc
      |∑ i, ∑ j, a i j * (scalarSpatialHessian w z i j -
          scalarSpatialHessian q z i j)| ≤
          ∑ i, ∑ j, |a i j * (scalarSpatialHessian w z i j -
            scalarSpatialHessian q z i j)| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, |a i j| * δ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hh i j) (abs_nonneg _)
      _ ≤ δ * M := by
        simp only [← Finset.sum_mul]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hM hδ
  have he : residual (fun _ => a) w z - residual (fun _ => a) q z =
      (scalarTimeDerivative w z - scalarTimeDerivative q z) -
      (matrixContraction a (scalarSpatialHessian w z) -
        matrixContraction a (scalarSpatialHessian q z)) := by unfold residual; ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add ht hmat).trans_eq (by ring))

/-- A nonnegative source plus a constant bounds the positive residual in the restricted norm. -/
theorem positive_norm_le_add_constant
    {N : ℕ} {Q : Set (TimeVelocity N)} (hQ : MeasurableSet Q)
    (hfinite : volume Q < ⊤) (F G : TimeVelocity N → ℝ)
    (hF : AEStronglyMeasurable F (volume.restrict Q))
    (hG : MemLp G (parabolicExponent N) (volume.restrict Q))
    (hG0 : ∀ z ∈ Q, 0 ≤ G z) {e : ℝ} (he : 0 ≤ e)
    (hbound : ∀ z ∈ Q, F z ≤ G z + e) :
    parabolicLpNormOn N (fun z => max (F z) 0) Q ≤
      parabolicLpNormOn N G Q + e * parabolicLpNormOn N (fun _ => (1 : ℝ)) Q := by
  letI : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hc : MemLp (fun _ => e) (parabolicExponent N)
      (volume.restrict Q) := memLp_const e
  have hm : AEStronglyMeasurable (fun z => max (F z) 0) (volume.restrict Q) :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable hF
  have hle : ∀ᵐ z ∂volume.restrict Q, ‖max (F z) 0‖ ≤ ‖G z + e‖ := by
    filter_upwards [ae_restrict_mem hQ] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (hG0 z hz) he)]
    exact max_le (hbound z hz) (add_nonneg (hG0 z hz) he)
  have hmono := ENNReal.toReal_mono (hG.add hc).eLpNorm_ne_top (eLpNorm_mono_ae hm hle)
  have hconst : lpNorm (fun _ => e) (parabolicExponent N)
      (volume.restrict Q) = e * parabolicLpNormOn N (fun _ => 1) Q := by
    simpa [Pi.smul_def, coe_nnnorm, abs_of_nonneg he]
      using! (lpNorm_const_smul e (fun _ => (1 : ℝ)) (volume.restrict Q) (p := parabolicExponent N))
  exact hmono.trans ((lpNorm_add_le hG (by simp [parabolicExponent]) (g := fun _ => e)).trans_eq (by rw [hconst]; rfl))

end HypoellipticAleksandrov.Parabolic.KrylovEstimate

