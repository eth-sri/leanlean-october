module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothApproximation
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.CoefficientExtension
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ApproximationBounds
public import HypoellipticAleksandrov.Parabolic.ABP

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Set Filter MeasureTheory
open scoped Topology MatrixOrder Matrix.Norms.Elementwise


/-- Interior smoothing controls the residual norm and corrects the boundary. -/
theorem exists_smooth_subsolution_close
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    (a : TimeVelocity N → PDE.Mat N) (f u : TimeVelocity N → ℝ)
    (ha : ContinuousOn a (krylovClosedCylinder t₀ h v₀))
    (hlo : ∀ z ∈ krylovClosedCylinder t₀ h v₀,
      lam • (1 : PDE.Mat N) ≤ a z)
    (hf : MemLp f (parabolicExponent N)
      (volume.restrict (krylovCylinder t₀ h v₀)))
    (hu : IsScalarC12UpTo u (krylovCylinder t₀ h v₀)
      (krylovClosedCylinder t₀ h v₀))
    (hsub : ∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀), residual a u z ≤ f z)
    (hb : ∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : CoefficientField N) (F w : TimeVelocity N → ℝ),
      IsContinuousCoefficient A ∧ Continuous F ∧ ContDiff ℝ 2 w ∧
      (∀ z ∈ closedParabolicCylinder h (0 : PDE.Vec N),
        lam • (1 : PDE.Mat N) ≤ coefficientAt A z) ∧
      IsParabolicSubsolutionOn A F w (parabolicInterior h (0 : PDE.Vec N)) ∧
      (∀ z ∈ forwardParabolicBoundary h (0 : PDE.Vec N), w z ≤ 0) ∧
      (∀ z ∈ closedParabolicCylinder h (0 : PDE.Vec N),
        |w z - u (innerMap t₀ h v₀ 1 z)| ≤ ε) ∧
      parabolicLpNormOn N (fun z => max (F z) 0)
          (parabolicInterior h (0 : PDE.Vec N)) ≤
        parabolicLpNormOn N f (krylovCylinder t₀ h v₀) + ε  := by
  have small_tolerance {η c k : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (hk : 0 ≤ k) :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ δ * c * k ≤ η := by
    let δ := η / (c * k + 1)
    have hd : 0 < c * k + 1 := by positivity
    have he := div_mul_cancel₀ η (ne_of_gt hd)
    refine ⟨δ, (div_pos hη hd), ?_, ?_⟩ <;> nlinarith [mul_nonneg hc hk]
  let Q := krylovCylinder t₀ h v₀
  let K := krylovClosedCylinder t₀ h v₀
  let S := parabolicInterior h (0 : PDE.Vec N)
  let L := closedParabolicCylinder h (0 : PDE.Vec N)
  have hQ := isOpen_krylovCylinder t₀ h v₀
  have hQK : Q ⊆ K := by
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩,
      PDE.euclideanBall_subset_euclideanClosedBall v₀ 1 hz.2⟩
  have hL : IsCompact L := isCompact_closedParabolicCylinder h 0
  have hSL : S ⊆ L := parabolicInterior_subset_closedParabolicCylinder h 0
  obtain ⟨hgp, hgnorm⟩ := positive_residual_memLp_norm_le hQ.measurableSet a u f
    ((continuousOn_residual a u (ha.mono hQK) hu.isScalarC12On).aestronglyMeasurable hQ.measurableSet) hf hsub
  let gp : TimeVelocity N → ℝ := fun z => max (residual a u z) 0
  let η := ε / 4
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨ρ, hρ, hρ1, hvalue⟩ :=
    exists_innerMap_value_close t₀ h v₀ hh u hu.continuousOn hη
  let Φ := innerMap t₀ h v₀ ρ
  let q := u ∘ Φ
  let ar := a ∘ Φ
  have hΦ : Continuous Φ := (contDiff_parabolicAffine _ _ _).continuous
  have hLV := innerMap_mapsTo t₀ h v₀ hh hρ hρ1
  have hVK : MapsTo Φ (Φ ⁻¹' Q) K := fun z hz => hQK hz
  obtain ⟨hq, hjet⟩ := scalarC12On_affine_pullback hQ u hu.isScalarC12On
    (t₀ - h + (1 - ρ ^ 2) * h / 2) v₀ hρ
  have har := ha.comp hΦ.continuousOn (fun z hz => hVK (hLV hz))
  obtain ⟨ae, hae, he⟩ := exists_continuous_matrix_extension hL.isClosed ar har
  let A : CoefficientField N := fun t v => ae (t, v)
  let total : TimeVelocity N → ℝ := fun z => ∑ i, ∑ j, |ar z i j|
  have htotal : ContinuousOn total L := by
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    exact (((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn har)).abs)
  obtain ⟨M₀, hM₀⟩ := hL.exists_bound_of_continuousOn htotal
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound (z : TimeVelocity N) (hz : z ∈ L) : total z ≤ M :=
    (le_abs_self _).trans ((hM₀ z hz).trans (le_max_left _ _))
  let k := parabolicLpNormOn N (fun _ => 1) S
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  obtain ⟨δ, hδ, hδη, hδnorm⟩ := small_tolerance hη (add_nonneg zero_le_one hM) hk
  obtain ⟨w₀, hw₀, hwjet⟩ := exists_smooth_scalar_jet_close (hQ.preimage hΦ) hL hLV q hq hδ
  let w : TimeVelocity N → ℝ := fun z => w₀ z + (-2 * η)
  let F := residual ae w₀
  let G : TimeVelocity N → ℝ := fun z => ρ ^ 2 * gp (Φ z)
  have hG := compressed_source_memLp_norm_le hN t₀ h v₀ hh hρ hρ1 gp hgp
  have hG0 (z : TimeVelocity N) : 0 ≤ G z :=
    mul_nonneg (sq_nonneg ρ) (le_max_right _ _)
  have hres (z : TimeVelocity N) (hz : z ∈ L) :
      residual ar q z = ρ ^ 2 * residual a u (Φ z) := by
    obtain ⟨ht, hs⟩ := hjet z (hLV hz)
    change scalarTimeDerivative q z = ρ ^ 2 * scalarTimeDerivative u (Φ z) at ht
    change scalarSpatialHessian q z = ρ ^ 2 • scalarSpatialHessian u (Φ z) at hs
    unfold residual
    rw [ht, hs, matrixContraction_smul_right]
    change _ - ρ ^ 2 * matrixContraction (a (Φ z)) _ = _
    ring
  have hFbound (z : TimeVelocity N) (hz : z ∈ S) : F z ≤ G z + δ * (1 + M) := by
    have hzL := hSL hz
    have hab := residual_difference_le (ar z) q w₀ z hδ.le (hbound z hzL)
      (hwjet z hzL).2.1 (hwjet z hzL).2.2.2
    have heq : residual ae w₀ z = residual (fun _ => ar z) w₀ z := by
      unfold residual
      rw [he hzL]
    have heq' : residual (fun _ => ar z) q z = residual ar q z := rfl
    rw [← heq, heq', hres z hzL] at hab
    have hpos : ρ ^ 2 * residual a u (Φ z) ≤ G z :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg ρ)
    have hab' := (le_abs_self _).trans hab
    dsimp [F]
    linarith
  have hw : ContDiff ℝ 2 w := hw₀.add contDiff_const
  refine ⟨A, F, w, hae, continuous_residual ae w₀ hae hw₀, hw, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change lam • 1 ≤ ae z
    rw [he hz]
    exact hlo (Φ z) (hVK (hLV hz))
  · intro z _
    rw [parabolicOperator_add_const]
    exact le_of_eq (scalar_residual_eq_parabolicOperator ae w₀ hw₀ z).symm
  · intro z hz
    have hzL : z ∈ L := by
      rcases hz with hz | hz
      · exact ⟨⟨by rw [hz.1], by rw [hz.1]; exact hh.le⟩, hz.2⟩
      · exact ⟨hz.1, hz.2.le⟩
    have hbu := hb _ (innerMap_one_boundary t₀ h v₀ hz)
    have hv := (hwjet z hzL).1
    have hi := hvalue z hzL
    have hval :=
      (abs_sub_le _ _ _).trans (add_le_add hv hi)
    have hupper := (le_abs_self _).trans hval
    change w₀ z + (-2 * η) ≤ 0
    linarith
  · intro z hz
    have hval :=
      (abs_sub_le _ _ _).trans (add_le_add ((hwjet z hz).1) (hvalue z hz))
    have heq : w z - u (innerMap t₀ h v₀ 1 z) =
        (w₀ z - u (innerMap t₀ h v₀ 1 z)) + (-2 * η) := by dsimp [w]; ring
    rw [heq]
    have hneg : |(-2 : ℝ) * η| = 2 * η := by
      rw [abs_mul, abs_of_pos hη]; norm_num
    exact (abs_add_le _ _).trans ((add_le_add hval le_rfl).trans (by
      rw [hneg]
      dsimp [η] at *
      linarith))
  · have hbnd := add_le_add (hG.2.trans hgnorm) hδnorm
    have hηε : η ≤ ε := by change ε / 4 ≤ ε; linarith
    exact (positive_norm_le_add_constant (measurableSet_parabolicInterior h 0) ((measure_mono hSL).trans_lt hL.measure_lt_top) F G (continuous_residual ae w₀ hae hw₀).aestronglyMeasurable hG.1 (fun z _ => hG0 z) (mul_nonneg hδ.le (add_nonneg zero_le_one hM)) hFbound).trans (hbnd.trans (add_le_add le_rfl hηε))

end HypoellipticAleksandrov.Parabolic.KrylovEstimate

namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Krylov's scalar parabolic Aleksandrov estimate, uniformly over location and height. -/
theorem parabolic_aleksandrov_aux
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t₀ : ℝ) (v₀ : PDE.Vec N) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (a : TimeVelocity N → PDE.Mat N) (f u : TimeVelocity N → ℝ),
        ContinuousOn a (krylovClosedCylinder t₀ h v₀) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀, (a z).IsSymm) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀,
          lam • (1 : PDE.Mat N) ≤ a z ∧ a z ≤ Lam • (1 : PDE.Mat N)) →
        MemLp f (parabolicExponent N) (volume.restrict (krylovCylinder t₀ h v₀)) →
        IsScalarC12UpTo u (krylovCylinder t₀ h v₀) (krylovClosedCylinder t₀ h v₀) →
        (∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀),
          scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)
            ≤ f z) →
        (∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) →
        ∀ z ∈ krylovCylinder t₀ h v₀,
          u z ≤ C * parabolicLpNormOn N f (krylovCylinder t₀ h v₀) := by
  obtain ⟨C, hC, hABP⟩ := parabolic_abp_unit_of_lower_ellipticity N hN lam hlam
  refine ⟨C, hC.le, ?_⟩
  intro t₀ v₀ h hh hh1 a f u ha _hsym hell hf hu hsub hb z hz
  let Z := (z.1 - (t₀ - h), z.2 - v₀)
  have hZ : Z ∈ closedParabolicCylinder h 0 := by
    refine ⟨⟨by dsimp [Z]; linarith [hz.1.1],
      by dsimp [Z]; linarith [hz.1.2]⟩, ?_⟩
    change PDE.euclideanSqDist (z.2 - v₀) 0 ≤ 1 ^ 2
    simpa [PDE.euclideanSqDist] using ((show PDE.euclideanSqDist z.2 v₀ < 1 ^ 2 from hz.2).le)
  have hmap : KrylovEstimate.innerMap t₀ h v₀ 1 Z = z := by
    apply Prod.ext
    · simp only [KrylovEstimate.innerMap, parabolicAffine, Z, one_pow,
        sub_self, zero_mul, zero_div, add_zero, one_mul]
      ring
    · simp only [KrylovEstimate.innerMap, parabolicAffine, Z, one_smul]
      exact add_sub_cancel _ _
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨A, F, w, hA, hF, hw, hlo, hsw, hbw, hclose, hnorm⟩ :=
    KrylovEstimate.exists_smooth_subsolution_close N hN lam hlam t₀ h v₀ hh a f u
      ha (fun y hy => (hell y hy).1) hf hu hsub hb hδ
  have hestimate := hABP hh hh1 0 A F w hA hF hw hlo hsw hbw Z hZ
  have hvalue := hclose Z hZ
  rw [hmap] at hvalue
  have hupper := (neg_le_abs (w Z - u z)).trans hvalue
  have hsource := mul_le_mul_of_nonneg_left hnorm hC.le
  have herror : δ * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
  nlinarith

end HypoellipticAleksandrov.Parabolic

