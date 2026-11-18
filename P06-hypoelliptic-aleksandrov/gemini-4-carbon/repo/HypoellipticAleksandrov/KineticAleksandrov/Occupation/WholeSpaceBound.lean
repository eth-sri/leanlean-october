module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothApproximation
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.CoefficientExtension
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ApproximationBounds
public import HypoellipticAleksandrov.Parabolic.ABP
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import Mathlib.Analysis.Calculus.FDeriv.Congr
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolev
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierPointwise
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTraces
public import Mathlib.Topology.Order.Real
public import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Matrix.Order
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
import Mathlib.Analysis.Calculus.FDeriv.Pow
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity

@[expose] public noncomputable section

section



namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal

variable {d : ℕ}

/-- The reflected and rescaled solution `u(t, y) = V(1 - R² t, v_* + R y)`. -/
def localizedScaled (R : ℝ) (vStar : PDE.Vec d) (V : TimeVelocity d → ℝ) :
    TimeVelocity d → ℝ :=
  fun z => V (reflectScale R vStar z)

/-- The reflected and rescaled coefficient `a(t, y) = B(1 - R² t, v_* + R y)`. -/
def localizedCoefficient (R : ℝ) (vStar : PDE.Vec d) (B : CoefficientField d) :
    TimeVelocity d → PDE.Mat d :=
  fun z => coefficientAt B (reflectScale R vStar z)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

namespace HypoellipticAleksandrov.KineticAleksandrov.LsuFree
open Parabolic Parabolic.KrylovEstimate Set Filter MeasureTheory
open scoped Topology MatrixOrder Matrix.Norms.Elementwise




/-- Krylov's scalar parabolic Aleksandrov estimate, uniformly over location and height. -/
theorem parabolic_aleksandrov_direct
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (_hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t₀ : ℝ) (v₀ : PDE.Vec N) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (a : TimeVelocity N → PDE.Mat N) (f u : TimeVelocity N → ℝ),
        ContinuousOn a (krylovClosedCylinder t₀ h v₀) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀, (a z).IsSymm) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀,
          lam • (1 : PDE.Mat N) ≤ a z ∧ a z ≤ Lam • (1 : PDE.Mat N)) →
        MemLp f (parabolicExponent N) (volume.restrict (krylovCylinder t₀ h v₀)) →
        IsScalarC12On u (krylovCylinder t₀ h v₀) →
        ContinuousOn u (krylovClosedCylinder t₀ h v₀) →
        (∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀),
          scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)
            ≤ f z) →
        (∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) →
        ∀ z ∈ krylovCylinder t₀ h v₀,
          u z ≤ C * parabolicLpNormOn N f (krylovCylinder t₀ h v₀)  := by
  have exists_smooth_subsolution_close_direct (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h) (a : TimeVelocity N → PDE.Mat N) (f : TimeVelocity N → ℝ) (u : TimeVelocity N → ℝ) (ha : ContinuousOn a (krylovClosedCylinder t₀ h v₀)) (hlo : ∀ z ∈ krylovClosedCylinder t₀ h v₀,
      lam • 1 ≤ a z) (hf : MemLp f (parabolicExponent N)
      (volume.restrict (krylovCylinder t₀ h v₀))) (hu : IsScalarC12On u (krylovCylinder t₀ h v₀)) (huc : ContinuousOn u (krylovClosedCylinder t₀ h v₀)) (hsub : ∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀), residual a u z ≤ f z) (hb : ∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) {ε : ℝ} (hε : 0 < ε) :
      ∃ (A : CoefficientField N) (F w : TimeVelocity N → ℝ),
      IsContinuousCoefficient A ∧ Continuous F ∧ ContDiff ℝ 2 w ∧
      (∀ z ∈ closedParabolicCylinder h 0,
        lam • 1 ≤ coefficientAt A z) ∧
      IsParabolicSubsolutionOn A F w (parabolicInterior h 0) ∧
      (∀ z ∈ forwardParabolicBoundary h 0, w z ≤ 0) ∧
      (∀ z ∈ closedParabolicCylinder h 0,
        |w z - u (innerMap t₀ h v₀ 1 z)| ≤ ε) ∧
      parabolicLpNormOn N (fun z => max (F z) 0)
          (parabolicInterior h 0) ≤
        parabolicLpNormOn N f (krylovCylinder t₀ h v₀) + ε := by
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
    have hg : ContinuousOn (residual a u) Q :=
      continuousOn_residual a u (ha.mono hQK) hu
    obtain ⟨hgp, hgnorm⟩ := positive_residual_memLp_norm_le hQ.measurableSet a u f
      (hg.aestronglyMeasurable hQ.measurableSet) hf hsub
    let gp : TimeVelocity N → ℝ := fun z => max (residual a u z) 0
    let η := ε / 4
    have hη : 0 < η := div_pos hε (by norm_num)
    obtain ⟨ρ, hρ, hρ1, hvalue⟩ :=
      exists_innerMap_value_close t₀ h v₀ hh u huc hη
    let Φ := innerMap t₀ h v₀ ρ
    let q := u ∘ Φ
    let ar := a ∘ Φ
    have hΦ : Continuous Φ := (contDiff_parabolicAffine _ _ _).continuous
    have hLV := innerMap_mapsTo t₀ h v₀ hh hρ hρ1
    have hVK : MapsTo Φ (Φ ⁻¹' Q) K := fun z hz => hQK hz
    obtain ⟨hq, hjet⟩ := scalarC12On_affine_pullback hQ u hu
      (t₀ - h + (1 - ρ ^ 2) * h / 2) v₀ hρ
    have har := ha.comp hΦ.continuousOn (fun z hz => hVK (hLV hz))
    obtain ⟨ae, hae, he⟩ := exists_continuous_matrix_extension hL.isClosed ar har
    let A : CoefficientField N := fun t v => ae (t, v)
    let total : TimeVelocity N → ℝ := fun z => ∑ i, ∑ j, |ar z i j|
    have htotal : ContinuousOn total L := by
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn har)).abs)
    obtain ⟨M₀, hM₀⟩ := hL.exists_bound_of_continuousOn htotal
    let M := max M₀ 0
    have hM : 0 ≤ M := le_max_right _ _
    have hbound (z : TimeVelocity N) (hz : z ∈ L) : total z ≤ M :=
      (le_abs_self _).trans ((hM₀ z hz).trans (le_max_left _ _))
    let k := parabolicLpNormOn N (fun _ : TimeVelocity N => 1) S
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
      unfold KrylovEstimate.residual
      rw [ht, hs, matrixContraction_smul_right]
      change _ - ρ ^ 2 * matrixContraction (a (Φ z)) _ = _
      ring
    have hFbound (z : TimeVelocity N) (hz : z ∈ S) : F z ≤ G z + δ * (1 + M) := by
      have hzL := hSL hz
      have hab := residual_difference_le (ar z) q w₀ z hδ.le (hbound z hzL)
        (hwjet z hzL).2.1 (hwjet z hzL).2.2.2
      have heq : residual ae w₀ z = residual (fun _ => ar z) w₀ z := by
        unfold KrylovEstimate.residual
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
      have hval : |w₀ z - u (innerMap t₀ h v₀ 1 z)| ≤ δ + η :=
        (abs_sub_le _ _ _).trans (add_le_add hv hi)
      have hupper := (le_abs_self _).trans hval
      change w₀ z + (-2 * η) ≤ 0
      linarith
    · intro z hz
      have hv := (hwjet z hz).1
      have hval :=
        (abs_sub_le _ _ _).trans (add_le_add hv (hvalue z hz))
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
  obtain ⟨C, hC, hABP⟩ := parabolic_abp_unit_of_lower_ellipticity N hN lam hlam
  refine ⟨C, hC.le, ?_⟩
  intro t₀ v₀ h hh hh1 a f u ha _hsym hell hf hu huc hsub hb z hz
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
    exists_smooth_subsolution_close_direct t₀ h v₀ hh a f u
      ha (fun y hy => (hell y hy).1) hf hu huc hsub hb hδ
  have hestimate := hABP hh hh1 0 A F w hA hF hw hlo hsw hbw Z hZ
  have hvalue := hclose Z hZ
  rw [hmap] at hvalue
  have hupper := (neg_le_abs (w Z - u z)).trans hvalue
  have herror : δ * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.LsuFree

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal

variable {d : ℕ}

section Admissibility

variable {lam Lam : ℝ} {B : CoefficientField d}
  {F : TimeVelocity d → ℝ} {α R : ℝ} {vStar : PDE.Vec d} {V : TimeVelocity d → ℝ}
  (hd : 0 < d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (hsymm : ∀ r v, (B r v).IsSymm) (hsmooth : IsSmoothCoefficient B)
  (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v) (hup : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
  (hF0 : ∀ z, 0 ≤ F z) (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
  (hFsupp : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
  (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 < R) (hR1 : 1 ≤ R)
  (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
    (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V)

include hd hlam hLam hsymm hsmooth hlow hup hF0 hFs hFc hFsupp hα0 hα1 hR hR1 hV

omit hd hLam hFsupp in
/-- Admissibility of the reflected and rescaled localized solution (for any `R ≥ 1`). -/
theorem localizedKrylov_admissible_of_one_le_direct :
    IsScalarC12On (localizedScaled R vStar V)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedScaled R vStar V)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedCoefficient R vStar B)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        (localizedCoefficient R vStar B z).IsSymm) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        lam • (1 : PDE.Mat d) ≤ localizedCoefficient R vStar B z ∧
          localizedCoefficient R vStar B z ≤ Lam • (1 : PDE.Mat d)) ∧
      0 < localHeight α R ∧ localHeight α R ≤ 1 ∧
      MemLp (localizedSource R vStar F) (parabolicExponent d)
        (volume.restrict
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d))) ∧
      (∀ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        scalarTimeDerivative (localizedScaled R vStar V) z -
            matrixContraction (localizedCoefficient R vStar B z)
              (scalarSpatialHessian (localizedScaled R vStar V) z) =
          localizedSource R vStar F z) ∧
      (∀ z, 0 ≤ localizedSource R vStar F z) ∧
      (∀ z ∈ krylovParabolicBoundary (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        localizedScaled R vStar V z = 0) ∧
      parabolicLpNormOn d (localizedSource R vStar F)
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
        R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F
            (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) ∧
      (∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R), 0 ≤ V z) := by
  have hQV : IsOpen (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
    isOpen_Ioo.prod (PDE.isOpen_euclideanBall vStar R)
  have hQ : krylovCylinder (localHeight α R) (localHeight α R) 0 ⊆
      reflectScale R vStar ⁻¹'
        scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) :=
    fun z hz => (mem_krylovCylinder_iff_reflectScale hR z).1 hz
  have hFcont : Continuous F := hFs.continuous
  refine ⟨?_, ?_, ?_, ?_, ?_,
    localHeight_pos hα1 hR, localHeight_le_one hα0 hR1, ?_, ?_, ?_, ?_, ?_,
    classical_solution_nonneg hlam hF0 hα1 hR hsmooth hlow hV⟩
  · have hc := (isScalarC12On_reflectScale hQV hV.2.1 hR vStar).1
    exact ⟨hc.continuousOn.mono hQ,
      fun z hz => hc.timeSlice_differentiableAt (hQ hz),
      fun z hz => hc.spatialSlice_contDiffAt (hQ hz),
      hc.continuousOn_scalarTimeDerivative.mono hQ,
      hc.continuousOn_scalarSpatialGradient.mono hQ,
      hc.continuousOn_scalarSpatialHessian.mono hQ⟩
  · exact hV.1.comp (continuous_reflectScale R vStar).continuousOn (krylovClosedCylinder_subset_preimage (α := α) (vStar := vStar) (d := d) hR)
  · exact (hsmooth.continuous.comp (continuous_reflectScale R vStar)).continuousOn
  · intro z _
    exact hsymm _ _
  · intro z _
    exact ⟨hlow _ _, hup _ _⟩
  · exact memLp_localizedSource hR hFcont (hFcont.memLp_of_hasCompactSupport hFc)
  · intro z hz
    have hz' := hQ hz
    show scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z -
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z) =
        R ^ 2 * F (reflectScale R vStar z)
    rw [scaled_operator_eq hQV hV.2.1 hR vStar B hz']
    have hp := hV.2.2.1 _ hz'
    simp at hp
    have hv0 : PDE.vecDot 0
        (scalarSpatialGradient V (reflectScale R vStar z)) = 0 := by
      simp [PDE.vecDot]
    have hsum : scalarTimeDerivative V (reflectScale R vStar z) +
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian V (reflectScale R vStar z)) =
        -F (reflectScale R vStar z) := by
      simpa [hv0, coefficientAt] using hp
    rw [hsum]
    ring
  · intro z
    exact mul_nonneg (sq_nonneg R) (hF0 _)
  · intro z hz
    have hmem := krylovParabolicBoundary_subset_preimage (α := α) (vStar := vStar) hR hz
    change reflectScale R vStar z ∈ scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R) ∪
      scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R) at hmem
    show V (reflectScale R vStar z) = 0
    generalize reflectScale R vStar z = w at hmem
    rcases w with ⟨r, y⟩
    rcases hmem with ht | hl
    · rw [mem_scalarParabolicTerminalFace_iff] at ht
      obtain ⟨rfl, hy⟩ := ht
      exact hV.2.2.2.1 y hy
    · exact hV.2.2.2.2 _ hl
  · exact parabolicLpNormOn_localizedSource hR hFcont

end Admissibility

/-- The admissibility statement: `R > 0` with `R² = max {1, 4 d Λ}`. -/
theorem localizedKrylov_admissible_direct
    {lam Lam : ℝ} {B : CoefficientField d}
    {F : TimeVelocity d → ℝ} {α R : ℝ} {vStar : PDE.Vec d} {V : TimeVelocity d → ℝ}
    (_hd : 0 < d) (hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (hsymm : ∀ r v, (B r v).IsSymm) (hsmooth : IsSmoothCoefficient B)
    (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
    (hup : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
    (hF0 : ∀ z, 0 ≤ F z) (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (_hFsupp : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 < R) (hRsq : R ^ 2 = max 1 (4 * d * Lam))
    (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
      (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V) :
    IsScalarC12On (localizedScaled R vStar V)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedScaled R vStar V)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedCoefficient R vStar B)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        (localizedCoefficient R vStar B z).IsSymm) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        lam • (1 : PDE.Mat d) ≤ localizedCoefficient R vStar B z ∧
          localizedCoefficient R vStar B z ≤ Lam • (1 : PDE.Mat d)) ∧
      0 < localHeight α R ∧ localHeight α R ≤ 1 ∧
      MemLp (localizedSource R vStar F) (parabolicExponent d)
        (volume.restrict
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d))) ∧
      (∀ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        scalarTimeDerivative (localizedScaled R vStar V) z -
            matrixContraction (localizedCoefficient R vStar B z)
              (scalarSpatialHessian (localizedScaled R vStar V) z) =
          localizedSource R vStar F z) ∧
      (∀ z, 0 ≤ localizedSource R vStar F z) ∧
      (∀ z ∈ krylovParabolicBoundary (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        localizedScaled R vStar V z = 0) ∧
      parabolicLpNormOn d (localizedSource R vStar F)
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
        R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F
            (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) ∧
      (∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R), 0 ≤ V z) := by
  have hR1 : 1 ≤ R := by
    have h1 : 1 ≤ R ^ 2 := by rw [hRsq]; exact le_max_left _ _
    rcases lt_or_ge R 1 with h | h
    · nlinarith
    · exact h
  exact localizedKrylov_admissible_of_one_le_direct hlam hsymm hsmooth hlow hup hF0 hFs hFc
    hα0 hα1 hR hR1 hV

end

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal

variable {d : ℕ}


/-- The restricted `L^{d+1}` norm of a continuous compactly supported function is at most its
global one. -/
theorem parabolicLpNormOn_le_parabolicLpNorm_direct
    {F : TimeVelocity d → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (S : Set (TimeVelocity d)) :
    parabolicLpNormOn d F S ≤ parabolicLpNorm d F := by
  have hfin : eLpNorm F (parabolicExponent d) volume ≠ ⊤ :=
    (hF.memLp_of_hasCompactSupport (p := parabolicExponent d) (μ := volume) hFc).ne
  exact ENNReal.toReal_mono hfin (eLpNorm_mono_measure F Measure.restrict_le_self)


end HypoellipticAleksandrov.KineticAleksandrov.Occupation

end

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set Matrix KineticAleksandrov Filter MeasureTheory Dirichlet
open scoped MatrixOrder Matrix.Norms.Elementwise Topology ENNReal

/-- The source-M quadratic barrier in the native Euclidean geometry. -/
def sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ) (y : PDE.Vec d) : ℝ :=
  M * (r ^ 2 - PDE.vecNormSq (y - v₀)) / (2 * (d : ℝ) * lam)

/-- The polynomial source barrier is smooth. -/
theorem contDiff_sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceBallBarrier v₀ r lam M) :=
  (contDiff_const.mul (contDiff_const.sub
    (PDE.contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)))).div_const _

/-- The source barrier is nonnegative on the closed Euclidean ball. -/
theorem sourceBallBarrier_nonneg {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) {y : PDE.Vec d}
    (hy : y ∈ closure (PDE.euclideanBall v₀ r)) :
    0 ≤ sourceBallBarrier v₀ r lam M y := by
  have hs : closure (PDE.euclideanBall v₀ r) ⊆
      {y | PDE.vecNormSq (y - v₀) ≤ r ^ 2} := by
    apply closure_minimal
    · intro y hy
      exact (show PDE.vecNormSq (y - v₀) < r ^ 2 from hy).le
    · exact isClosed_le (contDiff_vecNormSq_sub v₀).continuous continuous_const
  exact div_nonneg (mul_nonneg hM (sub_nonneg.mpr (hs hy)))
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hlam.le)

/-- The source barrier has zero trace on the Euclidean ball frontier. -/
theorem sourceBallBarrier_zero_frontier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    {y : PDE.Vec d} (hy : y ∈ frontier (PDE.euclideanBall v₀ r)) :
    sourceBallBarrier v₀ r lam M y = 0 := by
  rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq] at hy
  have hs : closure (PDE.euclideanBall v₀ r) ⊆
      {y | PDE.vecNormSq (y - v₀) ≤ r ^ 2} := by
    apply closure_minimal
    · intro y hy
      exact (show PDE.vecNormSq (y - v₀) < r ^ 2 from hy).le
    · exact isClosed_le (contDiff_vecNormSq_sub v₀).continuous continuous_const
  have heq : PDE.vecNormSq (y - v₀) = r ^ 2 :=
    le_antisymm (hs hy.1) (le_of_not_gt hy.2)
  simp [sourceBallBarrier, heq]

/-- The stationary quadratic has the literal negative trace forcing. -/
theorem scalarOperator_sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    (A : CoefficientField d) (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => sourceBallBarrier v₀ r lam M z.2) z =
      -(2 * M * (A z.1 z.2).trace) / (2 * (d : ℝ) * lam) := by
  let Ψ : ℝ → ℝ := fun s => M * (r ^ 2 - s) / (2 * (d : ℝ) * lam)
  have hΨ : ContDiff ℝ 2 Ψ :=
    (contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const _
  have hd (s : ℝ) : deriv Ψ s = -M / (2 * (d : ℝ) * lam) := by
    simpa only [zero_sub, mul_neg, neg_div, mul_one, Pi.sub_def, id_eq] using
      (((hasDerivAt_const s (r ^ 2)).sub (hasDerivAt_id s)).const_mul M
        |>.div_const (2 * (d : ℝ) * lam)).deriv
  have hdd (s : ℝ) : deriv (deriv Ψ) s = 0 := by
    rw [show deriv Ψ = fun _ => -M / (2 * (d : ℝ) * lam) from funext hd]
    exact deriv_const _ _
  have ht : scalarTimeDerivative (fun z => sourceBallBarrier v₀ r lam M z.2) z = 0 := by
    change deriv (fun _ : ℝ => sourceBallBarrier v₀ r lam M z.2) z.1 = 0
    exact deriv_const _ _
  rw [scalarParabolicZeroOrderOperator_apply, ht]
  simp [PDE.vecDot]
  change matrixContraction _ (sliceHessian (fun y => Ψ (PDE.vecNormSq (y - v₀))) _) = _
  rw [matrixContraction_sliceHessian_comp_vecNormSq_sub hΨ.contDiffAt, hd, hdd]
  ring

/-- Lower ellipticity gives the source-M supersolution inequality. -/
theorem scalarOperator_sourceBallBarrier_le {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r lam M : ℝ) (hlam : 0 < lam) (hM : 0 ≤ M)
    (A : CoefficientField d) (hlo : HasLowerEllipticity lam A) (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => sourceBallBarrier v₀ r lam M z.2) z ≤ -M := by
  rw [scalarOperator_sourceBallBarrier]
  have htr := (Matrix.le_iff.mp (hlo z.1 z.2)).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htr
  simp at htr
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hd)) hlam)).2
  nlinarith [mul_nonneg hM (show 0 ≤ (A z.1 z.2).trace - (d : ℝ) * lam by linarith)]


/-- Stationary scalar operators agree wherever their spatial representatives agree openly. -/
theorem stationary_scalarOperator_eqOn {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f q : PDE.Vec d → ℝ) (heq : EqOn f q Ω)
    (A : CoefficientField d) (z : TimeVelocity d) (hz : z.2 ∈ Ω) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => f z.2) z =
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => q z.2) z := by
  have he (y : PDE.Vec d) (hy : y ∈ Ω) : f =ᶠ[𝓝 y] q := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact heq hx
  have hg : PDE.classicalGradient f =ᶠ[𝓝 z.2] PDE.classicalGradient q := by
    filter_upwards [hΩ.mem_nhds hz] with y hy
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => fun i => L (PDE.basisVec i))
      (he y hy).fderiv_eq
  have hh : scalarSpatialHessian (fun z => f z.2) z =
      scalarSpatialHessian (fun z => q z.2) z := by
    ext i j
    exact congrArg (fun L : PDE.Vec d →L[ℝ] PDE.Vec d => L (PDE.basisVec i) j)
      hg.fderiv_eq
  have htf : scalarTimeDerivative (fun z => f z.2) z = 0 := by
    change deriv (fun _ : ℝ => f z.2) z.1 = 0
    exact deriv_const _ _
  have htq : scalarTimeDerivative (fun z => q z.2) z = 0 := by
    change deriv (fun _ : ℝ => q z.2) z.1 = 0
    exact deriv_const _ _
  simp [scalarParabolicZeroOrderOperator_apply, htf, htq, hh, PDE.vecDot]


/-- The smooth forcing of the source-M spatial barrier. -/
def sourceBallBarrierForcing {d : ℕ} (lam M : ℝ) (A : CoefficientField d)
    (z : TimeVelocity d) : ℝ :=
  -(2 * M * (A z.1 z.2).trace) / (2 * (d : ℝ) * lam)


/-- The ball barrier has an actual smooth H10 realization with its literal trace forcing. -/
theorem exists_h10_sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    (hr : 0 < r) (hlam : 0 < lam) (hM : 0 ≤ M) (A : CoefficientField d) :
    ∃ q : PDE.H10Function (PDE.euclideanBall v₀ r),
      ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
      EqOn q.toH1Function.toFun (sourceBallBarrier v₀ r lam M)
        (closure (PDE.euclideanBall v₀ r)) ∧
      ∀ z : TimeVelocity d, z.2 ∈ PDE.euclideanBall v₀ r →
        scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
          (fun z => q.toH1Function.toFun z.2) z = sourceBallBarrierForcing lam M A z := by
  obtain ⟨q, hq, _, hqe⟩ := exists_h10_smooth_barrier_eqOn
    (PDE.isOpen_euclideanBall v₀ r)
    (Occupation.isBounded_euclideanBall v₀ hr).isCompact_closure
    (sourceBallBarrier v₀ r lam M) (contDiff_sourceBallBarrier v₀ r lam M)
    (fun y hy => sourceBallBarrier_nonneg v₀ r lam M hlam hM (subset_closure hy))
    (fun y hy => sourceBallBarrier_zero_frontier v₀ r lam M hy)
  refine ⟨q, hq, hqe, ?_⟩
  intro z hz
  rw [stationary_scalarOperator_eqOn (PDE.isOpen_euclideanBall v₀ r)
    q.toH1Function.toFun (sourceBallBarrier v₀ r lam M)
    (hqe.mono subset_closure) A z hz, scalarOperator_sourceBallBarrier]
  rfl


/-- Smooth signed forcing admits an interior classical correction with both zero-trace bounds. -/
theorem exists_signed_source_ballInterior_with_bounds {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (M : ℝ) (hM : 0 ≤ M)
    (hFM : ∀ z ∈ scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r), |F z| ≤ M) :
    ∃ w : TimeVelocity d → ℝ,
      IsScalarC12On w (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r)) ∧
      (∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        scalarTimeDerivative w z +
          matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) = F z) ∧
      (∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        |w z| ≤ M * (T - z.1)) ∧
      ∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        |w z| ≤ sourceBallBarrier v₀ r lam M z.2  := by
  have contDiff_sourceBallBarrierForcing :
      ContDiff ℝ (⊤ : ℕ∞) (sourceBallBarrierForcing lam M A) := by
    have htr : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => (A z.1 z.2).trace) := by
      unfold Matrix.trace Matrix.diag
      apply ContDiff.sum
      intro i _
      exact (contDiff_apply ℝ ℝ i).comp
        ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
    exact (contDiff_const.mul htr).neg.div_const _
  let Ω := PDE.euclideanBall v₀ r
  have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
  have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
  obtain ⟨u, g, hdu, hu, w, _, hs, hw, he⟩ := exists_signed_source_classicalInterior
    hd hΩ hΩb a T haT lam Lam hlam hLam A hA hlo hhi F hF
  have htime := classicalEnergyRepresentative_abs_le_source_time hΩ hΩb a T lam haT
    hlam A hA hlo F hF M hM hFM u g hdu hu w hw.continuousOn hs
  obtain ⟨q, hq, hqe, hqo⟩ := exists_h10_sourceBallBarrier v₀ r lam M hr hlam hM A
  let G := sourceBallBarrierForcing lam M A
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_sourceBallBarrierForcing
  have hqn : ∀ y ∈ Ω, 0 ≤ q.toH1Function.toFun y := by
    intro y hy
    rw [hqe (subset_closure hy)]
    exact sourceBallBarrier_nonneg v₀ r lam M hlam hM (subset_closure hy)
  have hqeq : ∀ z ∈ Icc a T ×ˢ Ω,
      scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
        (fun z => q.toH1Function.toFun z.2) z = G z := fun z hz => hqo z hz.2
  have hGF : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, G z ≤ -|F z| := by
    intro z hz
    have hGle : G z ≤ -M := by
      change sourceBallBarrierForcing lam M A z ≤ -M
      rw [show sourceBallBarrierForcing lam M A z =
        scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
          (fun z => sourceBallBarrier v₀ r lam M z.2) z from
            (scalarOperator_sourceBallBarrier v₀ r lam M A z).symm]
      exact scalarOperator_sourceBallBarrier_le hd v₀ r lam M hlam hM A hlo z
    exact hGle.trans (neg_le_neg (hFM z hz))
  have henergy := variationalEnergySolution_abs_le_stationary_barrier hΩ hΩb a T haT
    lam hlam A hA hlo F G hF hG q (hq.of_le (by simp)) hqn hqeq hGF u g hdu hu
  have hspace := classicalEnergyRepresentative_abs_le_continuous_barrier hΩ a T haT
    u g hdu q.toH1Function.toFun hq.continuous henergy w hw.continuousOn hs
  refine ⟨w, hw, he, htime, ?_⟩
  intro z hz
  simpa only [hqe (subset_closure hz.2)] using hspace z hz


/-- The spatial barrier gives ambient continuity of the zero extension at lateral points. -/
theorem continuousAt_source_zeroExtension_lateral {d : ℕ}
    (a T : ℝ) (v₀ : PDE.Vec d) (r lam M : ℝ) (w : TimeVelocity d → ℝ)
    (hb : ∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
      |w z| ≤ sourceBallBarrier v₀ r lam M z.2)
    (p : TimeVelocity d) (hp : p.2 ∈ frontier (PDE.euclideanBall v₀ r)) :
    ContinuousAt (sourceInteriorZeroExtension a T (PDE.euclideanBall v₀ r) w) p := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  let U := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension a T Ω w
  have hpo : p.2 ∉ Ω := by
    rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq] at hp
    exact hp.2
  have hpW : W p = 0 := by
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hpo h.2)
  have hbW (z : TimeVelocity d) : ‖W z‖ ≤ |sourceBallBarrier v₀ r lam M z.2| := by
    by_cases hz : z ∈ U
    · rw [show W z = w z from piecewise_eq_of_mem U w (fun _ => 0) hz,
        Real.norm_eq_abs]
      exact (hb z hz).trans (le_abs_self _)
    · rw [show W z = 0 from piecewise_eq_of_notMem U w (fun _ => 0) hz, norm_zero]
      exact abs_nonneg _
  have hc : Continuous (fun z : TimeVelocity d => |sourceBallBarrier v₀ r lam M z.2|) :=
    ((contDiff_sourceBallBarrier v₀ r lam M).continuous.comp continuous_snd).abs
  have hz : Tendsto (fun z : TimeVelocity d => |sourceBallBarrier v₀ r lam M z.2|)
      (𝓝 p) (𝓝 0) := by
    simpa [sourceBallBarrier_zero_frontier v₀ r lam M hp] using
      (hc.continuousAt (x := p)).tendsto
  change Tendsto W (𝓝 p) (𝓝 (W p))
  rw [hpW]
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) hbW hz)

/-- A time collar and both envelopes give continuity on the entire closed cylinder. -/
theorem continuousOn_source_zeroExtension_closed_ball {d : ℕ}
    (a₀ a T : ℝ) (ha : a₀ < a) (v₀ : PDE.Vec d) (r lam M : ℝ)
    (hM : 0 ≤ M) (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r)))
    (ht : ∀ z ∈ scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r),
      |w z| ≤ M * (T - z.1))
    (hs : ∀ z ∈ scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r),
      |w z| ≤ sourceBallBarrier v₀ r lam M z.2) :
    ContinuousOn (sourceInteriorZeroExtension a₀ T (PDE.euclideanBall v₀ r) w)
      (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r)) := by
  classical
  intro p hp
  by_cases hpt : p.1 = T
  · exact (continuousWithinAt_source_zeroExtension_terminal a₀ T M hM w ht p hpt).mono
      (prod_mono (Icc_subset_Icc ha.le le_rfl) (Subset.refl _))
  · by_cases hpy : p.2 ∈ PDE.euclideanBall v₀ r
    · let U := scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r)
      have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ r)
      have hpu : p ∈ U := ⟨⟨lt_of_lt_of_le ha hp.1.1,
        lt_of_le_of_ne hp.1.2 hpt⟩, hpy⟩
      have he : sourceInteriorZeroExtension a₀ T (PDE.euclideanBall v₀ r) w =ᶠ[𝓝 p] w := by
        filter_upwards [hU.mem_nhds hpu] with z hz
        exact piecewise_eq_of_mem U w (fun _ => 0) hz
      exact ((hw.continuousAt (hU.mem_nhds hpu)).congr_of_eventuallyEq he).continuousWithinAt
    · have hpf : p.2 ∈ frontier (PDE.euclideanBall v₀ r) := by
        rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq]
        exact ⟨hp.2, hpy⟩
      have hc := continuousAt_source_zeroExtension_lateral a₀ T v₀ r lam M w hs p hpf
      exact hc.continuousWithinAt


/-- Every smooth signed source has a continuous zero-boundary classical correction on a ball. -/
theorem exists_signed_source_ball_correction {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ W : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        (fun _ => 0) (fun _ => 0) W := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
  have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
  have hleft : a - 1 < a := by linarith
  have hleftT : a - 1 < T := hleft.trans haT
  have hK := isCompact_scalarParabolicClosedCylinder (a - 1) T hΩb
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hFM : ∀ z ∈ scalarParabolicClosedCylinder (a - 1) T Ω, |F z| ≤ M := by
    intro z hz
    rw [← Real.norm_eq_abs]
    exact (hC z hz).trans (le_max_left _ _)
  obtain ⟨w, hw, he, ht, hs⟩ := exists_signed_source_ballInterior_with_bounds hd
    v₀ r hr (a - 1) T hleftT lam Lam hlam hLam A hA hlo hhi F hF M hM hFM
  let U := scalarParabolicOpenCylinder (a - 1) T Ω
  let D := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension (a - 1) T Ω w
  have hsub : D ⊆ U := prod_mono (Ioo_subset_Ioo hleft.le le_rfl) (Subset.refl _)
  have hWD : EqOn W w D := by
    intro z hz
    exact piecewise_eq_of_mem U w (fun _ => 0) (hsub hz)
  have hwD : IsScalarC12On w D :=
    ⟨hw.continuousOn.mono hsub,
      fun z hz => hw.timeSlice_differentiableAt (hsub hz),
      fun z hz => hw.spatialSlice_contDiffAt (hsub hz),
      hw.continuousOn_scalarTimeDerivative.mono hsub,
      hw.continuousOn_scalarSpatialGradient.mono hsub,
      hw.continuousOn_scalarSpatialHessian.mono hsub⟩
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  have hWc := continuousOn_source_zeroExtension_closed_ball (a - 1) a T hleft
    v₀ r lam M hM w hw.continuousOn ht hs
  have hWr := Occupation.isScalarC12On_congr_open hD hwD hWD
  obtain ⟨hdt, _, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, hWc, hWr, ?_, ?_, ?_⟩
  · intro z hz
    simp [scalarParabolicZeroOrderOperator_apply, PDE.vecDot, hdt hz, hdd hz]
    exact he z (hsub hz)
  · intro y _
    exact piecewise_eq_of_notMem U w (fun _ => 0)
      (fun h => (lt_irrefl T) h.1.2)
  · intro z hz
    have hzo : z.2 ∉ Ω := by
      have hf : z.2 ∈ frontier Ω := hz.2
      rw [hΩ.frontier_eq] at hf
      exact hf.2
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hzo h.2)

end HypoellipticAleksandrov.Parabolic.LocalHolder

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open Set HypoellipticAleksandrov.Parabolic Filter Matrix HypoellipticAleksandrov SectionTwo
open scoped MatrixOrder Topology ContDiff BigOperators Matrix.Norms.Elementwise


/-- A uniform half-supremum bound absorbs to twice the source bound. -/
theorem wholeSpace_absorb {α : Type*} {A : Set α} {W : α → ℝ} {M : ℝ}
    (hne : A.Nonempty)
    (hpoint : ∀ x ∈ A, W x ≤ M + sSup (W '' A) / 2) :
    sSup (W '' A) ≤ 2 * M := by
  have hsup : sSup (W '' A) ≤ M + sSup (W '' A) / 2 := by
    apply csSup_le (hne.image W)
    rintro _ ⟨x, hx, rfl⟩
    exact hpoint x hx
  linarith only [hsup]



private theorem scalarTimeDerivative_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarTimeDerivative (fun q => u q - v q) z =
      scalarTimeDerivative u z - scalarTimeDerivative v z := by
  exact ((hu.timeSlice_hasDerivAt hz).sub (hv.timeSlice_hasDerivAt hz)).deriv

private theorem scalarSpatialGradient_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialGradient (fun q => u q - v q) z =
      scalarSpatialGradient u z - scalarSpatialGradient v z := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u (z.1, y) - v (z.1, y)) z.2
      (PDE.basisVec i) = _
  rw [fderiv_fun_sub ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
    ((hv.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))]
  rfl

private theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    intro j
    exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt
  change (fderiv ℝ (fun y : PDE.Vec n => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi hdiff]
  have hj := (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv
  have hjApply := congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hj
  simpa [ContinuousLinearMap.flip_apply] using hjApply

private theorem scalarSpatialHessian_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialHessian (fun q => u q - v q) z =
      scalarSpatialHessian u z - scalarSpatialHessian v z := by
  let g_u : PDE.Vec n → ℝ := fun y => u (z.1, y)
  let g_v : PDE.Vec n → ℝ := fun y => v (z.1, y)
  have hfirst : fderiv ℝ (fun y => g_u y - g_v y) =ᶠ[𝓝 z.2]
      fun y => fderiv ℝ g_u y - fderiv ℝ g_v y := by
    filter_upwards [(hu.spatialSlice_contDiffAt hz).eventually (by norm_num),
      (hv.spatialSlice_contDiffAt hz).eventually (by norm_num)] with y huy hvy
    exact fderiv_fun_sub (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))
  have huSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_u y)
      (fderiv ℝ (fderiv ℝ g_u) z.2) z.2 :=
    ((hu.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hvSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_v y)
      (fderiv ℝ (fderiv ℝ g_v) z.2) z.2 :=
    ((hv.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hsecond : fderiv ℝ (fderiv ℝ (fun y => g_u y - g_v y)) z.2 =
      fderiv ℝ (fderiv ℝ g_u) z.2 - fderiv ℝ (fderiv ℝ g_v) z.2 := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => g_u y - g_v y)) z.2 =
          fderiv ℝ (fun y => fderiv ℝ g_u y - fderiv ℝ g_v y) z.2 :=
        hfirst.fderiv_eq
      _ = fderiv ℝ (fderiv ℝ g_u) z.2 - fderiv ℝ (fderiv ℝ g_v) z.2 :=
        fderiv_fun_sub huSecond.differentiableAt hvSecond.differentiableAt
  ext i j
  rw [Matrix.sub_apply,
    scalarSpatialHessian_apply_eq_sndFDeriv
    ((hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hv.spatialSlice_contDiffAt hz) i j,
    hsecond]
  rfl

/-- Scalar classical regularity is stable under subtraction. -/
theorem isScalarC12On_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D) :
    IsScalarC12On (fun q => u q - v q) D := by
  refine ⟨hu.continuousOn.sub hv.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hu.timeSlice_differentiableAt hz).sub (hv.timeSlice_differentiableAt hz)
  · intro z hz
    exact (hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)
  · apply (hu.continuousOn_scalarTimeDerivative.sub
      hv.continuousOn_scalarTimeDerivative).congr
    intro z hz
    exact scalarTimeDerivative_sub hu hv hz
  · apply (hu.continuousOn_scalarSpatialGradient.sub
      hv.continuousOn_scalarSpatialGradient).congr
    intro z hz
    exact scalarSpatialGradient_sub hu hv hz
  · apply (hu.continuousOn_scalarSpatialHessian.sub
      hv.continuousOn_scalarSpatialHessian).congr
    intro z hz
    exact scalarSpatialHessian_sub hu hv hz

/-- The scalar zero-order operator is linear on classical functions. -/
theorem scalarParabolicZeroOrderOperator_sub {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q - v q) z =
      scalarParabolicZeroOrderOperator a b c u z -
        scalarParabolicZeroOrderOperator a b c v z := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarParabolicZeroOrderOperator_apply,
    scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_sub hu hv hz,
    scalarSpatialGradient_sub hu hv hz, scalarSpatialHessian_sub hu hv hz]
  have hHessian : matrixContraction (a z.1 z.2)
      (scalarSpatialHessian u z - scalarSpatialHessian v z) =
      matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) -
        matrixContraction (a z.1 z.2) (scalarSpatialHessian v z) := by
    unfold matrixContraction
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hGradient : PDE.vecDot (b z.1 z.2)
      (scalarSpatialGradient u z - scalarSpatialGradient v z) =
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) -
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient v z) := by
    unfold PDE.vecDot
    simp [mul_sub, Finset.sum_sub_distrib]
  rw [hHessian, hGradient]
  ring



/-- Full smoothness restricts to the time--velocity coefficient. -/
theorem sectionTwoCoefficient_smooth {d : ℕ} {lam Lam : ℝ} {B : CoefficientField d}
    (hB : IsSectionTwoCoefficient lam Lam B) : IsSmoothCoefficient B := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have he : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × PDE.Vec d => (q.1, (q.2, (0 : PDE.Vec d)))) := by fun_prop
  exact (hB.2.2.1 i j).comp he

/-- Lower ellipticity implies positive semidefiniteness. -/
theorem sectionTwoCoefficient_posSemidef {d : ℕ} {lam Lam : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B) (r : ℝ)
    (v : PDE.Vec d) : (B r v).PosSemidef := by
  have hzero : 0 ≤ lam • (1 : PDE.Mat d) :=
    smul_nonneg hB.1.le (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one)
  exact Matrix.nonneg_iff_posSemidef.mp (hzero.trans (hB.2.2.2.2.1 r v))


/-- The numerator of the source quadratic supersolution. -/
def occupationQuadratic {d : ℕ} (Lam : ℝ) (vStar : PDE.Vec d)
    (z : TimeVelocity d) : ℝ :=
  (∑ i, (z.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - z.1)

private theorem gradient_sum_sq {d : ℕ} (vStar v : PDE.Vec d) :
    PDE.classicalGradient (fun y => ∑ i, (y i - vStar i) ^ 2) v =
      fun i => 2 * (v i - vStar i) := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun (i : Fin d) _ => ((hasFDerivAt_apply (𝕜 := ℝ) i v).sub_const (vStar i)).pow 2)
  ext i
  unfold PDE.classicalGradient
  rw [h.fderiv]
  simp [PDE.basisVec_apply]


/-- Its time derivative has the backward supersolution sign. -/
theorem scalarTimeDerivative_occupationQuadratic {d : ℕ} (Lam : ℝ)
    (vStar : PDE.Vec d) (z : TimeVelocity d) :
    scalarTimeDerivative (occupationQuadratic Lam vStar) z = -2 * d * Lam := by
  unfold scalarTimeDerivative occupationQuadratic
  have h := ((hasDerivAt_id z.1).const_sub 1).const_mul (2 * d * Lam)
  have h' := h.const_add (∑ i, (z.2 i - vStar i) ^ 2)
  simpa [mul_neg, neg_mul] using h'.deriv

/-- Its velocity Hessian is twice the identity. -/
theorem scalarSpatialHessian_occupationQuadratic {d : ℕ} (Lam : ℝ)
    (vStar : PDE.Vec d) (z : TimeVelocity d) :
    scalarSpatialHessian (occupationQuadratic Lam vStar) z =
      (2 : ℝ) • (1 : PDE.Mat d) := by
  have hg : (fun y : PDE.Vec d =>
      PDE.classicalGradient (fun w => occupationQuadratic Lam vStar (z.1, w)) y) =
      fun y => fun j => 2 * (y j - vStar j) := by
    funext y
    ext i
    change (fderiv ℝ (fun w : PDE.Vec d =>
      (∑ j, (w j - vStar j) ^ 2) + 2 * d * Lam * (1 - z.1)) y)
      (PDE.basisVec i) = _
    rw [fderiv_add_const]
    exact congrFun (gradient_sum_sq vStar y) i
  unfold scalarSpatialHessian
  rw [hg]
  have hdiff : ∀ j : Fin d,
      DifferentiableAt ℝ (fun y : PDE.Vec d => 2 * (y j - vStar j)) z.2 := by
    intro j
    exact (((hasFDerivAt_apply (𝕜 := ℝ) j z.2).sub_const (vStar j)).const_mul 2).differentiableAt
  ext i j
  rw [fderiv_pi hdiff]
  change (fderiv ℝ (fun y : PDE.Vec d => 2 * (y j - vStar j)) z.2)
    (PDE.basisVec i) = _
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) j z.2).sub_const (vStar j)).const_mul 2).fderiv
  rw [h]
  simp [PDE.basisVec_apply, Matrix.one_apply, eq_comm]

/-- Upper ellipticity makes the quadratic numerator a backward supersolution. -/
theorem scalarParabolicOperator_occupationQuadratic_le {d : ℕ}
    (B : CoefficientField d) (Lam : ℝ) (vStar : PDE.Vec d) (z : TimeVelocity d)
    (hB : B z.1 z.2 ≤ Lam • (1 : PDE.Mat d)) :
    scalarParabolicOperator B (fun _ _ => 0) (occupationQuadratic Lam vStar) z ≤ 0 := by
  have hpsd : (Lam • 1 - B z.1 z.2).PosSemidef :=
    Matrix.le_iff.mp hB
  have htrace := hpsd.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htrace
  simp [Fintype.card_fin] at htrace
  have hcontract : matrixContraction (B z.1 z.2) 1 =
      (B z.1 z.2).trace := by
    simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]
  unfold scalarParabolicOperator
  rw [scalarTimeDerivative_occupationQuadratic, scalarSpatialHessian_occupationQuadratic,
    matrixContraction_smul_right, hcontract]
  simp only [PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  linarith



/-- A smooth quadratic majorant controls a classical comparison defect. -/
theorem wholeSpace_quadratic_comparison {d : ℕ} {lam Lam α R H : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (hα : α < 1) (vStar : PDE.Vec d)
    (hΩbounded : Bornology.IsBounded (PDE.euclideanBall vStar R))
    (hH : 0 ≤ H)
    (W V : TimeVelocity d → ℝ) (F : TimeVelocity d → ℝ)
    (hWcont : ContinuousOn W
      (scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R)))
    (hWreg : IsScalarC12On W
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)))
    (hWeq : ∀ z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R),
      scalarParabolicOperator B (fun _ _ => 0) W z = -F z)
    (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
      (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
      (fun _ => 0) (fun _ => 0) V)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R),
      W z = 0)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R),
      W z ≤ H * occupationQuadratic Lam vStar z / R ^ 2) :
    ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
      W z ≤ V z + H * occupationQuadratic Lam vStar z / R ^ 2   := by
  have occupationQuadratic_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam) {z : TimeVelocity d} (hz : z.1 ≤ 1) :
      0 ≤ occupationQuadratic Lam vStar z := by
    unfold occupationQuadratic
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hz))
  have contDiff_occupationQuadratic (Lam : ℝ) :
      ContDiff ℝ (⊤ : ℕ∞) (occupationQuadratic Lam vStar) := by
    unfold occupationQuadratic
    fun_prop
  let c := H / R ^ 2
  let Q := occupationQuadratic Lam vStar
  let ψ := fun z => c * Q z + 0
  have hc : 0 ≤ c := div_nonneg hH (sq_nonneg R)
  have hQreg : IsScalarC12On Q
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
    isScalarC12On_of_contDiff_two
      ((contDiff_occupationQuadratic Lam).of_le (by simp)) _
  have hψreg := hQreg.const_mul_add_const c 0
  have hdiff := isScalarC12On_sub hWreg hV.2.1
  let u := fun z => W z - V z - ψ z
  have hureg : IsScalarC12On u
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
    isScalarC12On_sub hdiff hψreg
  have huc : ContinuousOn u
      (scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R)) :=
    (hWcont.sub hV.1).sub
      (((contDiff_occupationQuadratic Lam).continuous.const_mul c).add
        continuous_const).continuousOn
  have hsub : ∀ z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R),
      0 ≤ scalarParabolicOperator B (fun _ _ => 0) u z := by
    intro z hz
    have huop := scalarParabolicZeroOrderOperator_sub B (fun _ _ => 0)
      (fun _ _ => 0) hdiff hψreg hz
    have hdop := scalarParabolicZeroOrderOperator_sub B (fun _ _ => 0)
      (fun _ _ => 0) hWreg hV.2.1 hz
    have hψop := scalarParabolicZeroOrderOperator_const_mul_add_const B
      (fun _ _ => 0) (fun _ _ => 0) c 0 Q z
    have hVeq := hV.2.2.1 z hz
    have hQop := scalarParabolicOperator_occupationQuadratic_le B Lam vStar z
      (hB.2.2.2.2.2 z.1 z.2)
    simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at huop hdop hψop hVeq
    change 0 ≤ scalarParabolicOperator B (fun _ _ => 0) u z
    simp only [u, ψ, add_zero]
    rw [huop, hdop, hψop, hWeq z hz, hVeq]
    simpa only [Prod.mk.eta, sub_self] using
      sub_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hc hQop)
  have ht : ∀ z ∈ scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R),
      u z ≤ 0 := by
    intro z hz
    obtain ⟨htime, hv⟩ := mem_scalarParabolicTerminalFace_iff.mp hz
    have hVz : V z = 0 := by
      have he : z = (1, z.2) := Prod.ext htime rfl
      rw [he]
      exact hV.2.2.2.1 z.2 hv
    have hQ0 := occupationQuadratic_nonneg (hB.1.le.trans hB.2.1)
      (show z.1 ≤ 1 from htime.le)
    dsimp [u, ψ]
    rw [hterminal z hz, hVz]
    nlinarith [mul_nonneg hc hQ0]
  have hl : ∀ z ∈ scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R),
      u z ≤ 0 := by
    intro z hz
    have hw := hlateral z hz
    have hv := hV.2.2.2.2 z hz
    dsimp [u, ψ, c, Q]
    rw [hv]
    simpa only [sub_zero, add_zero, div_mul_eq_mul_div, sub_nonpos] using hw
  have hmax := scalar_le_on_closedCylinder_of_terminal_lateral_le
    (PDE.isOpen_euclideanBall vStar R) hΩbounded hα B (fun _ _ => 0)
    (sectionTwoCoefficient_smooth hB).continuous continuous_const
    (sectionTwoCoefficient_posSemidef hB) u huc hureg hsub ht hl
  intro z hz
  have hu := hmax z hz
  dsimp [u, ψ, c, Q] at hu
  rw [div_mul_eq_mul_div] at hu
  linarith


/-- The whole-space potential admits the source quadratic comparison on every ball. -/
theorem wholeSpace_localization_direct {d : ℕ} (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d)
    {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K)
    (F : TimeVelocity d → ℝ) (hF0 : ∀ q, 0 ≤ F q)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (vStar : PDE.Vec d)
    (R : ℝ) (hR : 0 < R) (hRsq : R ^ 2 = max 1 (4 * d * Lam)) :
    let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
    let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
    ∃ V : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
        (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
        (fun _ => 0) (fun _ => 0) V ∧
      (∀ q ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
        W q ≤ V q + H * occupationQuadratic Lam vStar q / R ^ 2) ∧
      (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2   := by
  have occupationQuadratic_center_half {d : ℕ} {Lam α R : ℝ} (hLam : 0 ≤ Lam) (hα : 0 ≤ α) (hR : 0 < R) (hRsq : R ^ 2 = max 1 (4 * d * Lam)) :
      (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    have hb : 4 * (d : ℝ) * Lam ≤ R ^ 2 := hRsq ▸ le_max_right _ _
    have ha : 0 ≤ 2 * (d : ℝ) * Lam := by positivity
    nlinarith [mul_nonneg ha hα]
  have radius_sq_le_frontier_sum {v : PDE.Vec d} (hv : v ∈ frontier (PDE.euclideanBall vStar R)) :
      R ^ 2 ≤ ∑ i, (v i - vStar i) ^ 2 := by
    have hn : v ∉ PDE.euclideanBall vStar R :=
      (PDE.isOpen_euclideanBall vStar R).frontier_eq ▸ hv |>.2
    have hsq : ¬ PDE.euclideanSqDist v vStar < R ^ 2 := hn
    simpa [PDE.euclideanSqDist, PDE.vecNormSq_eq_sum_sq] using le_of_not_gt hsq
  dsimp only
  let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
  let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
  obtain ⟨hW0, hbdd, -, hWt, hWs, hWe⟩ :=
    occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
  have hH0 : 0 ≤ H := (hW0 (0, 0)).trans
    (le_csSup hbdd ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
  have hU : tsupport F ⊆ {p : TimeVelocity d | p.1 < 1 ∧
      p.2 ∈ movingDomain (wholeSpace d) (fun _ => (0 : PDE.Vec d)) p.1} := by
    intro p hp
    exact ⟨(hFsupp hp).1.2, by simp [movingDomain_wholeSpace]⟩
  have hWcont := (parabolic_duhamel hH (wholeSpace_admissible d)
    (zeroCurve_piecewiseC1 d) hB K hP 1 F hF0 hFs hFc hU).2.2.2.1
  obtain ⟨V, hV⟩ := LocalHolder.exists_signed_source_ball_correction hd vStar R hR α 1
    hα1 lam Lam hB.1 hB.2.1 B (sectionTwoCoefficient_smooth hB)
    hB.2.2.2.2.1 hB.2.2.2.2.2 (fun z => -F z) hFs.neg
  refine ⟨V, hV, ?_, occupationQuadratic_center_half (hB.1.le.trans hB.2.1)
    hα0 hR hRsq⟩
  apply wholeSpace_quadratic_comparison hB hα1 vStar (isBounded_euclideanBall vStar hR)
    hH0 W V F
  · exact hWcont.mono fun p hp => ⟨hp.1.2, by simp [movingDomain_wholeSpace]⟩
  · apply isScalarC12On_of_isOpen_contDiffOn_two
      (isOpen_Ioo.prod (PDE.isOpen_euclideanBall vStar R))
    exact (hWs.of_le (by simp)).mono fun p hp => hp.1.2
  · intro p hp
    exact hWe p hp.1.2
  · exact hV
  · intro p hp
    have ht := (mem_scalarParabolicTerminalFace_iff.mp hp).1
    have hpEq : p = (1, p.2) := Prod.ext ht rfl
    rw [hpEq]
    exact hWt p.2
  · intro p hp
    have hz := mem_scalarParabolicLateralFace_iff.mp hp
    have hw : W p ≤ H := le_csSup hbdd
      ⟨p, ⟨⟨hα0.trans hz.1, hz.2.1⟩, mem_univ _⟩, rfl⟩
    have hs := radius_sq_le_frontier_sum hz.2.2
    have ht : 0 ≤ 2 * (d : ℝ) * Lam * (1 - p.1) :=
      mul_nonneg (by positivity [hB.1.le.trans hB.2.1]) (sub_nonneg.mpr hz.2.1)
    apply hw.trans
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    unfold occupationQuadratic
    exact mul_le_mul_of_nonneg_left (by linarith) hH0

variable {d : ℕ}

/-- The uniform whole-space source estimate and its ball comparison. -/
theorem occupation_whole_space_bound
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (F : TimeVelocity d → ℝ) (_hF0 : ∀ q, 0 ≤ F q)
        (_hFs : ContDiff ℝ (⊤ : ℕ∞) F) (_hFc : HasCompactSupport F)
        (_hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ),
        let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
        let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
        (∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ (vStar : PDE.Vec d) (R : ℝ),
          0 < R → R ^ 2 = max 1 (4 * d * Lam) →
          ∃ V : TimeVelocity d → ℝ,
            IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
              (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
              (fun _ => 0) (fun _ => 0) V ∧
            (∀ q ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
              W q ≤ V q + H *
                ((∑ i, (q.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - q.1)) / R ^ 2) ∧
            (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2) ∧
        H ≤ C * parabolicLpNorm d F  := by
  have localizedBound_direct :
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_ : ∀ r v, (B r v).IsSymm) (_ : IsSmoothCoefficient B)
        (_ : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
        (_ : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
        (F : TimeVelocity d → ℝ) (_ : ∀ z, 0 ≤ F z) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
        (_ : HasCompactSupport F) (_ : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
        (α : ℝ) (_ : 0 ≤ α) (_ : α < 1) (vStar : PDE.Vec d) (R : ℝ) (_ : 0 < R)
        (_ : R ^ 2 = max 1 (4 * d * Lam))
        (V : TimeVelocity d → ℝ)
        (_ : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
          (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V),
        ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
          0 ≤ V z ∧ V z ≤ C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) * parabolicLpNorm d F := open MeasureTheory in by
    have localizedBound_cylinder_direct :
        ∃ C : ℝ, 0 ≤ C ∧
        ∀ (B : CoefficientField d) (_ : ∀ r v, (B r v).IsSymm) (_ : IsSmoothCoefficient B)
          (_ : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
          (_ : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
          (F : TimeVelocity d → ℝ) (_ : ∀ z, 0 ≤ F z) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
          (_ : HasCompactSupport F) (_ : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
          (α : ℝ) (_ : 0 ≤ α) (_ : α < 1) (vStar : PDE.Vec d) (R : ℝ) (_ : 0 < R)
          (_ : R ^ 2 = max 1 (4 * d * Lam))
          (V : TimeVelocity d → ℝ)
          (_ : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
            (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V),
          ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
            0 ≤ V z ∧ V z ≤ C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
              parabolicLpNormOn d F
                (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
      obtain ⟨C, hC0, hK⟩ :=
        LsuFree.parabolic_aleksandrov_direct d hd lam Lam hlam hLam
      refine ⟨C, hC0, ?_⟩
      intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV
      obtain ⟨hInterior, hValue, hcoef, hsy, hbd, hpos, hle, hmem, hpde, -, hzero, hnorm, hnonneg⟩ :=
        localizedKrylov_admissible_direct hd hlam hLam hsymm hsmooth hlow hup hF0 hFs hFc hFsupp
          hα0 hα1 hR hRsq hV
      set Qk := krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) with hQk
      set QV := scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) with hQV
      set M : ℝ := C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d F QV with hM
      -- Krylov's estimate on the open cylinder
      have hqk := hK (localHeight α R) (0 : PDE.Vec d) (localHeight α R) hpos hle
        (localizedCoefficient R vStar B) (localizedSource R vStar F) (localizedScaled R vStar V)
        hcoef hsy hbd hmem hInterior hValue
        (ae_restrict_of_forall_mem (isOpen_krylovCylinder _ _ _).measurableSet
          (fun z hz => (hpde z hz).le))
        (fun z hz => (hzero z hz).le)
      have hopen : ∀ w ∈ QV, V w ≤ M := by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := exists_mem_krylovCylinder hR hw
        have h1 := hqk z hz
        rw [hnorm] at h1
        change V (reflectScale R vStar z) ≤ _ at h1
        simpa only [hM, mul_assoc] using h1
      -- extension to the closed cylinder by continuity
      have hclosure : closure QV = scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) := by
        rw [hQV, scalarParabolicOpenCylinder, closure_prod_eq, closure_Ioo hα1.ne]
        rfl
      intro z hz
      refine ⟨hnonneg z hz, ?_⟩
      have hQK : QV ⊆ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) :=
        subset_closure.trans hclosure.le
      have hzc : z ∈ closure QV := by rw [hclosure]; exact hz
      exact ContinuousWithinAt.closure_le hzc ((hV.1 z hz).mono hQK) continuousWithinAt_const hopen
    obtain ⟨C, hC0, hbound⟩ := localizedBound_cylinder_direct
    refine ⟨C, hC0, ?_⟩
    intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV z hz
    obtain ⟨h0, h1⟩ := hbound B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR
      hRsq V hV z hz
    refine ⟨h0, h1.trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (parabolicLpNormOn_le_parabolicLpNorm_direct hFs.continuous hFc _)
      (mul_nonneg hC0 (Real.rpow_nonneg hR.le _))
  obtain ⟨C, hC0, hbound⟩ := localizedBound_direct
  let R := Real.sqrt (max 1 (4 * (d : ℝ) * Lam))
  have hm : 0 < max 1 (4 * (d : ℝ) * Lam) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hR : 0 < R := Real.sqrt_pos.mpr hm
  have hRsq : R ^ 2 = max 1 (4 * (d : ℝ) * Lam) := Real.sq_sqrt hm.le
  let M := C * R ^ ((d : ℝ) / ((d : ℝ) + 1))
  have hM : 0 ≤ M := mul_nonneg hC0 (Real.rpow_nonneg hR.le _)
  refine ⟨2 * M, by positivity, ?_⟩
  intro B hB S K _hreal hP F hF0 hFs hFc hFsupp
  dsimp only
  let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
  let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
  have hloc := wholeSpace_localization_direct hH hd hB K hP F hF0 hFs hFc hFsupp
  refine ⟨?_, ?_⟩
  · intro α hα0 hα1 vStar R' hR' hRsq'
    simpa only [occupationQuadratic] using hloc α hα0 hα1 vStar R' hR' hRsq'
  · have hnorm : 0 ≤ parabolicLpNorm d F := ENNReal.toReal_nonneg
    have hpoint : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ univ,
        W q ≤ M * parabolicLpNorm d F + H / 2 := by
      intro q hq
      by_cases ht : q.1 = 1
      · have hzero : W q = 0 := by
          exact parabolicDuhamelPotential_eq_zero_of_terminal_le K MeasurableSet.univ
            1 F q ht.ge
        have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
        have hH0 : 0 ≤ H := (hpot.1 (0, 0)).trans
          (le_csSup hpot.2.1 ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
        rw [hzero]
        positivity
      · have htlt : q.1 < 1 := lt_of_le_of_ne hq.1.2 ht
        obtain ⟨V, hV, hcmp, hhalf⟩ := hloc q.1 hq.1.1 htlt q.2 R hR hRsq
        have hqball : q.2 ∈ closure (PDE.euclideanBall q.2 R) := by
          apply subset_closure
          change PDE.euclideanSqDist q.2 q.2 < R ^ 2
          simpa [PDE.euclideanSqDist, PDE.vecNormSq_eq_sum_sq] using sq_pos_of_pos hR
        have hqc : q ∈ scalarParabolicClosedCylinder q.1 1
            (PDE.euclideanBall q.2 R) := ⟨⟨le_rfl, hq.1.2⟩, hqball⟩
        have hc := hcmp q hqc
        have hv := (hbound B hB.2.2.2.1 (sectionTwoCoefficient_smooth hB)
          hB.2.2.2.2.1 hB.2.2.2.2.2 F hF0 hFs hFc hFsupp q.1 hq.1.1 htlt
          q.2 R hR hRsq V hV q hqc).2
        have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
        have hH0 : 0 ≤ H := (hpot.1 (0, 0)).trans
          (le_csSup hpot.2.1 ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
        have hh := mul_le_mul_of_nonneg_left hhalf hH0
        simp only [occupationQuadratic, sub_self, zero_pow (by norm_num : 2 ≠ 0),
          Finset.sum_const_zero, zero_add] at hc
        rw [mul_div_assoc] at hc
        dsimp [M] at hv ⊢
        linarith
    have hsup := wholeSpace_absorb
      (show (Icc (0 : ℝ) 1 ×ˢ (univ : Set (PDE.Vec d))).Nonempty from
        ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩⟩) hpoint
    change H ≤ (2 * M) * parabolicLpNorm d F
    nlinarith [hsup]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

