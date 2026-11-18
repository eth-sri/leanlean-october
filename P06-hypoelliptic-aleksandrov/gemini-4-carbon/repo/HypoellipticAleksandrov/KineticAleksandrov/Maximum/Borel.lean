module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Matrix.Normed
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelPhaseMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect
import Mathlib.MeasureTheory.Integral.IntegrableOn
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.MeasureTheory.Group.Arithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelBoundary

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
section
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Replace only matrices violating the source ellipticity bounds. -/
def borelEllipticRepresentative {d : ℕ} (lam Lam : ℝ) (A : CoefficientField d) :
    CoefficientField d := by
  classical
  exact fun t v => if lam • (1 : PDE.Mat d) ≤ A t v ∧ A t v ≤ Lam • (1 : PDE.Mat d)
  then A t v else lam • (1 : PDE.Mat d)


/-- The matrix bridge uses precisely the inherited finite-product supremum norm. -/
@[instance_reducible] def borelMatrixContinuousENorm {d : ℕ} :
    ContinuousENorm (PDE.Mat d) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))

attribute [local instance] borelMatrixContinuousENorm

/-- Global ellipticity provides the local integrability required for convolution. -/
theorem borel_coefficient_locallyIntegrable {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    LocallyIntegrable (coefficientAt A) volume := by
  let : ContinuousENorm (PDE.Mat d) :=
    inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))
  let : TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  change Measurable (coefficientAt A) at hBorel
  have hLam0 := (hlam.le.trans hLam)
  apply (locallyIntegrable_const Lam).mono hBorel.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_of_nonneg hLam0,Matrix.norm_le_iff hLam0]
  intro i j
  exact HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hlo z.1 z.2) (hhi z.1 z.2) i j

end
section
open MeasureTheory Filter Set ContinuousLinearMap
open scoped MatrixOrder Matrix.Norms.Elementwise Convolution Topology

attribute [local instance] borelMatrixContinuousENorm

private instance {d : ℕ} : CompleteSpace (PDE.Mat d) :=
  inferInstanceAs (CompleteSpace (Fin d → Fin d → ℝ))

/-- Normalised convolution acts only in the time and velocity variables. -/
def borelSmoothCoefficient {d : ℕ} (φ : ContDiffBump (0 : ℝ × PDE.Vec d))
    (A : CoefficientField d) : CoefficientField d := fun t v =>
  (φ.normed volume ⋆[lsmul ℝ ℝ,volume] coefficientAt A) (t,v)

/-- Convolution preserves the exact source bounds while making the coefficient smooth. -/
theorem borelSmoothCoefficient_spec {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (φ : ContDiffBump (0 : ℝ × PDE.Vec d)) :
    IsSmoothCoefficient (borelSmoothCoefficient φ A) ∧
    IsSymmetricCoefficient (borelSmoothCoefficient φ A) ∧
    HasLowerEllipticity lam (borelSmoothCoefficient φ A) ∧
    HasUpperEllipticity Lam (borelSmoothCoefficient φ A) := by
  let : TopologicalSpace (PDE.Mat d) :=
    let M := Matrix.normedAddCommGroup (m := Fin d) (n := Fin d) (α := ℝ)
    M.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : ContinuousENorm (PDE.Mat d) :=
    let M := Matrix.normedAddCommGroup (m := Fin d) (n := Fin d) (α := ℝ)
    M.toSeminormedAddCommGroup.toSeminormedAddGroup.toContinuousENorm
  have : (volume : Measure (ℝ × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have : IsOrderedModule ℝ (PDE.Mat d) :=
    IsOrderedModule.of_smul_nonneg fun a ha M hM =>
      Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp hM).smul ha)
  have : ClosedIciTopology (PDE.Mat d) := ⟨fun M =>
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)⟩
  have hloc := borel_coefficient_locallyIntegrable hlam hLam A hBorel hlo hhi
  have hbounds (z : ℝ × PDE.Vec d) :
      lam • 1 ≤ coefficientAt (borelSmoothCoefficient φ A) z ∧
      coefficientAt (borelSmoothCoefficient φ A) z ≤ Lam • 1 := by
    have hgi := φ.hasCompactSupport_normed.convolutionExists_left
      (μ := volume) (lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc z
    have hli := (φ.integrable_normed (μ := volume)).smul_const (lam • (1 : PDE.Mat d))
    have hui := (φ.integrable_normed (μ := volume)).smul_const (Lam • (1 : PDE.Mat d))
    have hl := integral_mono (E := PDE.Mat d) hli hgi fun y =>
      smul_le_smul_of_nonneg_left (hlo (z - y).1 (z - y).2) (φ.nonneg_normed y)
    have hh := integral_mono (E := PDE.Mat d) hgi hui fun y =>
      smul_le_smul_of_nonneg_left (hhi (z - y).1 (z - y).2) (φ.nonneg_normed y)
    simpa [integral_smul_const, φ.integral_normed, coefficientAt, borelSmoothCoefficient, convolution, lsmul_apply] using And.intro hl hh
  refine ⟨?_,?_,fun t v => (hbounds (t,v)).1,fun t v => (hbounds (t,v)).2⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hloc
  · intro t v
    exact Matrix.isHermitian_iff_isSymm.mp
      (HypoellipticAleksandrov.posDef_of_loewner_lower hlam (hbounds (t,v)).1).isHermitian

/-- The shrinking bumps have a fixed ratio of outer and inner radii. -/
def borelCoefficientBump (d j : ℕ) : ContDiffBump (0 : ℝ × PDE.Vec d) :=
  ⟨(1 / ((j : ℝ) + 1)) / 2,1 / ((j : ℝ) + 1),by positivity,
    half_lt_self (by positivity)⟩

/-- Smooth, uniformly elliptic approximation exists with a.e. time--velocity convergence. -/
theorem borel_coefficient_approximation {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A) (hsymm : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    ∃ C : ℕ → CoefficientField d,
      (∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
        HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j)) ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
        Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z))  := by
  have borelEllipticRepresentative_spec (_hlam : 0 < lam) :
      IsBorelCoefficient (borelEllipticRepresentative lam Lam A) ∧
    IsSymmetricCoefficient (borelEllipticRepresentative lam Lam A) ∧
    HasLowerEllipticity lam (borelEllipticRepresentative lam Lam A) ∧
    HasUpperEllipticity Lam (borelEllipticRepresentative lam Lam A) ∧
    coefficientAt (borelEllipticRepresentative lam Lam A) =ᵐ[volume] coefficientAt A := by
    classical
    let : SecondCountableTopology (PDE.Mat d) :=
      inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
    change Measurable (coefficientAt A) at hBorel
    have hscalar : lam • 1 ≤ Lam • (1 : PDE.Mat d) := by
      rw [Matrix.le_iff,← sub_smul]
      exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hLam)
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact hBorel.ite
        ((measurableSet_le measurable_const hBorel).inter
          (measurableSet_le hBorel measurable_const)) measurable_const
    · intro t v
      unfold borelEllipticRepresentative
      split_ifs
      · exact hsymm t v
      · exact Matrix.isSymm_one.smul lam
    · intro t v
      unfold borelEllipticRepresentative
      split_ifs with h
      · exact h.1
      · exact le_rfl
    · intro t v
      unfold borelEllipticRepresentative
      split_ifs with h
      · exact h.2
      · exact hscalar
    · filter_upwards [hlo,hhi] with z hl hh
      exact ite_eq_left ⟨hl,hh⟩
  have : (volume : Measure (ℝ × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let B := borelEllipticRepresentative lam Lam A
  obtain ⟨hB,_,hBl,hBu,hBA⟩ :=
    borelEllipticRepresentative_spec hlam
  refine ⟨(fun j => borelSmoothCoefficient (borelCoefficientBump d j) B),fun j => borelSmoothCoefficient_spec hlam hLam B hB hBl hBu _,?_⟩
  have hr : Tendsto (fun j => (borelCoefficientBump d j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ j in atTop,
      (borelCoefficientBump d j).rOut ≤ 2 * (borelCoefficientBump d j).rIn := by
    filter_upwards with j
    dsimp only [borelCoefficientBump]
    linarith
  filter_upwards [(ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hratio (borel_coefficient_locallyIntegrable hlam hLam B hB hBl hBu)),hBA] with z hz heq
  rw [heq] at hz
  convert! hz using 1

end
section
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Every column has Euclidean norm at most the upper ellipticity constant. -/
theorem borel_matrix_column_sq_sum_le {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d))
    (j : Fin d) : ∑ i, (A i j) ^ 2 ≤ Lam ^ 2 := by
  classical
  have hpos := (HypoellipticAleksandrov.posDef_of_loewner_lower hlam hlo).posSemidef
  have hgap := Matrix.le_iff.mp hhi
  have hcomm : Commute A (Lam • 1 - A) := by
    unfold Commute SemiconjBy
    simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,Matrix.one_mul]
  have hd := (Matrix.nonneg_iff_posSemidef.mp (hcomm.mul_nonneg hpos.nonneg hgap.nonneg)).diag_nonneg (i := j)
  have hjj := hgap.diag_nonneg (i := j)
  have he : ∑ i, A j i * A i j = ∑ i, (A i j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian).apply j i,pow_two]
  have heprod : A * (Lam • 1 - A) = Lam • A - A * A := by
    rw [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one]
  rw [heprod] at hd
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, he] at hd
  simp at hjj
  nlinarith only [hd,hjj,(hlam.le.trans hLam)]

end
section
open scoped MatrixOrder Matrix.Norms.Frobenius

/-- Mathlib's Frobenius norm, named to make the Euclidean normalization explicit. -/
def borelFrobeniusNorm {d : ℕ} (M : PDE.Mat d) : ℝ := ‖M‖

/-- The Frobenius norm is the square root of the sum of squared entries. -/
theorem borelFrobeniusNorm_eq {d : ℕ} (M : PDE.Mat d) :
    borelFrobeniusNorm M = Real.sqrt (∑ i, ∑ j, (M i j) ^ 2) := by
  simp [borelFrobeniusNorm, Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow]

/-- The sharp ellipticity-to-Frobenius bound has the source factor sqrt d. -/
theorem borel_frobenius_norm_le {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d)) :
    borelFrobeniusNorm A ≤ Real.sqrt d * Lam := by
  have hs : (∑ i, ∑ j, (A i j) ^ 2) ≤ (d : ℝ) * Lam ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j : Fin d, Lam ^ 2 := Finset.sum_le_sum fun j _ =>
        borel_matrix_column_sq_sum_le hlam hLam hlo hhi j
      _ = _ := by simp
  rw [borelFrobeniusNorm_eq]
  have hnon : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg (∑ i, ∑ j, (A i j) ^ 2)) (mul_nonneg (Real.sqrt_nonneg (d : ℝ)) (hlam.le.trans hLam))).mp
  calc
    _ = _ := (Real.sq_sqrt hnon)
    _ ≤ _ := hs
    _ = _ := by rw [mul_pow,(Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d))]

/-- Finite-dimensional Cauchy--Schwarz for the literal entrywise contraction. -/
theorem borel_matrix_contraction_le {d : ℕ} (M H : PDE.Mat d) :
    |matrixContraction M H| ≤ borelFrobeniusNorm M * borelFrobeniusNorm H := by
  have hplus := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun ij : Fin d × Fin d => M ij.1 ij.2) (fun ij => H ij.1 ij.2)
  have hminus := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun ij : Fin d × Fin d => -M ij.1 ij.2) (fun ij => H ij.1 ij.2)
  simp only [Fintype.sum_prod_type,neg_mul,Finset.sum_neg_distrib,neg_sq] at hplus hminus
  rw [borelFrobeniusNorm_eq,borelFrobeniusNorm_eq,abs_le]
  exact ⟨neg_le.mp hminus,hplus⟩

/-- The source error domination retains exactly 2 sqrt d times the upper bound. -/
theorem borel_coefficient_error_bound {d : ℕ} {lam Lam : ℝ} {A C : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hAl : lam • (1 : PDE.Mat d) ≤ A) (hAu : A ≤ Lam • (1 : PDE.Mat d))
    (hCl : lam • (1 : PDE.Mat d) ≤ C) (hCu : C ≤ Lam • (1 : PDE.Mat d))
    (H : PDE.Mat d) :
    |matrixContraction (C - A) H| ≤ 2 * Real.sqrt d * Lam * borelFrobeniusNorm H := by
  have hnorm : borelFrobeniusNorm (C - A) ≤ 2 * Real.sqrt d * Lam := by
    have ht := norm_sub_le C A
    change borelFrobeniusNorm (C - A) ≤ borelFrobeniusNorm C + borelFrobeniusNorm A at ht
    linarith only [(borel_frobenius_norm_le hlam hLam hAl hAu),(borel_frobenius_norm_le hlam hLam hCl hCu),ht]
  exact (borel_matrix_contraction_le (C - A) H).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg H))

end
section
open MeasureTheory Filter Set
open scoped MatrixOrder Matrix.Norms.Elementwise Topology

/-- The coefficient defect is the absolute literal Hessian contraction. -/
def borelCoefficientError {d : ℕ} (C A : CoefficientField d)
    (H : KineticPoint d → PDE.Mat d) (P : KineticPoint d) : ℝ :=
  |matrixContraction (C P.time P.velocity - A P.time P.velocity) (H P)|

/-- On each fixed compact set the classical coefficient error vanishes in Lp. -/
theorem borel_inner_error {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (C : ℕ → CoefficientField d)
    (hC : ∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
      HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j))
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
      Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z)))
    (K : Set (KineticPoint d)) (hK : IsCompact K)
    (H : KineticPoint d → PDE.Mat d) (hH : ContinuousOn H K) {p : ℝ} (hp : 0 < p) :
    (∀ j, ∀ᵐ P ∂(volume.restrict K), borelCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * borelFrobeniusNorm (H P)) ∧
    (∀ j, MemLp (borelCoefficientError (C j) A H) (ENNReal.ofReal p)
      (volume.restrict K)) ∧
    Tendsto (fun j => (eLpNorm (borelCoefficientError (C j) A H)
      (ENNReal.ofReal p) (volume.restrict K)).toReal) atTop (𝓝 0) := by
  let : IsFiniteMeasureOnCompacts (volume : Measure (KineticPoint d)) :=
    Measure.IsFiniteMeasureOnCompacts.map
      (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))
      (KineticPoint.homeomorphProd d).symm
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  let : TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let : BorelSpace (PDE.Mat d) :=
    inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  change Measurable (coefficientAt A) at hBorel
  have hproj :=
    ((continuous_time (d := d)).prodMk (continuous_velocity (d := d))).measurable
  have hAm : AEStronglyMeasurable
      (fun P => A P.time P.velocity) (volume.restrict K) :=
    (hBorel.comp hproj).aestronglyMeasurable.restrict
  have hHm : AEStronglyMeasurable H (volume.restrict K) := hH.aestronglyMeasurable hK.measurableSet
  have hcontr : Continuous (fun z : PDE.Mat d × PDE.Mat d =>
      matrixContraction z.1 z.2) :=
    continuousOn_univ.mp (continuousOn_matrixContraction
      continuous_fst.continuousOn continuous_snd.continuousOn)
  have hm j : AEStronglyMeasurable (borelCoefficientError (C j) A H)
      (volume.restrict K) := by
    have hCs : Continuous (coefficientAt (C j)) := by
      exact (hC j).1.continuous
    have hCm : AEStronglyMeasurable
        (fun P => C j P.time P.velocity) (volume.restrict K) :=
      (hCs.measurable.comp hproj).aestronglyMeasurable.restrict
    have he i k : Continuous (fun M : PDE.Mat d => M i k) :=
      (continuous_apply k).comp (continuous_apply i)
    have hsum : AEStronglyMeasurable (fun P =>
        matrixContraction (C j P.time P.velocity - A P.time P.velocity) (H P))
        (volume.restrict K) := by
      unfold matrixContraction
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (((he i k).comp_aestronglyMeasurable hCm).sub
            ((he i k).comp_aestronglyMeasurable hAm)).mul
            ((he i k).comp_aestronglyMeasurable hHm)
    exact (continuous_abs : Continuous (abs : ℝ → ℝ)).comp_aestronglyMeasurable hsum
  have hbounds j : ∀ᵐ P ∂(volume.restrict K), borelCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * borelFrobeniusNorm (H P) := by
    filter_upwards [ae_restrict_of_ae (borel_timeVelocity_ae_lift hlo),
      ae_restrict_of_ae (borel_timeVelocity_ae_lift hhi)] with P hl hh
    exact borel_coefficient_error_bound hlam hLam hl hh
      ((hC j).2.2.1 P.time P.velocity) ((hC j).2.2.2 P.time P.velocity) (H P)
  have hFN : ContinuousOn (fun P => borelFrobeniusNorm (H P)) K := by
    have ht := Real.continuous_sqrt.comp_continuousOn (continuousOn_matrixContraction hH hH)
    convert ht using 1
    funext P
    simp only [borelFrobeniusNorm_eq,matrixContraction,pow_two,Function.comp_def]
  obtain ⟨B,hB⟩ := hK.bddAbove_image hFN
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hHM P (hP : P ∈ K) : borelFrobeniusNorm (H P) ≤ M :=
    (hB (mem_image_of_mem _ hP)).trans (le_max_left _ _)
  have hLam0 := hlam.le.trans hLam
  have hbound j : ∀ᵐ P ∂(volume.restrict K), borelCoefficientError (C j) A H P ≤
      2 * Real.sqrt d * Lam * M := by
    filter_upwards [hbounds j,ae_restrict_mem hK.measurableSet] with P hb hP
    exact hb.trans (mul_le_mul_of_nonneg_left (hHM P hP) (by positivity))
  have heconv : ∀ᵐ P ∂(volume.restrict K),
      Tendsto (fun j => borelCoefficientError (C j) A H P) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (borel_timeVelocity_ae_lift hc)] with P hP
    have ht' := (hcontr.continuousAt.tendsto.comp ((hP.sub_const (A P.time P.velocity)).prodMk_nhds (tendsto_const_nhds (x := H P)))).abs
    simpa [coefficientAt, matrixContraction, Matrix.zero_apply, Function.comp_def, borelCoefficientError] using ht'
  refine ⟨hbounds,?_,borel_bounded_error_norm_tendsto (volume.restrict K) hp (by positivity)
    (fun j => borelCoefficientError (C j) A H) hm ?_ hbound heconv⟩
  · intro j
    apply (memLp_const (2 * Real.sqrt d * Lam * M)).of_le (hm j)
    filter_upwards [hbound j] with P hP
    simpa only [borelCoefficientError,Real.norm_eq_abs,abs_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt d * Lam * M)] using hP
  · exact fun j => Filter.Eventually.of_forall fun P => abs_nonneg _

end
section
open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology ENNReal

/-- The coefficient limit preserves the complete source estimate on a fixed inner cylinder. -/
theorem borel_smooth_inner_limit {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmooth : BorelSmoothEstimate (d := d) lam Lam p alpha C₀ localised)
    (A : CoefficientField d) (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (C : ℕ → CoefficientField d)
    (hC : ∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
      HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j))
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
      Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z)))
    {D : Set (KineticPoint d)} (u f : KineticPoint d → ℝ) (hreg : IsKineticC112On u D)
    (P₁ : KineticPoint d) (r : ℝ) (hr : 0 < r)
    (hK : IsCompact (closure (backwardCylinder P₁ r)))
    (hKD : closure (backwardCylinder P₁ r) ⊆ D) (hf : Measurable f)
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
  classical
  let Q := backwardCylinder P₁ r
  let K := closure Q
  let H := kineticVelocityHessian u
  have hH := hreg.continuousOn_kineticVelocityHessian.mono hKD
  let Hext := K.indicator H
  let e := fun j => borelCoefficientError (C j) A Hext
  have he0 j P : 0 ≤ e j P := abs_nonneg _
  have hQ := isOpen_backwardCylinder P₁ r hr
  have hQK : Q ⊆ K := subset_closure
  have hregQ := comparison_regular_mono hreg (hQK.trans hKD)
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let : BorelSpace (PDE.Mat d) := inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have hHext : Measurable Hext :=
    hH.measurable_piecewise continuousOn_const hK.measurableSet
  have hproj : Measurable (fun P : KineticPoint d => (P.time,P.velocity)) :=
    (continuous_time.prodMk continuous_velocity).measurable
  have hA : Measurable (fun P : KineticPoint d => A P.time P.velocity) := hBorel.comp hproj
  have hem j : Measurable (e j) := by
    have hCs : Continuous (coefficientAt (C j)) := (hC j).1.continuous
    have hs : Measurable (fun P : KineticPoint d =>
        matrixContraction (C j P.time P.velocity - A P.time P.velocity) (Hext P)) := by
      unfold matrixContraction
      exact Finset.measurable_fun_sum _ fun i _ =>
        Finset.measurable_fun_sum _ fun k _ =>
          (((hCs.measurable.comp hproj).eval.eval).sub hA.eval.eval).mul hHext.eval.eval
    exact continuous_abs.measurable.comp hs
  have heq j : e j =ᵐ[volume.restrict K] borelCoefficientError (C j) A H := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
    simp only [e,borelCoefficientError,Hext,indicator_of_mem hP]
  obtain ⟨_,hmraw,htraw⟩ := borel_inner_error hlam hLam A hBorel hlo hhi C hC hc K hK H hH
    (lt_of_lt_of_le zero_lt_one hp)
  have hmK j : MemLp (e j) (ENNReal.ofReal p) (volume.restrict K) :=
    (hmraw j).ae_eq (heq j).symm
  have hμ : volume.restrict Q ≤ volume.restrict K := Measure.restrict_mono_set volume hQK
  have hme j : MemLp (e j) (ENNReal.ofReal p) (volume.restrict Q) := (hmK j).mono_measure hμ
  have hte : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p)
      (volume.restrict Q)).toReal) atTop (𝓝 0) := by
    have htK : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p)
        (volume.restrict K)).toReal) atTop (𝓝 0) := by
      simpa only [eLpNorm_congr_ae (heq _)] using htraw
    apply squeeze_zero (fun j => ENNReal.toReal_nonneg) _ htK
    intro j
    exact ENNReal.toReal_mono (hmK j).eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  let G := fun j => borelSource localised u (f + e j)
  have hpert j : MemLp (fun P => max ((f + e j) P) 0) (ENNReal.ofReal p)
      (volume.restrict Q) := by
    apply (hLp.add (hme j)).of_le ((hf.add (hem j)).sup measurable_const).aestronglyMeasurable
    filter_upwards with P
    change ‖max (f P + e j P) 0‖ ≤ ‖max (f P) 0 + e j P‖
    simp only [Real.norm_of_nonneg (le_max_right _ _),
      Real.norm_of_nonneg (add_nonneg (le_max_right _ _) (he0 j P))]
    exact max_le (by linarith only [le_max_left (f P) 0])
      (add_nonneg (le_max_right (f P) 0) (he0 j P))
  have hGp j := borelSource_memLp hQ localised u (f + e j) hregQ.continuousOn (hpert j)
  have htG := borel_source_norm_tendsto hp (borelSource localised u f) G e (borelSource_memLp hQ localised u f hregQ.continuousOn hLp) hme
    (fun j => (hGp j).aestronglyMeasurable)
    (Filter.Eventually.of_forall (borelSource_nonneg localised u f))
    (fun j => Filter.Eventually.of_forall (borelSource_nonneg localised u (f + e j)))
    (fun j => Filter.Eventually.of_forall (he0 j))
    (fun j => Filter.Eventually.of_forall fun P => borelSource_error_le localised u f P (he0 j P))
    hte
  have hineq j : ∀ P ∈ K, u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) +
      C₀ * r ^ alpha * (eLpNorm (G j) (ENNReal.ofReal p) (volume.restrict Q)).toReal := by
    apply hsmooth (C j) (hC j).1 (hC j).2.1 (hC j).2.2.1 (hC j).2.2.2
      P₁ r hr u (f + e j) (hreg.continuousOn.mono hKD) hregQ (hf.add (hem j)) (hpert j)
    filter_upwards [hsub,ae_restrict_mem hQ.measurableSet] with P hsubP hP
    have heP : e j P = borelCoefficientError (C j) A H P := by
      simp only [e,borelCoefficientError,Hext,indicator_of_mem (hQK hP)]
    dsimp only [borelCoefficientError,H] at heP
    change backwardOperatorOfTimeVelocityCoefficient (C j) u P ≤ f P + e j P
    rw [heP]
    linarith only [(borel_backwardOperator_sub (C j) A u P),hsubP,(neg_le_abs (matrixContraction (C j P.time P.velocity - A P.time P.velocity) (H P)))]
  intro P hP
  exact ge_of_tendsto
    (tendsto_const_nhds.add (tendsto_const_nhds.mul htG))
    (Filter.Eventually.of_forall fun j => hineq j P hP)

end
open HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped MatrixOrder

/-- Source lemma Lemma 6.4, class (a), with C₀ fixed before all coefficient and solution data. -/
theorem kinetic_abp_smooth_to_borel {d : ℕ}
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmoothEstimate :
      ∀ A : CoefficientField d,
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
        ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
        ∀ u f : KineticPoint d → ℝ,
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        Measurable f → MemLp (fun P => max (f P) 0)
          (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
          sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C₀ * R ^ alpha * (eLpNorm (borelSource localised u f)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal)
    (A : CoefficientField d) (hBorel : IsBorelCoefficient A)
    (hsymm : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (u f : KineticPoint d → ℝ)
    (hcont : ContinuousOn u (closure (backwardCylinder P₀ R)))
    (hreg : IsKineticC112On u (backwardCylinder P₀ R))
    (hf : Measurable f) (hLp : MemLp (fun P => max (f P) 0)
      (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C,hC,hc⟩ := borel_coefficient_approximation lam Lam hlam hLam A hBorel hsymm hlo hhi
  apply borel_boundary_limit p hp alpha C₀ localised P₀ R hR u f hcont hLp
  intro n P hP
  have hk := isCompact_closure_reflected_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  have hKD := closure_reflected_innerCylinder_subset P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  rw [kineticReflection_image_innerCylinder] at hk hKD
  have hμ := Measure.restrict_mono_set volume (subset_closure.trans hKD)
  exact borel_smooth_inner_limit lam Lam hlam hLam p hp alpha C₀ localised hsmoothEstimate
    A hBorel hlo hhi C hC hc u f hreg (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
    (borelInnerRadius_pos R hR n) hk hKD hf (hLp.mono_measure hμ)
    (hsub.filter_mono (ae_mono hμ)) P hP

end HypoellipticAleksandrov.KineticAleksandrov

