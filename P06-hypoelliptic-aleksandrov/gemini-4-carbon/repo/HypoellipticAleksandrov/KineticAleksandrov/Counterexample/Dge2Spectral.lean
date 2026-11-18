module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
section
open Filter Topology
open scoped Matrix.Norms.L2Operator

/-- Indicator of the strictly positive spectral half-line. -/
def positiveSpectralIndicator (t : ℝ) : ℝ := if 0 < t then 1 else 0

/-- Continuous approximants to the positive spectral indicator. -/
def positiveSpectralRamp (n : ℕ) (t : ℝ) : ℝ := max 0 (min 1 ((n : ℝ) * t))

/-- The canonical strictly positive spectral projection. -/
def positiveSpectralProjection {d : ℕ} (M : PDE.Mat d) : PDE.Mat d :=
  cfc positiveSpectralIndicator M

/-- The canonical strictly negative spectral projection. -/
def negativeSpectralProjection {d : ℕ} (M : PDE.Mat d) : PDE.Mat d :=
  positiveSpectralProjection (-M)

/-- The canonical zero spectral projection. -/
def zeroSpectralProjection {d : ℕ} (M : PDE.Mat d) : PDE.Mat d :=
  1 - positiveSpectralProjection M - negativeSpectralProjection M


/-- At each scalar the ramps eventually equal the spectral indicator. -/
theorem positiveSpectralRamp_eventually (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, positiveSpectralRamp n t = positiveSpectralIndicator t := by
  by_cases ht : 0 < t
  · obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnN : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    have hnt := ((div_le_iff₀ ht).mp hN).trans (mul_le_mul_of_nonneg_right hnN ht.le)
    simp [positiveSpectralRamp, positiveSpectralIndicator, ht, min_eq_left hnt]
  · apply Eventually.of_forall
    intro n
    have hm : min 1 ((n : ℝ) * t) ≤ 0 := (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt ht))
    simp [positiveSpectralRamp, positiveSpectralIndicator, ht, max_eq_left hm]

/-- At a Hermitian matrix the ramp calculus eventually equals the positive projection. -/
theorem spectralRamp_eventually {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    ∀ᶠ n : ℕ in atTop, cfc (positiveSpectralRamp n) M = positiveSpectralProjection M := by
  filter_upwards [(eventually_all.mpr fun i => positiveSpectralRamp_eventually (hM.eigenvalues i))] with n hn
  apply cfc_congr
  intro t ht
  rw [hM.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hn i

/-- Continuous matrix fields have continuous ramp functional calculi. -/
theorem continuous_spectralRamp {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian)
    (n : ℕ) : Continuous (fun x => cfc (positiveSpectralRamp n) (M x))  := by
  have continuous_positiveSpectralRamp :
      Continuous (positiveSpectralRamp n) := by
    unfold positiveSpectralRamp
    fun_prop
  apply Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (positiveSpectralRamp n)
    (by simp) hM hherm (continuous_positiveSpectralRamp).continuousOn

end
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Positive spectral part of a real matrix. -/
def positiveSpectralPart {d : ℕ} (M : PDE.Mat d) : PDE.Mat d := cfc (max (0 : ℝ)) M

/-- Sum of the positive eigenvalues. -/
def positiveSpectralMass {d : ℕ} (M : PDE.Mat d) : ℝ := (positiveSpectralPart M).trace

/-- Sum of the absolute values of the negative eigenvalues. -/
def negativeSpectralMass {d : ℕ} (M : PDE.Mat d) : ℝ := positiveSpectralMass (-M)

/-- The source's canonical weighted spectral matrix. -/
def spectralTraceMatrix {d : ℕ} (M : PDE.Mat d) (b cminus : ℝ) : PDE.Mat d :=
  ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) •
      positiveSpectralProjection M +
    cminus • negativeSpectralProjection M + zeroSpectralProjection M

private theorem continuousOn_matrix_spectrum {d : ℕ} (M : PDE.Mat d) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop


/-- The positive projection has contraction equal to the positive spectral mass. -/
theorem contraction_positiveSpectralProjection {d : ℕ}
    (M : PDE.Mat d) (hM : M.IsHermitian) :
    matrixContraction (positiveSpectralProjection M) M = positiveSpectralMass M  := by
  have positiveSpectralProjection_mul :
      positiveSpectralProjection M * M = positiveSpectralPart M := by
    unfold positiveSpectralProjection positiveSpectralPart
    conv_lhs => rhs; rw [← cfc_id ℝ M hM.isSelfAdjoint]
    rw [← cfc_mul positiveSpectralIndicator (id : ℝ → ℝ) M
      (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
    apply cfc_congr
    intro t _
    by_cases ht : 0 < t
    · simp [positiveSpectralIndicator, ht, max_eq_right ht.le]
    · simp [positiveSpectralIndicator, ht, max_eq_left (le_of_not_gt ht)]
  rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hM.isSymm,
    positiveSpectralProjection_mul]
  rfl





/-- The literal source matrix solves the exact trace equation when the positive mass is nonzero. -/
theorem spectral_trace_solver {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus : ℝ) (hm : positiveSpectralMass M ≠ 0) :
    matrixContraction (spectralTraceMatrix M b cminus) M = b   := by
  have contraction_negativeSpectralProjection :
      matrixContraction (negativeSpectralProjection M) M = -negativeSpectralMass M := by
    have hh := contraction_positiveSpectralProjection (-M) hM.neg
    change matrixContraction (positiveSpectralProjection (-M)) M =
      -positiveSpectralMass (-M)
    rw [matrixContraction_neg_right] at hh
    linarith
  have contraction_zeroSpectralProjection :
      matrixContraction (zeroSpectralProjection M) M = 0 := by
    have trace_eq_spectralMass_sub :
        M.trace = positiveSpectralMass M - negativeSpectralMass M := by
      have spectralParts_sub :
          positiveSpectralPart M - positiveSpectralPart (-M) = M := by
        unfold positiveSpectralPart
        rw [← cfc_comp_neg (max 0) M
          (by fun_prop) hM.isSelfAdjoint,
          ← cfc_sub (max 0) (fun t => max 0 (-t)) M
            (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
        conv_rhs => rw [← cfc_id ℝ M hM.isSelfAdjoint]
        apply cfc_congr
        intro t _
        dsimp
        by_cases ht : 0 ≤ t
        · rw [max_eq_right ht, max_eq_left (neg_nonpos.mpr ht)]
          ring
        · have htn : t ≤ 0 := le_of_not_ge ht
          rw [max_eq_left htn, max_eq_right (neg_nonneg.mpr htn)]
          ring
      simpa only [Matrix.trace_sub, positiveSpectralMass, negativeSpectralMass] using (congrArg Matrix.trace (spectralParts_sub)).symm
    unfold zeroSpectralProjection
    have hsub (A B : PDE.Mat d) : matrixContraction (A - B) M =
        matrixContraction A M - matrixContraction B M := by
      rw [sub_eq_add_neg, matrixContraction_add_left, matrixContraction_neg_left,
        sub_eq_add_neg]
    rw [hsub, hsub, contraction_positiveSpectralProjection M hM,
      contraction_negativeSpectralProjection,
      matrixContraction_eq_trace_mul_of_isSymm _ _ hM.isSymm, one_mul,
      trace_eq_spectralMass_sub]
    ring
  unfold spectralTraceMatrix
  rw [matrixContraction_add_left, matrixContraction_add_left,
    matrixContraction_smul_left, matrixContraction_smul_left,
    contraction_positiveSpectralProjection M hM,
    contraction_negativeSpectralProjection, contraction_zeroSpectralProjection]
  field_simp
  ring

/-- Scalar eigenvalue of the trace solver in each of the three spectral regions. -/
def weightedSpectralSelector (w cminus t : ℝ) : ℝ :=
  if 0 < t then w else if t < 0 then cminus else 1


/-- Functional-calculus expression for the literal weighted matrix. -/
theorem spectralTraceMatrix_eq_cfc {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus : ℝ) :
    spectralTraceMatrix M b cminus =
      cfc (weightedSpectralSelector
        ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus) M  := by
  have negativeSpectralProjection_eq :
      negativeSpectralProjection M = cfc (fun t => positiveSpectralIndicator (-t)) M := by
    unfold negativeSpectralProjection positiveSpectralProjection
    symm
    exact cfc_comp_neg positiveSpectralIndicator M
      (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop) hM.isSelfAdjoint
  let w := (b + cminus * negativeSpectralMass M) / positiveSpectralMass M
  have hs : cfc (weightedSpectralSelector w cminus) M =
      cfc (fun t => w * positiveSpectralIndicator t +
        cminus * positiveSpectralIndicator (-t) +
        (1 - positiveSpectralIndicator t - positiveSpectralIndicator (-t))) M := by
    apply cfc_congr
    intro t _
    by_cases ht : 0 < t
    · simp [weightedSpectralSelector, positiveSpectralIndicator, ht, not_lt.mpr ht.le]
    · by_cases hn : t < 0
      · simp [weightedSpectralSelector, positiveSpectralIndicator, ht, hn]
      · simp [weightedSpectralSelector, positiveSpectralIndicator, ht, hn]
  rw [hs]
  rw [cfc_add M
    (fun t => w * positiveSpectralIndicator t + cminus * positiveSpectralIndicator (-t))
    (fun t => 1 - positiveSpectralIndicator t - positiveSpectralIndicator (-t))
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  rw [cfc_add M (fun t => w * positiveSpectralIndicator t)
    (fun t => cminus * positiveSpectralIndicator (-t))
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  rw [cfc_const_mul w positiveSpectralIndicator M
    (continuousOn_matrix_spectrum M _),
    cfc_const_mul cminus (fun t => positiveSpectralIndicator (-t)) M
    (continuousOn_matrix_spectrum M _)]
  rw [cfc_sub (fun t => 1 - positiveSpectralIndicator t)
    (fun t => positiveSpectralIndicator (-t)) M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _),
    cfc_sub (fun _ => 1) positiveSpectralIndicator M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _),
    cfc_const 1 M hM.isSelfAdjoint]
  simp
  rw [← negativeSpectralProjection_eq]
  rfl

/-- The positive spectral mass of a continuous Hermitian field is continuous. -/
theorem continuous_positiveSpectralMass {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian) :
    Continuous (fun x => positiveSpectralMass (M x)) := by
  exact (Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (max (0 : ℝ)) (by simp) hM (fun x => (hherm x).isSelfAdjoint) (by fun_prop)).matrix_trace

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

