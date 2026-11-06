module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SpectralMeasurable
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The canonical spectral trace solver of Appendix C

The positive and negative masses are traces of the actual matrix positive parts.
The trace equation is algebraic; uniform ellipticity requires the separate sign argument.
-/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Positive spectral part of a real matrix. -/
def positiveSpectralPart {d : ℕ} (M : PDE.Mat d) : PDE.Mat d := cfc (max (0 : ℝ)) M

variable {d : ℕ} (M : PDE.Mat d)

/-- Sum of the positive eigenvalues. -/
def positiveSpectralMass  : ℝ := (positiveSpectralPart M).trace

/-- Sum of the absolute values of the negative eigenvalues. -/
def negativeSpectralMass  : ℝ := positiveSpectralMass (-M)

/-- The source's canonical weighted spectral matrix. -/
def spectralTraceMatrix  (b cminus : ℝ) : PDE.Mat d :=
  ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) •
      positiveSpectralProjection M +
    cminus • negativeSpectralProjection M + zeroSpectralProjection M

private theorem continuousOn_matrix_spectrum  (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

section
variable (hM : M.IsHermitian)

include hM
/-- The positive projection times the original matrix is its positive part. -/
theorem positiveSpectralProjection_mul   :
    positiveSpectralProjection M * M = positiveSpectralPart M := by
  unfold positiveSpectralProjection positiveSpectralPart
  conv_lhs => rhs; rw [← cfc_id  ℝ M hM.isSelfAdjoint]
  rw [← cfc_mul  positiveSpectralIndicator (id ) M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  apply cfc_congr
  intro t _
  by_cases ht : 0 < t
  · simp [positiveSpectralIndicator, ht, max_eq_right ht.le]
  · simp_all [positiveSpectralIndicator]

/-- The positive projection has contraction equal to the positive spectral mass. -/
theorem contraction_positiveSpectralProjection   :
    matrixContraction (positiveSpectralProjection M) M = positiveSpectralMass M := by
  rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hM.isSymm,
    positiveSpectralProjection_mul M hM]
  rfl

/-- The negative projection has contraction equal to minus the negative spectral mass. -/
theorem contraction_negativeSpectralProjection   :
    matrixContraction (negativeSpectralProjection M) M = -negativeSpectralMass M := by
  have hh := contraction_positiveSpectralProjection (-M) hM.neg
  change matrixContraction (positiveSpectralProjection (-M)) M =
    -positiveSpectralMass (-M)
  rw [matrixContraction_neg_right] at hh
  linarith

/-- The difference of the spectral positive parts is the original Hermitian matrix. -/
theorem spectralParts_sub   :
    positiveSpectralPart M - positiveSpectralPart (-M) = M := by
  unfold positiveSpectralPart
  rw [← cfc_comp_neg (p := IsSelfAdjoint) (max (0 : ℝ)) M
    (by fun_prop) hM.isSelfAdjoint,
    ← cfc_sub  (max (0 : ℝ)) (fun t => max 0 (-t)) M
      (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  conv_rhs => rw [← cfc_id  ℝ M hM.isSelfAdjoint]
  apply cfc_congr
  intro t _
  dsimp
  by_cases ht : 0 ≤ t
  · rw [max_eq_right ht, max_eq_left (neg_nonpos.mpr ht)]
    ring
  · have htn  := le_of_not_ge ht
    rw [max_eq_left htn, max_eq_right (neg_nonneg.mpr htn)]
    ring

/-- The matrix trace is the positive spectral mass minus the negative spectral mass. -/
theorem trace_eq_spectralMass_sub   :
    M.trace = positiveSpectralMass M - negativeSpectralMass M := by

  simpa only [Matrix.trace_sub, positiveSpectralMass, negativeSpectralMass] using (congrArg Matrix.trace (spectralParts_sub M hM)).symm

/-- The zero projection has zero contraction with the original matrix. -/
theorem contraction_zeroSpectralProjection
     : matrixContraction (zeroSpectralProjection M) M = 0 := by
  unfold zeroSpectralProjection
  have hsub (A B : PDE.Mat d) : matrixContraction (A - B) M =
      matrixContraction A M - matrixContraction B M := by
    rw [sub_eq_add_neg, matrixContraction_add_left, matrixContraction_neg_left,
      sub_eq_add_neg]
  rw [hsub, hsub, contraction_positiveSpectralProjection M hM,
    contraction_negativeSpectralProjection M hM,
    matrixContraction_eq_trace_mul_of_isSymm _ _ hM.isSymm, one_mul,
    trace_eq_spectralMass_sub M hM]
  ring

/-- The literal source matrix solves the exact trace equation when the positive mass is nonzero. -/
theorem spectral_trace_solver
    (b cminus : ℝ) (hm : positiveSpectralMass M ≠ 0) :
    matrixContraction (spectralTraceMatrix M b cminus) M = b := by
  simp_all [spectralTraceMatrix, contraction_positiveSpectralProjection, contraction_negativeSpectralProjection, contraction_zeroSpectralProjection]
end


/-- Scalar eigenvalue of the trace solver in each of the three spectral regions. -/
def weightedSpectralSelector (w cminus t : ℝ) : ℝ :=
  if 0 < t then w else if t < 0 then cminus else 1

section
variable {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)

include hM
/-- The negative projection is the functional calculus of the negative spectral indicator. -/
theorem negativeSpectralProjection_eq  :
    negativeSpectralProjection M = cfc (fun t => positiveSpectralIndicator (-t)) M := by
  unfold negativeSpectralProjection positiveSpectralProjection
  symm
  exact cfc_comp_neg (p := IsSelfAdjoint) positiveSpectralIndicator M
    (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop) hM.isSelfAdjoint

/-- Functional-calculus expression for the literal weighted matrix. -/
theorem spectralTraceMatrix_eq_cfc
    (b cminus : ℝ) :
    spectralTraceMatrix M b cminus =
      cfc (weightedSpectralSelector
        ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus) M := by
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
  rw [cfc_add (p := IsSelfAdjoint) M
    (fun t => w * positiveSpectralIndicator t + cminus * positiveSpectralIndicator (-t))
    (fun t => 1 - positiveSpectralIndicator t - positiveSpectralIndicator (-t))
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  rw [cfc_add  M (fun t => w * positiveSpectralIndicator t)
    (fun t => cminus * positiveSpectralIndicator (-t))
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  rw [cfc_const_mul  w positiveSpectralIndicator M
    (continuousOn_matrix_spectrum M _),
    cfc_const_mul  cminus (fun t => positiveSpectralIndicator (-t)) M
    (continuousOn_matrix_spectrum M _)]
  rw [cfc_sub  (fun t => 1 - positiveSpectralIndicator t)
    (fun t => positiveSpectralIndicator (-t)) M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _),
    cfc_sub  (fun _ : ℝ => 1) positiveSpectralIndicator M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _),
    cfc_const (p := IsSelfAdjoint) 1 M hM.isSelfAdjoint]
  simp only [map_one]
  rw [← negativeSpectralProjection_eq M hM]
  rfl
end


/-- The positive spectral mass of a continuous Hermitian field is continuous. -/
theorem continuous_positiveSpectralMass {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian) :
    Continuous (fun x => positiveSpectralMass (M x)) := by
  have hh : Continuous (fun x => cfc (max (0 : ℝ)) (M x)) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (max (0 : ℝ))
      (by simp) hM (fun x => (hherm x).isSelfAdjoint) (by fun_prop)
  exact hh.matrix_trace

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
