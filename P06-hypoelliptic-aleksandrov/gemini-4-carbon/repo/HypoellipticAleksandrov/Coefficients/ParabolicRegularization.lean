module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Parabolic regularization of coefficient fields

This module repairs local almost-everywhere ellipticity on a measurable null
set, extends the repair by the ellipticity midpoint, and regularizes the
result entrywise with the parabolic mollifier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal MatrixOrder Topology

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance matrixMeasurableSpace (d : Nat) : MeasurableSpace (PDE.Mat d) := by
  unfold PDE.Mat Matrix
  infer_instance

variable {d : Nat}




/-- The entrywise right convolution of a coefficient field with the
native-norm parabolic mollifier. -/
noncomputable def parabolicMollifyCoefficient
    (A : CoefficientField d) (n : Nat) : CoefficientField d :=
  fun t v i j => parabolicConvolution
    (fun z : TimeVelocity d => coefficientAt A z i j)
    (parabolicMollifier d n) (t, v)



/-- Evaluation of an entrywise parabolic coefficient mollification. -/
@[simp] theorem coefficientAt_parabolicMollifyCoefficient
    (A : CoefficientField d) (n : Nat) (z : TimeVelocity d) (i j : Fin d) :
    coefficientAt (parabolicMollifyCoefficient A n) z i j =
      parabolicConvolution (fun y : TimeVelocity d => coefficientAt A y i j)
        (parabolicMollifier d n) z :=
  rfl




private theorem quadratic_lower_of_loewner {d : Nat} {lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) (x : PDE.Vec d) :
    lam * PDE.vecNormSq x ≤ PDE.vecDot x (Matrix.mulVec M x) := by
  have hquad := (Matrix.le_iff.mp hLower).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad

private theorem quadratic_upper_of_loewner {d : Nat} {Lam : Real} {M : PDE.Mat d}
    (hUpper : M ≤ Lam • (1 : PDE.Mat d)) (x : PDE.Vec d) :
    PDE.vecDot x (Matrix.mulVec M x) ≤ Lam * PDE.vecNormSq x := by
  have hquad := (Matrix.le_iff.mp hUpper).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad


private theorem sum_single_mul {d : Nat} (i : Fin d) (f : Fin d → Real) :
    ∑ x : Fin d, (Pi.single i (1 : Real) : PDE.Vec d) x * f x = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _hb hbi
    simp [hbi]
  · simp


private theorem quadratic_single_add {d : Nat} (M : PDE.Mat d) (i j : Fin d) :
    PDE.vecDot (Pi.single i 1 + Pi.single j 1)
      (Matrix.mulVec M (Pi.single i 1 + Pi.single j 1)) =
        M i i + M i j + M j i + M j j := by
  simp only [PDE.vecDot, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib]
  rw [sum_single_mul i, sum_single_mul i, sum_single_mul j, sum_single_mul j]
  simp
  ring





/-- An entry of a matrix between scalar lower and upper ellipticity bounds is
bounded by the corresponding absolute scalar bounds. -/
theorem coefficient_entry_abs_le_of_ellipticity
    {d : Nat} {lam Lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M)
    (hUpper : M ≤ Lam • (1 : PDE.Mat d))
    (i j : Fin d) :
    |M i j| ≤ 3 * (|lam| + |Lam|)  := by
  have vecNormSq_single (i : Fin d) :
      PDE.vecNormSq (Pi.single i 1) = 1 := by
    simp [PDE.vecNormSq, PDE.vecDot, sum_single_mul]
  have vecNormSq_single_add_le_four :
      PDE.vecNormSq (Pi.single i 1 + Pi.single j 1) ≤ 4 := by
    by_cases hij : i = j
    · subst j
      simp [PDE.vecNormSq, PDE.vecDot, Pi.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib, sum_single_mul]
      norm_num
    · simp [PDE.vecNormSq, PDE.vecDot, Pi.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib, sum_single_mul, hij]
      norm_num
  have quadratic_single {d : Nat} (M : PDE.Mat d) (i : Fin d) :
      PDE.vecDot (Pi.single i 1) (Matrix.mulVec M (Pi.single i 1)) = M i i := by
    simp
    exact sum_single_mul i fun x => M x i
  have isSymm_of_lower_ellipticity :
      M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have hherm := (Matrix.le_iff.mp hLower).isHermitian.apply i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij, hji] using hherm
  let q : PDE.Vec d := Pi.single i 1 + Pi.single j 1
  have hqnonneg := PDE.vecNormSq_nonneg q
  have hqle := vecNormSq_single_add_le_four
  have hquadLower' : -(4 * |lam|) ≤ PDE.vecDot q (Matrix.mulVec M q) := by
    have hmul :=
      mul_le_mul_of_nonneg_right (neg_abs_le lam) hqnonneg
    have hfour : -(4 * |lam|) ≤ -|lam| * PDE.vecNormSq q := by
      have hmul' :=
        mul_le_mul_of_nonneg_left hqle (abs_nonneg lam)
      nlinarith
    exact hfour.trans (hmul.trans (quadratic_lower_of_loewner hLower q))
  have hquadUpper' : PDE.vecDot q (Matrix.mulVec M q) ≤ 4 * |Lam| := by
    have hmul :=
      mul_le_mul_of_nonneg_right (le_abs_self Lam) hqnonneg
    have hfour : |Lam| * PDE.vecNormSq q ≤ 4 * |Lam| := by
      have hmul' :=
        mul_le_mul_of_nonneg_left hqle (abs_nonneg Lam)
      nlinarith
    exact (quadratic_upper_of_loewner hUpper q).trans (hmul.trans hfour)
  have hdiagLower (k : Fin d) : -|lam| ≤ M k k := by
    have h := quadratic_lower_of_loewner hLower (Pi.single k 1)
    rw [quadratic_single, vecNormSq_single] at h
    have hk : lam ≤ M k k := by simpa using h
    exact (neg_abs_le lam).trans hk
  have hdiagUpper (k : Fin d) : M k k ≤ |Lam| := by
    have h := quadratic_upper_of_loewner hUpper (Pi.single k 1)
    rw [quadratic_single, vecNormSq_single] at h
    have hk : M k k ≤ Lam := by simpa using h
    exact hk.trans (le_abs_self Lam)
  have hquad : PDE.vecDot q (Matrix.mulVec M q) = M i i + 2 * M i j + M j j := by
    rw [quadratic_single_add, isSymm_of_lower_ellipticity.apply i j]
    ring
  rw [abs_le]
  constructor
  · rw [hquad] at hquadLower'
    have hsum : 0 ≤ |lam| + |Lam| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [hdiagUpper i, hdiagUpper j, abs_nonneg lam, abs_nonneg Lam]
  · rw [hquad] at hquadUpper'
    have hsum : 0 ≤ |lam| + |Lam| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [hdiagLower i, hdiagLower j, abs_nonneg lam, abs_nonneg Lam]













end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic


end HypoellipticAleksandrov.Parabolic
