module

public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
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

section
variable {d : Nat} (c : Real) {lam : Real} {Lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) (hUpper : M ≤ Lam • (1 : PDE.Mat d)) (x : PDE.Vec d)

include hLower in
private theorem quadratic_lower_of_loewner :
    lam * PDE.vecNormSq x ≤ PDE.vecDot x (Matrix.mulVec M x) := by
  have hquad := (Matrix.le_iff.mp hLower).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  exact sub_nonneg.mp hquad

include hUpper in
private theorem quadratic_upper_of_loewner :
    PDE.vecDot x (Matrix.mulVec M x) ≤ Lam * PDE.vecNormSq x := by
  have hquad := (Matrix.le_iff.mp hUpper).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  exact sub_nonneg.mp hquad

include hLower in
private theorem isSymm_of_lower_ellipticity : M.IsSymm := by
  have hgap := Matrix.le_iff.mp hLower
  apply Matrix.IsSymm.ext
  intro i j
  have hherm := hgap.isHermitian.apply i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji := Ne.symm hij
    simpa [hij, hji] using hherm

end

section
variable {d : Nat} (M : PDE.Mat d) (i j : Fin d)

private theorem sum_single_mul (i : Fin d) (f : Fin d → Real) :
    ∑ x : Fin d, (Pi.single i (1 : Real) : PDE.Vec d) x * f x = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · grind
  · simp

private theorem quadratic_single (i : Fin d) :
    PDE.vecDot (Pi.single i 1) (Matrix.mulVec M (Pi.single i 1)) = M i i := by
  simp only [PDE.vecDot, Matrix.mulVec_single_one]
  apply sum_single_mul

private theorem quadratic_single_add :
    PDE.vecDot (Pi.single i 1 + Pi.single j 1)
      (Matrix.mulVec M (Pi.single i 1 + Pi.single j 1)) =
        M i i + M i j + M j i + M j j := by
  simp only [PDE.vecDot, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib]
  rw [sum_single_mul i, sum_single_mul i, sum_single_mul j, sum_single_mul j]
  simp only [Matrix.col_apply]
  ring

private theorem vecNormSq_single_add_le_four :
    PDE.vecNormSq (Pi.single i 1 + Pi.single j 1) ≤ 4 := by
  by_cases hij : i = j
  · subst j
    simp [PDE.vecNormSq, PDE.vecDot, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib, sum_single_mul]
    norm_num
  · simp [PDE.vecNormSq, PDE.vecDot, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib, sum_single_mul, hij]
    norm_num

end

private theorem vecNormSq_single (i : Fin d) : PDE.vecNormSq (Pi.single i 1) = 1 := by
  simp [PDE.vecNormSq, PDE.vecDot, sum_single_mul]

section
variable {d : Nat} {lam Lam : Real} {M : PDE.Mat d} {A : CoefficientField d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) (hA : IsBorelCoefficient A)
    (hUpper : M ≤ Lam • (1 : PDE.Mat d)) (i j : Fin d)

include hLower hUpper in
private theorem coefficient_entry_abs_le :
    |M i j| ≤ 3 * (|lam| + |Lam|) := by
  let q : PDE.Vec d := Pi.single i 1 + Pi.single j 1
  have hqnonneg := PDE.vecNormSq_nonneg q
  have hqle := vecNormSq_single_add_le_four i j
  have hquadLower' : -(4 * |lam|) ≤ PDE.vecDot q (Matrix.mulVec M q) := by
    have hlam := neg_abs_le lam
    have hfour : -(4 * |lam|) ≤ -|lam| * PDE.vecNormSq q := by
      nlinarith [mul_le_mul_of_nonneg_left hqle (abs_nonneg lam)]
    exact hfour.trans ((mul_le_mul_of_nonneg_right hlam hqnonneg).trans (quadratic_lower_of_loewner hLower q))
  have hquadUpper' : PDE.vecDot q (Matrix.mulVec M q) ≤ 4 * |Lam| := by
    have hLam := le_abs_self Lam
    have hfour : |Lam| * PDE.vecNormSq q ≤ 4 * |Lam| := by
      nlinarith [mul_le_mul_of_nonneg_left hqle (abs_nonneg Lam)]
    exact (quadratic_upper_of_loewner hUpper q).trans ((mul_le_mul_of_nonneg_right hLam hqnonneg).trans hfour)
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
    dsimp only [q]
    rw [quadratic_single_add, (isSymm_of_lower_ellipticity hLower).apply i j]
    ring
  rw [abs_le]
  constructor
  · rw [hquad] at hquadLower'
    nlinarith [hdiagUpper i, hdiagUpper j, abs_nonneg lam, abs_nonneg Lam]
  · rw [hquad] at hquadUpper'
    nlinarith [hdiagLower i, hdiagLower j, abs_nonneg lam, abs_nonneg Lam]

include hLower hUpper in
/-- An entry of a matrix between scalar lower and upper ellipticity bounds is
bounded by the corresponding absolute scalar bounds. -/
theorem coefficient_entry_abs_le_of_ellipticity :
    |M i j| ≤ 3 * (|lam| + |Lam|) :=
  coefficient_entry_abs_le hLower hUpper i j

end

section
variable (d : Nat) (lam Lam : Real) (A : CoefficientField d) (Abar : CoefficientField d)
    (hA : IsBorelCoefficient A) (hSymm : IsSymmetricCoefficient A) (U : Set (TimeVelocity d))
    (hLower : HasLowerEllipticity lam A) (hAbarSymm : ∀ z ∈ U, (coefficientAt Abar z).IsSymm)
    (hUpper : HasUpperEllipticity Lam A)
    (hAbarLower : ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt Abar z) (n : Nat)
    (hAbarUpper : ∀ z ∈ U, coefficientAt Abar z ≤ Lam • (1 : PDE.Mat d)) (hLam : lam ≤ Lam)

end

section
variable {d : Nat} {lam Lam : Real} (f : TimeVelocity d → Real) {A : CoefficientField d}
    (hA : IsBorelCoefficient A) (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat)

end

section
variable (d : Nat) (lam Lam : Real) (A : CoefficientField d) (hA : IsBorelCoefficient A)
    (hSymm : IsSymmetricCoefficient A) (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat)
include hA hSymm hLower hUpper

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

end HypoellipticAleksandrov.Parabolic
