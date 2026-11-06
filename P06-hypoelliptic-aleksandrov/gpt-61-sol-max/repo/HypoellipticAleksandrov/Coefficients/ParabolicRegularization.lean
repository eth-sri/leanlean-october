module

public import HypoellipticAleksandrov.Parabolic.WeakEquation
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Coefficients.Ellipticity
import PDEFoundation.Ambient.Basis
import all HypoellipticAleksandrov.Coefficients.Ellipticity
import all HypoellipticAleksandrov.LinearAlgebra.LoewnerPolarization
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.vecDot_mulVec_upper_of_loewner from HypoellipticAleksandrov.LinearAlgebra.LoewnerPolarization
open private HypoellipticAleksandrov.matrix_isSymm_of_loewner_lower from HypoellipticAleksandrov.LinearAlgebra.LoewnerPolarization
open private HypoellipticAleksandrov.isHermitian_of_isSymm from HypoellipticAleksandrov.Coefficients.Ellipticity


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

/-- The scalar midpoint of the lower and upper ellipticity bounds, times the
identity matrix. -/
def ellipticityMidpoint (d : Nat) (lam Lam : Real) : PDE.Mat d :=
  ((lam + Lam) / 2) • (1 : PDE.Mat d)

section
variable (A : CoefficientField d)



/-- A coefficient field extended by a fixed matrix outside a prescribed set. -/
def extendCoefficientByMidpoint
     (U : HypoellipticAleksandrov.Parabolic.Region d) (M : PDE.Mat d) :
    CoefficientField d := (fun t v => if (t, v) ∈ U then A t v else M)

/-- The entrywise right convolution of a coefficient field with the
native-norm parabolic mollifier. -/
def parabolicMollifyCoefficient
     (n : Nat) : CoefficientField d :=
  fun t v i j => parabolicConvolution
    (fun z : TimeVelocity d => coefficientAt A z i j)
    (parabolicMollifier d n) (t, v)



/-- Evaluation of a midpoint extension. -/
@[simp] theorem coefficientAt_extendCoefficientByMidpoint
     (U : HypoellipticAleksandrov.Parabolic.Region d) (M : PDE.Mat d)
    (z : TimeVelocity d) :
    coefficientAt (extendCoefficientByMidpoint A U M) z =
      if z ∈ U then coefficientAt A z else M :=
  by
    classical
    rfl


end


private theorem midpoint_isSymm (d : Nat) (lam Lam : Real) :
    (ellipticityMidpoint d lam Lam).IsSymm := by
  unfold ellipticityMidpoint
  exact Matrix.isSymm_one.smul _




private theorem vecDot_smul_right (c : Real) (x : PDE.Vec d) :
    PDE.vecDot x (c • x) = c * PDE.vecNormSq x := by
  unfold PDE.vecNormSq
  unfold PDE.vecDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

section
variable {d : Nat}










private theorem sum_single_mul  (i : Fin d) (f : Fin d → Real) :
    ∑ x : Fin d, (Pi.single i (1 ) : PDE.Vec d) x * f x = f i := (PDE.vecDot_basisVec_left i f)


section
variable (M : PDE.Mat d)

private theorem quadratic_single   (i : Fin d) :
    PDE.vecDot (Pi.single i 1) (Matrix.mulVec M (Pi.single i 1)) = M i i := by
  simp_all [PDE.vecDot, sum_single_mul]

private theorem quadratic_single_add   (i j : Fin d) :
    PDE.vecDot (Pi.single i 1 + Pi.single j 1)
      (Matrix.mulVec M (Pi.single i 1 + Pi.single j 1)) =
        M i i + M i j + M j i + M j j := by
  simp only [PDE.vecDot, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib]
  rw [sum_single_mul i, sum_single_mul i, sum_single_mul j, sum_single_mul j]
  simp only [Matrix.col_apply]
  ring
end


private theorem vecNormSq_single_add_le_four  (i j : Fin d) :
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
variable {d : Nat} {lam Lam : Real}

private theorem coefficient_entry_abs_le  {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) (hUpper : M ≤ Lam • (1 : PDE.Mat d))
    (i j : Fin d) :
    |M i j| ≤ 3 * (|lam| + |Lam|) := by
  let q : PDE.Vec d := Pi.single i 1 + Pi.single j 1
  have hqnonneg  := PDE.vecNormSq_nonneg q
  have hqle : PDE.vecNormSq q ≤ 4 := vecNormSq_single_add_le_four i j
  have hquadLower := _root_.HypoellipticAleksandrov.vecDot_mulVec_lower_of_loewner hLower q
  have hquadUpper := _root_.HypoellipticAleksandrov.vecDot_mulVec_upper_of_loewner hUpper q
  have hquadLower' : -(4 * |lam|) ≤ PDE.vecDot q (Matrix.mulVec M q) := by
    have hlam : -|lam| ≤ lam := neg_abs_le lam
    have hmul : -|lam| * PDE.vecNormSq q ≤ lam * PDE.vecNormSq q :=
      mul_le_mul_of_nonneg_right hlam hqnonneg

    exact (show -(4 * |lam|) ≤ -|lam| * PDE.vecNormSq q by
        have hmul' : |lam| * PDE.vecNormSq q ≤ |lam| * 4 :=
          mul_le_mul_of_nonneg_left hqle (abs_nonneg lam)
        nlinarith).trans (hmul.trans hquadLower)
  have hquadUpper' : PDE.vecDot q (Matrix.mulVec M q) ≤ 4 * |Lam| := by



    exact hquadUpper.trans ((mul_le_mul_of_nonneg_right (le_abs_self Lam) hqnonneg).trans (by
        have hmul' : |Lam| * PDE.vecNormSq q ≤ |Lam| * 4 :=
          mul_le_mul_of_nonneg_left hqle (abs_nonneg Lam)
        nlinarith))
  have hdiagLower (k : Fin d) : -|lam| ≤ M k k := by
    have h := _root_.HypoellipticAleksandrov.vecDot_mulVec_lower_of_loewner hLower (Pi.single k 1)
    rw [quadratic_single, vecNormSq_single] at h

    exact (neg_abs_le lam).trans (by simpa only [mul_one] using h)
  have hdiagUpper (k : Fin d) : M k k ≤ |Lam| := by
    have h := _root_.HypoellipticAleksandrov.vecDot_mulVec_upper_of_loewner hUpper (Pi.single k 1)
    rw [quadratic_single, vecNormSq_single] at h

    exact (show M k k ≤ Lam by simpa using h).trans (le_abs_self Lam)
  have hsymm := _root_.HypoellipticAleksandrov.matrix_isSymm_of_loewner_lower hLower
  have hquad : PDE.vecDot q (Matrix.mulVec M q) = M i i + 2 * M i j + M j j := by
    dsimp only [q]
    rw [quadratic_single_add, hsymm.apply i j]
    ring
  rw [abs_le]
  constructor
  · rw [hquad] at hquadLower'

    nlinarith [hdiagUpper i, hdiagUpper j, abs_nonneg lam, abs_nonneg Lam]
  · rw [hquad] at hquadUpper'

    nlinarith [hdiagLower i, hdiagLower j, abs_nonneg lam, abs_nonneg Lam]

private theorem locallyIntegrable_coefficient_entry
     {A : CoefficientField d}
    (hA : IsBorelCoefficient A) (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (i j : Fin d) :
    LocallyIntegrable (fun z : TimeVelocity d => coefficientAt A z i j)  := (fun z =>
  Exists.casesOn (Measure.finiteAt_nhds (timeVelocityVolume d) z) fun V h =>
    And.casesOn h fun hV hVfinite =>
      Exists.intro V
        ⟨hV,
          IntegrableOn.of_bound hVfinite
            (Measurable.aestronglyMeasurable (measurable_pi_iff.mp (measurable_pi_iff.mp hA i) j)) (3 * (|lam| + |Lam|))
            (univ_mem' (id fun y => coefficient_entry_abs_le (hLower y.1 y.2) (hUpper y.1 y.2) i j))⟩)

/-- An entry of a matrix between scalar lower and upper ellipticity bounds is
bounded by the corresponding absolute scalar bounds. -/
alias coefficient_entry_abs_le_of_ellipticity := _root_.HypoellipticAleksandrov.Parabolic.coefficient_entry_abs_le


/-- A Borel coefficient entry with global scalar ellipticity bounds is locally
integrable with respect to time--velocity volume. -/
alias locallyIntegrable_coefficientAt_entry_of_ellipticity := _root_.HypoellipticAleksandrov.Parabolic.locallyIntegrable_coefficient_entry

end


section
variable (d : Nat) (lam Lam : Real)

private theorem midpoint_lower  (hLam : lam ≤ Lam) :
    lam • (1 : PDE.Mat d) ≤ ellipticityMidpoint d lam Lam := by
  apply loewner_lower_of_quadraticForm (midpoint_isSymm d lam Lam)
  intro x
  unfold ellipticityMidpoint
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, vecDot_smul_right]
  have hx  := PDE.vecNormSq_nonneg x

  nlinarith

private theorem midpoint_upper  (hLam : lam ≤ Lam) :
    ellipticityMidpoint d lam Lam ≤ Lam • (1 : PDE.Mat d) := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simp_all [_root_.HypoellipticAleksandrov.isHermitian_of_isSymm, midpoint_isSymm]
  · intro x
    unfold ellipticityMidpoint
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub]
    have hx  := PDE.vecNormSq_nonneg x

    have hcalc : 0 ≤ PDE.vecDot x (Lam • x) -
        PDE.vecDot x (((lam + Lam) / 2) • x) := by
      rw [vecDot_smul_right, vecDot_smul_right]
      nlinarith
    assumption

/-- Midpoint extension preserves exact lower and upper ellipticity and
symmetry globally. -/
theorem extendCoefficientByMidpoint_global_ellipticity
     (Abar : CoefficientField d)
    (U : HypoellipticAleksandrov.Parabolic.Region d)
    (hAbarSymm : ∀ z ∈ U, (coefficientAt Abar z).IsSymm)
    (hAbarLower : ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt Abar z)
    (hAbarUpper : ∀ z ∈ U, coefficientAt Abar z ≤ Lam • (1 : PDE.Mat d))
    (hLam : lam ≤ Lam) :
    IsSymmetricCoefficient
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) ∧
    HasLowerEllipticity lam
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) ∧
    HasUpperEllipticity Lam
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) := by
  constructor
  · intro t v
    by_cases hUV : (t, v) ∈ U
    · simpa only [extendCoefficientByMidpoint, if_pos hUV, coefficientAt] using
      hAbarSymm (t, v) hUV
    · simpa only [extendCoefficientByMidpoint, if_neg hUV] using
        midpoint_isSymm d lam Lam
  constructor
  · intro t v
    by_cases hUV : (t, v) ∈ U
    · simpa only [extendCoefficientByMidpoint, if_pos hUV, coefficientAt] using
      hAbarLower (t, v) hUV
    · simpa only [extendCoefficientByMidpoint, if_neg hUV] using
        midpoint_lower d lam Lam hLam
  · intro t v
    by_cases hUV : (t, v) ∈ U
    · simpa only [extendCoefficientByMidpoint, if_pos hUV, coefficientAt] using
      hAbarUpper (t, v) hUV
    · simpa only [extendCoefficientByMidpoint, if_neg hUV] using
        midpoint_upper d lam Lam hLam

variable (A : CoefficientField d)

/-- Entrywise mollification produces a smooth coefficient field. -/
theorem isSmoothCoefficient_parabolicMollifyCoefficient

    (hA : IsBorelCoefficient A)
    (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat) :
    IsSmoothCoefficient (parabolicMollifyCoefficient A n) := (id
  (Eq.mpr (id (congrArg (fun _a => _a) (propext contDiff_pi))) fun i =>
    Eq.mpr (id (congrArg (fun _a => _a) (propext contDiff_pi))) fun j =>
      id
        (contDiff_parabolicConvolution (locallyIntegrable_coefficient_entry hA hLower hUpper i j)
          (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n))))

include lam Lam in
/-- Entrywise mollification preserves pointwise matrix symmetry. -/
theorem isSymmetricCoefficient_parabolicMollifyCoefficient

    (hSymm : IsSymmetricCoefficient A) (n : Nat) :
    IsSymmetricCoefficient (parabolicMollifyCoefficient A n) := by


  intro t v
  apply Matrix.IsSymm.ext
  intro i j
  have hentries : (fun z : TimeVelocity d => coefficientAt A z j i) =
      fun z : TimeVelocity d => coefficientAt A z i j := by
    funext z
    exact hSymm z.1 z.2 |>.apply i j
  simp only [parabolicMollifyCoefficient]
  rw [hentries]
end


section
variable {d : Nat}

section
variable {lam Lam : Real} {A : CoefficientField d} (hA : IsBorelCoefficient A) (hLower : HasLowerEllipticity lam A) (hUpper : HasUpperEllipticity Lam A)

include hA hLower hUpper in
private theorem locallyIntegrable_coefficient_quadratic
      (x : PDE.Vec d) :
    LocallyIntegrable (fun z : TimeVelocity d =>
      PDE.vecDot x (Matrix.mulVec (coefficientAt A z) x))  := by
  have hterm (i j : Fin d) : LocallyIntegrable
      (fun z : TimeVelocity d => (x i * x j) • coefficientAt A z i j)  :=
    (locallyIntegrable_coefficient_entry hA hLower hUpper i j).smul (x i * x j)
  have hrow (i : Fin d) : LocallyIntegrable
      (fun z : TimeVelocity d => ∑ j : Fin d, (x i * x j) • coefficientAt A z i j)  := by
    simpa only using locallyIntegrable_finset_sum Finset.univ (fun j _hj => hterm i j)

  convert ((locallyIntegrable_finset_sum Finset.univ fun i _hi => hrow i)) using 1
  ext z
  simp only [PDE.vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

include hA hLower hUpper in
private theorem quadratic_parabolicMollifyCoefficient_eq
      (n : Nat)
    (x z : TimeVelocity d) :
    PDE.vecDot x.2
      (Matrix.mulVec (coefficientAt (parabolicMollifyCoefficient A n) z) x.2) =
      parabolicConvolution
        (fun y  =>
          PDE.vecDot x.2 (Matrix.mulVec (coefficientAt A y) x.2))
        (parabolicMollifier d n) z := by
  let rhoz  := fun y => parabolicMollifier d n (z - y)


  have hint (i j : Fin d) : Integrable
      (fun y : TimeVelocity d => (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y)  := by

    convert ((locallyIntegrable_coefficient_entry hA hLower hUpper i j).smul (x.2 i * x.2 j)).integrable_smul_right_of_hasCompactSupport (show Continuous rhoz by
        dsimp only [rhoz]
        exact (contDiff_parabolicMollifier d n).continuous.comp
          (continuous_const.sub continuous_id)) (show HasCompactSupport rhoz by
        dsimp only [rhoz]
        exact (hasCompactSupport_parabolicMollifier d n).comp_homeomorph (Homeomorph.subLeft z)) using 1
  change (∑ i : Fin d, x.2 i * ∑ j : Fin d,
      (∫ y, coefficientAt A y i j * rhoz y) * x.2 j) =
    ∫ y, (∑ i : Fin d, x.2 i * ∑ j : Fin d,
      coefficientAt A y i j * x.2 j) * rhoz y
  have hsum : (fun y : TimeVelocity d =>
      (∑ i : Fin d, x.2 i * ∑ j : Fin d, coefficientAt A y i j * x.2 j) * rhoz y) =
      fun y => ∑ i : Fin d, ∑ j : Fin d,
        (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y := by
    funext y
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    calc
      (x.2 i * ∑ j : Fin d, coefficientAt A y i j * x.2 j) * rhoz y =
          x.2 i * ((∑ j : Fin d, coefficientAt A y i j * x.2 j) * rhoz y) := by
            ring
      _ = x.2 i * ∑ j : Fin d, (coefficientAt A y i j * x.2 j) * rhoz y := by
            rw [Finset.sum_mul]
      _ = ∑ j : Fin d, x.2 i * x.2 j * coefficientAt A y i j * rhoz y := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
  rw [hsum, integral_finset_sum Finset.univ]
  · rw [show (fun i  => ∫ y, ∑ j : Fin d,
        (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y) =
        fun i => ∑ j : Fin d, ∫ y,
          (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y by
      funext i
      rw [integral_finset_sum Finset.univ]
      intro j _hj
      exact hint i j]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  · intro i _hi
    apply integrable_finset_sum
    intro j _hj
    exact hint i j
end


private theorem parabolicConvolution_eq_normed_left
     (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (n : Nat) (z : TimeVelocity d) :
    parabolicConvolution f (parabolicMollifier d n) z =
      (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real,
        (volume )] f) z := by
  rw [← convolution_flip]
  simp only [parabolicConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  change f y * parabolicMollifier d n (z - y) =
    parabolicMollifier d n (z - y) * f y
  ring
end


section
variable (d : Nat) (lam Lam : Real) (A : CoefficientField d) (hA : IsBorelCoefficient A) (hSymm : IsSymmetricCoefficient A) (hLower : HasLowerEllipticity lam A) (hUpper : HasUpperEllipticity Lam A) (n : Nat)

include hA hSymm hLower hUpper in
/-- Entrywise mollification preserves the exact lower Loewner ellipticity
bound. -/
theorem hasLowerEllipticity_parabolicMollifyCoefficient
     :
    HasLowerEllipticity lam (parabolicMollifyCoefficient A n) := by
  intro t v

  apply loewner_lower_of_quadraticForm
    ((isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam A hSymm n) t v)
  intro x
  let q : TimeVelocity d := (t, v)
  let quad : HypoellipticAleksandrov.Parabolic.ScalarField d := fun y =>
    PDE.vecDot x (Matrix.mulVec (coefficientAt A y) x)
  let c : Real := lam * PDE.vecNormSq x

  have hconstLoc : LocallyIntegrable (fun _ : TimeVelocity d => c)  :=
    locallyIntegrable_const c
  have hquadExists := (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
    (ContinuousLinearMap.lsmul Real Real) (contDiff_parabolicMollifier d n).continuous (locallyIntegrable_coefficient_quadratic hA hLower hUpper x) q
  have hconstExists := (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
    (ContinuousLinearMap.lsmul Real Real) (contDiff_parabolicMollifier d n).continuous hconstLoc q

  have hmono := convolution_mono_right hconstExists hquadExists
    (parabolicMollifier_nonneg d n) (by
        intro y
        exact _root_.HypoellipticAleksandrov.vecDot_mulVec_lower_of_loewner (hLower y.1 y.2) x)

  have hquad :
      PDE.vecDot x (Matrix.mulVec
        (coefficientAt (parabolicMollifyCoefficient A n) q) x) =
        (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume] quad) q := by
    calc
      PDE.vecDot x (Matrix.mulVec
          (coefficientAt (parabolicMollifyCoefficient A n) q) x) =
          parabolicConvolution quad (parabolicMollifier d n) q := (quadratic_parabolicMollifyCoefficient_eq hA hLower hUpper n (0, x) q)
      _ = (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume] quad) q :=
        parabolicConvolution_eq_normed_left quad n q
  change c ≤ PDE.vecDot x (Matrix.mulVec
    (coefficientAt (parabolicMollifyCoefficient A n) q) x)
  rw [hquad]
  exact (show (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
        (fun _  => c)) q = c by
      exact ContDiffBump.normed_convolution_eq_right
          (fun _ _ => rfl)).symm.le.trans hmono

include hA hSymm hLower hUpper in
/-- Entrywise mollification preserves the exact upper Loewner ellipticity
bound. -/
theorem hasUpperEllipticity_parabolicMollifyCoefficient
     :
    HasUpperEllipticity Lam (parabolicMollifyCoefficient A n) := (fun t v =>
  Eq.mpr (id (congrArg (fun _a => _a) (propext Matrix.le_iff)))
    (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_of_isSymm
        (Matrix.IsSymm.sub (Matrix.IsSymm.smul Matrix.isSymm_one Lam)
          (isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam A hSymm n t v)))
      fun x =>
      Eq.mpr
        (id
          (congrArg (LE.le 0)
            (Eq.trans
              (Eq.trans
                (congr (congrArg dotProduct (star_trivial x))
                  (Eq.trans (Matrix.sub_mulVec (Lam • 1) (coefficientAt (parabolicMollifyCoefficient A n) (t, v)) x)
                    (congrFun'
                      (congrArg HSub.hSub
                        (Eq.trans (Matrix.smul_mulVec Lam 1 x) (congrArg (HSMul.hSMul Lam) (Matrix.one_mulVec x))))
                      (Matrix.mulVec (coefficientAt (parabolicMollifyCoefficient A n) (t, v)) x))))
                (dotProduct_sub x (Lam • x) (Matrix.mulVec (coefficientAt (parabolicMollifyCoefficient A n) (t, v)) x)))
              (congrFun' (congrArg HSub.hSub (dotProduct_smul Lam x x))
                (x ⬝ᵥ Matrix.mulVec (coefficientAt (parabolicMollifyCoefficient A n) (t, v)) x)))))
        (id
          (sub_nonneg.mpr
            (Eq.mpr
              (id
                (congrArg (fun _a => _a ≤ Lam * PDE.vecNormSq x)
                  (Trans.trans (quadratic_parabolicMollifyCoefficient_eq hA hLower hUpper n (0, x) (t, v))
                    (parabolicConvolution_eq_normed_left (fun y => PDE.vecDot x (Matrix.mulVec (coefficientAt A y) x)) n
                      (t, v)))))
              (LE.le.trans
                (convolution_mono_right
                  (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
                    (hasCompactSupport_parabolicMollifier d n) (ContDiff.continuous (contDiff_parabolicMollifier d n))
                    (locallyIntegrable_coefficient_quadratic hA hLower hUpper x) (t, v))
                  (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
                    (hasCompactSupport_parabolicMollifier d n) (ContDiff.continuous (contDiff_parabolicMollifier d n))
                    (locallyIntegrable_const (Lam * PDE.vecNormSq x)) (t, v))
                  (parabolicMollifier_nonneg d n) fun y => vecDot_mulVec_upper_of_loewner (hUpper y.1 y.2) x)
                (Eq.le (ContDiffBump.normed_convolution_eq_right fun x_1 x_2 => rfl))))))))
end


/-- The right parabolic convolution converges almost everywhere for
every locally integrable scalar function. -/
theorem tendsto_ae_parabolicConvolution_of_locallyIntegrable
    {d : Nat} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : LocallyIntegrable f ) :
    ∀ᵐ z,
      Tendsto (fun n =>
        parabolicConvolution f (parabolicMollifier d n) z)
        atTop (nhds (f z)) := by
  have hratio : ∀ᶠ n : Nat in atTop,
      (parabolicMollifierBump d n).rOut ≤ 2 * (parabolicMollifierBump d n).rIn :=
    Filter.Eventually.of_forall fun n => by
      rw [parabolicMollifierBump_rOut]
      change parabolicMollifierScale n ≤ 2 * (parabolicMollifierScale n / 2)
      ring_nf
      exact le_rfl
  have hleft := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun n  => parabolicMollifierBump d n)
    tendsto_parabolicMollifierScale_zero hratio hf
  filter_upwards [hleft] with z hz
  apply hz.congr'
  filter_upwards with n
  simpa only [parabolicMollifier] using (parabolicConvolution_eq_normed_left f n z).symm

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

/-- A pointwise lower Loewner ellipticity bound entails pointwise matrix
symmetry. -/
theorem isSymmetricCoefficient_of_hasLowerEllipticity
    {d : Nat} {lam : Real} {A : CoefficientField d}
    (hLower : HasLowerEllipticity lam A) :
    IsSymmetricCoefficient A := by
  intro t v
  exact _root_.HypoellipticAleksandrov.matrix_isSymm_of_loewner_lower (hLower t v)

end HypoellipticAleksandrov.Parabolic
