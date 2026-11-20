module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalHardyPrimitive
public import RequestProject.NeumannH1AffineMultiplier
public import RequestProject.NeumannH1VekuaWeakIdentity
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A Vekua series in the genuine physical H¹ space

The actual affine H¹ multiplier, the actual supplied-coordinate Hardy
extension, and the bounded normalized Hardy primitive give a norm-convergent
operator series. Its values are genuine physical H¹ vectors and its trace
series is obtained by applying the actual continuous H¹ trace.

All conformal coordinates and their smooth local inverse are supplied
explicitly. No initial boundary-map existence or Neumann boundary equation
is assumed by this construction.

Chosen-boundary-origin applications use p = F(1), the point corresponding
to angular origin zero in the actual normalized primitive. The general-p
construction below does not assert injectivity of the Vekua conormal map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

/-- The genuine complex coefficient at a fixed energy. -/
def physicalVekuaCoeff (E : ℂ) (j : ℕ) : ℂ := (-E / 4) ^ j / (j.factorial : ℂ)

theorem physicalVekuaCoeff_zero (E : ℂ) : physicalVekuaCoeff E 0 = 1 := by
  simp [physicalVekuaCoeff]

theorem physicalVekuaCoeff_succ (E : ℂ) (j : ℕ) :
    physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ) =
      (-E / 4) * physicalVekuaCoeff E j := by
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hjs : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : j + 1 ≠ 0)
  simp only [physicalVekuaCoeff, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp [hj, hjs]

theorem norm_physicalVekuaCoeff (E : ℂ) (j : ℕ) :
    ‖physicalVekuaCoeff E j‖ = ‖-E / 4‖ ^ j / (j.factorial : ℝ) := by
  simp  [physicalVekuaCoeff, norm_div, norm_pow, Complex.norm_natCast]

section BoundedSeries

variable {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

private theorem vekua_norm_clm_pow_le (A : X →L[ℂ] X) (j : ℕ) :
    ‖A ^ j‖ ≤ ‖A‖ ^ j := by
  induction j with
  | zero =>
    simp  [pow_zero]
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := X)
  | succ j ih =>
    calc
      ‖A ^ (j + 1)‖ = ‖A ^ j * A‖ := by rw [pow_succ]
      _ ≤ ‖A ^ j‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ ‖A‖ ^ j * ‖A‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg A)
      _ = ‖A‖ ^ (j + 1) := (pow_succ ‖A‖ j).symm

/-- The j-th bounded operator giving the genuine H¹ series term. -/
def boundedPhysicalVekuaTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) : X →L[ℂ] H :=
  physicalVekuaCoeff E j • ((M ^ j).comp (U.comp (J ^ j)))

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaTerm_le (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) :
    ‖boundedPhysicalVekuaTerm M U J E j‖ ≤
      ‖U‖ * ((‖-E / 4‖ * ‖M‖ * ‖J‖) ^ j / (j.factorial : ℝ)) := by
  have hc :=
    ((M ^ j).opNorm_comp_le (U.comp (J ^ j))).trans
      (mul_le_mul_of_nonneg_left (U.opNorm_comp_le (J ^ j)) (norm_nonneg _))
  calc
    _ = ‖physicalVekuaCoeff E j‖ * ‖(M ^ j).comp (U.comp (J ^ j))‖ := norm_smul _ _
    _ ≤ ‖physicalVekuaCoeff E j‖ * (‖M ^ j‖ * (‖U‖ * ‖J ^ j‖)) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ ‖physicalVekuaCoeff E j‖ * (‖M‖ ^ j * (‖U‖ * ‖J‖ ^ j)) := by
      gcongr
      · exact vekua_norm_clm_pow_le M j
      · exact vekua_norm_clm_pow_le J j
    _ = _ := by rw [norm_physicalVekuaCoeff]; simp only [mul_pow]; ring

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    Summable (fun j : ℕ => ‖boundedPhysicalVekuaTerm M U J E j‖) := by
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (norm_boundedPhysicalVekuaTerm_le M U J E)
    ((Real.summable_pow_div_factorial (‖-E / 4‖ * ‖M‖ * ‖J‖)).mul_left ‖U‖)

/-- A norm-convergent series of actual bounded maps. -/
def boundedPhysicalVekuaSeries (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaTerm M U J E j

theorem boundedPhysicalVekuaSeries_hasSum (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    HasSum (fun j : ℕ => boundedPhysicalVekuaTerm M U J E j)
      (boundedPhysicalVekuaSeries M U J E) :=
  (summable_norm_boundedPhysicalVekuaTerm M U J E).of_norm.hasSum

theorem boundedPhysicalVekuaSeries_hasSum_apply (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
      (boundedPhysicalVekuaSeries M U J E b) := by
  simpa only [ContinuousLinearMap.apply_apply, boundedPhysicalVekuaTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaSeries_hasSum M U J E)

private theorem vekua_pow_commutes_apply (J : X →L[ℂ] X) (j : ℕ) (b : X) :
    (J ^ j) (J b) = J ((J ^ j) b) := by
  rw [← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ', ContinuousLinearMap.mul_apply]


private theorem vekua_series_Dbar_primitive {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V Dbar : H →L[ℂ] Y) (b : X)
    (hDbar : ∀ j : ℕ, Dbar ((M ^ j) (U (J ((J ^ j) b)))) =
      V ((M ^ j) (U ((J ^ j) b)))) (E : ℂ) :
    Dbar (boundedPhysicalVekuaSeries M U J E (J b)) =
      V (boundedPhysicalVekuaSeries M U J E b) := by
  have hl := Dbar.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b))
  have hr := V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b)
  have he (j : ℕ) :
      Dbar (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) =
        V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))) := by
    simp only [map_smul]
    rw [vekua_pow_commutes_apply J j b, hDbar j]
  have hl' : HasSum (fun j : ℕ =>
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))))
      (Dbar (boundedPhysicalVekuaSeries M U J E (J b))) := by
    simpa only [he] using hl
  exact hl'.unique hr

end BoundedSeries

private theorem vekua_mapped_equality {Y : Type*} (N : Y → Y)
    {a b c d : Y} (ha : a = N b) (hb : b = c) (hd : d = N c) : a = d :=
  ha.trans ((congrArg N hb).trans hd.symm)

section PhysicalCoordinates

variable {R : ℝ}
    (hR : 1 < R)
    (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (coords : ConformalDiskCoordinates F)

section

variable {F}
include coords

/-- The genuine physical Vekua operator, based at the supplied point p. -/
def localConformalVekuaH1 (p E : ℂ) :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  boundedPhysicalVekuaSeries (neumannH1AffineMultiplier coords.bounded p)
    (localConformalHardyH1Extension coords)
    (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth) E

/-- The physical series based at the same boundary point F(1) as `antiPrim`. -/
def localConformalVekuaH1AtBoundaryOrigin (E : ℂ) :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  localConformalVekuaH1 coords (F 1) E

theorem localConformalVekuaH1_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j •
      ((neumannH1AffineMultiplier coords.bounded p) ^ j)
        (localConformalHardyH1Extension coords
          (((localConformalHardyPrimitive coords.one_lt_radius F coords.smooth) ^ j) b)))
      (localConformalVekuaH1 coords p E b) :=
  boundedPhysicalVekuaSeries_hasSum_apply _ _ _ E b


end

include hhol in
theorem localConformalHardyPrimitive_pow_nonpositive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    IsNonpositiveFourierSupport (((localConformalHardyPrimitive hR F hFs) ^ j) b) := by
  induction j with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using hbn
  | succ j ih =>
    rw [pow_succ']
    exact localConformalHardyPrimitive_nonpositive hR F hFs hhol _ ih

section

variable {F}
include coords


/-- The true conjugate derivative of the physical primitive is the
physical Hardy value; this keeps the full nonpositive subspace. -/
theorem localConformalHardyH1Extension_wirtingerDbar_primitive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar (F '' ball (0 : ℂ) 1)
      (localConformalHardyH1Extension coords
        (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension coords b) :=
  h1WirtingerDbar_eq_value_of_components _ _ _
    (localConformalHardyH1Extension_primitive_gradient coords b hbn)
    (localConformalHardyH1Extension_primitive_gradient_y coords b hbn)


/-- The conjugate derivative of the shifted series is exactly the original
physical value series, by the actual primitive derivative and affine rule. -/
theorem localConformalVekuaH1_wirtingerDbar_primitive (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar (F '' ball (0 : ℂ) 1)
      (localConformalVekuaH1 coords p E
        (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalVekuaH1 coords p E b) := by
  apply vekua_series_Dbar_primitive
  intro j
  let q := ((localConformalHardyPrimitive coords.one_lt_radius F coords.smooth) ^ j) b
  let u :=
    localConformalHardyH1Extension coords
      (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth q)
  let v :=
    localConformalHardyH1Extension coords q
  have hq :=
    localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn j
  have hprimitive :=
    localConformalHardyH1Extension_wirtingerDbar_primitive coords q hq
  exact vekua_mapped_equality
    (fun x : L2 (F '' ball (0 : ℂ) 1) =>
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec coords.bounded p) ^ j) x)
    (h1WirtingerDbar_affine_pow coords.bounded p u j) hprimitive
    (h1Value_neumannH1AffineMultiplier_pow coords.bounded p v j)

end

end PhysicalCoordinates

end PolyaNeumann

end
