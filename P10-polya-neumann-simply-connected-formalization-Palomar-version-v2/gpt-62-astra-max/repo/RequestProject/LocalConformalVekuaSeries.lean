module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalHardyPrimitive
public import RequestProject.NeumannH1AffineMultiplier
public import RequestProject.NeumannH1VekuaWeakIdentity
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecificLimits.Normed
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

section

variable (E : ℂ) (j : ℕ)
include E

include j in
/-- The genuine complex coefficient at a fixed energy. -/
def physicalVekuaCoeff : ℂ := (-E / 4) ^ j / (j.factorial : ℂ)

theorem physicalVekuaCoeff_zero : physicalVekuaCoeff E 0 = 1 := by
  simp [physicalVekuaCoeff]

theorem physicalVekuaCoeff_succ :
    physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ) =
      (-E / 4) * physicalVekuaCoeff E j := by
  
  
  simp only [physicalVekuaCoeff, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp [(by exact_mod_cast Nat.factorial_ne_zero j), (by exact_mod_cast (by omega : j + 1 ≠ 0))]

theorem norm_physicalVekuaCoeff :
    ‖physicalVekuaCoeff E j‖ = ‖-E / 4‖ ^ j / (j.factorial : ℝ) := by
  simp [physicalVekuaCoeff]

end

section BoundedSeries

variable {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

section

variable (A : X →L[ℂ] X) (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) (j : ℕ)
    (b : X)

private theorem vekua_norm_clm_pow_le :
    ‖A ^ j‖ ≤ ‖A‖ ^ j := by
  induction j with
  | zero =>
    exact ContinuousLinearMap.norm_id_le  (E := X)
  | succ j ih =>
    calc
      _ = ‖A ^ j * A‖ := by rw [pow_succ]
      _ ≤ _ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (norm_nonneg A)
      _ = _ := (pow_succ ‖A‖ j).symm

include E J M U j in
/-- The j-th bounded operator giving the genuine H¹ series term. -/
def boundedPhysicalVekuaTerm : X →L[ℂ] H :=
  physicalVekuaCoeff E j • ((M ^ j).comp (U.comp (J ^ j)))

omit [CompleteSpace H] in
theorem boundedPhysicalVekuaTerm_apply :
    boundedPhysicalVekuaTerm M U J E j b =
      physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)) := rfl

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaTerm_le :
    ‖boundedPhysicalVekuaTerm M U J E j‖ ≤
      ‖U‖ * ((‖-E / 4‖ * ‖M‖ * ‖J‖) ^ j / (j.factorial : ℝ)) := by
  
  calc
    _ = _ := norm_smul _ _
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (((M ^ j).opNorm_comp_le (U.comp (J ^ j))).trans
        (mul_le_mul_of_nonneg_left (U.opNorm_comp_le (J ^ j)) (norm_nonneg _))) (norm_nonneg _)
    _ ≤ ‖physicalVekuaCoeff E j‖ * (‖M‖ ^ j * (‖U‖ * ‖J‖ ^ j)) := by
      gcongr
      · exact vekua_norm_clm_pow_le M j
      · exact vekua_norm_clm_pow_le J j
    _ = _ := by simp [norm_physicalVekuaCoeff, mul_pow] <;> ring

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaTerm :
    Summable (fun j : ℕ => ‖boundedPhysicalVekuaTerm M U J E j‖) := Summable.of_nonneg_of_le ((by norm_num))
    (norm_boundedPhysicalVekuaTerm_le M U J E)
    ((Real.summable_pow_div_factorial (‖-E / 4‖ * ‖M‖ * ‖J‖)).mul_left ‖U‖)

include E J M U in
/-- A norm-convergent series of actual bounded maps. -/
def boundedPhysicalVekuaSeries : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaTerm M U J E j

theorem boundedPhysicalVekuaSeries_hasSum :
    HasSum (boundedPhysicalVekuaTerm M U J E)
      (boundedPhysicalVekuaSeries M U J E) :=
  (summable_norm_boundedPhysicalVekuaTerm M U J E).of_norm.hasSum

theorem boundedPhysicalVekuaSeries_hasSum_apply :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
      (boundedPhysicalVekuaSeries M U J E b) := by
  simpa only [ContinuousLinearMap.apply_apply, boundedPhysicalVekuaTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaSeries_hasSum M U J E)

private theorem vekua_pow_commutes_apply :
    (J ^ j) (J b) = J ((J ^ j) b) := by
  rw [← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ', ContinuousLinearMap.mul_apply]

end

private theorem vekua_series_D_shift {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V D : H →L[ℂ] Y)
    (hD0 : ∀ b : X, D (U b) = 0)
    (hD : ∀ (j : ℕ) (b : X), D ((M ^ (j + 1)) (U b)) =
      ((j + 1 : ℕ) : ℂ) • V ((M ^ j) (U b))) (E : ℂ) (b : X) :
    D (boundedPhysicalVekuaSeries M U J E b) =
      (-E / 4) • V (boundedPhysicalVekuaSeries M U J E (J b)) := by
  let f  := fun j =>
    D (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
  have hs  :=
    D.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b)
  have hz : f 0 = 0 := by
    simp [f, hD0]
  have hs1 : HasSum (fun j : ℕ => f (j + 1))
      (D (boundedPhysicalVekuaSeries M U J E b)) := by
    simpa only [Finset.sum_range_one, hz, sub_zero] using
      (hasSum_nat_add_iff' (f := f) 1).2 hs
  have hf (j : ℕ) : f (j + 1) = (-E / 4) •
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) := calc
      _ = (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          V ((M ^ j) (U ((J ^ (j + 1)) b))) := by
        dsimp [f]
        rw [map_smul, hD, smul_smul]
      _ = _ := by
        rw [physicalVekuaCoeff_succ, pow_succ, ContinuousLinearMap.mul_apply,
          map_smul, smul_smul]
  
  have hl : HasSum (fun j : ℕ => (-E / 4) •
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))))
      (D (boundedPhysicalVekuaSeries M U J E b)) := by
    simpa only [hf] using hs1
  exact hl.unique ((V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b))).const_smul
    (-E / 4))

private theorem vekua_series_Dbar_primitive {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V Dbar : H →L[ℂ] Y) (b : X)
    (hDbar : ∀ j : ℕ, Dbar ((M ^ j) (U (J ((J ^ j) b)))) =
      V ((M ^ j) (U ((J ^ j) b)))) (E : ℂ) :
    Dbar (boundedPhysicalVekuaSeries M U J E (J b)) =
      V (boundedPhysicalVekuaSeries M U J E b) := by
  have hl := Dbar.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b))
  
  have he (j : ℕ) :
      Dbar (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) =
        V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))) := by
    simp only [map_smul]
    rw [vekua_pow_commutes_apply J j b, hDbar j]
  have hl' : HasSum (fun j : ℕ =>
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))))
      (Dbar (boundedPhysicalVekuaSeries M U J E (J b))) := by
    simpa only [he] using hl
  exact hl'.unique (V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b))

end BoundedSeries

private theorem vekua_mapped_equality {Y : Type*} (N : Y → Y)
    {a b c d : Y} (ha : a = N b) (hb : b = c) (hd : d = N c) : a = d :=
  (by grind)

section PhysicalCoordinates

section

variable (Φ : DiskCoordinates) (p E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)

include E p in
/-- The genuine physical Vekua operator, based at the supplied point p. -/
def DiskCoordinates.vekuaH1 :
    L2Z →L[ℂ] NeumannH1 Φ.domain :=
  boundedPhysicalVekuaSeries (neumannH1AffineMultiplier Φ.bounded p)
    Φ.hardyH1Extension
    Φ.hardyPrimitive E

include E in
/-- The physical series based at the same boundary point F(1) as `antiPrim`. -/
def DiskCoordinates.vekuaH1AtBoundaryOrigin :
    L2Z →L[ℂ] NeumannH1 Φ.domain :=
  Φ.vekuaH1 (Φ.map 1) E

theorem localConformalVekuaH1_hasSum :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j •
      ((neumannH1AffineMultiplier Φ.bounded p) ^ j)
        (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b)))
      (Φ.vekuaH1 p E b) :=
  boundedPhysicalVekuaSeries_hasSum_apply _ _ _ E b

/-- Applying the actual coordinate half trace preserves the true H¹ series. -/
theorem localConformalVekuaH1_halfTrace_hasSum :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j •
      Φ.pulledBackHalfTrace Φ.lipschitzDomain
        (((neumannH1AffineMultiplier Φ.bounded p) ^ j)
          (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))
      (Φ.pulledBackHalfTrace Φ.lipschitzDomain
        (Φ.vekuaH1 p E b)) := by
  simpa only [map_smul] using (Φ.pulledBackHalfTrace Φ.lipschitzDomain).hasSum
    (localConformalVekuaH1_hasSum Φ p E b)

theorem localConformalHardyPrimitive_pow_nonpositive (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (j : ℕ) :
    IsNonpositiveFourierSupport ((Φ.hardyPrimitive ^ j) b) := by
  induction j with
  | zero => exact hbn
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact localConformalHardyPrimitive_nonpositive Φ hhol _ ih

/-- The actual physical Hardy extension is killed by the true first
Wirtinger derivative, for every normalized input. -/
theorem localConformalHardyH1Extension_wirtingerD_eq_zero :
    h1WirtingerD Φ.domain
      (Φ.hardyH1Extension b) = 0 :=
  h1WirtingerD_eq_zero_of_cauchyRiemann _ _
    (localConformalHardyH1Extension_cauchyRiemann Φ b)

include hbn in
/-- The true conjugate derivative of the physical primitive is the
physical Hardy value; this keeps the full nonpositive subspace. -/
theorem localConformalHardyH1Extension_wirtingerDbar_primitive :
    h1WirtingerDbar Φ.domain
      (Φ.hardyH1Extension (Φ.hardyPrimitive b)) =
      h1Value Φ.domain
        (Φ.hardyH1Extension b) :=
  h1WirtingerDbar_eq_value_of_components _ _ _
    (localConformalHardyH1Extension_primitive_gradient Φ b hbn)
    (localConformalHardyH1Extension_primitive_gradient_y Φ b hbn)

/-- Differentiation of the genuine H¹ series shifts the primitive once.
The factorial identity is applied only after continuous L² differentiation. -/
theorem localConformalVekuaH1_wirtingerD :
    h1WirtingerD Φ.domain
      (Φ.vekuaH1 p E b) =
      (-E / 4) • h1Value Φ.domain
        (Φ.vekuaH1 p E
          (Φ.hardyPrimitive b)) := by
  apply vekua_series_D_shift
  · intro x
    exact localConformalHardyH1Extension_wirtingerD_eq_zero Φ x
  · intro j x
    exact h1WirtingerD_affine_pow_of_antiholomorphic Φ.bounded p
      (Φ.hardyH1Extension x)
      (localConformalHardyH1Extension_cauchyRiemann Φ x) j

include hbn in
/-- The conjugate derivative of the shifted series is exactly the original
physical value series, by the actual primitive derivative and affine rule. -/
theorem localConformalVekuaH1_wirtingerDbar_primitive :
    h1WirtingerDbar Φ.domain
      (Φ.vekuaH1 p E
        (Φ.hardyPrimitive b)) =
      h1Value Φ.domain
        (Φ.vekuaH1 p E b) := by
  apply vekua_series_Dbar_primitive
  intro j
  let q  := (Φ.hardyPrimitive ^ j) b
  let u  :=
    Φ.hardyH1Extension (Φ.hardyPrimitive q)
  let v  :=
    Φ.hardyH1Extension q
  have hq  :=
    localConformalHardyPrimitive_pow_nonpositive Φ Φ.holomorphic b hbn j
  have hprimitive  :=
    localConformalHardyH1Extension_wirtingerDbar_primitive Φ q hq
  exact vekua_mapped_equality
    ((neumannAffineL2Multiplier p (neumannH1AffineBound_spec Φ.bounded p) ^ j))
    (h1WirtingerDbar_affine_pow Φ.bounded p u j) hprimitive
    (h1Value_neumannH1AffineMultiplier_pow Φ.bounded p v j)

end

end PhysicalCoordinates

end PolyaNeumann

end
