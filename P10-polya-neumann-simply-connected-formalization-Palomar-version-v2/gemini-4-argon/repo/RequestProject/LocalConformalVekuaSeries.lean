module

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate ContDiff

/-- The genuine complex coefficient at a fixed energy. -/
def physicalVekuaCoeff (E : ℂ) (j : ℕ) : ℂ := (-E / 4) ^ j / (j.factorial : ℂ)

theorem physicalVekuaCoeff_zero E : physicalVekuaCoeff E 0 = 1 := by
  simp [physicalVekuaCoeff]

theorem physicalVekuaCoeff_succ E j :
    physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ) =
      (-E / 4) * physicalVekuaCoeff E j := by
  simp [physicalVekuaCoeff, Nat.factorial_succ, pow_succ]
  field_simp [(by exact_mod_cast Nat.factorial_ne_zero j), (by exact_mod_cast (by omega : j + 1 ≠ 0))]

theorem norm_physicalVekuaCoeff E j :
    ‖physicalVekuaCoeff E j‖ = ‖-E / 4‖ ^ j / (j.factorial : ℝ) := by
  simp [physicalVekuaCoeff]

section BoundedSeries

variable {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

private theorem vekua_norm_clm_pow_le (A : X →L[ℂ] X) j :
    ‖A ^ j‖ ≤ ‖A‖ ^ j := by
  induction j with
  | zero =>
    simp
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := X)
  | succ j ih =>
    calc
      _ = _ := by rw [pow_succ]
      _ ≤ _ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (norm_nonneg A)
      _ = _ := (pow_succ ‖A‖ j).symm

/-- The j-th bounded operator giving the genuine H¹ series term. -/
def boundedPhysicalVekuaTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) : X →L[ℂ] H :=
  physicalVekuaCoeff E j • ((M ^ j).comp (U.comp (J ^ j)))

omit [CompleteSpace H] in
theorem boundedPhysicalVekuaTerm_apply (M : H →L[ℂ] H) U
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) (b : X) :
    boundedPhysicalVekuaTerm M U J E j b =
      physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)) := rfl

omit [CompleteSpace H] in
theorem norm_boundedPhysicalVekuaTerm_le (M : H →L[ℂ] H) U
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) :
    ‖boundedPhysicalVekuaTerm M U J E j‖ ≤
      ‖U‖ * ((‖-E / 4‖ * ‖M‖ * ‖J‖) ^ j / (j.factorial : ℝ)) := by
  calc
    _ = _ := norm_smul _ _
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (((M ^ j).opNorm_comp_le (U.comp (J ^ j))).trans (mul_le_mul_of_nonneg_left (U.opNorm_comp_le (J ^ j)) (norm_nonneg _))) (norm_nonneg _)
    _ ≤ ‖physicalVekuaCoeff E j‖ * (‖M‖ ^ j * (‖U‖ * ‖J‖ ^ j)) := by
      gcongr
      · exact vekua_norm_clm_pow_le M j
      · exact vekua_norm_clm_pow_le J j
    _ = _ := by rw [norm_physicalVekuaCoeff]; simp [mul_pow]; ring

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) :
    Summable (fun j => ‖boundedPhysicalVekuaTerm M U J E j‖) := by
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (norm_boundedPhysicalVekuaTerm_le M U J E)
    ((Real.summable_pow_div_factorial (‖-E / 4‖ * ‖M‖ * ‖J‖)).mul_left ‖U‖)

/-- A norm-convergent series of actual bounded maps. -/
def boundedPhysicalVekuaSeries (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaTerm M U J E j

theorem boundedPhysicalVekuaSeries_hasSum (M : H →L[ℂ] H) U
    (J : X →L[ℂ] X) (E : ℂ) :
    HasSum (fun j => boundedPhysicalVekuaTerm M U J E j)
      (boundedPhysicalVekuaSeries M U J E) :=
  (summable_norm_boundedPhysicalVekuaTerm M U J E).of_norm.hasSum

theorem boundedPhysicalVekuaSeries_hasSum_apply (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    HasSum (fun j => physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
      (boundedPhysicalVekuaSeries M U J E b) := by
  simpa [boundedPhysicalVekuaTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum (boundedPhysicalVekuaSeries_hasSum M U J E)

private theorem vekua_series_D_shift {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V D : H →L[ℂ] Y)
    (hD0 : ∀ b : X, D (U b) = 0)
    (hD : ∀ (j : ℕ) (b : X), D ((M ^ (j + 1)) (U b)) =
      ((j + 1 : ℕ) : ℂ) • V ((M ^ j) (U b))) (E : ℂ) (b : X) :
    D (boundedPhysicalVekuaSeries M U J E b) =
      (-E / 4) • V (boundedPhysicalVekuaSeries M U J E (J b)) := by
  let f : ℕ → Y := fun j =>
    D (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))
  have hf j : f (j + 1) = (-E / 4) •
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) := by
    calc
      _ = (physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) •
          V ((M ^ j) (U ((J ^ (j + 1)) b))) := by
        dsimp only [f]
        rw [map_smul, hD, smul_smul]
      _ = _ := by
        rw [physicalVekuaCoeff_succ, pow_succ, ContinuousLinearMap.mul_apply,
          map_smul, smul_smul]
  have hl : HasSum (fun j => (-E / 4) •
      V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))))
      (D (boundedPhysicalVekuaSeries M U J E b)) := by
    simpa [hf] using show HasSum (fun j => f (j + 1)) (D (boundedPhysicalVekuaSeries M U J E b)) by
      simpa [Finset.sum_range_one, show f 0 = 0 by
        simp [f, physicalVekuaCoeff_zero, hD0]] using
        (hasSum_nat_add_iff' (f := f) 1).2 (D.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b))
  exact hl.unique ((V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b))).const_smul (-E / 4))

private theorem vekua_series_Dbar_primitive {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (M : H →L[ℂ] H) (U : X →L[ℂ] H) (J : X →L[ℂ] X)
    (V Dbar : H →L[ℂ] Y) (b : X)
    (hDbar : ∀ j : ℕ, Dbar ((M ^ j) (U (J ((J ^ j) b)))) =
      V ((M ^ j) (U ((J ^ j) b)))) E :
    Dbar (boundedPhysicalVekuaSeries M U J E (J b)) =
      V (boundedPhysicalVekuaSeries M U J E b) := by
  have he j :
      Dbar (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) (J b)))) =
        V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b))) := by
    simp only [map_smul]
    rw [show (J ^ j) (J b) = J ((J ^ j) b) by
      rw [← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ', ContinuousLinearMap.mul_apply], hDbar j]
  exact (show HasSum (fun j => V (physicalVekuaCoeff E j • (M ^ j) (U ((J ^ j) b)))) (Dbar (boundedPhysicalVekuaSeries M U J E (J b))) by
    simpa only [he] using (Dbar.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E (J b)))).unique (V.hasSum (boundedPhysicalVekuaSeries_hasSum_apply M U J E b))

end BoundedSeries

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

/-- The genuine physical Vekua operator, based at the supplied point p. -/
local notation "Φ0" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ2" => localConformalHardyPrimitive hR F hFs

local notation "Φ3" => ball 0 1

def localConformalVekuaH1 (p E : ℂ) :
    L2Z →L[ℂ] NeumannH1 (F '' Φ3) :=
  boundedPhysicalVekuaSeries (neumannH1AffineMultiplier hb p)
    (Φ0)
    (Φ2) E

/-- The physical series based at the same boundary point F(1) as `antiPrim`. -/
local notation "Φ1" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes

def localConformalVekuaH1AtBoundaryOrigin (E : ℂ) :
    L2Z →L[ℂ] NeumannH1 (F '' Φ3) :=
  Φ1 (F 1) E

theorem localConformalVekuaH1_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j => physicalVekuaCoeff E j •
      ((neumannH1AffineMultiplier hb p) ^ j)
        (Φ0
          (((Φ2) ^ j) b)))
      (Φ1 p E b) :=
  boundedPhysicalVekuaSeries_hasSum_apply _ _ _ E b

/-- Applying the actual coordinate half trace preserves the true H¹ series. -/
theorem localConformalVekuaH1_halfTrace_hasSum p E b :
    HasSum (fun j => physicalVekuaCoeff E j •
      localConformalDiskHalfTrace hR F hFs hL
        (((neumannH1AffineMultiplier hb p) ^ j)
          (Φ0
            (((Φ2) ^ j) b))))
      (localConformalDiskHalfTrace hR F hFs hL
        (Φ1 p E b)) := by
  simpa using (localConformalDiskHalfTrace hR F hFs hL).hasSum
    (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)

include hhol in
theorem localConformalHardyPrimitive_pow_nonpositive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) j :
    IsNonpositiveFourierSupport (((Φ2) ^ j) b) := by
  induction j with
  | zero => simpa using hbn
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact localConformalHardyPrimitive_nonpositive hR F hFs hhol _ ih

/-- The actual physical Hardy extension is killed by the true first
Wirtinger derivative, for every normalized input. -/
local notation "Φ4" => localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalHardyH1Extension_wirtingerD_eq_zero b :
    h1WirtingerD (F '' Φ3)
      (Φ0 b) = 0 :=
  h1WirtingerD_eq_zero_of_cauchyRiemann _ _
    (Φ4 b)

/-- The true conjugate derivative of the physical primitive is the
physical Hardy value; this keeps the full nonpositive subspace. -/
theorem localConformalHardyH1Extension_wirtingerDbar_primitive (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar (F '' Φ3)
      (Φ0
        (Φ2 b)) =
      h1Value (F '' Φ3)
        (Φ0 b) :=
  h1WirtingerDbar_eq_value_of_components _ _ _
    (localConformalHardyH1Extension_primitive_gradient hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn)
    (localConformalHardyH1Extension_primitive_gradient_y hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn)

/-- Differentiation of the genuine H¹ series shifts the primitive once.
The factorial identity is applied only after continuous L² differentiation. -/
theorem localConformalVekuaH1_wirtingerD (p E : ℂ) (b : L2Z) :
    h1WirtingerD (F '' Φ3)
      (Φ1 p E b) =
      (-E / 4) • h1Value (F '' Φ3)
        (Φ1 p E
          (Φ2 b)) := by
  apply vekua_series_D_shift
  · intro x
    exact localConformalHardyH1Extension_wirtingerD_eq_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes x
  · intro j x
    exact h1WirtingerD_affine_pow_of_antiholomorphic hb p
      (Φ0 x)
      (Φ4 x) j

/-- The conjugate derivative of the shifted series is exactly the original
physical value series, by the actual primitive derivative and affine rule. -/
theorem localConformalVekuaH1_wirtingerDbar_primitive p E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar (F '' Φ3)
      (Φ1 p E
        (Φ2 b)) =
      h1Value (F '' Φ3)
        (Φ1 p E b) := by
  apply vekua_series_Dbar_primitive
  intro j
  let q := ((Φ2) ^ j) b
  exact (h1WirtingerDbar_affine_pow hb p (Φ0 (Φ2 q)) j).trans ((congrArg (fun x : L2 (F '' Φ3) => (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) ^ j) x) (localConformalHardyH1Extension_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK e he hsource hes q (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j))).trans (h1Value_neumannH1AffineMultiplier_pow hb p (Φ0 q) j).symm)

end PhysicalCoordinates

end PolyaNeumann

end
