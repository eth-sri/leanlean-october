module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Coordinates
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The Euclidean radius differential on native coordinates. -/
def positionRadiusDifferential {d : ℕ} (x : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  (PDE.vecEuclideanNorm x)⁻¹ • seedDotLinear x


/-- The radius derivative applied to a native direction is its Euclidean dot product. -/
theorem positionRadiusDifferential_apply {d : ℕ} (x w : PDE.Vec d) :
    positionRadiusDifferential x w = PDE.vecDot (positionDirection x) w := by
  simp [positionRadiusDifferential, smul_apply, seedDotLinear_apply]
  unfold positionDirection PDE.vecDot
  simp [mul_assoc, Finset.mul_sum]

/-- The exact linear differential of the normalized position direction. -/
def positionDirectionDifferential {d : ℕ} (x : PDE.Vec d) : PDE.Vec d →L[ℝ] PDE.Vec d :=
  (PDE.vecEuclideanNorm x)⁻¹ • ContinuousLinearMap.id ℝ (PDE.Vec d) +
    ((-((PDE.vecEuclideanNorm x)⁻¹ ^ 2)) • positionRadiusDifferential x).smulRight x


/-- The normalized direction differential is the projection onto the tangent hyperplane. -/
theorem positionDirectionDifferential_apply {d : ℕ} (x w : PDE.Vec d) :
    positionDirectionDifferential x w =
      (PDE.vecEuclideanNorm x)⁻¹ •
        (w - PDE.vecDot (positionDirection x) w • positionDirection x) := by
  simp [positionDirectionDifferential, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, positionRadiusDifferential_apply, positionDirection, smul_sub, smul_smul]
  ext i
  simp
  ring





/-- The full joint derivative splits into the two literal slice derivatives. -/
theorem fderiv_uncurry_split {d : ℕ} (phi : PDE.Vec d → PDE.Vec d → ℝ)
    (y e u w : PDE.Vec d) (hphi : DifferentiableAt ℝ (Function.uncurry phi) (y, e)) :
    fderiv ℝ (Function.uncurry phi) (y, e) (u, w) =
      fderiv ℝ (fun z => phi z e) y u + fderiv ℝ (fun z => phi y z) e w := by
  have hiy : HasFDerivAt (fun z => (z, e))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
        0) y := by
    convert (hasFDerivAt_id (𝕜 := ℝ) y).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) e y) using 1
    funext z
    rfl
  have hie : HasFDerivAt (fun z => (y, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod
        (ContinuousLinearMap.id ℝ (PDE.Vec d))) e := by
    convert (hasFDerivAt_const (𝕜 := ℝ) y e).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) e) using 1
    funext z
    rfl
  have hy' : HasFDerivAt (fun z => phi z e)
      ((fderiv ℝ (Function.uncurry phi) (y, e)).comp
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod 0)) y := by
    convert (hphi.hasFDerivAt.comp y hiy) using 1
    funext z
    rfl
  have he' : HasFDerivAt (fun z => phi y z)
      ((fderiv ℝ (Function.uncurry phi) (y, e)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))) e := by
    convert (hphi.hasFDerivAt.comp e hie) using 1
    funext z
    rfl
  rw [hy'.fderiv, he'.fderiv]
  have hsplit : (u, w) = ((u, 0) : PDE.Vec d × PDE.Vec d) + (0, w) := by simp
  rw [hsplit, map_add]
  simp



/-- The exact position derivative gives the angular expression before transport contraction. -/
theorem fderiv_homogeneousAnsatz_position {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v w : PDE.Vec d) (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    fderiv ℝ (fun z => homogeneousAnsatz alpha phi z v) x w =
      Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
        (PDE.vecDot (positionDirection x) w *
          (alpha / 3 * phi (normalizedVelocity x v) (positionDirection x) -
            (1 / 3 : ℝ) * fderiv ℝ (fun z => phi z (positionDirection x))
              (normalizedVelocity x v) (normalizedVelocity x v)) +
          fderiv ℝ (fun z => phi (normalizedVelocity x v) z) (positionDirection x)
            (w - PDE.vecDot (positionDirection x) w • positionDirection x))    := by
  let normalizedVelocityDifferential {d : ℕ} (x : PDE.Vec d) (v : PDE.Vec d) :=
    (((-(1 / 3 : ℝ)) * Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ) - 1)) •
        positionRadiusDifferential x).smulRight v
  have hasFDerivAt_homogeneousAnsatz_position :
      HasFDerivAt (fun z => homogeneousAnsatz alpha phi z v)
      ((phi (normalizedVelocity x v) (positionDirection x)) •
          ((alpha / 3 * Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1)) •
            positionRadiusDifferential x) +
        (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3)) •
          (fderiv ℝ (Function.uncurry phi) (normalizedVelocity x v, positionDirection x)).comp
            ((normalizedVelocityDifferential x v).prod (positionDirectionDifferential x))) x := by
    have hasFDerivAt_positionRadius :
        HasFDerivAt (PDE.vecEuclideanNorm (d := d)) (positionRadiusDifferential x) x := by
      have hb : HasFDerivAt (PDE.vecNormSq (d := d)) (2 • seedDotLinear x) x := by
        simpa [seedBase, zero_pow (by norm_num : 2 ≠ 0)]
          using hasFDerivAt_seedBase 0 x 0
      convert hb.sqrt (PDE.vecNormSq_eq_zero_iff.not.mpr hx) using 1
      · rfl
      · ext w
        simp [positionRadiusDifferential, PDE.vecEuclideanNorm, smul_apply, two_smul, add_apply]
        field_simp
        ring
    have hasFDerivAt_normalizedVelocity :
        HasFDerivAt (fun z => normalizedVelocity z v) (normalizedVelocityDifferential x v) x := by
      exact ((hasFDerivAt_positionRadius).rpow_const
        (p := -(1 / 3 : ℝ)) (Or.inl (PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx))).smul_const v
    have hasFDerivAt_positionDirection :
        HasFDerivAt (positionDirection (d := d)) (positionDirectionDifferential x) x := by
      have hr := (hasDerivAt_inv (PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx)).comp_hasFDerivAt
        x (hasFDerivAt_positionRadius)
      convert hr.smul (hasFDerivAt_id x) using 1
      · rfl
      · simp only [positionDirectionDifferential, Function.comp_apply, id_eq, inv_pow]
    have hr := (hasFDerivAt_positionRadius).rpow_const
      (p := alpha / 3) (Or.inl (PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx))
    have hcoord := (hasFDerivAt_normalizedVelocity).prodMk
      (hasFDerivAt_positionDirection)
    convert hr.mul (hphi.hasFDerivAt.comp x hcoord) using 1
    · rfl
    · ext w
      simp
      ring
  have normalizedVelocityDifferential_apply :
      normalizedVelocityDifferential x v w =
      (-(1 / 3 : ℝ) * (PDE.vecEuclideanNorm x)⁻¹ *
        PDE.vecDot (positionDirection x) w) • normalizedVelocity x v := by
    have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
    have hp : Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ) - 1) =
        (PDE.vecEuclideanNorm x)⁻¹ * Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) := by
      simp
      rw [Real.rpow_sub hr, Real.rpow_one]
      ring
    simp only [normalizedVelocityDifferential, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, positionRadiusDifferential_apply, normalizedVelocity,
      smul_smul, hp]
    congr 1
    ring
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      (PDE.vecEuclideanNorm x)⁻¹ =
      Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub (PDE.vecEuclideanNorm_pos_iff.mpr hx), Real.rpow_one]
    simp only [div_eq_mul_inv]
  rw [(hasFDerivAt_homogeneousAnsatz_position).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, positionRadiusDifferential_apply,
    normalizedVelocityDifferential_apply, positionDirectionDifferential_apply]
  rw [fderiv_uncurry_split phi _ _ _ _ hphi, map_smul, map_smul]
  simp only [smul_eq_mul]
  simp only [Real.rpow_eq_pow] at hp ⊢
  linear_combination
    (PDE.vecDot (positionDirection x) w *
      (-(1 / 3 : ℝ) * fderiv ℝ (fun z => phi z (positionDirection x))
        (normalizedVelocity x v) (normalizedVelocity x v)) +
      fderiv ℝ (fun z => phi (normalizedVelocity x v) z) (positionDirection x)
        (w - PDE.vecDot (positionDirection x) w • positionDirection x)) * hp

/-- Transport and the velocity Hessian have the identical kinetic prefactor. -/
theorem homogeneousAnsatz_transport {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    fderiv ℝ (fun z => homogeneousAnsatz alpha phi z v) x v =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) *
        ansatzTransport alpha phi (normalizedVelocity x v) (positionDirection x)  := by
  have velocity_eq_cubeRoot_smul :
      v = Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) • normalizedVelocity x v := by
    have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
    unfold normalizedVelocity
    rw [smul_smul]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hr]
    norm_num
  have hv := velocity_eq_cubeRoot_smul
  have hdot : PDE.vecDot (positionDirection x) v =
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) *
        PDE.vecDot (normalizedVelocity x v) (positionDirection x) := by
    conv_lhs => rhs; rw [hv]
    unfold PDE.vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htangent : v - PDE.vecDot (positionDirection x) v • positionDirection x =
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) •
        (normalizedVelocity x v -
          PDE.vecDot (normalizedVelocity x v) (positionDirection x) • positionDirection x) := by
    rw [hdot, smul_sub, smul_smul, ← hv]
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (PDE.vecEuclideanNorm_pos_iff.mpr hx)]
    congr 1
    ring
  rw [fderiv_homogeneousAnsatz_position alpha phi x v v hx hphi, htangent, hdot, map_smul]
  simp only [smul_eq_mul]
  calc
    _ = (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
        Real.rpow (PDE.vecEuclideanNorm x) (1 / 3)) *
        ansatzTransport alpha phi (normalizedVelocity x v) (positionDirection x) := by
      unfold ansatzTransport
      ring
    _ = _ := by rw [hp]


/-- The homogeneous cutoff ansatz has the literal source velocity-Hessian scaling. -/
theorem homogeneousAnsatz_velocity_hessian {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (x v w u : PDE.Vec d) (hx : x ≠ 0) :
    fderiv ℝ (fun z => fderiv ℝ
      (fun a => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x a) z w) v u =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) *
        fderiv ℝ (fun z => fderiv ℝ
          (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) z w)
          (normalizedVelocity x v) u := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
      (contDiff_id.prodMk contDiff_const)
  have heq : (fun a => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x a) =
      (fun a => Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
        cutoffProfile alpha C₀ sigma R
          (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) • a) (positionDirection x)) := by
    funext a
    rfl
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) ^ 2 =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    congr 1
    norm_num
    ring
  rw [heq]
  have hh := hessian_scaledFunction _ hF
    (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3))
    (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ))) v w u
  rw [hp] at hh
  exact hh


/-- The literal profile with the source's extension at zero position. -/
def geometricProfile {d : ℕ} (alpha C₀ sigma R : ℝ) (q : PDE.Vec d × PDE.Vec d) : ℝ :=
  if q.1 = 0 then radialProfile alpha q.2 else
    homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) q.1 q.2

/-- The profile vanishes at the joint origin for positive homogeneity degree. -/
theorem geometricProfile_zero (d : ℕ) (alpha C₀ sigma R : ℝ) (ha : 0 < alpha) :
    geometricProfile (d := d) alpha C₀ sigma R 0 = 0 := by
  simp [geometricProfile, radialProfile, PDE.vecNormSq, PDE.vecDot, Real.rpow_eq_pow,
    Real.zero_rpow (ne_of_gt (div_pos ha (by norm_num : (0 : ℝ) < 2)))]

/-- The literal radial profile scales by the exact power alpha under positive dilation. -/
theorem radialProfile_smul {d : ℕ} (alpha r : ℝ) (hr : 0 < r) (v : PDE.Vec d) :
    radialProfile alpha (r • v) = Real.rpow r alpha * radialProfile alpha v := by
  unfold radialProfile
  rw [PDE.vecNormSq_smul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (sq_nonneg r) (PDE.vecNormSq_nonneg v),
    ← Real.rpow_natCast_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

/-- The extended profile has exact kinetic homogeneity, including both axes. -/
theorem geometricProfile_homogeneous {d : ℕ} (alpha C₀ sigma R r : ℝ) (hr : 0 < r)
    (q : PDE.Vec d × PDE.Vec d) :
    geometricProfile alpha C₀ sigma R (r ^ 3 • q.1, r • q.2) =
      Real.rpow r alpha * geometricProfile alpha C₀ sigma R q := by
  have hzero : r ^ 3 • q.1 = 0 ↔ q.1 = 0 :=
    smul_eq_zero_iff_right (pow_ne_zero 3 hr.ne')
  unfold geometricProfile
  by_cases hx : q.1 = 0
  · simp only [hx, smul_zero, ite_true]
    exact radialProfile_smul alpha r hr q.2
  · simp only [hx, hzero.not.mpr hx, ite_false]
    exact homogeneousAnsatz_dilate alpha r hr _ q.1 q.2

/-- The extended profile is positive at every nonzero kinetic point. -/
theorem geometricProfile_pos {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hC₀ : 0 ≤ C₀) (hsigma : 0 < sigma) (hR : 0 < R)
    (q : PDE.Vec d × PDE.Vec d) (hq : q ≠ 0) :
    0 < geometricProfile alpha C₀ sigma R q := by
  unfold geometricProfile
  split_ifs with hx
  · apply radialProfile_pos
    intro hv
    exact hq (Prod.ext hx hv)
  · apply mul_pos
    · exact Real.rpow_pos_of_pos (PDE.vecEuclideanNorm_pos_iff.mpr hx) _
    · exact cutoffProfile_pos alpha C₀ sigma R hC₀ hsigma hR _ _

/-- Exterior interpolation cancels all position dependence of the ansatz exactly. -/
theorem homogeneousAnsatz_eq_radial {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (x v : PDE.Vec d) (hx : x ≠ 0)
    (hout : 2 * R ≤ PDE.vecEuclideanNorm (normalizedVelocity x v)) :
    homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x v = radialProfile alpha v := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  unfold homogeneousAnsatz
  rw [cutoffProfile_eq_radial alpha C₀ sigma R hR _ _ hout]
  unfold radialProfile normalizedVelocity
  rw [PDE.vecNormSq_smul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (sq_nonneg _) (PDE.vecNormSq_nonneg v),
    ← Real.rpow_natCast_mul (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  rw [← mul_assoc, ← Real.rpow_add hr]
  have he : alpha / 3 + (-(1 / 3 : ℝ) * (2 * (alpha / 2))) = 0 := by ring
  rw [he, Real.rpow_zero, one_mul]

/-- The physical outer-region condition forces exact radial agreement. -/
theorem geometricProfile_eq_radial_of_outer {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (q : PDE.Vec d × PDE.Vec d)
    (hout : 2 * R * Real.rpow (PDE.vecEuclideanNorm q.1) (1 / 3) ≤
      PDE.vecEuclideanNorm q.2) :
    geometricProfile alpha C₀ sigma R q = radialProfile alpha q.2 := by
  by_cases hx : q.1 = 0
  · simp [geometricProfile, hx]
  · rw [geometricProfile, ite_eq_right hx]
    apply homogeneousAnsatz_eq_radial alpha C₀ sigma R hR q.1 q.2 hx
    have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
    have hp : 0 < Real.rpow (PDE.vecEuclideanNorm q.1) (1 / 3) :=
      Real.rpow_pos_of_pos hr _
    unfold normalizedVelocity
    simp only [Real.rpow_eq_pow] at hp hout ⊢
    rw [PDE.vecEuclideanNorm_smul,
      abs_of_pos (Real.rpow_pos_of_pos hr (-(1 / 3 : ℝ)))]
    rw [Real.rpow_neg hr.le]
    simpa only [div_eq_mul_inv, mul_comm] using ((le_div_iff₀ hp).mpr hout)

/-- The ansatz of the actual smooth cutoff is smooth at every nonzero position. -/
theorem contDiffAt_cutoffAnsatz {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : PDE.Vec d × PDE.Vec d) (hx : q.1 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : PDE.Vec d × PDE.Vec d =>
        homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) z.1 z.2) q := by
  have hnorm := PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx
  have hr :=
    (PDE.contDiff_vecNormSq.comp contDiff_fst).contDiffAt.sqrt (PDE.vecNormSq_eq_zero_iff.not.mpr hx)
  exact (hr.rpow_const_of_ne (p := alpha / 3) hnorm).mul
    ((contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).contDiffAt.comp q (((hr.rpow_const_of_ne (p := -(1 / 3 : ℝ)) hnorm).smul contDiffAt_snd).prodMk ((hr.inv hnorm).smul contDiffAt_fst)))

/-- The literal extension is smooth everywhere except the joint origin. -/
theorem geometricProfile_smooth_off_origin {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (geometricProfile (d := d) alpha C₀ sigma R) ({0}ᶜ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hx : q.1 = 0
  · have hv : q.2 ≠ 0 := by
      intro hv
      apply hq
      exact Set.mem_singleton_iff.mpr (Prod.ext hx hv)
    have hr : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => radialProfile alpha z.2) q :=
      (PDE.contDiff_vecNormSq.comp contDiff_snd).contDiffAt.rpow_const_of_ne
        (PDE.vecNormSq_eq_zero_iff.not.mpr hv)
    have hc : Continuous (fun z : PDE.Vec d × PDE.Vec d =>
        2 * R * Real.rpow (PDE.vecEuclideanNorm z.1) (1 / 3)) := by
      apply continuous_const.mul
      exact (PDE.continuous_vecEuclideanNorm.comp continuous_fst).rpow_const
        (fun _ => Or.inr (by norm_num))
    have hmem : q ∈ {z : PDE.Vec d × PDE.Vec d |
        2 * R * Real.rpow (PDE.vecEuclideanNorm z.1) (1 / 3) <
          PDE.vecEuclideanNorm z.2} := by
      simpa [hx, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Real.rpow_eq_pow]
        using PDE.vecEuclideanNorm_pos_iff.mpr hv
    apply hr.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hc (PDE.continuous_vecEuclideanNorm.comp continuous_snd)).mem_nhds hmem] with z hz
    exact geometricProfile_eq_radial_of_outer alpha C₀ sigma R hR z hz.le
  · apply (contDiffAt_cutoffAnsatz alpha C₀ sigma R hsigma hR q hx).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually_ne hx] with z hz
    simp only [geometricProfile, ite_eq_right hz]


/-- The unit kinetic gauge shell is compact in native coordinates. -/
theorem isCompact_unitGaugeShell (d : ℕ) : IsCompact {q : XV d | rho q = 1} :=
  (isCompact_rho_sublevel d 1).of_isClosed_subset
    (isClosed_eq (continuous_rho d) continuous_const) (fun _ h => le_of_eq h)

/-- Positive-degree homogeneity transports shell bounds to every nonzero kinetic point. -/
theorem homogeneous_profile_comparison {d : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (H : XV d → ℝ) (hzero : H 0 = 0)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hpos : ∀ q, q ≠ 0 → 0 < H q)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q,
      c * Real.rpow (rho q) alpha ≤ H q ∧ H q ≤ C * Real.rpow (rho q) alpha := by
  let K : Set (XV d) := {q | rho q = 1}
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hzeroq
    have hh : rho q = 1 := hq
    simp [hzeroq] at hh
  obtain ⟨c, C, hc, hcC, hbound⟩ := exists_positive_bounds_on_compact K
    (isCompact_unitGaugeShell d) H (hsmooth.continuousOn.mono (fun q hq => hKnz q hq)) (fun q hq => hpos q (hKnz q hq))
  refine ⟨c, C, hc, hcC, ?_⟩
  intro q
  by_cases hq : q = 0
  · subst q
    simp only [rho_zero, hzero, Real.rpow_eq_pow, Real.zero_rpow ha.ne', mul_zero, le_refl,
      and_self]
  · have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
    let p := dilate (rho q)⁻¹ q
    have hp : p ∈ K := by
      change rho (dilate (rho q)⁻¹ q) = 1
      rw [rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have hpR : Real.rpow (rho q) alpha * Real.rpow (rho q)⁻¹ alpha = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.inv_rpow hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr alpha).ne']
    have hH : H q = Real.rpow (rho q) alpha * H p := by
      dsimp [p]
      rw [(hhom (rho q)⁻¹ (inv_pos.mpr hr) q)]
      simp only [Real.rpow_eq_pow] at hpR ⊢
      rw [← mul_assoc, hpR, one_mul]
    obtain ⟨hlo, hhi⟩ := hbound p hp
    rw [hH]
    have hnonneg := (Real.rpow_pos_of_pos hr alpha).le
    constructor
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hlo hnonneg
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hhi hnonneg

/-- The actual profile is quantitatively comparable with the source kinetic gauge power. -/
theorem geometricProfile_comparison {d : ℕ} (alpha C₀ sigma R : ℝ) (ha : 0 < alpha)
    (hC₀ : 0 ≤ C₀) (hsigma : 0 < sigma) (hR : 0 < R) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV d,
      c * Real.rpow (rho q) alpha ≤ geometricProfile alpha C₀ sigma R q ∧
      geometricProfile alpha C₀ sigma R q ≤ C * Real.rpow (rho q) alpha := by
  apply homogeneous_profile_comparison alpha ha (geometricProfile alpha C₀ sigma R)
    (geometricProfile_zero d alpha C₀ sigma R ha)
    (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
    (geometricProfile_pos alpha C₀ sigma R hC₀ hsigma hR)
  exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q


/-- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dilate r q ≠ 0 := by
  intro hzero
  exact hq (Prod.ext ((smul_eq_zero_iff_right (pow_ne_zero 3 hr.ne')).mp (congrArg Prod.fst hzero))
    ((smul_eq_zero_iff_right hr.ne').mp (congrArg Prod.snd hzero)))

/-- The derivative of a homogeneous smooth function has the source velocity weight. -/
theorem homogeneous_velocity_jet {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ H (dilate r q) (0, w) =
      Real.rpow r (alpha - 1) * fderiv ℝ H q (0, w) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hother : HasFDerivAt (fun z => H (dilate r z))
      (Real.rpow r alpha • fderiv ℝ H q) q := by
    convert hqd.hasFDerivAt.const_mul (Real.rpow r alpha) using 1
    funext z
    exact hhom r hr z
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, w)) ((hrqd.hasFDerivAt.comp q hd).unique hother)
  have hsmul : (0, r • w) = r • ((0, w) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (alpha - 1) = Real.rpow r alpha / r := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
  rw [hpower]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using heq

/-- The native selector vector has the same exact velocity homogeneity. -/
theorem homogeneous_dv {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dv H (dilate r q) = Real.rpow r (alpha - 1) • dv H q := by
  ext i
  exact homogeneous_velocity_jet alpha H hsmooth hhom r hr q hq (Pi.single i 1)

/-- Smooth homogeneous profiles satisfy the source velocity-gradient bound. -/
theorem homogeneous_velocity_gradient_bound {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) :
    ∃ C : ℝ, 0 < C ∧ ∀ q, q ≠ 0 →
      PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1) := by
  let K : Set (XV d) := {q | rho q = 1}
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hz
    have hh : rho q = 1 := hq
    simp [hz] at hh
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hd : ContinuousOn (fun q => PDE.vecEuclideanNorm (dv H q)) K := by
    apply PDE.continuous_vecEuclideanNorm.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    have hc := (hsmooth.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
      (continuousOn_const (c := ((0, Pi.single i 1) : XV d)))
    exact hc.mono (fun q hq => hKnz q hq)
  obtain ⟨B, hB⟩ := (isCompact_unitGaugeShell d).bddAbove_image hd
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq
  have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  let p := dilate (rho q)⁻¹ q
  have hp : p ∈ K := by
    change rho (dilate (rho q)⁻¹ q) = 1
    rw [rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hqp : dilate (rho q) p = q := by
    dsimp [p]
    rw [dilate_mul, mul_inv_cancel₀ hr.ne', dilate_one]
  have hj := homogeneous_dv alpha H hsmooth hhom (rho q) hr p (hKnz p hp)
  rw [hqp] at hj
  rw [hj, PDE.vecEuclideanNorm_smul]
  have hpow := Real.rpow_pos_of_pos hr (alpha - 1)
  simp only [Real.rpow_eq_pow] at hpow ⊢
  rw [abs_of_pos hpow]
  have hb : PDE.vecEuclideanNorm (dv H p) ≤ C :=
    (hB ⟨p, hp, rfl⟩).trans (le_max_right _ _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hpow.le

/-- The actual profile satisfies the required velocity-gradient estimate. -/
theorem geometricProfile_velocity_gradient_bound {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (dv (geometricProfile alpha C₀ sigma R) q) ≤
        C * Real.rpow (rho q) (alpha - 1) := by
  apply homogeneous_velocity_gradient_bound alpha (geometricProfile alpha C₀ sigma R)
    (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
  exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q


/-- The native full-product velocity derivative agrees with its literal slice derivative. -/
theorem fderiv_velocity_slice {d : ℕ} (H : XV d → ℝ) (x v w : PDE.Vec d)
    (hH : DifferentiableAt ℝ H (x, v)) :
    fderiv ℝ (fun z => H (x, z)) v w = fderiv ℝ H (x, v) (0, w) := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (x, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d))) v := by
    convert (hasFDerivAt_const (𝕜 := ℝ) x v).prodMk (hasFDerivAt_id (𝕜 := ℝ) v) using 1
    funext z
    rfl
  have hh' : HasFDerivAt (fun z => H (x, z))
      ((fderiv ℝ H (x, v)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))) v := by
    convert (hH.hasFDerivAt.comp v hi) using 1
    funext z
    rfl
  rw [hh'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- Scalar evaluation of the full first derivative gives its literal second derivative. -/
theorem full_secondDirectional_eq {d : ℕ} (H : XV d → ℝ) (q u w : XV d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) :
    fderiv ℝ (fun z => fderiv ℝ H z w) q u = fderiv ℝ (fderiv ℝ H) q u w := by
  have hd := (hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- A smooth full-product velocity Hessian agrees with the literal velocity slice Hessian. -/
theorem full_velocity_hessian_eq_slice {d : ℕ} (H : XV d → ℝ) (x v w u : PDE.Vec d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H (x, v)) :
    fderiv ℝ (fun z => fderiv ℝ H z (0, w)) (x, v) (0, u) =
      fderiv ℝ (fun z => fderiv ℝ (fun a => H (x, a)) z w) v u := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (x, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d))) v := by
    convert (hasFDerivAt_const (𝕜 := ℝ) x v).prodMk (hasFDerivAt_id (𝕜 := ℝ) v) using 1
    funext z
    rfl
  have hd := ((hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (contDiffAt_const (c := ((0, w) : XV d)))).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp v hi
  have hevent : (fun z => fderiv ℝ (fun a => H (x, a)) z w) =ᶠ[nhds v]
      (fun z => fderiv ℝ H (x, z) (0, w)) := by
    have hc : Continuous (fun z : PDE.Vec d => (x, z)) := by fun_prop
    have hreg := hc.continuousAt.eventually ((hH.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
      simp)).eventually (by simp))
    filter_upwards [hreg] with z hz
    exact fderiv_velocity_slice H x z w (hz.differentiableAt (by norm_num))
  rw [hevent.fderiv_eq (𝕜 := ℝ)]
  have hh' : HasFDerivAt (fun z => fderiv ℝ H (x, z) (0, w))
      ((fderiv ℝ (fun z => fderiv ℝ H z (0, w)) (x, v)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))) v := by
    convert hh using 1
    funext z
    rfl
  rw [hh'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- The full-product position derivative agrees with its literal position slice. -/
theorem fderiv_position_slice {d : ℕ} (H : XV d → ℝ) (x v w : PDE.Vec d)
    (hH : DifferentiableAt ℝ H (x, v)) :
    fderiv ℝ (fun z => H (z, v)) x w = fderiv ℝ H (x, v) (w, 0) := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (z, v))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod 0) x := by
    convert (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) v x) using 1
    funext z
    rfl
  have hh' : HasFDerivAt (fun z => H (z, v))
      ((fderiv ℝ H (x, v)).comp
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
          0)) x := by
    convert (hH.hasFDerivAt.comp x hi) using 1
    funext z
    rfl
  rw [hh'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- Native position selectors conditions to the full directional transport derivative. -/
theorem transport_eq_direction {d : ℕ} (H : XV d → ℝ) (q : XV d) :
    PDE.vecDot q.2 (dx H q) = fderiv ℝ H q (q.2, 0) := by
  have heq : (q.2, 0) =
      ∑ i : Fin d, q.2 i • ((Pi.single i 1, 0) : XV d) := by
    apply Prod.ext
    · ext k
      simp [Prod.fst_sum, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [heq, map_sum]
  simp only [map_smul, smul_eq_mul, dx, PDE.vecDot]

/-- The local full-product Hessian matrix is Hermitian at every smooth point. -/
theorem dvv_isHermitian {d : ℕ} (H : XV d → ℝ) (q : XV d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) : (dvv H q).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i k
  change fderiv ℝ (fun z => fderiv ℝ H z (0, Pi.single i 1)) q (0, Pi.single k 1) =
    fderiv ℝ (fun z => fderiv ℝ H z (0, Pi.single k 1)) q (0, Pi.single i 1)
  rw [full_secondDirectional_eq H q _ _ hH, full_secondDirectional_eq H q _ _ hH]
  exact (hH.isSymmSndFDerivAt (by simp)).eq _ _

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

