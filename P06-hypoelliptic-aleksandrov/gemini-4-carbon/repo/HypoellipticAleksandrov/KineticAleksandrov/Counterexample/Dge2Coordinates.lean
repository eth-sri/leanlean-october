module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import Mathlib.Tactic.FieldSimp

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped BigOperators


/-- The positive quantity inside the seed's real power. -/
def seedBase {d : ℕ} (sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  sigma ^ 2 + PDE.vecNormSq (y - e)

/-- The literal seed of Appendix C. -/
def seed {d : ℕ} (alpha C₀ sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  C₀ + Real.rpow (seedBase sigma y e) (alpha / 2)

/-- The seed base is strictly positive when the regularization parameter is positive. -/
theorem seedBase_pos {d : ℕ} (sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) : 0 < seedBase sigma y e := by
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hsigma) (PDE.vecNormSq_nonneg _)

/-- The literal seed is positive for a nonnegative additive constant. -/
theorem seed_pos {d : ℕ} (alpha C₀ sigma : ℝ) (hC₀ : 0 ≤ C₀)
    (hsigma : 0 < sigma) (y e : PDE.Vec d) : 0 < seed alpha C₀ sigma y e := by
  exact add_pos_of_nonneg_of_pos hC₀ (Real.rpow_pos_of_pos
    (seedBase_pos sigma hsigma y e) _)

/-- The regularized seed is smooth jointly in its two native vector variables. -/
theorem contDiff_seed {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => seed alpha C₀ sigma q.1 q.2) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => seedBase sigma q.1 q.2) := by
    unfold seedBase PDE.vecNormSq PDE.vecDot
    fun_prop
  exact contDiff_const.add (hb.rpow_const_of_ne fun q =>
    (seedBase_pos sigma hsigma q.1 q.2).ne')

/-- The tangential Hessian eigenvalue of the seed. -/
def seedTangentialEigenvalue {d : ℕ} (alpha sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1)

/-- The radial Hessian eigenvalue of the seed. -/
def seedRadialEigenvalue {d : ℕ} (alpha sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 2) *
    (sigma ^ 2 - (1 - alpha) * PDE.vecNormSq (y - e))

/-- The tangential seed eigenvalue is strictly positive. -/
theorem seedTangentialEigenvalue_pos {d : ℕ} (alpha sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d) :
    0 < seedTangentialEigenvalue alpha sigma y e := by
  exact mul_pos ha (Real.rpow_pos_of_pos (seedBase_pos sigma hsigma y e) _)

/-- The radial seed eigenvalue is negative precisely past the source threshold. -/
theorem seedRadialEigenvalue_neg_iff {d : ℕ} (alpha sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d) :
    seedRadialEigenvalue alpha sigma y e < 0 ↔
      sigma ^ 2 < (1 - alpha) * PDE.vecNormSq (y - e) := by
  unfold seedRadialEigenvalue
  have hp := mul_pos ha
    (Real.rpow_pos_of_pos (seedBase_pos sigma hsigma y e) (alpha / 2 - 2))
  simp
  rw [mul_neg_iff]
  simp [hp, hp.not_gt, sub_neg]

/-- The Euclidean dot product with a fixed vector as a continuous linear map. -/
def seedDotLinear {d : ℕ} (z : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, z i • ContinuousLinearMap.proj i

/-- Evaluation of the dot-product continuous linear map. -/
theorem seedDotLinear_apply {d : ℕ} (z w : PDE.Vec d) :
    seedDotLinear z w = PDE.vecDot z w := by
  simp [seedDotLinear, PDE.vecDot]

/-- The exact Frechet derivative of the seed base. -/
theorem hasFDerivAt_seedBase {d : ℕ} (sigma : ℝ) (y e : PDE.Vec d) :
    HasFDerivAt (fun z => seedBase sigma z e) (2 • seedDotLinear (y - e)) y := by
  have hi (i : Fin d) : HasFDerivAt (fun z => (z i - e i) ^ 2)
      ((2 * (y i - e i)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i) y := by
    convert ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ => ℝ) i y).sub_const
      (e i)).pow 2 using 1
    simp
  convert (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_add (sigma ^ 2) using 1
  · simp [seedBase, PDE.vecNormSq_eq_sum_sq]
  · ext w
    simp [seedDotLinear, Finset.mul_sum, mul_assoc]

/-- The exact first derivative of the seed with respect to its velocity variable. -/
theorem hasFDerivAt_seed {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    HasFDerivAt (fun z => seed alpha C₀ sigma z e)
      ((alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1)) •
        seedDotLinear (y - e)) y := by
  convert (((hasFDerivAt_seedBase sigma y e).rpow_const (p := alpha / 2) (Or.inl (seedBase_pos sigma hsigma y e).ne')).const_add C₀) using 1
  · rfl
  · ext w
    simp
    ring

/-- The first seed derivative applied to a native vector. -/
theorem fderiv_seed_apply {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w : PDE.Vec d) :
    fderiv ℝ (fun z => seed alpha C₀ sigma z e) y w =
      alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
        PDE.vecDot (y - e) w := by
  rw [(hasFDerivAt_seed alpha C₀ sigma hsigma y e).fderiv]
  simp [smul_apply, seedDotLinear_apply]

/-- The rank-one expression for the seed's velocity Hessian. -/
def seedHessianForm {d : ℕ} (alpha sigma : ℝ) (y e w u : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) * PDE.vecDot w u +
    alpha * (alpha - 2) * Real.rpow (seedBase sigma y e) (alpha / 2 - 2) *
      PDE.vecDot (y - e) w * PDE.vecDot (y - e) u

/-- The differentiated seed first derivative, with an explicit linear-map value. -/
theorem hasFDerivAt_seed_first {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w : PDE.Vec d) :
    HasFDerivAt (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w)
      ((PDE.vecDot (y - e) w *
          (alpha * (alpha - 2) * Real.rpow (seedBase sigma y e) (alpha / 2 - 2))) •
        seedDotLinear (y - e) +
        (alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1)) • seedDotLinear w)
      y := by
  have hd : HasFDerivAt (fun z => PDE.vecDot (z - e) w) (seedDotLinear w) y := by
    have hh := ((seedDotLinear w).hasFDerivAt (x := y)).sub_const (PDE.vecDot w e)
    convert hh using 1
    ext z
    simp [seedDotLinear_apply, PDE.vecDot, mul_sub, Finset.sum_sub_distrib, mul_comm]
  have hh := (((hasFDerivAt_seedBase sigma y e).rpow_const (p := alpha / 2 - 1) (Or.inl (seedBase_pos sigma hsigma y e).ne')).const_mul alpha).mul hd
  have hexp : alpha / 2 - 1 - 1 = alpha / 2 - 2 := by ring
  convert hh using 1
  · ext z
    exact fderiv_seed_apply alpha C₀ sigma hsigma z e w
  · ext u
    simp
    ring

/-- The exact seed Hessian, evaluated on two arbitrary native directions. -/
theorem seed_hessian {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w u : PDE.Vec d) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y u =
      seedHessianForm alpha sigma y e w u := by
  rw [(hasFDerivAt_seed_first alpha C₀ sigma hsigma y e w).fderiv]
  simp [seedHessianForm, smul_apply, add_apply, seedDotLinear_apply]
  ring

/-- The seed Hessian has its stated tangential eigenvalue on orthogonal directions. -/
theorem seed_hessian_tangent {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w u : PDE.Vec d) (hw : PDE.vecDot (y - e) w = 0) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y u =
      seedTangentialEigenvalue alpha sigma y e * PDE.vecDot w u := by
  rw [seed_hessian alpha C₀ sigma hsigma]
  simp [seedHessianForm, seedTangentialEigenvalue, hw]

/-- The seed Hessian has its stated radial eigenvalue on the translated radial vector. -/
theorem seed_hessian_radial {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e u : PDE.Vec d) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z (y - e)) y u =
      seedRadialEigenvalue alpha sigma y e * PDE.vecDot (y - e) u := by
  rw [seed_hessian alpha C₀ sigma hsigma]
  have hpower : Real.rpow (seedBase sigma y e) (alpha / 2 - 1) =
      Real.rpow (seedBase sigma y e) (alpha / 2 - 2) * seedBase sigma y e := by
    simp
    calc
      seedBase sigma y e ^ (alpha / 2 - 1) =
          seedBase sigma y e ^ ((alpha / 2 - 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (seedBase_pos sigma hsigma y e), Real.rpow_one]
  simp only [seedHessianForm, seedRadialEigenvalue, hpower, PDE.vecNormSq]
  unfold seedBase PDE.vecNormSq
  ring

/-- The ambient sphere-direction derivative of the seed is the negative velocity jet. -/
theorem fderiv_seed_sphere_apply {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w : PDE.Vec d) :
    fderiv ℝ (fun a => seed alpha C₀ sigma y a) e w =
      -(alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
        PDE.vecDot (y - e) w) := by
  have hsym (a b : PDE.Vec d) : seed alpha C₀ sigma a b = seed alpha C₀ sigma b a := by
    unfold seed seedBase
    rw [show a - b = -(b - a) by abel, PDE.vecNormSq_neg]
  have hf : (fun a => seed alpha C₀ sigma y a) =
      (fun a => seed alpha C₀ sigma a y) := by
    funext a
    exact hsym y a
  rw [hf, fderiv_seed_apply alpha C₀ sigma hsigma]
  have hdot : PDE.vecDot (e - y) w = -PDE.vecDot (y - e) w := by
    simp only [PDE.vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hdot]
  have hbase : seedBase sigma e y = seedBase sigma y e := by
    unfold seedBase
    rw [show e - y = -(y - e) by abel, PDE.vecNormSq_neg]
  rw [hbase]
  ring


/-- The unit Euclidean position direction, defined by the literal normalization. -/
def positionDirection {d : ℕ} (x : PDE.Vec d) : PDE.Vec d :=
  (PDE.vecEuclideanNorm x)⁻¹ • x

/-- Velocity normalized by the cube root of the Euclidean position radius. -/
def normalizedVelocity {d : ℕ} (x v : PDE.Vec d) : PDE.Vec d :=
  Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) • v

/-- The literal homogeneous ansatz on nonzero positions. -/
def homogeneousAnsatz {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) : ℝ :=
  Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
    phi (normalizedVelocity x v) (positionDirection x)

/-- The source transport expression, using the ambient derivative in a tangent direction. -/
def ansatzTransport {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (y e : PDE.Vec d) : ℝ :=
  PDE.vecDot y e * (alpha / 3 * phi y e -
    (1 / 3 : ℝ) * fderiv ℝ (fun z => phi z e) y y) +
    fderiv ℝ (fun a => phi y a) e (y - PDE.vecDot y e • e)

/-- Normalizing a nonzero position gives a Euclidean unit vector. -/
theorem positionDirection_normSq {d : ℕ} (x : PDE.Vec d) (hx : x ≠ 0) :
    PDE.vecNormSq (positionDirection x) = 1 := by
  have hp := PDE.vecEuclideanNorm_pos_iff.mpr hx
  unfold positionDirection
  rw [PDE.vecNormSq_smul, ← PDE.vecEuclideanNorm_sq]
  field_simp



/-- The homogeneous ansatz has the exact kinetic scaling of Appendix C. -/
theorem homogeneousAnsatz_dilate {d : ℕ} (alpha r : ℝ) (hr : 0 < r)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) :
    homogeneousAnsatz alpha phi (r ^ 3 • x) (r • v) =
      Real.rpow r alpha * homogeneousAnsatz alpha phi x v   := by
  have normalizedVelocity_dilate {d : ℕ} (x : PDE.Vec d) (v : PDE.Vec d) :
      normalizedVelocity (r ^ 3 • x) (r • v) = normalizedVelocity x v := by
    unfold normalizedVelocity
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)]
    simp
    rw [Real.mul_rpow (pow_nonneg hr.le 3) (PDE.vecEuclideanNorm_nonneg x),
      ← Real.rpow_natCast_mul hr.le]
    norm_num
    rw [Real.rpow_neg_one, smul_smul]
    congr 1
    field_simp
  have positionDirection_dilate {d : ℕ} (x : PDE.Vec d) :
      positionDirection (r ^ 3 • x) = positionDirection x := by
    unfold positionDirection
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3), mul_inv_rev, smul_smul]
    have h : (PDE.vecEuclideanNorm x)⁻¹ * (r ^ 3)⁻¹ * r ^ 3 =
        (PDE.vecEuclideanNorm x)⁻¹ := by
      field_simp
    rw [h]
  unfold homogeneousAnsatz
  rw [normalizedVelocity_dilate, positionDirection_dilate,
    PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)]
  simp
  rw [Real.mul_rpow (pow_nonneg hr.le 3) (PDE.vecEuclideanNorm_nonneg x),
    ← Real.rpow_natCast_mul hr.le]
  have h : 3 * (alpha / 3) = alpha := by ring
  norm_num only [Nat.cast_ofNat]
  rw [h, mul_assoc]

/-- The seed transport is the explicit source expression with its sphere derivative. -/
theorem ansatzTransport_seed {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    ansatzTransport alpha (seed alpha C₀ sigma) y e =
      PDE.vecDot y e * (alpha / 3 * seed alpha C₀ sigma y e -
        (1 / 3 : ℝ) * (alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
          PDE.vecDot (y - e) y)) -
      alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
        PDE.vecDot (y - e) (y - PDE.vecDot y e • e) := by
  unfold ansatzTransport
  rw [fderiv_seed_apply alpha C₀ sigma hsigma,
    fderiv_seed_sphere_apply alpha C₀ sigma hsigma]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

