module

public import OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting

@[expose] public section

namespace OAI.EuclideanRamsey
noncomputable section
open Real Filter Topology MeasureTheory Polynomial Matrix
open scoped TensorProduct RealInnerProductSpace BigOperators

universe uDomain uCodomain uAction

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessianB (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y) x

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
  hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v, w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]; rfl

lemma hessianB_linear_comp {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (x v w : E) :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  have hG : (fun y => fderiv ℝ (f ∘ L) y) = fun y => (fderiv ℝ f (L y)).comp L :=
    funext fun y => ((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hd : Differentiable ℝ fun y => fderiv ℝ f y :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h := ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).clm_comp (hasFDerivAt_const L x)
  dsimp only [Function.comp_def] at h
  unfold hessianB; rw [hG, h.fderiv]; simp

lemma hessianB_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v w : E) :
    hessianB (fun y => f y * g y) x v w =
      f x * hessianB g x v w + g x * hessianB f x v w +
      fderiv ℝ f x v * fderiv ℝ g x w + fderiv ℝ g x v * fderiv ℝ f x w := by
  have hf' (y : E) := (hf.differentiable (by simp) y).hasFDerivAt
  have hg' (y : E) := (hg.differentiable (by simp) y).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z * g z) y) =
      fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y :=
    funext fun y => ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ fun y => fderiv ℝ f y :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ fun y => fderiv ℝ g y :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((hf' x).smul (hgd x).hasFDerivAt).add ((hg' x).smul (hfd x).hasFDerivAt)
  unfold hessianB; rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) + g • fun y => fderiv ℝ f y) x) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]; ring

lemma hessianB_compact {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (hessianB f) := (hf.fderiv ℝ).fderiv ℝ

lemma hessianB_apply_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v w : E) : Continuous (fun x => hessianB f x v w) :=
  (((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply continuous_const

end Hessian

def smoothPositivePart (t : ℝ) : ℝ := t * expNegInvGlue t
def smoothPositivePart' (t : ℝ) : ℝ := (1 + t⁻¹) * expNegInvGlue t

lemma smoothPositivePart_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart (smoothPositivePart' t) t := by
  have hg : HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) t
  have h := (hasDerivAt_id t).mul hg
  change HasDerivAt smoothPositivePart _ t at h
  convert h using 1
  unfold smoothPositivePart'
  by_cases ht : t = 0
  · simp [ht]
  · simp only [id_eq]; field_simp

lemma smoothPositivePart'_bounds (t : ℝ) :
    0 ≤ smoothPositivePart' t ∧ smoothPositivePart' t ≤ 1 := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart', expNegInvGlue.zero_of_nonpos ht]
  have ht0 : 0 < t := lt_of_not_ge ht
  refine ⟨mul_nonneg (by positivity) (expNegInvGlue.nonneg _), ?_⟩
  unfold smoothPositivePart'
  rw [expNegInvGlue, ite_eq_right ht, show -t⁻¹ = -1 / t by ring,
    show -1 / t = -(t⁻¹) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  simpa [add_comm] using Real.add_one_le_exp (t⁻¹)

section Radial
variable {d : ℕ}

def radialPower (a p : ℝ) (x : Space d) : ℝ := (a + ‖x‖ ^ 2) ^ p

lemma radialPower_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPower (d := d) a p) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    fun _ => ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _))

lemma radialPower_hasFDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ) (x : Space d) :
    HasFDerivAt (radialPower a p)
      ((2 * p * (a + ‖x‖ ^ 2) ^ (p - 1)) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := p) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _))))
  change HasFDerivAt (radialPower a p) _ x at h
  refine h.congr_fderiv ?_
  ext v; simp only [_root_.smul_apply, smul_eq_mul]; ring

def halfLaplacian (f : Space d → ℝ) (x : Space d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, hessianB f x
    (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i)

lemma radialPower_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : Space d) :
    halfLaplacian (radialPower a p) x =
      p * (a + ‖x‖ ^ 2) ^ (p - 2) *
        ((d : ℝ) * a + (d + 2 * p - 2) * ‖x‖ ^ 2) := by
  classical
  have hhess (v w : Space d) :
      hessianB (radialPower a p) x v w =
        4 * p * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * inner ℝ x v * inner ℝ x w +
        2 * p * (a + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ v w := by
    have hg : (fun y => fderiv ℝ (radialPower a p) y) =
        fun y => (2 * p * radialPower a (p - 1) y) • innerSL ℝ y :=
      funext fun (y : Space d) => by simpa only [radialPower] using (radialPower_hasFDerivAt ha p y).fderiv
    have hd := ((radialPower_hasFDerivAt ha (p - 1) x).const_smul (2 * p)).smul (innerSL ℝ (E := Space d)).hasFDerivAt
    change HasFDerivAt (fun y => (2 * p * radialPower a (p - 1) y) • innerSL ℝ y) _ x at hd
    unfold hessianB; rw [hg, hd.fderiv]
    simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
      innerSL_apply_apply, Pi.smul_apply, smul_eq_mul, radialPower, show p - 1 - 1 = p - 2 by ring]
    change (2 * p * (a + ‖x‖ ^ 2) ^ (p - 1)) * inner ℝ v w +
      (2 * p) * (2 * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * inner ℝ x v) * inner ℝ x w = _
    ring
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hsum : (∑ i, inner ℝ x (e i) * inner ℝ x (e i)) = ‖x‖ ^ 2 := by
    simpa only [real_inner_comm (e _), real_inner_self_eq_norm_sq] using e.sum_inner_mul_inner x x
  unfold halfLaplacian
  simp_rw [hhess]
  simp only [(EuclideanSpace.basisFun (Fin d) ℝ).inner_eq_ite, ite_eq_left, mul_one, Finset.sum_add_distrib]
  have hsum' : (∑ i, 4 * p * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * inner ℝ x (e i) * inner ℝ x (e i)) =
      4 * p * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * ‖x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  change (1 / 2 : ℝ) * ((∑ i, 4 * p * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * inner ℝ x (e i) * inner ℝ x (e i)) +
    ∑ _ : Fin d, 2 * p * (a + ‖x‖ ^ 2) ^ (p - 1)) = _
  rw [hsum']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (a + ‖x‖ ^ 2) ^ (p - 1) = (a + ‖x‖ ^ 2) ^ (p - 2) * (a + ‖x‖ ^ 2) by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add (by positivity), Real.rpow_one]]
  ring

def radialBump (a p : ℝ) (x : Space d) : ℝ :=
  smoothPositivePart (radialPower a p x - 1)

lemma radialBump_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialBump (d := d) a p) :=
  (contDiff_id.mul expNegInvGlue.contDiff).comp ((radialPower_contDiff ha p).sub contDiff_const)

lemma radialBump_nonneg (a p : ℝ) (x : Space d) : 0 ≤ radialBump a p x := by
  by_cases ht : radialPower a p x - 1 ≤ 0
  · simp [radialBump, smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]
  · exact mul_nonneg (le_of_not_ge ht) (expNegInvGlue.nonneg _)

lemma radialBump_compact {a p : ℝ} (ha : 0 < a) (hp : p < 0) :
    HasCompactSupport (radialBump (d := d) a p) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space d) 1) fun x hx => ?_
  have hx1 : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have ht : radialPower a p x - 1 ≤ 0 :=
    sub_nonpos.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) hp.le)
  simp [radialBump, smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]

end Radial

lemma bilinear_matrix_pushforward {k n : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ l, (M * D * M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  have hp (v : Fin k → ℝ) : v = ∑ j, v j • Pi.single j (1 : ℝ) := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm
  have hex (v w : Fin k → ℝ) : B v w = ∑ j, ∑ l, (v j * w l) * B (Pi.single j 1) (Pi.single l 1) := by
    conv_lhs => rw [hp v, hp w]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  conv_rhs => arg 2; intro a; arg 2; intro b; rw [hex]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro b; rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def rightInverseSplit {E H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    (U : E →ₗ[ℝ] H) (R : H →ₗ[ℝ] E) (hUR : U.comp R = LinearMap.id) : E ≃ₗ[ℝ] H × LinearMap.ker U where
  toFun x := (U x, ⟨x - R (U x), by
    change U (x - R (U x)) = 0
    simp only [map_sub, show U (R (U x)) = U x from LinearMap.congr_fun hUR (U x), sub_self]⟩)
  invFun v := R v.1 + v.2
  left_inv _ := by simp
  right_inv v := by
    ext
    · simp only [map_add, show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1,
        LinearMap.map_coe_ker, add_zero]
    · change R v.1 + (v.2 : E) - R (U (R v.1 + v.2)) = v.2
      simp only [map_add, show U (R v.1) = v.1 from LinearMap.congr_fun hUR v.1,
        LinearMap.map_coe_ker, add_zero]
      abel
  map_add' _ _ := by ext <;> simp [map_add]; abel
  map_smul' _ _ := by ext <;> simp [map_smul, smul_sub]

def stencilDifferential {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ∑ l, C j l *
    iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]

def gradientWeight {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, (∑ j, U a j * x j) ^ 2

def scaleVertical {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]
    (t : ℝ) (ht : t ≠ 0) : (H × V) ≃L[ℝ] H × V :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun x := (x.1, t • x.2)
      invFun x := (x.1, t⁻¹ • x.2)
      left_inv x := by simp [smul_smul, ht]
      right_inv x := by simp [smul_smul, ht]
      map_add' _ _ := by simp [smul_add]
      map_smul' _ _ := by ext <;> simp [smul_smul, mul_comm] }

set_option maxHeartbeats 800000 in
theorem compact_smoothing (k d : ℕ) (hd : 1 ≤ d) (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm) (hU : U * C * U.transpose = 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ b : (Fin k → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      0 < ∫ x, b x ∧
      (∫ x, max (-stencilDifferential C b x) 0 * gradientWeight U x) < η * ∫ x, b x := by
  let R := C * U.transpose
  let Z : Matrix (Fin k) (Fin k) ℝ := 1 - R * U
  have hUR : U * R = 1 := by simpa only [R, ← Matrix.mul_assoc] using hU
  have hRt : R.transpose = U * C := by simp only [R, Matrix.transpose_mul, Matrix.transpose_transpose, hC.eq]
  have hRR : R.transpose * U.transpose = 1 := by rw [← Matrix.transpose_mul, hUR, Matrix.transpose_one]
  have hUZ : U * Z = 0 := by
    change U * (1 - R * U) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hUR, Matrix.one_mul, sub_self]
  have hsplit : C = R * R.transpose + Z * C * Z.transpose := by
    have ht : (1 - R * U).transpose = 1 - U.transpose * R.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
    have h1 : R * U * C = R * R.transpose := by rw [hRt, Matrix.mul_assoc]
    have h2 : C * (U.transpose * R.transpose) = R * R.transpose := by rw [← Matrix.mul_assoc]
    have h3 : R * R.transpose * (U.transpose * R.transpose) = R * R.transpose := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose, hRR, Matrix.one_mul]
    dsimp [Z]
    simp only [ht, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h1, h2, h3]; abel
  let H := Space d
  let eH : H ≃ₗ[ℝ] (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u : (Fin k → ℝ) →ₗ[ℝ] H := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r : H →ₗ[ℝ] (Fin k → ℝ) := (Matrix.toLin' R).comp eH.toLinearMap
  have hur : u.comp r = LinearMap.id := LinearMap.ext fun y => by
    simp only [u, r, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]
    exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] H × V := (rightInverseSplit u r hur).toContinuousLinearEquiv
  let eh : OrthonormalBasis (Fin d) ℝ H := EuclideanSpace.basisFun (Fin d) ℝ
  have hZv (j : Fin k) : (fun l => Z l j) ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker]
    change eH.symm (U.mulVec fun l => Z l j) = 0
    rw [show U.mulVec (fun l => Z l j) = 0 by ext a; exact congrFun (congrFun hUZ a) j, map_zero]
  let z : Fin k → V := fun j => ⟨fun l => Z l j, hZv j⟩
  have hR (j : Fin d) : e (fun l => R l j) = (eh j, 0) := by
    have hRv : r (eh j) = fun l => R l j := by
      change R.mulVec (eH (eh j)) = _
      have h : eH (eh j) = Pi.single j 1 := by
        change ((EuclideanSpace.basisFun (Fin d) ℝ) j).ofLp = _; rw [EuclideanSpace.basisFun_apply]; rfl
      rw [h, Matrix.mulVec_single]; simp; rfl
    rw [← hRv]
    exact Prod.ext (LinearMap.congr_fun hur (eh j)) (Subtype.ext <| by
      change r (eh j) - r (u (r (eh j))) = 0
      rw [show u (r (eh j)) = eh j from LinearMap.congr_fun hur (eh j), sub_self])
  have hZ (j : Fin k) : e (fun l => Z l j) = (0, z j) :=
    Prod.ext (hZv j) (Subtype.ext <| by
      change (fun l => Z l j) - r (u fun l => Z l j) = _
      rw [show u (fun l => Z l j) = 0 from hZv j, map_zero, sub_zero])
  let μH : Measure H := Measure.addHaar
  let μV : Measure V := Measure.addHaar
  let p : ℝ := 1 / 4 - (d : ℝ) / 2
  let n : ℝ := d
  let m := ∫ x, radialBump (1 / 4) p x ∂μH
  let K₁ := μH.real (Metric.ball (0 : Space d) 1) * (-p) * n * (n + 1) ^ (d + 2)
  have hp : p < 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [p]; linarith
  have hm : 0 < m := by
    apply (radialBump_contDiff (d := d) (by norm_num : (0 : ℝ) < 1 / 4) p).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (radialBump_compact (by norm_num) hp) (radialBump_nonneg _ _) (x := (0 : Space d))
    have ht : 0 < radialPower (1 / 4) p (0 : Space d) - 1 := by
      simp only [radialPower, norm_zero, sq, mul_zero, add_zero]
      exact sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hp)
    exact ne_of_gt (mul_pos ht (expNegInvGlue.pos_of_pos ht))
  have hK₁ : 0 ≤ K₁ := by
    dsimp [K₁, n]
    exact mul_nonneg (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (neg_nonneg.mpr hp.le)) (Nat.cast_nonneg _)) (by positivity)
  obtain ⟨t₁, ht₁, ht'⟩ := exists_pos_mul_lt (mul_pos (half_pos hη) hm) (K₁ + 1)
  let δ := min t₁ (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min ht₁ (by norm_num)
  have hδt : δ ≤ t₁ := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hsmall₁ : K₁ * δ < (η / 2) * m := by
    have := mul_le_mul_of_nonneg_left hδt (show 0 ≤ K₁ + 1 by linarith)
    nlinarith
  let ε := δ ^ 2
  have hε : 0 < ε := sq_pos_of_pos hδ
  let a₀ := ε ^ 2
  have hε2 : 0 < a₀ := sq_pos_of_pos hε
  have hεlimit : a₀ ≤ 1 / 4 := by
    have hs : δ ^ 2 ≤ 1 / 4 := by nlinarith
    exact ((sq_le_sq₀ (sq_nonneg _) (by norm_num)).mpr hs).trans (by norm_num)
  let f : H → ℝ := radialBump a₀ p
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := radialBump_contDiff hε2 p
  have hfc : HasCompactSupport f := radialBump_compact hε2 hp
  have hfp : ∀ x, 0 ≤ f x := radialBump_nonneg _ _
  have hlow : m ≤ ∫ x, f x ∂μH :=
    integral_mono
      ((radialBump_contDiff (by norm_num) _).continuous.integrable_of_hasCompactSupport (radialBump_compact (by norm_num) hp))
      (hfs.continuous.integrable_of_hasCompactSupport hfc)
      fun x => monotone_of_hasDerivAt_nonneg smoothPositivePart_hasDerivAt (fun s => (smoothPositivePart'_bounds s).1)
        (sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hp.le) 1)
  have hfm : 0 < ∫ x, f x ∂μH := hm.trans_le hlow
  have hfsmall : (∫ x, max (-halfLaplacian f x) 0 * ‖x‖ ^ 2 ∂μH) < (η / 2) * ∫ x, f x ∂μH := by
    let R₀ := (n + 1) * ε
    let K₀ := (-p) * n * (n + 1) ^ 2 * a₀ ^ p
    have hR₀ : 0 ≤ R₀ := by dsimp [R₀, n]; positivity
    have hI : Integrable ((Metric.closedBall (0 : Space d) R₀).indicator fun _ => K₀) μH :=
      (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
    have hbound := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => mul_nonneg (le_max_right _ _) (sq_nonneg _)) hI
      (Filter.Eventually.of_forall fun x => by
        classical
        have hn0 : 0 ≤ n := Nat.cast_nonneg _
        have hbracket : n + 2 * p - 2 = -(3 / 2 : ℝ) := by dsimp [p, n]; ring
        have hle : max (-halfLaplacian f x) 0 ≤ max (-halfLaplacian (radialPower a₀ p) x) 0 := by
          let spp'' (t : ℝ) : ℝ := t⁻¹ ^ 3 * expNegInvGlue t
          have hf' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space d => radialPower a₀ p y - 1) :=
            (radialPower_contDiff hε2 p).sub contDiff_const
          have he (v w : Space d) :
              hessianB f x v w =
                spp'' (radialPower a₀ p x - 1) *
                  (2 * p * (a₀ + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ x v) *
                  (2 * p * (a₀ + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ x w) +
                smoothPositivePart' (radialPower a₀ p x - 1) *
                  hessianB (radialPower a₀ p) x v w := by
            have hfy (y : Space d) := (hf'.differentiable (by simp) y).hasFDerivAt
            have hG : (fun y => fderiv ℝ f y) =
                fun y => smoothPositivePart' (radialPower a₀ p y - 1) • fderiv ℝ (fun z => radialPower a₀ p z - 1) y :=
              funext fun y => ((smoothPositivePart_hasDerivAt (radialPower a₀ p y - 1)).comp_hasFDerivAt y (hfy y)).fderiv
            have hfd : Differentiable ℝ (fun y => fderiv ℝ (fun z => radialPower a₀ p z - 1) y) :=
              (hf'.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
            have hp'' (t : ℝ) : HasDerivAt smoothPositivePart' (spp'' t) t := by
              have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 + X : ℝ[X]) t
              simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] at h
              exact h.congr_deriv (by simp [spp'']; left; ring)
            have hd := ((hp'' (radialPower a₀ p x - 1)).comp_hasFDerivAt x (hfy x)).smul
              (hfd x).hasFDerivAt
            change HasFDerivAt (fun y => smoothPositivePart' (radialPower a₀ p y - 1) • fderiv ℝ (fun z => radialPower a₀ p z - 1) y) _ x at hd
            unfold hessianB
            change ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) w = _
            rw [hG, hd.fderiv]
            simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul,
              Function.comp_apply, fderiv_sub_const, (radialPower_hasFDerivAt hε2 p x).fderiv, innerSL_apply_apply]
            ring
          have hsum : (∑ i, inner ℝ x (eh i) * inner ℝ x (eh i)) = ‖x‖ ^ 2 := by
            simpa only [real_inner_comm (eh _), real_inner_self_eq_norm_sq] using eh.sum_inner_mul_inner x x
          have hlap : halfLaplacian f x =
              smoothPositivePart' (radialPower a₀ p x - 1) * halfLaplacian (radialPower a₀ p) x +
              2 * spp'' (radialPower a₀ p x - 1) * p ^ 2 *
                ((a₀ + ‖x‖ ^ 2) ^ (p - 1)) ^ 2 * ‖x‖ ^ 2 := by
            unfold halfLaplacian
            simp_rw [he, Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
            have hs : (∑ i, spp'' (radialPower a₀ p x - 1) *
                (2 * p * (a₀ + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ x (eh i)) *
                (2 * p * (a₀ + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ x (eh i))) =
                (4 * spp'' (radialPower a₀ p x - 1) * p ^ 2 * ((a₀ + ‖x‖ ^ 2) ^ (p - 1)) ^ 2) * ‖x‖ ^ 2 := by
              rw [← hsum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
            change (1 / 2 : ℝ) * ((∑ i, spp'' (radialPower a₀ p x - 1) *
                (2 * p * (a₀ + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ x (eh i)) *
                (2 * p * (a₀ + ‖x‖ ^ 2) ^ (p - 1) * inner ℝ x (eh i))) + _) = _
            rw [hs]; ring
          rw [hlap]
          have hb := smoothPositivePart'_bounds (radialPower a₀ p x - 1)
          have hpp : 0 ≤ spp'' (radialPower a₀ p x - 1) := by
            by_cases ht : radialPower a₀ p x - 1 ≤ 0
            · simp [spp'', expNegInvGlue.zero_of_nonpos ht]
            · have ht0 : 0 < radialPower a₀ p x - 1 := lt_of_not_ge ht
              exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)
          have hc : 0 ≤ 2 * spp'' (radialPower a₀ p x - 1) * p ^ 2 *
              ((a₀ + ‖x‖ ^ 2) ^ (p - 1)) ^ 2 * ‖x‖ ^ 2 := by positivity
          refine max_le ?_ (le_max_right _ _)
          by_cases h : 0 ≤ halfLaplacian (radialPower a₀ p) x
          · exact le_trans (by nlinarith [mul_nonneg hb.1 h]) (le_max_right _ _)
          · have : smoothPositivePart' (radialPower a₀ p x - 1) *
                halfLaplacian (radialPower a₀ p) x ≥ halfLaplacian (radialPower a₀ p) x := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (neg_nonneg.mpr (le_of_not_ge h))]
            exact le_trans (by linarith) (le_max_left _ _)
        by_cases hx : x ∈ Metric.closedBall (0 : Space d) R₀
        · rw [Set.indicator_of_mem hx]
          have hx' : ‖x‖ ≤ (n + 1) * ε := by simpa [R₀, Metric.mem_closedBall, dist_zero_right] using hx
          have hs : ‖x‖ ^ 2 ≤ ((n + 1) * ε) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx'
          have hlower : p * n * a₀ ^ (p - 1) ≤ halfLaplacian (radialPower a₀ p) x := by
            rw [radialPower_halfLaplacian hε2]
            change p * n * a₀ ^ (p - 1) ≤ p * (a₀ + ‖x‖ ^ 2) ^ (p - 2) * (n * a₀ + (n + 2 * p - 2) * ‖x‖ ^ 2)
            rw [hbracket, show p * n * a₀ ^ (p - 1) = (p * n * a₀) * a₀ ^ (p - 2) by
              rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hε2, Real.rpow_one]; ring]
            have hpow := Real.rpow_le_rpow_of_nonpos hε2 (show a₀ ≤ a₀ + ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖]) (show p - 2 ≤ 0 by linarith)
            have hq : 0 ≤ (a₀ + ‖x‖ ^ 2) ^ (p - 2) := Real.rpow_nonneg (by positivity) _
            refine (mul_le_mul_of_nonpos_left hpow (mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg hp.le hn0) hε2.le)).trans ?_
            have := mul_nonneg (neg_nonneg.mpr hp.le) (mul_nonneg hq (sq_nonneg ‖x‖))
            nlinarith
          have hK' : 0 ≤ (-p) * n * a₀ ^ (p - 1) :=
            mul_nonneg (mul_nonneg (neg_nonneg.mpr hp.le) hn0) (Real.rpow_nonneg hε2.le _)
          refine (mul_le_mul (hle.trans (max_le (by linarith) hK')) hs (sq_nonneg _) hK').trans_eq ?_
          have hpow : a₀ ^ (p - 1) * a₀ = a₀ ^ p := by
            rw [← Real.rpow_add_one hε2.ne', sub_add_cancel]
          change (-p) * n * a₀ ^ (p - 1) * ((n + 1) * ε) ^ 2 = K₀
          dsimp [K₀, a₀]; rw [← hpow]; ring
        · rw [Set.indicator_of_notMem hx]
          have hx' : (n + 1) * ε ≤ ‖x‖ := by
            simp only [R₀, Metric.mem_closedBall, dist_zero_right, not_le] at hx; exact hx.le
          have hnonneg : 0 ≤ halfLaplacian (radialPower a₀ p) x := by
            rw [radialPower_halfLaplacian hε2]
            change 0 ≤ p * (a₀ + ‖x‖ ^ 2) ^ (p - 2) * (n * a₀ + (n + 2 * p - 2) * ‖x‖ ^ 2)
            rw [hbracket]
            refine mul_nonneg_of_nonpos_of_nonpos
              (mul_nonpos_of_nonpos_of_nonneg hp.le (Real.rpow_nonneg (by positivity) _)) ?_
            have hs : ((n + 1) * ε) ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hx'
            have hnn' := mul_le_mul_of_nonneg_right (show n ≤ (n + 1) ^ 2 by nlinarith [sq_nonneg n]) (sq_nonneg ε)
            dsimp [a₀]; nlinarith
          rw [max_eq_right (neg_nonpos.mpr hnonneg)] at hle
          exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg _))
    have hupper : (∫ x, max (-halfLaplacian f x) 0 * ‖x‖ ^ 2 ∂μH) ≤ K₁ * δ := by
      refine hbound.trans_eq ?_
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
        Measure.real_def, μH.addHaar_closedBall (0 : Space d) hR₀, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR₀ _)]
      dsimp [R₀, K₀, K₁, n]
      rw [mul_pow]
      have he : ε ^ d * (ε ^ 2) ^ p = δ := by
        have hroot : Real.sqrt ε = δ := by dsimp [ε]; exact Real.sqrt_sq hδ.le
        rw [← hroot, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast_mul hε.le 2, ← Real.rpow_add hε]
        congr 1; dsimp [p]; ring
      change ((d + 1 : ℝ) ^ d * ε ^ d * μH.real (Metric.ball (0 : Space d) 1)) *
        ((-p) * (d : ℝ) * (d + 1 : ℝ) ^ 2 * (ε ^ 2) ^ p) = _
      rw [pow_add, ← he]; ring
    exact hupper.trans_lt (hsmall₁.trans_le (mul_le_mul_of_nonneg_left hlow (by positivity)))
  let g₀ : ContDiffBump (0 : V) := ⟨1, 2, by norm_num, by norm_num⟩
  let g : V → ℝ := g₀
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := g₀.contDiff
  have hgc : HasCompactSupport g := g₀.hasCompactSupport
  have hgp : ∀ y, 0 ≤ g y := g₀.nonneg'
  have hgm : 0 < ∫ y, g y ∂μV := g₀.integral_pos
  let a := halfLaplacian f
  let bV (y : V) : ℝ := (1 / 2 : ℝ) * ∑ j, ∑ l, C j l * hessianB g y (z j) (z l)
  have hac : Continuous a :=
    continuous_const.mul (continuous_finsetSum _ fun _ _ => hessianB_apply_continuous hfs _ _)
  have hak : HasCompactSupport a := by
    apply (hessianB_compact hfc).comp_left
      (g := fun B => (1 / 2 : ℝ) * ∑ j, B (eh j) (eh j))
    simp
  have hbc : Continuous bV :=
    continuous_const.mul (continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => continuous_const.mul (hessianB_apply_continuous hgs _ _))
  have hbk : HasCompactSupport bV := by
    apply (hessianB_compact hgc).comp_left (g := fun B => (1 / 2 : ℝ) * ∑ j, ∑ l, C j l * B (z j) (z l))
    simp
  have haI : Integrable (fun x => max (-a x) 0 * ‖x‖ ^ 2) μH := by
    have hk : HasCompactSupport fun x => max (-a x) 0 := by
      apply hak.comp_left (g := fun r : ℝ => max (-r) 0); simp
    exact ((hac.neg.max continuous_const).mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hk.mul_right
  have hfI : Integrable (fun x => f x * ‖x‖ ^ 2) μH :=
    (hfs.continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hfc.mul_right
  have hgI : Integrable g μV := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hbI : Integrable (fun y => |bV y|) μV := hbc.abs.integrable_of_hasCompactSupport hbk.abs
  let K := (∫ x, f x * ‖x‖ ^ 2 ∂μH) * (∫ y, |bV y| ∂μV)
  have hK : 0 ≤ K := mul_nonneg (integral_nonneg fun x => mul_nonneg (hfp x) (sq_nonneg _))
    (integral_nonneg fun _ => abs_nonneg _)
  obtain ⟨t₀, ht₀, htsmall⟩ := exists_pos_mul_lt
    (mul_pos (mul_pos (show 0 < η / 2 by positivity) hfm) hgm) (K + 1)
  let t := min t₀ 1
  have ht : 0 < t := lt_min ht₀ zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htt₀ : t ≤ t₀ := min_le_left _ _
  have hsmall : t ^ 2 * K < (η / 2) * (∫ x, f x ∂μH) * (∫ y, g y ∂μV) := by
    have h : (K + 1) * t ≤ (K + 1) * t₀ := mul_le_mul_of_nonneg_left htt₀ (by linarith)
    have hsq : t ^ 2 ≤ t := by nlinarith
    have hsqK := mul_le_mul_of_nonneg_right hsq hK
    nlinarith
  let et := e.trans (scaleVertical t ht.ne')
  let b := (fun y : H × V => f y.1 * g y.2) ∘ et
  have hfgs : ContDiff ℝ (⊤ : ℕ∞) (fun y : H × V => f y.1 * g y.2) :=
    (hfs.comp contDiff_fst).mul (hgs.comp contDiff_snd)
  have hbs : ContDiff ℝ (⊤ : ℕ∞) b := hfgs.comp et.contDiff
  have hbk' : HasCompactSupport b :=
    (HasCompactSupport.of_support_subset_isCompact (hfc.prod hgc) fun ⟨x, y⟩ h =>
      ⟨subset_closure fun h0 => h (by simp [h0]), subset_closure fun h0 => h (by simp [h0])⟩).comp_homeomorph et.toHomeomorph
  let μP := μH.prod μV
  let : (volume.map et).IsAddHaarMeasure := et.isAddHaarMeasure_map volume
  let c : ℝ := (volume.map et).addHaarScalarFactor μP
  have hc : 0 < c := by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume.map et) μP
  have hchange (φ : H × V → ℝ) (hφ : Continuous φ) : (∫ x, φ (et x)) = c * ∫ y, φ y ∂μP := by
    rw [← integral_map et.continuous.measurable.aemeasurable hφ.aestronglyMeasurable,
      Measure.isAddLeftInvariant_eq_smul (volume.map et) μP]
    simp [c, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hmass : (∫ x, b x) = c * ((∫ x, f x ∂μH) * (∫ y, g y ∂μV)) := by
    change (∫ x, f (et x).1 * g (et x).2) = _
    rw [hchange _ hfgs.continuous, integral_prod_mul]
  have hdiff (x : Fin k → ℝ) : stencilDifferential C b x =
      g (et x).2 * a (et x).1 + t ^ 2 * f (et x).1 * bV (et x).2 := by
    have hb (v w : Fin k → ℝ) : hessianB b x v w =
        hessianB (fun y : H × V => f y.1 * g y.2) (et x) (et v) (et w) :=
      hessianB_linear_comp hfgs et.toContinuousLinearMap x v w
    have hhr (j : Fin d) : et (fun l => R l j) = (eh j, 0) := by simp [et, scaleVertical, hR]
    have hhz (j : Fin k) : et (fun l => Z l j) = (0, t • z j) := by simp [et, scaleVertical, hZ]
    have hhor : ∑ j, hessianB b x (fun l => R l j) (fun l => R l j) =
        g (et x).2 * ∑ j, hessianB f (et x).1 (eh j) (eh j) := by
      have hh (y : H × V) (v w : H) :
          hessianB (fun y : H × V => f y.1 * g y.2) y (v, 0) (w, 0) = g y.2 * hessianB f y.1 v w := by
        rw [hessianB_mul (f := fun y : H × V => f y.1) (g := fun y : H × V => g y.2) (hfs.comp contDiff_fst) (hgs.comp contDiff_snd),
          show (fun y : H × V => f y.1) = f ∘ ContinuousLinearMap.fst ℝ H V from rfl,
          show (fun y : H × V => g y.2) = g ∘ ContinuousLinearMap.snd ℝ H V from rfl,
          hessianB_linear_comp hfs, hessianB_linear_comp hgs]
        have hfg := ((hgs.differentiable (by simp) y.2).hasFDerivAt.comp y
          (ContinuousLinearMap.snd ℝ H V).hasFDerivAt).fderiv
        change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.snd ℝ H V)) y = _ at hfg
        rw [hfg]; simp
      simp only [hb, hhr, hh, Finset.mul_sum]
    have hver : ∑ j, ∑ l, C j l * hessianB b x (fun m => Z m j) (fun m => Z m l) =
        t ^ 2 * f (et x).1 * ∑ j, ∑ l, C j l * hessianB g (et x).2 (z j) (z l) := by
      have hv' (y : H × V) (v w : V) :
          hessianB (fun y : H × V => f y.1 * g y.2) y (0, v) (0, w) = f y.1 * hessianB g y.2 v w := by
        rw [hessianB_mul (f := fun y : H × V => f y.1) (g := fun y : H × V => g y.2) (hfs.comp contDiff_fst) (hgs.comp contDiff_snd),
          show (fun y : H × V => f y.1) = f ∘ ContinuousLinearMap.fst ℝ H V from rfl,
          show (fun y : H × V => g y.2) = g ∘ ContinuousLinearMap.snd ℝ H V from rfl,
          hessianB_linear_comp hfs, hessianB_linear_comp hgs]
        have hfg := ((hfs.differentiable (by simp) y.1).hasFDerivAt.comp y
          (ContinuousLinearMap.fst ℝ H V).hasFDerivAt).fderiv
        change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.fst ℝ H V)) y = _ at hfg
        rw [hfg]; simp
      simp only [hb, hhz, hv', map_smul, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hcon : ∑ j, ∑ l, C j l * hessianB b x (Pi.single j 1) (Pi.single l 1) =
        (∑ j, hessianB b x (fun l => R l j) (fun l => R l j)) +
        ∑ j, ∑ l, C j l * hessianB b x (fun m => Z m j) (fun m => Z m l) := by
      conv_lhs => rw [hsplit]
      simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      exact congrArg₂ _ (by simpa [Matrix.one_apply] using bilinear_matrix_pushforward (hessianB b x) R 1)
        (bilinear_matrix_pushforward (hessianB b x) Z C)
    change stencilDifferential C b x = _
    simp only [stencilDifferential, ← hessianB_eq]
    rw [hcon, hhor, hver]
    simp only [a, bV, halfLaplacian, eh]; ring
  let φ : H × V → ℝ := fun y => max (-(g y.2 * a y.1 + t ^ 2 * f y.1 * bV y.2)) 0 * ‖y.1‖ ^ 2
  have hφ : Continuous φ :=
    ((((hgs.continuous.comp continuous_snd).mul (hac.comp continuous_fst)).add
      ((continuous_const.mul (hfs.continuous.comp continuous_fst)).mul
        (hbc.comp continuous_snd))).neg.max continuous_const).mul (continuous_fst.norm.pow 2)
  have hw (x : Fin k → ℝ) : gradientWeight U x = ‖(et x).1‖ ^ 2 := by
    change _ = ‖eH.symm (U.mulVec x)‖ ^ 2; rw [EuclideanSpace.real_norm_sq_eq]; rfl
  have hneg : (∫ x, max (-stencilDifferential C b x) 0 * gradientWeight U x) =
      c * ∫ y, φ y ∂μP := by
    conv_lhs => arg 2; intro x; rw [hdiff, hw]
    exact hchange φ hφ
  have hbound : (∫ z : H × V, φ z ∂μP) ≤
      (∫ x, max (-a x) 0 * ‖x‖ ^ 2 ∂μH) * (∫ y, g y ∂μV) +
      t ^ 2 * (∫ x, f x * ‖x‖ ^ 2 ∂μH) * (∫ y, |bV y| ∂μV) := by
    have hI := (haI.mul_prod hgI).add ((hfI.mul_prod hbI).const_mul (t ^ 2))
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)) hI
      (Filter.Eventually.of_forall fun z => ?_)).trans_eq ?_
    · have h : max (-(g z.2 * a z.1 + t ^ 2 * f z.1 * bV z.2)) 0 ≤
          g z.2 * max (-a z.1) 0 + t ^ 2 * f z.1 * |bV z.2| :=
        max_le (by
          nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-a z.1) 0) (hgp z.2),
            mul_le_mul_of_nonneg_left (neg_le_abs (bV z.2)) (mul_nonneg (sq_nonneg t) (hfp z.1))])
          (add_nonneg (mul_nonneg (hgp z.2) (le_max_right _ _))
            (mul_nonneg (mul_nonneg (sq_nonneg t) (hfp z.1)) (abs_nonneg _)))
      exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans_eq (by dsimp; ring)
    · change (∫ z : H × V, (max (-a z.1) 0 * ‖z.1‖ ^ 2) * g z.2 +
        t ^ 2 * ((f z.1 * ‖z.1‖ ^ 2) * |bV z.2|) ∂μP) = _
      rw [integral_add (haI.mul_prod hgI) ((hfI.mul_prod hbI).const_mul (t ^ 2)),
        integral_const_mul, integral_prod_mul (fun x => max (-a x) 0 * ‖x‖ ^ 2) g,
        integral_prod_mul (fun x => f x * ‖x‖ ^ 2) fun y => |bV y|]
      ring
  have hfinal : (∫ y, φ y ∂μP) < η * ((∫ x, f x ∂μH) * (∫ y, g y ∂μV)) := by
    have hh := mul_lt_mul_of_pos_right hfsmall hgm
    rw [mul_assoc (t ^ 2)] at hbound
    exact (hbound.trans_lt (add_lt_add hh hsmall)).trans_eq (by ring)
  refine ⟨b, hbs, hbk', by rw [hmass]; positivity, ?_⟩
  rw [hneg, hmass]
  exact (mul_lt_mul_of_pos_left hfinal hc).trans_eq (by ring)

end
end OAI.EuclideanRamsey
