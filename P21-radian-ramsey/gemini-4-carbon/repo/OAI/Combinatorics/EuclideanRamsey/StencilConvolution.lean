module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace Pointwise Topology
open Real Filter MeasureTheory Polynomial Matrix

namespace EuclideanRamsey

def hessianB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x

lemma hessianB_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x v w : E) : hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v, w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]; rfl

lemma hessianB_linear_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (x v w : E) : hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  have hG : fderiv ℝ (f ∘ L) = fun y => (fderiv ℝ f (L y)).comp L := funext fun y =>
    ((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hd : Differentiable ℝ (fderiv ℝ f) := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h := ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).clm_comp (hasFDerivAt_const L x)
  dsimp only [Function.comp_def] at h
  unfold hessianB; rw [hG, h.fderiv]; simp

lemma hessianB_prod_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : E × F) (v w : E) :
    hessianB (fun q : E × F => f q.1 * g q.2) y (v, 0) (w, 0) = g y.2 * hessianB f y.1 v w := by
  let Φ (q : E × F) := f q.1 * g q.2
  have htr (z : E × F) : hessianB (fun q => Φ ((0, y.2) + q)) z = hessianB Φ ((0, y.2) + z) := by
    unfold hessianB
    rw [show fderiv ℝ (fun q => Φ ((0, y.2) + q)) = fun q => fderiv ℝ Φ ((0, y.2) + q) from
      funext fun _ => fderiv_comp_add_left _, fderiv_comp_add_left]
  have hlc := hessianB_linear_comp (((hf.comp contDiff_fst).mul (hg.comp contDiff_snd)).comp
    ((contDiff_const (c := ((0 : E), y.2))).add contDiff_id)) (.inl ℝ E F) y.1 v w
  rw [show (((fun x : E × F => (f ∘ Prod.fst) x * (g ∘ Prod.snd) x) ∘ fun x => (0, y.2) + id x) ∘
      ⇑(ContinuousLinearMap.inl ℝ E F)) = fun x => f x * g y.2 by ext; simp,
    show ((fun x : E × F => (f ∘ Prod.fst) x * (g ∘ Prod.snd) x) ∘ fun x => (0, y.2) + id x) =
      fun q => Φ ((0, y.2) + q) from rfl, htr] at hlc
  have hcm : hessianB (fun x => f x * g y.2) y.1 = g y.2 • hessianB f y.1 := by
    unfold hessianB
    have h1 : fderiv ℝ (fun x => f x * g y.2) = g y.2 • fderiv ℝ f :=
      funext fun x => ((hf.differentiable (by simp) x).hasFDerivAt.mul_const _).fderiv
    rw [h1]; exact (((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) y.1).hasFDerivAt.const_smul _).fderiv
  simpa [Φ, hcm] using hlc.symm

lemma hessianB_prod_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : E × F) (v w : F) :
    hessianB (fun q : E × F => f q.1 * g q.2) y (0, v) (0, w) = f y.1 * hessianB g y.2 v w := by
  have h := hessianB_linear_comp ((hg.comp contDiff_fst).mul (hf.comp contDiff_snd))
    (ContinuousLinearEquiv.prodComm ℝ E F).toContinuousLinearMap y (0, v) (0, w)
  change hessianB (fun q : E × F => g q.2 * f q.1) y (0, v) (0, w) =
    hessianB (fun q : F × E => g q.1 * f q.2) y.swap (v, 0) (w, 0) at h
  rw [show (fun q : E × F => g q.2 * f q.1) = fun q => f q.1 * g q.2 from funext fun _ => mul_comm _ _] at h
  exact h.trans (hessianB_prod_fst hg hf y.swap v w)

def secondOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E) (f : E → ℝ) (x : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ∑ l, C j l * hessianB f x (v j) (v l)

abbrev stencilDifferential {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) :=
  secondOp C (fun j => Pi.single j (1 : ℝ))

abbrev halfLap {d : ℕ} := secondOp (1 : Matrix (Fin d) (Fin d) ℝ) (fun i => EuclideanSpace.single i (1 : ℝ))

lemma halfLap_apply {d : ℕ} (f : Space d → ℝ) (x : Space d) :
    halfLap f x = (1 / 2 : ℝ) * ∑ i : Fin d, hessianB f x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp [halfLap, secondOp, Matrix.one_apply]

lemma secondOp_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E) {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (secondOp C v f) := by
  have hc : Continuous (hessianB f) := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous_fderiv (by simp)
  exact continuous_const.mul (continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
    continuous_const.mul ((hc.clm_apply continuous_const).clm_apply continuous_const))

lemma hessianB_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (hessianB f) :=
  (hf.fderiv ℝ).fderiv ℝ

lemma secondOp_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E) {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (secondOp C v f) := by
  apply (hessianB_compact hf).comp_left (g := fun B => (1 / 2 : ℝ) * ∑ j, ∑ l, C j l * B (v j) (v l))
  simp

abbrev smoothPos (t : ℝ) : ℝ := t * expNegInvGlue t
abbrev smoothPos' (t : ℝ) : ℝ := (1 + t⁻¹) * expNegInvGlue t
abbrev smoothPos'' (t : ℝ) : ℝ := t⁻¹ ^ 3 * expNegInvGlue t

lemma smoothPos_hasDerivAt (t : ℝ) : HasDerivAt smoothPos (smoothPos' t) t := by
  have h := (hasDerivAt_id t).mul (by simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) t)
  refine (h : HasDerivAt smoothPos _ t).congr_deriv ?_
  by_cases ht : t = 0
  · simp [smoothPos', ht]
  · simp only [smoothPos', id_eq]; field_simp

lemma smoothPos'_hasDerivAt (t : ℝ) : HasDerivAt smoothPos' (smoothPos'' t) t := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 + X : ℝ[X]) t
  simp only [eval_add, eval_one, eval_X] at h
  exact (h : HasDerivAt smoothPos' _ t).congr_deriv (by simp [smoothPos'']; left; ring)

lemma smoothPos'_bounds (t : ℝ) : 0 ≤ smoothPos' t ∧ smoothPos' t ≤ 1 := by
  by_cases ht : t ≤ 0
  · simp [smoothPos', expNegInvGlue.zero_of_nonpos ht]
  · have : 0 < t := lt_of_not_ge ht
    refine ⟨mul_nonneg (by positivity) (expNegInvGlue.nonneg _), ?_⟩
    rw [smoothPos', expNegInvGlue, ite_eq_right ht, show -t⁻¹ = -(t⁻¹) from rfl, Real.exp_neg,
      ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    simpa [add_comm] using Real.add_one_le_exp t⁻¹

def radialPow {d : ℕ} (a p : ℝ) (x : Space d) : ℝ := (a + ‖x‖ ^ 2) ^ p
def radialBump {d : ℕ} (a p : ℝ) (x : Space d) : ℝ := smoothPos (radialPow a p x - 1)

lemma radialPow_hasFDerivAt {d : ℕ} {a : ℝ} (ha : 0 < a) (p : ℝ) (x : Space d) :
    HasFDerivAt (radialPow a p) ((2 * p * (a + ‖x‖ ^ 2) ^ (p - 1)) • innerSL ℝ x) x :=
  (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := p) (Or.inl (by positivity))).congr_fderiv (by ext; simp [smul_eq_mul]; ring)

lemma radialPow_halfLap {d : ℕ} {a : ℝ} (ha : 0 < a) (p : ℝ) (x : Space d) :
    halfLap (radialPow a p) x =
      p * (a + ‖x‖ ^ 2) ^ (p - 2) * (d * a + (d + 2 * p - 2) * ‖x‖ ^ 2) := by
  have hg : fderiv ℝ (radialPow (d := d) a p) = fun y => (2 * p * radialPow a (p - 1) y) • innerSL ℝ y :=
    funext fun y => (radialPow_hasFDerivAt ha p y).fderiv
  have hd := ((radialPow_hasFDerivAt (d := d) ha (p - 1) x).const_smul (2 * p)).smul (innerSL ℝ (E := Space d)).hasFDerivAt
  change HasFDerivAt (fun y => (2 * p * radialPow a (p - 1) y) • innerSL ℝ y) _ x at hd
  have hdiag (i : Fin d) : hessianB (radialPow a p) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      4 * p * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * x i ^ 2 + 2 * p * (a + ‖x‖ ^ 2) ^ (p - 1) := by
    unfold hessianB; rw [hg, hd.fderiv]
    simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
      innerSL_apply_apply, Pi.smul_apply, smul_eq_mul, radialPow, show p - 1 - 1 = p - 2 by ring]
    change 2 * p * (a + ‖x‖ ^ 2) ^ (p - 1) * ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i 1⟫ +
      2 * p * (2 * (p - 1) * (a + ‖x‖ ^ 2) ^ (p - 2) * ⟪x, EuclideanSpace.single i 1⟫) * ⟪x, EuclideanSpace.single i 1⟫ = _
    simp [EuclideanSpace.inner_single_right]; ring
  rw [halfLap_apply]; simp_rw [hdiag, Finset.sum_add_distrib, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (a + ‖x‖ ^ 2) ^ (p - 1) = (a + ‖x‖ ^ 2) ^ (p - 2) * (a + ‖x‖ ^ 2) by
      rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add (by positivity), Real.rpow_one]]
  ring

lemma radialBump_negative_le {d : ℕ} {a : ℝ} (ha : 0 < a) (p : ℝ) (x : Space d) :
    max (-halfLap (radialBump a p) x) 0 ≤ max (-halfLap (radialPow a p) x) 0 := by
  let f : Space d → ℝ := fun y => radialPow a p y - 1
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun _ => by positivity).sub contDiff_const
  have hf' (y : Space d) := (hf.differentiable (by simp) y).hasFDerivAt
  have hG : fderiv ℝ (smoothPos ∘ f) = fun y => smoothPos' (f y) • fderiv ℝ f y :=
    funext fun y => ((smoothPos_hasDerivAt (f y)).comp_hasFDerivAt y (hf' y)).fderiv
  have hfd : Differentiable ℝ (fderiv ℝ f) := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((smoothPos'_hasDerivAt (f x)).comp_hasFDerivAt x (hf' x)).smul (hfd x).hasFDerivAt
  change HasFDerivAt (fun y => smoothPos' (f y) • fderiv ℝ f y) _ x at hd
  have hhess (i : Fin d) : hessianB (radialBump a p) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      smoothPos'' (f x) * (2 * p * (a + ‖x‖ ^ 2) ^ (p - 1) * x i) ^ 2 +
      smoothPos' (f x) * hessianB (radialPow a p) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    change ((fderiv ℝ (fderiv ℝ (smoothPos ∘ f)) x) _) _ = _
    rw [hG, hd.fderiv]
    simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    rw [show fderiv ℝ f = fderiv ℝ (radialPow a p) from funext fun _ => fderiv_sub_const 1,
      (radialPow_hasFDerivAt ha p x).fderiv]
    simp only [_root_.smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, smul_eq_mul]
    unfold hessianB; ring
  have hlap : halfLap (radialBump a p) x =
      smoothPos' (f x) * halfLap (radialPow a p) x +
      2 * smoothPos'' (f x) * p ^ 2 * ((a + ‖x‖ ^ 2) ^ (p - 1)) ^ 2 * ‖x‖ ^ 2 := by
    rw [halfLap_apply, halfLap_apply]
    simp_rw [hhess, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show (∑ i : Fin d, (2 * p * (a + ‖x‖ ^ 2) ^ (p - 1) * x i) ^ 2) =
      4 * p ^ 2 * ((a + ‖x‖ ^ 2) ^ (p - 1)) ^ 2 * ‖x‖ ^ 2 by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
    ring
  rw [hlap]
  have hb := smoothPos'_bounds (f x)
  have hc'' : 0 ≤ smoothPos'' (f x) := by
    by_cases ht : f x ≤ 0
    · simp [smoothPos'', expNegInvGlue.zero_of_nonpos ht]
    · have : 0 < f x := lt_of_not_ge ht; exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)
  have hpos : 0 ≤ 2 * smoothPos'' (f x) * p ^ 2 * ((a + ‖x‖ ^ 2) ^ (p - 1)) ^ 2 * ‖x‖ ^ 2 := by positivity
  refine max_le ?_ (le_max_right _ _)
  by_cases h0 : 0 ≤ halfLap (radialPow a p) x
  · exact (by nlinarith [mul_nonneg hb.1 h0] : _ ≤ (0 : ℝ)).trans (le_max_right _ _)
  · exact (by nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (neg_nonneg.mpr (le_of_not_ge h0))] :
      _ ≤ -halfLap (radialPow a p) x).trans (le_max_left _ _)

lemma exists_radial_smoothing {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ f : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ 0 < ∫ x, f x ∧
      (∫ x, max (-halfLap f x) 0 * ‖x‖ ^ 2) < η * ∫ x, f x := by
  let p : ℝ := 1 / 4 - (d : ℝ) / 2
  have hp : p < 0 := by have : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr hd; dsimp [p]; linarith
  have hb_cd {a : ℝ} (ha : 0 < a) : ContDiff ℝ (⊤ : ℕ∞) (radialBump (d := d) a p) :=
    (contDiff_id.mul expNegInvGlue.contDiff).comp
      (((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun _ => by positivity).sub contDiff_const)
  have hb_cs {a : ℝ} (ha : 0 < a) : HasCompactSupport (radialBump (d := d) a p) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space d) 1) fun x hx => ?_
    have hx1 : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    simp [radialBump, smoothPos]
    exact Or.inr (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) hp.le)
  have hb_nn (a : ℝ) (x : Space d) : 0 ≤ radialBump a p x := by
    by_cases ht : radialPow a p x - 1 ≤ 0
    · simp [radialBump, smoothPos, expNegInvGlue.zero_of_nonpos ht]
    · exact mul_nonneg (le_of_not_ge ht) (expNegInvGlue.nonneg _)
  let m := ∫ x : Space d, radialBump (1 / 4) p x
  have hm : 0 < m := by
    refine (hb_cd (by norm_num)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (hb_cs (by norm_num)) (hb_nn _) (ne_of_gt ?_)
    have ht : 0 < radialPow (1 / 4) p (0 : Space d) - 1 := by
      simpa [radialPow] using sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hp)
    exact mul_pos ht (expNegInvGlue.pos_of_pos ht)
  let K := (volume : Measure (Space d)).real (Metric.ball 0 1) * (-p) * d * (d + 1 : ℝ) ^ (d + 2)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (neg_nonneg.mpr hp.le))
    (Nat.cast_nonneg _)) (by positivity)
  let δ := min (η * m / (2 * (K + 1))) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  let ε := δ ^ 2
  have hε : 0 < ε := sq_pos_of_pos hδ
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hε_lim : ε ^ 2 ≤ 1 / 4 := by
    have : δ ^ 2 ≤ 1 / 4 := by nlinarith [min_le_right (η * m / (2 * (K + 1))) (1 / 2)]
    exact ((sq_le_sq₀ (sq_nonneg _) (by norm_num)).mpr this).trans (by norm_num)
  have hmono : m ≤ ∫ x : Space d, radialBump (ε ^ 2) p x :=
    integral_mono ((hb_cd (by norm_num)).continuous.integrable_of_hasCompactSupport (hb_cs (by norm_num)))
      ((hb_cd hε2).continuous.integrable_of_hasCompactSupport (hb_cs hε2)) fun x =>
        monotone_of_hasDerivAt_nonneg smoothPos_hasDerivAt (fun t => (smoothPos'_bounds t).1)
          (sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hp.le) 1)
  let R := (d + 1 : ℝ) * ε
  let C_ind := (-p) * d * (d + 1 : ℝ) ^ 2 * (ε ^ 2) ^ p
  have hpt (x : Space d) : max (-halfLap (radialBump (ε ^ 2) p) x) 0 * ‖x‖ ^ 2 ≤
      (Metric.closedBall (0 : Space d) R).indicator (fun _ => C_ind) x := by
    classical
    have hle := radialBump_negative_le hε2 p x
    have hbr : (d : ℝ) + 2 * p - 2 = -(3 / 2 : ℝ) := by dsimp [p]; ring
    by_cases hx : x ∈ Metric.closedBall (0 : Space d) R
    · rw [Set.indicator_of_mem hx]
      have hx' : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hs : ‖x‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by dsimp [R]; positivity)).mpr hx'
      have hlow : p * d * (ε ^ 2) ^ (p - 1) ≤ halfLap (radialPow (ε ^ 2) p) x := by
        rw [radialPow_halfLap hε2, hbr, show p * d * (ε ^ 2) ^ (p - 1) = (p * d * ε ^ 2) * (ε ^ 2) ^ (p - 2) by
          rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add hε2, Real.rpow_one]; ring]
        have hpw := Real.rpow_le_rpow_of_nonpos hε2
          (show ε ^ 2 ≤ ε ^ 2 + ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖]) (show p - 2 ≤ 0 by linarith)
        have hq : 0 ≤ (ε ^ 2 + ‖x‖ ^ 2) ^ (p - 2) := Real.rpow_nonneg (by positivity) _
        refine (mul_le_mul_of_nonpos_left hpw (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hp.le (Nat.cast_nonneg _)) hε2.le)).trans ?_
        nlinarith [mul_nonneg (neg_nonneg.mpr hp.le) (mul_nonneg hq (sq_nonneg ‖x‖))]
      have hK0 : 0 ≤ (-p) * d * (ε ^ 2) ^ (p - 1) :=
        mul_nonneg (mul_nonneg (neg_nonneg.mpr hp.le) (Nat.cast_nonneg _)) (Real.rpow_nonneg hε2.le _)
      refine (mul_le_mul (hle.trans (max_le (by linarith) hK0)) hs (sq_nonneg _) hK0).trans_eq ?_
      dsimp only [R, C_ind]
      have hpow : (ε ^ 2) ^ (p - 1) * ε ^ 2 = (ε ^ 2) ^ p := by
        rw [← Real.rpow_add_one hε2.ne', show p - 1 + 1 = p by ring]
      linear_combination (-p) * d * (d + 1 : ℝ) ^ 2 * hpow
    · rw [Set.indicator_of_notMem hx]
      have hx' : R ≤ ‖x‖ := le_of_not_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
      have hnn : 0 ≤ halfLap (radialPow (ε ^ 2) p) x := by
        rw [radialPow_halfLap hε2, hbr]
        refine mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg hp.le (Real.rpow_nonneg (by positivity) _)) ?_
        have hs : R ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (by dsimp [R]; positivity) (norm_nonneg _)).mpr hx'
        have hd2 : (d : ℝ) ≤ (d + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
        dsimp only [R] at hs
        nlinarith [mul_le_mul_of_nonneg_right hd2 (sq_nonneg ε)]
      rw [max_eq_right (neg_nonpos.mpr hnn)] at hle
      exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg _)
  have hupper : (∫ x : Space d, max (-halfLap (radialBump (ε ^ 2) p) x) 0 * ‖x‖ ^ 2) ≤ K * δ := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => mul_nonneg (le_max_right _ _) (sq_nonneg _))
      ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall)
      (Eventually.of_forall hpt)).trans_eq ?_
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real_def,
      volume.addHaar_closedBall 0 hR0, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR0 _),
      ← Measure.real_def, finrank_euclideanSpace_fin]
    have hexp : ε ^ d * (ε ^ 2) ^ p = δ := by
      rw [← Real.sqrt_sq hδ.le, show δ ^ 2 = ε from rfl, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_natCast_mul hε.le 2, ← Real.rpow_add hε]
      congr 1; dsimp [p]; ring
    dsimp only [R, C_ind, K]; rw [mul_pow, pow_add, ← hexp]; ring
  refine ⟨radialBump (ε ^ 2) p, hb_cd hε2, hb_cs hε2, hb_nn _, hm.trans_le hmono, ?_⟩
  have hsmall : K * δ < η * m := by
    have : (K + 1) * δ ≤ η * m / 2 :=
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (by field_simp)
    nlinarith
  exact hupper.trans_lt (hsmall.trans_le (mul_le_mul_of_nonneg_left hmono hη.le))

def gradientWeight {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, (∑ j, U a j * x j) ^ 2

lemma clm2_pi_expand {k : ℕ} (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) (v w : Fin k → ℝ) :
    B v w = ∑ j, ∑ l, v j * w l * B (Pi.single j 1) (Pi.single l 1) := by
  have hp (u : Fin k → ℝ) : u = ∑ j, u j • Pi.single j (1 : ℝ) := by
    simpa [← Pi.single_smul] using (Finset.univ_sum_single u).symm
  conv_lhs => rw [hp v, hp w]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma bilinear_matrix_pushforward {k n : ℕ} (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ l, (M * D * M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  conv_rhs => arg 2; intro a; arg 2; intro b; rw [clm2_pi_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro b; rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma exists_split_smoothing {k d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (hd : 1 ≤ d) (C : Matrix (Fin k) (Fin k) ℝ) (R : Matrix (Fin k) (Fin d) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ) (hsplit : C = R * R.transpose + Z * C * Z.transpose)
    (e : (Fin k → ℝ) ≃L[ℝ] Space d × V) (z : Fin k → V)
    (hR : ∀ j, e (fun l => R l j) = (EuclideanSpace.single j 1, 0))
    (hZ : ∀ j, e (fun l => Z l j) = (0, z j)) {η : ℝ} (hη : 0 < η) :
    ∃ b : (Fin k → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      0 < ∫ x, b x ∧
      (∫ x, max (-stencilDifferential C b x) 0 * ‖(e x).1‖ ^ 2) < η * ∫ x, b x := by
  let μV : Measure V := Measure.addHaar
  obtain ⟨f, hfs, hfc, hfp, hfm, hfsmall⟩ := exists_radial_smoothing hd (η := η / 2) (by positivity)
  let g₀ : ContDiffBump (0 : V) := ⟨1, 2, by norm_num, by norm_num⟩
  let g : V → ℝ := g₀
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := g₀.contDiff
  have hgc : HasCompactSupport g := g₀.hasCompactSupport
  have hgp : ∀ y, 0 ≤ g y := g₀.nonneg'
  have hgm : 0 < ∫ y, g y ∂μV := g₀.integral_pos
  let a := halfLap f
  let bV := secondOp C z g
  have hac : Continuous a := secondOp_continuous _ _ hfs
  have hak : HasCompactSupport a := secondOp_compact _ _ hfc
  have hbc : Continuous bV := secondOp_continuous C z hgs
  have hbk : HasCompactSupport bV := secondOp_compact C z hgc
  have haI : Integrable (fun x => max (-a x) 0 * ‖x‖ ^ 2) := by
    have hak' : HasCompactSupport fun x => max (-a x) 0 := by apply hak.comp_left (g := fun r => max (-r) 0); simp
    exact ((hac.neg.max continuous_const).mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hak'.mul_right
  have hfI : Integrable (fun x => f x * ‖x‖ ^ 2) :=
    (hfs.continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hfc.mul_right
  have hgI : Integrable g μV := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hbI : Integrable (fun y => |bV y|) μV := hbc.abs.integrable_of_hasCompactSupport hbk.abs
  let K := (∫ x, f x * ‖x‖ ^ 2) * ∫ y, |bV y| ∂μV
  have hK : 0 ≤ K := mul_nonneg (integral_nonneg fun x => mul_nonneg (hfp x) (sq_nonneg _))
    (integral_nonneg fun _ => abs_nonneg _)
  let M := (∫ x, f x) * ∫ y, g y ∂μV
  have hM : 0 < M := mul_pos hfm hgm
  let t := min (η * M / (4 * (K + 1))) 1
  have ht : 0 < t := lt_min (by positivity) zero_lt_one
  have hsmall : t ^ 2 * K < η / 2 * M := by
    have h1 : (K + 1) * t ≤ η * M / 4 :=
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (by field_simp)
    have h2 : t ^ 2 ≤ t := by nlinarith [min_le_right (η * M / (4 * (K + 1))) 1]
    nlinarith [mul_le_mul_of_nonneg_right h2 hK]
  let et := e.trans ((ContinuousLinearEquiv.refl ℝ (Space d)).prodCongr (ContinuousLinearEquiv.smulLeft (Units.mk0 t ht.ne')))
  let b := (fun y : Space d × V => f y.1 * g y.2) ∘ et
  have hfgs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space d × V => f y.1 * g y.2) :=
    (hfs.comp contDiff_fst).mul (hgs.comp contDiff_snd)
  have hb_cs : HasCompactSupport b :=
    (HasCompactSupport.of_support_subset_isCompact (hfc.prod hgc) fun ⟨_, _⟩ hxy =>
      ⟨subset_closure fun h0 => hxy (by simp [h0]), subset_closure fun h0 => hxy (by simp [h0])⟩).comp_homeomorph et.toHomeomorph
  let _ : ((volume : Measure (Fin k → ℝ)).map et).IsAddHaarMeasure := et.isAddHaarMeasure_map volume
  let c : ℝ := ((volume : Measure (Fin k → ℝ)).map et).addHaarScalarFactor (volume.prod μV)
  have hc : 0 < c := by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hchange (φ : Space d × V → ℝ) (hφ : Continuous φ) : (∫ x, φ (et x)) = c * ∫ y, φ y ∂volume.prod μV := by
    rw [← integral_map et.continuous.measurable.aemeasurable hφ.aestronglyMeasurable,
      Measure.isAddLeftInvariant_eq_smul ((volume : Measure (Fin k → ℝ)).map et) (volume.prod μV)]
    simp [c, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hmass : (∫ x, b x) = c * M := by
    change (∫ x, f (et x).1 * g (et x).2) = _; rw [hchange _ hfgs.continuous, integral_prod_mul]
  have hdiff (x : Fin k → ℝ) : stencilDifferential C b x =
      g (et x).2 * a (et x).1 + t ^ 2 * f (et x).1 * bV (et x).2 := by
    have hb_comp (v w : Fin k → ℝ) : hessianB b x v w =
        hessianB (fun y : Space d × V => f y.1 * g y.2) (et x) (et v) (et w) :=
      hessianB_linear_comp hfgs et.toContinuousLinearMap x v w
    have hhr (j : Fin d) : et (fun l => R l j) = (EuclideanSpace.single j 1, 0) := by simp [et, hR]
    have hhz (j : Fin k) : et (fun l => Z l j) = (0, t • z j) := by simp [et, hZ, Units.smul_def]
    unfold stencilDifferential secondOp
    have hcon : ∑ j, ∑ l, C j l * hessianB b x (Pi.single j 1) (Pi.single l 1) =
        (∑ j, hessianB b x (fun m => R m j) (fun m => R m j)) +
        ∑ j, ∑ l, C j l * hessianB b x (fun m => Z m j) (fun m => Z m l) := by
      conv_lhs => rw [hsplit]
      simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) (by simpa [Matrix.one_apply] using bilinear_matrix_pushforward (hessianB b x) R 1)
        (bilinear_matrix_pushforward (hessianB b x) Z C)
    have hhor : ∑ j, hessianB b x (fun m => R m j) (fun m => R m j) =
        g (et x).2 * ∑ j, hessianB f (et x).1 (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
      simp only [hb_comp, hhr, hessianB_prod_fst hfs hgs, Finset.mul_sum]
    have hver : ∑ j, ∑ l, C j l * hessianB b x (fun m => Z m j) (fun m => Z m l) =
        t ^ 2 * f (et x).1 * ∑ j, ∑ l, C j l * hessianB g (et x).2 (z j) (z l) := by
      simp only [hb_comp, hhz, hessianB_prod_snd hfs hgs, map_smul, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hcon, hhor, hver]; dsimp only [a, bV]; rw [halfLap_apply]; unfold secondOp; ring
  let φ : Space d × V → ℝ := fun y => max (-(g y.2 * a y.1 + t ^ 2 * f y.1 * bV y.2)) 0 * ‖y.1‖ ^ 2
  have hφ : Continuous φ :=
    ((((hgs.continuous.comp continuous_snd).mul (hac.comp continuous_fst)).add
      ((continuous_const.mul (hfs.continuous.comp continuous_fst)).mul (hbc.comp continuous_snd))).neg.max
      continuous_const).mul (continuous_fst.norm.pow 2)
  have hneg_eq : (∫ x, max (-stencilDifferential C b x) 0 * ‖(e x).1‖ ^ 2) = c * ∫ y, φ y ∂volume.prod μV := by
    conv_lhs => arg 2; intro x; rw [hdiff, show (e x).1 = (et x).1 from rfl]
    exact hchange φ hφ
  have hprod_bd : (∫ y, φ y ∂volume.prod μV) ≤
      (∫ x, max (-a x) 0 * ‖x‖ ^ 2) * (∫ y, g y ∂μV) + t ^ 2 * K := by
    have hI := (haI.mul_prod hgI).add ((hfI.mul_prod hbI).const_mul (t ^ 2))
    refine (integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (le_max_right _ _) (sq_nonneg _))
      hI (Eventually.of_forall fun y => ?_)).trans_eq ?_
    · have hm : max (-(g y.2 * a y.1 + t ^ 2 * f y.1 * bV y.2)) 0 ≤
          g y.2 * max (-a y.1) 0 + t ^ 2 * f y.1 * |bV y.2| := max_le
        (by nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-a y.1) 0) (hgp y.2),
          mul_le_mul_of_nonneg_left (neg_le_abs (bV y.2)) (mul_nonneg (sq_nonneg t) (hfp y.1))])
        (by have := hgp y.2; have := hfp y.1; positivity)
      exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans_eq (by dsimp only [Pi.add_apply]; ring)
    · change (∫ y : Space d × V, (max (-a y.1) 0 * ‖y.1‖ ^ 2 * g y.2) +
          t ^ 2 * ((f y.1 * ‖y.1‖ ^ 2) * |bV y.2|) ∂volume.prod μV) = _
      rw [integral_add (haI.mul_prod hgI) ((hfI.mul_prod hbI).const_mul (t ^ 2)),
        integral_const_mul, integral_prod_mul (fun x => max (-a x) 0 * ‖x‖ ^ 2) g,
        integral_prod_mul (fun x => f x * ‖x‖ ^ 2) fun y => |bV y|]
  have hfinal : (∫ y, φ y ∂volume.prod μV) < η * M := by
    dsimp [M] at hsmall ⊢; nlinarith [mul_lt_mul_of_pos_right hfsmall hgm]
  refine ⟨b, hfgs.comp et.contDiff, hb_cs, by rw [hmass]; positivity, ?_⟩
  rw [hneg_eq, hmass]; nlinarith [mul_lt_mul_of_pos_left hfinal hc]

abbrev realLattice (k : ℕ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))
def latticeSample {k : ℕ} (n : ℕ) (γ : Fin k → ℤ) : Fin k → ℝ := fun j => (γ j : ℝ) / n

lemma lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) = ∑' x : ↑(s ∩ (n : ℝ)⁻¹ • realLattice k), f x := by
  let _ : NeZero n := ⟨hn⟩
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmem (γ : Fin k → ℤ) : latticeSample n γ ∈ (n : ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)) := by
    rw [← Submodule.coe_pointwise_smul]
    exact BoxIntegral.unitPartition.mem_smul_span_iff.mpr fun j => ⟨γ j, by change (γ j : ℝ) = n * ((γ j : ℝ) / n); field_simp⟩
  let e : {γ : Fin k → ℤ // latticeSample n γ ∈ s} ≃ ↑(s ∩ (n : ℝ)⁻¹ • realLattice k) :=
    Equiv.ofBijective (fun γ => ⟨latticeSample n γ, γ.2, hmem γ.1⟩) ⟨fun x y h => Subtype.ext <| funext fun j => by
      exact_mod_cast (div_left_inj' hn').mp (congrFun (congrArg Subtype.val h) j), fun ⟨y, hy1, hy2⟩ => by
      rw [← Submodule.coe_pointwise_smul] at hy2
      choose γ hγ using BoxIntegral.unitPartition.mem_smul_span_iff.mp hy2
      have hγx : latticeSample n γ = y := funext fun j => by
        simp only [latticeSample, show (γ j : ℝ) = n * y j from hγ j, mul_div_cancel_left₀ _ hn']
      exact ⟨⟨γ, hγx.symm ▸ hy1⟩, Subtype.ext hγx⟩⟩
  rw [← tsum_subtype_eq_of_support_subset (s := {γ | latticeSample n γ ∈ s}) fun _ hγ => hf hγ]
  exact e.tsum_eq fun x => f x

lemma lattice_riemann_perturb {k : ℕ} {f : (Fin k → ℝ) → ℝ} {g : ℕ → (Fin k → ℝ) → ℝ}
    (hf : Continuous f) {R : ℝ} (hR : 0 < R) (hfs : Function.support f ⊆ Metric.closedBall 0 R)
    (hgs : ∀ n, 1 ≤ n → Function.support (g n) ⊆ Metric.closedBall 0 R)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hbd : ∀ n, 1 ≤ n → ∀ x, |g n x - f x| ≤ ε n) :
    Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ, g n (latticeSample n δ)) / (n : ℝ) ^ k) atTop (𝓝 (∫ x, f x)) := by
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have hbase := tendsto_tsum_div_pow_atTop_integral s f hf Metric.isBounded_closedBall measurableSet_closedBall hfront
  rw [Fintype.card_fin, ← integral_indicator measurableSet_closedBall, Set.indicator_eq_self.mpr hfs] at hbase
  have hlim := hε.mul (tendsto_card_div_pow_atTop_volume s Metric.isBounded_closedBall measurableSet_closedBall hfront)
  rw [zero_mul, Fintype.card_fin] at hlim
  have hdiff : Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ, g n (latticeSample n δ)) / (n : ℝ) ^ k -
      (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • realLattice k), f x) / (n : ℝ) ^ k) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    let G : Type _ := ↑(s ∩ (n : ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)))
    have hGfin : (s ∩ (n : ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))).Finite := by
      rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (Nat.cast_ne_zero.mpr hn0))]
      exact ZSpan.setFinite_inter _ Metric.isBounded_closedBall
    let _ : Fintype G := hGfin.fintype
    rw [Real.norm_eq_abs, lattice_tsum_eq_grid hn0 s (g n) (hgs n hn),
      ← sub_div, abs_div, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ k)]
    have hsum_G : |(∑' x : G, g n x) - ∑' x : G, f x| ≤ Nat.card G * ε n := by
      rw [tsum_fintype, tsum_fintype, ← Finset.sum_sub_distrib]
      calc |∑ x : G, (g n x - f x)| ≤ ∑ x : G, |g n x - f x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : G, ε n := Finset.sum_le_sum fun x _ => hbd n hn x
        _ = Nat.card G * ε n := by simp [Nat.card_eq_fintype_card]
    exact (div_le_div_of_nonneg_right hsum_G (by positivity)).trans_eq (by ring)
  simpa using hdiff.add hbase

lemma stencil_taylor_uniform {k : ℕ} (S : Finset (Fin k → ℤ))
    (q : (Fin k → ℤ) → ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S, q γ = 0) (hfirst : ∀ j, ∑ γ ∈ S, q γ * (γ j : ℝ) = 0)
    (hsecond : ∀ j l, ∑ γ ∈ S, q γ * (γ j : ℝ) * (γ l : ℝ) = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ x,
      |t ^ 2 * (∑ γ ∈ S, q γ * b (x + (-t⁻¹) • fun j => (γ j : ℝ))) - stencilDifferential C b x| ≤ K / t := by
  let v (γ : Fin k → ℤ) (j : Fin k) : ℝ := γ j
  obtain ⟨K₀, hK₀⟩ := (hb.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hbc.iteratedFDeriv 3)
  have hK₀_nn : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ 0)
  have hTaylor3 (x h : Fin k → ℝ) :
      |b (x + h) - b x - fderiv ℝ b x h - (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 b x ![h, h]| ≤ K₀ * ‖h‖ ^ 3 := by
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := b) (x := x) (y := h)
      fun _ _ => (hb.of_le (by norm_cast)).contDiffAt
    have he : b (x + h) - b x - fderiv ℝ b x h - (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 b x ![h, h] =
        (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedFDeriv ℝ 3 b (x + t • h) (fun _ => h) := by
      have hvec : (fun _ : Fin 2 => h) = ![h, h] := by ext i; fin_cases i <;> rfl
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial,
        Nat.cast_one, Nat.cast_mul, inv_one, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
        smul_eq_mul, hvec] at ht
      linarith
    rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hi : |∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedFDeriv ℝ 3 b (x + t • h) (fun _ => h)| ≤ K₀ * ‖h‖ ^ 3 := by
      have hbd (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
          ‖(1 - t) ^ 2 * iteratedFDeriv ℝ 3 b (x + t • h) (fun _ => h)‖ ≤ K₀ * ‖h‖ ^ 3 := by
        obtain ⟨ht0, ht1⟩ : 0 < t ∧ t ≤ 1 := by simpa using ht
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hm := (iteratedFDeriv ℝ 3 b (x + t • h)).le_opNorm (fun _ => h)
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
        exact (mul_le_mul (by nlinarith : (1 - t) ^ 2 ≤ 1)
          (hm.trans (mul_le_mul_of_nonneg_right (hK₀ _) (by positivity))) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd
    nlinarith [mul_nonneg hK₀_nn (pow_nonneg (norm_nonneg h) 3)]
  let K := ∑ γ ∈ S, |q γ| * K₀ * ‖v γ‖ ^ 3
  refine ⟨K, Finset.sum_nonneg fun _ _ => by positivity, fun t ht x => ?_⟩
  have hl : ∑ γ ∈ S, q γ * fderiv ℝ b x (v γ) = 0 := by
    have hv_exp (γ : Fin k → ℤ) : v γ = ∑ j, v γ j • Pi.single j (1 : ℝ) := by ext; simp [Pi.single_apply]
    conv_lhs => arg 2; intro γ; rw [hv_exp γ]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show (∑ γ ∈ S, q γ * (v γ j * fderiv ℝ b x (Pi.single j 1))) =
      (∑ γ ∈ S, q γ * v γ j) * fderiv ℝ b x (Pi.single j 1) by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, hfirst j, zero_mul]
  have hb2 : ∑ γ ∈ S, q γ * hessianB b x (v γ) (v γ) =
      ∑ j, ∑ l, C j l * hessianB b x (Pi.single j 1) (Pi.single l 1) := by
    conv_lhs => arg 2; intro γ; rw [clm2_pi_expand (hessianB b x)]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← hsecond, Finset.sum_mul]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  let rem (γ : Fin k → ℤ) := b (x + (-t⁻¹) • v γ) - b x - fderiv ℝ b x ((-t⁻¹) • v γ) -
    (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ, (-t⁻¹) • v γ]
  have hrem_eq : t ^ 2 * (∑ γ ∈ S, q γ * b (x + (-t⁻¹) • v γ)) - stencilDifferential C b x =
      t ^ 2 * ∑ γ ∈ S, q γ * rem γ := by
    have hsc (γ : Fin k → ℤ) : iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ, (-t⁻¹) • v γ] =
        (t⁻¹) ^ 2 * hessianB b x (v γ) (v γ) := by
      simp only [← hessianB_eq, map_smul, _root_.smul_apply, smul_eq_mul]; ring
    simp only [rem, mul_sub, Finset.sum_sub_distrib, map_smul, smul_eq_mul, hsc]
    have hz0 : ∑ γ ∈ S, q γ * b x = 0 := by rw [← Finset.sum_mul, hzero, zero_mul]
    have hz1 : ∑ γ ∈ S, q γ * (-t⁻¹ * fderiv ℝ b x (v γ)) = 0 := by
      rw [show (∑ γ ∈ S, q γ * (-t⁻¹ * fderiv ℝ b x (v γ))) = -t⁻¹ * ∑ γ ∈ S, q γ * fderiv ℝ b x (v γ) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hl, mul_zero]
    have hz2 : ∑ γ ∈ S, q γ * ((1 / 2 : ℝ) * ((t⁻¹) ^ 2 * hessianB b x (v γ) (v γ))) =
        (t⁻¹) ^ 2 * stencilDifferential C b x := by
      unfold stencilDifferential secondOp; rw [← hb2, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hz0, hz1, hz2]; field_simp; ring
  rw [hrem_eq, abs_mul, abs_of_nonneg (sq_nonneg t)]
  calc t ^ 2 * |∑ γ ∈ S, q γ * rem γ|
    _ ≤ t ^ 2 * ∑ γ ∈ S, |q γ| * |rem γ| := by
      gcongr; simpa [abs_mul] using Finset.abs_sum_le_sum_abs (fun γ => q γ * rem γ) S
    _ ≤ t ^ 2 * ∑ γ ∈ S, |q γ| * (K₀ * (t⁻¹) ^ 3 * ‖v γ‖ ^ 3) := by
      gcongr with γ _
      simpa [rem, norm_smul, abs_of_pos ht, mul_pow, mul_assoc] using hTaylor3 x ((-t⁻¹) • v γ)
    _ = K / t := by
      dsimp [K]; rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by field_simp

theorem exists_rational_stencil {k d : ℕ} (hd : 1 ≤ d)
    (ν : AddMonoidAlgebra ℚ (Fin k → ℤ)) (C : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U * C * U.transpose = 1)
    (hzero : ∑ γ ∈ ν.coeff.support, (ν.coeff γ : ℝ) = 0)
    (hfirst : ∀ j, ∑ γ ∈ ν.coeff.support, (ν.coeff γ : ℝ) * (γ j : ℝ) = 0)
    (hsecond : ∀ j l, ∑ γ ∈ ν.coeff.support, (ν.coeff γ : ℝ) * (γ j : ℝ) * (γ l : ℝ) = C j l)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (p : AddMonoidAlgebra ℚ (Fin k → ℤ)),
      1 ≤ n ∧ 0 < (p.coeff.sum fun _ q => q : ℚ) ∧
      (n : ℝ) ^ 2 * (ν * p).coeff.sum (fun δ q => max (-(q : ℝ)) 0 * gradientWeight U (latticeSample n δ)) <
        η * ((p.coeff.sum fun _ q => q : ℚ) : ℝ) := by
  classical
  let R₀ := C * U.transpose
  let Z : Matrix (Fin k) (Fin k) ℝ := 1 - R₀ * U
  have hUR : U * R₀ = 1 := by simpa only [R₀, ← Matrix.mul_assoc] using hU
  have hUZ : U * Z = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hUR, Matrix.one_mul, sub_self]
  have hsplit : C = R₀ * R₀.transpose + Z * C * Z.transpose := by
    have hRt : R₀.transpose = U * C := by simp [R₀, Matrix.transpose_mul, hC.eq]
    have hRR : R₀.transpose * U.transpose = 1 := by rw [← Matrix.transpose_mul, hUR, Matrix.transpose_one]
    have h1 : R₀ * U * C = R₀ * R₀.transpose := by rw [hRt, Matrix.mul_assoc]
    have h2 : C * (U.transpose * R₀.transpose) = R₀ * R₀.transpose := (Matrix.mul_assoc _ _ _).symm
    have h3 : R₀ * R₀.transpose * (U.transpose * R₀.transpose) = R₀ * R₀.transpose := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc R₀.transpose, hRR, Matrix.one_mul]
    rw [show Z.transpose = 1 - U.transpose * R₀.transpose by simp [Z, Matrix.transpose_sub, Matrix.transpose_mul]]
    dsimp only [Z]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h1, h2, h3]; abel
  let eH : Space d ≃ₗ[ℝ] (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u : (Fin k → ℝ) →ₗ[ℝ] Space d := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let rMap : Space d →ₗ[ℝ] (Fin k → ℝ) := (Matrix.toLin' R₀).comp eH.toLinearMap
  have hur (y : Space d) : u (rMap y) = y := by
    simp only [u, rMap, LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]; exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] Space d × V := (show (Fin k → ℝ) ≃ₗ[ℝ] Space d × V from
    { toFun := fun x => (u x, ⟨x - rMap (u x), by rw [LinearMap.mem_ker, map_sub, hur, sub_self]⟩)
      invFun := fun v => rMap v.1 + v.2
      left_inv := fun x => by simp
      right_inv := fun v => Prod.ext (by simp [hur])
        (Subtype.ext (by change rMap v.1 + (v.2 : Fin k → ℝ) - rMap (u (rMap v.1 + v.2)) = v.2; simp [hur]))
      map_add' := fun _ _ => by ext <;> simp [map_add]; abel
      map_smul' := fun _ _ => by ext <;> simp [map_smul, smul_sub] }).toContinuousLinearEquiv
  have hR (j : Fin d) : e (fun l => R₀ l j) = (EuclideanSpace.single j 1, 0) := by
    have hrj : rMap (EuclideanSpace.single j 1) = fun l => R₀ l j := by
      change R₀.mulVec (Pi.single j 1) = _; rw [Matrix.mulVec_single]; simp; rfl
    rw [← hrj]; exact Prod.ext (hur _) (Subtype.ext (by change rMap _ - rMap (u (rMap _)) = 0; rw [hur, sub_self]))
  have hZv (j : Fin k) : (fun l => Z l j) ∈ V := by
    rw [LinearMap.mem_ker]; change eH.symm (U.mulVec fun l => Z l j) = 0
    rw [show (U.mulVec fun l => Z l j) = 0 by ext a; exact congrFun (congrFun hUZ a) j, map_zero]
  let _ : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  obtain ⟨b, hb, hbc, hbI, hbη⟩ := exists_split_smoothing hd C R₀ Z hsplit e
    (fun j => ⟨fun l => Z l j, hZv j⟩) hR
    (fun j => Prod.ext (hZv j) (Subtype.ext (by change (fun l => Z l j) - rMap (u _) = _; rw [show u _ = 0 from hZv j, map_zero, sub_zero]))) hη
  have hw_eq (x : Fin k → ℝ) : ‖(e x).1‖ ^ 2 = gradientWeight U x := by
    change ‖eH.symm (U.mulVec x)‖ ^ 2 = _; rw [EuclideanSpace.real_norm_sq_eq]; rfl
  simp only [hw_eq] at hbη
  let S := ν.coeff.support
  let qf (γ : Fin k → ℤ) : ℝ := ν.coeff γ
  let vf (γ : Fin k → ℤ) (j : Fin k) : ℝ := γ j
  obtain ⟨r, hr, hbr⟩ := hbc.exists_pos_le_norm
  let Vnorm := ∑ γ ∈ S, ‖vf γ‖
  have hVn : 0 ≤ Vnorm := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let R := r + Vnorm + 1
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hbsupp : tsupport b ⊆ Metric.closedBall 0 R :=
    (closure_minimal (fun y hy => by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_not_gt fun h => hy (hbr y h.le))
      Metric.isClosed_closedBall).trans (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith))
  let f := fun x => max (-stencilDifferential C b x) 0 * gradientWeight U x
  let g := fun (n : ℕ) x => max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, qf γ * b (x + (-(n : ℝ)⁻¹) • vf γ))) 0 * gradientWeight U x
  have hfr : Function.support f ⊆ Metric.closedBall 0 R := fun x hx => hbsupp <| Classical.byContradiction fun h => hx <| by
    have hz := image_eq_zero_of_notMem_tsupport (fun hs => h (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) 2 hs))
    simp [f, stencilDifferential, secondOp, hessianB_eq, hz]
  have hgr (n : ℕ) (hn : 1 ≤ n) : Function.support (g n) ⊆ Metric.closedBall 0 R := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    have hni : |(n : ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr hn)
    have hsum : ∑ γ ∈ S, qf γ * b (x + (-(n : ℝ)⁻¹) • vf γ) = 0 := Finset.sum_eq_zero fun γ hγ => by
      have hsh : ‖(-(n : ℝ)⁻¹) • vf γ‖ ≤ Vnorm := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact (mul_le_mul_of_nonneg_right hni (norm_nonneg _)).trans
          (by simpa using Finset.single_le_sum (fun _ _ => norm_nonneg _) hγ)
      have htri := norm_le_norm_add_norm_sub (x + (-(n : ℝ)⁻¹) • vf γ) x
      rw [add_sub_cancel_left] at htri
      rw [hbr _ (by dsimp [R] at h; linarith), mul_zero]
    exact hx (by dsimp only [g]; rw [hsum]; simp)
  obtain ⟨W, hW⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_bound_of_continuousOn
    (show Continuous (gradientWeight U) by unfold gradientWeight; fun_prop).continuousOn
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp [hRpos.le]))
  obtain ⟨K, hK, hStencil⟩ := stencil_taylor_uniform S qf C hzero hfirst hsecond hb hbc
  have hZ := lattice_riemann_perturb (g := fun _ => b) hb.continuous hRpos
    (subset_closure.trans hbsupp) (fun _ _ => subset_closure.trans hbsupp) tendsto_const_nhds (by simp)
  have hN := lattice_riemann_perturb (f := f) (g := g)
    (((secondOp_continuous C _ hb).neg.max continuous_const).mul (by unfold gradientWeight; fun_prop))
    hRpos hfr hgr (ε := fun n => K * W / n) (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop) fun n hn x => by
      by_cases hx : x ∈ Metric.closedBall (0 : Fin k → ℝ) R
      · have hw : |gradientWeight U x| ≤ W := by simpa [Real.norm_eq_abs] using hW x hx
        have hm := (abs_max_sub_max_le_abs
          (-((n : ℝ) ^ 2 * ∑ γ ∈ S, qf γ * b (x + (-(n : ℝ)⁻¹) • vf γ))) (-stencilDifferential C b x) 0).trans
          (by simpa only [neg_sub_neg, abs_sub_comm] using hStencil n (Nat.cast_pos.mpr (by omega)) x)
        dsimp only [g, f]; rw [← sub_mul, abs_mul]
        exact (mul_le_mul hm hw (abs_nonneg _) (by positivity)).trans_eq (by ring)
      · rw [Function.notMem_support.mp fun hh => hx (hgr n hn hh),
          Function.notMem_support.mp fun hh => hx (hfr hh), sub_self, abs_zero]
        positivity
  obtain ⟨n, hn, hp, he⟩ := (eventually_ge_atTop 1 |>.and
    ((tendsto_const_nhds.eventually_lt hZ hbI).and (hN.eventually_lt (tendsto_const_nhds.mul hZ) hbη))).exists
  let a := fun γ : Fin k → ℤ => b (latticeSample n γ)
  have hnf : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hshift (δ γ : Fin k → ℤ) : latticeSample n δ + (-(n : ℝ)⁻¹) • vf γ = latticeSample n (δ - γ) := by
    ext j; simp only [latticeSample, vf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Int.cast_sub]; ring
  have hscale (δ : Fin k → ℤ) :
      max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, qf γ * a (δ - γ))) 0 * gradientWeight U (latticeSample n δ) =
      (n : ℝ) ^ 2 * (max (-(∑ γ ∈ S, qf γ * a (δ - γ))) 0 * gradientWeight U (latticeSample n δ)) := by
    rw [← mul_neg, ← mul_zero ((n : ℝ) ^ 2), ← mul_max_of_nonneg _ _ (sq_nonneg (n : ℝ)), mul_assoc, mul_zero]
  simp only [g, hshift] at he
  change (∑' δ, max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, qf γ * a (δ - γ))) 0 * gradientWeight U (latticeSample n δ)) / (n : ℝ) ^ k <
    η * ((∑' γ, a γ) / (n : ℝ) ^ k) at he
  simp only [hscale, tsum_mul_left] at he
  have hp0 : 0 < ∑' γ, a γ := (div_pos_iff_of_pos_right (pow_pos hnf k)).mp hp
  have han : (n : ℝ) ^ 2 * ∑' δ, max (-(∑ γ ∈ S, qf γ * a (δ - γ))) 0 * gradientWeight U (latticeSample n δ) <
      η * ∑' γ, a γ := (div_lt_div_iff_of_pos_right (pow_pos hnf k)).mp (by simpa [← mul_div_assoc] using he)
  let m : ℕ := ⌈r * n⌉₊
  let E : Finset (Fin k → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m
  have haE : ∀ γ ∉ E, a γ = 0 := fun γ hγ => by
    simp only [E, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le, not_forall, not_le] at hγ
    obtain ⟨j, hj⟩ := hγ
    have h1 : r ≤ |(γ j : ℝ)| / n := (le_div_iff₀ hnf).mpr ((Nat.le_ceil (r * n)).trans (by exact_mod_cast hj.le))
    exact hbr _ (h1.trans (by simpa [latticeSample, abs_div, abs_of_pos hnf] using norm_le_pi_norm (latticeSample n γ) j))
  let w (δ : Fin k → ℤ) := gradientWeight U (latticeSample n δ)
  let Kset := S + E
  let ζf (d : (Fin k → ℤ) → ℝ) := ∑ β ∈ E, d β
  let Nf (d : (Fin k → ℤ) → ℝ) := ∑ δ ∈ Kset, max (-(∑ γ ∈ S,
    qf γ * if δ - γ ∈ E then d (δ - γ) else 0)) 0 * w δ
  have hζc : Continuous ζf := by unfold ζf; fun_prop
  have hNc : Continuous Nf := continuous_finsetSum _ fun δ _ => ((continuous_finsetSum _ fun γ _ =>
    continuous_const.mul (by by_cases h : δ - γ ∈ E <;> simp [h] <;> fun_prop)).neg.max continuous_const).mul continuous_const
  have ha_sum : ∑' γ, a γ = ∑ β ∈ E, a β := tsum_eq_sum haE
  have ha_N : Nf a = ∑' δ, max (-(∑ γ ∈ S, qf γ * a (δ - γ))) 0 * w δ := by
    rw [tsum_eq_sum (s := Kset) fun δ hδ => by
      have hz : ∑ γ ∈ S, qf γ * a (δ - γ) = 0 := Finset.sum_eq_zero fun γ hγ => by
        rw [haE _ fun h => hδ (Finset.mem_add.mpr ⟨γ, hγ, δ - γ, h, by abel⟩), mul_zero]
      simp [hz]]
    refine Finset.sum_congr rfl fun δ _ => congrArg (fun x => max (-x) 0 * w δ) <|
      Finset.sum_congr rfl fun γ _ => by by_cases h : δ - γ ∈ E <;> simp [h, haE]
  obtain ⟨q, hq0, hqN⟩ := (DenseRange.piMap fun _ : Fin k → ℤ => Rat.denseRange_cast).exists_mem_open
    ((isOpen_lt continuous_const hζc).inter (isOpen_lt (continuous_const.mul hNc) (continuous_const.mul hζc)))
    ⟨a, by dsimp [ζf]; rwa [← ha_sum], by change (n : ℝ) ^ 2 * Nf a < η * ζf a; dsimp [ζf]; rwa [ha_N, ← ha_sum]⟩
  change 0 < ζf (fun i => q i) at hq0
  change (n : ℝ) ^ 2 * Nf (fun i => q i) < η * ζf (fun i => q i) at hqN
  let p : AddMonoidAlgebra ℚ (Fin k → ℤ) := ∑ β ∈ E, AddMonoidAlgebra.single β (q β)
  have hp_c (β : Fin k → ℤ) : p.coeff β = if β ∈ E then q β else 0 := by
    simp [p, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hp_m : (p.coeff.sum fun _ x => x : ℚ) = ∑ β ∈ E, q β := by
    rw [Finsupp.sum_of_support_subset _ (s := E) (fun β hβ => by contrapose! hβ; simp [hp_c, hβ]) _ (by simp)]
    exact Finset.sum_congr rfl fun β hβ => by simp [hp_c, hβ]
  have hvp (δ : Fin k → ℤ) : ((ν * p).coeff δ : ℝ) = ∑ γ ∈ S,
      qf γ * if δ - γ ∈ E then (q (δ - γ) : ℝ) else 0 := by
    have h0 : (ν * p).coeff δ = ∑ γ ∈ S, ν.coeff γ * p.coeff (δ - γ) := by
      rw [AddMonoidAlgebra.coeff_mul]
      refine Finset.sum_congr rfl fun γ _ => ?_
      have he (β : Fin k → ℤ) : γ + β = δ ↔ β = δ - γ := ⟨eq_sub_of_add_eq', fun h => by subst h; abel⟩
      simpa [Finsupp.sum, he] using fun h => Or.inr h
    rw [h0]; push_cast; exact Finset.sum_congr rfl fun γ _ => by rw [hp_c, apply_ite Rat.cast, Rat.cast_zero]
  refine ⟨n, p, hn, by exact_mod_cast (by simpa [hp_m, ζf] using hq0 : (0 : ℝ) < (p.coeff.sum fun _ x => x : ℚ)), ?_⟩
  rw [Finsupp.sum_of_support_subset _ (s := Kset) (fun δ hδ => by
    contrapose! hδ; rw [Finsupp.notMem_support_iff, ← Rat.cast_eq_zero (α := ℝ), hvp]
    exact Finset.sum_eq_zero fun γ hγ => by
      rw [ite_eq_right_iff.mpr fun h => (hδ (Finset.mem_add.mpr ⟨γ, hγ, δ - γ, h, by abel⟩)).elim, mul_zero]) _ (by simp)]
  rw [hp_m]; push_cast; simpa only [hvp] using hqN

end EuclideanRamsey
end
end OAI
