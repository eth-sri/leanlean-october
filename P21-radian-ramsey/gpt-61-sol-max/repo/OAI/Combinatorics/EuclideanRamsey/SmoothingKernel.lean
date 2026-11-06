/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.TensorDescent

@[expose] public section

open scoped ContDiff Topology

namespace OAI.EuclideanRamsey


noncomputable section


open MeasureTheory Polynomial

def smoothPositivePart (t : ℝ) : ℝ := t * expNegInvGlue t

def smoothPositivePart' (t : ℝ) : ℝ := (1 + t⁻¹) * expNegInvGlue t

def smoothPositivePart'' (t : ℝ) : ℝ := t⁻¹ ^ 3 * expNegInvGlue t

lemma smoothPositivePart_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart (smoothPositivePart' t) t := by
  have hg : HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) t
  have h := (hasDerivAt_id t).mul hg
  change HasDerivAt smoothPositivePart _ t at h
  grind [OAI.EuclideanRamsey.smoothPositivePart, OAI.EuclideanRamsey.smoothPositivePart']

lemma smoothPositivePart'_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart' (smoothPositivePart'' t) t := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 + X : ℝ[X]) t
  simp at h
  change HasDerivAt smoothPositivePart' _ t at h
  grind [OAI.EuclideanRamsey.smoothPositivePart', OAI.EuclideanRamsey.smoothPositivePart'']

lemma smoothPositivePart_nonneg (t : ℝ) : 0 ≤ smoothPositivePart t := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]
  · exact mul_nonneg (le_of_not_ge ht) (expNegInvGlue.nonneg t)

lemma smoothPositivePart_pos {t : ℝ} (ht : 0 < t) : 0 < smoothPositivePart t :=
  mul_pos ht (expNegInvGlue.pos_of_pos ht)

lemma smoothPositivePart'_bounds (t : ℝ) :
    0 ≤ smoothPositivePart' t ∧ smoothPositivePart' t ≤ 1 := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart', expNegInvGlue.zero_of_nonpos ht]
  have ht0 := lt_of_not_ge ht
  constructor
  · exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)
  · unfold smoothPositivePart'
    rw [expNegInvGlue, ite_eq_right ht, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    simpa [add_comm] using Real.add_one_le_exp (t⁻¹)

lemma smoothPositivePart''_nonneg (t : ℝ) : 0 ≤ smoothPositivePart'' t := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart'', expNegInvGlue.zero_of_nonpos ht]
  · have ht0  := lt_of_not_ge ht
    exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialPower (a p : ℝ) (x : E) : ℝ := (a + ‖x‖^2) ^ p

lemma radialPower_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ ∞ (radialPower (E := E) a p) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    (fun x => ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _)))

lemma radialPower_hasFDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    HasFDerivAt (radialPower a p)
      ((2*p*(a+‖x‖^2)^(p-1)) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := p) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _))))
  change HasFDerivAt (radialPower a p) _ x at h
  apply h.congr_fderiv
  ext v
  simp
  ring

def radialBump (a p : ℝ) (x : E) : ℝ :=
  smoothPositivePart (radialPower a p x - 1)

lemma radialBump_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ ∞ (radialBump (E := E) a p) :=
  (contDiff_id.mul expNegInvGlue.contDiff).comp ((radialPower_contDiff ha p).sub contDiff_const)

omit [InnerProductSpace ℝ E] in
lemma radialBump_nonneg (a p : ℝ) (x : E) : 0 ≤ radialBump a p x :=
  smoothPositivePart_nonneg _

variable [FiniteDimensional ℝ E]

def halfLaplacian (f : E → ℝ) (x : E) : ℝ :=
  (1/2 : ℝ) * ∑ i, iteratedFDeriv ℝ 2 f x
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]

lemma radialPower_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialPower a p) x =
      p * (a+‖x‖^2)^(p-2) *
        ((Module.finrank ℝ E : ℝ)*a + (Module.finrank ℝ E + 2*p-2)*‖x‖^2) := by
  classical
  have hg : fderiv ℝ (radialPower a p) =
    (fun y => (2*p*radialPower a (p-1) y) • innerSL ℝ y) :=
    funext fun (y : E) => by simpa [radialPower] using (radialPower_hasFDerivAt ha p y).fderiv
  have hs := (radialPower_hasFDerivAt ha (p-1) x).const_smul (2*p)
  have hd := hs.smul (innerSL ℝ (E := E)).hasFDerivAt
  change HasFDerivAt (fun y => (2*p*radialPower a (p-1) y) • innerSL ℝ y) _ x at hd
  unfold halfLaplacian
  simp only [iteratedFDeriv_two_apply]
  rw [hg]
  simp only [hd.fderiv]
  simp [innerSL,radialPower,show p-1-1=p-2 by ring,
    smul_eq_mul,mul_add,Finset.sum_add_distrib]
  simp only [mul_assoc,←pow_two,←Finset.mul_sum,OrthonormalBasis.sum_sq_inner_left]
  simp only [Real.rpow_sub (show 0 < a+‖x‖^2 by positivity),Real.rpow_one,Real.rpow_two]
  field_simp
  ring



lemma radialBump_compact {a p : ℝ} (ha : 0 < a) (hp : p < 0) :
    HasCompactSupport (radialBump (E := E) a p) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) 1) ?_
  intro x hx
  dsimp only [radialBump,smoothPositivePart]
  rw [expNegInvGlue.zero_of_nonpos ?_,mul_zero]
  have hx1 : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hq : 1 ≤ a+‖x‖^2 := by nlinarith
  exact sub_nonpos.mpr (Real.rpow_le_one_of_one_le_of_nonpos hq hp.le)

lemma radialBump_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialBump a p) x =
      smoothPositivePart' (radialPower a p x-1) * halfLaplacian (radialPower a p) x +
      2 * smoothPositivePart'' (radialPower a p x-1) * p^2 *
        ((a+‖x‖^2)^(p-1))^2 * ‖x‖^2 := by
  classical
  have hf : ContDiff ℝ ∞ (fun y : E => radialPower a p y - 1) :=
    (radialPower_contDiff ha p).sub contDiff_const
  have he v w :
      iteratedFDeriv ℝ 2 (radialBump a p) x ![v,w] =
        smoothPositivePart'' (radialPower a p x-1) *
          (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x v) *
          (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x w) +
        smoothPositivePart' (radialPower a p x-1) *
          iteratedFDeriv ℝ 2 (radialPower a p) x ![v,w] := by
    let f := fun y : E => radialPower a p y-1
    have hfd : fderiv ℝ (fun y : E => radialPower a p y-1) = _ := funext fun _ => fderiv_sub_const 1
    have hf' y := (hf.differentiable (by simp) y).hasFDerivAt
    have hG : fderiv ℝ (radialBump a p) = fun y => smoothPositivePart' (f y) • fderiv ℝ f y := by
      funext y
      exact ((smoothPositivePart_hasDerivAt (f y)).comp_hasFDerivAt y (hf' y)).fderiv
    have hd := ((smoothPositivePart'_hasDerivAt (f x)).comp_hasFDerivAt x (hf' x)).smul
      (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (fun y => smoothPositivePart' (f y) • fderiv ℝ f y) _ x at hd
    simp only [iteratedFDeriv_two_apply]
    rw [hG, hd.fderiv]
    simp only [hfd]
    simp [f, (radialPower_hasFDerivAt ha p x).fderiv, innerSL_apply_apply]
    ring
  unfold halfLaplacian
  simp_rw [he, mul_mul_mul_comm _ _ (2*p*(a+‖x‖^2)^(p-1)) _, mul_assoc,
    ← pow_two, Finset.sum_add_distrib, ← Finset.mul_sum,
    OrthonormalBasis.sum_sq_inner_left]
  ring_nf

lemma radialBump_negative_le {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    max (-halfLaplacian (radialBump a p) x) 0 ≤
      max (-halfLaplacian (radialPower a p) x) 0 := by
  rw [radialBump_halfLaplacian ha]
  have hb := smoothPositivePart'_bounds (radialPower a p x-1)
  have hpp := smoothPositivePart''_nonneg (radialPower a p x-1)
  have hc : 0 ≤ 2 * smoothPositivePart'' (radialPower a p x-1) * p^2 *
      ((a+‖x‖^2)^(p-1))^2 * ‖x‖^2 := by positivity
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left
      (le_max_left (-halfLaplacian (radialPower a p) x) 0) hb.1,
      mul_le_of_le_one_left (le_max_right (-halfLaplacian (radialPower a p) x) 0) hb.2]
  · exact le_max_right _ _

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem exists_radial_smoothing (hn : 1 ≤ Module.finrank ℝ E) {η : ℝ} (hη : 0 < η) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∂μ ∧
      (∫ x, max (-halfLaplacian b x) 0 * ‖x‖^2 ∂μ) < η * ∫ x, b x ∂μ := by
  classical
  let n : ℝ := Module.finrank ℝ E
  let p := 1/4-n/2
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hp : p < 0 := by
    have : (1 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
    dsimp [p]
    linarith
  have hbracket : n+2*p-2 = -(3/2:ℝ) := by dsimp [p]; ring
  have bound {ε} (hε : 0 < ε) x :
      max (-halfLaplacian (radialBump (ε^2) p) x) 0 * ‖x‖^2 ≤
        (Metric.closedBall (0 : E) ((n+1)*ε)).indicator
          (fun _ => (-p)*n*(n+1)^2*(ε^2)^p) x := by
    have hε2 := sq_pos_of_pos hε
    have hle := radialBump_negative_le hε2 p x
    by_cases hx : x ∈ Metric.closedBall (0 : E) ((n+1)*ε)
    · rw [Set.indicator_of_mem hx]
      have hx' : ‖x‖ ≤ (n+1)*ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hs  := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx'
      have hlower : p*n*(ε^2)^(p-1) ≤ halfLaplacian (radialPower (ε^2) p) x := by
        rw [radialPower_halfLaplacian hε2]
        change p*n*(ε^2)^(p-1) ≤ p*(ε^2+‖x‖^2)^(p-2)*(n*ε^2+(n+2*p-2)*‖x‖^2)
        rw [hbracket]
        have hpow := Real.rpow_le_rpow_of_nonpos hε2
          (le_add_of_nonneg_right (sq_nonneg ‖x‖)) (show p-2 ≤ 0 by linarith)
        have hq : 0 ≤ (ε^2+‖x‖^2)^(p-2) := by positivity
        have hstep : p*n*(ε^2)^(p-1) = (p*n*ε^2)*(ε^2)^(p-2) := by
          rw [show p-1 = (p-2)+1 by ring, Real.rpow_add hε2, Real.rpow_one]
          ring
        rw [hstep]
        have hneg : p*n*ε^2 ≤ 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hp.le hn0, sq_nonneg ε]
        have hh := mul_le_mul_of_nonpos_left hpow hneg
        have := mul_nonneg (neg_nonneg.mpr hp.le) (mul_nonneg hq (sq_nonneg ‖x‖))
        nlinarith
      have hK : 0 ≤ (-p)*n*(ε^2)^(p-1) := by
        have := neg_nonneg.mpr hp.le
        positivity
      have hmax : max (-halfLaplacian (radialPower (ε^2) p) x) 0 ≤
          (-p)*n*(ε^2)^(p-1) := max_le (by linarith) hK
      calc
        _ ≤ ((-p)*n*(ε^2)^(p-1))*((n+1)*ε)^2 :=
          mul_le_mul (hle.trans hmax) hs (sq_nonneg _) hK
        _ = _ := by
          rw [Real.rpow_sub_one hε2.ne']
          field_simp
    · rw [Set.indicator_of_notMem hx]
      have hx' : (n+1)*ε ≤ ‖x‖ := by simpa using (not_le.mp (by simpa using hx)).le
      have hnonneg : 0 ≤ halfLaplacian (radialPower (ε^2) p) x := by
        rw [radialPower_halfLaplacian hε2]
        change 0 ≤ p*(ε^2+‖x‖^2)^(p-2)*(n*ε^2+(n+2*p-2)*‖x‖^2)
        rw [hbracket]
        apply mul_nonneg_of_nonpos_of_nonpos
        · exact mul_nonpos_of_nonpos_of_nonneg hp.le (by positivity)
        · have hs : ((n+1)*ε)^2 ≤ ‖x‖^2 := sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr hx'
          nlinarith
      simp_all
  let m := ∫ x, radialBump (1/4) p x ∂μ
  have hm : 0 < m := by
    apply (radialBump_contDiff (E := E) (by norm_num : (0:ℝ)<1/4) p).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (radialBump_compact (by norm_num) hp) (radialBump_nonneg _ _)
    apply ne_of_gt (smoothPositivePart_pos (t := radialPower (1/4) p (0:E)-1) _)
    simp only [radialPower, norm_zero, sq, mul_zero, add_zero]
    exact sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hp)
  have lower {a} (ha : 0 < a) (ha' : a ≤ 1/4) : m ≤ ∫ x, radialBump a p x ∂μ := by
    apply integral_mono
    · exact (radialBump_contDiff (by norm_num) _).continuous.integrable_of_hasCompactSupport
        (radialBump_compact (by norm_num) hp)
    · exact (radialBump_contDiff ha _).continuous.integrable_of_hasCompactSupport (radialBump_compact ha hp)
    · intro x
      apply monotone_of_hasDerivAt_nonneg smoothPositivePart_hasDerivAt
        (fun t => (smoothPositivePart'_bounds t).1)
      exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hp.le) 1
  let K := μ.real (Metric.ball (0:E) 1) * (-p) * n * (n+1)^(Module.finrank ℝ E+2)
  have negative {ε} (hε : 0 < ε) :
      (∫ x, max (-halfLaplacian (radialBump (ε^2) p) x) 0 * ‖x‖^2 ∂μ) ≤ K*Real.sqrt ε := by
    let R := (n+1)*ε
    let K' := (-p)*n*(n+1)^2*(ε^2)^p
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hI : Integrable ((Metric.closedBall (0:E) R).indicator (fun _ => K')) μ :=
      (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
    have hbound := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => mul_nonneg (le_max_right _ _) (sq_nonneg ‖x‖))) hI
      (Filter.Eventually.of_forall (bound hε))
    refine hbound.trans_eq ?_
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    rw [Measure.real_def, μ.addHaar_closedBall (0:E) hR, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hR _)]
    have hweight : ε^(Module.finrank ℝ E) * (ε^2)^p = Real.sqrt ε := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast_mul hε.le 2, ← Real.rpow_add hε]
      congr 1
      dsimp [p,n]
      ring
    dsimp [R,K',K]
    rw [mul_pow, pow_add, ← hweight]
    simp only [Measure.real_def]
    ring
  have hlim : ContinuousAt (fun ε : ℝ => K*Real.sqrt ε) 0 := by fun_prop
  have he := hlim.eventually_lt_const (by simpa using mul_pos hη hm)
  have hpow : ∀ᶠ ε : ℝ in 𝓝 0, ε^2 < 1/4 :=
    (continuousAt_id.pow 2).eventually_lt_const (by norm_num)
  obtain ⟨ε,hε,hεlimit,hsmall⟩ :=
    (Filter.Eventually.and (self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)))
      ((hpow.and he).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨radialBump (ε^2) p, radialBump_contDiff (sq_pos_of_pos hε) p,
    radialBump_compact (sq_pos_of_pos hε) hp, radialBump_nonneg _ _, hm.trans_le (lower (sq_pos_of_pos hε) hεlimit.le), ?_⟩
  exact (negative hε).trans_lt (hsmall.trans_le (mul_le_mul_of_nonneg_left
    (lower (sq_pos_of_pos hε) hεlimit.le) hη.le))



end

end OAI.EuclideanRamsey
