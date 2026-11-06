/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.TensorNecessity

@[expose] public section

noncomputable section

open Real MeasureTheory Polynomial ContDiff

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔤" => 1/2
notation "𝔣" => (u^p - 1)
local notation "𝔢" => (by norm_num)
notation "𝔡" => (0:E)
local notation "𝔠" => (by positivity)
local notation "𝔟" => (‖y‖^2)
local notation "𝔞" => (n+1)
local notation "𝔵" => ‖x‖^2
notation "𝔭" => (p-1-1)

def smoothPositivePart (t : ℝ):= t * expNegInvGlue t
def smoothPositivePart' (t : ℝ):= (1 + t⁻¹) * expNegInvGlue t
def smoothPositivePart'' (t : ℝ):= t⁻¹ ^ 3 * expNegInvGlue t

lemma glue_mul_nonneg t (h : 0 < t → 0 ≤ c) : 0 ≤ c * expNegInvGlue t := by
  rcases le_or_gt t 0 with h' | h'
  · simp [expNegInvGlue.zero_of_nonpos h']
  exact mul_nonneg (h h') (expNegInvGlue.nonneg _)

lemma smoothPositivePart_hasDerivAt t :
    HasDerivAt smoothPositivePart (smoothPositivePart' t) t := by
  have := (hasDerivAt_id t).mul (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) t)
  convert this
  · ext
    simp [smoothPositivePart]
  rcases eq_or_ne t 0 with rfl | ht <;> simp [smoothPositivePart', *]
  field_simp

lemma smoothPositivePart'_hasDerivAt t :
    HasDerivAt smoothPositivePart' (smoothPositivePart'' t) t := by
  convert expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 + X : ℝ[X]) t using 1
  · ext
    simp [smoothPositivePart']
  simp [smoothPositivePart'']
  left
  ring

lemma smoothPositivePart'_bounds t :
    0 ≤ smoothPositivePart' t ∧ smoothPositivePart' t ≤ 1 := by
  refine ⟨glue_mul_nonneg t fun _ => by positivity, ?_⟩
  rcases le_or_gt t 0 with ht | ht
  · simp [smoothPositivePart', expNegInvGlue.zero_of_nonpos ht]
  rw [smoothPositivePart', expNegInvGlue, ite_eq_right ht.not_ge, exp_neg, ← div_eq_mul_inv,
    div_le_one (exp_pos _)]
  linarith [add_one_le_exp t⁻¹]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] (e : OrthonormalBasis ι ℝ E)

def halfLaplacian (f : E → ℝ) (x : E):=
  (𝔤 : ℝ) * ∑ i, iteratedFDeriv ℝ 2 f x ![e i, e i]

lemma radial_halfLaplacian {F F' F'' : ℝ → ℝ} (h1 : ∀ s ≥ 0, HasDerivAt F (F' s) s)
    (h2 : ∀ s ≥ 0, HasDerivAt F' (F'' s) s) x :
    halfLaplacian e (fun y => F 𝔟) x = 2 * F'' (𝔵) * 𝔵 + Module.finrank ℝ E * F' (𝔵) := by
  have hd (y : E) := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hG : fderiv ℝ (fun y => F 𝔟) = fun y : E => F' 𝔟 • (2 • innerSL ℝ y) :=
    funext fun y => ((h1 _ (sq_nonneg _)).comp_hasFDerivAt y (hd y)).fderiv
  have : HasFDerivAt (fun y => F' 𝔟 • (2 • innerSL ℝ y)) _ x := ((h2 _ (sq_nonneg _)).comp_hasFDerivAt x (hd x)).smul ((innerSL ℝ).hasFDerivAt.const_smul 2)
  simp only [halfLaplacian, iteratedFDeriv_succ_apply_right]
  change (𝔤:ℝ) * ∑ i, fderiv ℝ (fderiv ℝ _) x _ _ = _
  rw [hG, this.fderiv]
  have := e.sum_inner_mul_inner x x
  simp [Fin.init, real_inner_comm x, ← sq, innerSL_apply_apply] at this ⊢
  ring_nf
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, this]
  erw [Finset.sum_congr rfl fun i _ => innerSL_apply_apply ..]
  simp [Module.finrank_eq_card_basis e.toBasis]
  ring
def radialBump (a p : ℝ) (x : E):= smoothPositivePart ((𝔵 + a) ^ p - 1)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem exists_radial_smoothing (hn : 1 ≤ Module.finrank ℝ E) (hη : 0 < η) :
    ∃ b, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∂μ ∧
      (∫ x, max (-halfLaplacian e b x) 0 * 𝔵 ∂μ) < η * ∫ x, b x ∂μ := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set p : ℝ := 1/4 - n/2
  have hp2 : 2 * p = 𝔤 - n := by ring
  have hp : p < 0 := by linarith [show (1:ℝ) ≤ n from Nat.one_le_cast.2 hn]
  have hc a (ha : 0 < a) : ContDiff ℝ ∞ (radialBump (E := E) a p) :=
    (contDiff_id.mul expNegInvGlue.contDiff).comp (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun x => (add_pos_of_nonneg_of_pos (sq_nonneg _) ha).ne') |>.sub contDiff_const)
  have hk a (ha : 0 < a) : HasCompactSupport (radialBump a p) :=
    .intro (isCompact_closedBall (0 : E) 1) fun x hx => by
      have : 1 < ‖x‖ := by simp_all
      simp [radialBump, smoothPositivePart,
        rpow_le_one_of_one_le_of_nonpos (by nlinarith : 1 ≤ 𝔵 + a) hp.le]
  have hI (a : ℝ) (ha : 0 < a) := (hc a ha).continuous.integrable_of_hasCompactSupport (μ := μ) (hk a ha)
  have h0 a (x : E) : 0 ≤ radialBump a p x := glue_mul_nonneg _ le_of_lt
  have hm : 0 < ∫ x, radialBump (1/4) p x ∂μ := by
    refine (hc _ 𝔢).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hk _ 𝔢) (h0 _) (x := 0) ?_
    have h : 0 < (‖𝔡‖^2 + 1/4) ^ p - 1 := by
      simpa using one_lt_rpow_of_pos_of_lt_one_of_neg 𝔢 𝔢 hp
    exact (mul_pos h (expNegInvGlue.pos_of_pos h)).ne'
  obtain ⟨t, ht, ht'⟩ := exists_pos_mul_lt (mul_pos hη hm) (μ.real (Metric.closedBall 𝔡 1) * (-p) * n * 𝔞^Module.finrank ℝ E*𝔞^2 + 1)
  set δ := min t (𝔤)
  have hδ : 0 < δ := lt_min ht 𝔢
  have ha : 0 < δ^4 := by positivity
  have hlow : ∫ x, radialBump (1/4) p x ∂μ ≤ ∫ x, radialBump (δ^4) p x ∂μ :=
    integral_mono (hI _ 𝔢) (hI _ ha) fun x => monotone_of_hasDerivAt_nonneg smoothPositivePart_hasDerivAt
      (fun t => (smoothPositivePart'_bounds t).1) (sub_le_sub_right (rpow_le_rpow_of_nonpos 𝔠
      (by nlinarith [pow_le_pow_left₀ hδ.le (min_le_right t (𝔤)) 4]) hp.le) 1)
  set D := δ^4 with hD
  refine ⟨_, hc _ ha, hk _ ha, h0 _, hm.trans_le hlow, ?_⟩
  have hb x : max (-halfLaplacian e (radialBump D p) x) 0 * 𝔵 ≤
      (Metric.closedBall 𝔡 (𝔞*δ^2)).indicator (fun _ => -p*n*𝔞^2*D^p) x := by
    have hs := sq_nonneg ‖x‖
    have hφ s (hs : s ≥ 0) := ((hasDerivAt_rpow_const (p := p) (Or.inl 𝔠)).comp_add_const s D).sub_const 1
    rw [show halfLaplacian e (radialBump D p) x = _ from radial_halfLaplacian e (fun s hs => (smoothPositivePart_hasDerivAt _).comp s (hφ s hs))
      (fun s hs => ((smoothPositivePart'_hasDerivAt _).comp s (hφ s hs)).mul
        (((hasDerivAt_rpow_const (Or.inl 𝔠)).comp_add_const s D).const_mul p)) x, Function.comp_apply]
    have hu : 0 < 𝔵 + D := by positivity
    set u := 𝔵 + D with hu'
    have hq : u^(p-1) = u^𝔭 * u := by rw [← rpow_add_one hu.ne']
                                      ring_nf
    have hA : D^p = D^𝔭 * D * D := by rw [← rpow_add_one ha.ne', ← rpow_add_one ha.ne']
                                      ring_nf
    have hqA : u^𝔭 ≤ D^𝔭 := rpow_le_rpow_of_nonpos ha (by linarith) (by linarith)
    have g1 := smoothPositivePart'_bounds 𝔣
    have g2 : 0 ≤ smoothPositivePart'' 𝔣 := glue_mul_nonneg _ fun h => pow_nonneg (inv_nonneg.2 h.le) 3
    have q0 : 0 ≤ u^𝔭 := by positivity
    rw [hq, hA]
    set q := u^𝔭
    set A := D^𝔭
    set g' := smoothPositivePart' 𝔣
    have e1 := mul_nonneg (mul_nonneg g2 (mul_self_nonneg (p*(q*u)))) hs
    have hpq : p*q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp.le q0
    have n0 : (0:ℝ) ≤ n := by positivity
    have hpn : 0 ≤ -p*n := by nlinarith
    have hm : 2*p*(g'*q*𝔵*p) = (𝔤-n)*(g'*q*𝔵*p) := by grind
    by_cases hx : x ∈ Metric.closedBall 𝔡 (𝔞*δ^2)
    · rw [Set.indicator_of_mem hx]
      have := pow_le_pow_left₀ (norm_nonneg _) (by simpa using hx) 2
      have hK : 0 ≤ -p*n*D*A := mul_nonneg (mul_nonneg (by nlinarith) ha.le) (q0.trans hqA)
      refine (mul_le_mul (max_le ?_ hK) this hs hK).trans_eq (by ring)
      linarith [ mul_nonneg (mul_nonneg g1.1 (neg_nonneg.2 hpq)) hs, mul_nonneg (mul_nonneg (sub_nonneg.2 g1.2) (neg_nonneg.2 hpq)) (mul_nonneg n0 ha.le), mul_nonneg (mul_nonneg hpn ha.le) (sub_nonneg.2 hqA)]
    · rw [Set.indicator_of_notMem hx]
      have := pow_lt_pow_left₀ (by simpa using hx) 𝔠 two_ne_zero
      have h3 : n*D ≤ 3/2*𝔵 := by linarith [mul_le_mul_of_nonneg_right (by linarith [sq_nonneg n] : n ≤ 3/2*𝔞^2) ha.le]
      rw [max_eq_right (by linarith [ mul_nonneg (mul_nonneg g1.1 (neg_nonneg.2 hpq)) (sub_nonneg.2 h3)])]
      simp
  have he : (δ^2)^(Module.finrank ℝ E) * D^p = δ := by
    rw [hD, ← rpow_natCast, ← rpow_natCast, ← rpow_natCast, ← rpow_mul hδ.le, ← rpow_mul hδ.le, ← rpow_add hδ]
    convert rpow_one δ
    simp
    ring
  have K0 : 0 ≤ μ.real (Metric.closedBall 𝔡 1) * (-p) * n * 𝔞^Module.finrank ℝ E*𝔞^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg measureReal_nonneg (neg_nonneg.2 hp.le)) (Nat.cast_nonneg _)) 𝔠) 𝔠
  refine (integral_mono_of_nonneg (.of_forall fun x => mul_nonneg (le_max_right _ _) (sq_nonneg _))
    ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall)
    (.of_forall hb)).trans_lt ?_
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, μ.addHaar_real_closedBall' _ 𝔠, mul_pow]
  linarith [mul_le_mul_of_nonneg_left (he.trans_le (min_le_left t (𝔤))) K0, mul_le_mul_of_nonneg_left hlow hη.le]
