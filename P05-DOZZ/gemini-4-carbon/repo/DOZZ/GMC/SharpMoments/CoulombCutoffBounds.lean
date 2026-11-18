/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CoulombCutoffDefs
public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.Moments.InfinityChart

/-! # Pointwise bounds for the single-chart regularized Coulomb weight

Away from the origin both partition functions are at most one and add up to one, and the
inverted-chart weight at `x⁻¹` has a closed form in `x` with softened distances
`‖x - z k‖ + e^{-r} ‖x‖`. Near a root, in the bulk and in the exterior every base lies in a compact
subinterval of `(0, ∞)`, uniformly in the parameters, except the softened root factor; this gives
upper bounds in the three regions and a lower bound on a fixed exterior disk, with constants
depending only on the size of the parameters. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {N : ℕ}


private lemma weight_le_add (partition : GMCChartPartition) {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0) {A B : ℝ≥0∞}
    (hf : partition.finiteWeight x ≠ 0 → coulombCutoffFiniteWeight γ α z αinf r x ≤ A)
    (hi : partition.infinityWeight x⁻¹ ≠ 0 → coulombCutoffInfinityWeight γ α z αinf r x⁻¹ ≤ B) :
    coulombCutoffWeight partition γ α z αinf r x ≤ A + B := by
  have h : (partition.finiteWeight x : ℝ≥0∞) + (partition.infinityWeight x⁻¹ : ℝ≥0∞) = 1 := by
    exact_mod_cast partition.sum_one x hx
  have h1 : (partition.finiteWeight x : ℝ≥0∞) ≤ 1 := le_self_add.trans_eq h
  have h2 : (partition.infinityWeight x⁻¹ : ℝ≥0∞) ≤ 1 := le_add_self.trans_eq h
  unfold coulombCutoffWeight
  refine add_le_add ?_ ?_
  · by_cases h0 : partition.finiteWeight x = 0 <;> [simp [h0]; exact (mul_le_mul' h1 (hf h0)).trans_eq (one_mul _)]
  · by_cases h0 : partition.infinityWeight x⁻¹ = 0 <;> [simp [h0]; exact (mul_le_mul' h2 (hi h0)).trans_eq (one_mul _)]

private lemma infinityWeight_inv (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0) :
    coulombCutoffInfinityWeight γ α z αinf r x⁻¹ =
      (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / (‖x - z k‖ + Real.exp (-r) * ‖x‖))) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x / (1 + Real.exp (-r) * ‖x‖))) (γ * αinf) := by
  have hn := (norm_pos_iff.2 hx).ne'
  unfold coulombCutoffInfinityWeight
  rw [normPlus_inv_identity hx, norm_inv, show ‖x‖⁻¹ + Real.exp (-r) = (1 + Real.exp (-r) * ‖x‖) / ‖x‖ by field_simp,
    div_div_div_cancel_right₀ hn]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show ‖1 - z k * x⁻¹‖ = ‖x - z k‖ / ‖x‖ by rw [← norm_div]; congr 1; field_simp,
    div_add' _ _ _ hn, div_div_div_cancel_right₀ hn]

private lemma prod_rpow_le (s : Finset (Fin N)) (a e : Fin N → ℝ) {L E : ℝ}
    (hL : 1 ≤ L) (hE : 0 ≤ E) (h : ∀ j ∈ s, L⁻¹ ≤ a j ∧ a j ≤ L) (he : ∀ j ∈ s, |e j| ≤ E) :
    ∏ j ∈ s, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) ≤ ENNReal.ofReal (L ^ ((N : ℝ) * E)) := by
  refine (coulombWeight_prod_le s a e hL h).trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hL ((Finset.sum_le_sum he).trans ?_)))
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin N)) hE

private lemma rpow_le_one_fac {L y e E : ℝ} (hL : 1 ≤ L) (hy : L⁻¹ ≤ y ∧ y ≤ L) (he : |e| ≤ E) :
    ENNReal.rpow (ENNReal.ofReal y) e ≤ ENNReal.ofReal (L ^ E) :=
  (ennreal_rpow_ofReal_le_of_mem_Icc hL hy.1 hy.2 e).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL he))



private lemma infty_base_mem {t m δ : ℝ} (hm1 : 1 ≤ m) (htm : t ≤ m) (ht0 : 0 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (2 : ℝ)⁻¹ ≤ m / (1 + δ * t) ∧ m / (1 + δ * t) ≤ m := by
  have hp : 0 < 1 + δ * t := by positivity
  exact ⟨(le_div_iff₀ hp).2 (by nlinarith),
    (div_le_iff₀ hp).2 (by nlinarith [mul_nonneg (by linarith : 0 ≤ m) (mul_nonneg hδ.le ht0)])⟩

private lemma ext_quot {t v Zs : ℝ} (ht : 2 * Zs ≤ t) (ht0 : 0 < t)
    (hv1 : t - Zs ≤ v) (hv2 : v ≤ 2 * t + Zs) :
    (5 / 2 : ℝ)⁻¹ ≤ t / v ∧ t / v ≤ 5 / 2 := by
  have hv : 0 < v := by linarith
  exact ⟨(le_div_iff₀ hv).2 (by linarith), (div_le_iff₀ hv).2 (by linarith)⟩

/-- Near a finite root the single-chart weight is the softened root singularity times a bounded
factor, uniformly over bounded parameters. -/
theorem coulombCutoffWeight_le_root (partition : GMCChartPartition) (N : ℕ)
    {Zs E ρs Ri : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri)
    (hsupp : ∀ u, partition.infinityWeight u ≠ 0 → ‖u‖ ≤ Ri) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (k : Fin N)
      (x : ℂ), 0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      (∀ j, j ≠ k → 2 * ρs ≤ ‖z j - z k‖) → x ∈ Metric.ball (z k) ρs → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤
        ENNReal.ofReal C * ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) := by
  have rootForm_le (a e : Fin N → ℝ) (c D g eg : ℝ) (k : Fin N) {L E : ℝ} (hL : 1 ≤ L) (hE : 0 ≤ E) (hD : 0 < D) (hak : a k = c / D) (hc : L⁻¹ ≤ c ∧ c ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L) (ha : ∀ j, j ≠ k → L⁻¹ ≤ a j ∧ a j ≤ L) (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) : (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg ≤
        ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) * ENNReal.rpow (ENNReal.ofReal D) (-e k) := by
    have hLp := lt_of_lt_of_le one_pos hL
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hak,
      coulombWeight_rpow_ofReal_div (lt_of_lt_of_le (inv_pos.2 hLp) hc.1) hD]
    have hp := prod_rpow_le (Finset.univ.erase k) a e hL hE
      (fun j hj => ha j (Finset.ne_of_mem_erase hj)) fun j _ => he j
    have h1 := rpow_le_one_fac hL hc (he k)
    have h2 := rpow_le_one_fac hL hg heg
    refine (by ring : _ = (ENNReal.rpow (ENNReal.ofReal c) (e k) *
        (∏ j ∈ Finset.univ.erase k, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) *
        ENNReal.rpow (ENNReal.ofReal g) eg) * ENNReal.rpow (ENNReal.ofReal D) (-e k)).trans_le ?_
    refine (mul_le_mul' (mul_le_mul' (mul_le_mul' h1 hp) h2) le_rfl).trans_eq ?_
    rw [mul_comm (ENNReal.ofReal (L ^ E)), coulombWeight_ofReal_rpow_mul hLp, coulombWeight_ofReal_rpow_mul hLp]
  let L := (3 * Zs + 3) * Ri / ρs
  have hLρ : Zs + 1 ≤ L * ρs := by dsimp [L]; rw [div_mul_cancel₀ _ hρs.ne']; nlinarith
  have hL3 : 3 * Zs + 3 ≤ L := (le_div_iff₀ hρs).2 (by nlinarith)
  have hLRi : (Zs + 1) * Ri ≤ L := (le_div_iff₀ hρs).2
    (by linarith [mul_le_mul_of_nonneg_left hρs1 (by positivity : 0 ≤ (Zs + 1) * Ri),
      mul_nonneg hZs (by positivity : 0 ≤ Ri)])
  have hL1 : 1 ≤ L := by linarith
  have hL2 : 2 ≤ L := by linarith
  refine ⟨L ^ ((N : ℝ) * E + E + E) + L ^ ((N : ℝ) * E + E + E), by positivity,
    fun γ α z αinf r k x hr hz hα hαinf hsep hx hx0 => ?_⟩
  have hzj (j : Fin N) : ‖z j‖ ≤ Zs :=
    (Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)).trans hz
  have hd : ‖x - z k‖ < ρs := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have ht : ‖x‖ ≤ Zs + 1 := by linarith [norm_sub_norm_le x (z k), hzj k]
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have hmM : normPlus x ≤ Zs + 1 := max_le (by linarith) ht
  have hδ : 0 < Real.exp (-r) := Real.exp_pos _
  have hδ1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hr)
  have hDk : 0 < ‖x - z k‖ + Real.exp (-r) := by positivity
  have hrdist (j : Fin N) (hj : j ≠ k) : ρs ≤ ‖x - z j‖ ∧ ‖x - z j‖ ≤ 2 * Zs + 1 := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (z j) x (z k)
    rw [norm_sub_rev (z j) x] at h1
    exact ⟨by linarith [hsep j hj], by linarith [norm_sub_le x (z j), hzj j, hzj k]⟩
  rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul,
    ← coulombWeight_rpow_ofReal hDk, neg_mul γ (α k)]
  refine weight_le_add partition γ α z αinf r hx0 (fun _ => ?_) (fun h => ?_)
  · unfold coulombCutoffFiniteWeight
    have hc : L⁻¹ ≤ normPlus x ∧ normPlus x ≤ L :=
      ⟨(inv_le_one_of_one_le₀ hL1).trans hm1, hmM.trans (by linarith)⟩
    exact rootForm_le (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r))) (fun j => γ * α j)
      (normPlus x) _ (normPlus x) _ k hL1 hE hDk rfl hc hc
      (fun j hj => coulombWeight_quot_bounds (b := ‖x - z j‖ + Real.exp (-r)) (B := 2 * Zs + 2)
        hρs hρs1 hm1 hmM (by linarith [(hrdist j hj).1]) (by linarith [(hrdist j hj).2]) hLρ (by linarith)) hα hαinf
  · have hxRi : Ri⁻¹ ≤ ‖x‖ := (inv_le_comm₀ (norm_pos_iff.2 hx0) (by positivity)).1
      (by simpa using hsupp _ h)
    have ht0 : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have htm : ‖x‖ ≤ normPlus x := le_max_right _ _
    have := mul_le_of_le_one_left ht0.le hδ1
    have hden : 0 < ‖x - z k‖ + Real.exp (-r) * ‖x‖ := by positivity
    have hRit : 1 ≤ Ri * ‖x‖ := (mul_inv_cancel₀ (by positivity : Ri ≠ 0)).symm.le.trans
      (mul_le_mul_of_nonneg_left hxRi (by positivity))
    have hc : L⁻¹ ≤ normPlus x * (‖x - z k‖ + Real.exp (-r)) / (‖x - z k‖ + Real.exp (-r) * ‖x‖) ∧
        normPlus x * (‖x - z k‖ + Real.exp (-r)) / (‖x - z k‖ + Real.exp (-r) * ‖x‖) ≤ L := by
      refine ⟨(inv_le_one_of_one_le₀ hL1).trans ((le_div_iff₀ hden).2 (by nlinarith [norm_nonneg (x - z k)])),
        ((div_le_iff₀ hden).2 ?_).trans hLRi⟩
      have : ‖x - z k‖ + Real.exp (-r) ≤ Ri * (‖x - z k‖ + Real.exp (-r) * ‖x‖) := by
        nlinarith [norm_nonneg (x - z k)]
      nlinarith
    obtain ⟨hg1, hg2⟩ := infty_base_mem hm1 htm ht0.le hδ hδ1
    rw [infinityWeight_inv γ α z αinf r hx0]
    exact rootForm_le (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖)) (fun j => γ * α j)
      _ _ _ _ k hL1 hE hDk (by field_simp [hDk.ne']) hc
      ⟨(inv_anti₀ two_pos hL2).trans hg1, hg2.trans (by linarith)⟩
      (fun j hj => coulombWeight_quot_bounds (b := ‖x - z j‖ + Real.exp (-r) * ‖x‖) (B := 3 * Zs + 3)
        hρs hρs1 hm1 hmM (by nlinarith [(hrdist j hj).1]) (by linarith [(hrdist j hj).2]) hLρ hL3) hα hαinf

/-- Away from the roots, on a bounded set, the single-chart weight is bounded. -/
theorem coulombCutoffWeight_le_bulk (partition : GMCChartPartition) (N : ℕ)
    {Zs E ρs R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hR0 : 0 ≤ R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      ‖x‖ ≤ R0 → (∀ k, ρs ≤ ‖x - z k‖) → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤ ENNReal.ofReal C := by
  have form_le (a e : Fin N → ℝ) (g eg : ℝ) {L E : ℝ} (hL : 1 ≤ L) (hE : 0 ≤ E) (ha : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L) (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) := 
    (mul_le_mul' (prod_rpow_le Finset.univ a e hL hE (fun j _ => ha j) fun j _ => he j)
      (rpow_le_one_fac hL hg heg)).trans_eq (coulombWeight_ofReal_rpow_mul (lt_of_lt_of_le one_pos hL) _ _)
  let L := (2 * R0 + Zs + 2) / ρs
  have hLρ : 1 + R0 ≤ L * ρs := by dsimp [L]; rw [div_mul_cancel₀ _ hρs.ne']; linarith
  have hLB : 2 * R0 + Zs + 2 ≤ L := (le_div_iff₀ hρs).2 (by nlinarith)
  have hL1 : 1 ≤ L := by linarith
  have hL2 : 2 ≤ L := by linarith
  refine ⟨L ^ ((N : ℝ) * E + E) + L ^ ((N : ℝ) * E + E), by positivity,
    fun γ α z αinf r x hr hz hα hαinf hxR hxz hx0 => ?_⟩
  have hzj (j : Fin N) : ‖z j‖ ≤ Zs :=
    (Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)).trans hz
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have hmM : normPlus x ≤ 1 + R0 := max_le (by linarith) (by linarith)
  have hδ : 0 < Real.exp (-r) := Real.exp_pos _
  have hδ1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hr)
  have hmL : normPlus x ≤ L := hmM.trans (hLρ.trans (mul_le_of_le_one_right (by positivity) hρs1))
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine weight_le_add partition γ α z αinf r hx0 (fun _ => ?_) (fun _ => ?_)
  · unfold coulombCutoffFiniteWeight
    exact form_le (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r))) (fun j => γ * α j)
      (normPlus x) (γ * αinf) hL1 hE
      (fun j => coulombWeight_quot_bounds (b := ‖x - z j‖ + Real.exp (-r)) (B := 2 * R0 + Zs + 2)
        hρs hρs1 hm1 hmM (by linarith [hxz j])
        (by linarith [norm_sub_le x (z j), hzj j]) hLρ hLB)
      ⟨(inv_le_one_of_one_le₀ hL1).trans hm1, hmL⟩ hα hαinf
  · have ht0 := norm_pos_iff.2 hx0
    have := mul_le_of_le_one_left ht0.le hδ1
    obtain ⟨hg1, hg2⟩ := infty_base_mem hm1 (le_max_right _ _) ht0.le hδ hδ1
    rw [infinityWeight_inv γ α z αinf r hx0]
    exact form_le (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖)) (fun j => γ * α j)
      (normPlus x / (1 + Real.exp (-r) * ‖x‖)) (γ * αinf) hL1 hE
      (fun j => coulombWeight_quot_bounds (b := ‖x - z j‖ + Real.exp (-r) * ‖x‖) (B := 2 * R0 + Zs + 2)
        hρs hρs1 hm1 hmM (by nlinarith [hxz j])
        (by linarith [norm_sub_le x (z j), hzj j]) hLρ hLB)
      ⟨(inv_anti₀ two_pos hL2).trans hg1, hg2.trans hmL⟩ hα hαinf

/-- Far out the single-chart weight is at most a constant times the power at infinity. -/
theorem coulombCutoffWeight_le_exterior (partition : GMCChartPartition) (N : ℕ)
    {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hR0 : 2 * Zs + 2 ≤ R0)
    (hsuppf : ∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E → R0 ≤ ‖x‖ →
      coulombCutoffWeight partition γ α z αinf r x ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0) := by
  refine ⟨(5 / 2 : ℝ) ^ ((N : ℝ) * E) * 2 ^ E, by positivity,
    fun γ α z αinf r x hr hz hα hαinf hxR => ?_⟩
  have hzj (j : Fin N) : ‖z j‖ ≤ Zs :=
    (Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)).trans hz
  have ht1 : 1 ≤ ‖x‖ := by linarith
  have ht0 : 0 < ‖x‖ := by linarith
  have hδ : 0 < Real.exp (-r) := Real.exp_pos _
  have hδ1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hr)
  have := mul_le_of_le_one_left ht0.le hδ1
  rw [ENNReal.ofReal_mul (by positivity), mul_assoc, ← zero_add (ENNReal.ofReal _ * _)]
  refine weight_le_add partition γ α z αinf r (norm_pos_iff.1 ht0)
    (fun h => absurd (hsuppf x h) (not_lt.2 hxR)) fun _ => ?_
  rw [infinityWeight_inv γ α z αinf r (norm_pos_iff.1 ht0), show normPlus x = ‖x‖ from max_eq_right ht1]
  refine mul_le_mul' (prod_rpow_le Finset.univ _ _ (by norm_num) hE
    (fun j _ => ext_quot (Zs := Zs) (by linarith) ht0
      (by nlinarith [norm_sub_norm_le x (z j), hzj j])
      (by linarith [norm_sub_le x (z j), hzj j])) fun j _ => hα j) ?_
  obtain ⟨hy1, hy2⟩ := infty_base_mem ht1 le_rfl ht0.le hδ hδ1
  have hy0 : 0 < ‖x‖ / (1 + Real.exp (-r) * ‖x‖) := by positivity
  rw [coulombWeight_rpow_ofReal hy0, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total 0 (γ * αinf) with he0 | he0
  · rw [max_eq_left he0]
    exact (Real.rpow_le_rpow hy0.le hy2 he0).trans
      ((one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right
        (Real.one_le_rpow one_le_two ((abs_nonneg _).trans hαinf)) (Real.rpow_nonneg ht0.le _)))
  · rw [max_eq_right he0, Real.rpow_zero, mul_one]
    exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hy1 he0).trans
      ((by rw [Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two] :
          ((2 : ℝ)⁻¹) ^ (γ * αinf) = 2 ^ (-(γ * αinf))).trans_le
        (Real.rpow_le_rpow_of_exponent_le one_le_two ((neg_le_abs _).trans hαinf)))

/-- On a fixed exterior disk the single-chart weight is bounded below. -/
theorem coulombCutoffWeight_ge_ball (partition : GMCChartPartition) (N : ℕ)
    {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hR0 : 2 * Zs + 2 ≤ R0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8) →
      ENNReal.ofReal c ≤ coulombCutoffWeight partition γ α z αinf r x := by
  refine ⟨(R0 + 2) ^ (-((N : ℝ) * E + E)), Real.rpow_pos_of_pos (by linarith) _,
    fun γ α z αinf r x hr hz hα hαinf hx => ?_⟩
  have hzj (j : Fin N) : ‖z j‖ ≤ Zs :=
    (Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)).trans hz
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hc_norm : ‖(((R0 + 1 : ℝ)) : ℂ)‖ = R0 + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have ht1 : R0 + 7 / 8 < ‖x‖ := by
    have h2 := norm_sub_norm_le (((R0 + 1 : ℝ)) : ℂ) x
    rw [norm_sub_rev, hc_norm] at h2; linarith
  have ht2 : ‖x‖ < R0 + 9 / 8 := by linarith [norm_sub_norm_le x (((R0 + 1 : ℝ)) : ℂ)]
  have ht0 : 0 < ‖x‖ := by linarith
  have hx0 : x ≠ 0 := norm_pos_iff.1 ht0
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith)
  have hδ : 0 < Real.exp (-r) := Real.exp_pos _
  have hδ1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hr)
  have hL : 1 ≤ R0 + 2 := by linarith
  have hform_ge (a : Fin N → ℝ) (g : ℝ)
      (ha : ∀ j, (R0 + 2)⁻¹ ≤ a j ∧ a j ≤ R0 + 2) (hg : (R0 + 2)⁻¹ ≤ g ∧ g ≤ R0 + 2) :
      ENNReal.ofReal ((R0 + 2) ^ (-((N : ℝ) * E + E))) ≤
        (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (γ * α j)) * ENNReal.rpow (ENNReal.ofReal g) (γ * αinf) := by
    rw [neg_add, ← coulombWeight_ofReal_rpow_mul (by linarith)]
    refine mul_le_mul' ((ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL
        (neg_le_neg ((Finset.sum_le_sum fun j _ => hα j).trans_eq (by simp))))).trans
        (coulombWeight_prod_ge Finset.univ a _ hL fun j _ => ha j))
      ((ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hαinf))).trans
        (ennreal_ofReal_le_rpow_ofReal_of_mem_Icc hL hg.1 hg.2 _))
  have hsum : (partition.finiteWeight x : ℝ≥0∞) + (partition.infinityWeight x⁻¹ : ℝ≥0∞) = 1 := by
    exact_mod_cast partition.sum_one x hx0
  unfold coulombCutoffWeight
  rw [← one_mul (ENNReal.ofReal _), ← hsum, add_mul]
  refine add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_)
  · unfold coulombCutoffFiniteWeight; rw [hnp]
    refine hform_ge (fun j => ‖x‖ / (‖x - z j‖ + Real.exp (-r))) ‖x‖
      (fun j => ?_) ⟨(inv_le_one_of_one_le₀ hL).trans (by linarith), by linarith⟩
    obtain ⟨q1, q2⟩ := coulombWeight_exterior_quot_bounds (w := Zs + 1) (u := ‖x‖)
      (v := ‖x - z j‖ + Real.exp (-r)) (by linarith)
      (by linarith) (by linarith [norm_sub_norm_le x (z j), hzj j]) (by linarith [norm_sub_le x (z j), hzj j])
    exact ⟨(inv_anti₀ two_pos (by linarith)).trans q1, q2.trans (by linarith)⟩
  · rw [infinityWeight_inv γ α z αinf r hx0, hnp]
    have := mul_le_of_le_one_left ht0.le hδ1
    obtain ⟨hg1, hg2⟩ := infty_base_mem (t := ‖x‖) (m := ‖x‖) (by linarith) le_rfl ht0.le hδ hδ1
    refine hform_ge (fun j => ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖))
      (‖x‖ / (1 + Real.exp (-r) * ‖x‖))
      (fun j => ?_) ⟨(inv_anti₀ two_pos (by linarith)).trans hg1, hg2.trans (by linarith)⟩
    obtain ⟨q1, q2⟩ := ext_quot (t := ‖x‖) (v := ‖x - z j‖ + Real.exp (-r) * ‖x‖) (Zs := Zs)
      (by linarith) ht0 (by nlinarith [norm_sub_norm_le x (z j), hzj j])
      (by linarith [norm_sub_le x (z j), hzj j])
    exact ⟨(inv_anti₀ (by norm_num : (0 : ℝ) < 5 / 2) (by linarith)).trans q1, q2.trans (by linarith)⟩

end DOZZ.Proofs
