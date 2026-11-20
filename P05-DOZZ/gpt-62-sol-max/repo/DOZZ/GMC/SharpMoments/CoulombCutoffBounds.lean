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

section
variable (partition : GMCChartPartition) {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
  (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0)

include hx in
private theorem partition_sum_one :
    (partition.finiteWeight x : ℝ≥0∞) + (partition.infinityWeight x⁻¹ : ℝ≥0∞) = 1 := by
  exact_mod_cast partition.sum_one x hx

include hx in
/-- A common bound on the two chart weights, needed only on their supports, bounds the mixture. -/
private theorem cutoffWeight_le {C : ℝ≥0∞}
    (hf : partition.finiteWeight x ≠ 0 → coulombCutoffFiniteWeight γ α z αinf r x ≤ C)
    (hi : partition.infinityWeight x⁻¹ ≠ 0 → coulombCutoffInfinityWeight γ α z αinf r x⁻¹ ≤ C) :
    coulombCutoffWeight partition γ α z αinf r x ≤ C := by
  have bound (w : ℝ≥0) (a : ℝ≥0∞) (h : w ≠ 0 → a ≤ C) :
      (w : ℝ≥0∞) * a ≤ w * C := by
    by_cases hw : w = 0
    · simp [hw]
    · gcongr
      exact h hw
  unfold coulombCutoffWeight
  refine (add_le_add (bound _ _ hf) (bound _ _ hi)).trans_eq ?_
  rw [← add_mul, partition_sum_one partition hx, one_mul]

include hx in
private theorem le_cutoffWeight {c : ℝ≥0∞}
    (hf : c ≤ coulombCutoffFiniteWeight γ α z αinf r x)
    (hi : c ≤ coulombCutoffInfinityWeight γ α z αinf r x⁻¹) :
    c ≤ coulombCutoffWeight partition γ α z αinf r x := by
  refine Eq.trans_le ?_ (add_le_add (mul_le_mul' le_rfl hf) (mul_le_mul' le_rfl hi))
  rw [← add_mul, partition_sum_one partition hx, one_mul]

end

/-- Common product form of the weights in the original coordinate of either chart. -/
private noncomputable def cutoffForm {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf δ : ℝ) (x : ℂ) (t g : ℝ) : ℝ≥0∞ :=
  (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / (‖x - z k‖ + δ * t))) (γ * α k)) *
    ENNReal.rpow (ENNReal.ofReal g) (γ * αinf)

private theorem cutoffFinite_eq {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) (x : ℂ) :
    coulombCutoffFiniteWeight γ α z αinf r x =
      cutoffForm γ α z αinf (Real.exp (-r)) x 1 (normPlus x) := by
  simp only [cutoffForm, coulombCutoffFiniteWeight, mul_one]

/-- The inverted-chart root base in the original variable. -/
theorem coulombCutoffBound_inv_root_base {x z : ℂ} {δ : ℝ} (hx : x ≠ 0) :
    normPlus x⁻¹ / (‖1 - z * x⁻¹‖ + δ) = normPlus x / (‖x - z‖ + δ * ‖x‖) := by
  have hn  := norm_pos_iff.mpr hx
  have h1 : ‖1 - z * x⁻¹‖ = ‖x - z‖ / ‖x‖ := by
    rw [← norm_div]
    congr 1
    field_simp
  rw [normPlus_inv_identity hx, h1, div_add' _ _ _ hn.ne', div_div_div_cancel_right₀ hn.ne']

/-- The inverted-chart base at infinity in the original variable. -/
theorem coulombCutoffBound_inv_infty_base {x : ℂ} {δ : ℝ} (hx : x ≠ 0) :
    normPlus x⁻¹ / (‖x⁻¹‖ + δ) = normPlus x / (1 + δ * ‖x‖) := by
  have hn  := norm_pos_iff.mpr hx
  have h1 : ‖x⁻¹‖ + δ = (1 + δ * ‖x‖) / ‖x‖ := by
    rw [norm_inv]
    field_simp
  rw [normPlus_inv_identity hx, h1, div_div_div_cancel_right₀ hn.ne']

private theorem cutoffInfinity_eq {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0) :
    coulombCutoffInfinityWeight γ α z αinf r x⁻¹ =
      cutoffForm γ α z αinf (Real.exp (-r)) x ‖x‖ (normPlus x / (1 + Real.exp (-r) * ‖x‖)) := by
  simp only [cutoffForm, coulombCutoffInfinityWeight, coulombCutoffBound_inv_root_base hx,
    coulombCutoffBound_inv_infty_base hx]

/-! ### Products of powers with bounded bases and exponents -/

section
variable {L y e E : ℝ} (hL : 1 ≤ L) (hy1 : L⁻¹ ≤ y) (hy2 : y ≤ L) (he : |e| ≤ E)
include hL hy1 hy2 he

/-- A single power with base in `[L⁻¹, L]` and exponent of size at most `E`. -/
theorem coulombCutoffBound_rpow_le : ENNReal.rpow (ENNReal.ofReal y) e ≤ ENNReal.ofReal (L ^ E) :=
  (ennreal_rpow_ofReal_le_of_mem_Icc hL hy1 hy2 e).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL he))

/-- A single power with base in `[L⁻¹, L]` and exponent of size at most `E`: lower bound. -/
theorem coulombCutoffBound_le_rpow : ENNReal.ofReal (L ^ (-E)) ≤ ENNReal.rpow (ENNReal.ofReal y) e :=
  (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg he))).trans
    (ennreal_ofReal_le_rpow_ofReal_of_mem_Icc hL hy1 hy2 e)

end

/-- A product over a subset of `Fin N` of powers with bases in `[L⁻¹, L]`. -/
theorem coulombCutoffBound_prod_le {N : ℕ} (s : Finset (Fin N)) (a e : Fin N → ℝ) {L E : ℝ}
    (hL : 1 ≤ L) (hE : 0 ≤ E) (h : ∀ j ∈ s, L⁻¹ ≤ a j ∧ a j ≤ L)
    (he : ∀ j ∈ s, |e j| ≤ E) :
    ∏ j ∈ s, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E)) := by
  refine (coulombWeight_prod_le s a e hL h).trans (ENNReal.ofReal_le_ofReal ?_)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  calc ∑ j ∈ s, |e j| ≤ ∑ j ∈ s, E := Finset.sum_le_sum he
    _ = s.card * E := by simp
    _ ≤ N * E := by
      refine mul_le_mul_of_nonneg_right ?_ hE
      exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin N)

section
variable {N : ℕ} (a e : Fin N → ℝ)

/-- A product over `Fin N` of powers with bases in `[L⁻¹, L]`: lower bound. -/
theorem coulombCutoffBound_prod_ge {L E : ℝ} (hL : 1 ≤ L)
    (h : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (he : ∀ j, |e j| ≤ E) :
    ENNReal.ofReal (L ^ (-((N : ℝ) * E))) ≤
      ∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (coulombWeight_prod_ge Finset.univ a e hL fun j _ => h j)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  rw [neg_le_neg_iff]
  calc ∑ j, |e j| ≤ ∑ _j : Fin N, E := Finset.sum_le_sum fun j _ => he j
    _ = N * E := by simp

/-- A product of bounded powers times the factor at infinity: upper bound. -/
theorem coulombCutoffBound_form_le (g eg : ℝ) {L E : ℝ} (hL : 1 ≤ L)
    (hE : 0 ≤ E) (ha : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L)
    (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) :
    (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E)) := by
  have hLpos  := lt_of_lt_of_le one_pos hL
  calc _ ≤ ENNReal.ofReal (L ^ ((N : ℝ) * E)) * ENNReal.ofReal (L ^ E) :=
        mul_le_mul' (coulombCutoffBound_prod_le Finset.univ a e hL hE (fun j _ => ha j)
          fun j _ => he j) (coulombCutoffBound_rpow_le hL hg.1 hg.2 heg)
    _ = _ := coulombWeight_ofReal_rpow_mul hLpos _ _

/-- A product of bounded powers times the factor at infinity: lower bound. -/
theorem coulombCutoffBound_form_ge (g eg : ℝ) {L E : ℝ} (hL : 1 ≤ L)
    (ha : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L)
    (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) :
    ENNReal.ofReal (L ^ (-((N : ℝ) * E + E))) ≤
      (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg := by
  have hLpos  := lt_of_lt_of_le one_pos hL
  calc ENNReal.ofReal (L ^ (-((N : ℝ) * E + E)))
      = ENNReal.ofReal (L ^ (-((N : ℝ) * E))) * ENNReal.ofReal (L ^ (-E)) := by
        rw [coulombWeight_ofReal_rpow_mul hLpos, neg_add]
    _ ≤ _ := mul_le_mul' (coulombCutoffBound_prod_ge a e hL ha he)
        (coulombCutoffBound_le_rpow hL hg.1 hg.2 heg)

/-- A product of bounded powers times the factor at infinity, with one root factor singled out:
the root factor contributes the softened root singularity. -/
theorem coulombCutoffBound_rootForm_le (c D g eg : ℝ) (k : Fin N)
    {L E : ℝ} (hL : 1 ≤ L) (hE : 0 ≤ E) (hD : 0 < D) (hak : a k = c / D)
    (hc : L⁻¹ ≤ c ∧ c ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L)
    (ha : ∀ j, j ≠ k → L⁻¹ ≤ a j ∧ a j ≤ L) (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) :
    (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) * ENNReal.rpow (ENNReal.ofReal D) (-e k) := by
  have hLpos  := lt_of_lt_of_le one_pos hL
  have hcpos  := lt_of_lt_of_le (inv_pos.mpr hLpos) hc.1
  have hP : ∏ j ∈ Finset.univ.erase k, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E)) :=
    coulombCutoffBound_prod_le _ a e hL hE
      (fun j hj => ha j (Finset.ne_of_mem_erase hj)) fun j _ => he j
  have hC := coulombCutoffBound_rpow_le hL hc.1 hc.2 (he k)
  have hG := coulombCutoffBound_rpow_le hL hg.1 hg.2 heg
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hak,
    coulombWeight_rpow_ofReal_div hcpos hD]
  generalize ENNReal.rpow (ENNReal.ofReal D) (-e k) = R
  calc _ = (ENNReal.rpow (ENNReal.ofReal c) (e k) *
          (∏ j ∈ Finset.univ.erase k, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) *
            ENNReal.rpow (ENNReal.ofReal g) eg) * R := by ring
    _ ≤ (ENNReal.ofReal (L ^ E) * ENNReal.ofReal (L ^ ((N : ℝ) * E)) *
          ENNReal.ofReal (L ^ E)) * R := by gcongr
    _ = (ENNReal.ofReal (L ^ ((N : ℝ) * E)) * ENNReal.ofReal (L ^ E) *
          ENNReal.ofReal (L ^ E)) * R := by rw [mul_comm (ENNReal.ofReal (L ^ E))]
    _ = _ := by rw [coulombWeight_ofReal_rpow_mul hLpos, coulombWeight_ofReal_rpow_mul hLpos]

end

/-! ### Elementary real inequalities -/

/-- The softening `e^{-r}` for `r ≥ 0` lies in `(0, 1]`. -/
theorem coulombCutoffBound_exp_neg_mem {r : ℝ} (hr : 0 ≤ r) :
    0 < Real.exp (-r) ∧ Real.exp (-r) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)⟩

/-- Each root has norm at most the sum of the norms. -/
theorem coulombCutoffBound_norm_le {N : ℕ} {z : Fin N → ℂ} {Zs : ℝ} (hz : ∑ j, ‖z j‖ ≤ Zs)
    (j : Fin N) : ‖z j‖ ≤ Zs :=
  (Finset.single_le_sum (f := fun i => ‖z i‖) (fun i _ => norm_nonneg (z i))
    (Finset.mem_univ j)).trans hz

/-- A point near the root `z k` is at distance between `ρs` and `2 Zs + 1` from every other
root. -/
theorem coulombCutoffBound_root_dist {Zs ρs : ℝ} {x zj zk : ℂ} (hzj : ‖zj‖ ≤ Zs)
    (hsep : 2 * ρs ≤ ‖zj - zk‖) (hd : ‖x - zk‖ < ρs) (hzk : ‖zk‖ ≤ Zs) (hρs1 : ρs ≤ 1) :
    ρs ≤ ‖x - zj‖ ∧ ‖x - zj‖ ≤ 2 * Zs + 1 := by
  have h1 := norm_sub_le_norm_sub_add_norm_sub zj x zk
  rw [norm_sub_rev zj x] at h1
  have h2 := norm_sub_le x zj
  have h3 := norm_sub_norm_le x zk
  constructor <;> linarith only [h1, h2, h3, hsep, hd, hzj, hzk, hρs1]

/-- A point `y ≥ 1` below `L ≥ 1` lies in `[L⁻¹, L]`. -/
theorem coulombCutoffBound_mem_of_one_le {L y : ℝ} (hL : 1 ≤ L) (hy1 : 1 ≤ y) (hyL : y ≤ L) :
    L⁻¹ ≤ y ∧ y ≤ L :=
  ⟨(inv_le_one_of_one_le₀ hL).trans hy1, hyL⟩

/-- Enlarging `L` enlarges the interval `[L⁻¹, L]`. -/
theorem coulombCutoffBound_mem_mono {L L' y : ℝ} (hL : 0 < L) (hLL' : L ≤ L')
    (h : L⁻¹ ≤ y ∧ y ≤ L) : L'⁻¹ ≤ y ∧ y ≤ L' :=
  ⟨(inv_anti₀ hL hLL').trans h.1, h.2.trans hLL'⟩

/-- The base at infinity of the inverted chart lies between `1/2` and `normPlus`. -/
theorem coulombCutoffBound_infty_base_mem {t m δ : ℝ} (hm1 : 1 ≤ m) (htm : t ≤ m) (ht0 : 0 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (2 : ℝ)⁻¹ ≤ m / (1 + δ * t) ∧ m / (1 + δ * t) ≤ m := by
  have hδt  := mul_le_of_le_one_left ht0 hδ1
  have hδt0  := mul_nonneg hδ.le ht0
  have hpos : 0 < 1 + δ * t := by linarith only [hδt0]
  constructor
  · rw [le_div_iff₀ hpos]
    linarith
  · rw [div_le_iff₀ hpos]
    linarith only [mul_nonneg (by linarith only [hm1] : 0 ≤ m) hδt0]

private theorem cutoff_last_mem {L δ : ℝ} {x : ℂ} (h2 : 2 ≤ L) (hm : normPlus x ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    L⁻¹ ≤ normPlus x / (1 + δ * ‖x‖) ∧ normPlus x / (1 + δ * ‖x‖) ≤ L := by
  obtain ⟨hl, hu⟩ := coulombCutoffBound_infty_base_mem (le_max_left 1 ‖x‖) (le_max_right 1 ‖x‖)
    (norm_nonneg x) hδ hδ1
  exact ⟨(inv_anti₀ two_pos h2).trans hl, hu.trans hm⟩

/-- The numerator constant of the root factor in the inverted chart. -/
theorem coulombCutoffBound_root_numer {m t d δ M Ri : ℝ} (hm1 : 1 ≤ m) (htm : t ≤ m)
    (hmM : m ≤ M) (hd : 0 ≤ d) (hδ : 0 < δ) (hRi : 1 ≤ Ri) (ht : Ri⁻¹ ≤ t) :
    1 ≤ m * (d + δ) / (d + δ * t) ∧ m * (d + δ) / (d + δ * t) ≤ M * Ri := by
  have hRipos  := lt_of_lt_of_le one_pos hRi
  have ht0  := lt_of_lt_of_le (inv_pos.mpr hRipos) ht
  have hpos : 0 < d + δ * t := by positivity
  have hRit : 1 ≤ Ri * t := by
    calc (1 : ℝ) = Ri * Ri⁻¹ := (mul_inv_cancel₀ hRipos.ne').symm
      _ ≤ Ri * t := mul_le_mul_of_nonneg_left ht hRipos.le
  have hM0 : 0 ≤ M := by linarith
  constructor
  · rw [le_div_iff₀ hpos]
    linarith only [mul_nonneg hd (sub_nonneg.2 hm1), mul_nonneg hδ.le (sub_nonneg.2 htm)]
  · rw [div_le_iff₀ hpos]
    have h1 : d + δ ≤ Ri * (d + δ * t) := by
      linarith only [mul_nonneg hd (sub_nonneg.2 hRi), mul_nonneg hδ.le (sub_nonneg.2 hRit)]
    calc m * (d + δ) ≤ M * (d + δ) := mul_le_mul_of_nonneg_right hmM (by positivity)
      _ ≤ M * (Ri * (d + δ * t)) := mul_le_mul_of_nonneg_left h1 hM0
      _ = M * Ri * (d + δ * t) := by ring

/-- Quotient bounds for the exterior: `t` against a point within `Zs` of `t` and `2 t + Zs`. -/
theorem coulombCutoffBound_ext_quot {t v Zs : ℝ} (ht : 2 * Zs ≤ t) (ht0 : 0 < t)
    (hv1 : t - Zs ≤ v) (hv2 : v ≤ 2 * t + Zs) :
    (5 / 2 : ℝ)⁻¹ ≤ t / v ∧ t / v ≤ 5 / 2 := by
  have hv : 0 < v := by linarith
  constructor
  · rw [le_div_iff₀ hv, show (5 / 2 : ℝ)⁻¹ = 2 / 5 by norm_num]
    linarith
  · rw [div_le_iff₀ hv]
    linarith

/-- The factor at infinity of the inverted chart in the exterior. -/
theorem coulombCutoffBound_exterior_last {t δ e E : ℝ} (ht : 1 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he : |e| ≤ E) :
    ENNReal.rpow (ENNReal.ofReal (t / (1 + δ * t))) e ≤
      ENNReal.ofReal (2 ^ E) * ENNReal.ofReal (t ^ max e 0) := by
  have ht0  := lt_of_lt_of_le one_pos ht
  obtain ⟨hy1, hy2⟩ := coulombCutoffBound_infty_base_mem (m := t) ht le_rfl ht0.le hδ hδ1
  have hy0  :=
    lt_of_lt_of_le (inv_pos.mpr two_pos) hy1
  have hE0  := (abs_nonneg e).trans he
  have h2E  := Real.one_le_rpow one_le_two hE0
  rw [coulombWeight_rpow_ofReal hy0, ← ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two E)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total 0 e with he0 | he0
  · rw [max_eq_left he0]
    calc (t / (1 + δ * t)) ^ e ≤ t ^ e := Real.rpow_le_rpow hy0.le hy2 he0
      _ = 1 * t ^ e := (one_mul _).symm
      _ ≤ 2 ^ E * t ^ e := mul_le_mul_of_nonneg_right h2E (Real.rpow_nonneg ht0.le e)
  · rw [max_eq_right he0, Real.rpow_zero, mul_one]
    calc (t / (1 + δ * t)) ^ e ≤ ((2 : ℝ)⁻¹) ^ e :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hy1 he0
      _ = 2 ^ (-e) := by rw [Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two]
      _ ≤ 2 ^ E := Real.rpow_le_rpow_of_exponent_le one_le_two
          ((neg_le_abs e).trans he)

/-! ### Compact regions -/

section
variable {N : ℕ} {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf : ℝ}
  {δ Zs E ρs L : ℝ} {x : ℂ}

/-- Away from the chosen root, the denominators are bounded above and away from zero
in both charts. The chosen denominator is compared to the finite-chart distance. -/
private theorem cutoffForm_root_le {k : Fin N} {t g Ri : ℝ}
    (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri)
    (hLρ : Zs + 1 ≤ L * ρs) (hL : 3 * Zs + 3 ≤ L) (hLRi : (Zs + 1) * Ri ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E)
    (hαinf : |γ * αinf| ≤ E) (hsep : ∀ j, j ≠ k → 2 * ρs ≤ ‖z j - z k‖)
    (hx : x ∈ Metric.ball (z k) ρs) (ht : Ri⁻¹ ≤ t) (htm : t ≤ normPlus x)
    (hg : L⁻¹ ≤ g ∧ g ≤ L) :
    cutoffForm γ α z αinf δ x t g ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) * ENNReal.ofReal ((‖x - z k‖ + δ) ^ (-γ * α k)) := by
  have ht0 := (inv_pos.mpr (one_pos.trans_le hRi)).trans_le ht
  have hd : ‖x - z k‖ < ρs := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have hmM : normPlus x ≤ Zs + 1 := max_le (by linarith) (by
    linarith only [norm_sub_norm_le x (z k), hd, hρs1, coulombCutoffBound_norm_le hz k])
  have hδt := (mul_le_of_le_one_left ht0.le hδ1).trans (htm.trans hmM)
  have hδt0 := mul_pos hδ ht0
  have hL1 : 1 ≤ L := by linarith
  have hD : 0 < ‖x - z k‖ + δ := by positivity
  have ha (j : Fin N) (hj : j ≠ k) :
      L⁻¹ ≤ normPlus x / (‖x - z j‖ + δ * t) ∧ normPlus x / (‖x - z j‖ + δ * t) ≤ L := by
    obtain ⟨hl, hu⟩ := coulombCutoffBound_root_dist (coulombCutoffBound_norm_le hz j)
      (hsep j hj) hd (coulombCutoffBound_norm_le hz k) hρs1
    exact coulombWeight_quot_bounds hρs hρs1 hm1 hmM (by linarith) (by linarith) hLρ hL
  obtain ⟨hc1, hc2⟩ := coulombCutoffBound_root_numer hm1 htm hmM (norm_nonneg (x - z k)) hδ hRi ht
  rw [neg_mul, ← coulombWeight_rpow_ofReal hD, cutoffForm]
  apply coulombCutoffBound_rootForm_le _ _ _ _ _ _ k hL1 hE hD _
    (coulombCutoffBound_mem_of_one_le hL1 hc1 (hc2.trans hLRi)) hg ha hα hαinf
  rw [div_div, mul_div_mul_right _ _ hD.ne']

private theorem cutoffForm_bulk_le {R0 t g : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hLρ : 1 + R0 ≤ L * ρs) (hL : 2 * R0 + Zs + 2 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E)
    (hαinf : |γ * αinf| ≤ E) (hxR : ‖x‖ ≤ R0) (hxz : ∀ k, ρs ≤ ‖x - z k‖)
    (ht : 0 ≤ t) (htR : t ≤ 1 + R0) (hg : L⁻¹ ≤ g ∧ g ≤ L) :
    cutoffForm γ α z αinf δ x t g ≤ ENNReal.ofReal (L ^ ((N : ℝ) * E + E)) := by
  have hR0 := (norm_nonneg x).trans hxR
  have hmM : normPlus x ≤ 1 + R0 := max_le (by linarith) (by linarith)
  have hδt := (mul_le_of_le_one_left ht hδ1).trans htR
  have hδt0 := mul_nonneg hδ.le ht
  refine coulombCutoffBound_form_le _ _ g _ (by linarith) hE (fun j => ?_) hg hα hαinf
  have hdist := norm_sub_le x (z j)
  have hzj := coulombCutoffBound_norm_le hz j
  exact coulombWeight_quot_bounds hρs hρs1 (le_max_left _ _) hmM
    (by linarith only [hxz j, hδt0]) (by linarith) hLρ hL

end

/-! ### Exterior -/

private theorem exterior_base_mem {Zs ε : ℝ} {x z : ℂ}
    (hx : 2 * Zs ≤ ‖x‖) (hx0 : 0 < ‖x‖) (hz : ‖z‖ ≤ Zs) (hε : 0 ≤ ε) (hεx : ε ≤ ‖x‖) :
    (5 / 2 : ℝ)⁻¹ ≤ ‖x‖ / (‖x - z‖ + ε) ∧ ‖x‖ / (‖x - z‖ + ε) ≤ 5 / 2 :=
  coulombCutoffBound_ext_quot hx hx0 (by linarith only [norm_sub_norm_le x z, hz, hε])
    (by linarith only [norm_sub_le x z, hz, hεx])

/-- The norm on the fixed exterior disk. -/
theorem coulombCutoffBound_ball_norm {R0 : ℝ} (hR0 : 0 ≤ R0) {x : ℂ}
    (hx : x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8)) :
    R0 + 7 / 8 < ‖x‖ ∧ ‖x‖ < R0 + 9 / 8 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 := norm_sub_norm_le x (((R0 + 1 : ℝ)) : ℂ)
  have h2 := norm_sub_norm_le (((R0 + 1 : ℝ)) : ℂ) x
  have h3 : ‖(((R0 + 1 : ℝ)) : ℂ)‖ = R0 + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith only [hR0])]
  rw [norm_sub_rev] at h2
  constructor <;> linarith only [h1, h2, h3, hx]

private theorem cutoffForm_ball_ge {N : ℕ} {Zs E R0 γ δ t g : ℝ} {α : Fin N → ℝ}
    {z : Fin N → ℂ} {αinf : ℝ} {x : ℂ}
    (hZs : 0 ≤ Zs) (hR0 : 2 * Zs + 2 ≤ R0) (hz : ∑ j, ‖z j‖ ≤ Zs)
    (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hx : x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ht : 0 ≤ t) (htx : t ≤ ‖x‖) (hg : (R0 + 2)⁻¹ ≤ g ∧ g ≤ R0 + 2) :
    ENNReal.ofReal ((R0 + 2) ^ (-((N : ℝ) * E + E))) ≤ cutoffForm γ α z αinf δ x t g := by
  obtain ⟨hl, hu⟩ := coulombCutoffBound_ball_norm (by linarith) hx
  rw [cutoffForm, show normPlus x = ‖x‖ from max_eq_right (by linarith)]
  refine coulombCutoffBound_form_ge _ _ _ _ (by linarith) (fun j => ?_) hg hα hαinf
  exact coulombCutoffBound_mem_mono (L := 5 / 2) (by norm_num) (by linarith)
    (exterior_base_mem (by linarith) (by linarith) (coulombCutoffBound_norm_le hz j)
      (mul_nonneg hδ.le ht) ((mul_le_of_le_one_left ht hδ1).trans htx))

/-- On the support of the inverted partition function, a bound on `‖x⁻¹‖` is a lower bound on
`‖x‖`. -/
theorem coulombCutoffBound_le_norm_of_inv {x : ℂ} {Ri : ℝ} (hRi : 0 < Ri) (hx : x ≠ 0)
    (h : ‖x⁻¹‖ ≤ Ri) : Ri⁻¹ ≤ ‖x‖ := by
  rw [norm_inv] at h
  exact (inv_le_comm₀ (norm_pos_iff.mpr hx) hRi).1 h

/-- The scale `L` used near a finite root. -/
theorem coulombCutoffBound_root_const {Zs ρs Ri : ℝ} (hZs : 0 ≤ Zs) (hρs : 0 < ρs)
    (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri) :
    ∃ L : ℝ, Zs + 1 ≤ L * ρs ∧ 3 * Zs + 3 ≤ L ∧ (Zs + 1) * Ri ≤ L := by
  refine ⟨(3 * Zs + 3) * Ri / ρs, ?_, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ hρs.ne']
    linarith only [mul_nonneg hZs (sub_nonneg.2 hRi), hZs, hRi]
  · rw [le_div_iff₀ hρs]
    nlinarith
  · rw [le_div_iff₀ hρs]
    have hZ1 : 0 ≤ Zs + 1 := by linarith only [hZs]
    have hRi0 : 0 ≤ Ri := by linarith only [hRi]
    linarith only [mul_nonneg hZ1 hRi0, mul_nonneg (mul_nonneg hZ1 hRi0) (sub_nonneg.2 hρs1)]

/-- The scale `L` used in the bulk. -/
theorem coulombCutoffBound_bulk_const {Zs R0 ρs : ℝ} (hZs : 0 ≤ Zs) (hR0 : 0 ≤ R0)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) : ∃ L : ℝ, 1 + R0 ≤ L * ρs ∧ 2 * R0 + Zs + 2 ≤ L := by
  refine ⟨(2 * R0 + Zs + 2) / ρs, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ hρs.ne']
    linarith
  · rw [le_div_iff₀ hρs]
    linarith only [mul_nonneg (by positivity : 0 ≤ 2 * R0 + Zs + 2)
      (sub_nonneg.2 hρs1)]

section
variable (partition : GMCChartPartition) (N : ℕ)

/-- Near a finite root the single-chart weight is the softened root singularity times a bounded
factor, uniformly over bounded parameters. -/
theorem coulombCutoffWeight_le_root
    {Zs E ρs Ri : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri)
    (hsupp : ∀ u, partition.infinityWeight u ≠ 0 → ‖u‖ ≤ Ri) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (k : Fin N)
      (x : ℂ), 0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      (∀ j, j ≠ k → 2 * ρs ≤ ‖z j - z k‖) → x ∈ Metric.ball (z k) ρs → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤
        ENNReal.ofReal C * ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) := by
  obtain ⟨L, hLρ, hL, hLRi⟩ := coulombCutoffBound_root_const hZs hρs hρs1 hRi
  have hL2 : 2 ≤ L := by linarith
  refine ⟨L ^ ((N : ℝ) * E + E + E), by positivity, ?_⟩
  intro γ α z αinf r k x hr hz hα hαinf hsep hx hx0
  have hm : normPlus x ≤ L := max_le (by linarith) (by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    linarith only [hZs, hL, hρs1, hx, norm_sub_norm_le x (z k), coulombCutoffBound_norm_le hz k])
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  apply cutoffWeight_le _ _ _ _ _ _ hx0
  · rw [cutoffFinite_eq]
    exact fun _ => cutoffForm_root_le hZs hE hρs hρs1 hRi hLρ hL hLRi hδ hδ1 hz hα hαinf
      hsep hx (inv_le_one_of_one_le₀ hRi) (le_max_left _ _)
      (coulombCutoffBound_mem_of_one_le (by linarith) (le_max_left _ _) hm)
  · rw [cutoffInfinity_eq _ _ _ _ _ hx0]
    exact fun hs => cutoffForm_root_le hZs hE hρs hρs1 hRi hLρ hL hLRi hδ hδ1 hz hα hαinf
      hsep hx (coulombCutoffBound_le_norm_of_inv (one_pos.trans_le hRi) hx0 (hsupp _ hs))
      (le_max_right _ _) (cutoff_last_mem hL2 hm hδ hδ1)

/-- Away from the roots, on a bounded set, the single-chart weight is bounded. -/
theorem coulombCutoffWeight_le_bulk
    {Zs E ρs R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hR0 : 0 ≤ R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      ‖x‖ ≤ R0 → (∀ k, ρs ≤ ‖x - z k‖) → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤ ENNReal.ofReal C := by
  obtain ⟨L, hLρ, hL⟩ := coulombCutoffBound_bulk_const hZs hR0 hρs hρs1
  have hL2 : 2 ≤ L := by linarith
  refine ⟨L ^ ((N : ℝ) * E + E), by positivity, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hxR hxz hx0
  have hm : normPlus x ≤ L := (max_le (by linarith) (by linarith only [hxR]) :
    normPlus x ≤ 1 + R0).trans (hLρ.trans (mul_le_of_le_one_right (by linarith) hρs1))
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  apply cutoffWeight_le _ _ _ _ _ _ hx0
  · rw [cutoffFinite_eq]
    exact fun _ => cutoffForm_bulk_le hZs hE hρs hρs1 hLρ hL hδ hδ1 hz hα hαinf hxR hxz
      zero_le_one (by linarith) (coulombCutoffBound_mem_of_one_le (by linarith) (le_max_left _ _) hm)
  · rw [cutoffInfinity_eq _ _ _ _ _ hx0]
    exact fun _ => cutoffForm_bulk_le hZs hE hρs hρs1 hLρ hL hδ hδ1 hz hα hαinf hxR hxz
      (norm_nonneg x) (by linarith) (cutoff_last_mem hL2 hm hδ hδ1)

/-- Far out the single-chart weight is at most a constant times the power at infinity. -/
theorem coulombCutoffWeight_le_exterior
    {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hR0 : 2 * Zs + 2 ≤ R0)
    (hsuppf : ∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E → R0 ≤ ‖x‖ →
      coulombCutoffWeight partition γ α z αinf r x ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0) := by
  refine ⟨(5 / 2 : ℝ) ^ ((N : ℝ) * E) * 2 ^ E, by positivity, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hxR
  have ht0 : 0 < ‖x‖ := by linarith
  have hx0 := norm_pos_iff.mp ht0
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  apply cutoffWeight_le _ _ _ _ _ _ hx0 (fun h => absurd (hsuppf x h) (not_lt.2 hxR))
  intro _
  rw [cutoffInfinity_eq _ _ _ _ _ hx0, cutoffForm, show normPlus x = ‖x‖ from max_eq_right (by linarith),
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  refine mul_le_mul' (coulombCutoffBound_prod_le Finset.univ _ _ (by norm_num) hE
    (fun j _ => ?_) (fun j _ => hα j)) (coulombCutoffBound_exterior_last (by linarith) hδ hδ1 hαinf)
  exact exterior_base_mem (by linarith) ht0 (coulombCutoffBound_norm_le hz j)
    (mul_nonneg hδ.le ht0.le) (mul_le_of_le_one_left ht0.le hδ1)

/-- On a fixed exterior disk the single-chart weight is bounded below. -/
theorem coulombCutoffWeight_ge_ball
    {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hR0 : 2 * Zs + 2 ≤ R0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8) →
      ENNReal.ofReal c ≤ coulombCutoffWeight partition γ α z αinf r x := by
  refine ⟨(R0 + 2) ^ (-((N : ℝ) * E + E)), Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hx
  obtain ⟨hl, hu⟩ := coulombCutoffBound_ball_norm (by linarith) hx
  have hx0 := norm_pos_iff.mp (by linarith : 0 < ‖x‖)
  have hm : normPlus x ≤ R0 + 2 := max_le (by linarith) (by linarith)
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  apply le_cutoffWeight _ _ _ _ _ _ hx0
  · rw [cutoffFinite_eq]
    exact cutoffForm_ball_ge hZs hR0 hz hα hαinf hx hδ hδ1 zero_le_one (by linarith)
      (coulombCutoffBound_mem_of_one_le (by linarith) (le_max_left _ _) hm)
  · rw [cutoffInfinity_eq _ _ _ _ _ hx0]
    exact cutoffForm_ball_ge hZs hR0 hz hα hαinf hx hδ hδ1 (norm_nonneg x) le_rfl
      (cutoff_last_mem (by linarith) hm hδ hδ1)

end

end DOZZ.Proofs
