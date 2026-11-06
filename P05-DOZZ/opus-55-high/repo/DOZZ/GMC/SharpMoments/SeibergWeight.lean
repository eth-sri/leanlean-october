/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CoulombMass

/-! # Deterministic bounds for the Coulomb weight

The Coulomb weight is the integrand of `coulombMass`. Near a finite root it is a bounded multiple
of the root singularity, on a bulk region away from the finite roots and from infinity it is
bounded, and on an exterior region it is comparable to the power at infinity. Every point lies
near a root, in the bulk, or in the exterior, which gives a covering inequality. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The Coulomb weight integrated by `coulombMass`. -/
noncomputable def coulombWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ)
    (x : ℂ) : ℝ≥0∞ :=
  (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z k‖)) (γ * α k)) *
    ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf)
section
variable {N : ℕ} (γ : ℝ)

theorem coulombMass_eq_lintegral_coulombWeight (μ : Measure ℂ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    coulombMass γ μ α z αinf = ∫⁻ x, coulombWeight γ α z αinf x ∂μ := rfl

theorem measurable_coulombWeight (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    Measurable (coulombWeight γ α z αinf) := by
  have hn : Measurable normPlus := by
    unfold normPlus
    fun_prop
  unfold coulombWeight
  measurability

end
section
variable {L y : ℝ}
section
variable (hL : 1 ≤ L) (hy1 : L⁻¹ ≤ y) (hy2 : y ≤ L) (e : ℝ)
include hL hy1 hy2

/-! ### Real power bounds on an interval -/

/-- The real power of a point of `[L⁻¹, L]` is at most `L ^ |e|`. -/
theorem coulombWeight_rpow_le :
    y ^ e ≤ L ^ |e| := by
  have hLpos := lt_of_lt_of_le one_pos hL
  have hypos := lt_of_lt_of_le (inv_pos.mpr hLpos) hy1
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he]
    bound
  · rw [abs_of_nonpos he]
    have h1 : y ^ e = y⁻¹ ^ (-e) := by
      rw [Real.inv_rpow hypos.le, Real.rpow_neg hypos.le, inv_inv]
    have h2 : y⁻¹ ≤ L := by
      have := inv_anti₀ (inv_pos.mpr hLpos) hy1
      simp_all
    rw [h1]
    bound

/-- The real power of a point of `[L⁻¹, L]` is at least `L ^ (-|e|)`. -/
theorem coulombWeight_le_rpow :
    L ^ (-|e|) ≤ y ^ e := by
  have hLpos := lt_of_lt_of_le one_pos hL
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he]
    have h1 : L ^ (-e) = L⁻¹ ^ e := by
      rw [Real.inv_rpow hLpos.le, Real.rpow_neg hLpos.le]
    rw [h1]
    bound
  · rw [abs_of_nonpos he, neg_neg]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (inv_pos.mpr hLpos) hy1) hy2 he

end

end

/-- `ENNReal.rpow` of `ENNReal.ofReal` of a positive real. -/
theorem coulombWeight_rpow_ofReal {y : ℝ} (hy : 0 < y) (e : ℝ) :
    ENNReal.rpow (ENNReal.ofReal y) e = ENNReal.ofReal (y ^ e) := by
  rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hy]
section
variable {L y : ℝ}
section
variable (hL : 1 ≤ L) (hy1 : L⁻¹ ≤ y) (hy2 : y ≤ L) (e : ℝ)
include hL hy1 hy2

/-- On a positive interval `[L⁻¹, L]`, real powers are bounded above by `L ^ |e|`. -/
theorem ennreal_rpow_ofReal_le_of_mem_Icc : ENNReal.rpow (ENNReal.ofReal y) e ≤ ENNReal.ofReal (L ^ |e|) := by
  rw [coulombWeight_rpow_ofReal (lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le one_pos hL)) hy1)]
  exact ENNReal.ofReal_le_ofReal (coulombWeight_rpow_le hL hy1 hy2 e)

/-- On a positive interval `[L⁻¹, L]`, real powers are bounded below by `L ^ (-|e|)`. -/
theorem ennreal_ofReal_le_rpow_ofReal_of_mem_Icc : ENNReal.ofReal (L ^ (-|e|)) ≤ ENNReal.rpow (ENNReal.ofReal y) e := by
  rw [coulombWeight_rpow_ofReal (lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le one_pos hL)) hy1)]
  exact ENNReal.ofReal_le_ofReal (coulombWeight_le_rpow hL hy1 hy2 e)

end

end

/-- The singular factor splits off the distance to a root. -/
theorem coulombWeight_rpow_ofReal_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (e : ℝ) :
    ENNReal.rpow (ENNReal.ofReal (a / b)) e =
      ENNReal.rpow (ENNReal.ofReal a) e * ENNReal.rpow (ENNReal.ofReal b) (-e) := by
  rw [coulombWeight_rpow_ofReal (div_pos ha hb), coulombWeight_rpow_ofReal ha,
    coulombWeight_rpow_ofReal hb, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le e),
    Real.div_rpow ha.le hb.le, Real.rpow_neg hb.le, div_eq_mul_inv]

/-- Powers of a common base multiply by adding exponents. -/
theorem coulombWeight_ofReal_rpow_mul {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    ENNReal.ofReal (L ^ s) * ENNReal.ofReal (L ^ t) = ENNReal.ofReal (L ^ (s + t)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le s), ← Real.rpow_add hL]
section
variable {ι : Type*} (s : Finset ι) (a e : ι → ℝ) {L : ℝ}
section
variable (hL : 1 ≤ L) (h : ∀ j ∈ s, L⁻¹ ≤ a j ∧ a j ≤ L)
include hL h

/-- A finite product of powers with bases in `[L⁻¹, L]`: upper bound. -/
theorem coulombWeight_prod_le :
    ∏ j ∈ s, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) ≤
      ENNReal.ofReal (L ^ ∑ j ∈ s, |e j|) := by
  have hLpos := lt_of_lt_of_le one_pos hL
  calc ∏ j ∈ s, ENNReal.rpow _ (e j)
      ≤ ∏ j ∈ s, ENNReal.ofReal _ :=
        Finset.prod_le_prod fun j hj =>
          ennreal_rpow_ofReal_le_of_mem_Icc hL (h j hj).1 (h j hj).2 (e j)
    _ = ENNReal.ofReal _ :=
        (ENNReal.ofReal_prod_of_nonneg fun j _ => Real.rpow_nonneg hLpos.le _).symm
    _ = ENNReal.ofReal _ := by
        rw [Real.rpow_sum_of_pos hLpos]

/-- A finite product of powers with bases in `[L⁻¹, L]`: lower bound. -/
theorem coulombWeight_prod_ge :
    ENNReal.ofReal (L ^ (-∑ j ∈ s, |e j|)) ≤
      ∏ j ∈ s, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) := by
  have hLpos := lt_of_lt_of_le one_pos hL
  calc ENNReal.ofReal _
      = ENNReal.ofReal _ := by
        rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hLpos]
    _ = ∏ j ∈ s, ENNReal.ofReal _ :=
        ENNReal.ofReal_prod_of_nonneg fun j _ => Real.rpow_nonneg hLpos.le _
    _ ≤ ∏ j ∈ s, ENNReal.rpow _ (e j) :=
        Finset.prod_le_prod fun j hj =>
          ennreal_ofReal_le_rpow_ofReal_of_mem_Icc hL (h j hj).1 (h j hj).2 (e j)

end

end

/-! ### Elementary real inequalities -/

/-- Bounds `1 ≤ a ≤ A ≤ L δ` with `δ ≤ 1` put `a` in `[L⁻¹, L]`. -/
theorem coulombWeight_base_bounds {a A L δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha1 : 1 ≤ a)
    (haA : a ≤ A) (hAL : A ≤ L * δ) : 1 ≤ L ∧ L⁻¹ ≤ a ∧ a ≤ L := by
  have hL0 : 0 < L := by
    nlinarith
  have hLδ := mul_le_of_le_one_right hL0.le hδ1
  have hL1 := (ha1.trans (haA.trans hAL)).trans hLδ
  exact ⟨hL1, (inv_le_one_of_one_le₀ hL1).trans ha1, haA.trans (hAL.trans hLδ)⟩

/-- Quotient `a / b` with `1 ≤ a ≤ A ≤ L δ` and `δ ≤ b ≤ B ≤ L` lies in `[L⁻¹, L]`. -/
theorem coulombWeight_quot_bounds {a b A B L δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha1 : 1 ≤ a)
    (haA : a ≤ A) (hδb : δ ≤ b) (hbB : b ≤ B) (hAL : A ≤ L * δ) (hBL : B ≤ L) :
    L⁻¹ ≤ a / b ∧ a / b ≤ L := by
  obtain ⟨hL1, -, -⟩ := coulombWeight_base_bounds hδ hδ1 ha1 haA hAL
  have hL0 := lt_of_lt_of_le one_pos hL1
  have hb := lt_of_lt_of_le hδ hδb
  constructor
  · rw [le_div_iff₀ hb]
    calc L⁻¹ * b ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left (hbB.trans hBL) (inv_nonneg.mpr hL0.le)
      _ = 1 := inv_mul_cancel₀ hL0.ne'
      _ ≤ a := ha1
  · rw [div_le_iff₀ hb]
    nlinarith

/-- Quotient bounds far from the origin: `v` is within `w` of `u` and `2 w < u`. -/
theorem coulombWeight_exterior_quot_bounds {u v w : ℝ} (hw0 : 0 ≤ w) (hwu : 2 * w < u)
    (hv1 : u - w ≤ v) (hv2 : v ≤ u + w) : (2 : ℝ)⁻¹ ≤ u / v ∧ u / v ≤ 2 := by
  have hv : 0 < v := by linarith
  constructor
  · rw [le_div_iff₀ hv]
    linarith
  · rw [div_le_iff₀ hv]
    linarith
section
variable {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ)

/-! ### Bounds for the Coulomb weight -/

/-- Near a finite root the Coulomb weight is the root singularity times a bounded factor. -/
theorem coulombWeight_le_root (k : Fin N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ j, j ≠ k → 2 * δ ≤ ‖z j - z k‖) {x : ℂ} (hx : x ∈ Metric.ball (z k) δ)
    (hxk : x ≠ z k) :
    coulombWeight γ α z αinf x ≤
      ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) *
        ENNReal.rpow (ENNReal.ofReal ‖x - z k‖) (-γ * α k) := by
  set S := ∑ j, ‖z j‖ with hS_def
  set L := (2 + 2 * S) / δ with hL_def
  have hS : 0 ≤ S := by positivity
  have hzS : ∀ j, ‖z j‖ ≤ S := fun j =>
    Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)
  have hr0 : 0 < ‖x - z k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxk)
  have hrδ : ‖x - z k‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hxn : ‖x‖ ≤ 1 + S := by
    have h1 := norm_sub_norm_le x (z k)
    linarith [hzS k]
  have ha1 : 1 ≤ normPlus x := le_max_left ..
  have haA : normPlus x ≤ 1 + S := max_le (by linarith) hxn
  have hLδ : L * δ = 2 + 2 * S := div_mul_cancel₀ _ hδ.ne'
  have hAL : 1 + S ≤ L * δ := by linarith
  have hBL : 1 + 2 * S ≤ L := by
    nlinarith
  obtain ⟨hL1, hLa1, hLa2⟩ := coulombWeight_base_bounds hδ hδ1 ha1 haA hAL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hP : ∏ j ∈ Finset.univ.erase k,
        ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z j‖)) (γ * α j) ≤
      ENNReal.ofReal (L ^ ∑ j ∈ Finset.univ.erase k, |γ * α j|) := by
    refine coulombWeight_prod_le _ (fun j => normPlus x / ‖x - z j‖) (fun j => γ * α j) hL1 ?_
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    have hδb : δ ≤ ‖x - z j‖ := by
      have h1 := hsep j hjk
      have h2 : ‖z j - z k‖ ≤ ‖x - z j‖ + ‖x - z k‖ :=
        calc ‖z j - z k‖ = ‖(z j - x) + (x - z k)‖ := by congr 1; ring
          _ ≤ ‖z j - x‖ + ‖x - z k‖ := norm_add_le ..
          _ = ‖x - z j‖ + ‖x - z k‖ := by rw [norm_sub_rev]
      linarith
    have hbB : ‖x - z j‖ ≤ 1 + 2 * S := by
      have h1 := norm_sub_le x (z j)
      linarith [hzS j]
    exact coulombWeight_quot_bounds hδ hδ1 ha1 haA hδb hbB hAL hBL
  have hA : ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * α k) ≤
      ENNReal.ofReal (L ^ |γ * α k|) :=
    ennreal_rpow_ofReal_le_of_mem_Icc hL1 hLa1 hLa2 _
  have hI : ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) ≤
      ENNReal.ofReal (L ^ |γ * αinf|) :=
    ennreal_rpow_ofReal_le_of_mem_Icc hL1 hLa1 hLa2 _
  have hTk : ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z k‖)) (γ * α k) =
      ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * α k) *
        ENNReal.rpow (ENNReal.ofReal ‖x - z k‖) (-γ * α k) := by
    rw [coulombWeight_rpow_ofReal_div (lt_of_lt_of_le one_pos ha1) hr0, neg_mul]
  have hexp : ∑ j, |γ * α j| + |γ * αinf| =
      |γ * α k| + ∑ j ∈ Finset.univ.erase k, |γ * α j| + |γ * αinf| := by
    rw [Finset.add_sum_erase Finset.univ (fun j => |γ * α j|) (Finset.mem_univ k)]
  unfold coulombWeight
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hTk]
  generalize ENNReal.rpow (ENNReal.ofReal ‖x - z k‖) (-γ * α k) = R
  calc _ ≤ ((ENNReal.ofReal (L ^ |γ * α k|) * R) *
        ENNReal.ofReal (L ^ ∑ j ∈ Finset.univ.erase k, |γ * α j|)) *
        ENNReal.ofReal (L ^ |γ * αinf|) := by gcongr
    _ = (ENNReal.ofReal (L ^ |γ * α k|) *
        ENNReal.ofReal (L ^ ∑ j ∈ Finset.univ.erase k, |γ * α j|) *
        ENNReal.ofReal (L ^ |γ * αinf|)) * R := by ring
    _ = ENNReal.ofReal (L ^ (|γ * α k| + ∑ j ∈ Finset.univ.erase k, |γ * α j| +
        |γ * αinf|)) * R := by
      rw [coulombWeight_ofReal_rpow_mul hL0, coulombWeight_ofReal_rpow_mul hL0]
    _ = _ := by simp

/-- Away from the finite roots and from infinity the Coulomb weight is bounded. -/
theorem coulombWeight_le_bulk {δ Rr : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hRr : 0 ≤ Rr) {x : ℂ} (hx : ‖x‖ ≤ Rr)
    (hxz : ∀ k, δ ≤ ‖x - z k‖) :
    coulombWeight γ α z αinf x ≤
      ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) := by
  set S := ∑ j, ‖z j‖ with hS_def
  set L := (1 + Rr + S) / δ with hL_def
  have hS : 0 ≤ S := by positivity
  have hzS : ∀ j, ‖z j‖ ≤ S := fun j =>
    Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)
  have ha1 : 1 ≤ normPlus x := le_max_left ..
  have haA : normPlus x ≤ 1 + Rr := max_le (by linarith) (by linarith)
  have hLδ : L * δ = 1 + Rr + S := div_mul_cancel₀ _ hδ.ne'
  have hAL : 1 + Rr ≤ L * δ := by linarith
  have hBL : Rr + S ≤ L := by
    nlinarith
  obtain ⟨hL1, hLa1, hLa2⟩ := coulombWeight_base_bounds hδ hδ1 ha1 haA hAL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hP : ∏ j, ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z j‖)) (γ * α j) ≤
      ENNReal.ofReal (L ^ ∑ j, |γ * α j|) := by
    refine coulombWeight_prod_le Finset.univ (fun j => normPlus x / ‖x - z j‖)
      (fun j => γ * α j) hL1 ?_
    intro j _
    have hbB : ‖x - z j‖ ≤ Rr + S := by
      have h1 := norm_sub_le x (z j)
      linarith [hzS j]
    exact coulombWeight_quot_bounds hδ hδ1 ha1 haA (hxz j) hbB hAL hBL
  have hI : ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) ≤
      ENNReal.ofReal _ :=
    ennreal_rpow_ofReal_le_of_mem_Icc hL1 hLa1 hLa2 _
  calc coulombWeight γ α z αinf x
      ≤ ENNReal.ofReal _ * ENNReal.ofReal _ :=
        mul_le_mul' hP hI
    _ = ENNReal.ofReal _ :=
        coulombWeight_ofReal_rpow_mul hL0 ..
section
variable {Rr : ℝ} (hRr : 1 ≤ Rr) (hz : ∀ j, 2 * ‖z j‖ ≤ Rr) {x : ℂ} (hx : Rr < ‖x‖)
include hRr hz hx

/-- Far out the Coulomb weight is comparable to the power at infinity: upper bound. -/
theorem coulombWeight_le_exterior :
    coulombWeight γ α z αinf x ≤
      ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) *
        ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) := by
  have hnp : normPlus x = ‖x‖ := max_eq_right (hRr.trans hx.le)
  have hprod := coulombWeight_prod_le Finset.univ (fun j => ‖x‖ / ‖x - z j‖)
    (fun j => γ * α j) one_le_two fun j _ =>
    coulombWeight_exterior_quot_bounds (norm_nonneg (z j)) (by grind)
      (by linarith [norm_sub_norm_le x (z j)]) (norm_sub_le x (z j))
  unfold coulombWeight
  rw [hnp]
  bound

/-- Far out the Coulomb weight is comparable to the power at infinity: lower bound. -/
theorem coulombWeight_ge_exterior :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ≤
      coulombWeight γ α z αinf x := by
  have hnp : normPlus x = ‖x‖ := max_eq_right (hRr.trans hx.le)
  have hprod := coulombWeight_prod_ge Finset.univ (fun j => ‖x‖ / ‖x - z j‖)
    (fun j => γ * α j) one_le_two fun j _ =>
    coulombWeight_exterior_quot_bounds (norm_nonneg (z j)) (by grind)
      (by linarith [norm_sub_norm_le x (z j)]) (norm_sub_le x (z j))
  unfold coulombWeight
  rw [hnp]
  bound

end

/-- Every point lies near a root, in the bulk, or in the exterior. -/
theorem coulombWeight_le_pieces (δ Rr : ℝ) (x : ℂ) :
    coulombWeight γ α z αinf x ≤
      ∑ k, (Metric.ball (z k) δ).indicator (coulombWeight γ α z αinf) x +
        {y : ℂ | ‖y‖ ≤ Rr ∧ ∀ k, δ ≤ ‖y - z k‖}.indicator (coulombWeight γ α z αinf) x +
        {y : ℂ | Rr < ‖y‖}.indicator (coulombWeight γ α z αinf) x := by
  by_cases hext : Rr < ‖x‖
  · simp_all
  · by_cases hroot : ∃ k, ‖x - z k‖ < δ
    · obtain ⟨k, hk⟩ := hroot
      have h1 : (Metric.ball (z k) δ).indicator (coulombWeight γ α z αinf) x =
          coulombWeight γ α z αinf x :=
        Set.indicator_of_mem (by rwa [Metric.mem_ball, dist_eq_norm]) _
      have h2 : coulombWeight γ α z αinf x ≤
          ∑ k, (Metric.ball (z k) δ).indicator _ x :=
        calc coulombWeight γ α z αinf x
            = (Metric.ball (z k) δ).indicator _ x := h1.symm
          _ ≤ ∑ k, (Metric.ball (z k) δ).indicator _ x :=
              Finset.single_le_sum
                (f := fun k => (Metric.ball (z k) δ).indicator _ x)
                (fun _ _ => zero_le) (Finset.mem_univ k)
      exact h2.trans (le_self_add.trans le_self_add)
    simp_all

end

end DOZZ.Proofs
