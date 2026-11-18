/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.IntegralHolomorphy
public import DOZZ.Upsilon.StripShifts
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.HalfPlane

/-!
# Entire continuation of the Upsilon strip function
-/

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace DOZZ.Proofs

variable {γ : ℝ}

private def upsBase (γ : ℝ) (z : ℂ) : ℂ := Complex.exp (upsilonLog γ z)
private def upsB (γ : ℝ) : ℂ := ((γ / 2 : ℝ) : ℂ)
private def upsShift (γ : ℝ) (n : ℕ) : ℂ := ((n : ℝ) * (γ / 2) : ℂ)

private def upsRFactor (γ : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (upsB γ * z) * (Complex.Gamma (1 - upsB γ * z))⁻¹ * upsB γ ^ (1 - (γ : ℂ) * z)

private def upsLFactor (γ : ℝ) (z : ℂ) : ℂ :=
  upsB γ ^ ((γ : ℂ) * z - 1) * Complex.Gamma (1 - upsB γ * z) * (Complex.Gamma (upsB γ * z))⁻¹

private def upsRChart (γ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  upsBase γ (z - upsShift γ n) * ∏ j ∈ Finset.range n, upsRFactor γ (z - upsShift γ (j + 1))

private def upsLChart (γ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  upsBase γ (z + upsShift γ n) * ∏ j ∈ Finset.range n, upsLFactor γ (z + upsShift γ j)

private def upsRDom (γ : ℝ) (n : ℕ) : Set ℂ :=
  {z | 0 < (z - upsShift γ n).re ∧ (z - upsShift γ n).re < Q γ}

private def upsLDom (γ : ℝ) (n : ℕ) : Set ℂ :=
  {z | 0 < (z + upsShift γ n).re ∧ (z + upsShift γ n).re < Q γ}

@[simp] private lemma upsShift_re (γ : ℝ) (n : ℕ) : (upsShift γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsShift]





/-- Existence of an entire Upsilon function from the defining strip integral and its first shift. -/
theorem exists_IsUpsilon (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ U : ℂ → ℂ, IsUpsilon γ U := by
  have exists_chart (z : ℂ) : ∃ s : ℕ ⊕ ℕ, z ∈ Sum.elim (upsLDom γ) (upsRDom γ) s := by
    have hb : 0 < γ / 2 := half_pos hγ
    have hQb : γ / 2 < Q γ := by unfold Q; linarith [div_pos zero_lt_two hγ]
    have hQ2b : γ < Q γ := by
      unfold Q; have : γ / 2 < 2 / γ := (lt_div_iff₀ hγ).2 (by nlinarith); linarith
    by_cases hzpos : 0 < z.re
    · let y := z.re / (γ / 2)
      have hy0 : 0 ≤ y := by positivity
      by_cases hylt : y < 1
      · refine ⟨.inr 0, ?_⟩
        simp only [Sum.elim_inr, upsRDom, upsShift, Nat.cast_zero, zero_mul, Complex.ofReal_zero, sub_zero]
        exact ⟨hzpos, by linarith [(div_lt_iff₀ hb).1 hylt]⟩
      · let N := Nat.floor y
        have hN1 : 1 ≤ N := (Nat.one_le_floor_iff y).2 (le_of_not_gt hylt)
        refine ⟨.inr (N - 1), ?_⟩
        simp only [Sum.elim_inr, upsRDom, Complex.sub_re, upsShift_re, Nat.cast_sub hN1, Nat.cast_one]
        have hy_eq : z.re = y * (γ / 2) := (div_mul_cancel₀ _ hb.ne').symm
        have hfl := Nat.floor_le hy0
        have hfl1 := Nat.lt_floor_add_one y
        exact ⟨by nlinarith, by nlinarith⟩
    · let y := -z.re / (γ / 2)
      have hy0 : 0 ≤ y := div_nonneg (neg_nonneg.2 (le_of_not_gt hzpos)) hb.le
      let N := Nat.floor y
      refine ⟨.inl (N + 1), ?_⟩
      simp only [Sum.elim_inl, upsLDom, Complex.add_re, upsShift_re, Nat.cast_add, Nat.cast_one]
      have hy_eq : -z.re = y * (γ / 2) := (div_mul_cancel₀ _ hb.ne').symm
      have hfl := Nat.floor_le hy0
      have hfl1 := Nat.lt_floor_add_one y
      exact ⟨by nlinarith, by nlinarith⟩
  have diffAt_upsLFactor {z : ℂ} (hz : z.re < 2 / γ) : DifferentiableAt ℂ (upsLFactor γ) z := by
    have hlt1 : (γ / 2) * z.re < 1 := by
      have := mul_lt_mul_of_pos_left hz (half_pos hγ)
      rwa [show (γ / 2) * (2 / γ) = 1 by field_simp [hγ.ne']] at this
    have hRe : 0 < (1 - upsB γ * z).re := by simp [upsB, Complex.mul_re]; linarith
    have hG1 : DifferentiableAt ℂ (fun w => upsB γ ^ ((γ : ℂ) * w - 1)) z :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.2 (by positivity)))
    have hG2 := DifferentiableAt.fun_comp' z
      (Complex.differentiableAt_Gamma (1 - upsB γ * z) fun n hn =>
        (Complex.Gamma_ne_zero_of_re_pos hRe) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
      (by fun_prop : DifferentiableAt ℂ (fun w => 1 - upsB γ * w) z)
    have hG3 := DifferentiableAt.fun_comp' z Complex.differentiable_one_div_Gamma.differentiableAt
      (by fun_prop : DifferentiableAt ℂ (fun w => upsB γ * w) z)
    exact (hG1.mul hG2).mul hG3
  have diffAt_upsRFactor {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (upsRFactor γ) z := by
    have hRe : 0 < (upsB γ * z).re := by simp [upsB, Complex.mul_re]; positivity
    have hG1 := Complex.differentiableAt_Gamma (upsB γ * z) fun n hn =>
      (Complex.Gamma_ne_zero_of_re_pos hRe) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n)
    have hG2 := DifferentiableAt.fun_comp' z Complex.differentiable_one_div_Gamma.differentiableAt
      (by fun_prop : DifferentiableAt ℂ (fun w => 1 - upsB γ * w) z)
    have hG3 : DifferentiableAt ℂ (fun w => upsB γ ^ (1 - (γ : ℂ) * w)) z :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.2 (by positivity)))
    exact ((hG1.comp z (by fun_prop)).mul hG2).mul hG3
  have chain_eq_of_overlap {P : ℕ → Prop} {F : ℕ → ℂ} (hinter : ∀ {m k n}, m ≤ k → k ≤ n → P m → P n → P k) (hstep : ∀ {k}, P k → P (k + 1) → F (k + 1) = F k) : ∀ {m n}, P m → P n → F m = F n := by
    have hle : ∀ k m, m ≤ k → P m → P k → F m = F k := fun k => by
      induction k with
      | zero => intro m hm _ _; obtain rfl := Nat.eq_zero_of_le_zero hm; rfl
      | succ k ih =>
        intro m hm pm pk1
        rcases eq_or_lt_of_le hm with rfl | hlt
        · rfl
        · have hmk : m ≤ k := Nat.lt_succ_iff.1 hlt
          have pk := hinter hmk (Nat.le_succ k) pm pk1
          exact (ih m hmk pm pk).trans (hstep pk pk1).symm
    intro m n pm pn
    rcases le_total m n with h | h
    · exact hle n m h pm pn
    · exact (hle m n h pn pm).symm
  have hQsub : Q γ - γ / 2 = 2 / γ := by unfold Q; ring
  have hbase_diff : DifferentiableOn ℂ (upsBase γ) {z | 0 < z.re ∧ z.re < Q γ} :=
    fun z hz => differentiable_exp.differentiableAt.comp_differentiableWithinAt z
      (upsilonLog_differentiableOn hγ hγ2 z hz)
  have hstrip_open : IsOpen {z : ℂ | 0 < z.re ∧ z.re < Q γ} :=
    (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (Q γ))
  have hshift (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
      upsBase γ (z + upsB γ) = upsRFactor γ z * upsBase γ z := by
    simpa [upsBase, upsB, upsRFactor, lFun, div_eq_mul_inv, mul_assoc] using
      exp_upsilonLog_shift_b hγ hγ2 hz0 hzQ
  have hlrec {v : ℂ} (hv0 : 0 < v.re) (hvQ : v.re < 2 / γ) :
      upsLFactor γ v * upsBase γ (v + upsB γ) = upsBase γ v := by
    have hbz : (upsB γ * v).re = (γ / 2) * v.re := by simp [upsB, Complex.mul_re]
    have hlt1 : (γ / 2) * v.re < 1 := by
      have := mul_lt_mul_of_pos_left hvQ (half_pos hγ)
      rwa [show (γ / 2) * (2 / γ) = 1 by field_simp [hγ.ne']] at this
    have hG0 : Complex.Gamma (upsB γ * v) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by rw [hbz]; positivity)
    have hG1 : Complex.Gamma (1 - upsB γ * v) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.sub_re, Complex.one_re, hbz]; linarith)
    have hpow : upsB γ ^ (1 - (γ : ℂ) * v) ≠ 0 :=
      Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 (by positivity : γ / 2 ≠ 0)))
    have hcancel : upsLFactor γ v * upsRFactor γ v = 1 := by
      dsimp [upsLFactor, upsRFactor]
      rw [show (γ : ℂ) * v - 1 = -(1 - (γ : ℂ) * v) by ring, Complex.cpow_neg]
      rw [mul_comm (upsB γ) v] at hG0 hG1
      field_simp [hG0, hG1, hpow]
    rw [hshift v hv0 hvQ, ← mul_assoc, hcancel, one_mul]
  have hl_eq {m n : ℕ} {z : ℂ} (hm : z ∈ upsLDom γ m) (hn : z ∈ upsLDom γ n) :
      upsLChart γ m z = upsLChart γ n z :=
    chain_eq_of_overlap (P := fun k => z ∈ upsLDom γ k) (F := fun k => upsLChart γ k z)
      (fun {a k b} hak hkb ha hb => by
        obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
        simp only [upsShift_re, Complex.add_re] at ha1 ha2 hb1 hb2
        have h1 : (a : ℝ) * (γ / 2) ≤ (k : ℝ) * (γ / 2) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hak) (by positivity)
        have h2 : (k : ℝ) * (γ / 2) ≤ (b : ℝ) * (γ / 2) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkb) (by positivity)
        exact ⟨by simp only [Complex.add_re, upsShift_re]; linarith,
          by simp only [Complex.add_re, upsShift_re]; linarith⟩)
      (fun {k} hk hk1 => by
        let v := z + upsShift γ k
        have htr : z + upsShift γ (k + 1) = v + upsB γ := by
          dsimp [v, upsShift, upsB]; push_cast; ring
        have hv0 : 0 < v.re := hk.1
        have hvQ : v.re < 2 / γ := by
          have h2 := hk1.2; rw [htr, Complex.add_re] at h2
          simp only [upsB, Complex.ofReal_re] at h2; linarith
        unfold upsLChart
        rw [Finset.prod_range_succ, htr,
          show upsBase γ (v + upsB γ) * ((∏ j ∈ Finset.range k, upsLFactor γ (z + upsShift γ j)) * upsLFactor γ v) =
            (upsLFactor γ v * upsBase γ (v + upsB γ)) * ∏ j ∈ Finset.range k, upsLFactor γ (z + upsShift γ j) by ring,
          hlrec hv0 hvQ])
      hm hn
  have hr_eq {m n : ℕ} {z : ℂ} (hm : z ∈ upsRDom γ m) (hn : z ∈ upsRDom γ n) :
      upsRChart γ m z = upsRChart γ n z :=
    chain_eq_of_overlap (P := fun k => z ∈ upsRDom γ k) (F := fun k => upsRChart γ k z)
      (fun {a k b} hak hkb ha hb => by
        obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
        simp only [upsShift_re, Complex.sub_re] at ha1 ha2 hb1 hb2
        have h1 : (a : ℝ) * (γ / 2) ≤ (k : ℝ) * (γ / 2) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hak) (by positivity)
        have h2 : (k : ℝ) * (γ / 2) ≤ (b : ℝ) * (γ / 2) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkb) (by positivity)
        exact ⟨by simp only [Complex.sub_re, upsShift_re]; linarith,
          by simp only [Complex.sub_re, upsShift_re]; linarith⟩)
      (fun {k} hk hk1 => by
        let v := z - upsShift γ (k + 1)
        have htr : z - upsShift γ k = v + upsB γ := by
          dsimp [v, upsShift, upsB]; push_cast; ring
        have hv0 : 0 < v.re := hk1.1
        have hvQ : v.re < 2 / γ := by
          have h2 := hk.2; rw [htr, Complex.add_re] at h2
          simp only [upsB, Complex.ofReal_re] at h2; linarith
        unfold upsRChart
        rw [Finset.prod_range_succ, htr,
          show upsBase γ v * ((∏ j ∈ Finset.range k, upsRFactor γ (z - upsShift γ (j + 1))) * upsRFactor γ v) =
            (upsRFactor γ v * upsBase γ v) * ∏ j ∈ Finset.range k, upsRFactor γ (z - upsShift γ (j + 1)) by ring,
          ← hshift v hv0 hvQ])
      hm hn
  let chart : ℕ ⊕ ℕ → ℂ → ℂ := Sum.elim (upsLChart γ) (upsRChart γ)
  let dom : ℕ ⊕ ℕ → Set ℂ := Sum.elim (upsLDom γ) (upsRDom γ)
  have hchart_eq {z : ℂ} {i j : ℕ ⊕ ℕ} (hi : z ∈ dom i) (hj : z ∈ dom j) : chart i z = chart j z := by
    have hlr {m n : ℕ} (hl : z ∈ upsLDom γ m) (hr : z ∈ upsRDom γ n) :
        upsLChart γ m z = upsRChart γ n z := by
      have hl1 := hl.1; have hl2 := hl.2; have hr1 := hr.1; have hr2 := hr.2
      simp only [Complex.sub_re, Complex.add_re, upsShift_re] at hl1 hl2 hr1 hr2
      have hz0 : 0 < z.re := by linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (half_pos hγ).le]
      have hzQ : z.re < Q γ := by linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (half_pos hγ).le]
      have h0L : z ∈ upsLDom γ 0 := by simpa [upsLDom, upsShift] using (⟨hz0, hzQ⟩ : 0 < z.re ∧ z.re < Q γ)
      have h0R : z ∈ upsRDom γ 0 := by simpa [upsRDom, upsShift] using (⟨hz0, hzQ⟩ : 0 < z.re ∧ z.re < Q γ)
      have h0eq : upsLChart γ 0 z = upsRChart γ 0 z := by simp [upsLChart, upsRChart, upsShift]
      exact (hl_eq hl h0L).trans (h0eq.trans (hr_eq h0R hr))
    rcases i with m | m <;> rcases j with n | n
    · exact hl_eq hi hj
    · exact hlr hi hj
    · exact (hlr hj hi).symm
    · exact hr_eq hi hj
  let idx (z : ℂ) := Classical.choose (exists_chart z)
  have hidx (z : ℂ) : z ∈ dom (idx z) := Classical.choose_spec (exists_chart z)
  let U (z : ℂ) := chart (idx z) z
  refine ⟨U, fun z => ?_, fun z hz0 hzQ => ?_⟩
  · have hopen (s : ℕ ⊕ ℕ) : IsOpen (dom s) := by
      rcases s with n | n
      · exact isOpen_Ioo.preimage (by fun_prop : Continuous fun w : ℂ => (w + upsShift γ n).re)
      · exact isOpen_Ioo.preimage (by fun_prop : Continuous fun w : ℂ => (w - upsShift γ n).re)
    have hloc : U =ᶠ[𝓝 z] chart (idx z) :=
      eventually_of_mem ((hopen (idx z)).mem_nhds (hidx z)) fun w hw => hchart_eq (hidx w) hw
    refine (?_ : DifferentiableAt ℂ (chart (idx z)) z).congr_of_eventuallyEq hloc
    have hz := hidx z
    rcases h : idx z with n | n
    · rw [h] at hz
      have hzn : z + upsShift γ n ∈ {w : ℂ | 0 < w.re ∧ w.re < Q γ} := hz
      have hb := (hbase_diff.differentiableAt (hstrip_open.mem_nhds hzn)).comp z
        (by fun_prop : DifferentiableAt ℂ (fun w => w + upsShift γ n) z)
      have hp := DifferentiableAt.fun_finsetProd (u := Finset.range n)
        (f := fun j w => upsLFactor γ (w + upsShift γ j)) fun j hj => by
          have hj1 : (j : ℝ) + 1 ≤ n := mod_cast Nat.succ_le_iff.2 (Finset.mem_range.1 hj)
          have harg : (z + upsShift γ j).re < 2 / γ := by
            have h2 := hzn.2
            simp only [Complex.add_re, upsShift_re] at h2 ⊢
            nlinarith
          exact DifferentiableAt.fun_comp' z (diffAt_upsLFactor harg) (by fun_prop)
      exact hb.mul (by simpa only [Finset.prod_apply] using hp)
    · rw [h] at hz
      have hzn : z - upsShift γ n ∈ {w : ℂ | 0 < w.re ∧ w.re < Q γ} := hz
      have hb := (hbase_diff.differentiableAt (hstrip_open.mem_nhds hzn)).comp z
        (by fun_prop : DifferentiableAt ℂ (fun w => w - upsShift γ n) z)
      have hp := DifferentiableAt.fun_finsetProd (u := Finset.range n)
        (f := fun j w => upsRFactor γ (w - upsShift γ (j + 1))) fun j hj => by
          have hj1 : ((j + 1 : ℕ) : ℝ) ≤ n := mod_cast Nat.succ_le_iff.2 (Finset.mem_range.1 hj)
          have harg : 0 < (z - upsShift γ (j + 1)).re := by
            have h1 := hzn.1
            simp only [Complex.sub_re, upsShift_re] at h1 ⊢
            nlinarith
          exact DifferentiableAt.fun_comp' z (diffAt_upsRFactor harg) (by fun_prop)
      exact hb.mul (by simpa only [Finset.prod_apply] using hp)
  · have h0 : z ∈ dom (.inl 0) := by simpa [dom, upsLDom, upsShift] using (⟨hz0, hzQ⟩ : 0 < z.re ∧ z.re < Q γ)
    exact (hchart_eq (hidx z) h0).trans (by simp [chart, upsLChart, upsShift, upsBase])

end DOZZ.Proofs

end
