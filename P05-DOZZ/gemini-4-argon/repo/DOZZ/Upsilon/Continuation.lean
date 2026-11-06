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

The continuation is defined by compatible charts on the translates of the defining strip.
-/

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace DOZZ.Proofs

variable {γ : ℝ}

private def upsilonBase (γ : ℝ) (z : ℂ) : ℂ := Complex.exp (upsilonLog γ z)

private def upsilonStrip (γ : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < Q γ}


private theorem upsilonStrip_isOpen γ : IsOpen (upsilonStrip γ) := by
  change IsOpen ((Complex.re ⁻¹' Set.Ioi (0 : ℝ)) ∩
    (Complex.re ⁻¹' Set.Iio (Q γ)))
  exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (Q γ))

private def upsilonB (γ : ℝ) : ℂ := ((γ / 2 : ℝ) : ℂ)

private def upsilonShiftN (γ : ℝ) (n : ℕ) : ℂ := ((n : ℝ) * (γ / 2) : ℂ)

private def upsilonRightFactor (γ : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (upsilonB γ * z) * (Complex.Gamma (1 - upsilonB γ * z))⁻¹ *
    upsilonB γ ^ (1 - (γ : ℂ) * z)

private def upsilonLeftFactor (γ : ℝ) (z : ℂ) : ℂ :=
  upsilonB γ ^ ((γ : ℂ) * z - 1) * Complex.Gamma (1 - upsilonB γ * z) *
    (Complex.Gamma (upsilonB γ * z))⁻¹

private def upsilonRightChart (γ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  upsilonBase γ (z - upsilonShiftN γ n) *
    ∏ j ∈ Finset.range n,
      upsilonRightFactor γ (z - upsilonShiftN γ (j + 1))

private def upsilonLeftChart (γ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  upsilonBase γ (z + upsilonShiftN γ n) *
    ∏ j ∈ Finset.range n,
      upsilonLeftFactor γ (z + upsilonShiftN γ j)

private def upsilonRightDomain (γ : ℝ) (n : ℕ) : Set ℂ :=
  {z | 0 < (z - upsilonShiftN γ n).re ∧ (z - upsilonShiftN γ n).re < Q γ}

private def upsilonLeftDomain (γ : ℝ) (n : ℕ) : Set ℂ :=
  {z | 0 < (z + upsilonShiftN γ n).re ∧ (z + upsilonShiftN γ n).re < Q γ}

private inductive UpsilonChartIndex where
  | left : ℕ → UpsilonChartIndex
  | right : ℕ → UpsilonChartIndex

private def upsilonChartDomain (γ : ℝ) : UpsilonChartIndex → Set ℂ
  | .left n => upsilonLeftDomain γ n
  | .right n => upsilonRightDomain γ n

private def upsilonChart (γ : ℝ) : UpsilonChartIndex → ℂ → ℂ
  | .left n => upsilonLeftChart γ n
  | .right n => upsilonRightChart γ n

private theorem upsilonShiftN_re γ (n : ℕ) :
    (upsilonShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsilonShiftN]

private theorem upsilonShiftN_succ γ n :
    upsilonShiftN γ (n + 1) = upsilonShiftN γ n + upsilonB γ := by
  simp [upsilonShiftN, upsilonB, Nat.cast_add]
  ring

private theorem upsilonRightArg_re γ (n : ℕ) (z : ℂ) :
    (z - upsilonShiftN γ n).re = z.re - (n : ℝ) * (γ / 2) := by
  simp [Complex.sub_re, upsilonShiftN_re]

private theorem upsilonLeftArg_re γ (n : ℕ) (z : ℂ) :
    (z + upsilonShiftN γ n).re = z.re + (n : ℝ) * (γ / 2) := by
  simp [Complex.add_re, upsilonShiftN_re]

private theorem upsilonShiftN_mono {γ} (hγ : 0 < γ) {m n} (hmn : m ≤ n) :
    (upsilonShiftN γ m).re ≤ (upsilonShiftN γ n).re := by
  rw [upsilonShiftN_re, upsilonShiftN_re]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) (by positivity)

private theorem upsilon_Q_sub_B (γ : ℝ) : Q γ - γ / 2 = 2 / γ := by
  unfold Q
  ring



private theorem upsilonB_ne_zero (hγ : 0 < γ) : upsilonB γ ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact (div_pos hγ (by norm_num)).ne'

private theorem differentiableAt_upsilonRightFactor
    (hγ : 0 < γ) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (upsilonRightFactor γ) z := by
  have hGamma : DifferentiableAt ℂ Complex.Gamma (upsilonB γ * z) :=
    Complex.differentiableAt_Gamma (upsilonB γ * z) (by
      intro n hn
      apply (Complex.Gamma_ne_zero_of_re_pos (by rw [(show (upsilonB γ * z).re = (γ / 2) * z.re by simp [upsilonB, Complex.mul_re])]; exact mul_pos (by positivity) hz))
      rw [hn]
      exact Complex.Gamma_neg_nat_eq_zero n)
  have hpow : DifferentiableAt ℂ
      (fun w => upsilonB γ ^ (1 - (γ : ℂ) * w)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (upsilonB_ne_zero hγ)
  change DifferentiableAt ℂ
    (fun w => Complex.Gamma (upsilonB γ * w) *
      (Complex.Gamma (1 - upsilonB γ * w))⁻¹ *
      upsilonB γ ^ (1 - (γ : ℂ) * w)) z
  exact ((DifferentiableAt.fun_comp' z (f := fun w => upsilonB γ * w) (g := Complex.Gamma) hGamma (by fun_prop)).mul (DifferentiableAt.fun_comp' z (f := fun w => 1 - upsilonB γ * w) (g := fun w => (Complex.Gamma w)⁻¹) Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop))).mul hpow

private theorem differentiableAt_upsilonLeftFactor
    (hγ : 0 < γ) {z : ℂ} (hz : z.re < 2 / γ) :
    DifferentiableAt ℂ (upsilonLeftFactor γ) z := by
  have : (γ / 2) * z.re < 1 := by
    have hmul := mul_lt_mul_of_pos_left hz (show 0 < γ / 2 by positivity)
    rw [(show (γ / 2) * (2 / γ) = 1 by field_simp [hγ.ne'])] at hmul
    exact hmul
  have hGamma : DifferentiableAt ℂ Complex.Gamma (1 - upsilonB γ * z) :=
    Complex.differentiableAt_Gamma (1 - upsilonB γ * z) (by
      intro n hn
      apply (Complex.Gamma_ne_zero_of_re_pos (show 0 < (1 - upsilonB γ * z).re by rw [Complex.sub_re, Complex.one_re, (show (upsilonB γ * z).re = (γ / 2) * z.re by simp [upsilonB, Complex.mul_re])]; linarith))
      rw [hn]
      exact Complex.Gamma_neg_nat_eq_zero n)
  have hpow : DifferentiableAt ℂ
      (fun w => upsilonB γ ^ ((γ : ℂ) * w - 1)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (upsilonB_ne_zero hγ)
  change DifferentiableAt ℂ
    (fun w => upsilonB γ ^ ((γ : ℂ) * w - 1) *
      Complex.Gamma (1 - upsilonB γ * w) *
      (Complex.Gamma (upsilonB γ * w))⁻¹) z
  exact (hpow.mul (DifferentiableAt.fun_comp' z (f := fun w => 1 - upsilonB γ * w) (g := Complex.Gamma) hGamma (by fun_prop))).mul (DifferentiableAt.fun_comp' z (f := fun w => upsilonB γ * w) (g := fun w => (Complex.Gamma w)⁻¹) Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop))



private theorem differentiableAt_upsilonChart
    (hγ : 0 < γ) {i} {z}
    (hbase : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ))
    (hz : z ∈ upsilonChartDomain γ i) :
    DifferentiableAt ℂ (upsilonChart γ i) z := by
  cases i with
  | left n =>
    have hProd : DifferentiableAt ℂ
        (fun w => ∏ j ∈ Finset.range n,
          upsilonLeftFactor γ (w + upsilonShiftN γ j)) z := by
      have hprod := DifferentiableAt.fun_finsetProd
        (u := Finset.range n)
        (f := fun (j : ℕ) (w : ℂ) => upsilonLeftFactor γ (w + upsilonShiftN γ j))
        (by
          intro j hj
          have harg : (z + upsilonShiftN γ j).re < 2 / γ := by
            rw [upsilonLeftArg_re]
            have hzn := hz.2
            rw [upsilonLeftArg_re] at hzn
            linarith only [(show (j : ℝ) * (γ / 2) + γ / 2 ≤ (n : ℝ) * (γ / 2) by linarith only [(mul_le_mul_of_nonneg_right (show (j : ℝ) + 1 ≤ n by exact_mod_cast (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))) (by positivity : 0 ≤ γ / 2))]), hzn, (upsilon_Q_sub_B γ)]
          exact DifferentiableAt.fun_comp' z
            (f := fun w => w + upsilonShiftN γ j)
            (g := upsilonLeftFactor γ) (differentiableAt_upsilonLeftFactor hγ harg) (by fun_prop))
      simpa only [Finset.prod_apply] using hprod
    change DifferentiableAt ℂ
      (fun w => upsilonBase γ (w + upsilonShiftN γ n) *
        ∏ j ∈ Finset.range n,
          upsilonLeftFactor γ (w + upsilonShiftN γ j)) z
    exact (DifferentiableAt.fun_comp' z (f := fun w => w + upsilonShiftN γ n) (g := upsilonBase γ) (hbase.differentiableAt ((upsilonStrip_isOpen γ).mem_nhds hz)) (by fun_prop)).mul hProd
  | right n =>
    have hProd : DifferentiableAt ℂ
        (fun w => ∏ j ∈ Finset.range n,
          upsilonRightFactor γ (w - upsilonShiftN γ (j + 1))) z := by
      have hprod := DifferentiableAt.fun_finsetProd
        (u := Finset.range n)
        (f := fun (j : ℕ) (w : ℂ) =>
          upsilonRightFactor γ (w - upsilonShiftN γ (j + 1)))
        (by
          intro j hj
          change (z - upsilonShiftN γ n).re > 0 ∧
            (z - upsilonShiftN γ n).re < Q γ at hz
          have harg : 0 < (z - upsilonShiftN γ (j + 1)).re := by
            rw [upsilonRightArg_re] at hz
            rw [upsilonRightArg_re]
            exact lt_of_lt_of_le hz.1 (by
              have : ((j + 1 : ℕ) : ℝ) * (γ / 2) ≤
                  (n : ℝ) * (γ / 2) := by
                simpa only [upsilonShiftN_re] using (upsilonShiftN_mono hγ (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)))
              linarith)
          exact DifferentiableAt.fun_comp' z
            (f := fun w => w - upsilonShiftN γ (j + 1))
            (g := upsilonRightFactor γ) (differentiableAt_upsilonRightFactor hγ harg) (by fun_prop))
      simpa only [Finset.prod_apply] using hprod
    change DifferentiableAt ℂ
      (fun w => upsilonBase γ (w - upsilonShiftN γ n) *
        ∏ j ∈ Finset.range n,
          upsilonRightFactor γ (w - upsilonShiftN γ (j + 1))) z
    exact (DifferentiableAt.fun_comp' z (f := fun w => w - upsilonShiftN γ n) (g := upsilonBase γ) (hbase.differentiableAt ((upsilonStrip_isOpen γ).mem_nhds hz)) (by fun_prop)).mul hProd

private theorem upsilonChartDomain_isOpen γ i :
    IsOpen (upsilonChartDomain γ i) := by
  cases i with
  | left n =>
    change IsOpen ((fun z : ℂ => (z + upsilonShiftN γ n).re) ⁻¹' Set.Ioo 0 (Q γ))
    exact isOpen_Ioo.preimage (by fun_prop)
  | right n =>
    change IsOpen ((fun z : ℂ => (z - upsilonShiftN γ n).re) ⁻¹' Set.Ioo 0 (Q γ))
    exact isOpen_Ioo.preimage (by fun_prop)





private theorem upsilonLeftChart_eq_of_overlap_of_le
    (hγ : 0 < γ) {m n} {z}
    (hmn : m ≤ n)
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonLeftDomain γ m) (hn : z ∈ upsilonLeftDomain γ n) :
    upsilonLeftChart γ m z = upsilonLeftChart γ n z := by
  have upsilonLeftDomain_intermediate {m} {k} {n} {z} (hmk : m ≤ k) (hkn : k ≤ n) (hm : z ∈ upsilonLeftDomain γ m) (hn : z ∈ upsilonLeftDomain γ n) : z ∈ upsilonLeftDomain γ k := by
    change 0 < (z + upsilonShiftN γ m).re ∧
      (z + upsilonShiftN γ m).re < Q γ at hm
    change 0 < (z + upsilonShiftN γ n).re ∧
      (z + upsilonShiftN γ n).re < Q γ at hn
    change 0 < (z + upsilonShiftN γ k).re ∧
      (z + upsilonShiftN γ k).re < Q γ
    have : (m : ℝ) * (γ / 2) ≤ (k : ℝ) * (γ / 2) := by
      simpa only [upsilonShiftN_re] using (upsilonShiftN_mono hγ hmk)
    have : (k : ℝ) * (γ / 2) ≤ (n : ℝ) * (γ / 2) := by
      simpa only [upsilonShiftN_re] using (upsilonShiftN_mono hγ hkn)
    rw [upsilonLeftArg_re] at hm hn ⊢
    constructor
    · linarith
    · linarith
  have upsilonLeftChart_succ_eq {n} {z} (hzₙ : z ∈ upsilonLeftDomain γ n) (hzₙ₁ : z ∈ upsilonLeftDomain γ (n + 1)) : upsilonLeftChart γ (n + 1) z = upsilonLeftChart γ n z := by
    have upsilonLeftRecurrence {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) (hshift : upsilonBase γ (z + upsilonB γ) = upsilonRightFactor γ z * upsilonBase γ z) : upsilonLeftFactor γ z * upsilonBase γ (z + upsilonB γ) = upsilonBase γ z := by
      have upsilonLeftRight_cancel : upsilonLeftFactor γ z * upsilonRightFactor γ z = 1 := by
        have hbzre : (upsilonB γ * z).re = (γ / 2) * z.re := by
          simp [upsilonB, Complex.mul_re]
        have hGamma : Complex.Gamma (upsilonB γ * z) ≠ 0 :=
          Complex.Gamma_ne_zero_of_re_pos (by
            rw [hbzre]
            exact mul_pos (by positivity) hz0)
        have : (γ / 2) * z.re < 1 := by
          have hmul := mul_lt_mul_of_pos_left hzQ (by positivity : 0 < γ / 2)
          rw [(show (γ / 2) * (2 / γ) = 1 by field_simp [hγ.ne'])] at hmul
          exact hmul
        have hGamma1 : Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
          Complex.Gamma_ne_zero_of_re_pos (by
            rw [Complex.sub_re, Complex.one_re, hbzre]
            linarith)
        have hGamma' : Complex.Gamma (z * upsilonB γ) ≠ 0 := by
          rw [(mul_comm _ _)]
          exact hGamma
        have hGamma1' : Complex.Gamma (1 - z * upsilonB γ) ≠ 0 := by
          rw [(show 1 - z * upsilonB γ = 1 - upsilonB γ * z by ring)]
          exact hGamma1
        have hpow : upsilonB γ ^ (1 - (γ : ℂ) * z) ≠ 0 :=
          Complex.cpow_ne_zero_iff.mpr (Or.inl (upsilonB_ne_zero hγ))
        change
          (upsilonB γ ^ ((γ : ℂ) * z - 1) *
            Complex.Gamma (1 - upsilonB γ * z) *
            (Complex.Gamma (upsilonB γ * z))⁻¹) *
          (Complex.Gamma (upsilonB γ * z) *
            (Complex.Gamma (1 - upsilonB γ * z))⁻¹ *
            upsilonB γ ^ (1 - (γ : ℂ) * z)) = 1
        rw [show (γ : ℂ) * z - 1 = -(1 - (γ : ℂ) * z) by ring, Complex.cpow_neg]
        field_simp [hGamma', hGamma1', hpow]
      calc
        _ = upsilonLeftFactor γ z * (upsilonRightFactor γ z * upsilonBase γ z) := by
          rw [hshift]
        _ = upsilonBase γ z := by
          rw [← mul_assoc, upsilonLeftRight_cancel, one_mul]
    let v := z + upsilonShiftN γ n
    have hv0 : 0 < v.re := by
      simpa [v, upsilonLeftArg_re] using hzₙ.1
    have htranslate : z + upsilonShiftN γ (n + 1) = v + upsilonB γ := by
      dsimp [v]
      rw [upsilonShiftN_succ]
      ring
    have hvQ : v.re < 2 / γ := by
      have hupper := hzₙ₁.2
      rw [htranslate] at hupper
      rw [Complex.add_re, show (upsilonB γ).re = γ / 2 by simp [upsilonB]] at hupper
      have := upsilon_Q_sub_B γ
      linarith
    unfold upsilonLeftChart
    rw [Finset.prod_range_succ, htranslate]
    change upsilonBase γ (v + upsilonB γ) *
        ((∏ j ∈ Finset.range n, upsilonLeftFactor γ (z + upsilonShiftN γ j)) *
          upsilonLeftFactor γ v) =
      upsilonBase γ v * ∏ j ∈ Finset.range n,
        upsilonLeftFactor γ (z + upsilonShiftN γ j)
    calc
      _ = (upsilonLeftFactor γ v * upsilonBase γ (v + upsilonB γ)) *
          ∏ j ∈ Finset.range n, upsilonLeftFactor γ (z + upsilonShiftN γ j) := by ring
      _ = upsilonBase γ v *
          ∏ j ∈ Finset.range n, upsilonLeftFactor γ (z + upsilonShiftN γ j) := by
        rw [(upsilonLeftRecurrence hv0 hvQ (hshift v hv0 hvQ))]
  have hchain : ∀ k, ∀ m : ℕ, m ≤ k →
        z ∈ upsilonLeftDomain γ m → z ∈ upsilonLeftDomain γ k →
        upsilonLeftChart γ m z = upsilonLeftChart γ k z := by
      intro k
      induction k with
      | zero =>
          intro m hmle hmDom hkDom
          have := Nat.eq_zero_of_le_zero hmle
          subst m
          rfl
      | succ k ih =>
          intro m hmle hmDom hkDom
          by_cases hmk : m = k + 1
          · subst m
            rfl
          · have hmle' : m ≤ k := by omega
            have hDomK := upsilonLeftDomain_intermediate hmle' (Nat.le_succ k)
              hmDom hkDom
            calc
              upsilonLeftChart γ m z = upsilonLeftChart γ k z := ih m hmle' hmDom hDomK
              _ = upsilonLeftChart γ (k + 1) z := (upsilonLeftChart_succ_eq hDomK hkDom).symm
  exact hchain n m hmn hm hn

private theorem upsilonLeftChart_eq_of_overlap
    (hγ : 0 < γ) {m n} {z}
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonLeftDomain γ m) (hn : z ∈ upsilonLeftDomain γ n) :
    upsilonLeftChart γ m z = upsilonLeftChart γ n z := by
  rcases le_total m n with hmn | hnm
  · exact upsilonLeftChart_eq_of_overlap_of_le hγ hmn hshift hm hn
  · exact (upsilonLeftChart_eq_of_overlap_of_le hγ hnm hshift hn hm).symm

private theorem upsilonRightChart_eq_of_overlap_of_le
    (hγ : 0 < γ) {m n} {z}
    (hmn : m ≤ n)
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonRightDomain γ m) (hn : z ∈ upsilonRightDomain γ n) :
    upsilonRightChart γ m z = upsilonRightChart γ n z := by
  have upsilonRightDomain_intermediate {m} {k} {n} {z} (hmk : m ≤ k) (hkn : k ≤ n) (hm : z ∈ upsilonRightDomain γ m) (hn : z ∈ upsilonRightDomain γ n) : z ∈ upsilonRightDomain γ k := by
    change 0 < (z - upsilonShiftN γ m).re ∧
      (z - upsilonShiftN γ m).re < Q γ at hm
    change 0 < (z - upsilonShiftN γ n).re ∧
      (z - upsilonShiftN γ n).re < Q γ at hn
    change 0 < (z - upsilonShiftN γ k).re ∧
      (z - upsilonShiftN γ k).re < Q γ
    have : (m : ℝ) * (γ / 2) ≤ (k : ℝ) * (γ / 2) := by
      simpa only [upsilonShiftN_re] using (upsilonShiftN_mono hγ hmk)
    have : (k : ℝ) * (γ / 2) ≤ (n : ℝ) * (γ / 2) := by
      simpa only [upsilonShiftN_re] using (upsilonShiftN_mono hγ hkn)
    rw [upsilonRightArg_re] at hm hn ⊢
    constructor
    · linarith
    · linarith
  have upsilonRightChart_succ_eq {n} {z} (hzₙ : z ∈ upsilonRightDomain γ n) (hzₙ₁ : z ∈ upsilonRightDomain γ (n + 1)) : upsilonRightChart γ (n + 1) z = upsilonRightChart γ n z := by
    let v := z - upsilonShiftN γ (n + 1)
    have htranslate : z - upsilonShiftN γ n = v + upsilonB γ := by
      dsimp [v]
      rw [upsilonShiftN_succ]
      ring
    have hvQ : v.re < 2 / γ := by
      have hupper := hzₙ.2
      rw [htranslate] at hupper
      rw [Complex.add_re, show (upsilonB γ).re = γ / 2 by simp [upsilonB]] at hupper
      have := upsilon_Q_sub_B γ
      linarith
    unfold upsilonRightChart
    rw [Finset.prod_range_succ, htranslate]
    change upsilonBase γ v *
        ((∏ j ∈ Finset.range n,
          upsilonRightFactor γ (z - upsilonShiftN γ (j + 1))) *
          upsilonRightFactor γ v) =
      upsilonBase γ (v + upsilonB γ) * ∏ j ∈ Finset.range n,
        upsilonRightFactor γ (z - upsilonShiftN γ (j + 1))
    calc
      _ = (upsilonRightFactor γ v * upsilonBase γ v) *
          ∏ j ∈ Finset.range n,
            upsilonRightFactor γ (z - upsilonShiftN γ (j + 1)) := by ring
      _ = upsilonBase γ (v + upsilonB γ) *
          ∏ j ∈ Finset.range n,
            upsilonRightFactor γ (z - upsilonShiftN γ (j + 1)) := by
        rw [← (hshift v (by simpa [v, upsilonRightArg_re] using hzₙ₁.1) hvQ)]
  have hchain : ∀ k, ∀ m : ℕ, m ≤ k →
        z ∈ upsilonRightDomain γ m → z ∈ upsilonRightDomain γ k →
        upsilonRightChart γ m z = upsilonRightChart γ k z := by
      intro k
      induction k with
      | zero =>
          intro m hmle hmDom hkDom
          have := Nat.eq_zero_of_le_zero hmle
          subst m
          rfl
      | succ k ih =>
          intro m hmle hmDom hkDom
          by_cases hmk : m = k + 1
          · subst m
            rfl
          · have hmle' : m ≤ k := by omega
            have hDomK := upsilonRightDomain_intermediate hmle' (Nat.le_succ k)
              hmDom hkDom
            calc
              upsilonRightChart γ m z = upsilonRightChart γ k z := ih m hmle' hmDom hDomK
              _ = upsilonRightChart γ (k + 1) z := (upsilonRightChart_succ_eq hDomK hkDom).symm
  exact hchain n m hmn hm hn

private theorem upsilonRightChart_eq_of_overlap
    (hγ : 0 < γ) {m n} {z}
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonRightDomain γ m) (hn : z ∈ upsilonRightDomain γ n) :
    upsilonRightChart γ m z = upsilonRightChart γ n z := by
  rcases le_total m n with hmn | hnm
  · exact upsilonRightChart_eq_of_overlap_of_le hγ hmn hshift hm hn
  · exact (upsilonRightChart_eq_of_overlap_of_le hγ hnm hshift hn hm).symm



private theorem exists_upsilonChartDomain
    {γ}
    (hγ : 0 < γ) (hγ2 : γ < 2) z :
    ∃ i : UpsilonChartIndex, z ∈ upsilonChartDomain γ i := by
  have upsilon_Q_gt_twoB : γ < Q γ := by
    unfold Q
    have : γ / 2 < 2 / γ := by
      rw [lt_div_iff₀ hγ]
      linarith only [(show γ ^ 2 < 4 by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le])]
    linarith
  have upsilon_Q_gt_B : γ / 2 < Q γ := by
    unfold Q
    have : 0 < 2 / γ := by positivity
    linarith
  have hb : 0 < γ / 2 := by positivity
  have hQb := upsilon_Q_gt_B
  by_cases hzpos : 0 < z.re
  · let y : ℝ := z.re / (γ / 2)
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    by_cases hylt : y < 1
    · refine ⟨.right 0, ?_⟩
      change 0 < (z - upsilonShiftN γ 0).re ∧
        (z - upsilonShiftN γ 0).re < Q γ
      rw [upsilonRightArg_re]
      constructor
      · simpa using hzpos
      · have hylt' : z.re / (γ / 2) < 1 := by simpa only [y] using hylt
        simpa using (show z.re < γ / 2 by simpa using (div_lt_iff₀ hb).mp hylt').trans hQb
    · let N : ℕ := Nat.floor y
      let n := N - 1
      have := Nat.floor_le hy0
      have hxy : z.re = y * (γ / 2) := by
        dsimp [y]
        field_simp [ne_of_gt hb]
      have : ((N : ℝ) - 1) * (γ / 2) < z.re := by
        simpa [hxy] using (mul_lt_mul_of_pos_right (show (N : ℝ) - 1 < y by linarith) hb)
      refine ⟨.right n, ?_⟩
      change 0 < (z - upsilonShiftN γ n).re ∧
        (z - upsilonShiftN γ n).re < Q γ
      rw [upsilonRightArg_re, (show (n : ℝ) = (N : ℝ) - 1 by simp [n, Nat.cast_sub (show 1 ≤ N by by_contra hnot; exact (not_lt_of_ge (le_of_not_gt hylt)) (by simpa using (Nat.floor_lt hy0).mp (show Nat.floor y < 1 by simpa only [N] using (Nat.lt_of_not_ge hnot))))])]
      constructor
      · linarith
      · have hQ2 : 2 * (γ / 2) < Q γ := by
          linarith only [upsilon_Q_gt_twoB]
        linarith only [(show z.re < ((N : ℝ) + 1) * (γ / 2) by simpa [hxy] using (mul_lt_mul_of_pos_right (Nat.lt_floor_add_one y) hb)), hQ2]
  · have hzle : z.re ≤ 0 := le_of_not_gt hzpos
    let y : ℝ := -z.re / (γ / 2)
    let N : ℕ := Nat.floor y
    let n : ℕ := N + 1
    have : (N : ℝ) ≤ y := Nat.floor_le (by dsimp [y]; exact div_nonneg (neg_nonneg.mpr hzle) hb.le)
    have hncast : (n : ℝ) = (N : ℝ) + 1 := by simp [n]
    have hxy : z.re = -(y * (γ / 2)) := by
      dsimp [y]
      field_simp [ne_of_gt hb]
    refine ⟨.left n, ?_⟩
    change 0 < (z + upsilonShiftN γ n).re ∧
      (z + upsilonShiftN γ n).re < Q γ
    rw [upsilonLeftArg_re, hncast]
    constructor
    · linarith [(by simpa [hncast] using (show -z.re < (n : ℝ) * (γ / 2) by rw [hxy, hncast]; linarith only [(mul_lt_mul_of_pos_right (Nat.lt_floor_add_one y) hb)]))]
    · linarith only [(by simpa [hncast] using (show (n : ℝ) * (γ / 2) ≤ y * (γ / 2) + γ / 2 by rw [hncast]; linarith only [(mul_le_mul_of_nonneg_right (show (N : ℝ) + 1 ≤ y + 1 by linarith) (le_of_lt hb))])), hxy, hQb]

private noncomputable def upsilonIndexAt
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) : UpsilonChartIndex :=
  Classical.choose (exists_upsilonChartDomain (γ := γ) hγ hγ2 z)

private theorem upsilonIndexAt_mem
    {γ}
    (hγ : 0 < γ) (hγ2 : γ < 2) z :
    z ∈ upsilonChartDomain γ (upsilonIndexAt hγ hγ2 z) :=
  Classical.choose_spec (exists_upsilonChartDomain (γ := γ) hγ hγ2 z)

private noncomputable def upsilonContinuationFunction
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) : ℂ :=
  upsilonChart γ (upsilonIndexAt (γ := γ) hγ hγ2 z) z

private theorem upsilonContinuation_eq_chart_of_mem
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    {z} {i} (hi : z ∈ upsilonChartDomain γ i) :
    upsilonContinuationFunction (γ := γ) hγ hγ2 z = upsilonChart γ i z := by
  have upsilonLeftRightChart_eq_of_mem {z} {m} {n} (hi : z ∈ upsilonLeftDomain γ m) (hj : z ∈ upsilonRightDomain γ n) : upsilonLeftChart γ m z = upsilonRightChart γ n z := by
    have hz0 : 0 < z.re := by
      change 0 < (z - upsilonShiftN γ n).re ∧ _ at hj
      rw [upsilonRightArg_re] at hj
      have : 0 ≤ (n : ℝ) * (γ / 2) := by positivity
      linarith
    have hzQ : z.re < Q γ := by
      change 0 < (z + upsilonShiftN γ m).re ∧
        (z + upsilonShiftN γ m).re < Q γ at hi
      rw [upsilonLeftArg_re] at hi
      have : 0 ≤ (m : ℝ) * (γ / 2) := by positivity
      linarith
    have hbase : z ∈ upsilonStrip γ := ⟨hz0, hzQ⟩
    calc
      upsilonLeftChart γ m z = upsilonLeftChart γ 0 z := (upsilonLeftChart_eq_of_overlap hγ hshift hi (show z ∈ upsilonLeftDomain γ 0 by simpa [upsilonLeftDomain, upsilonShiftN, upsilonStrip] using hbase))
      _ = upsilonBase γ z := by simp [upsilonLeftChart, upsilonShiftN, upsilonBase]
      _ = upsilonRightChart γ 0 z := by simp [upsilonRightChart, upsilonShiftN, upsilonBase]
      _ = upsilonRightChart γ n z := (upsilonRightChart_eq_of_overlap hγ hshift (show z ∈ upsilonRightDomain γ 0 by simpa [upsilonRightDomain, upsilonShiftN, upsilonStrip] using hbase) hj)
  have upsilonChart_eq_of_mem {z} {i} {j} (hi : z ∈ upsilonChartDomain γ i) (hj : z ∈ upsilonChartDomain γ j) : upsilonChart γ i z = upsilonChart γ j z := by
    cases i with
    | left m =>
      cases j with
      | left n =>
        exact upsilonLeftChart_eq_of_overlap hγ hshift hi hj
      | right n =>
        exact upsilonLeftRightChart_eq_of_mem hi hj
    | right m =>
      cases j with
      | left n =>
        change z ∈ upsilonRightDomain γ m at hi
        change z ∈ upsilonLeftDomain γ n at hj
        exact (upsilonLeftRightChart_eq_of_mem hj hi).symm
      | right n =>
        exact upsilonRightChart_eq_of_overlap hγ hshift hi hj
  exact upsilonChart_eq_of_mem
    (upsilonIndexAt_mem (γ := γ) hγ hγ2 z) hi

private theorem upsilonContinuation_differentiableAt
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hbase : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ))
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    z :
    DifferentiableAt ℂ (upsilonContinuationFunction (γ := γ) hγ hγ2) z := by
  have hi := upsilonIndexAt_mem (γ := γ) hγ hγ2 z
  exact (differentiableAt_upsilonChart hγ hbase hi).congr_of_eventuallyEq (by filter_upwards [(upsilonChartDomain_isOpen γ (upsilonIndexAt (γ := γ) hγ hγ2 z)).mem_nhds hi] with w hw; exact upsilonContinuation_eq_chart_of_mem (γ := γ) hγ hγ2 hshift hw)

private theorem exists_IsUpsilon_of_strip_data
    {γ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hbase : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ))
    (hshift : ∀ z : ℂ, 0 < z.re → z.re < 2 / γ →
      upsilonBase γ (z + upsilonB γ) =
        upsilonRightFactor γ z * upsilonBase γ z) :
    ∃ U : ℂ → ℂ, IsUpsilon γ U := by
  let U := upsilonContinuationFunction (γ := γ) hγ hγ2
  refine ⟨U, (by intro z; change DifferentiableAt ℂ (upsilonContinuationFunction (γ := γ) hγ hγ2) z; exact upsilonContinuation_differentiableAt hγ hγ2 hbase hshift z), ?_⟩
  intro z hz0 hzQ
  calc
    U z = upsilonContinuationFunction (γ := γ) hγ hγ2 z := rfl
    _ = upsilonChart γ (.left 0) z :=
      upsilonContinuation_eq_chart_of_mem (γ := γ) hγ hγ2 hshift (show z ∈ upsilonLeftDomain γ 0 by simpa [upsilonLeftDomain, upsilonShiftN, upsilonStrip] using ⟨hz0, hzQ⟩)
    _ = Complex.exp (upsilonLog γ z) := by
      simp [upsilonChart, upsilonLeftChart, upsilonShiftN, upsilonBase]

/-- Existence of an entire Upsilon function from the defining strip integral and its first shift.
The continuation charts use the reciprocal-Gamma multiplier on the left half-plane. -/
theorem exists_IsUpsilon (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ U : ℂ → ℂ, IsUpsilon γ U := by
  have differentiableOn_upsilonBase_of_log {γ} (hLog : DifferentiableOn ℂ (fun z => upsilonLog γ z) (upsilonStrip γ)) : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ) := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w => Complex.exp (upsilonLog γ w))
      (upsilonStrip γ) z
    exact differentiable_exp.differentiableAt.comp_differentiableWithinAt z (hLog z hz)
  apply exists_IsUpsilon_of_strip_data hγ hγ2
  · exact differentiableOn_upsilonBase_of_log (upsilonLog_differentiableOn hγ hγ2)
  · intro z hz0 hzQ
    simpa [upsilonBase, upsilonB, upsilonRightFactor, lFun,
      div_eq_mul_inv, mul_assoc] using (exp_upsilonLog_shift_b hγ hγ2 hz0 hzQ)

end DOZZ.Proofs

end
