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

private theorem differentiableOn_upsilonBase_of_log
    {γ : ℝ}
    (hLog : DifferentiableOn ℂ (fun z => upsilonLog γ z) (upsilonStrip γ)) :
    DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ) := by
  intro z hz
  change DifferentiableWithinAt ℂ (fun w => Complex.exp _)
    (upsilonStrip γ) z
  exact differentiable_exp.differentiableAt.comp_differentiableWithinAt z (hLog z hz)

private theorem upsilonStrip_isOpen (γ : ℝ) : IsOpen (upsilonStrip γ) := by
  change IsOpen ((Complex.re ⁻¹' Set.Ioi 0) ∩
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
section
variable (γ : ℝ) (n : ℕ)

private theorem upsilonShiftN_re :
    (upsilonShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsilonShiftN]

private theorem upsilonShiftN_succ :
    upsilonShiftN γ (n + 1) = upsilonShiftN γ n + upsilonB γ := by
  simp [upsilonShiftN, upsilonB, Nat.cast_add]
  ring
section
variable (z : ℂ)

private theorem upsilonRightArg_re :
    (z - upsilonShiftN γ n).re = z.re - (n : ℝ) * (γ / 2) := by
  simp [Complex.sub_re, upsilonShiftN_re]

private theorem upsilonLeftArg_re :
    (z + upsilonShiftN γ n).re = z.re + (n : ℝ) * (γ / 2) := by
  simp [Complex.add_re, upsilonShiftN_re]

end

end

private theorem upsilonShiftN_mono {γ : ℝ} (hγ : 0 < γ) {m n : ℕ} (hmn : m ≤ n) :
    (upsilonShiftN γ m).re ≤ (upsilonShiftN γ n).re := by
  rw [upsilonShiftN_re, upsilonShiftN_re]
  simp_all

private theorem upsilon_Q_sub_B (γ : ℝ) : Q γ - γ / 2 = 2 / γ := by
  unfold Q
  ring
section
variable (hγ : 0 < γ)
include hγ

private theorem upsilon_Q_gt_B : γ / 2 < Q γ := by
  unfold Q
  simp_all

private theorem upsilon_Q_gt_twoB (hγ2 : γ < 2) :
    γ < Q γ := by
  unfold Q
  have hsq : γ ^ 2 < 4 := by
    nlinarith
  have hb : γ / 2 < 2 / γ := by
    gcongr
  linarith

private theorem upsilonB_ne_zero : upsilonB γ ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  positivity
section
variable {z : ℂ}

private theorem differentiableAt_upsilonRightFactor
    (hz : 0 < z.re) :
    DifferentiableAt ℂ (upsilonRightFactor γ) z := by
  have hbR : 0 < γ / 2 := by positivity
  have hbzre : (upsilonB γ * z).re = (γ / 2) * z.re := by
    simp [upsilonB, Complex.mul_re]
  have hArgRe : 0 < (upsilonB γ * z).re := by
    simp_all
  have hlin : DifferentiableAt ℂ (fun w => upsilonB γ * w) z := by fun_prop
  have hOneMinus : DifferentiableAt ℂ
      (fun w => 1 - upsilonB γ * w) z := by fun_prop
  have hGamma :=
    Complex.differentiableAt_Gamma (upsilonB γ * z) (by
      intro n hn
      apply (Complex.Gamma_ne_zero_of_re_pos hArgRe)
      grind)
  have hGammaComp :=
    DifferentiableAt.fun_comp' z
      hGamma hlin
  have hInvGammaComp : DifferentiableAt ℂ
      (fun w => (Complex.Gamma (1 - upsilonB γ * w))⁻¹) z := DifferentiableAt.fun_comp' z
      (g := fun w : ℂ => (Complex.Gamma w)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hOneMinus
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => upsilonB γ ^ (1 - γ * w)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (upsilonB_ne_zero hγ)
  change DifferentiableAt ℂ
    (fun w => Complex.Gamma _ *
      (Complex.Gamma (1 - upsilonB γ * w))⁻¹ *
      upsilonB γ ^ (1 - γ * w)) z
  simp_all

private theorem differentiableAt_upsilonLeftFactor
    (hz : z.re < 2 / γ) :
    DifferentiableAt ℂ (upsilonLeftFactor γ) z := by
  have hbR : 0 < γ / 2 := by positivity
  have hbzre : (upsilonB γ * z).re = (γ / 2) * z.re := by
    simp [upsilonB, Complex.mul_re]
  have hscale : (γ / 2) * z.re < 1 := by
    have hmul := mul_lt_mul_of_pos_left hz hbR
    grind
  have hArgRe : 0 < (1 - upsilonB γ * z).re := by
    simp_all
  have hlin : DifferentiableAt ℂ (fun w => upsilonB γ * w) z := by fun_prop
  have hOneMinus : DifferentiableAt ℂ
      (fun w => 1 - upsilonB γ * w) z := by fun_prop
  have hGamma : DifferentiableAt ℂ Complex.Gamma (1 - upsilonB γ * z) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      apply (Complex.Gamma_ne_zero_of_re_pos hArgRe)
      grind)
  have hGammaComp : DifferentiableAt ℂ
      (fun w => Complex.Gamma (1 - upsilonB γ * w)) z :=
    by fun_prop
  have hInvGammaComp : DifferentiableAt ℂ
      (fun w => (Complex.Gamma (upsilonB γ * w))⁻¹) z := by
    exact DifferentiableAt.fun_comp' z
      (g := fun w : ℂ => (Complex.Gamma w)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hlin
  have hpow : DifferentiableAt ℂ
      (fun w => upsilonB γ ^ ((γ : ℂ) * w - 1)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (upsilonB_ne_zero hγ)
  change DifferentiableAt ℂ
    (fun w => upsilonB γ ^ ((γ : ℂ) * w - 1) *
      Complex.Gamma _ *
      (Complex.Gamma _)⁻¹) z
  exact (hpow.mul hGammaComp).mul hInvGammaComp

end

end
section
variable (hγ : 0 < γ) {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ)
include hγ hz0 hzQ

private theorem upsilonLeftRight_cancel
    :
    upsilonLeftFactor γ z * upsilonRightFactor γ z = 1 := by
  have hb : upsilonB γ ≠ 0 := upsilonB_ne_zero hγ
  have hbzre : (upsilonB γ * z).re = (γ / 2) * z.re := by
    simp [upsilonB, Complex.mul_re]
  have hGamma : Complex.Gamma (upsilonB γ * z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp_all)
  have hscale : (γ / 2) * z.re < 1 := by
    have hmul := mul_lt_mul_of_pos_left hzQ (by positivity : 0 < γ / 2)
    grind
  have hGamma1 : Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp_all)
  have hGamma' : Complex.Gamma (z * upsilonB γ) ≠ 0 := by
    grind
  have hGamma1' : Complex.Gamma (1 - z * upsilonB γ) ≠ 0 := by
    grind
  have hpow : upsilonB γ ^ (1 - (γ : ℂ) * z) ≠ 0 :=
    by simp_all
  change
    (upsilonB γ ^ ((γ : ℂ) * z - 1) *
      Complex.Gamma _ *
      (Complex.Gamma _)⁻¹) *
    (Complex.Gamma _ *
      (Complex.Gamma _)⁻¹ *
      upsilonB γ ^ (1 - (γ : ℂ) * z)) = 1
  rw [show (γ : ℂ) * z - 1 = -(1 - (γ : ℂ) * z) by ring, Complex.cpow_neg]
  field_simp

private theorem upsilonLeftRecurrence
    (hshift : upsilonBase γ (z + upsilonB γ) =
      upsilonRightFactor γ z * upsilonBase γ z) :
    upsilonLeftFactor γ z * upsilonBase γ (z + upsilonB γ) = upsilonBase γ z := by
  calc
    _ = upsilonLeftFactor γ z * (upsilonRightFactor γ z * upsilonBase γ z) := by
      simp_all
    _ = upsilonBase γ z := by
      rw [← mul_assoc, upsilonLeftRight_cancel hγ hz0 hzQ, one_mul]

end

private theorem differentiableAt_upsilonChart
    (hγ : 0 < γ) {i : UpsilonChartIndex} {z : ℂ}
    (hbase : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ))
    (hz : z ∈ upsilonChartDomain γ i) :
    DifferentiableAt ℂ (upsilonChart γ i) z := by
  cases i with
  | left n =>
    have hBaseArg : z + upsilonShiftN γ n ∈ upsilonStrip γ := hz
    have hBaseAt :=
      hbase.differentiableAt ((upsilonStrip_isOpen γ).mem_nhds hBaseArg)
    have hShiftDiff : DifferentiableAt ℂ
        (fun w => w + upsilonShiftN γ n) z := by fun_prop
    have hBaseComp : DifferentiableAt ℂ
        (fun w => upsilonBase γ _) z :=
      DifferentiableAt.fun_comp' z
        (g := upsilonBase γ) hBaseAt hShiftDiff
    have hProd : DifferentiableAt ℂ
        (fun w => ∏ j ∈ Finset.range n,
          upsilonLeftFactor γ (w + upsilonShiftN γ j)) z := by
      exact DifferentiableAt.fun_finsetProd
       
       
        (by
          intro j hj
          have hjcast : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
          have hshift : (j : ℝ) * (γ / 2) + γ / 2 ≤ (n : ℝ) * (γ / 2) := by
            nlinarith
          have harg : (z + upsilonShiftN γ j).re < 2 / γ := by
            rw [upsilonLeftArg_re]
            have hzn := hz.2
            rw [upsilonLeftArg_re] at hzn
            have hQ := upsilon_Q_sub_B γ
            linarith
          have hArgDiff := differentiableAt_upsilonLeftFactor hγ harg
          fun_prop)
    change DifferentiableAt ℂ
      (fun w => upsilonBase γ _ *
        ∏ j ∈ Finset.range n,
          upsilonLeftFactor γ _) z
    exact hBaseComp.mul hProd
  | right n =>
    have hBaseAt : DifferentiableAt ℂ (upsilonBase γ)
        (z - upsilonShiftN γ n) :=
      hbase.differentiableAt ((upsilonStrip_isOpen γ).mem_nhds hz)
    have hShiftDiff : DifferentiableAt ℂ
        (fun w => w - upsilonShiftN γ n) z := by fun_prop
    have hBaseComp : DifferentiableAt ℂ
        (fun w => upsilonBase γ (w - upsilonShiftN γ n)) z :=
      DifferentiableAt.fun_comp' z
        hBaseAt hShiftDiff
    have hProd : DifferentiableAt ℂ
        (fun w => ∏ j ∈ Finset.range n,
          upsilonRightFactor γ (w - upsilonShiftN γ (j + 1))) z := by
      have hprod := DifferentiableAt.fun_finsetProd
       
        (f := fun (j : ℕ) (w : ℂ) =>
          upsilonRightFactor γ (w - upsilonShiftN γ (j + 1)))
        (by
          intro j hj
          have hjn' : j + 1 ≤ n := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
          have hshift : (upsilonShiftN γ (j + 1)).re ≤
              (upsilonShiftN γ n).re := upsilonShiftN_mono hγ hjn'
          change (z - upsilonShiftN γ n).re > 0 ∧
            (z - upsilonShiftN γ n).re < Q γ at hz
          have harg : 0 < (z - upsilonShiftN γ (j + 1)).re := by
            rw [upsilonRightArg_re] at hz
            rw [upsilonRightArg_re]
            exact lt_of_lt_of_le hz.1 (by
              have hshift' : ((j + 1 : ℕ) : ℝ) * (γ / 2) ≤
                  (n : ℝ) * (γ / 2) := by
                simpa only [upsilonShiftN_re] using hshift
              linarith)
          have hlin : DifferentiableAt ℂ
              (fun w => w - upsilonShiftN γ (j + 1)) z := by fun_prop
          exact DifferentiableAt.fun_comp' z
           
            (differentiableAt_upsilonRightFactor hγ harg) hlin)
      simpa using hprod
    change DifferentiableAt ℂ
      (fun w => upsilonBase γ _ *
        ∏ j ∈ Finset.range n,
          upsilonRightFactor γ _) z
    exact hBaseComp.mul hProd

private theorem upsilonChartDomain_isOpen (γ : ℝ) (i : UpsilonChartIndex) :
    IsOpen (upsilonChartDomain γ i) := by
  cases i with
  | left n =>
    exact isOpen_Ioo.preimage (by fun_prop)
  | right n =>
    exact isOpen_Ioo.preimage (by fun_prop)

private theorem upsilonLeftChart_succ_eq
    (hγ : 0 < γ) {n : ℕ} {z : ℂ}
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hzₙ : z ∈ upsilonLeftDomain γ n)
    (hzₙ₁ : z ∈ upsilonLeftDomain γ (n + 1)) :
    upsilonLeftChart γ (n + 1) z = upsilonLeftChart γ n z := by
  let v := z + upsilonShiftN γ n
  have hv0 : 0 < v.re := by
    simpa [v, upsilonLeftArg_re] using hzₙ.1
  have htranslate : z + upsilonShiftN γ (n + 1) = v + upsilonB γ := by
    dsimp [v]
    rw [upsilonShiftN_succ]
    ring
  have hvQ : v.re < 2 / γ := by
    have hupper := hzₙ₁.2
    rw [htranslate, Complex.add_re, show (upsilonB γ).re = γ / 2 by rfl] at hupper
    have hQ := upsilon_Q_sub_B γ
    linarith
  have hrec := upsilonLeftRecurrence hγ hv0 hvQ (hshift v hv0 hvQ)
  unfold upsilonLeftChart
  rw [Finset.prod_range_succ, htranslate]
  grind

private theorem upsilonRightChart_succ_eq
    {n : ℕ} {z : ℂ}
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hzₙ : z ∈ upsilonRightDomain γ n)
    (hzₙ₁ : z ∈ upsilonRightDomain γ (n + 1)) :
    upsilonRightChart γ (n + 1) z = upsilonRightChart γ n z := by
  let v := z - upsilonShiftN γ (n + 1)
  have hv0 : 0 < v.re := by
    simpa [v, upsilonRightArg_re] using hzₙ₁.1
  have htranslate : z - upsilonShiftN γ n = v + upsilonB γ := by
    dsimp [v]
    rw [upsilonShiftN_succ]
    ring
  have hvQ : v.re < 2 / γ := by
    have hupper := hzₙ.2
    rw [htranslate, Complex.add_re, show (upsilonB γ).re = γ / 2 by rfl] at hupper
    have hQ := upsilon_Q_sub_B γ
    linarith
  have hstripShift := hshift v hv0 hvQ
  unfold upsilonRightChart
  rw [Finset.prod_range_succ, htranslate]
  grind
section
variable (hγ : 0 < γ) {m k n : ℕ} {z : ℂ} (hmk : m ≤ k) (hkn : k ≤ n)
include hγ hmk hkn

private theorem upsilonLeftDomain_intermediate
    (hm : z ∈ upsilonLeftDomain γ m) (hn : z ∈ upsilonLeftDomain γ n) :
    z ∈ upsilonLeftDomain γ k := by
  change 0 < (z + upsilonShiftN γ m).re ∧
    (z + upsilonShiftN γ m).re < Q γ at hm
  change 0 < (z + upsilonShiftN γ n).re ∧
    (z + upsilonShiftN γ n).re < Q γ at hn
  change 0 < (z + upsilonShiftN γ k).re ∧
    (z + upsilonShiftN γ k).re < Q γ
  have hmk' := upsilonShiftN_mono hγ hmk
  have hkn' := upsilonShiftN_mono hγ hkn
  have hmkR : m * (γ / 2) ≤ k * (γ / 2) := by
    simp_all
  have hknR : k * (γ / 2) ≤ n * (γ / 2) := by
    simp_all
  rw [upsilonLeftArg_re] at hm hn ⊢
  grind

private theorem upsilonRightDomain_intermediate
    (hm : z ∈ upsilonRightDomain γ m) (hn : z ∈ upsilonRightDomain γ n) :
    z ∈ upsilonRightDomain γ k := by
  change 0 < (z - upsilonShiftN γ m).re ∧
    (z - upsilonShiftN γ m).re < Q γ at hm
  change 0 < (z - upsilonShiftN γ n).re ∧
    (z - upsilonShiftN γ n).re < Q γ at hn
  change 0 < (z - upsilonShiftN γ k).re ∧
    (z - upsilonShiftN γ k).re < Q γ
  have hmk' := upsilonShiftN_mono hγ hmk
  have hkn' := upsilonShiftN_mono hγ hkn
  have hmkR : m * (γ / 2) ≤ k * (γ / 2) := by
    simp_all
  have hknR : k * (γ / 2) ≤ n * (γ / 2) := by
    simp_all
  rw [upsilonRightArg_re] at hm hn ⊢
  grind

end
section
variable (hγ : 0 < γ) {m n : ℕ} {z : ℂ}
include hγ

private theorem upsilonLeftChart_eq_of_overlap_of_le
    (hmn : m ≤ n)
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonLeftDomain γ m) (hn : z ∈ upsilonLeftDomain γ n) :
    upsilonLeftChart γ m z = upsilonLeftChart γ n z := by
  have hchain : ∀ k, ∀ m : ℕ, m ≤ k →
        z ∈ upsilonLeftDomain γ m → z ∈ upsilonLeftDomain γ k →
        upsilonLeftChart γ m z = upsilonLeftChart γ k z := by
      intro k
      induction k with
      | zero =>
          intro m hmle hmDom hkDom
          have : m = 0 := Nat.eq_zero_of_le_zero hmle
          subst m
          rfl
      | succ k ih =>
          intro m hmle hmDom hkDom
          by_cases hmk : m = k + 1
          · simp_all
          · have hmle' : m ≤ k := by omega
            have hDomK := upsilonLeftDomain_intermediate hγ hmle' (Nat.le_succ k)
              hmDom hkDom
            calc
              upsilonLeftChart γ m z = upsilonLeftChart γ k z := ih m hmle' hmDom hDomK
              _ = upsilonLeftChart γ _ z := (upsilonLeftChart_succ_eq hγ hshift hDomK hkDom).symm
  tauto

private theorem upsilonLeftChart_eq_of_overlap
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonLeftDomain γ m) (hn : z ∈ upsilonLeftDomain γ n) :
    upsilonLeftChart γ m z = upsilonLeftChart γ n z := by
  rcases le_total m n with hmn | hnm
  · exact upsilonLeftChart_eq_of_overlap_of_le hγ hmn hshift hm hn
  · exact (upsilonLeftChart_eq_of_overlap_of_le hγ hnm hshift hn hm).symm

private theorem upsilonRightChart_eq_of_overlap_of_le
    (hmn : m ≤ n)
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonRightDomain γ m) (hn : z ∈ upsilonRightDomain γ n) :
    upsilonRightChart γ m z = upsilonRightChart γ n z := by
  have hchain : ∀ k, ∀ m : ℕ, m ≤ k →
        z ∈ upsilonRightDomain γ m → z ∈ upsilonRightDomain γ k →
        upsilonRightChart γ m z = upsilonRightChart γ k z := by
      intro k
      induction k with
      | zero =>
          intro m hmle hmDom hkDom
          have : m = 0 := Nat.eq_zero_of_le_zero hmle
          subst m
          rfl
      | succ k ih =>
          intro m hmle hmDom hkDom
          by_cases hmk : m = k + 1
          · simp_all
          · have hmle' : m ≤ k := by omega
            have hDomK := upsilonRightDomain_intermediate hγ hmle' (Nat.le_succ k)
              hmDom hkDom
            calc
              upsilonRightChart γ m z = upsilonRightChart γ k z := ih m hmle' hmDom hDomK
              _ = upsilonRightChart γ _ z := (upsilonRightChart_succ_eq hshift hDomK hkDom).symm
  tauto

private theorem upsilonRightChart_eq_of_overlap
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hm : z ∈ upsilonRightDomain γ m) (hn : z ∈ upsilonRightDomain γ n) :
    upsilonRightChart γ m z = upsilonRightChart γ n z := by
  rcases le_total m n with hmn | hnm
  · exact upsilonRightChart_eq_of_overlap_of_le hγ hmn hshift hm hn
  · exact (upsilonRightChart_eq_of_overlap_of_le hγ hnm hshift hn hm).symm

end
section
variable (hγ : 0 < γ) {z : ℂ}
include hγ

private theorem upsilonLeftRightChart_eq_of_mem
    {m n : ℕ}
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hi : z ∈ upsilonLeftDomain γ m) (hj : z ∈ upsilonRightDomain γ n) :
    upsilonLeftChart γ m z = upsilonRightChart γ n z := by
  have hz0 : 0 < z.re := by
    change 0 < (z - upsilonShiftN γ n).re ∧ _ at hj
    rw [upsilonRightArg_re] at hj
    nlinarith
  have hzQ : z.re < Q γ := by
    change 0 < (z + upsilonShiftN γ m).re ∧
      (z + upsilonShiftN γ m).re < Q γ at hi
    rw [upsilonLeftArg_re] at hi
    nlinarith
  have hbase : z ∈ upsilonStrip γ := by tauto
  have hleft0 : z ∈ upsilonLeftDomain γ 0 := by
    simpa [upsilonLeftDomain, upsilonShiftN, upsilonStrip] using hbase
  have hright0 : z ∈ upsilonRightDomain γ 0 := by
    simpa [upsilonRightDomain, upsilonShiftN, upsilonStrip] using hbase
  calc
    upsilonLeftChart γ m z = upsilonLeftChart γ 0 z := (upsilonLeftChart_eq_of_overlap hγ hshift hi hleft0)
    _ = upsilonBase γ z := by simp [upsilonLeftChart, upsilonShiftN, upsilonBase]
    _ = upsilonRightChart γ 0 z := by simp [upsilonRightChart, upsilonShiftN, upsilonBase]
    _ = upsilonRightChart γ n z := (upsilonRightChart_eq_of_overlap hγ hshift hright0 hj)

private theorem upsilonChart_eq_of_mem
    {i j : UpsilonChartIndex}
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (hi : z ∈ upsilonChartDomain γ i) (hj : z ∈ upsilonChartDomain γ j) :
    upsilonChart γ i z = upsilonChart γ j z := by
  cases i with
  | left m =>
    cases j with
    | left n =>
      exact upsilonLeftChart_eq_of_overlap hγ hshift hi hj
    | right n =>
      exact upsilonLeftRightChart_eq_of_mem hγ hshift hi hj
  | right m =>
    cases j with
    | left n =>
      exact (upsilonLeftRightChart_eq_of_mem hγ hshift hj hi).symm
    | right n =>
      exact upsilonRightChart_eq_of_overlap hγ hshift hi hj

end

private theorem exists_upsilonChartDomain
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) :
    ∃ i : UpsilonChartIndex, z ∈ upsilonChartDomain γ i := by
  have hb : 0 < γ / 2 := by positivity
  have hQb := upsilon_Q_gt_B hγ
  by_cases hzpos : 0 < z.re
  · let y := z.re / (γ / 2)
    have hy0 : 0 ≤ y := by positivity
    by_cases hylt : y < 1
    · refine ⟨.right 0, ?_⟩
      change 0 < (z - upsilonShiftN γ 0).re ∧
        (z - upsilonShiftN γ 0).re < Q γ
      rw [upsilonRightArg_re]
      constructor
      · linarith
      · have hylt' : z.re / (γ / 2) < 1 := by simpa using hylt
        have hzlt : z.re < γ / 2 := by
          simpa using (div_lt_iff₀ hb).mp hylt'
        linarith
    · let N := Nat.floor y
      have hNpos : 1 ≤ N := by
        aesop
      let n := N - 1
      have hfloor : N ≤ y := Nat.floor_le hy0
      have hfloorlt : y < N + 1 := Nat.lt_floor_add_one y
      have hncast : n = (N : ℝ) - 1 := by
        aesop
      have hxy : z.re = y * (γ / 2) := by
        grind
      have hlow : (N : ℝ) - 1 < y := by linarith
      have hscaledLow : ((N : ℝ) - 1) * (γ / 2) < z.re := by
        simp_all
      have hscaledHigh : z.re < ((N : ℝ) + 1) * (γ / 2) := by
        simp_all
      refine ⟨.right n, ?_⟩
      change 0 < (z - upsilonShiftN γ n).re ∧
        (z - upsilonShiftN γ n).re < Q γ
      rw [upsilonRightArg_re, hncast]
      constructor
      · linarith
      · have hQ2 : 2 * (γ / 2) < Q γ := by
          linarith only [upsilon_Q_gt_twoB hγ hγ2]
        linarith only [hscaledHigh, hQ2]
  · have hzle := le_of_not_gt hzpos
    let y := -z.re / (γ / 2)
    have hy0 : 0 ≤ y := by
      bound
    let N := Nat.floor y
    let n := N + 1
    have hfloor := Nat.floor_le hy0
    have hfloorlt := Nat.lt_floor_add_one y
    have hncast : n = (N : ℝ) + 1 := by aesop
    have hxy : z.re = -(y * (γ / 2)) := by
      grind
    have hscaledLow : -z.re < (n : ℝ) * (γ / 2) := by
      nlinarith
    have hscaledLow' : -z.re < (N + 1) * (γ / 2) := by
      simp_all
    have hscaledHigh : (n : ℝ) * (γ / 2) ≤ y * (γ / 2) + γ / 2 := by
      nlinarith
    have hscaledHigh' : ((N : ℝ) + 1) * (γ / 2) ≤
        y * (γ / 2) + γ / 2 := by simp_all
    refine ⟨.left n, ?_⟩
    change 0 < (z + upsilonShiftN γ n).re ∧
      (z + upsilonShiftN γ n).re < Q γ
    rw [upsilonLeftArg_re, hncast]
    constructor
    · linarith
    · linarith only [hscaledHigh', hxy, hQb]

private noncomputable def upsilonIndexAt
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) : UpsilonChartIndex :=
  Classical.choose (exists_upsilonChartDomain (γ := γ) hγ hγ2 z)

private theorem upsilonIndexAt_mem
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) :
    z ∈ upsilonChartDomain γ (upsilonIndexAt hγ hγ2 z) :=
  Classical.choose_spec (exists_upsilonChartDomain hγ hγ2 z)

private noncomputable def upsilonContinuationFunction
    {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) : ℂ :=
  upsilonChart γ (upsilonIndexAt (γ := γ) hγ hγ2 z) z
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ) (hγ2 : γ < 2)

private theorem upsilonContinuation_eq_chart_of_mem
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    {z : ℂ} {i : UpsilonChartIndex} (hi : z ∈ upsilonChartDomain γ i) :
    upsilonContinuationFunction (γ := γ) hγ hγ2 z = upsilonChart γ i z := upsilonChart_eq_of_mem hγ hshift
    (upsilonIndexAt_mem hγ hγ2 z) hi

private theorem upsilonContinuation_differentiableAt
    (hbase : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ))
    (hshift : ∀ v : ℂ, 0 < v.re → v.re < 2 / γ →
      upsilonBase γ (v + upsilonB γ) =
        upsilonRightFactor γ v * upsilonBase γ v)
    (z : ℂ) :
    DifferentiableAt ℂ (upsilonContinuationFunction (γ := γ) hγ hγ2) z := by
  let i := upsilonIndexAt hγ hγ2 z
  have hi : z ∈ upsilonChartDomain γ i := upsilonIndexAt_mem hγ hγ2 z
  have hloc : upsilonContinuationFunction hγ hγ2 =ᶠ[𝓝 z] upsilonChart γ i := by
    filter_upwards [(upsilonChartDomain_isOpen γ i).mem_nhds hi] with w hw
    exact upsilonContinuation_eq_chart_of_mem hγ hγ2 hshift hw
  exact (differentiableAt_upsilonChart hγ hbase hi).congr_of_eventuallyEq hloc

end

private theorem exists_IsUpsilon_of_strip_data
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hbase : DifferentiableOn ℂ (upsilonBase γ) (upsilonStrip γ))
    (hshift : ∀ z : ℂ, 0 < z.re → z.re < 2 / γ →
      upsilonBase γ (z + upsilonB γ) =
        upsilonRightFactor γ z * upsilonBase γ z) :
    ∃ U : ℂ → ℂ, IsUpsilon γ U := by
  let U := upsilonContinuationFunction hγ hγ2
  have hUdiff : Differentiable ℂ U := by
    intro z
    exact upsilonContinuation_differentiableAt hγ hγ2 hbase hshift z
  refine ⟨U, hUdiff, ?_⟩
  intro z hz0 hzQ
  have hstrip : z ∈ upsilonStrip γ := ⟨hz0, hzQ⟩
  have hleft0 : z ∈ upsilonLeftDomain γ 0 := by
    simpa [upsilonLeftDomain, upsilonShiftN, upsilonStrip] using hstrip
  calc
    U z = upsilonContinuationFunction hγ hγ2 z := rfl
    _ = upsilonChart γ (.left 0) z :=
      upsilonContinuation_eq_chart_of_mem hγ hγ2 hshift hleft0
    _ = Complex.exp _ := by
      simp [upsilonChart, upsilonLeftChart, upsilonShiftN, upsilonBase]

end

/-- Existence of an entire Upsilon function from the defining strip integral and its first shift.
The continuation charts use the reciprocal-Gamma multiplier on the left half-plane. -/
theorem exists_IsUpsilon (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ U : ℂ → ℂ, IsUpsilon γ U := by
  apply exists_IsUpsilon_of_strip_data hγ hγ2
  · exact differentiableOn_upsilonBase_of_log (upsilonLog_differentiableOn hγ hγ2)
  · intro z hz0 hzQ
    simpa [upsilonBase, upsilonB, upsilonRightFactor, lFun,
      div_eq_mul_inv, mul_assoc] using (exp_upsilonLog_shift_b hγ hγ2 hz0 hzQ)

end DOZZ.Proofs

end
