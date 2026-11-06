/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Notation

public import BergmanWeakType.Weighted.PolarCap
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Normalizing a polar supersolution by a positive radial solution -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

def quotientRadialFirst (F Fr : ℝ → ℝ → ℝ) (J Jr : ℝ → ℝ) (r θ : ℝ) : ℝ :=
  (Fr r θ * J r - F r θ * Jr r) / J r ^ 2

def quotientRadialSecond (F Fr Frr : ℝ → ℝ → ℝ) (J Jr Jrr : ℝ → ℝ)
    (r θ : ℝ) : ℝ :=
  Frr r θ / J r - F r θ * Jrr r / J r ^ 2 - 2 * Fr r θ * Jr r / J r ^ 2 +
    2 * F r θ * Jr r ^ 2 / J r ^ 3

theorem quotientRadialFirst_hasDerivAt {F Fr Frr : ℝ → ℝ → ℝ} {J Jr Jrr : ℝ → ℝ}
    {r θ : ℝ} (hF : HasDerivAt (fun u ↦ F u θ) (Fr r θ) r)
    (hFr : HasDerivAt (fun u ↦ Fr u θ) (Frr r θ) r)
    (hJ : HasDerivAt J (Jr r) r) (hJr : HasDerivAt Jr (Jrr r) r) (hJ0 : J r ≠ 0) :
    HasDerivAt (fun u ↦ quotientRadialFirst F Fr J Jr u θ)
      (quotientRadialSecond F Fr Frr J Jr Jrr r θ) r := by
  convert ((hFr.mul hJ).sub (hF.mul hJr)).div (hJ.pow 2) (pow_ne_zero 2 hJ0) using 1
  · rfl
  · unfold quotientRadialSecond
    dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
    field_simp [hJ0]
    ring

def quotientWeight (k : ℝ) (J : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 - r ^ 2) ^ k * J r ^ 2

def quotientWeightDeriv (k : ℝ) (J Jr : ℝ → ℝ) (r : ℝ) : ℝ :=
  quotientWeight k J r * (-(2 * k * r / (1 - r ^ 2)) + 2 * Jr r / J r)

theorem quotientWeight_hasDerivAt {k r : ℝ} {J Jr : ℝ → ℝ}
    (hr : r ^ 2 < 1) (hJ0 : J r ≠ 0) (hJ : HasDerivAt J (Jr r) r) :
    HasDerivAt (quotientWeight k J) (quotientWeightDeriv k J Jr r) r := by
  have ht : 0 < 1 - r ^ 2 := sub_pos.mpr hr
  have hd := (((hasDerivAt_id r).pow 2).const_sub 1).rpow_const (p := k) (Or.inl ht.ne')
  convert hd.mul (hJ.pow 2) using 1
  · rfl
  · unfold quotientWeightDeriv quotientWeight
    dsimp only [Pi.pow_apply, id_eq]
    rw [Real.rpow_sub_one ht.ne']
    field_simp [hJ0, ht.ne']
    ring

theorem antitoneOn_angularMean_min_quotient {F Fr Frr Ft Ftt : ℝ → ℝ → ℝ}
    {J Jr Jrr : ℝ → ℝ} (k c : ℝ) (h : PolarSmooth F Fr Frr Ft Ftt)
    (hJ : RadialSmooth J Jr Jrr)
    (hJode : ∀ r ∈ Ioo01,
      Jrr r + (1 / r - 2 * k * r / (1 - r ^ 2)) * Jr r -
        (k ^ 2 / (1 - r ^ 2)) * J r = 0)
    (hFode : ∀ r ∈ Ioo01, ∀ θ,
      Frr r θ + (1 / r - 2 * k * r / (1 - r ^ 2)) * Fr r θ + Ftt r θ / r ^ 2 -
        (k ^ 2 / (1 - r ^ 2)) * F r θ ≤ 0) :
    AntitoneOn (angularMean (fun r θ ↦ min (F r θ / J r) c)) (Ico 0 1) := by
  have hJ' : ContinuousOn (fun p : ℝ × ℝ ↦ J p.1) (Ico 0 1 ×ˢ univ) :=
    hJ.cont.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hJr' : ContinuousOn (fun p : ℝ × ℝ ↦ Jr p.1) (Ico 0 1 ×ˢ univ) :=
    hJ.contR.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hJrr' : ContinuousOn (fun p : ℝ × ℝ ↦ Jrr p.1) (Ico 0 1 ×ˢ univ) :=
    hJ.contRR.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hn : ∀ p ∈ Ico01 ×ˢ (univ : Set ℝ), J p.1 ≠ 0 :=
    fun p hp ↦ (hJ.pos p.1 hp.1).ne'
  have hpow (n : ℕ) : ∀ p ∈ Ico01 ×ˢ (univ : Set ℝ), J p.1 ^ n ≠ 0 :=
    fun p hp ↦ pow_ne_zero n (hn p hp)
  have hmem : ∀ r ∈ Ioo01, r ∈ Ico01 := fun r hr ↦ ⟨hr.1.le, hr.2⟩
  have hr2 : ∀ r ∈ Ioo01, r ^ 2 < 1 := fun r hr ↦
    (sq_lt_one_iff_abs_lt_one r).mpr (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩)
  have hbase : ContinuousOn (fun r : ℝ ↦ (1 - r ^ 2) ^ k) (Ico 0 1) := by
    apply (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const
    rintro r ⟨h0, h1⟩
    exact Or.inl (by nlinarith : (0 : ℝ) < 1 - r ^ 2).ne'
  refine antitoneOn_angularMean_min_of_polar_flux c
    (Fr := quotientRadialFirst F Fr J Jr) (Frr := quotientRadialSecond F Fr Frr J Jr Jrr)
    (Ft := fun r θ ↦ Ft r θ / J r) (Ftt := fun r θ ↦ Ftt r θ / J r)
    (w := quotientWeight k J) (w' := quotientWeightDeriv k J Jr)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · exact h.cont.div hJ' hn
  · exact ((h.contR.mul hJ').sub (h.cont.mul hJr')).div (hJ'.pow 2) (hpow 2)
  · exact (((h.contRR.div hJ' hn).sub ((h.cont.mul hJrr').div (hJ'.pow 2) (hpow 2))).sub
      (((h.contR.const_mul 2).mul hJr').div (hJ'.pow 2) (hpow 2))).add
      (((h.cont.const_mul 2).mul (hJr'.pow 2)).div (hJ'.pow 3) (hpow 3))
  · exact h.contT.div hJ' hn
  · exact h.contTT.div hJ' hn
  · intro r hr θ
    exact (h.deriv r hr θ).div (hJ.deriv r hr) (hJ.pos r (hmem r hr)).ne'
  · intro r hr θ
    exact quotientRadialFirst_hasDerivAt (h.deriv r hr θ) (h.derivR r hr θ) (hJ.deriv r hr)
      (hJ.derivR r hr) (hJ.pos r (hmem r hr)).ne'
  · intro r hr θ
    exact (h.derivT r hr θ).div_const (J r)
  · intro r hr θ
    exact (h.derivTT r hr θ).div_const (J r)
  · intro r hr
    rw [h.periodF r hr]
  · intro r hr
    rw [h.periodT r hr]
  · exact hbase.mul (hJ.cont.pow 2)
  · intro r hr
    exact quotientWeight_hasDerivAt (hr2 r hr) (hJ.pos r (hmem r hr)).ne' (hJ.deriv r hr)
  · intro r hr
    exact mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr (hr2 r hr)) k)
      (sq_pos_of_pos (hJ.pos r (hmem r hr)))
  · intro r hr θ
    have hj := hJ.pos r (hmem r hr)
    have ht : 0 < 1 - r ^ 2 := sub_pos.mpr (hr2 r hr)
    have h := quotient_polar_operator_nonpos hj hr.1.ne'
      (a := 1 / r - 2 * k * r / (1 - r ^ 2)) (b := -(k ^ 2 / (1 - r ^ 2)))
      (by simpa only [neg_mul, ← sub_eq_add_neg] using hJode r hr)
      (by simpa only [neg_mul, ← sub_eq_add_neg] using hFode r hr θ)
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hr.1.le (mul_nonneg (Real.rpow_nonneg ht.le k) (sq_nonneg (J r)))) h
    convert hm using 1
    unfold quotientWeightDeriv quotientWeight quotientRadialFirst quotientRadialSecond
    field_simp [hj.ne', hr.1.ne', ht.ne']
    ring

end BergmanWeakType.Weighted
