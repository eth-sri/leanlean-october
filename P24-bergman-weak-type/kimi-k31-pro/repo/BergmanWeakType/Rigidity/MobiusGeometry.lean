/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.PhaseRigidity
public import BergmanWeakType.Rigidity.UnitDiscShift
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section

open Set Metric
open scoped ComplexConjugate

namespace BergmanWeakType

theorem mobius_denominator_ne_zero {ζ w : ℂ} (hζ : ‖ζ‖ ≤ 1) (hw : w ∈ disk) :
    1 - star ζ * w ≠ 0 := by
  simpa using kernel_denominator_ne_zero_closed_left
    (show ‖star ζ‖ ≤ 1 by simpa using hζ)
    (show star w ∈ disk by simpa [mem_disk_iff] using hw)

theorem image_affine_disk {a b : ℂ} (hb : b ≠ 0) :
    (fun w ↦ a + b * w) '' disk = ball a ‖b‖ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_mul]
    simpa using (mul_lt_mul_of_pos_left ((mem_disk_iff w).mp hw) (norm_pos_iff.mpr hb))
  · intro hz
    refine ⟨(z - a) / b, ?_, ?_⟩
    · rw [mem_disk_iff, norm_div, div_lt_one (norm_pos_iff.mpr hb)]
      exact mem_ball_iff_norm.mp hz
    · field_simp
      ring

/-- In the bounded case the equality derivative can only parametrize a Euclidean disk. -/
theorem image_is_disk_of_derivative_form {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ disk) (hφ0 : deriv φ 0 ≠ 0)
    (hbounded : Bornology.IsBounded (φ '' disk)) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (hderiv : ∀ w ∈ disk, deriv φ w * (1 - star ζ * w) ^ 2 = deriv φ 0) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ φ '' disk = ball c R := by
  have heq : φ '' disk =
      (fun w ↦ φ 0 + deriv φ 0 * w / (1 - star ζ * w)) '' disk :=
    image_congr (by
      let H : ℂ → ℂ := fun w ↦ φ 0 + deriv φ 0 * w / (1 - star ζ * w)
      have hH : ∀ w ∈ disk, HasDerivAt H (deriv φ w) w := by
        intro w hw
        have hn := mobius_denominator_ne_zero hζ hw
        have heq : deriv φ w = deriv φ 0 / (1 - star ζ * w) ^ 2 :=
          (eq_div_iff (pow_ne_zero 2 hn)).mpr (hderiv w hw)
        have hd := (((hasDerivAt_id w).const_mul (deriv φ 0)).div
          ((hasDerivAt_const w 1).sub ((hasDerivAt_id w).const_mul (star ζ))) hn).const_add
            (φ 0)
        convert hd using 1
        · rfl
        · simp only [Pi.sub_apply, id_eq, heq]
          ring
      have hd : DifferentiableOn ℂ (fun w ↦ φ w - H w) disk :=
        hφ.sub (fun w hw ↦ (hH w hw).differentiableAt.differentiableWithinAt)
      have hz : EqOn (deriv (fun w ↦ φ w - H w)) 0 disk := by
        intro w hw
        have hh : HasDerivAt (fun w ↦ φ w - H w) (deriv φ w - deriv φ w) w := by
          convert ((hφ w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.sub
            (hH w hw) using 1
        simpa using hh.deriv
      intro w hw
      have heq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
        hd hz hw (show (0 : ℂ) ∈ disk by simp [disk])
      dsimp [H] at heq ⊢
      simpa using sub_eq_zero.mp (by simpa using heq))
  have hζlt : ‖ζ‖ < 1 := lt_of_le_of_ne hζ fun h ↦
    by
      have hbounded' := heq ▸ hbounded
      obtain ⟨M, hMpos, hM⟩ := hbounded'.exists_pos_norm_le
      let N : ℝ := (M + ‖φ 0‖ + 1) / ‖deriv φ 0‖
      have hbpos : 0 < ‖deriv φ 0‖ := norm_pos_iff.mpr hφ0
      have hN : 0 < N := by dsimp [N]; positivity
      let t : ℝ := N / (N + 1)
      have ht : 0 < t := by dsimp [t]; positivity
      have ht1 : t < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      have hw : (t : ℂ) * ζ ∈ disk := by
        rw [mem_disk_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, h]
        simpa using ht1
      have hζmul : star ζ * ζ = 1 := by
        change conj ζ * ζ = 1
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h]
        norm_num
      have hvalue : (t : ℂ) * ζ / (1 - star ζ * ((t : ℂ) * ζ)) = (N : ℂ) * ζ := by
        have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : N + 1 ≠ 0)
        rw [show star ζ * ((t : ℂ) * ζ) = t * (star ζ * ζ) by ring, hζmul, mul_one]
        dsimp [t]
        push_cast
        field_simp [hN1]
        ring
      have hbound := hM _ ⟨_, hw, rfl⟩
      dsimp only at hbound
      rw [mul_div_assoc, hvalue] at hbound
      have hnorm := norm_sub_le (φ 0 + deriv φ 0 * ((N : ℂ) * ζ)) (φ 0)
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hN, h, mul_one] at hnorm
      have hNmass : ‖deriv φ 0‖ * N = M + ‖φ 0‖ + 1 := by
        dsimp [N]
        field_simp
      linarith
  refine ⟨_, _, ?_, heq.trans (by
      let d : ℝ := 1 - ‖ζ‖ ^ 2
      have hd : 0 < d := by dsimp [d]; nlinarith [norm_nonneg ζ]
      have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
      let Z : Complex.UnitDisc := Complex.UnitDisc.mk ζ hζlt
      let c : ℂ := φ 0 + deriv φ 0 * ζ / (d : ℂ)
      let s : ℂ := deriv φ 0 / (d : ℂ)
      have hs : s ≠ 0 := div_ne_zero hφ0 hdc
      have hform : ∀ W : Complex.UnitDisc,
          φ 0 + deriv φ 0 * (W : ℂ) / (1 - star ζ * W) =
            c + s * (Complex.UnitDisc.shift (-Z) W : ℂ) := by
        intro W
        have hn := mobius_denominator_ne_zero hζlt.le
          (show (W : ℂ) ∈ disk from (mem_disk_iff _).mpr W.norm_lt_one)
        have hnorm : (‖ζ‖ ^ 2 : ℝ) = star ζ * ζ := by
          change (‖ζ‖ ^ 2 : ℝ) = conj ζ * ζ
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        change 1 - conj ζ * (W : ℂ) ≠ 0 at hn
        have hn' : 1 - (W : ℂ) * conj ζ ≠ 0 := by simpa only [mul_comm] using hn
        change (‖ζ‖ ^ 2 : ℝ) = conj ζ * ζ at hnorm
        dsimp [c, s]
        rw [Complex.UnitDisc.coe_shift]
        simp only [Z, Complex.UnitDisc.coe_neg, Complex.UnitDisc.coe_mk, map_neg, neg_mul,
          ← sub_eq_add_neg]
        field_simp [hn, hn', hdc]
        dsimp [d]
        push_cast at hnorm ⊢
        rw [hnorm]
        field_simp [hn, hn']
        ring
      have himage : (fun w ↦ φ 0 + deriv φ 0 * w / (1 - star ζ * w)) '' disk =
          (fun w ↦ c + s * w) '' disk := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          let W : Complex.UnitDisc := Complex.UnitDisc.mk w ((mem_disk_iff _).mp hw)
          refine ⟨Complex.UnitDisc.shift (-Z) W,
            (mem_disk_iff _).mpr (Complex.UnitDisc.shift (-Z) W).norm_lt_one, ?_⟩
          exact (hform W).symm
        · rintro ⟨w, hw, rfl⟩
          let W : Complex.UnitDisc := Complex.UnitDisc.mk w ((mem_disk_iff _).mp hw)
          let V := (Complex.UnitDisc.shift (-Z)).symm W
          refine ⟨V, (mem_disk_iff _).mpr V.norm_lt_one, ?_⟩
          dsimp only
          rw [hform V]
          simp [V, W]
      rw [himage, image_affine_disk hs])⟩
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < 1 - ‖ζ‖ ^ 2 by nlinarith [norm_nonneg ζ])]
  exact div_pos (norm_pos_iff.mpr hφ0) (by nlinarith [norm_nonneg ζ])

end BergmanWeakType
