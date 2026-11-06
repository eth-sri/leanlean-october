module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.HeckeHeight
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound


def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff  W  (hW : ContDiff ℝ ∞ W)  c  :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support  W   a b B c  (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x))  k n  :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated  W   a b B c   ha 
     hB   hc   hcB 
     hs   hW   t x  :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  grind [dilated]

theorem normPowerProfile_dilated_seminorm  W   a b B c   ha 
     hB   hc   hcB 
     hs   hW 
     t   k n  :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  simp_all [normPowerProfile_dilated]

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

def clippedScale (S : ℝ)  := max 1 S

def clipDilation (S : ℝ)  := clippedScale S / S

theorem clippedScale_ge_one  S  : 1 ≤ clippedScale S := le_max_left _ _

theorem clipDilation_ge_one  S  (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le  b S  (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

theorem clipped_source  W   S x  (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  grind [clippedScale, clippedScale_ge_one, dilated, clipDilation]

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal ActualEisensteinCubic.O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal ActualEisensteinCubic.O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal ActualEisensteinCubic.O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal ActualEisensteinCubic.O → ℂ)  W   S  (hS : 0 < S) :
    (∑' I : Ideal ActualEisensteinCubic.O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal ActualEisensteinCubic.O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  simp_all [clipped_source]

theorem clipped_rowTwistedSum  η   m A₀ z 
     W   t S  (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero  η   m A₀ z 
     W  (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

def retainedProfile (W : ℝ → ℂ) (a b ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ)  :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_support  W   a b   ha 
     hs   hW 
     S   hS   hret   t  :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  grind [dilated_support, max, clipDilation, clipDilation_ge_one, clipDilation_le]

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI
