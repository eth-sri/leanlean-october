/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import GaussianFields.Ambient.Euclidean

/-!
# GaussianFields Haar basic atoms

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace GaussianFields

/-- A dyadic Haar packet index in `R^d`: scale, cell, and a father/mother signature in each
coordinate. -/
structure HaarIndex (d : Nat) where
  /-- Dyadic scale. -/
  scale : ℤ
  /-- Dyadic spatial cell. -/
  cell : Fin d → ℤ
  /-- Coordinate-wise signature: `false` is the father function, `true` is the mother wavelet. -/
  signature : Fin d → Bool
deriving DecidableEq

instance instCountable_haarIndex (d : Nat) : Countable (HaarIndex d) := by
  classical
  exact (show Function.Injective
      (fun idx : HaarIndex d => (idx.scale, idx.cell, idx.signature)) by
    intro idx idx' hidx
    cases idx with
    | mk scale cell signature =>
    cases idx' with
    | mk scale' cell' signature' =>
    simp at hidx
    simpa).countable

noncomputable instance instEncodable_haarIndex (d : Nat) : Encodable (HaarIndex d) :=
  Encodable.ofCountable (HaarIndex d)

/-- A nonzero tensor Haar signature: at least one coordinate uses the mother wavelet. -/
abbrev HaarWaveletSignature (d : Nat) :=
  { signature : Fin d → Bool // signature ≠ fun _ => false }

/-- A dyadic tensor-product Haar wavelet index in `R^d`.  Unlike `HaarIndex`, this excludes the
all-father signature, which is the source of the scale-by-scale redundancy in the raw packet
family. -/
structure HaarWaveletIndex (d : Nat) where
  /-- Dyadic scale. -/
  scale : ℤ
  /-- Dyadic spatial cell. -/
  cell : Fin d → ℤ
  /-- Nonzero coordinate-wise wavelet signature. -/
  signature : HaarWaveletSignature d
deriving DecidableEq

instance instCountable_haarWaveletSignature (d : Nat) :
    Countable (HaarWaveletSignature d) := by
  infer_instance

instance instCountable_haarWaveletIndex (d : Nat) : Countable (HaarWaveletIndex d) := by
  classical
  exact (show Function.Injective
      (fun idx : HaarWaveletIndex d => (idx.scale, idx.cell, idx.signature)) by
    intro idx idx' hidx
    cases idx with
    | mk scale cell signature =>
    cases idx' with
    | mk scale' cell' signature' =>
    simp at hidx
    simpa).countable

noncomputable instance instEncodable_haarWaveletSignature (d : Nat) :
    Encodable (HaarWaveletSignature d) :=
  Encodable.ofCountable (HaarWaveletSignature d)

noncomputable instance instEncodable_haarWaveletIndex (d : Nat) :
    Encodable (HaarWaveletIndex d) :=
  Encodable.ofCountable (HaarWaveletIndex d)

/-- Forget the nonzero-signature proof and view a wavelet index as a raw Haar packet index. -/
@[expose]
def HaarWaveletIndex.toHaarIndex {d : Nat} (idx : HaarWaveletIndex d) : HaarIndex d where
  scale := idx.scale
  cell := idx.cell
  signature := idx.signature

theorem HaarWaveletIndex.toHaarIndex_injective {d : Nat} :
    Function.Injective (@HaarWaveletIndex.toHaarIndex d) := by
  intro idx idx' hidx
  cases idx with
  | mk scale cell signature =>
  cases idx' with
  | mk scale' cell' signature' =>
  cases signature with
  | mk sig hsig =>
  cases signature' with
  | mk sig' hsig' =>
  simp [HaarWaveletIndex.toHaarIndex] at hidx
  simpa

/-- The dyadic dilation `2^j`. -/
@[expose]
noncomputable def dyadicPower (j : ℤ) : ℝ :=
  (2 : ℝ) ^ j

section
variable (j : ℤ)

theorem dyadicPower_pos : 0 < dyadicPower j := by
  unfold dyadicPower
  positivity

theorem dyadicPower_ne_zero : dyadicPower j ≠ 0 :=
  ne_of_gt (dyadicPower_pos j)

theorem dyadicPower_add_one :
    dyadicPower (j + 1) = 2 * dyadicPower j := by
  unfold dyadicPower
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

end

/-- The one-dimensional `L^2` normalization factor `2^(j/2)`. -/
@[expose]
noncomputable def haarScaleFactor (j : ℤ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) / 2)

section
variable (j : ℤ)

theorem haarScaleFactor_pos : 0 < haarScaleFactor j := by
  unfold haarScaleFactor
  positivity

theorem haarScaleFactor_sq :
    haarScaleFactor j ^ (2 : Nat) = dyadicPower j := by
  unfold haarScaleFactor dyadicPower
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num

theorem haarScaleFactor_add_one :
    haarScaleFactor (j + 1) = Real.sqrt 2 * haarScaleFactor j := by
  unfold haarScaleFactor
  have hexp : (((j + 1 : ℤ) : ℝ) / 2) = (j : ℝ) / 2 + (1 / 2 : ℝ) := by
    norm_num
    ring
  rw [hexp, Real.rpow_add (by norm_num : 0 < (2 : ℝ)), ← Real.sqrt_eq_rpow]
  ring

end

/-- The one-dimensional Haar father function `1_[0,1)`. -/
@[expose]
noncomputable def haarFather1D : ℝ → ℝ :=
  Set.indicator (Set.Ico (0 : ℝ) 1) fun _ => (1 : ℝ)

/-- The one-dimensional Haar mother function `1_[0,1/2) - 1_[1/2,1)`. -/
@[expose]
noncomputable def haarMother1D : ℝ → ℝ :=
  Set.indicator (Set.Ico (0 : ℝ) (1 / 2)) (fun _ => (1 : ℝ)) -
    Set.indicator (Set.Ico (1 / 2 : ℝ) 1) fun _ => (1 : ℝ)

@[fun_prop]
theorem measurable_haarFather1D : Measurable haarFather1D := by
  unfold haarFather1D
  exact measurable_const.indicator measurableSet_Ico

@[fun_prop]
theorem measurable_haarMother1D : Measurable haarMother1D := by
  unfold haarMother1D
  exact (measurable_const.indicator measurableSet_Ico).sub
    (measurable_const.indicator measurableSet_Ico)

theorem integrable_haarFather1D :
    Integrable haarFather1D (volume : Measure ℝ) := by
  unfold haarFather1D
  exact (integrableOn_const (C := (1 : ℝ)) (s := Set.Ico (0 : ℝ) 1)
    (μ := volume) (by
      simp)).integrable_indicator measurableSet_Ico

section
variable (x : ℝ)

theorem haarFather1D_sq :
    haarFather1D x ^ (2 : Nat) = haarFather1D x := by
  classical
  simp only [haarFather1D, haarMother1D, Pi.sub_apply, Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> norm_num at * <;> grind

theorem haarMother1D_sq :
    haarMother1D x ^ (2 : Nat) = haarFather1D x := by
  classical
  simp only [haarFather1D, haarMother1D, Pi.sub_apply, Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> norm_num at * <;> grind

theorem haarFather1D_mul_haarMother1D :
    haarFather1D x * haarMother1D x = haarMother1D x := by
  classical
  simp only [haarFather1D, haarMother1D, Pi.sub_apply, Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> norm_num at * <;> grind

end

theorem integral_haarFather1D :
    ∫ x : ℝ, haarFather1D x ∂volume = 1 := by
  rw [haarFather1D, integral_indicator_const]
  simp
  · exact measurableSet_Ico

theorem integral_haarMother1D :
    ∫ x : ℝ, haarMother1D x ∂volume = 0 := by
  rw [haarMother1D]
  change ∫ x : ℝ,
      (Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
        (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x ∂volume = 0
  rw [integral_sub]
  · rw [integral_indicator_const, integral_indicator_const]
    · norm_num [MeasureTheory.measureReal_def, Real.volume_Ico]
    · exact measurableSet_Ico
    · exact measurableSet_Ico
  · exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Ico (0 : ℝ) (1 / 2)) (μ := volume) (by
        simp)).integrable_indicator measurableSet_Ico
  · exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Ico (1 / 2 : ℝ) 1) (μ := volume) (by
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico

/-- Change variables in the full-line Lebesgue integral under an affine map. -/
theorem integral_comp_mul_add_volume (a b : ℝ) (f : ℝ → ℝ) :
    ∫ x : ℝ, f (a * x + b) ∂volume = |a⁻¹| * ∫ y : ℝ, f y ∂volume := by
  rw [Measure.integral_comp_mul_left (fun y => f (y + b)), integral_add_right_eq_self, smul_eq_mul]

/-- Select the father or mother Haar function from a Boolean signature. -/
@[expose]
noncomputable def haarAtom1D (signature : Bool) : ℝ → ℝ :=
  if signature then haarMother1D else haarFather1D

section
variable (signature : Bool)

@[fun_prop]
theorem measurable_haarAtom1D : Measurable (haarAtom1D signature) := by
  cases signature <;> simp [haarAtom1D, measurable_haarFather1D, measurable_haarMother1D]

theorem haarAtom1D_sq (x : ℝ) :
    haarAtom1D signature x ^ (2 : Nat) = haarFather1D x := by
  cases signature <;> simp [haarAtom1D, haarFather1D_sq, haarMother1D_sq]

/-- A one-dimensional Haar atom is supported in `[0, 1)`. -/
theorem haarAtom1D_eq_zero_of_notMem_Ico {x : ℝ}
    (hx : x ∉ Set.Ico (0 : ℝ) 1) :
    haarAtom1D signature x = 0 := by
  simpa [haarFather1D, hx] using haarAtom1D_sq signature x

end

/-- Parent atoms are signed constants on each dyadic child. -/
private theorem haarAtom1D_mul_child_mother (s b : Bool) (x : ℝ) :
    haarAtom1D s x * haarMother1D (2 * x - (if b then 1 else 0)) =
      (if b && s then -1 else 1) * haarMother1D (2 * x - (if b then 1 else 0)) := by
  classical
  cases s <;> cases b <;>
    simp only [haarAtom1D, Bool.false_eq_true, Bool.false_and,
      Bool.true_and, ↓reduceIte, haarFather1D, haarMother1D, Pi.sub_apply, Set.indicator_apply, Set.mem_Ico] <;>
    split_ifs <;> norm_num at * <;> grind

/-- Every child mother has mean zero against either parent atom. -/
theorem integral_haarAtom1D_mul_child_mother (s b : Bool) :
    ∫ x : ℝ, haarAtom1D s x * haarMother1D (2 * x - (if b then 1 else 0)) ∂volume = 0 := by
  simp_rw [haarAtom1D_mul_child_mother, integral_const_mul, sub_eq_add_neg]
  rw [integral_comp_mul_add_volume, integral_haarMother1D, mul_zero, mul_zero]

/-- The two child fathers recover the parent with the sign selected by the signature. -/
theorem haarAtom1D_refine (s : Bool) (x : ℝ) :
    haarAtom1D s x = haarFather1D (2 * x) + (if s then -1 else 1) * haarFather1D (2 * x - 1) := by
  classical
  cases s <;> simp only [haarAtom1D, Bool.false_eq_true, ↓reduceIte,
    haarFather1D, haarMother1D, Pi.sub_apply, Set.indicator_apply, Set.mem_Ico] <;>
    split_ifs <;> norm_num at * <;> grind

/-- Distinct integer translates of `[0,1)` are disjoint. -/
theorem not_both_mem_Ico_sub_int {z : ℝ} {k₁ k₂ : ℤ} (hk : k₁ ≠ k₂) :
    ¬ (z - (k₁ : ℝ) ∈ Set.Ico (0 : ℝ) 1 ∧
      z - (k₂ : ℝ) ∈ Set.Ico (0 : ℝ) 1) := by
  rintro ⟨h₁, h₂⟩
  rcases lt_or_gt_of_ne hk with hklt | hkgt
  · have hle : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hklt)
    linarith [h₁.2, h₂.1, hle]
  · have hle : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hkgt)
    linarith [h₂.2, h₁.1, hle]

/-- Haar atoms in distinct integer cells have pointwise-zero product. -/
theorem haarAtom1D_mul_eq_zero_of_cells_ne (signature₁ signature₂ : Bool)
    {z : ℝ} {k₁ k₂ : ℤ} (hk : k₁ ≠ k₂) :
    haarAtom1D signature₁ (z - (k₁ : ℝ)) *
        haarAtom1D signature₂ (z - (k₂ : ℝ)) = 0 := by
  by_cases h₁ : z - (k₁ : ℝ) ∈ Set.Ico (0 : ℝ) 1
  · by_cases h₂ : z - (k₂ : ℝ) ∈ Set.Ico (0 : ℝ) 1
    · exact False.elim (not_both_mem_Ico_sub_int hk ⟨h₁, h₂⟩)
    · rw [haarAtom1D_eq_zero_of_notMem_Ico signature₂ h₂, mul_zero]
  · rw [haarAtom1D_eq_zero_of_notMem_Ico signature₁ h₁, zero_mul]

private theorem haarAtom1D_mul (s t : Bool) (x : ℝ) :
    haarAtom1D s x * haarAtom1D t x = haarAtom1D (s != t) x := by
  cases s <;> cases t <;> simp [haarAtom1D, ← pow_two, haarFather1D_sq,
    haarMother1D_sq, haarFather1D_mul_haarMother1D, mul_comm (haarMother1D x)]

theorem integral_haarAtom1D_mul_haarAtom1D (signature₁ signature₂ : Bool) :
    ∫ x : ℝ, haarAtom1D signature₁ x * haarAtom1D signature₂ x ∂volume =
      if signature₁ = signature₂ then 1 else 0 := by
  simp_rw [haarAtom1D_mul]
  cases signature₁ <;> cases signature₂ <;> simp [haarAtom1D, integral_haarFather1D, integral_haarMother1D]

end GaussianFields

end
