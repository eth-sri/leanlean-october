/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.WhiteNoise.Haar.Basic

/-!
# GaussianFields Haar one dimensional refinements

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace GaussianFields

/-- The normalized one-dimensional Haar packet at scale `j`, cell `k`, and signature `signature`. -/
@[expose]
noncomputable def haar1D (j k : ℤ) (signature : Bool) : ℝ → ℝ :=
  fun x => haarScaleFactor j * haarAtom1D signature (dyadicPower j * x - (k : ℝ))

/-- The one-dimensional dyadic interval supporting the father packet at scale `j` and cell `k`. -/
@[expose]
def dyadicInterval (j k : ℤ) : Set ℝ :=
  Set.Ico ((k : ℝ) / dyadicPower j) (((k : ℝ) + 1) / dyadicPower j)
section
variable (j k : ℤ)

theorem mem_dyadicInterval_iff (x : ℝ) :
    x ∈ dyadicInterval j k ↔
      dyadicPower j * x - (k : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
  let a := dyadicPower j
  have ha := dyadicPower_pos j
  have hane : a ≠ 0 := ne_of_gt ha
  constructor
  · intro hx
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hx.1 ha.le
      have hk : a * ((k : ℝ) / a) = (k : ℝ) := by
        field_simp
      linarith
    · have hmul := mul_lt_mul_of_pos_left hx.2 ha
      have hk : a * (((k : ℝ) + 1) / a) = (k : ℝ) + 1 := by
        field_simp
      linarith
  · intro hx
    constructor
    · have hle : k ≤ a * x := by linarith [hx.1]
      exact (div_le_iff₀ ha).2 (by linarith)
    · have hlt : a * x < k + 1 := by linarith [hx.2]
      exact (lt_div_iff₀ ha).2 (by linarith)

theorem measurableSet_dyadicInterval :
    MeasurableSet (dyadicInterval j k) := by
  exact measurableSet_Ico

theorem haar1D_father_eq_indicator_dyadicInterval (x : ℝ) :
    haar1D j k false x =
      haarScaleFactor j *
        Set.indicator (dyadicInterval j k) (fun _ : ℝ => (1 : ℝ)) x := by
  unfold haar1D haarAtom1D haarFather1D
  by_cases hx : x ∈ dyadicInterval j k
  · have hx' :=
      (mem_dyadicInterval_iff j k x).1 hx
    simp_all
  · have hx' :=
      mt (mem_dyadicInterval_iff j k x).2 hx
    simp_all

end

@[fun_prop]
theorem measurable_haar1D (j k : ℤ) (signature : Bool) :
    Measurable (haar1D j k signature) := by
  unfold haar1D
  fun_prop
section
variable (j k : ℤ)

theorem integrable_haarFather1D_affine :
    Integrable (fun x : ℝ => haarFather1D (dyadicPower j * x - (k : ℝ)))
      (volume : Measure ℝ) := by
  have hshift :
      Integrable (fun y => haarFather1D (y - k)) volume := by
    simpa [sub_eq_add_neg] using integrable_haarFather1D.comp_add_right (-k)
  simpa [sub_eq_add_neg] using hshift.comp_mul_left' (dyadicPower_ne_zero j)
section
variable (signature : Bool)

theorem haar1D_sq (x : ℝ) :
    haar1D j k signature x ^ (2 : Nat) =
      dyadicPower j * haarFather1D (dyadicPower j * x - (k : ℝ)) := by
  unfold haar1D
  rw [mul_pow, haarAtom1D_sq, haarScaleFactor_sq]

theorem integrable_haar1D_sq :
    Integrable (fun x : ℝ => haar1D j k signature x ^ (2 : Nat))
      (volume : Measure ℝ) := by
  refine ((integrable_haarFather1D_affine j k).const_mul (dyadicPower j)).congr
    (ae_of_all _ ?_)
  intro x
  exact (haar1D_sq j k signature x).symm

theorem memLp_haar1D :
    MemLp (haar1D j k signature) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq]
  · exact integrable_haar1D_sq j k signature
  fun_prop

end

end

/-- The one-dimensional Haar packet as an `L²` vector. -/
@[expose]
noncomputable def haar1DLp (j k : ℤ) (signature : Bool) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_haar1D j k signature).toLp (haar1D j k signature)
section
variable (j k : ℤ) (signature₁ signature₂ : Bool)

theorem haar1D_mul_haar1D_same_scale_cell (x : ℝ) :
    haar1D j k signature₁ x * haar1D j k signature₂ x =
      dyadicPower j *
        (haarAtom1D signature₁ (dyadicPower j * x - (k : ℝ)) *
          haarAtom1D signature₂ (dyadicPower j * x - (k : ℝ))) := by
  unfold haar1D
  rw [← haarScaleFactor_sq]
  ring

theorem integral_haar1D_mul_haar1D_same_scale_cell :
    ∫ x : ℝ, haar1D j k signature₁ x * haar1D j k signature₂ x ∂volume =
      if signature₁ = signature₂ then 1 else 0 := by
  let f : ℝ → ℝ := fun y => haarAtom1D signature₁ y * haarAtom1D signature₂ y
  have hbase :
      ∫ y : ℝ, f y ∂volume = if signature₁ = signature₂ then 1 else 0 := integral_haarAtom1D_mul_haarAtom1D signature₁ signature₂
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - k) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -k)
      (dyadicPower_ne_zero j) f
      (integrable_haarAtom1D_mul_haarAtom1D signature₁ signature₂)
    simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr (dyadicPower_pos j)), f] using h
  calc
    ∫ x : ℝ, haar1D j k signature₁ x * haar1D j k signature₂ x ∂volume =
        ∫ x : ℝ, dyadicPower j * f _ ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          change haar1D j k signature₁ x * haar1D j k signature₂ x =
            dyadicPower j * f _
          rw [haar1D_mul_haar1D_same_scale_cell]
    _ = dyadicPower j *
        ∫ x : ℝ, f _ ∂volume := by
          rw [integral_const_mul]
    _ = if signature₁ = signature₂ then 1 else 0 := by
          rw [haffine, hbase]
          by_cases hsig : signature₁ = signature₂
          · simp [hsig, mul_inv_cancel₀ (dyadicPower_ne_zero j)]
          simp_all

end
section
variable (j k₁ k₂ : ℤ) (signature₁ signature₂ : Bool)
section
variable (hk : k₁ ≠ k₂)
include hk

/-- One-dimensional Haar atoms at the same scale but in distinct cells have pointwise-zero
product. -/
theorem haar1D_mul_haar1D_same_scale_cell_ne (x : ℝ) :
    haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x = 0 := by
  unfold haar1D
  let a₁ := haarAtom1D signature₁ (dyadicPower j * x - k₁)
  let a₂ := haarAtom1D signature₂ (dyadicPower j * x - k₂)
  have hprod : a₁ * a₂ = 0 := haarAtom1D_mul_eq_zero_of_cells_ne signature₁ signature₂
      hk
  aesop

/-- One-dimensional Haar atoms at the same scale but in distinct cells are orthogonal. -/
theorem integral_haar1D_mul_haar1D_same_scale_cell_ne :
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume =
        ∫ x : ℝ, 0 ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          exact haar1D_mul_haar1D_same_scale_cell_ne j k₁ k₂
            signature₁ signature₂ hk x
    _ = 0 := by simp

end

/-- Same-scale one-dimensional Haar inner products reduce to equality of cells and signatures. -/
theorem integral_haar1D_mul_haar1D_same_scale :
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume =
      if k₁ = k₂ then if signature₁ = signature₂ then 1 else 0 else 0 := by
  by_cases hk : k₁ = k₂
  · subst k₂
    rw [ite_eq_left rfl]
    exact integral_haar1D_mul_haar1D_same_scale_cell j k₁ signature₁ signature₂
  · rw [ite_eq_right hk]
    exact integral_haar1D_mul_haar1D_same_scale_cell_ne j k₁ k₂
      signature₁ signature₂ hk

end
section
variable (j k : ℤ)
section
variable (x : ℝ)

theorem haar1D_left_child_arg :
    dyadicPower (j + 1) * x - 2 * (k : ℝ) =
      2 * (dyadicPower j * x - (k : ℝ)) := by
  rw [dyadicPower_add_one]
  ring

theorem haar1D_right_child_arg :
    dyadicPower (j + 1) * x - (2 * (k : ℝ) + 1) =
      2 * (dyadicPower j * x - (k : ℝ)) - 1 := by
  rw [dyadicPower_add_one]
  ring

/-- The normalized father packet is the normalized sum of its two next-scale father children. -/
theorem haar1D_father_refine :
    haar1D j k false x =
      (Real.sqrt 2)⁻¹ *
        (haar1D (j + 1) ((2 : ℤ) * k) false x +
          haar1D (j + 1) ((2 : ℤ) * k + 1) false x) := by
  unfold haar1D
  simp [haarAtom1D]
  rw [haar1D_left_child_arg, haar1D_right_child_arg, haarFather1D_refine (dyadicPower j * x - (k : ℝ)), haarScaleFactor_add_one]
  field_simp

/-- The normalized mother packet is the normalized difference of the two next-scale father
children. -/
theorem haar1D_mother_refine :
    haar1D j k true x =
      (Real.sqrt 2)⁻¹ *
        (haar1D (j + 1) ((2 : ℤ) * k) false x -
          haar1D (j + 1) ((2 : ℤ) * k + 1) false x) := by
  unfold haar1D
  simp [haarAtom1D]
  rw [haar1D_left_child_arg, haar1D_right_child_arg, haarMother1D_refine (dyadicPower j * x - (k : ℝ)), haarScaleFactor_add_one]
  field_simp

theorem haar1D_left_child_father_refine_pointwise :
    haar1D (j + 1) ((2 : ℤ) * k) false x =
      (Real.sqrt 2)⁻¹ * (haar1D j k false x + haar1D j k true x) := by
  let L := haar1D (j + 1) (2 * k) false x
  let R := haar1D (j + 1) (2 * k + 1) false x
  let F := haar1D j k false x
  let M := haar1D j k true x
  have hf : F = (Real.sqrt 2)⁻¹ * (L + R) := by
    simpa [F, L, R] using haar1D_father_refine j k x
  have hm : M = (Real.sqrt 2)⁻¹ * (L - R) := by
    simpa [M, L, R] using haar1D_mother_refine j k x
  grind

theorem haar1D_right_child_father_refine_pointwise :
    haar1D (j + 1) ((2 : ℤ) * k + 1) false x =
      (Real.sqrt 2)⁻¹ * (haar1D j k false x - haar1D j k true x) := by
  let L := haar1D (j + 1) (2 * k) false x
  let R := haar1D (j + 1) (2 * k + 1) false x
  let F := haar1D j k false x
  let M := haar1D j k true x
  have hf : F = (Real.sqrt 2)⁻¹ * (L + R) := by
    simpa [F, L, R] using haar1D_father_refine j k x
  have hm : M = (Real.sqrt 2)⁻¹ * (L - R) := by
    simpa [M, L, R] using haar1D_mother_refine j k x
  grind

end

theorem haar1D_child_father_refine_bool (side : Bool) (x : ℝ) :
    haar1D (j + 1) ((2 : ℤ) * k + if side then 1 else 0) false x =
      ∑ signature : Bool,
        ((Real.sqrt 2)⁻¹ * (if side && signature then (-1 : ℝ) else 1)) *
          haar1D j k signature x := by
  cases side
  · rw [show 2 * k + (if false then 1 else 0) = 2 * k by simp]
    rw [haar1D_left_child_father_refine_pointwise]
    simp
    ring
  · rw [show 2 * k + (if true then 1 else 0) = 2 * k + 1 by simp]
    rw [haar1D_right_child_father_refine_pointwise]
    simp
    ring

/-- The father refinement identity as an equality in `L²(R)`. -/
theorem haar1DLp_father_refine :
    haar1DLp j k false =
      (Real.sqrt 2)⁻¹ •
        (haar1DLp (j + 1) ((2 : ℤ) * k) false +
          haar1DLp (j + 1) ((2 : ℤ) * k + 1) false) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_haar1D j k false).coeFn_toLp,
    Lp.coeFn_smul (c := (Real.sqrt 2)⁻¹)
      (haar1DLp _ _ false +
        haar1DLp _ _ false),
    Lp.coeFn_add _
      (haar1DLp _ _ false),
    (memLp_haar1D _ _ false).coeFn_toLp,
    (memLp_haar1D _ _ false).coeFn_toLp] with
    x hx hsmul hadd hleft hright
  change ((memLp_haar1D j k false).toLp (haar1D j k false)) x =
    (((Real.sqrt 2)⁻¹) •
      (haar1DLp _ _ false +
        haar1DLp _ _ false)) x
  rw [hx, hsmul]
  change haar1D j k false x =
    (Real.sqrt 2)⁻¹ *
      ((haar1DLp _ _ false +
        haar1DLp _ _ false) x)
  rw [hadd]
  change haar1D j k false x =
    (Real.sqrt 2)⁻¹ *
      (((memLp_haar1D _ _ false).toLp
          (haar1D _ _ false)) x +
        ((memLp_haar1D _ _ false).toLp
          (haar1D _ _ false)) x)
  rw [hleft, hright]
  exact haar1D_father_refine j k x

/-- The mother refinement identity as an equality in `L²(R)`. -/
theorem haar1DLp_mother_refine :
    haar1DLp j k true =
      (Real.sqrt 2)⁻¹ •
        (haar1DLp (j + 1) ((2 : ℤ) * k) false -
          haar1DLp (j + 1) ((2 : ℤ) * k + 1) false) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_haar1D j k true).coeFn_toLp,
    Lp.coeFn_smul (c := (Real.sqrt 2)⁻¹)
      (haar1DLp _ _ false -
        haar1DLp _ _ false),
    Lp.coeFn_sub _
      (haar1DLp _ _ false),
    (memLp_haar1D _ _ false).coeFn_toLp,
    (memLp_haar1D _ _ false).coeFn_toLp] with
    x hx hsmul hsub hleft hright
  change ((memLp_haar1D j k true).toLp (haar1D j k true)) x =
    (((Real.sqrt 2)⁻¹) •
      (haar1DLp _ _ false -
        haar1DLp _ _ false)) x
  rw [hx, hsmul]
  change haar1D j k true x =
    (Real.sqrt 2)⁻¹ *
      ((haar1DLp _ _ false -
        haar1DLp _ _ false) x)
  rw [hsub]
  change haar1D j k true x =
    (Real.sqrt 2)⁻¹ *
      (((memLp_haar1D _ _ false).toLp
          (haar1D _ _ false)) x -
        ((memLp_haar1D _ _ false).toLp
          (haar1D _ _ false)) x)
  rw [hleft, hright]
  exact haar1D_mother_refine j k x

/-- A normalized mother Haar atom is orthogonal to the left mother atom at the next dyadic scale. -/
theorem integral_haar1D_mul_left_child_mother :
    ∫ x : ℝ, haar1D j k true x * haar1D (j + 1) ((2 : ℤ) * k) true x ∂volume = 0 := by
  let f : ℝ → ℝ := fun y => haarMother1D y * haarMother1D (2 * y)
  have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
    simpa [f] using integral_haarMother1D_mul_left_child
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - k) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -k)
      (dyadicPower_ne_zero j) f integrable_haarMother1D_mul_left_child
    aesop
  calc
    ∫ x : ℝ, haar1D j k true x * haar1D _ _ true x ∂volume =
        ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
          f (dyadicPower j * x - k) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          unfold haar1D f
          simp [haarAtom1D]
          rw [haar1D_left_child_arg]
          ring
    _ = (haarScaleFactor j * haarScaleFactor _) *
        ∫ x : ℝ, f _ ∂volume := by
          rw [integral_const_mul]
    _ = 0 := by
          simp_all

/-- A normalized mother Haar atom is orthogonal to the right mother atom at the next dyadic scale. -/
theorem integral_haar1D_mul_right_child_mother :
    ∫ x : ℝ, haar1D j k true x * haar1D (j + 1) ((2 : ℤ) * k + 1) true x ∂volume = 0 := by
  let f : ℝ → ℝ := fun y => haarMother1D y * haarMother1D (2 * y - 1)
  have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
    simpa [f] using integral_haarMother1D_mul_right_child
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - k) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -k)
      (dyadicPower_ne_zero j) f integrable_haarMother1D_mul_right_child
    aesop
  calc
    ∫ x : ℝ, haar1D j k true x * haar1D _ _ true x ∂volume =
        ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
          f (dyadicPower j * x - k) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          unfold haar1D f
          simp [haarAtom1D]
          rw [haar1D_right_child_arg]
          ring
    _ = (haarScaleFactor j * haarScaleFactor _) *
        ∫ x : ℝ, f _ ∂volume := by
          rw [integral_const_mul]
    _ = 0 := by
          simp_all
section
variable (signature : Bool)

theorem integral_haar1D_mul_left_child_mother_any_signature :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) ((2 : ℤ) * k) true x ∂volume = 0 := by
  cases signature
  · let f : ℝ → ℝ := fun y => haarFather1D y * haarMother1D (2 * y)
    have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
      simpa [f] using integral_haarFather1D_mul_left_child_mother
    have haffine :
        ∫ x : ℝ, f (dyadicPower j * x - k) ∂volume =
          (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
      have h := integral_comp_mul_add_volume
        (a := dyadicPower j) (b := -k)
        (dyadicPower_ne_zero j) f integrable_haarFather1D_mul_left_child_mother
      aesop
    calc
      ∫ x : ℝ, haar1D j k false x * haar1D _ _ true x ∂volume =
          ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
            f (dyadicPower j * x - k) ∂volume := by
            refine integral_congr_ae (ae_of_all _ ?_)
            intro x
            unfold haar1D f
            simp [haarAtom1D]
            rw [haar1D_left_child_arg]
            ring
      _ = (haarScaleFactor j * haarScaleFactor _) *
          ∫ x : ℝ, f _ ∂volume := by
            rw [integral_const_mul]
      _ = 0 := by simp_all
  · exact integral_haar1D_mul_left_child_mother j k

theorem integral_haar1D_mul_right_child_mother_any_signature :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) ((2 : ℤ) * k + 1) true x ∂volume = 0 := by
  cases signature
  · let f : ℝ → ℝ := fun y => haarFather1D y * haarMother1D (2 * y - 1)
    have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
      simpa [f] using integral_haarFather1D_mul_right_child_mother
    have haffine :
        ∫ x : ℝ, f (dyadicPower j * x - k) ∂volume =
          (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
      have h := integral_comp_mul_add_volume
        (a := dyadicPower j) (b := -k)
        (dyadicPower_ne_zero j) f integrable_haarFather1D_mul_right_child_mother
      aesop
    calc
      ∫ x : ℝ, haar1D j k false x * haar1D _ _ true x ∂volume =
          ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
            f (dyadicPower j * x - k) ∂volume := by
            refine integral_congr_ae (ae_of_all _ ?_)
            intro x
            unfold haar1D f
            simp [haarAtom1D]
            rw [haar1D_right_child_arg]
            ring
      _ = (haarScaleFactor j * haarScaleFactor _) *
          ∫ x : ℝ, f _ ∂volume := by
            rw [integral_const_mul]
      _ = 0 := by simp_all
  · exact integral_haar1D_mul_right_child_mother j k

end

end
section
variable {y : ℝ}

theorem int_eq_zero_or_one_of_mem_Ico {n : ℤ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hz : 2 * y - (n : ℝ) ∈ Set.Ico (0 : ℝ) 1) :
    n = 0 ∨ n = 1 := by
  have hnlt_two_real : (n : ℝ) < 2 := by
    grind
  have hneg_one_lt_real : (-1) < (n : ℝ) := by
    grind
  have hnlt_two : n < 2 := by exact_mod_cast hnlt_two_real
  have hneg_one_lt : (-1) < n := by exact_mod_cast hneg_one_lt_real
  omega

/-- A next-scale dyadic child intersects a parent cell only for the two child cell labels. -/
theorem adjacent_child_overlap_cells {k l : ℤ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hz : 2 * y + 2 * (k : ℝ) - (l : ℝ) ∈ Set.Ico (0 : ℝ) 1) :
    l = (2 : ℤ) * k ∨ l = (2 : ℤ) * k + 1 := by
  have hz' : 2 * y - ((l - 2 * k : ℤ) : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    grind
  have h := int_eq_zero_or_one_of_mem_Ico hy hz'
  omega

end
section
variable (j k l : ℤ) (signature : Bool)
section
variable (hl0 : l ≠ (2 : ℤ) * k) (hl1 : l ≠ (2 : ℤ) * k + 1)
include hl0 hl1

/-- If an adjacent-scale child is not one of the two children of the parent cell, the 1D product is
pointwise zero. -/
theorem haar1D_mul_adjacent_child_mother_ne (x : ℝ) :
    haar1D j k signature x * haar1D (j + 1) l true x = 0 := by
  by_cases hparent : dyadicPower j * x - k ∈ Set.Ico 0 1
  · by_cases hchild : dyadicPower (j + 1) * x - l ∈ Set.Ico 0 1
    · have hchild' :
          2 * (dyadicPower j * x - k) + 2 * k - l ∈
            Set.Ico 0 1 := by
        convert hchild using 1
        rw [dyadicPower_add_one]
        ring
      have hoverlap := adjacent_child_overlap_cells (k := k) (l := l) hparent hchild'
      simp_all
    · have hzero : haar1D (j + 1) l true x = 0 := by
        unfold haar1D
        rw [haarAtom1D_eq_zero_of_notMem_Ico true hchild, mul_zero]
      simp_all
  · have hzero : haar1D j k signature x = 0 := by
      unfold haar1D
      rw [haarAtom1D_eq_zero_of_notMem_Ico signature hparent, mul_zero]
    simp_all

theorem integral_haar1D_mul_adjacent_child_mother_ne :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haar1D j k signature x * haar1D _ l true x ∂volume =
        ∫ x : ℝ, 0 ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          exact haar1D_mul_adjacent_child_mother_ne j k l signature hl0 hl1 x
    _ = 0 := by simp

end

theorem integral_haar1D_mul_adjacent_child_mother :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume = 0 := by
  by_cases hl0 : l = 2 * k
  · subst l
    exact integral_haar1D_mul_left_child_mother_any_signature j k signature
  · by_cases hl1 : l = 2 * k + 1
    · subst l
      exact integral_haar1D_mul_right_child_mother_any_signature j k signature
    · exact integral_haar1D_mul_adjacent_child_mother_ne j k l signature hl0 hl1

end

/-- The one-dimensional father space at scale `j`, spanned by all father translates. -/
@[expose]
noncomputable def haar1DFatherSubmodule (j : ℤ) :
    Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  Submodule.span ℝ (Set.range fun k : ℤ => haar1DLp j k false)

theorem haar1DLp_father_mem_fatherSubmodule (j k : ℤ) :
    haar1DLp j k false ∈ haar1DFatherSubmodule j := Submodule.subset_span ⟨k, rfl⟩

theorem inner_haar1DLp_eq_integral (j₁ k₁ : ℤ) (signature₁ : Bool)
    (j₂ k₂ : ℤ) (signature₂ : Bool) :
    ⟪haar1DLp j₁ k₁ signature₁, haar1DLp j₂ k₂ signature₂⟫_ℝ =
      ∫ x : ℝ, haar1D j₁ k₁ signature₁ x * haar1D j₂ k₂ signature₂ x ∂volume := by
  rw [haar1DLp, haar1DLp, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_haar1D j₁ k₁ signature₁).coeFn_toLp,
    (memLp_haar1D j₂ k₂ signature₂).coeFn_toLp] with x hx₁ hx₂
  simp [hx₁, hx₂, mul_comm]

theorem haar1DLp_mem_fatherSubmodule_succ (j k : ℤ) (signature : Bool) :
    haar1DLp j k signature ∈ haar1DFatherSubmodule (j + 1) := by
  cases signature
  · rw [haar1DLp_father_refine]
    apply Submodule.smul_mem
    apply Submodule.add_mem <;> exact haar1DLp_father_mem_fatherSubmodule _ _
  · rw [haar1DLp_mother_refine]
    apply Submodule.smul_mem
    apply Submodule.sub_mem <;> exact haar1DLp_father_mem_fatherSubmodule _ _

theorem haar1DFatherSubmodule_le_succ (j : ℤ) :
    haar1DFatherSubmodule j ≤ haar1DFatherSubmodule (j + 1) := by
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨k, rfl⟩
  exact haar1DLp_mem_fatherSubmodule_succ j k false

theorem inner_haar1DLp_adjacent_child_mother (j k l : ℤ) (signature : Bool) :
    ⟪haar1DLp j k signature, haar1DLp (j + 1) l true⟫_ℝ = 0 := by
  rw [inner_haar1DLp_eq_integral]
  exact integral_haar1D_mul_adjacent_child_mother j k l signature

theorem inner_haar1DFatherSubmodule_adjacent_mother (j l : ℤ)
    {v : Lp ℝ 2 (volume : Measure ℝ)} (hv : v ∈ haar1DFatherSubmodule j) :
    ⟪v, haar1DLp (j + 1) l true⟫_ℝ = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨k, rfl⟩
      exact inner_haar1DLp_adjacent_child_mother j k l false
  | zero =>
      simp
  | add x y _ _ hx hy =>
      rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx =>
      rw [inner_smul_left, hx, mul_zero]

theorem haar1DFatherSubmodule_le_add_nat (j : ℤ) (n : ℕ) :
    haar1DFatherSubmodule j ≤ haar1DFatherSubmodule (j + (n : ℤ)) := by
  induction n with
  | zero =>
      intro v hv
      simpa using hv
  | succ n ih =>
      intro v hv
      have hvnext :=
        haar1DFatherSubmodule_le_succ _ (ih hv)
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_assoc] using hvnext

theorem haar1DLp_mem_fatherSubmodule_add_nat_succ (j k : ℤ)
    (signature : Bool) (n : ℕ) :
    haar1DLp j k signature ∈ haar1DFatherSubmodule (j + ((n + 1 : ℕ) : ℤ)) := by
  have hfirst :=
    haar1DLp_mem_fatherSubmodule_succ j k signature
  have hmem :=
    (haar1DFatherSubmodule_le_add_nat _ n) hfirst
  grind
section
variable (j k l : ℤ) (signature : Bool) (n : ℕ)

theorem inner_haar1DLp_finer_mother_nat_succ_succ :
    ⟪haar1DLp j k signature,
      haar1DLp (j + ((n + 1 : ℕ) : ℤ) + 1) l true⟫_ℝ = 0 := by
  exact inner_haar1DFatherSubmodule_adjacent_mother
    (j + ((n + 1 : ℕ) : ℤ)) l
    (haar1DLp_mem_fatherSubmodule_add_nat_succ j k signature n)

theorem inner_haar1DLp_finer_mother_nat_succ :
    ⟪haar1DLp j k signature,
      haar1DLp (j + ((n + 1 : ℕ) : ℤ)) l true⟫_ℝ = 0 := by
  cases n with
  | zero =>
      simpa using inner_haar1DLp_adjacent_child_mother j k l signature
  | succ n =>
      have h :=
        inner_haar1DLp_finer_mother_nat_succ_succ j k l signature n
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one,
        Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using h

theorem integral_haar1D_mul_finer_mother_nat_succ :
    ∫ x : ℝ,
      haar1D j k signature x *
        haar1D (j + ((n + 1 : ℕ) : ℤ)) l true x ∂volume = 0 := by
  simpa [inner_haar1DLp_eq_integral] using (inner_haar1DLp_finer_mother_nat_succ j k l signature n)

end

end GaussianFields

end
