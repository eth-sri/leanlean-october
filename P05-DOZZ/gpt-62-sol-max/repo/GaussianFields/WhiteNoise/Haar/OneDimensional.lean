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
noncomputable def haar1D (j : ℤ) (k : ℤ) (signature : Bool) : ℝ → ℝ :=
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
  have ha : 0 < a := dyadicPower_pos j
  have hane : a ≠ 0 := ne_of_gt ha
  constructor
  · intro hx
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hx.1 ha.le
      have hk : a * ((k : ℝ) / a) = (k : ℝ) := by
        field_simp [hane]
      linarith
    · have hmul := mul_lt_mul_of_pos_left hx.2 ha
      have hk : a * (((k : ℝ) + 1) / a) = (k : ℝ) + 1 := by
        field_simp [hane]
      linarith
  · intro hx
    constructor
    · have hle : (k : ℝ) ≤ a * x := by linarith [hx.1]
      exact (div_le_iff₀ ha).2 (by linarith)
    · have hlt : a * x < (k : ℝ) + 1 := by linarith [hx.2]
      exact (lt_div_iff₀ ha).2 (by linarith)

theorem measurableSet_dyadicInterval :
    MeasurableSet (dyadicInterval j k) := by
  unfold dyadicInterval
  exact measurableSet_Ico

theorem haar1D_father_eq_indicator_dyadicInterval (x : ℝ) :
    haar1D j k false x =
      haarScaleFactor j *
        Set.indicator (dyadicInterval j k) (fun _ : ℝ => (1 : ℝ)) x := by
  unfold haar1D haarAtom1D haarFather1D
  by_cases hx : x ∈ dyadicInterval j k
  · have hx'  :=
      (mem_dyadicInterval_iff j k x).1 hx
    simp [hx, hx']
  · have hx'  :=
      mt (mem_dyadicInterval_iff j k x).2 hx
    simp [hx, hx']

end

@[fun_prop]
theorem measurable_haar1D (j : ℤ) (k : ℤ) (signature : Bool) :
    Measurable (haar1D j k signature) := by
  unfold haar1D
  exact measurable_const.mul
    ((measurable_haarAtom1D signature).comp (by fun_prop))

theorem integrable_haarFather1D_affine (j k : ℤ) :
    Integrable (fun x : ℝ => haarFather1D (dyadicPower j * x - (k : ℝ)))
      (volume : Measure ℝ) := by
  have hshift :
      Integrable (fun y : ℝ => haarFather1D (y - (k : ℝ))) (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using integrable_haarFather1D.comp_add_right (-(k : ℝ))
  simpa [sub_eq_add_neg] using hshift.comp_mul_left' (dyadicPower_ne_zero j)

section
variable (j k : ℤ) (signature : Bool)

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
  · exact (measurable_haar1D j k signature).aestronglyMeasurable

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
  let f  := fun y => haarAtom1D signature₁ y * haarAtom1D signature₂ y
  have hbase := integral_haarAtom1D_mul_haarAtom1D signature₁ signature₂
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume (dyadicPower j) (-(k : ℝ)) f
    have hpos  := dyadicPower_pos j
    simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos), f] using h
  calc
    ∫ x : ℝ, haar1D j k signature₁ x * haar1D j k signature₂ x ∂volume =
        ∫ x : ℝ, dyadicPower j * f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          change haar1D j k signature₁ x * haar1D j k signature₂ x =
            dyadicPower j * f (dyadicPower j * x - (k : ℝ))
          rw [haar1D_mul_haar1D_same_scale_cell]
    _ = dyadicPower j *
        ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          rw [integral_const_mul]
    _ = if signature₁ = signature₂ then 1 else 0 := by
          rw [haffine, hbase]
          by_cases hsig : signature₁ = signature₂
          · simp [hsig, mul_inv_cancel₀ (dyadicPower_ne_zero j)]
          · simp [hsig]

end

section
variable (j k₁ k₂ : ℤ) (signature₁ signature₂ : Bool)

/-- One-dimensional Haar atoms at the same scale but in distinct cells have pointwise-zero
product. -/
theorem haar1D_mul_haar1D_same_scale_cell_ne (hk : k₁ ≠ k₂) (x : ℝ) :
    haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x = 0 := by
  unfold haar1D
  let a₁ := haarAtom1D signature₁ (dyadicPower j * x - (k₁ : ℝ))
  let a₂ := haarAtom1D signature₂ (dyadicPower j * x - (k₂ : ℝ))
  have hprod : a₁ * a₂ = 0 := by
    apply haarAtom1D_mul_eq_zero_of_cells_ne <;> assumption
  grind

/-- One-dimensional Haar atoms at the same scale but in distinct cells are orthogonal. -/
theorem integral_haar1D_mul_haar1D_same_scale_cell_ne (hk : k₁ ≠ k₂) :
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume =
        ∫ x : ℝ, 0 ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          apply haar1D_mul_haar1D_same_scale_cell_ne <;> assumption
    _ = 0 := by simp

/-- Same-scale one-dimensional Haar inner products reduce to equality of cells and signatures. -/
theorem integral_haar1D_mul_haar1D_same_scale :
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume =
      if k₁ = k₂ then if signature₁ = signature₂ then 1 else 0 else 0 := by
  by_cases hk : k₁ = k₂
  · subst k₂
    rw [ite_eq_left rfl]
    exact integral_haar1D_mul_haar1D_same_scale_cell ..
  · rw [ite_eq_right hk]
    apply integral_haar1D_mul_haar1D_same_scale_cell_ne <;> assumption

end

section
variable (j k : ℤ)

private theorem haar1D_child_arg (b : Bool) (x : ℝ) :
    dyadicPower (j + 1) * x - (((2 : ℤ) * k + if b then 1 else 0 : ℤ) : ℝ) =
      2 * (dyadicPower j * x - (k : ℝ)) - (if b then 1 else 0) := by
  rw [dyadicPower_add_one]
  cases b <;> push_cast <;> ring

/-- Pointwise Haar packet refinement at either signature. -/
private theorem haar1D_refine (s : Bool) (x : ℝ) :
    haar1D j k s x = (Real.sqrt 2)⁻¹ *
      (haar1D (j + 1) ((2 : ℤ) * k) false x + (if s then -1 else 1) *
        haar1D (j + 1) ((2 : ℤ) * k + 1) false x) := by
  have hl := haar1D_child_arg j k false x
  have hr := haar1D_child_arg j k true x
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, sub_zero] at hl
  simp only [↓reduceIte] at hr
  rw [haar1D, haarAtom1D_refine, haar1D, haar1D, hl, hr, haarScaleFactor_add_one]
  simp only [haarAtom1D, Bool.false_eq_true, ↓reduceIte]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs]

/-- Inversion of the two-signature refinement identity. -/
theorem haar1D_child_father_refine_bool (side : Bool) (x : ℝ) :
    haar1D (j + 1) ((2 : ℤ) * k + if side then 1 else 0) false x =
      ∑ signature : Bool,
        ((Real.sqrt 2)⁻¹ * (if side && signature then (-1 : ℝ) else 1)) *
          haar1D j k signature x := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  cases side <;> simp [haar1D_refine j k false x, haar1D_refine j k true x] <;>
    field_simp [hs] <;> ring_nf <;> norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The two pointwise refinements induce a single refinement in `L²(R)`. -/
private theorem haar1DLp_refine (s : Bool) :
    haar1DLp j k s = (Real.sqrt 2)⁻¹ •
      (haar1DLp (j + 1) ((2 : ℤ) * k) false + ((if s then -1 else 1 : ℝ) •
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false)) := by
  have h := (memLp_haar1D j k s).toLp_congr
    (((memLp_haar1D (j + 1) ((2 : ℤ) * k) false).add
      ((memLp_haar1D (j + 1) ((2 : ℤ) * k + 1) false).const_smul (if s then -1 else (1 : ℝ)))).const_smul
        (Real.sqrt 2)⁻¹) (ae_of_all _ (haar1D_refine j k s))
  assumption

private theorem integral_haar1D_mul_child_mother (s b : Bool) :
    ∫ x : ℝ, haar1D j k s x * haar1D (j + 1) ((2 : ℤ) * k + if b then 1 else 0) true x ∂volume = 0 := by
  let f (x : ℝ) := haarAtom1D s x * haarMother1D (2 * x - (if b then 1 else 0))
  have he (x : ℝ) : haar1D j k s x * haar1D (j + 1) ((2 : ℤ) * k + if b then 1 else 0) true x =
      (haarScaleFactor j * haarScaleFactor (j + 1)) * f (dyadicPower j * x - (k : ℝ)) := by
    simp only [haar1D, haar1D_child_arg, haarAtom1D, ↓reduceIte, f]
    ring
  simp_rw [he, integral_const_mul, sub_eq_add_neg]
  rw [integral_comp_mul_add_volume, show ∫ x, f x = 0 from integral_haarAtom1D_mul_child_mother s b,
    mul_zero, mul_zero]

end

theorem int_eq_zero_or_one_of_mem_Ico {y : ℝ} {n : ℤ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hz : 2 * y - (n : ℝ) ∈ Set.Ico (0 : ℝ) 1) :
    n = 0 ∨ n = 1 := by
  have hnlt_two_real : (n : ℝ) < 2 := by
    linarith [hz.1, hy.2]
  have hneg_one_lt_real : (-1 : ℝ) < (n : ℝ) := by
    linarith [hz.2, hy.1]
  have hnlt_two : n < 2 := by exact_mod_cast hnlt_two_real
  have hneg_one_lt : (-1 : ℤ) < n := by exact_mod_cast hneg_one_lt_real
  omega

/-- A next-scale dyadic child intersects a parent cell only for the two child cell labels. -/
theorem adjacent_child_overlap_cells {y : ℝ} {k l : ℤ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hz : 2 * y + 2 * (k : ℝ) - (l : ℝ) ∈ Set.Ico (0 : ℝ) 1) :
    l = (2 : ℤ) * k ∨ l = (2 : ℤ) * k + 1 := by
  have hz' : 2 * y - ((l - (2 : ℤ) * k : ℤ) : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    convert hz using 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    ring
  have h := int_eq_zero_or_one_of_mem_Ico hy hz'
  rcases h with h | h
  · left
    omega
  · right
    omega

section
variable (j k l : ℤ) (signature : Bool) (hl0 : l ≠ (2 : ℤ) * k) (hl1 : l ≠ (2 : ℤ) * k + 1)
include hl0 hl1

/-- If an adjacent-scale child is not one of the two children of the parent cell, the 1D product is
pointwise zero. -/
theorem haar1D_mul_adjacent_child_mother_ne (x : ℝ) :
    haar1D j k signature x * haar1D (j + 1) l true x = 0 := by
  by_cases hparent : dyadicPower j * x - (k : ℝ) ∈ Set.Ico (0 : ℝ) 1
  · by_cases hchild : dyadicPower (j + 1) * x - (l : ℝ) ∈ Set.Ico (0 : ℝ) 1
    · have hchild' :
          2 * (dyadicPower j * x - (k : ℝ)) + 2 * (k : ℝ) - (l : ℝ) ∈
            Set.Ico (0 : ℝ) 1 := by
        convert hchild using 1
        rw [dyadicPower_add_one]
        ring
      have hoverlap := adjacent_child_overlap_cells (k := k) (l := l) hparent hchild'
      rcases hoverlap with h | h
      · exact False.elim (hl0 h)
      · exact False.elim (hl1 h)
    · have hzero : haar1D (j + 1) l true x = 0 := by
        unfold haar1D
        rw [haarAtom1D_eq_zero_of_notMem_Ico true hchild, mul_zero]
      rw [hzero, mul_zero]
  · have hzero : haar1D j k signature x = 0 := by
      unfold haar1D
      rw [haarAtom1D_eq_zero_of_notMem_Ico signature hparent, mul_zero]
    rw [hzero, zero_mul]

theorem integral_haar1D_mul_adjacent_child_mother_ne :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume =
        ∫ x : ℝ, 0 ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          apply haar1D_mul_adjacent_child_mother_ne <;> assumption
    _ = 0 := by simp

end

theorem integral_haar1D_mul_adjacent_child_mother (j k l : ℤ)
    (signature : Bool) :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume = 0 := by
  by_cases hl0 : l = (2 : ℤ) * k
  · subst l
    simpa using integral_haar1D_mul_child_mother j k signature false
  · by_cases hl1 : l = (2 : ℤ) * k + 1
    · subst l
      simpa using integral_haar1D_mul_child_mother j k signature true
    · apply integral_haar1D_mul_adjacent_child_mother_ne <;> assumption

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
  rw [haar1DLp_refine]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _
    (haar1DLp_father_mem_fatherSubmodule (j + 1) (2 * k))
    (Submodule.smul_mem _ _ (haar1DLp_father_mem_fatherSubmodule (j + 1) (2 * k + 1))))

theorem haar1DFatherSubmodule_le_succ (j : ℤ) :
    haar1DFatherSubmodule j ≤ haar1DFatherSubmodule (j + 1) := by
  rw [haar1DFatherSubmodule, haar1DFatherSubmodule]
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨k, rfl⟩
  exact haar1DLp_mem_fatherSubmodule_succ j k false

theorem inner_haar1DLp_adjacent_child_mother (j k l : ℤ) (signature : Bool) :
    ⟪haar1DLp j k signature, haar1DLp (j + 1) l true⟫_ℝ = 0 := by
  rw [inner_haar1DLp_eq_integral]
  exact integral_haar1D_mul_adjacent_child_mother ..

theorem inner_haar1DFatherSubmodule_adjacent_mother (j l : ℤ)
    {v : Lp ℝ 2 (volume : Measure ℝ)} (hv : v ∈ haar1DFatherSubmodule j) :
    ⟪v, haar1DLp (j + 1) l true⟫_ℝ = 0 := by
  rw [haar1DFatherSubmodule] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨k, rfl⟩
      exact inner_haar1DLp_adjacent_child_mother ..
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
      simp
  | succ n ih =>
      intro v hv
      have hvn  := ih hv
      have hvnext := haar1DFatherSubmodule_le_succ (j + (n : ℤ)) hvn
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_assoc] using hvnext

theorem haar1DLp_mem_fatherSubmodule_add_nat_succ (j k : ℤ)
    (signature : Bool) (n : ℕ) :
    haar1DLp j k signature ∈ haar1DFatherSubmodule (j + ((n + 1 : ℕ) : ℤ)) := by
  have hfirst  :=
    haar1DLp_mem_fatherSubmodule_succ j k signature
  have hle := haar1DFatherSubmodule_le_add_nat (j + 1) n
  have hmem  :=
    hle hfirst
  simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_assoc,
    add_comm, add_left_comm] using hmem

section
variable (j k l : ℤ) (signature : Bool) (n : ℕ)

theorem inner_haar1DLp_finer_mother_nat_succ_succ :
    ⟪haar1DLp j k signature,
      haar1DLp (j + ((n + 1 : ℕ) : ℤ) + 1) l true⟫_ℝ = 0 := inner_haar1DFatherSubmodule_adjacent_mother
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
  have h := inner_haar1DLp_finer_mother_nat_succ j k l signature n
  simpa [inner_haar1DLp_eq_integral] using h

end

end GaussianFields

end
