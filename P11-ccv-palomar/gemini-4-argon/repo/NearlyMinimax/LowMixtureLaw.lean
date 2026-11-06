module
public import NearlyMinimax.LowSmoothnessPrior
public import Mathlib
public import NearlyMinimax.ParametricLower
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
section
def clampUnit (x : ℝ) : ℝ := min 1 (max 0 x)
theorem clampUnit_mem (x ) : clampUnit x ∈ Icc ↑0 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _
theorem clampUnit_eq (x ) (hx : x ∈ Icc (0 : ℝ) 1) : clampUnit x = x := by
  simp [clampUnit, max_eq_right hx.1, min_eq_right hx.2]
def gridTent (k ) (j : Fin (k + 1)) (x : ℝ) : ℝ :=
  max 0 (1 - |↑k * clampUnit x - j.val|)
theorem gridTent_nonneg (k j x) : 0 ≤ gridTent k j x :=
  le_max_left _ _
theorem gridTent_continuous (k j) : Continuous (gridTent k j) := by
  unfold gridTent clampUnit
  fun_prop
def gridTentEnergy (k : ℕ) (x : ℝ) : ℝ := ∑ j : Fin (k + 1), gridTent k j x ^ 2
theorem gridTentEnergy_lower (k x) : (1 / 4 ) ≤ gridTentEnergy k x := by
  have h_gridTent_cover : ∃ j, (1 / 2 ) ≤ gridTent k j x := by
    let t := ↑k * clampUnit x
    have  := mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1
    have : t ≤ k := by
      simpa [t] using mul_le_mul_of_nonneg_left (clampUnit_mem x).2 (Nat.cast_nonneg k)
    let j := Nat.floor (t + 1 / 2)
    have : ↑j ≤ t + 1 / 2 := Nat.floor_le (by linarith)
    have : t + 1 / 2 < ↑j + 1 := Nat.lt_floor_add_one _
    have : j ≤ k := by
      by_contra h
      have hj : (k : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : k + 1 ≤ j)
      linarith
    refine ⟨⟨j, by omega⟩, ?_⟩
    have : |t - j| ≤ (1 / 2 ) := abs_le.mpr ⟨by linarith, by linarith⟩
    exact le_trans (by simpa [t] using (show (1 / 2 ) ≤ 1 - |t - j| by linarith))
      (le_max_right _ _)
  obtain ⟨j, hj⟩ := h_gridTent_cover
  have hsq : (1 / 4 ) ≤ gridTent k j x ^ 2 := by nlinarith
  exact hsq.trans (Finset.single_le_sum (fun i _ => sq_nonneg (gridTent k i x)) (Finset.mem_univ j))
theorem gridTentEnergy_pos (k x) : 0 < gridTentEnergy k x :=
  lt_of_lt_of_le (by norm_num) (gridTentEnergy_lower k x)
def gridWindow (k ) (j : Fin (k + 1)) (x : ℝ) : ℝ :=
  gridTent k j x / Real.sqrt (gridTentEnergy k x)
theorem gridWindow_nonneg (k j x) : 0 ≤ gridWindow k j x :=
  div_nonneg (gridTent_nonneg k j x) (Real.sqrt_nonneg _)
theorem gridWindow_continuous (k j) : Continuous (gridWindow k j) := by
  exact (gridTent_continuous k j).div (continuous_finsetSum _ (fun j _ => (gridTent_continuous k j).pow 2)).sqrt
    (fun x => ne_of_gt (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)))
theorem gridWindow_square_partition (k x) :
    (∑ j : Fin (k + 1), gridWindow k j x ^ 2) = 1 := by
  simp only [gridWindow, div_pow, Real.sq_sqrt (gridTentEnergy_pos k x).le]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gridTentEnergy_pos k x))
theorem gridWindow_le_one (k j x) : gridWindow k j x ≤ 1 := by
  have : gridWindow k j x ^ 2 ≤ 1 := by
    rw [← gridWindow_square_partition k x]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (gridWindow k i x)) (Finset.mem_univ j)
  nlinarith [gridWindow_nonneg k j x]
def gridTensorWindow (d k ) (j : Fin d → Fin (k + 1)) (x : Covariate d) : ℝ :=
  ∏ i, gridWindow k (j i) (x i)
theorem gridTensorWindow_continuous (d k j) :
    Continuous (gridTensorWindow d k j) :=
  continuous_finsetProd _ (fun i _ => (gridWindow_continuous k (j i)).comp (continuous_apply i))
theorem gridTensorWindow_nonneg (d k j x) :
    0 ≤ gridTensorWindow d k j x := Finset.prod_nonneg (fun i _ => gridWindow_nonneg k (j i) (x i))
theorem gridTensorWindow_le_one (d k j x) :
    gridTensorWindow d k j x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => gridWindow_nonneg k (j i) (x i))
    (fun i _ => gridWindow_le_one k (j i) (x i))
def gridTentActive (k ) (x : ℝ) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun j => gridTent k j x ≠ 0)
theorem gridTent_active_card (k x) : (gridTentActive k x).card ≤ 2 := by
  have hsub : (gridTentActive k x).image Fin.val ⊆
      {Nat.floor (↑k * clampUnit x), Nat.floor (↑k * clampUnit x) + 1} := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have h_gridTent_active_indices : i.val = Nat.floor (↑k * clampUnit x) ∨
        i.val = Nat.floor (↑k * clampUnit x) + 1 := by
      let t := ↑k * clampUnit x
      let m := Nat.floor t
      have hd : |t - i.val| < 1 := by
        by_contra h
        have he : gridTent k i x = 0 := max_eq_left (by dsimp [t] at h; linarith)
        exact ((Finset.mem_filter.mp hi).2) he
      have  := Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1)
      have  := Nat.lt_floor_add_one t
      have : m ≤ i.val := by
        by_contra h
        have : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : i.val + 1 ≤ m)
        linarith [(abs_lt.mp hd).2]
      have : i.val ≤ m + 1 := by
        by_contra h
        have : (m : ℝ) + 2 ≤ i.val := by exact_mod_cast (by omega : m + 2 ≤ i.val)
        linarith [(abs_lt.mp hd).1]
      change i.val = m ∨ i.val = m + 1
      omega
    rcases h_gridTent_active_indices with h | h <;> simp [h]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  exact hcard.trans (by simp)
theorem gridWindow_eq_zero_iff (k j x) :
    gridWindow k j x = 0 ↔ gridTent k j x = 0 := by
  simp only [gridWindow, div_eq_zero_iff, ne_of_gt (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)),
    or_false]
def gridTensorActive (d k ) (x : Covariate d) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridTentActive k (x i))
theorem gridTensorWindow_eq_zero_of_not_active (d k j x) (hj : j ∉ gridTensorActive d k x) : gridTensorWindow d k j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp (by simpa [gridTensorActive, Fintype.mem_piFinset] using hj)
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by apply (gridWindow_eq_zero_iff k (j i) (x i)).mpr; simpa [gridTentActive] using hi)
theorem gridTensor_active_card (d k x) : (gridTensorActive d k x).card ≤ 2 ^ d := by
  rw [gridTensorActive, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 2 := Finset.prod_le_prod (fun i _ => gridTent_active_card k (x i))
    _ = _ := by simp
theorem clampUnit_modulus (x y ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  have hmax : |max 0 x - max 0 y| ≤ |x - y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] using
      abs_max_sub_max_le_max ↑0 x 0 y
  have hmin : |clampUnit x - clampUnit y| ≤ |max 0 x - max 0 y| := by
    simpa only [clampUnit, sub_self, abs_zero,
      max_eq_right (abs_nonneg (max 0 x - max 0 y))] using
      abs_min_sub_min_le_max ↑1 (max 0 x) 1 (max 0 y)
  exact hmin.trans hmax
theorem gridTent_modulus (k ) (j : Fin (k + 1)) (x y ) :
    |gridTent k j x - gridTent k j y| ≤ ↑k * |x - y| := by
  have h := abs_max_sub_max_le_max ↑0
    (1 - |↑k * clampUnit x - j.val|) 0 (1 - |↑k * clampUnit y - j.val|)
  have hr : max 0 |(1 - |↑k * clampUnit x - j.val|) -
      (1 - |↑k * clampUnit y - j.val|)| =
      abs (|↑k * clampUnit x - j.val| - |↑k * clampUnit y - j.val|) := by
    rw [max_eq_right (abs_nonneg _), sub_sub_sub_cancel_left, abs_sub_comm]
  calc
    _ ≤ abs (|↑k * clampUnit x - j.val| - |↑k * clampUnit y - j.val|) := by simpa only [gridTent, sub_self, abs_zero, hr] using h
    _ ≤ |(↑k * clampUnit x - j.val) - (↑k * clampUnit y - j.val)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = ↑k * |clampUnit x - clampUnit y| := by
      rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (clampUnit_modulus x y) (Nat.cast_nonneg k)
theorem bounded_product_modulus  [DecidableEq ι] (s )
    (f g : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have : |∏ j ∈ s, f j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hh := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    rw [show f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
      (f i - g i) * (∏ j ∈ s, f j) + g i * ((∏ j ∈ s, f j) - (∏ j ∈ s, g j)) by ring]
    calc
      _ ≤ |(f i - g i) * (∏ j ∈ s, f j)| +
          |g i * ((∏ j ∈ s, f j) - (∏ j ∈ s, g j))| := abs_add_le _ _
      _ ≤ |f i - g i| + ∑ j ∈ s, |f j - g j| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (by nlinarith [abs_nonneg (f i - g i)])
          (by simpa only [one_mul] using mul_le_mul (hg i (Finset.mem_insert_self _ _)) hh (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
def gridPriorField (d k ) (η : ℝ) (ξ : (Fin d → Fin (k + 1)) → Fin 3)
    (x : Covariate d) : ℝ :=
  η * ∑ j, gridTensorWindow d k j x * ternaryValue 1 (ξ j)
theorem gridPriorField_continuous (d k η ξ) : Continuous (gridPriorField d k η ξ) :=
  (continuous_finsetSum _ (fun j _ => (gridTensorWindow_continuous d k j).mul_const _)).const_mul _
theorem ternaryValue_one_abs_le (y ) : |ternaryValue 1 y| ≤ 1 := by
  fin_cases y <;> norm_num [ternaryValue]
theorem gridPriorField_abs_bound (d k η) (hη : 0 ≤ η)
    (ξ x) :
    |gridPriorField d k η ξ x| ≤ ↑2 ^ d * η := by
  have heq : (∑ j, gridTensorWindow d k j x * ternaryValue 1 (ξ j)) =
      ∑ j ∈ gridTensorActive d k x, gridTensorWindow d k j x * ternaryValue 1 (ξ j) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [gridTensorWindow_eq_zero_of_not_active d k j x hj]
  rw [gridPriorField, abs_mul, abs_of_nonneg hη, heq]
  have hsum : |∑ j ∈ gridTensorActive d k x,
      gridTensorWindow d k j x * ternaryValue 1 (ξ j)| ≤ ↑2 ^ d := by
    calc
      _ ≤ ∑ j ∈ gridTensorActive d k x, |gridTensorWindow d k j x * ternaryValue 1 (ξ j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ gridTensorActive d k x, ↑1 := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (gridTensorWindow_nonneg d k j x)]
        simpa only [one_mul] using mul_le_mul (gridTensorWindow_le_one d k j x)
          (ternaryValue_one_abs_le (ξ j)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast gridTensor_active_card d k x
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsum hη
theorem gridPriorField_lipschitz_bound (d k η) (hη : 0 ≤ η)
    (ξ x y) :
    |gridPriorField d k η ξ x - gridPriorField d k η ξ y| ≤
      68 * ↑2 ^ d * (d + 1) * η * k * euclideanNorm (x - y) := by
  have h_gridTent_le_one (j : Fin (k + 1)) (x) : gridTent k j x ≤ 1 := max_le (by norm_num) (by linarith [abs_nonneg (↑k * clampUnit x - j.val)])
  have h_gridTentEnergy_sqrt_lower (x) : (1 / 2 ) ≤ Real.sqrt (gridTentEnergy k x) := by
    nlinarith [Real.sqrt_nonneg (gridTentEnergy k x),
      Real.sq_sqrt (gridTentEnergy_pos k x).le, gridTentEnergy_lower k x]
  let S := gridTensorActive d k x ∪ gridTensorActive d k y
  have hcard : ↑S.card ≤ 2 * (2 : ℝ) ^ d := by
    have h := (Finset.card_union_le (gridTensorActive d k x) (gridTensorActive d k y)).trans
      (Nat.add_le_add (gridTensor_active_card d k x) (gridTensor_active_card d k y))
    have hcast : ((gridTensorActive d k x ∪ gridTensorActive d k y).card : ℝ) ≤
        (2 : ℝ) ^ d + (2 : ℝ) ^ d := by exact_mod_cast h
    simpa only [S, two_mul] using hcast
  have hzero (j : Fin d → Fin (k + 1)) (hj : j ∉ S) :
      (gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j) = 0 := by
    have hx := gridTensorWindow_eq_zero_of_not_active d k j x
      (fun h => hj (Finset.mem_union_left _ h))
    have hy := gridTensorWindow_eq_zero_of_not_active d k j y
      (fun h => hj (Finset.mem_union_right _ h))
    simp [hx, hy]
  have hn : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
  have hpoint (j : Fin d → Fin (k + 1)) :
      |(gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j)| ≤
        34 * k * d * euclideanNorm (x - y) := by
    rw [abs_mul]
    have h_gridTensorWindow_modulus : |gridTensorWindow d k j x - gridTensorWindow d k j y| ≤
      34 * k * d * euclideanNorm (x - y) := by
      have hh := bounded_product_modulus (Finset.univ : Finset (Fin d))
        (fun i => gridWindow k (j i) (x i)) (fun i => gridWindow k (j i) (y i))
        (fun i _ => by rw [abs_of_nonneg (gridWindow_nonneg k (j i) (x i))]; exact gridWindow_le_one k (j i) (x i))
        (fun i _ => by rw [abs_of_nonneg (gridWindow_nonneg k (j i) (y i))]; exact gridWindow_le_one k (j i) (y i))
      calc
        _ ≤ ∑ i, |gridWindow k (j i) (x i) - gridWindow k (j i) (y i)| := hh
        _ ≤ ∑ _i : Fin d, 34 * ↑k * euclideanNorm (x - y) := by
          apply Finset.sum_le_sum
          intro i _
          have h_gridWindow_modulus (j : Fin (k + 1)) x y : |gridWindow k j x - gridWindow k j y| ≤ 34 * k * |x - y| := by
            let A := Real.sqrt (gridTentEnergy k x)
            let B := Real.sqrt (gridTentEnergy k y)
            have  := h_gridTentEnergy_sqrt_lower x
            have  := h_gridTentEnergy_sqrt_lower y
            have hAp : 0 < A := by linarith
            have hBp : 0 < B := by linarith
            have : (1 / 4 ) ≤ A * B := by nlinarith
            have : |B - A| ≤ 8 * k * |x - y| := by
              have hx := h_gridTentEnergy_sqrt_lower x
              have hy := h_gridTentEnergy_sqrt_lower y
              have hid : |gridTentEnergy k x - gridTentEnergy k y| =
                  |Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y)| *
                    (Real.sqrt (gridTentEnergy k x) + Real.sqrt (gridTentEnergy k y)) := by
                conv_lhs => rw [← Real.sq_sqrt (gridTentEnergy_pos k x).le, ← Real.sq_sqrt (gridTentEnergy_pos k y).le]
                rw [show Real.sqrt (gridTentEnergy k x) ^ 2 - Real.sqrt (gridTentEnergy k y) ^ 2 =
                  (Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y)) *
                    (Real.sqrt (gridTentEnergy k x) + Real.sqrt (gridTentEnergy k y)) by ring,
                  abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg (gridTentEnergy k x))
                    (Real.sqrt_nonneg (gridTentEnergy k y)))]
              have h_gridTentEnergy_modulus : |gridTentEnergy k x - gridTentEnergy k y| ≤ 8 * k * |x - y| := by
                let S := gridTentActive k x ∪ gridTentActive k y
                have hcard : S.card ≤ 4 := (Finset.card_union_le _ _).trans
                  (by have hx := gridTent_active_card k x; have hy := gridTent_active_card k y; omega)
                have hzero (j : Fin (k + 1)) (hj : j ∉ S) :
                    gridTent k j x ^ 2 - gridTent k j y ^ 2 = 0 := by
                  have hx : gridTent k j x = 0 := by
                    have : j ∉ gridTentActive k x := fun h => hj (Finset.mem_union_left _ h)
                    simpa [gridTentActive] using this
                  have hy : gridTent k j y = 0 := by
                    have : j ∉ gridTentActive k y := fun h => hj (Finset.mem_union_right _ h)
                    simpa [gridTentActive] using this
                  simp [hx, hy]
                have hpoint (j : Fin (k + 1)) :
                    |gridTent k j x ^ 2 - gridTent k j y ^ 2| ≤ 2 * k * |x - y| := by
                  have hx0 := gridTent_nonneg k j x
                  have hy0 := gridTent_nonneg k j y
                  have := h_gridTent_le_one j x
                  have := h_gridTent_le_one j y
                  rw [show gridTent k j x ^ 2 - gridTent k j y ^ 2 =
                    (gridTent k j x - gridTent k j y) * (gridTent k j x + gridTent k j y) by ring,
                    abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
                  nlinarith [gridTent_modulus k j x y, abs_nonneg (gridTent k j x - gridTent k j y),
                    mul_nonneg (sub_nonneg.mpr (gridTent_modulus k j x y)) (add_nonneg hx0 hy0)]
                change |(∑ j, gridTent k j x ^ 2) - (∑ j, gridTent k j y ^ 2)| ≤ _
                rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S)
                  (fun j _ hj => hzero j hj)]
                calc
                  _ ≤ ∑ j ∈ S, |gridTent k j x ^ 2 - gridTent k j y ^ 2| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ _j ∈ S, 2 * ↑k * |x - y| := Finset.sum_le_sum (fun j _ => hpoint j)
                  _ ≤ _ := by
                    simp only [Finset.sum_const, nsmul_eq_mul]
                    have hcast : (S.card : ℝ) ≤ 4 := by exact_mod_cast hcard
                    nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
              have hb := h_gridTentEnergy_modulus
              simpa only [abs_sub_comm] using (by rw [hid] at hb; nlinarith [abs_nonneg (Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y))])
            have : |(gridTent k j x - gridTent k j y) / A| ≤ 2 * k * |x - y| := by
              rw [abs_div, abs_of_pos hAp]
              apply (div_le_iff₀ hAp).mpr
              have htent := gridTent_modulus k j x y
              nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
            have : |gridTent k j y * (B - A) / (A * B)| ≤ 32 * k * |x - y| := by
              rw [abs_div, abs_mul, abs_of_nonneg (gridTent_nonneg k j y), abs_of_pos (mul_pos hAp hBp)]
              apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
              have htent := h_gridTent_le_one j y
              have := gridTent_nonneg k j y
              have habs := abs_nonneg (B - A)
              nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y)),
                mul_nonneg (sub_nonneg.mpr htent) habs]
            have hid : gridWindow k j x - gridWindow k j y =
                (gridTent k j x - gridTent k j y) / A + gridTent k j y * (B - A) / (A * B) := by
              change gridTent k j x / A - gridTent k j y / B = _
              field_simp [ne_of_gt hAp, ne_of_gt hBp]
              ring
            rw [hid]
            exact (abs_add_le _ _).trans (by linarith)
          have h_coordinate_abs_le_euclideanNorm (x : Covariate d) : |x i| ≤ euclideanNorm x := by
            have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
              Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
            have : euclideanNorm x ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
            have : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
            nlinarith [sq_abs (x i), abs_nonneg (x i)]
          exact (h_gridWindow_modulus (j i) (x i) (y i)).trans
            (mul_le_mul_of_nonneg_left (h_coordinate_abs_le_euclideanNorm (x - y)) (by positivity))
        _ = _ := by simp; ring
    simpa only [mul_one] using mul_le_mul h_gridTensorWindow_modulus
      (ternaryValue_one_abs_le (ξ j)) (abs_nonneg _) (by positivity :
        0 ≤ 34 * ↑k * d * euclideanNorm (x - y))
  have hsum : |∑ j ∈ S, (gridTensorWindow d k j x - gridTensorWindow d k j y) *
      ternaryValue 1 (ξ j)| ≤ 68 * ↑2 ^ d * (d + 1) * k * euclideanNorm (x - y) := by
    calc
      _ ≤ ∑ j ∈ S, |(gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S, 34 * ↑k * d * euclideanNorm (x - y) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = S.card * (34 * k * d * euclideanNorm (x - y)) := by simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hcard
          (by positivity : 0 ≤ 34 * (k : ℝ) * d * euclideanNorm (x - y))
        nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d * k) hn]
  rw [gridPriorField, gridPriorField, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj),
    abs_mul, abs_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left hsum hη).trans_eq (by ring)
def gridPatch (d k ) (j : Fin d → Fin (k + 1)) : Set (Covariate d) :=
  {x | ∀ i, |↑k * clampUnit (x i) - (j i).val| ≤ 1}
theorem gridPatch_measurable (d k j) :
    MeasurableSet (gridPatch d k j) := by
  have heq : gridPatch d k j = ⋂ i : Fin d, {x : Covariate d |
      |↑k * clampUnit (x i) - (j i).val| ≤ 1} := by
    ext x
    simp [gridPatch]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le
  · have hc : Continuous (fun x : Covariate d => |↑k * clampUnit (x i) - (j i).val|) := by
      unfold clampUnit
      fun_prop
    exact hc.measurable
  · exact measurable_const
theorem gridTensorWindow_zero_outside_patch (d k j x) (hx : x ∉ gridPatch d k j) : gridTensorWindow d k j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) ((gridWindow_eq_zero_iff k (j i) (x i)).mpr (max_eq_left (by linarith [lt_of_not_ge hi])))
def gridNeighbors (k ) (j : Fin (k + 1)) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun l => |(j.val : ℝ) - l.val| ≤ 2)
def gridTensorNeighbors (d k ) (j : Fin d → Fin (k + 1)) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridNeighbors k (j i))
theorem gridPatch_common_point_neighbors (d k j l x) (hj : x ∈ gridPatch d k j) (hl : x ∈ gridPatch d k l) :
    l ∈ gridTensorNeighbors d k j := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have := abs_le.mp (hj i)
  have := abs_le.mp (hl i)
  exact abs_le.mpr ⟨by linarith, by linarith⟩
variable {d : ℕ}
theorem patch_score_ratio_formula (n a V η z g w y)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchObservableScore n a V η g w y z =
      symmetricDifference (patchResponseProduct n a V η g w y) /
        patchResponseProduct n a V η g w y z -
      η ^ 2 * ∑ i, (w i) ^ 2 *
        (ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i)) := by
  unfold patchObservableScore patchScoreNumerator
  have h_patch_variance_ratio' (i) : patchVarianceTerm n a V η g w y z i / patchResponseProduct n a V η g w y z =
      ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i) := by
    unfold patchVarianceTerm patchResponseProduct
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact mul_div_mul_right _ _ (ne_of_gt (Finset.prod_pos (fun k _ => hp k)))
  rw [sub_div]
  simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, (h_patch_variance_ratio' _)]
theorem patch_expected_score_energy_measurable  [MeasurableSpace α]
    (n : ℕ) (a V η z : ℝ) (g w : α → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun x => g x i)) (hw : ∀ i, Measurable (fun x => w x i)) :
    Measurable (fun x => patchExpectedScoreEnergy n a V η (g x) (w x) z) := by
  have hq (u : ℝ) (i : Fin n) (y : Fin 3) :
      Measurable (fun x => ternaryMass a (g x i + η * w x i * u) V y) := by
    apply ternaryMass_measurable_comp
    fun_prop
  have hprod (s : Finset (Fin n)) (u : ℝ) (y : Fin n → Fin 3) :
      Measurable (fun x => ∏ i ∈ s, ternaryMass a (g x i + η * w x i * u) V (y i)) :=
    Finset.measurable_prod _ (fun i _ => hq u i (y i))
  have hpatch (u : ℝ) (y : Fin n → Fin 3) :
      Measurable (fun x => patchResponseProduct n a V η (g x) (w x) y u) := hprod _ u y
  have hvar (i : Fin n) (y : Fin n → Fin 3) :
      Measurable (fun x => patchVarianceTerm n a V η (g x) (w x) y z i) :=
    (hprod (Finset.univ.erase i) z y).const_mul _
  have hscore (y : Fin n → Fin 3) :
      Measurable (fun x => patchObservableScore n a V η (g x) (w x) y z) := by
    have hcorr : Measurable (fun x => ∑ i, (w x i) ^ 2 *
        patchVarianceTerm n a V η (g x) (w x) y z i) :=
      Finset.measurable_sum _ (fun i _ => (hw i).pow_const 2 |>.mul (hvar i y))
    exact (((hpatch 1 y).const_mul (1 / 2) |>.add ((hpatch (-1) y).const_mul (1 / 2))
      |>.sub (hpatch 0 y)).sub (hcorr.const_mul (η ^ 2))).div (hpatch z y)
  exact Finset.measurable_sum _ (fun y _ => (hpatch z y).mul ((hscore y).pow_const 2))
theorem iid_design_full_patch_score_energy_bound  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n A) (hA : MeasurableSet A)
    (a V η z ρ c : ℝ) (g w : (Fin n → α) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun x => g x i)) (hwmeas : ∀ i, Measurable (fun x => w x i))
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c) (hz : z ∈ Icc (-1 : ℝ) 1)
    (hmean : n * μ.real A ≤ 1)
    (hwzero : ∀ x i, x i ∉ A → w x i = 0)
    (hw : ∀ x i, x i ∈ A → |w x i| ≤ 1)
    (hreg : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i, x i ∈ A → |g x i + η * w x i * u| ≤ ρ)
    (hq : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i, x i ∈ A → ∀ y,
      0 ≤ ternaryMass a (g x i + η * w x i * u) V y ∧
        ternaryMass a (g x i + η * w x i * u) V y ≤ 1)
    (hlower : ∀ x i, x i ∈ A → ∀ y, c ≤ ternaryMass a (g x i + η * w x i * z) V y)
    (hp : ∀ x i y, 0 < ternaryMass a (g x i + η * w x i * z) V y) :
    (∫ x : Fin n → α, patchExpectedScoreEnergy n a V η (g x) (w x) z
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ternaryScoreExponentialConstant a ρ c ^ 2 * Real.exp (ternaryScoreExponentialConstant a ρ c) *
        η ^ 4 * (n * μ.real A) ^ 2 := by
  let K := ternaryScoreExponentialConstant a ρ c
  let e : ℕ → ℝ := fun k => if 2 ≤ k then K ^ k * η ^ 4 else 0
  have hpoint (x : Fin n → α) : patchExpectedScoreEnergy n a V η (g x) (w x) z ≤
      e (designPatchCount n A x) := by
    let S := Finset.univ.filter (fun i : Fin n => x i ∈ A)
    have hS (i : Fin n) : i ∈ S ↔ x i ∈ A := by simp [S]
    have h_patch_expected_score_energy_support_bound (g) (w) (hwzero : ∀ i, i ∉ S → w i = 0) (hw : ∀ i ∈ S, |w i| ≤ 1) (hreg : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, |g i + η * w i * u| ≤ ρ) (hq : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i ∈ S, ∀ y, 0 ≤ ternaryMass a (g i + η * w i * u) V y ∧ ternaryMass a (g i + η * w i * u) V y ≤ 1) (hlower : ∀ i ∈ S, ∀ y, c ≤ ternaryMass a (g i + η * w i * z) V y) (hp : ∀ i y, 0 < ternaryMass a (g i + η * w i * z) V y) : patchExpectedScoreEnergy n a V η g w z ≤
        if 2 ≤ S.card then ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4 else 0 := by
      split_ifs with hcount
      · calc
          _ ≤ ∑ y : Fin n → Fin 3, patchResponseProduct n a V η g w y z *
              (ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4) := by
            apply Finset.sum_le_sum
            intro y _
            have h_patch_score_square_support_bound : (patchObservableScore n a V η g w y z) ^ 2 ≤
          ternaryScoreExponentialConstant a ρ c ^ S.card * η ^ 4 := by
              have hcount : 1 ≤ S.card := by omega
              have hq  := fun u hu i hi => hq u hu i hi (y i)
              have hlower  := fun i hi => hlower i hi (y i)
              have hp  := fun i => hp i (y i)
              let e := S.equivFin.symm
              have h_patch_score_restrict : patchObservableScore n a V η g w y z =
                  patchObservableScore S.card a V η (fun i => g (e i)) (fun i => w (e i))
                    (fun i => y (e i)) z := by
                let O : ℝ := ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (y i)
                have hfactor u : patchResponseProduct n a V η g w y u =
                    O * patchResponseProduct S.card a V η (fun i => g (e i)) (fun i => w (e i))
                      (fun i => y (e i)) u := by
                  unfold patchResponseProduct
                  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
                  congr 1
                  · apply Finset.prod_congr rfl
                    intro i hi
                    simp [hwzero i (Finset.mem_sdiff.mp hi).2]
                  · rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
                    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
                have hratio u : patchResponseProduct n a V η g w y u /
                    patchResponseProduct n a V η g w y z =
                    patchResponseProduct S.card a V η (fun i => g (e i)) (fun i => w (e i))
                      (fun i => y (e i)) u /
                    patchResponseProduct S.card a V η (fun i => g (e i)) (fun i => w (e i))
                      (fun i => y (e i)) z := by
                  rw [hfactor u, hfactor z]
                  exact mul_div_mul_left _ _ (by apply ne_of_gt; apply Finset.prod_pos; intro i hi; simpa [hwzero i (Finset.mem_sdiff.mp hi).2] using hp i)
                rw [patch_score_ratio_formula n a V η z g w y hp,
                  patch_score_ratio_formula S.card a V η z _ _ _ (fun i => hp (e i))]
                congr 1
                · unfold symmetricDifference
                  simp only [sub_div, add_div, mul_div_assoc]
                  rw [hratio 1, hratio (-1), hratio 0]
                · congr 1
                  rw [← Finset.sum_subset (Finset.subset_univ S)]
                  · rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
                    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
                  · intro i _ hi
                    simp [hwzero i hi]
              rw [h_patch_score_restrict]
              let M := (2 * ρ + a) / a ^ 2
              let K := M ^ 2 + 3 / a ^ 2
              have hs := patch_score_square_bound S.card a V η z M (2 / a ^ 2) (1 / a ^ 2) c
                (fun i => g (e i)) (fun i => w (e i)) (fun i => y (e i)) hcount hz
                (by dsimp [M]; positivity) (by positivity) (by positivity) hc
                (fun i => hw (e i) (e i).property)
                (fun u hu i => (abs_of_nonneg (hq u hu (e i) (e i).property).1).trans_le
                  (hq u hu (e i) (e i).property).2)
                (fun u hu i => ternary_mean_derivative_abs_bound a _ ρ ha hρ
                  (hreg u hu (e i) (e i).property) (y (e i)))
                (fun i => ternary_mean_second_derivative_abs_bound a ha (y (e i)))
                (fun i => ternary_variance_derivative_abs_bound a ha (y (e i)))
                (fun i => hlower (e i) (e i).property)
              have hK : M ^ 2 + 2 / a ^ 2 + 1 / a ^ 2 = K := by dsimp [K]; ring
              rw [hK] at hs
              simpa [ternaryScoreExponentialConstant, K, M] using
                score_bound_exponential_absorption S.card K c η _ hcount hc hs
            exact mul_le_mul_of_nonneg_left
              h_patch_score_square_support_bound
              (Finset.prod_nonneg (fun i _ => (hp i (y i)).le))
          _ = _ := by rw [← Finset.sum_mul, patch_response_normalized n a V η g w z ha.ne', one_mul]
      · have : S.card < 2 := by omega
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro y _
        have h_patch_score_zero_of_support_count_lt_two : patchObservableScore n a V η g w y z = 0 := by
          have hcases : S.card = 0 ∨ S.card = 1 := by omega
          rcases hcases with hzero | hone
          · have hS  := Finset.card_eq_zero.mp hzero
            have hnum := patch_score_cancel_zero n a V η g w y z (fun i => hwzero i (by simp [hS]))
            simp [patchObservableScore, hnum]
          · obtain ⟨i, hS⟩ := Finset.card_eq_one.mp hone
            have h_patch_score_cancel_singleton (ha : a ≠ 0) (hw : ∀ k, k ≠ i → w k = 0) : patchScoreNumerator n a V η g w y z = 0 := by
              have h_patch_product_singleton (z) (i) (hw : ∀ k, k ≠ i → w k = 0) : patchResponseProduct n a V η g w y z =
                  ternaryMass a (g i + η * w i * z) V (y i) *
                    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (g k) V (y k) := by
                unfold patchResponseProduct
                rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
                congr 1
                apply Finset.prod_congr rfl
                intro k hk
                rw [hw k (Finset.ne_of_mem_erase hk)]
                simp
              have hterm : ∑ k, (w k) ^ 2 * patchVarianceTerm n a V η g w y z k =
                  (w i) ^ 2 * patchVarianceTerm n a V η g w y z i := by
                apply Finset.sum_eq_single i
                · intro k _ hki
                  simp [hw k hki]
                · simp
              have hvar : patchVarianceTerm n a V η g w y z i =
                  ternaryVarianceDerivative a (y i) *
                    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (g k) V (y k) := by
                unfold patchVarianceTerm
                congr 1
                apply Finset.prod_congr rfl
                intro k hk
                simp [hw k (Finset.ne_of_mem_erase hk)]
              unfold patchScoreNumerator symmetricDifference
              rw [hterm, hvar, h_patch_product_singleton 1 i hw,
                h_patch_product_singleton (-1) i hw,
                h_patch_product_singleton 0 i hw]
              simp only [mul_one, mul_neg_one, mul_zero, add_zero]
              have h_ternary_finite_difference (g) (w) (y) : (1 / 2 ) * ternaryMass a (g + η * w) V y +
                  (1 / 2 ) * ternaryMass a (g - η * w) V y - ternaryMass a g V y =
                  η ^ 2 * w ^ 2 * ternaryVarianceDerivative a y := by
                fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative] <;>
                  field_simp [ha] <;> ring
              have hheat := h_ternary_finite_difference (g i) (w i) (y i)
              simp only [sub_eq_add_neg] at hheat
              linear_combination (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
                ternaryMass a (g k) V (y k)) * hheat
            have hnum := (h_patch_score_cancel_singleton ha.ne' (fun k hki => hwzero k (by simpa [hS] using hki)))
            simp [patchObservableScore, hnum]
        rw [h_patch_score_zero_of_support_count_lt_two]
        ring
    exact h_patch_expected_score_energy_support_bound (g x) (w x) (fun i hi => hwzero x i (fun h => hi ((hS i).mpr h))) (fun i hi => hw x i ((hS i).mp hi)) (fun u hu i hi => hreg x u hu i ((hS i).mp hi)) (fun u hu i hi y => hq x u hu i ((hS i).mp hi) y) (fun i hi y => hlower x i ((hS i).mp hi) y) (hp x)
  have h_iid_design_count_observable_integrable : Integrable (fun x : Fin n → α => e (designPatchCount n A x))
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply Integrable.of_bound
      ((measurable_of_countable e).comp (design_patch_count_measurable n A hA)).aestronglyMeasurable
      (∑ k ∈ Finset.range (n + 1), |e k|)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg (e k))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (design_patch_count_le n A x)))
  have he := h_iid_design_count_observable_integrable
  have henergy : Integrable (fun x => patchExpectedScoreEnergy n a V η (g x) (w x) z)
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply he.mono' (patch_expected_score_energy_measurable n a V η z g w hg hwmeas).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint x
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg
        (Finset.prod_nonneg (fun i _ => (hp x i (y i)).le)) (sq_nonneg _))
  have h_iid_design_collision_energy_bound : (∫ x : Fin n → α, e (designPatchCount n A x) ∂Measure.pi (fun _ : Fin n => μ)) ≤
      K ^ 2 * Real.exp K * η ^ 4 * (n * μ.real A) ^ 2 := by
    have hC : 0 ≤ K := (by dsimp [K, ternaryScoreExponentialConstant]; positivity)
    have he0 : e 0 = 0 := by simp [e]
    have he1 : e 1 = 0 := by simp [e]
    have he : ∀ k, 2 ≤ k → e k ≤ K ^ k * η ^ 4 := fun k hk => by simp [e, hk]
    have h_iid_design_count_integral : (∫ x : Fin n → α, e (designPatchCount n A x) ∂Measure.pi (fun _ : Fin n => μ)) =
        ∑ k ∈ Finset.range (n + 1), binomialCountMass n (μ.real A) k * e k := by
      let ν := Measure.pi (fun _ : Fin n => μ)
      have hm (k : ℕ) : MeasurableSet {x : Fin n → α | designPatchCount n A x = k} :=
        (measurableSet_singleton k).preimage (design_patch_count_measurable n A hA)
      have hdecomp (x : Fin n → α) : e (designPatchCount n A x) =
          ∑ k ∈ Finset.range (n + 1),
            ({x : Fin n → α | designPatchCount n A x = k}).indicator (fun _ => e k) x := by
        symm
        calc
          _ = ({x : Fin n → α | designPatchCount n A x = designPatchCount n A x}).indicator
              (fun _ => e (designPatchCount n A x)) x := by
            apply Finset.sum_eq_single (designPatchCount n A x)
            · intro k _ hk
              simp [Ne.symm hk]
            · intro hn
              exact False.elim (hn (Finset.mem_range.mpr
                (Nat.lt_succ_iff.mpr (design_patch_count_le n A x))))
          _ = e (designPatchCount n A x) := by simp
      have hfun  := funext hdecomp
      rw [hfun, integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k _
        have h_iid_design_patch_count_probability : (Measure.pi (fun _ : Fin n => μ)).real {x : Fin n → α | designPatchCount n A x = k} =
        binomialCountMass n (μ.real A) k := by
          have h_design_patch_count_fiber : {x : Fin n → α | designPatchCount n A x = k} =
              ⋃ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, designMembershipCell n A s := by
            ext x
            constructor
            · intro hx
              change designPatchCount n A x = k at hx
              let s : Finset (Fin n) := Finset.univ.filter fun i => x i ∈ A
              apply Set.mem_iUnion.mpr
              refine ⟨s, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
              · apply Finset.mem_powersetCard.mpr
                exact ⟨Finset.subset_univ _, hx⟩
              · rw [design_membership_cell_iff]
                intro i
                simp [s]
            · intro hx
              obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
              have hfilter : (Finset.univ.filter fun i => x i ∈ A) = s := by
                ext i
                simpa using (design_membership_cell_iff n A s x).mp hxs i
              change (Finset.univ.filter fun i => x i ∈ A).card = k
              rw [hfilter]
              exact (Finset.mem_powersetCard.mp hs).2
          rw [measureReal_def, h_design_patch_count_fiber, measure_biUnion_finset]
          · rw [ENNReal.toReal_sum (fun s _ => measure_ne_top _ _)]
            have hcell (s : Finset (Fin n)) (hs : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
                ((Measure.pi (fun _ : Fin n => μ)) (designMembershipCell n A s)).toReal =
                  (μ.real A) ^ k * (1 - μ.real A) ^ (n - k) := by
              have h_iid_design_membership_cell_measure (s : Finset (Fin n)) : (Measure.pi (fun _ : Fin n => μ)) (designMembershipCell n A s) =
              (μ A) ^ s.card * (μ Aᶜ) ^ (n - s.card) := by
                rw [designMembershipCell, Measure.pi_pi]
                simp only [apply_ite]
                rw [Finset.prod_ite]
                have hin : (Finset.univ.filter fun i : Fin n => i ∈ s) = s := by ext i; simp
                have hout : (Finset.univ.filter fun i : Fin n => i ∉ s) = Finset.univ \ s := by ext i; simp
                rw [hin, hout]
                simp [Finset.card_sdiff_of_subset (Finset.subset_univ s)]
              rw [h_iid_design_membership_cell_measure, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, (Finset.mem_powersetCard.mp hs).2]
              have hcompl : μ.real Aᶜ = 1 - μ.real A := by
                simpa using measureReal_compl hA (μ := μ)
              change (μ.real A) ^ k * (μ.real Aᶜ) ^ (n - k) = _
              rw [hcompl]
            rw [Finset.sum_congr rfl hcell]
            simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
              Finset.card_univ, Fintype.card_fin]
            unfold binomialCountMass
            ring
          · intro s hs t ht hst
            exact design_membership_cells_disjoint n A hst
          · intro s _
            exact design_membership_cell_measurable n A hA s
        rw [integral_indicator_const (e k) (hm k), h_iid_design_patch_count_probability]
        simp [smul_eq_mul]
      · intro k _
        exact (integrable_const (e k)).indicator (hm k)
    rw [h_iid_design_count_integral]
    exact binomial_collision_energy_bound n (μ.real A) K η e measureReal_nonneg
      measureReal_le_one hC hmean he0 he1 he
  exact (integral_mono henergy he hpoint).trans
    h_iid_design_collision_energy_bound
theorem patch_expected_score_energy_integrable  [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) (a V η z ρ c : ℝ) (g w : α → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun x => g x i)) (hwmeas : ∀ i, Measurable (fun x => w x i))
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hc : 0 < c) (hz : z ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ x i, |w x i| ≤ 1)
    (hreg : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i, |g x i + η * w x i * u| ≤ ρ)
    (hq : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ i y,
      0 ≤ ternaryMass a (g x i + η * w x i * u) V y ∧
        ternaryMass a (g x i + η * w x i * u) V y ≤ 1)
    (hlower : ∀ x i y, c ≤ ternaryMass a (g x i + η * w x i * z) V y) :
    Integrable (fun x => patchExpectedScoreEnergy n a V η (g x) (w x) z) μ := by
  cases n with
  | zero =>
    simp_rw [patch_expected_score_energy_zero]
    exact integrable_zero _ _ _
  | succ n =>
    apply Integrable.of_bound
      (patch_expected_score_energy_measurable (n + 1) a V η z g w hg hwmeas).aestronglyMeasurable
      (ternaryScoreExponentialConstant a ρ c ^ (n + 1) * η ^ 4)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hn : 1 ≤ (n + 1) := by omega
      have hq  := hq x
      have hlower  := hlower x
      let M := (2 * ρ + a) / a ^ 2
      let K := M ^ 2 + 3 / a ^ 2
      have hy (y : Fin (n + 1) → Fin 3) : (patchObservableScore (n + 1) a V η (g x) (w x) y z) ^ 2 ≤
          ternaryScoreExponentialConstant a ρ c ^ (n + 1) * η ^ 4 := by
        have hs := patch_score_square_bound (n + 1) a V η z M (2 / a ^ 2) (1 / a ^ 2) c (g x) (w x) y hn hz
          (by dsimp [M]; positivity) (by positivity) (by positivity) hc (hw x)
          (fun u hu i => (abs_of_nonneg (hq u hu i (y i)).1).trans_le (hq u hu i (y i)).2)
          (fun u hu i => ternary_mean_derivative_abs_bound a _ ρ ha hρ ((hreg x) u hu i) (y i))
          (fun i => ternary_mean_second_derivative_abs_bound a ha (y i))
          (fun i => ternary_variance_derivative_abs_bound a ha (y i)) (fun i => hlower i (y i))
        have hK : M ^ 2 + 2 / a ^ 2 + 1 / a ^ 2 = K := by dsimp [K]; ring
        rw [hK] at hs
        simpa [ternaryScoreExponentialConstant, K, M] using
          score_bound_exponential_absorption (n + 1) K c η _ hn hc hs
      calc
        _ ≤ ∑ y : Fin (n + 1) → Fin 3,
            patchResponseProduct (n + 1) a V η (g x) (w x) y z * (ternaryScoreExponentialConstant a ρ c ^ (n + 1) * η ^ 4) := by
          apply Finset.sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (hy y) (le_trans
            (pow_nonneg hc.le (n + 1)) (patch_response_lower_bound (n + 1) a V η z c (g x) (w x) y hc.le (fun i => hlower i (y i))))
        _ = _ := by rw [← Finset.sum_mul, patch_response_normalized (n + 1) a V η (g x) (w x) z (ne_of_gt ha), one_mul]
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg
        (Finset.prod_nonneg (fun i _ => (hq x z hz i (y i)).1)) (sq_nonneg _))
def gridWindowCount (d k : ℕ) : ℕ := (k + 1) ^ d
def gridWindowIndexEquiv (d k : ℕ) : Fin (gridWindowCount d k) ≃ (Fin d → Fin (k + 1)) :=
  (Fintype.equivFinOfCardEq (by simp [gridWindowCount])).symm
def indexedGridWindow (d k : ℕ) (j : Fin (gridWindowCount d k)) : Covariate d → ℝ :=
  gridTensorWindow d k (gridWindowIndexEquiv d k j)
def indexedGridPatch (d k : ℕ) (j : Fin (gridWindowCount d k)) : Set (Covariate d) :=
  gridPatch d k (gridWindowIndexEquiv d k j)
def indexedGridField (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (x : Covariate d) : ℝ := η * ∑ j, indexedGridWindow d k j x * ternaryValue 1 (ξ j)
theorem indexedGridField_eq (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3) :
    indexedGridField d k η ξ =
      gridPriorField d k η (fun j => ξ ((gridWindowIndexEquiv d k).symm j)) := by
  funext x
  unfold indexedGridField gridPriorField
  congr 1
  exact Fintype.sum_equiv (gridWindowIndexEquiv d k) _ _ (fun j => by simp [indexedGridWindow])
theorem indexedGridField_continuous (d k : ℕ) (η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Continuous (indexedGridField d k η ξ) := by
  rw [indexedGridField_eq]
  exact gridPriorField_continuous _ _ _ _
theorem indexedGridField_abs_bound (d k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Covariate d) :
    |indexedGridField d k η ξ x| ≤ ↑2 ^ d * η := by
  rw [indexedGridField_eq]
  exact gridPriorField_abs_bound _ _ _ hη _ x
def gridSampleWeights (d k n : ℕ) (x : Fin n → Covariate d) :
    Fin n → Fin (gridWindowCount d k) → ℝ := fun i j => indexedGridWindow d k j (x i)
theorem grid_latent_regression_eq (d k n : ℕ) (η : ℝ) (x : Fin n → Covariate d)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
    latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ i =
      indexedGridField d k η ξ (x i) := by
  simp [latentRegression, indexedGridField, gridSampleWeights]
theorem grid_modified_regression_abs_bound (d k n : ℕ) (η u : ℝ) (hη : 0 ≤ η)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (j : Fin (gridWindowCount d k)) (i : Fin n) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i +
      η * gridSampleWeights d k n x i j * u| ≤ (↑2 ^ d + 2) * η := by
  let z := ternaryValue 1 (ξ j)
  have  := ternaryValue_one_abs_le (ξ j)
  have hw : |gridSampleWeights d k n x i j| ≤ 1 := by
    change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
    rw [abs_of_nonneg (gridTensorWindow_nonneg d k (gridWindowIndexEquiv d k j) (x i))]
    exact gridTensorWindow_le_one _ _ _ _
  have hdiff : |u - z| ≤ 2 := by
    have h := abs_sub_le u 0 z
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [abs_le.mpr hu]
  have heq : latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j i + η * gridSampleWeights d k n x i j * u =
        indexedGridField d k η ξ (x i) + η * gridSampleWeights d k n x i j * (u - z) := by
    rw [← grid_latent_regression_eq, latent_regression_decomposition]
    ring
  rw [heq]
  have : |η * gridSampleWeights d k n x i j * (u - z)| ≤ 2 * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg hη]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hw hη) hdiff (abs_nonneg _) (by positivity : 0 ≤ η * 1)
    simpa only [mul_one, mul_comm] using h
  exact (abs_add_le _ _).trans (by nlinarith [indexedGridField_abs_bound d k η hη ξ (x i)])
def gridCoordinateEnergy (d k n : ℕ) (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (x : Fin n → Covariate d) : ℝ :=
  patchExpectedScoreEnergy n a V η
    (latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j)
    (fun i => gridSampleWeights d k n x i j) (ternaryValue 1 (ξ j))
theorem grid_sample_weight_measurable (d k n : ℕ) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x : Fin n → Covariate d => gridSampleWeights d k n x i j) :=
  ((gridTensorWindow_continuous d k (gridWindowIndexEquiv d k j)).comp
    (continuous_apply i)).measurable
theorem grid_excluded_field_measurable (d k n : ℕ) (η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x : Fin n → Covariate d =>
      latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j i) := by
  exact measurable_const.add ((Finset.measurable_sum _
    (fun l _ => (grid_sample_weight_measurable d k n l i).mul_const _)).const_mul _)
theorem grid_coordinate_design_energy_bound  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (hk : 0 < k) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    (∫ x : Fin n → Covariate d, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
      ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
        Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 *
          (n * (2 / ↑k) ^ d) ^ 2 := by
  let _ := cubeVolume_isProbability d
  let g : (Fin n → Covariate d) → Fin n → ℝ := fun x =>
    latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j
  let w : (Fin n → Covariate d) → Fin n → ℝ := fun x i => gridSampleWeights d k n x i j
  let A := indexedGridPatch d k j
  let z := ternaryValue 1 (ξ j)
  have hz : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp (ternaryValue_one_abs_le (ξ j))
  have hreg (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
      |g x i + η * w x i * u| ≤ P.ρ :=
    (grid_modified_regression_abs_bound d k n η u hη x ξ j i hu).trans hfield
  have hlegal (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :=
    P.path_legality η t (g x i + η * w x i * u) ht hvariance (hreg x u hu i)
  have hp (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) (y : Fin 3) :
      0 < ternaryMass P.a (g x i + η * w x i * u) (P.variancePath η t) y :=
    P.c_pos.trans_le ((hlegal x u hu i).2.2.1 y)
  have h_gridPatch_cube_probability_bound (j : Fin d → Fin (k + 1)) : (cubeVolume d).real (gridPatch d k j) ≤ (2 / ↑k) ^ d := by
    have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
    let R : Set (Covariate d) := Set.univ.pi
      (fun i => Icc (((j i).val - 1 : ℝ) / k) (((j i).val + 1 : ℝ) / k))
    have hsub : gridPatch d k j ∩ unitCube d ⊆ R := by
      intro x hx
      rw [Set.mem_pi]
      intro i _
      have hi := hx.1 i
      rw [clampUnit_eq (x i) (hx.2 i)] at hi
      constructor
      · apply (div_le_iff₀ hkp).mpr
        linarith [(abs_le.mp hi).1]
      · apply (le_div_iff₀ hkp).mpr
        linarith [(abs_le.mp hi).2]
    have hvol : volume R = ENNReal.ofReal ((2 / ↑k) ^ d) := by
      rw [volume_pi, Measure.pi_pi]
      simp only [Real.volume_Icc]
      have hwidth (i : Fin d) : (((j i).val + 1 : ℝ) / k) - ((j i).val - 1 : ℝ) / k = 2 / k := by ring
      simp_rw [hwidth]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (ENNReal.ofReal_pow (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hkp.le) d).symm
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (by rw [cubeVolume, Measure.restrict_apply (gridPatch_measurable d k j), ← hvol]; exact measure_mono hsub)).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hvol : (cubeVolume d).real A ≤ (2 / ↑k) ^ d := h_gridPatch_cube_probability_bound _
  have hmean' : n * (cubeVolume d).real A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg n)).trans hmean
  have hbound := iid_design_full_patch_score_energy_bound (cubeVolume d) n A
    (gridPatch_measurable d k _) P.a (P.variancePath η t) η z P.ρ P.c g w
    (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable d k n j)
    P.a_pos P.ρ_pos.le P.c_pos hz hmean'
    (fun x i hi => gridTensorWindow_zero_outside_patch d k (gridWindowIndexEquiv d k j) (x i) hi)
    (fun x i _ => by
      change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
      rw [abs_of_nonneg (gridTensorWindow_nonneg d k _ _)]; exact gridTensorWindow_le_one d k _ _)
    (fun x u hu i _ => hreg x u hu i)
    (fun x u hu i _ y => ⟨(hp x u hu i y).le,
      ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun b => (hp x u hu i b).le) y⟩)
    (fun x i _ y => (hlegal x z hz i).2.2.1 y) (fun x i y => hp x z hz i y)
  apply hbound.trans
  gcongr
def gridFullScoreEnergy (d k n : ℕ) (a V η : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (x : Fin n → Covariate d) : ℝ :=
  ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V
    (latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)) ξ y *
    (finiteExperimentScore (gridWindowCount d k) n a V η
      (latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)) ξ y) ^ 2
theorem grid_full_score_conditional_energy_bound (d k n : ℕ) (a V η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d)
    (ha : a ≠ 0) (hp : ∀ i y, 0 < ternaryMass a (indexedGridField d k η ξ (x i)) V y) :
    gridFullScoreEnergy d k n a V η ξ x ≤ ↑5 ^ d *
      ∑ j, gridCoordinateEnergy d k n a V η ξ j x := by
  let f := latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)
  have h_grid_sample_squared_partition (i : Fin n) : (∑ j, gridSampleWeights d k n x i j ^ 2) = 1 := by
    have h := Fintype.sum_equiv (gridWindowIndexEquiv d k)
      (fun j => indexedGridWindow d k j (x i) ^ 2) (fun j => gridTensorWindow d k j (x i) ^ 2)
      (fun _ => rfl)
    have h_gridTensorWindow_square_partition (x : Covariate d) : (∑ j : Fin d → Fin (k + 1), gridTensorWindow d k j x ^ 2) = 1 := by
      simp only [gridTensorWindow, ← Finset.prod_pow]
      rw [← Fintype.prod_sum (fun i (j : Fin (k + 1)) => gridWindow k j (x i) ^ 2)]
      simp [gridWindow_square_partition]
    exact h.trans (h_gridTensorWindow_square_partition (x i))
  have h_indexed_grid_observed_patch_degree (j : Fin (gridWindowCount d k)) : (Finset.univ.filter fun l : Fin (gridWindowCount d k) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l)).card ≤ 5 ^ d := by
    have heq := Finset.card_equiv (gridWindowIndexEquiv d k) (s := Finset.univ.filter fun l =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ indexedGridPatch d k l))
      (t := Finset.univ.filter fun l =>
        ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k (gridWindowIndexEquiv d k j))
          (Finset.univ.filter fun i => x i ∈ gridPatch d k l))
      (fun _ => by
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        rfl)
    rw [heq]
    have h_grid_observed_patch_degree (j : Fin d → Fin (k + 1)) : (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
        ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
          (Finset.univ.filter fun i => x i ∈ gridPatch d k l)).card ≤ 5 ^ d := by
      have hsub : (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
          ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
            (Finset.univ.filter fun i => x i ∈ gridPatch d k l)) ⊆ gridTensorNeighbors d k j := by
        intro l hl
        obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hl).2
        exact gridPatch_common_point_neighbors d k j l (x i) (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hi').2
      have h_gridTensorNeighbors_card : (gridTensorNeighbors d k j).card ≤ 5 ^ d := by
        rw [gridTensorNeighbors, Fintype.card_piFinset]
        have h_gridNeighbors_card (j : Fin (k + 1)) : (gridNeighbors k j).card ≤ 5 := by
          have hsub : (gridNeighbors k j).image Fin.val ⊆ Finset.Icc (j.val - 2) (j.val + 2) := by
            intro l hl
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
            have hdist := (Finset.mem_filter.mp hi).2
            have hl1 : j.val ≤ i.val + 2 := by exact_mod_cast (by linarith [(abs_le.mp hdist).2] :
              (j.val : ℝ) ≤ i.val + 2)
            have hl2 : i.val ≤ j.val + 2 := by exact_mod_cast (by linarith [(abs_le.mp hdist).1] :
              (i.val : ℝ) ≤ j.val + 2)
            exact Finset.mem_Icc.mpr ⟨by omega, hl2⟩
          have h := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h
          omega
        calc
          _ ≤ ∏ _i : Fin d, 5 := Finset.prod_le_prod (fun i _ => (h_gridNeighbors_card (j i)))
          _ = _ := by simp
      exact (Finset.card_le_card hsub).trans h_gridTensorNeighbors_card
    exact h_grid_observed_patch_degree _
  have h := latent_full_score_variance_bound (gridWindowCount d k) n a V η (fun _ => 0)
    (gridSampleWeights d k n x) ξ (fun j => Finset.univ.filter (fun i => x i ∈ indexedGridPatch d k j)) (5 ^ d)
    (fun j i hi => gridTensorWindow_zero_outside_patch d k _ (x i) (by
      intro hmem
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩))
    h_grid_sample_squared_partition
    h_indexed_grid_observed_patch_degree ha (by intro i y; simpa [f, grid_latent_regression_eq] using hp i y)
  simp_rw [ternary_index_product_integral] at h
  change gridFullScoreEnergy d k n a V η ξ x ≤ (5 ^ d : ℕ) *
    ∑ j, ∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V f ξ y *
      (finiteCoordinateScore (gridWindowCount d k) n a V η f (gridSampleWeights d k n x) ξ y j) ^ 2 at h
  have hcoord (j : Fin (gridWindowCount d k)) :
      (∑ y, finiteResponseLikelihood (gridWindowCount d k) n a V f ξ y *
        (finiteCoordinateScore (gridWindowCount d k) n a V η f (gridSampleWeights d k n x) ξ y j) ^ 2) =
        gridCoordinateEnergy d k n a V η ξ j x := by
    unfold gridCoordinateEnergy patchExpectedScoreEnergy
    apply Finset.sum_congr rfl
    intro y _
    rw [latent_coordinate_score_eq_patch]
    congr 1
    simp only [finiteResponseLikelihood, patchResponseProduct, f]
    simp_rw [latent_regression_decomposition (gridWindowCount d k) n η (fun _ => 0)
      (gridSampleWeights d k n x) ξ j]
  simp_rw [hcoord] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
theorem grid_coordinate_energy_integrable  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (j : Fin (gridWindowCount d k))
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  let g : (Fin n → Covariate d) → Fin n → ℝ := fun x =>
    latentRegressionWithout (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) ξ j
  let w : (Fin n → Covariate d) → Fin n → ℝ := fun x i => gridSampleWeights d k n x i j
  let z := ternaryValue 1 (ξ j)
  have hz  := abs_le.mp (ternaryValue_one_abs_le (ξ j))
  have hreg (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :
      |g x i + η * w x i * u| ≤ P.ρ :=
    (grid_modified_regression_abs_bound d k n η u hη x ξ j i hu).trans hfield
  have hlegal (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) :=
    P.path_legality η t (g x i + η * w x i * u) ht hvariance (hreg x u hu i)
  have hp (x : Fin n → Covariate d) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (i : Fin n) (y : Fin 3) :
      0 < ternaryMass P.a (g x i + η * w x i * u) (P.variancePath η t) y :=
    P.c_pos.trans_le ((hlegal x u hu i).2.2.1 y)
  exact patch_expected_score_energy_integrable _ n P.a (P.variancePath η t) η z P.ρ P.c g w
    (grid_excluded_field_measurable d k n η ξ j) (grid_sample_weight_measurable d k n j)
    P.a_pos P.ρ_pos.le P.c_pos hz
    (fun x i => by
      change |gridTensorWindow d k (gridWindowIndexEquiv d k j) (x i)| ≤ 1
      rw [abs_of_nonneg (gridTensorWindow_nonneg d k _ _)]; exact gridTensorWindow_le_one d k _ _)
    hreg (fun x u hu i y => ⟨(hp x u hu i y).le,
      ternary_mass_le_one P.a _ _ P.a_pos.ne' (fun b => (hp x u hu i b).le) y⟩)
    (fun x i y => (hlegal x z hz i).2.2.1 y)
theorem grid_response_positive  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    ∀ i y, 0 < ternaryMass P.a (indexedGridField d k η ξ (x i)) (P.variancePath η t) y := by
  intro i y
  exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance ((indexedGridField_abs_bound d k η hη ξ (x i)).trans (by nlinarith))).2.2.1 y)
theorem grid_full_score_energy_integrable  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  have hI := (integrable_finsetSum (Finset.univ : Finset (Fin (gridWindowCount d k))) (fun j _ =>
    grid_coordinate_energy_integrable C P k n η t ξ j hη ht hfield hvariance)).const_mul (↑5 ^ d)
  have h_grid_full_score_energy_measurable : Measurable (gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ) := by
    let f : (Fin n → Covariate d) → (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
      fun x => latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x)
    have hq (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) (y : Fin 3) :
        Measurable (fun x => ternaryMass P.a (f x ξ' i) (P.variancePath η t) y) := by
      apply ternaryMass_measurable_comp
      simpa only [f, grid_latent_regression_eq, Function.comp_def] using
        ((indexedGridField_continuous d k η ξ').comp (continuous_apply i)).measurable
    have hL (ξ' : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
        Measurable (fun x => finiteResponseLikelihood (gridWindowCount d k) n P.a (P.variancePath η t) (f x) ξ' y) :=
      Finset.measurable_prod _ (fun i _ => hq ξ' i (y i))
    have hU (y : Fin n → Fin 3) (i : Fin n) :
        Measurable (fun x => finiteResponseVarianceTerm (gridWindowCount d k) n P.a (P.variancePath η t) (f x) ξ y i) :=
      (Finset.measurable_prod _ (fun l _ => hq ξ l (y l))).const_mul _
    have hD (y : Fin n → Fin 3) (j : Fin (gridWindowCount d k)) :
        Measurable (fun x => latentDifference (gridWindowCount d k) j
          (fun ξ' => finiteResponseLikelihood (gridWindowCount d k) n P.a (P.variancePath η t) (f x) ξ' y) ξ) :=
      (((hL (Function.update ξ j 2) y).const_mul (1 / 2)).add
        ((hL (Function.update ξ j 0) y).const_mul (1 / 2))).sub (hL (Function.update ξ j 1) y)
    have hR (y : Fin n → Fin 3) :
        Measurable (fun x => finiteExperimentScore (gridWindowCount d k) n P.a (P.variancePath η t) η (f x) ξ y) :=
      ((Finset.measurable_sum _ (fun j _ => hD y j)).sub
        ((Finset.measurable_sum _ (fun i _ => hU y i)).const_mul (η ^ 2))).div (hL ξ y)
    exact Finset.measurable_sum _ (fun y _ => (hL ξ y).mul ((hR y).pow_const 2))
  apply hI.mono' h_grid_full_score_energy_measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hp := grid_response_positive C P k n η t ξ x hη ht hfield hvariance
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact grid_full_score_conditional_energy_bound d k n P.a (P.variancePath η t) η ξ x P.a_pos.ne' hp
  · exact Finset.sum_nonneg (fun y _ => mul_nonneg
      (Finset.prod_nonneg (fun i _ => by simpa [grid_latent_regression_eq] using (hp i (y i)).le))
      (sq_nonneg _))
def gridPriorScoreEnergy (d k n : ℕ) (a v η t : ℝ) : ℝ :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ *
    ∫ x : Fin n → Covariate d, gridFullScoreEnergy d k n a (v - η ^ 2 * t) η ξ x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)
theorem grid_prior_score_energy_bound  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ) (hk : 1 ≤ k)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    gridPriorScoreEnergy d k n P.a P.v η t ≤
      ↑40 ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
        Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * n ^ 2 * η ^ 4 / ↑k ^ d := by
  let K := ternaryScoreExponentialConstant P.a P.ρ P.c
  let B := ↑5 ^ d * gridWindowCount d k *
    (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / ↑k) ^ d) ^ 2)
  have hkp : 0 < k := by omega
  have hbudget : gridPriorScoreEnergy d k n P.a P.v η t ≤ B := by
    unfold gridPriorScoreEnergy
    calc
      _ ≤ ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * B := by
        apply Finset.sum_le_sum
        intro ξ _
        have h_grid_full_score_design_energy_bound : (∫ x : Fin n → Covariate d, gridFullScoreEnergy d k n P.a (P.variancePath η t) η ξ x
            ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤
            ↑5 ^ d * gridWindowCount d k *
              (ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
                Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 * (n * (2 / ↑k) ^ d) ^ 2) := by
          let μ := Measure.pi (fun _ : Fin n => cubeVolume d)
          have hcoords (j : Fin (gridWindowCount d k)) :=
            grid_coordinate_energy_integrable C P k n η t ξ j hη ht hfield hvariance
          calc
            _ ≤ ∫ x, ↑5 ^ d * ∑ j, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x ∂μ :=
              integral_mono (grid_full_score_energy_integrable C P k n η t ξ hη ht hfield hvariance)
                ((integrable_finsetSum _ (fun j _ => hcoords j)).const_mul _)
                (fun x => grid_full_score_conditional_energy_bound d k n P.a (P.variancePath η t) η ξ x
                  P.a_pos.ne' (grid_response_positive C P k n η t ξ x hη ht hfield hvariance))
            _ = ↑5 ^ d * ∑ j, ∫ x, gridCoordinateEnergy d k n P.a (P.variancePath η t) η ξ j x ∂μ := by
              rw [integral_const_mul, integral_finsetSum _ (fun j _ => hcoords j)]
            _ ≤ _ := by
              rw [mul_assoc]
              apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (5 : ℝ) ^ d)
              calc
                _ ≤ ∑ _j : Fin (gridWindowCount d k),
                    ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
                      Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * η ^ 4 *
                        (n * (2 / ↑k) ^ d) ^ 2 := Finset.sum_le_sum (fun j _ =>
                  grid_coordinate_design_energy_bound C P k n η t ξ j hkp hη ht hfield hvariance hmean)
                _ = _ := by simp
        exact mul_le_mul_of_nonneg_left
          h_grid_full_score_design_energy_bound
          (Finset.prod_nonneg (fun i _ => activation_prior_nonnegative t ht.1 ht.2 (ξ i)))
      _ = B := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]
  have hkr : 0 < ↑k := by exact_mod_cast hkp
  have hm : (gridWindowCount d k : ℝ) ≤ (2 * ↑k) ^ d := by
    have hk1 : (k : ℝ) + 1 ≤ 2 * k := by exact_mod_cast (by omega : k + 1 ≤ 2 * k)
    simpa only [gridWindowCount, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k + 1) hk1 d
  calc
    _ ≤ B := hbudget
    _ ≤ ↑5 ^ d * (2 * ↑k) ^ d *
        (K ^ 2 * Real.exp K * η ^ 4 * (n * (2 / ↑k) ^ d) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)
    _ = _ := by
      rw [show (40 : ℝ) = 5 * 2 ^ 3 by norm_num]
      have htwo : ((2 : ℝ) ^ 3) ^ d = ((2 : ℝ) ^ d) ^ 3 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 d]
      simp only [mul_pow, div_pow, htwo]
      dsimp [K]
      field_simp [ne_of_gt hkr]
def gridPathParameter  (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)
    (k : ℕ) (η t : ℝ) (ξ : Fin (gridWindowCount d k) → Fin 3)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    RegressionParameter d :=
  P.pathParameter (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ) η t ht hvariance
    (fun x => (indexedGridField_abs_bound d k η hη ξ x).trans (by nlinarith))
end
variable {α : Type*} {d n : ℕ} {s x b : ℝ}
def lowSmoothnessGridExponent (d : ℕ) (s : ℝ) : ℝ := 2 / (↑d + 4 * s)
def lowSmoothnessGrid (d : ℕ) (s x : ℝ) : ℕ := Nat.ceil (4 * x ^ lowSmoothnessGridExponent d s)
def lowSmoothnessAmplitude (d : ℕ) (s b x : ℝ) : ℝ := b / (lowSmoothnessGrid d s x : ℝ) ^ s
theorem lowSmoothnessGridExponent_pos   (hs : 0 < s) :
    0 < lowSmoothnessGridExponent d s := by
  unfold lowSmoothnessGridExponent
  positivity
theorem lowSmoothnessGrid_rounding   (hs : 0 < s) (hx : 1 ≤ x) :
    4 * x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) ∧
      (lowSmoothnessGrid d s x : ℝ) ≤ 5 * x ^ lowSmoothnessGridExponent d s := by
  have : 1 ≤ x ^ lowSmoothnessGridExponent d s :=
    Real.one_le_rpow hx (lowSmoothnessGridExponent_pos hs).le
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * x ^ lowSmoothnessGridExponent d s by positivity)
  refine ⟨Nat.le_ceil _, ?_⟩
  change (lowSmoothnessGrid d s x : ℝ) < 4 * x ^ lowSmoothnessGridExponent d s + 1 at hc
  linarith
theorem lowSmoothnessGrid_ge_four   (hs : 0 < s) (hx : 1 ≤ x) :
    4 ≤ lowSmoothnessGrid d s x := by
  have : 1 ≤ x ^ lowSmoothnessGridExponent d s :=
    Real.one_le_rpow hx (lowSmoothnessGridExponent_pos hs).le
  have := (lowSmoothnessGrid_rounding (d := d) hs hx).1
  exact_mod_cast (show ↑4 ≤ (lowSmoothnessGrid d s x : ℝ) by linarith)
theorem lowSmoothnessGrid_positive   (hs : 0 < s) (hx : 1 ≤ x) :
    0 < (lowSmoothnessGrid d s x : ℝ) := by
  have := lowSmoothnessGrid_ge_four (d := d) hs hx
  exact_mod_cast (by omega : 0 < lowSmoothnessGrid d s x)
theorem lowSmoothness_design_occupancy  
    (hs : 0 < s) (hd : 4 * s ≤ (d : ℝ)) (hx : 1 ≤ x) :
    x * (2 / (lowSmoothnessGrid d s x : ℝ)) ^ d ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hpd : 1 ≤ lowSmoothnessGridExponent d s * d := by
    unfold lowSmoothnessGridExponent
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity)).2 (by linarith)
  have hxp : x ≤ x ^ (lowSmoothnessGridExponent d s * d) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hpd
  have hgrid := pow_le_pow_left₀ (by positivity) (lowSmoothnessGrid_rounding (d := d) hs hx).1 d
  rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hgrid
  have hbudget : x * ↑2 ^ d ≤ (lowSmoothnessGrid d s x : ℝ) ^ d := by
    calc
      _ ≤ x * ↑4 ^ d := mul_le_mul_of_nonneg_left (by gcongr; norm_num) hx0.le
      _ ≤ ↑4 ^ d * x ^ (lowSmoothnessGridExponent d s * d) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxp (by positivity : 0 ≤ (4 : ℝ) ^ d)
      _ ≤ _ := hgrid
  rw [div_pow, ← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos (lowSmoothnessGrid_positive (d := d) hs hx) d)).2 (by simpa only [one_mul] using hbudget)
theorem lowSmoothness_variance_separation  
    (hs : 0 < s) (hx : 1 ≤ x) :
    b ^ 2 / ↑5 ^ (2 * s) * x ^ (-4 * s / (↑d + 4 * s)) ≤
      (lowSmoothnessAmplitude d s b x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hk := lowSmoothnessGrid_positive (d := d) hs hx
  have hupper := Real.rpow_le_rpow hk.le ((lowSmoothnessGrid_rounding (d := d) hs hx).2) (show 0 ≤ 2 * s by positivity)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (Real.rpow_pos_of_pos hx0 _).le,
    ← Real.rpow_mul hx0.le] at hupper
  have heq : lowSmoothnessGridExponent d s * (2 * s) = 4 * s / (↑d + 4 * s) := by
    unfold lowSmoothnessGridExponent
    ring
  rw [heq] at hupper
  have hright : (lowSmoothnessAmplitude d s b x) ^ 2 = b ^ 2 / (lowSmoothnessGrid d s x : ℝ) ^ (2 * s) := by
    unfold lowSmoothnessAmplitude
    rw [div_pow, ← Real.rpow_mul_natCast hk.le]
    congr 2
    norm_num
    ring
  rw [hright]
  have hleft : b ^ 2 / (↑5 ^ (2 * s) * x ^ (4 * s / (↑d + 4 * s))) =
      b ^ 2 / ↑5 ^ (2 * s) * x ^ (-4 * s / (↑d + 4 * s)) := by
    rw [show -4 * s / (↑d + 4 * s) = -(4 * s / (↑d + 4 * s)) by ring,
      Real.rpow_neg hx0.le]
    ring
  rw [← hleft]
  exact div_le_div_of_nonneg_left (sq_nonneg b) (Real.rpow_pos_of_pos hk _) hupper
theorem lowSmoothness_amplitude_legal_guards  {s b x ρ : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x)
    (hlinear : ((2 : ℝ) ^ d + 2) * b ≤ ρ) (hsquare : b ^ 2 ≤ ρ) :
    0 ≤ lowSmoothnessAmplitude d s b x ∧
      (↑2 ^ d + 2) * lowSmoothnessAmplitude d s b x ≤ ρ ∧
      (lowSmoothnessAmplitude d s b x) ^ 2 ≤ ρ := by
  have h_lowSmoothnessAmplitude_nonneg := div_nonneg hb (Real.rpow_pos_of_pos (lowSmoothnessGrid_positive (d := d) hs hx) s).le
  have hn := h_lowSmoothnessAmplitude_nonneg
  have hk : 1 ≤ (lowSmoothnessGrid d s x : ℝ) := by
    have := lowSmoothnessGrid_ge_four (d := d) hs hx
    exact_mod_cast (by omega : 1 ≤ lowSmoothnessGrid d s x)
  have h_lowSmoothnessAmplitude_le_budget := div_le_self hb (Real.one_le_rpow hk hs.le)
  have hbnd := h_lowSmoothnessAmplitude_le_budget
  refine ⟨hn, ?_, (pow_le_pow_left₀ hn hbnd 2).trans hsquare⟩
  exact (mul_le_mul_of_nonneg_left hbnd (by positivity : 0 ≤ (2 : ℝ) ^ d + 2)).trans hlinear
theorem lowSmoothness_total_score_budget  {s b x Q : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hx : 1 ≤ x) (hQ : 0 ≤ Q) :
    Q * (x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d) ≤ Q * b ^ 4 :=
  have h_lowSmoothness_numeric_score_budget {d} : x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d ≤ b ^ 4 := by
    have hk := lowSmoothnessGrid_positive (d := d) hs hx
    have h_lowSmoothness_grid_power_budget : x ^ ↑2 ≤ (lowSmoothnessGrid d s x : ℝ) ^ (↑d + 4 * s) := by
      have hx0 : 0 < x := by linarith
      have hk := lowSmoothnessGrid_positive (d := d) hs hx
      have hden : 0 < ↑d + 4 * s := by positivity
      have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) := by
        have hh := (lowSmoothnessGrid_rounding (d := d) hs hx).1
        have : 0 ≤ x ^ lowSmoothnessGridExponent d s := (Real.rpow_pos_of_pos hx0 _).le
        linarith
      have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hx0 _).le hbase hden.le
      rw [← Real.rpow_mul hx0.le] at hh
      have heq : lowSmoothnessGridExponent d s * (↑d + 4 * s) = 2 := by
        exact div_mul_cancel₀ _ hden.ne'
      rw [heq, Real.rpow_two] at hh
      exact hh
    have hid : x ^ 2 * (lowSmoothnessAmplitude d s b x) ^ 4 / (lowSmoothnessGrid d s x : ℝ) ^ d =
        b ^ 4 * (x ^ 2 / (lowSmoothnessGrid d s x : ℝ) ^ (↑d + 4 * s)) := by
      unfold lowSmoothnessAmplitude
      have hp4 : ((lowSmoothnessGrid d s x : ℝ) ^ s) ^ ↑4 =
          (lowSmoothnessGrid d s x : ℝ) ^ (4 * s) := by
        rw [← Real.rpow_mul_natCast hk.le]
        congr 1
        norm_num
        ring
      rw [div_pow, hp4, Real.rpow_add hk, Real.rpow_natCast]
      field_simp
    rw [hid]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ((div_le_one (Real.rpow_pos_of_pos hk _)).2 (h_lowSmoothness_grid_power_budget)) (by positivity : 0 ≤ b ^ ↑4)
  mul_le_mul_of_nonneg_left h_lowSmoothness_numeric_score_budget hQ
def lowSmoothnessScoreConstant  {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : ℝ :=
  ↑40 ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
    Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c)
theorem lowSmoothnessScoreConstant_nonneg  {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : 0 ≤ lowSmoothnessScoreConstant P := by
  unfold lowSmoothnessScoreConstant
  positivity
def responseIndexKernel  [MeasurableSpace α] (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel α (Fin 3) where
  toFun x := ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun y _ =>
      (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul_const _)
theorem responseIndexKernel_apply  [MeasurableSpace α] (a V )
    (F : α → ℝ) (hF : Measurable F) (x : α) :
    responseIndexKernel a V F hF x =
      ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) • Measure.dirac y := rfl
theorem responseIndexKernel_markov  [MeasurableSpace α] (a V )
    (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseIndexKernel a V F hF) := by
  constructor
  intro x
  constructor
  simp only [responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp x y), ternary_normalized a (F x) V ha]
  simp
def responseSampleIndexKernel  [MeasurableSpace α] (n : ℕ) (a V : ℝ)
    (F : α → ℝ) (hF : Measurable F) : Kernel (Fin n → α) (Fin n → Fin 3) where
  toFun x := ∑ y : Fin n → Fin 3,
    ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro y _
    apply Measurable.mul_const
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → α => F (x i))
        (hF.comp (measurable_pi_apply i)) (y i))
theorem responseSampleIndexKernel_apply  [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α) :
    responseSampleIndexKernel n a V F hF x =
      ∑ y : Fin n → Fin 3,
        ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) • Measure.dirac y := rfl
theorem responseSampleIndexKernel_markov  [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (responseSampleIndexKernel n a V F hF) := by
  constructor
  intro x
  constructor
  simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => Finset.prod_nonneg
      (fun i _ => hp (x i) (y i))), ← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]
theorem responseSampleIndexKernel_joint_map  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => μ)).compProd
      (responseSampleIndexKernel n a V F hF)).map
      (fun z : (Fin n → α) × (Fin n → Fin 3) => fun i => (z.1 i, z.2 i)) =
      Measure.pi (fun _ : Fin n => μ.compProd (responseIndexKernel a V F hF)) := by
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have hm : Measurable (fun z : (Fin n → α) × (Fin n → Fin 3) =>
      fun i => (z.1 i, z.2 i)) := by fun_prop
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage hm)]
  have hinner (x : Fin n → α) :
      responseSampleIndexKernel n a V F hF x
        (Prod.mk x ⁻¹' (fun z : (Fin n → α) × (Fin n → Fin 3) =>
          fun i => (z.1 i, z.2 i)) ⁻¹' Set.pi Set.univ s) =
        ∏ i, ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F (x i)) V y) *
          (s i).indicator 1 (x i, y) := by
    simp only [responseSampleIndexKernel_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hp (x i) _)]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Measure.dirac_apply' _ (((MeasurableSet.univ_pi hs).preimage hm).preimage measurable_prodMk_left)]
    by_cases h : ∀ i, (x i, y i) ∈ s i
    · have : ∏ i, (s i).indicator (1 : α × Fin 3 → ℝ≥0∞) (x i, y i) = 1 := by
        simp [Set.indicator_of_mem, h]
      simp [Set.indicator_of_mem, h, Set.mem_pi]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hz : (s i).indicator (1 : α × Fin 3 → ℝ≥0∞) (x i, y i) = 0 :=
        Set.indicator_of_notMem hi _
      rw [Finset.prod_mul_distrib]
      have hzero : ∏ j, (s j).indicator (1 : α × Fin 3 → ℝ≥0∞) (x j, y j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hz
      rw [hzero, mul_zero]
      simp [Set.indicator_of_notMem, Set.mem_pi, h]
  simp_rw [hinner]
  let G : Fin n → α → ℝ≥0∞ := fun i x =>
    ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) * (s i).indicator 1 (x, y)
  have hG : ∀ i, Measurable (G i) := by
    intro i
    exact Finset.measurable_sum _ (fun y _ =>
      (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul
        ((Measurable.indicator measurable_const (hs i)).comp (measurable_id.prodMk measurable_const)))
  change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ : Fin n => μ)) = _
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
    (iIndepFun_pi (fun i => (hG i).aemeasurable))
    (fun i => (hG i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval (fun _ : Fin n => μ) i).lintegral_comp (hG i), Measure.compProd_apply (hs i)]
  apply lintegral_congr
  intro x
  simp only [G, responseIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ ((hs i).preimage measurable_prodMk_left), smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  rfl
def encodeDesignResponse  (a : ℝ) :
    (Fin n → Covariate d) × (Fin n → Fin 3) → (Fin n → Observation d) :=
  fun z i => (z.1 i, ternaryValue a (z.2 i))
theorem encodeDesignResponse_measurable  (a ) :
    Measurable (encodeDesignResponse (d := d) (n := n) a) := (encodeResponse_measurable a).comp measurable_swap
theorem uniformTernaryParameter_sample_index_map 
    (n a V F) (hF : Measurable F) (ha )
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => cubeVolume d)).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (uniformTernaryParameter a V F hF ha hp) n := by
  let _ := cubeVolume_isProbability d
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  have h_uniformTernaryParameter_observation_index_map : ((cubeVolume d).compProd (responseIndexKernel a V F hF)).map
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) =
      observationLaw (uniformTernaryParameter a V F hF ha hp) := by
    let _ := cubeVolume_isProbability d
    let _ := responseIndexKernel_markov a V F hF ha hp
    let _ := ternaryErrorKernel_markov a V F hF ha hp
    have hencode : Measurable (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) :=
      measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
    have hreal : Measurable (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) :=
      measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
    ext s hs
    rw [Measure.map_apply hencode hs, observationLaw]
    change _ = (((designLaw (uniformTernaryParameter a V F hF ha hp)).compProd
      (ternaryErrorKernel a V F hF)).map (fun z : Covariate d × ℝ => (z.1, F z.1 + z.2))) s
    rw [Measure.map_apply hreal hs]
    simp only [designLaw, uniformTernaryParameter, ENNReal.ofReal_one, withDensity_const, one_smul]
    rw [Measure.compProd_apply (hs.preimage hencode), Measure.compProd_apply (hs.preimage hreal)]
    apply lintegral_congr
    intro x
    have hSreal : MeasurableSet {u : ℝ | (x, F x + u) ∈ s} :=
      hs.preimage (measurable_const.prodMk (measurable_const.add measurable_id))
    have hSindex : MeasurableSet {y : Fin 3 | (x, ternaryValue a y) ∈ s} :=
      hs.preimage (measurable_const.prodMk (measurable_of_countable _))
    simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    change Measure.dirac y {y | (x, ternaryValue a y) ∈ s} =
      Measure.dirac (ternaryValue a y - F x) {u | (x, F x + u) ∈ s}
    rw [Measure.dirac_apply' _ hSindex, Measure.dirac_apply' _ hSreal]
    have he : F x + ternaryValue a y - F x = ternaryValue a y := by ring
    by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, he, h]
  have hsingle : MeasurePreserving
      (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2))
      ((cubeVolume d).compProd (responseIndexKernel a V F hF))
      (observationLaw (uniformTernaryParameter a V F hF ha hp)) :=
    ⟨measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd),
      h_uniformTernaryParameter_observation_index_map⟩
  let _ : IsProbabilityMeasure (observationLaw (uniformTernaryParameter a V F hF ha hp)) := by
    rw [← hsingle.map_eq]
    infer_instance
  have h := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).map_eq
  rw [← responseSampleIndexKernel_joint_map (cubeVolume d) n a V F hF ha hp,
    Measure.map_map] at h
  · exact h
  · apply Measurable.of_eval
    intro i
    exact (measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)).comp
      (measurable_pi_apply i)
  · fun_prop
theorem responseSampleIndexKernel_integral  [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : Fin n → α)
    (hp : ∀ i y, 0 ≤ ternaryMass a (F (x i)) V y)
    (H : (Fin n → Fin 3) → ℝ) :
    (∫ y, H y ∂responseSampleIndexKernel n a V F hF x) =
      ∑ y, (∏ i, ternaryMass a (F (x i)) V (y i)) * H y := by
  rw [responseSampleIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => hp i (y i)))]
  · intro y _
    let _ := (Measure.dirac y).smul_finite
      (c := ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) ENNReal.ofReal_ne_top
    exact Integrable.of_finite
theorem uniformTernaryParameter_risk_formula 
    (a V F hF ha hp)
    (T : Estimator d n) (B : ℝ) (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
      (∏ i, ternaryMass a (F (x i)) V (y i)) *
        (T.val (encodeDesignResponse a (x, y)) - V) ^ 2
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) =
      meanSquaredRisk T (uniformTernaryParameter a V F hF ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  let _ : IsProbabilityMeasure (sampleLaw (uniformTernaryParameter a V F hF ha hp) n) := by
    rw [← uniformTernaryParameter_sample_index_map n a V F hF ha hp]
    infer_instance
  have hm  := (T.property.sub_const V).pow_const 2
  have hbound (z : Fin n → Observation d) : |(T.val z - V) ^ 2| ≤ (B + |V|) ^ 2 := by
    have he := (abs_sub (T.val z) V).trans (add_le_add (hB z) (le_refl |V|))
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  have hint : Integrable (fun z => (T.val z - V) ^ 2)
      (sampleLaw (uniformTernaryParameter a V F hF ha hp) n) :=
    (integrable_const ((B + |V|) ^ 2)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound z))
  have h_uniformTernaryParameter_sample_integral (H) (hH : Measurable H) (B : ℝ) (hB : ∀ z, |H z| ≤ B) : (∫ z, H z ∂sampleLaw (uniformTernaryParameter a V F hF ha hp) n) =
      ∫ x, ∑ y : Fin n → Fin 3,
        (∏ i, ternaryMass a (F (x i)) V (y i)) * H (encodeDesignResponse a (x, y))
        ∂Measure.pi (fun _ : Fin n => cubeVolume d) := by
    let _ := cubeVolume_isProbability d
    let _ := responseSampleIndexKernel_markov n a V F hF ha hp
    have hm := encodeDesignResponse_measurable (d := d) (n := n) a
    rw [← uniformTernaryParameter_sample_index_map n a V F hF ha hp,
      integral_map hm.aemeasurable hH.aestronglyMeasurable]
    have hi : Integrable (fun z => H (encodeDesignResponse a z))
        ((Measure.pi (fun _ : Fin n => cubeVolume d)).compProd
          (responseSampleIndexKernel n a V F hF)) :=
      (integrable_const B).mono' (hH.comp hm).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB _))
    rw [Measure.integral_compProd hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x =>
      responseSampleIndexKernel_integral n a V F hF x (fun i y => hp (x i) y) _)
  rw [← (h_uniformTernaryParameter_sample_integral _ hm _ hbound)]
  exact ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
theorem gridPathParameter_risk_formula 
    (C ) (P : LowSmoothnessTernaryConstants C)
    (k η t ξ hη ht hfield hvariance)
    (T : Estimator d n) (B ) (hB : ∀ z, |T.val z| ≤ B) :
    ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
      finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
        (fun ξ i => indexedGridField d k η ξ (x i)) ξ y *
        (T.val (encodeDesignResponse P.a (x, y)) - (P.v - η ^ 2 * t)) ^ 2
      ∂Measure.pi (fun _ => cubeVolume d)) =
      meanSquaredRisk T (gridPathParameter C P k η t ξ hη ht hfield hvariance) := by
  have hf (x : Covariate d) : |indexedGridField d k η ξ x| ≤ P.ρ :=
    (indexedGridField_abs_bound d k η hη ξ x).trans (by nlinarith)
  have hp (x : Covariate d) (y : Fin 3) :
      0 ≤ ternaryMass P.a (indexedGridField d k η ξ x) (P.v - η ^ 2 * t) y :=
    P.c_pos.le.trans ((P.path_legality η t _ ht hvariance (hf x)).2.2.1 y)
  simpa only [gridPathParameter, LowSmoothnessTernaryConstants.pathParameter,
    LowSmoothnessTernaryConstants.variancePath, finiteResponseLikelihood] using
    uniformTernaryParameter_risk_formula P.a (P.v - η ^ 2 * t)
      (indexedGridField d k η ξ) (indexedGridField_continuous d k η ξ).measurable
      P.a_pos.ne' hp T B hB
theorem boundedEstimator_worstCaseRisk_ne_top  (C : ModelConstants d)
    (T : BoundedEstimator C n) : worstCaseRisk C T.val ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply iSup_le
  intro θ
  exact boundedEstimator_risk_le_diameter C T θ.val θ.property
end NearlyMinimax
