module

public import NearlyMinimax.LowSmoothnessPrior

@[expose] public section

/-! # Normalized tent windows for the order-zero lower bound

The manuscript uses smooth periodic compact bumps. For `0 < s ≤ 1` only
continuity and Hölder bounds are required. Normalized finite-grid tents,
extended by coordinate clamping, provide an alternative globally continuous
partition with local support on the design cube.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

section
variable {k : ℕ} (j : Fin (k + 1)) (x : ℝ)

def clampUnit : ℝ := min 1 (max 0 x)

theorem clampUnit_mem : clampUnit x ∈ Icc 0 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem clampUnit_eq {x : ℝ} (hx : x ∈ Icc 0 1) : clampUnit x = x := by
  simp_all [clampUnit]

def gridTent : ℝ :=
  max 0 (1 - |k * clampUnit x - j.val|)

theorem gridTent_nonneg : 0 ≤ gridTent j x :=
  le_max_left _ _

theorem gridTent_le_one : gridTent j x ≤ 1 := max_le (by norm_num) (by bound)

theorem gridTent_continuous : Continuous (gridTent j) := by
  unfold gridTent clampUnit
  fun_prop

end

section
variable (k : ℕ) (x : ℝ)

/-- A nearest grid index has tent value at least one half, globally. -/
theorem gridTent_cover :
    ∃ j : Fin (k + 1), (1 / 2) ≤ gridTent j x := by
  let t := k * clampUnit x
  have ht0  := mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1
  have htk : t ≤ k := by
    simpa using mul_le_mul_of_nonneg_left (clampUnit_mem x).2 (Nat.cast_nonneg k)
  let j := Nat.floor (t + 1 / 2)
  have hfloor : j ≤ t + 1 / 2 := Nat.floor_le (by linarith)
  have hlt : t + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  have hjk : j ≤ k := by
    by_contra h
    have hj : (k : ℝ) + 1 ≤ j := by exact_mod_cast (by omega)
    linarith
  refine ⟨⟨j, by omega⟩, ?_⟩
  have hdist : |t - j| ≤ (1 / 2) := abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_trans (by bound)
    (le_max_right _ _)

def gridTentEnergy : ℝ := ∑ j : Fin (k + 1), gridTent j x ^ 2

theorem gridTentEnergy_lower : (1 / 4) ≤ gridTentEnergy k x := by
  obtain ⟨j, hj⟩ := gridTent_cover k x
  have hsq : (1 / 4) ≤ gridTent j x ^ 2 := by nlinarith
  exact hsq.trans (Finset.single_le_sum (fun i _ => sq_nonneg (gridTent i x)) (Finset.mem_univ j))

theorem gridTentEnergy_pos : 0 < gridTentEnergy k x :=
  lt_of_lt_of_le (by norm_num) (gridTentEnergy_lower k x)

theorem gridTentEnergy_continuous : Continuous (gridTentEnergy k) :=
  continuous_finsetSum _ (fun j _ => (gridTent_continuous j).pow 2)

end

section
variable {k : ℕ} (j : Fin (k + 1))

def gridWindow (x : ℝ) : ℝ :=
  gridTent j x / Real.sqrt (gridTentEnergy k x)

theorem gridWindow_nonneg (x : ℝ) : 0 ≤ gridWindow j x :=
  div_nonneg (gridTent_nonneg j x) (Real.sqrt_nonneg _)

end

/-- The normalized windows form an exact squared partition of unity. -/
theorem gridWindow_square_partition (k : ℕ) (x : ℝ) :
    (∑ j : Fin (k + 1), gridWindow j x ^ 2) = 1 := by
  simp only [gridWindow, div_pow, Real.sq_sqrt (gridTentEnergy_pos k x).le]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gridTentEnergy_pos k x))

section
variable {d k : ℕ} (j : Fin d → Fin (k + 1))

theorem gridWindow_le_one (j : Fin (k + 1)) (x : ℝ) : gridWindow j x ≤ 1 := by
  have hs : gridWindow j x ^ 2 ≤ 1 := by
    rw [← gridWindow_square_partition k x]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (gridWindow i x)) (Finset.mem_univ j)
  nlinarith

def gridTensorWindow (x : Covariate d) : ℝ :=
  ∏ i, gridWindow (j i) (x i)

theorem gridTensorWindow_continuous :
    Continuous (gridTensorWindow j) :=
  continuous_finsetProd _ (fun i _ => ((gridTent_continuous (j i)).div (gridTentEnergy_continuous k).sqrt (fun x => ne_of_gt (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)))).comp (continuous_apply i))

end

section
variable (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d)

theorem gridTensorWindow_nonneg :
    0 ≤ gridTensorWindow j x := Finset.prod_nonneg (fun i _ => gridWindow_nonneg ..)

theorem gridTensorWindow_le_one :
    gridTensorWindow j x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => gridWindow_nonneg ..)
    (fun i _ => gridWindow_le_one ..)

end

section
variable (d k : ℕ) (x y η : ℝ) (hη : 0 ≤ η) (ξ : (Fin d → Fin (k + 1)) → Fin 3)

theorem gridTensorWindow_square_partition (x : Covariate d) :
    (∑ j : Fin d → Fin (k + 1), gridTensorWindow j x ^ 2) = 1 := by
  simp only [gridTensorWindow, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i j => gridWindow j (x i) ^ 2)]
  simp [gridWindow_square_partition]

def gridTentActive : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun j => gridTent j x ≠ 0)

private theorem gridTent_active_indices {k : ℕ} {x : ℝ} {j : Fin (k + 1)}
    (hj : j ∈ gridTentActive k x) :
    j.val = Nat.floor (k * clampUnit x) ∨
      j.val = Nat.floor (k * clampUnit x) + 1 := by
  let t := k * clampUnit x
  let m := Nat.floor t
  have hne  := (Finset.mem_filter.mp hj).2
  have hd : |t - j.val| < 1 := by
    by_contra h
    exact hne (max_eq_left (by linarith))
  have hm  := Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1)
  have hlt  := Nat.lt_floor_add_one t
  have hlow : m ≤ j.val := by
    by_contra h
    have hcast : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast (by omega)
    grind
  have hhigh : j.val ≤ m + 1 := by
    by_contra h
    have hcast : (m : ℝ) + 2 ≤ j.val := by exact_mod_cast (by omega)
    grind
  grind

/-- At most two one-dimensional tents are nonzero at any point. -/
theorem gridTent_active_card : (gridTentActive k x).card ≤ 2 := by
  have hsub : (gridTentActive k x).image Fin.val ⊆
      {Nat.floor (k * clampUnit x), Nat.floor (k * clampUnit x) + 1} := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    rcases gridTent_active_indices hi with h | h <;> simp [h]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  simp_all

theorem gridWindow_eq_zero_iff {k : ℕ} (j : Fin (k + 1)) (x : ℝ) :
    gridWindow j x = 0 ↔ gridTent j x = 0 := by
  simp only [gridWindow, div_eq_zero_iff, ne_of_gt (Real.sqrt_pos.mpr (gridTentEnergy_pos k x)),
    or_false]

def gridTensorActive {d : ℕ} (k : ℕ) (x : Covariate d) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridTentActive k (x i))

theorem gridTensorWindow_eq_zero_of_not_active {d k : ℕ} (j : Fin d → Fin (k + 1))
    (x : Covariate d) (hj : j ∉ gridTensorActive k x) : gridTensorWindow j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp (by
    simpa [gridTensorActive] using hj)
  have hz : gridWindow (j i) (x i) = 0 := by
    apply (gridWindow_eq_zero_iff (j i) (x i)).mpr
    simpa [gridTentActive] using hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem gridTensor_active_card (x : Covariate d) : (gridTensorActive k x).card ≤ 2 ^ d := by
  rw [gridTensorActive, Fintype.card_piFinset]
  calc
    _ ≤ _ := Finset.prod_le_prod (fun i _ => gridTent_active_card ..)
    _ = _ := by simp

theorem clampUnit_modulus : |clampUnit x - clampUnit y| ≤ |x - y| := by
  have hmin : |clampUnit x - clampUnit y| ≤ |max 0 x - max 0 y| := by
    simpa only [clampUnit, sub_self, abs_zero,
      max_eq_right (abs_nonneg (max 0 x - max 0 y))] using
      abs_min_sub_min_le_max 1 (max 0 x) 1 (max 0 y)
  exact hmin.trans (by
    simpa using abs_max_sub_max_le_max 0 x 0 y)

theorem gridTent_modulus {k : ℕ} (j : Fin (k + 1)) (x y : ℝ) :
    |gridTent j x - gridTent j y| ≤ k * |x - y| := by
  have hmax : |gridTent j x - gridTent j y| ≤
      abs (|k * clampUnit x - j.val| - |k * clampUnit y - j.val|) := by
    have h := abs_max_sub_max_le_max 0
      (1 - |k * clampUnit x - j.val|) 0 (1 - |k * clampUnit y - j.val|)
    have hr : max 0 |(1 - |k * clampUnit x - j.val|) -
        (1 - |k * clampUnit y - j.val|)| =
        abs (|k * clampUnit x - j.val| - |k * clampUnit y - j.val|) := by
      grind
    simpa only [gridTent, sub_self, abs_zero, hr] using h
  calc
    _ ≤ _ := hmax
    _ ≤ _ :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = _ := by
      rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (clampUnit_modulus x y) (Nat.cast_nonneg k)

/-- The normalization energy has a scale-correct uniform Lipschitz bound. -/
theorem gridTentEnergy_modulus :
    |gridTentEnergy k x - gridTentEnergy k y| ≤ 8 * k * |x - y| := by
  let S := gridTentActive k x ∪ gridTentActive k y
  have hcard : S.card ≤ 4 := (Finset.card_union_le _ _).trans
    (by bound [gridTent_active_card k x, gridTent_active_card k y])
  have hzero j (hj : j ∉ S) :
      gridTent j x ^ 2 - gridTent j y ^ 2 = 0 := by
    have hx : gridTent j x = 0 := by
      have  := fun h => hj (Finset.mem_union_left _ h)
      simpa [gridTentActive] using this
    have hy : gridTent j y = 0 := by
      have  := fun h => hj (Finset.mem_union_right _ h)
      simpa [gridTentActive] using this
    simp [hx, hy]
  have hpoint (j : Fin (k + 1)) :
      |gridTent j x ^ 2 - gridTent j y ^ 2| ≤ 2 * k * |x - y| := by
    have hx0 := gridTent_nonneg j x
    have hy0 := gridTent_nonneg j y
    have hx1 := gridTent_le_one j x
    have hy1 := gridTent_le_one j y
    rw [show gridTent j x ^ 2 - gridTent j y ^ 2 =
      (gridTent j x - gridTent j y) * (gridTent j x + gridTent j y) by ring,
      abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
    nlinarith [gridTent_modulus j x y, abs_nonneg (gridTent j x - gridTent j y),
      mul_nonneg (sub_nonneg.mpr (gridTent_modulus j x y)) (add_nonneg hx0 hy0)]
  change |(∑ j, gridTent j x ^ 2) - (∑ j, gridTent j y ^ 2)| ≤ _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S)
    (fun j _ hj => hzero j hj)]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S, 2 * k * |x - y| := by bound
    _ ≤ _ := by
      simp
      have hcast : (S.card : ℝ) ≤ 4 := by exact_mod_cast hcard
      nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]

theorem gridTentEnergy_sqrt_lower :
    (1 / 2) ≤ Real.sqrt (gridTentEnergy k x) := by
  nlinarith [Real.sqrt_nonneg (gridTentEnergy k x),
    Real.sq_sqrt (gridTentEnergy_pos k x).le, gridTentEnergy_lower k x]

theorem gridTentEnergy_sqrt_modulus :
    let root := Real.sqrt (gridTentEnergy k x) - Real.sqrt (gridTentEnergy k y)
    |root| ≤ 8 * k * |x - y| := by
  intro root
  have hx := gridTentEnergy_sqrt_lower k x
  have hy := gridTentEnergy_sqrt_lower k y
  have hid : |gridTentEnergy k x - gridTentEnergy k y| =
      |root| *
        (Real.sqrt (gridTentEnergy k x) + Real.sqrt (gridTentEnergy k y)) := by
    conv_lhs => rw [← Real.sq_sqrt (gridTentEnergy_pos k x).le, ← Real.sq_sqrt (gridTentEnergy_pos k y).le]
    rw [show Real.sqrt (gridTentEnergy k x) ^ 2 - Real.sqrt (gridTentEnergy k y) ^ 2 =
      (root) *
        (Real.sqrt (gridTentEnergy k x) + Real.sqrt (gridTentEnergy k y)) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))]
  have hb := gridTentEnergy_modulus k x y
  nlinarith [abs_nonneg (root)]

theorem gridWindow_modulus {k : ℕ} (j : Fin (k + 1)) (x y : ℝ) :
    |gridWindow j x - gridWindow j y| ≤ 34 * k * |x - y| := by
  let A := Real.sqrt (gridTentEnergy k x)
  let B := Real.sqrt (gridTentEnergy k y)
  have hA  := gridTentEnergy_sqrt_lower k x
  have hB  := gridTentEnergy_sqrt_lower k y
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hAB : (1 / 4) ≤ A * B := by nlinarith
  have hroot : |B - A| ≤ 8 * k * |x - y| := by
    simpa only [abs_sub_comm] using gridTentEnergy_sqrt_modulus k x y
  have hfirst : |(gridTent j x - gridTent j y) / A| ≤ 2 * k * |x - y| := by
    rw [abs_div, abs_of_pos hAp]
    apply (div_le_iff₀ hAp).mpr
    have htent := gridTent_modulus j x y
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (x - y))]
  have hsecond : |gridTent j y * (B - A) / (A * B)| ≤ 32 * k * |x - y| := by
    rw [abs_div, abs_mul, abs_of_nonneg (gridTent_nonneg j y), abs_of_pos (mul_pos hAp hBp)]
    apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    have htent := gridTent_le_one j y
    have habs := abs_nonneg (B - A)
    nlinarith
  have hid : gridWindow j x - gridWindow j y =
      (gridTent j x - gridTent j y) / A + gridTent j y * (B - A) / (A * B) := by
    change gridTent j x / A - gridTent j y / B = _
    field_simp <;> ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

private theorem bounded_product_modulus {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hp : |∏ j ∈ s, f j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hh := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    rw [show f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
      (f i - g i) * (∏ j ∈ s, f j) + g i * ((∏ j ∈ s, f j) - (∏ j ∈ s, g j)) by ring]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ |f i - g i| + ∑ j ∈ s, |f j - g j| := by
        rw [abs_mul]
        exact add_le_add (by bound)
          (by simpa using mul_le_mul (hg i (Finset.mem_insert_self _ _)) hh (abs_nonneg _) (by norm_num))

theorem gridTensorWindow_modulus {d k : ℕ} (j : Fin d → Fin (k + 1)) (x y : Covariate d) :
    |gridTensorWindow j x - gridTensorWindow j y| ≤
      34 * k * d * euclideanNorm (x - y) := by
  have hh := bounded_product_modulus Finset.univ
    (fun i => gridWindow (j i) (x i)) (fun i => gridWindow (j i) (y i))
    (fun i _ => by grind [gridWindow_nonneg (j i) (x i), gridWindow_le_one (j i) (x i)])
    (fun i _ => by grind [gridWindow_nonneg (j i) (y i), gridWindow_le_one (j i) (y i)])
  calc
    _ ≤ _ := hh
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact (gridWindow_modulus (j i) (x i) (y i)).trans
        (mul_le_mul_of_nonneg_left (abs_coordinate_le_euclideanNorm (x - y) i) (by positivity))
    _ = _ := by simp; ring

def gridPriorField {d k : ℕ} (η : ℝ) (ξ : (Fin d → Fin (k + 1)) → Fin 3)
    (x : Covariate d) : ℝ :=
  η * ∑ j, gridTensorWindow j x * ternaryValue 1 (ξ j)

theorem ternaryValue_one_abs_le (y : Fin 3) : |ternaryValue 1 y| ≤ 1 := by
  fin_cases y <;> norm_num [ternaryValue]

theorem gridPriorField_abs_bound {η : ℝ} (hη : 0 ≤ η)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (x : Covariate d) :
    |gridPriorField η ξ x| ≤ 2 ^ d * η := by
  have heq : (∑ j, gridTensorWindow j x * ternaryValue 1 (ξ j)) =
      ∑ j ∈ gridTensorActive k x, gridTensorWindow j x * ternaryValue 1 (ξ j) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [gridTensorWindow_eq_zero_of_not_active j x hj]
  rw [gridPriorField, abs_mul, abs_of_nonneg hη, heq]
  have hsum : |∑ j ∈ gridTensorActive k x,
      gridTensorWindow j x * ternaryValue 1 (ξ j)| ≤ 2 ^ d := by
    calc
      _ ≤ _ :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ gridTensorActive k x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (gridTensorWindow_nonneg ..)]
        bound [gridTensorWindow_le_one d k j x, ternaryValue_one_abs_le (ξ j)]
      _ ≤ _ := by
        simp
        exact_mod_cast gridTensor_active_card ..
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsum hη

include hη in
theorem gridPriorField_lipschitz_bound (x y : Covariate d) :
    |gridPriorField η ξ x - gridPriorField η ξ y| ≤
      (68 * 2 ^ d * (d + 1)) * η * k * euclideanNorm (x - y) := by
  let S := gridTensorActive k x ∪ gridTensorActive k y
  have hcard : S.card ≤ 2 * (2 : ℝ) ^ d := by
    have h := (Finset.card_union_le (gridTensorActive k x) (gridTensorActive k y)).trans
      (Nat.add_le_add (gridTensor_active_card ..) (gridTensor_active_card ..))
    have hcast : (S).card ≤
        2 ^ d + (2 : ℝ) ^ d := by exact_mod_cast h
    bound
  have hzero j (hj : j ∉ S) :
      (gridTensorWindow j x - gridTensorWindow j y) * ternaryValue 1 (ξ j) = 0 := by
    grind [gridTensorWindow_eq_zero_of_not_active j x (fun h => hj (Finset.mem_union_left _ h)), gridTensorWindow_eq_zero_of_not_active j y (fun h => hj (Finset.mem_union_right _ h))]
  have hn : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
  have hpoint j :
      |(gridTensorWindow j x - gridTensorWindow j y) * ternaryValue 1 (ξ j)| ≤
        34 * k * d * euclideanNorm (x - y) := by
    simpa using mul_le_mul (gridTensorWindow_modulus ..)
      (ternaryValue_one_abs_le (ξ j)) (abs_nonneg _) (by positivity)
  have hsum : |∑ j ∈ S, (gridTensorWindow j x - gridTensorWindow j y) *
      ternaryValue 1 (ξ j)| ≤ 68 * 2 ^ d * (d + 1) * k * euclideanNorm (x - y) := by
    calc
      _ ≤ _ :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S, 34 * k * d * euclideanNorm (x - y) :=
        by bound
      _ = S.card * (34 * k * d * euclideanNorm (x - y)) := by simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hcard
          (by positivity : 0 ≤ 34 * k * d * euclideanNorm (x - y))
        nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d * k) hn]
  rw [gridPriorField, gridPriorField, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj),
    abs_mul, abs_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left hsum hη).trans_eq (by ring)

end

/-- Interpolation of a uniform oscillation bound and a scale `k` Lipschitz bound. -/
theorem scaled_lipschitz_holder_bound (s b k A r u : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hb : 0 ≤ b) (hk : 0 < k) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hbounded : u ≤ A * (b / k ^ s)) (hlip : u ≤ A * (b / k ^ s) * k * r) :
    u ≤ A * b * r ^ s := by
  have hcoef : 0 ≤ A * (b / k ^ s) := by positivity
  have heq : A * (b / k ^ s) * (k * r) ^ s = A * b * r ^ s := by
    rw [(Real.mul_rpow hk.le hr)]
    field_simp
  by_cases hkr : k * r ≤ 1
  · have hsmall := Real.self_le_rpow_of_le_one (mul_nonneg hk.le hr) hkr hs1
    nlinarith
  · have hlarge := Real.one_le_rpow (le_of_lt (lt_of_not_ge hkr)) hs
    nlinarith

section
variable {d k : ℕ} (j : Fin d → Fin (k + 1))

theorem gridPriorField_holder_bound {s b : ℝ} (hk : 1 ≤ k)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hb : 0 ≤ b)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (x y : Covariate d) :
    let priorField := gridPriorField (b / k ^ s) ξ
    |priorField x - priorField y| ≤
      (68 * 2 ^ d * (d + 1)) * b * euclideanNorm (x - y) ^ s := by
  intro priorField
  have hη : 0 ≤ b / k ^ s := by positivity
  apply scaled_lipschitz_holder_bound s b k (68 * 2 ^ d * (d + 1)) _ _ hs hs1 hb
    (by positivity) (by positivity) (Real.sqrt_nonneg _)
  · have hx := gridPriorField_abs_bound d k hη ξ x
    have hy := gridPriorField_abs_bound d k hη ξ y
    have hab : |priorField x -
        priorField y| ≤
          |priorField x| + |priorField y| :=
      by
        grind
    nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d) hη]
  · solve_by_elim [gridPriorField_lipschitz_bound]

/-- A support patch, defined globally through the same clamp as its window. -/
def gridPatch : Set (Covariate d) :=
  {x | ∀ i, |k * clampUnit (x i) - (j i).val| ≤ 1}

theorem gridPatch_measurable (d k : ℕ) (j : Fin d → Fin (k + 1)) :
    MeasurableSet (gridPatch j) := by
  have heq : gridPatch j = ⋂ i, {x |
      |k * clampUnit (x i) - (j i).val| ≤ 1} := by
    ext x
    simp [gridPatch]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le
  · have hc : Continuous (fun x : Covariate d => |k * clampUnit (x i) - (j i).val|) := by
      unfold clampUnit
      fun_prop
    exact hc.measurable
  · exact measurable_const

theorem gridTensorWindow_zero_outside_patch (d k : ℕ) {j : Fin d → Fin (k + 1)}
    (x : Covariate d) (hx : x ∉ gridPatch j) : gridTensorWindow j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) ((gridWindow_eq_zero_iff (j i) (x i)).mpr (max_eq_left (by linarith [lt_of_not_ge hi])))

/-- Actual uniform-design patch probability has the required volume scaling. -/
theorem gridPatch_cube_probability_bound (d k : ℕ) (j : Fin d → Fin (k + 1)) (hk : 0 < k) :
    (cubeVolume d).real (gridPatch j) ≤ (2 / k) ^ d := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  let R  := Set.univ.pi
    (fun i => Icc (((j i).val - 1 : ℝ) / k) (((j i).val + 1) / k))
  have hsub : gridPatch j ∩ unitCube d ⊆ R := by
    intro x hx
    intro i _
    have hi := hx.1 i
    rw [clampUnit_eq (hx.2 i)] at hi
    constructor
    · apply (div_le_iff₀ hkp).mpr
      linarith [(abs_le.mp hi).1]
    · apply (le_div_iff₀ hkp).mpr
      linarith [(abs_le.mp hi).2]
  have hvol : volume R = ENNReal.ofReal ((2 / k) ^ d) := by
    rw [volume_pi, Measure.pi_pi]
    simp
    have hwidth i : (((j i).val + 1) / k) - (((j i).val - 1 : ℝ) / k) = 2 / k := by ring
    simp_rw [hwidth]
    simp
    exact (ENNReal.ofReal_pow (by positivity) d).symm
  have hbound : cubeVolume d (gridPatch j) ≤ ENNReal.ofReal ((2 / k) ^ d) := by
    rw [cubeVolume, Measure.restrict_apply (gridPatch_measurable ..), ← hvol]
    exact measure_mono hsub
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

def gridNeighbors (j : Fin (k + 1)) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun l => |(j.val : ℝ) - l.val| ≤ 2)

theorem gridNeighbors_card (j : Fin (k + 1)) : (gridNeighbors j).card ≤ 5 := by
  have hsub : (gridNeighbors j).image Fin.val ⊆ Finset.Icc (j.val - 2) (j.val + 2) := by
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

def gridTensorNeighbors : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridNeighbors (j i))

theorem gridTensorNeighbors_card :
    (gridTensorNeighbors j).card ≤ 5 ^ d := by
  rw [gridTensorNeighbors, Fintype.card_piFinset]
  calc
    _ ≤ _ := Finset.prod_le_prod (fun i _ => gridNeighbors_card (j i))
    _ = _ := by simp

theorem gridPatch_common_point_neighbors {j l : Fin d → Fin (k + 1)}
    {x : Covariate d} (hj : x ∈ gridPatch j) (hl : x ∈ gridPatch l) :
    l ∈ gridTensorNeighbors j := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_filter.mpr
  grind [abs_le.mp (hj i), abs_le.mp (hl i)]

end

/-- Every actual observation-support graph has uniformly bounded closed degree. -/
theorem grid_observed_patch_degree (d k n : ℕ) (x : DesignSample d n)
    (j : Fin d → Fin (k + 1)) :
    (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch j)
        (Finset.univ.filter fun i => x i ∈ gridPatch l)).card ≤ 5 ^ d := by
  exact (Finset.card_le_card (by
    intro l hl
    obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hl).2
    grind [gridPatch_common_point_neighbors])).trans (gridTensorNeighbors_card j)

end NearlyMinimax
