module

public import NearlyMinimax.FiniteBounds
public import NearlyMinimax.HighSmoothnessWindows

public import NearlyMinimax.LowSmoothnessPrior

@[expose] public section

/-! The low-smoothness grid uses the same squared partition profile as
 the high-smoothness prior. Clamping to the unit cube keeps only finitely
 many translates and gives a global Hölder bound. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal

namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

def clampUnit (x : ℝ) : ℝ := min 1 (max 0 x)

section
variable (x : ℝ)

theorem clampUnit_mem : clampUnit x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply le_min <;> positivity
  · exact min_le_left _ _

theorem clampUnit_eq (hx : x ∈ Icc (0 : ℝ) 1) : clampUnit x = x := by
  simp [clampUnit, max_eq_right hx.1, min_eq_right hx.2]

end

private def gridIntegerIndex (k : ℕ) : Fin (k+1) ↪ ℤ :=
  ⟨fun j => j.val, fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩

private theorem gridIntegerIndex_apply (k : ℕ) (j : Fin (k+1)) : gridIntegerIndex k j = (j.val : ℤ) := rfl

def gridWindow (k : ℕ) (j : Fin (k+1)) (x : ℝ) : ℝ :=
  highWindowProfile ((k : ℝ) * clampUnit x - j.val)

section
variable (k : ℕ)

theorem gridWindow_nonneg (j : Fin (k+1)) (x : ℝ) : 0 ≤ gridWindow k j x :=
  highWindowProfile_nonneg _

theorem gridWindow_continuous (j : Fin (k+1)) : Continuous (gridWindow k j) := by
  unfold gridWindow
  apply highWindowProfile_contDiff.continuous.comp
  unfold clampUnit
  fun_prop

/-- Clamping puts all nonzero integer translates among the grid indices. -/
theorem gridWindow_square_partition (x : ℝ) :
    (∑ j : Fin (k+1), gridWindow k j x ^ 2) = 1 := by
  let t := (k : ℝ) * clampUnit x
  have h0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) (clampUnit_mem x).1
  have h1 : t ≤ k := mul_le_of_le_one_right (Nat.cast_nonneg _) (clampUnit_mem x).2
  let f (z : ℤ) := highWindowProfile (t-z)^2
  have hS : Function.support f ⊆ ↑(Finset.univ.map (gridIntegerIndex k)) := by
    intro z hz
    have hd : |t - (z : ℝ)| < 3/4 := lt_of_not_ge fun h => hz (by simp [f, highWindowProfile_eq_zero _ h])
    have hlo : 0 ≤ z := by
      by_contra! hn
      have : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
      linarith [(abs_lt.mp hd).2]
    have hhi : z ≤ (k : ℤ) := by
      by_contra! hn
      have : (k : ℝ)+1 ≤ z := by exact_mod_cast (show (k : ℤ)+1 ≤ z by omega)
      linarith [(abs_lt.mp hd).1]
    have hz' := Int.toNat_of_nonneg hlo
    exact Finset.mem_map.mpr ⟨⟨z.toNat, by omega⟩, Finset.mem_univ _, hz'⟩
  have h := highWindowProfile_sq_partition t
  change (∑ᶠ z, f z) = 1 at h
  rw [finsum_eq_finsetSum_of_support_subset f hS, Finset.sum_map] at h
  simpa only [f, t, gridWindow, gridIntegerIndex_apply, Int.cast_natCast] using h

theorem gridWindow_le_one (j : Fin (k + 1)) (x : ℝ) : gridWindow k j x ≤ 1 := by
  have hs : gridWindow k j x ^ 2 ≤ 1 := by
    rw [← gridWindow_square_partition k x]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (gridWindow k i x)) (Finset.mem_univ j)
  nlinarith [gridWindow_nonneg k j x]

end

def gridTensorWindow (d k : ℕ) (j : Fin d → Fin (k + 1)) (x : Covariate d) : ℝ :=
  ∏ i, gridWindow k (j i) (x i)

section
variable (d k : ℕ)

theorem gridTensorWindow_continuous (j : Fin d → Fin (k + 1)) :
    Continuous (gridTensorWindow d k j) :=
  continuous_finsetProd _ (fun i _ => (gridWindow_continuous k (j i)).comp (continuous_apply i))

theorem gridTensorWindow_nonneg (j : Fin d → Fin (k + 1)) (x : Covariate d) :
    0 ≤ gridTensorWindow d k j x := Finset.prod_nonneg (fun i _ => gridWindow_nonneg k (j i) (x i))

theorem gridTensorWindow_le_one (j : Fin d → Fin (k + 1)) (x : Covariate d) :
    gridTensorWindow d k j x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => gridWindow_nonneg k (j i) (x i))
    (fun i _ => gridWindow_le_one k (j i) (x i))

theorem gridTensorWindow_square_partition (x : Covariate d) :
    (∑ j : Fin d → Fin (k + 1), gridTensorWindow d k j x ^ 2) = 1 := by
  simp only [gridTensorWindow, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (j : Fin (k + 1)) => gridWindow k j (x i) ^ 2)]
  simp [gridWindow_square_partition]

end

def gridWindowActive (k : ℕ) (x : ℝ) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun j => gridWindow k j x ≠ 0)

section
variable (k : ℕ)

theorem gridWindow_active_card (x : ℝ) : (gridWindowActive k x).card ≤ 2 := by
  let t := (k : ℝ) * clampUnit x
  have hs : (gridWindowActive k x).map (gridIntegerIndex k) ⊆ {⌊t⌋, ⌊t⌋+1} := by
    simp only [Finset.subset_iff, Finset.mem_map]
    rintro z ⟨j, hj, rfl⟩
    have hd : |t - (j.val : ℝ)| ≤ 3/4 := le_of_not_ge fun hh => (Finset.mem_filter.mp hj).2
      (highWindowProfile_eq_zero _ hh)
    simp only [gridIntegerIndex_apply, Finset.mem_insert, Finset.mem_singleton]
    exact integer_close_three_quarters t j.val hd
  simpa [Finset.card_map] using (Finset.card_le_card hs).trans (Finset.card_insert_le ..)

end

def gridTensorActive (d k : ℕ) (x : Covariate d) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridWindowActive k (x i))

section
variable (d k : ℕ)

theorem gridTensorWindow_eq_zero_of_not_active (j : Fin d → Fin (k + 1))
    (x : Covariate d) (hj : j ∉ gridTensorActive d k x) : gridTensorWindow d k j x = 0 := by
  have hnot : ¬∀ i, j i ∈ gridWindowActive k (x i) := by
    simpa [gridTensorActive, Fintype.mem_piFinset] using hj
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hz : gridWindow k (j i) (x i) = 0 := by simpa [gridWindowActive] using hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem gridTensor_active_card (x : Covariate d) : (gridTensorActive d k x).card ≤ 2 ^ d := by
  rw [gridTensorActive, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 2 := Finset.prod_le_prod (fun i _ => gridWindow_active_card k (x i))
    _ = _ := by simp

end

theorem clampUnit_modulus (x y : ℝ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  have h : LipschitzWith 1 clampUnit := (LipschitzWith.id.const_max 0).const_min 1
  simpa [Real.dist_eq] using h.dist_le_mul x y

private theorem abs_sum_support_le {ι : Type*} [Fintype ι]
    {S : Finset ι} {f : ι → ℝ} {A : ℝ}
    (hzero : ∀ j ∉ S, f j = 0) (hbound : ∀ j ∈ S, |f j| ≤ A) :
    |∑ j, f j| ≤ (S.card : ℝ) * A := by
  simpa only [Real.norm_eq_abs] using norm_sum_le_support_card_mul hzero
    (by simpa only [Real.norm_eq_abs] using hbound)

theorem highWindowProfile_lipschitz_exists : ∃ K, LipschitzWith K highWindowProfile :=
  ContDiff.lipschitzWith_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (3/4)) fun x hx =>
      highWindowProfile_eq_zero x (le_of_not_ge (by simpa [Metric.mem_closedBall, Real.dist_eq] using hx)))
    highWindowProfile_contDiff (by simp)

/-- A common Lipschitz constant for translates of the profile, before dilation. -/
def gridWindowSlope : ℝ≥0 := max 1 (Classical.choose highWindowProfile_lipschitz_exists)

private theorem gridWindowSlope_ge_one : (1 : ℝ) ≤ gridWindowSlope := by
  exact_mod_cast (le_max_left (1 : ℝ≥0) (Classical.choose highWindowProfile_lipschitz_exists))

theorem gridWindow_modulus (k : ℕ) (j : Fin (k+1)) (x y : ℝ) :
    |gridWindow k j x - gridWindow k j y| ≤ (gridWindowSlope : ℝ) * k * |x-y| := by
  have h : LipschitzWith gridWindowSlope highWindowProfile :=
    LipschitzWith.weaken (Classical.choose_spec highWindowProfile_lipschitz_exists) (le_max_right _ _)
  have hh := h.dist_le_mul ((k : ℝ) * clampUnit x - j.val) ((k : ℝ) * clampUnit y - j.val)
  simp only [Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub, abs_mul,
    abs_of_nonneg (show 0 ≤ (k : ℝ) from Nat.cast_nonneg k)] at hh
  refine hh.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (clampUnit_modulus x y) (Nat.cast_nonneg k)) (NNReal.coe_nonneg _)

attribute [-instance] Classical.propDecidable in
private theorem bounded_product_modulus {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i - g i| := by
  have he := Finset.prod_sub_ordered s f (fun i => f i - g i)
  simp only [sub_sub_cancel] at he
  rw [he, sub_sub_cancel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc
    _ ≤ |f i - g i| * 1 * 1 := by
      simp only [abs_mul]
      gcongr <;> apply abs_prod_le_one <;> intro j hj
      · exact hg j (Finset.mem_filter.mp hj).1
      · exact hf j (Finset.mem_filter.mp hj).1
    _ = _ := by simp

theorem gridTensorWindow_modulus (d k : ℕ) (j : Fin d → Fin (k + 1)) (x y : Covariate d) :
    |gridTensorWindow d k j x - gridTensorWindow d k j y| ≤
      (gridWindowSlope : ℝ) * k * d * euclideanNorm (x - y) := by
  have hh := bounded_product_modulus (Finset.univ : Finset (Fin d))
    (fun i => gridWindow k (j i) (x i)) (fun i => gridWindow k (j i) (y i))
    (fun i _ => by rw [abs_of_nonneg (gridWindow_nonneg k (j i) (x i))]; exact gridWindow_le_one ..)
    (fun i _ => by rw [abs_of_nonneg (gridWindow_nonneg k (j i) (y i))]; exact gridWindow_le_one ..)
  calc
    _ ≤ ∑ i, |gridWindow k (j i) (x i) - gridWindow k (j i) (y i)| := hh
    _ ≤ ∑ _i : Fin d, (gridWindowSlope : ℝ) * (k : ℝ) * euclideanNorm (x - y) := by
      refine Finset.sum_le_sum fun i _ => (gridWindow_modulus k (j i) (x i) (y i)).trans ?_
      gcongr
      exact abs_coordinate_le_euclideanNorm (x - y) i
    _ = _ := by simp; ring

def gridPriorField (d k : ℕ) (η : ℝ) (ξ : (Fin d → Fin (k + 1)) → Fin 3)
    (x : Covariate d) : ℝ :=
  η * ∑ j, gridTensorWindow d k j x * ternaryValue 1 (ξ j)

theorem gridPriorField_continuous (d k : ℕ) (η : ℝ)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) : Continuous (gridPriorField d k η ξ) :=
  (continuous_finsetSum _ (fun j _ => (gridTensorWindow_continuous d k j).mul_const _)).const_mul _

theorem ternaryValue_one_abs_le (y : Fin 3) : |ternaryValue 1 y| ≤ 1 := by
  fin_cases y <;> norm_num [ternaryValue]

def gridPriorSlope (d : ℕ) : ℝ := 2 * gridWindowSlope * (2 : ℝ)^d * (d+1)

theorem gridPriorSlope_nonneg (d : ℕ) : 0 ≤ gridPriorSlope d := by
  unfold gridPriorSlope
  positivity

def gridHolderBudget (d : ℕ) : ℝ := (2 : ℝ)^d + gridPriorSlope d

theorem gridHolderBudget_pos (d : ℕ) : 0 < gridHolderBudget d :=
  add_pos_of_pos_of_nonneg (by positivity) (gridPriorSlope_nonneg d)

section
variable (d k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3)
include hη

theorem gridPriorField_abs_bound (x : Covariate d) :
    |gridPriorField d k η ξ x| ≤ (2 : ℝ) ^ d * η := by
  rw [gridPriorField, abs_mul, abs_of_nonneg hη, mul_comm ((2 : ℝ)^d)]
  apply mul_le_mul_of_nonneg_left _ hη
  have hs := abs_sum_support_le (S := gridTensorActive d k x)
    (f := fun j => gridTensorWindow d k j x * ternaryValue 1 (ξ j)) (A := 1)
    (fun j hj => by simp [gridTensorWindow_eq_zero_of_not_active d k j x hj]) (fun j _ => by
      rw [abs_mul, abs_of_nonneg (gridTensorWindow_nonneg d k j x)]
      simpa using mul_le_mul (gridTensorWindow_le_one d k j x) (ternaryValue_one_abs_le (ξ j))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  refine hs.trans ?_
  rw [mul_one]
  exact_mod_cast gridTensor_active_card d k x

theorem gridPriorField_lipschitz_bound (x y : Covariate d) :
    |gridPriorField d k η ξ x - gridPriorField d k η ξ y| ≤
      gridPriorSlope d * η * k * euclideanNorm (x - y) := by
  let S := gridTensorActive d k x ∪ gridTensorActive d k y
  have hcard : (S.card : ℝ) ≤ 2 * (2 : ℝ) ^ d := by
    rw [two_mul]
    exact_mod_cast (Finset.card_union_le _ _).trans
      (Nat.add_le_add (gridTensor_active_card d k x) (gridTensor_active_card d k y))
  have hzero (j : Fin d → Fin (k + 1)) (hj : j ∉ S) :
      (gridTensorWindow d k j x - gridTensorWindow d k j y) * ternaryValue 1 (ξ j) = 0 := by
    simp only [S, Finset.mem_union, not_or] at hj
    simp [gridTensorWindow_eq_zero_of_not_active d k j x hj.1,
      gridTensorWindow_eq_zero_of_not_active d k j y hj.2]
  have hsum := abs_sum_support_le hzero (A := (gridWindowSlope : ℝ) * (k : ℝ) * d * euclideanNorm (x-y)) (fun j _ => by
    rw [abs_mul]
    simpa using mul_le_mul (gridTensorWindow_modulus d k j x y)
      (ternaryValue_one_abs_le (ξ j)) (abs_nonneg _) (by unfold euclideanNorm; positivity))
  rw [gridPriorField, gridPriorField, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [abs_mul, abs_of_nonneg hη]
  refine (mul_le_mul_of_nonneg_left hsum hη).trans ?_
  calc
    _ ≤ η * (2 * (2 : ℝ)^d * ((gridWindowSlope : ℝ) * k * (d + 1) * euclideanNorm (x-y))) := by
      have := Real.sqrt_nonneg (∑ j, (x-y) j ^ 2)
      change 0 ≤ euclideanNorm (x-y) at this
      gcongr
      linarith
    _ = _ := by unfold gridPriorSlope; ring

end

theorem gridPriorField_holder_bound (d k : ℕ) (s b : ℝ) (hk : 1 ≤ k)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hb : 0 ≤ b)
    (ξ : (Fin d → Fin (k + 1)) → Fin 3) (x y : Covariate d) :
    |gridPriorField d k (b / (k : ℝ) ^ s) ξ x - gridPriorField d k (b / (k : ℝ) ^ s) ξ y| ≤
      gridPriorSlope d * b * euclideanNorm (x - y) ^ s := by
  have hkp : 0 < (k : ℝ) := by positivity
  have hη : 0 ≤ b / (k : ℝ) ^ s := by positivity
  apply le_rpow_of_scaled_uniform_and_linear hkp (Real.sqrt_nonneg _)
    (mul_nonneg (gridPriorSlope_nonneg d) hb) hs hs1 <;> rw [mul_div_assoc]
  · have hx := gridPriorField_abs_bound d k _ hη ξ x
    have hy := gridPriorField_abs_bound d k _ hη ξ y
    have hab := abs_sub (gridPriorField d k (b / (k : ℝ) ^ s) ξ x)
      (gridPriorField d k (b / (k : ℝ) ^ s) ξ y)
    have hcap : 2*(2 : ℝ)^d ≤ gridPriorSlope d := by
      unfold gridPriorSlope
      calc
        _ = 2*(1 : ℝ)*(2 : ℝ)^d*1 := by ring
        _ ≤ _ := by gcongr <;> first | exact gridWindowSlope_ge_one | linarith
    exact (hab.trans (add_le_add hx hy)).trans (by
      have h := mul_le_mul_of_nonneg_right hcap hη
      linarith only [h])
  · apply gridPriorField_lipschitz_bound <;> assumption

/-- A support patch, defined globally through the same clamp as its window. -/
def gridPatch (d k : ℕ) (j : Fin d → Fin (k + 1)) : Set (Covariate d) :=
  {x | ∀ i, |(k : ℝ) * clampUnit (x i) - (j i).val| ≤ 1}

section
variable (d k : ℕ) (j : Fin d → Fin (k + 1))

theorem gridPatch_measurable :
    MeasurableSet (gridPatch d k j) := by
  have heq : gridPatch d k j = ⋂ i : Fin d, {x : Covariate d |
      |(k : ℝ) * clampUnit (x i) - (j i).val| ≤ 1} := by
    ext x
    simp [gridPatch]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le
  · have hc : Continuous (fun x : Covariate d => |(k : ℝ) * clampUnit (x i) - (j i).val|) := by
      unfold clampUnit
      fun_prop
    exact hc.measurable
  · exact measurable_const

theorem gridTensorWindow_zero_outside_patch
    (x : Covariate d) (hx : x ∉ gridPatch d k j) : gridTensorWindow d k j x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (highWindowProfile_eq_zero _ (by linarith [lt_of_not_ge hi]))

/-- Actual uniform-design patch probability has the required volume scaling. -/
theorem gridPatch_cube_probability_bound (hk : 0 < k) :
    (cubeVolume d).real (gridPatch d k j) ≤ (2 / (k : ℝ)) ^ d := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  let R := Set.univ.pi
    (fun i => Icc (((j i).val - 1 : ℝ) / k) (((j i).val + 1 : ℝ) / k))
  have hsub : gridPatch d k j ∩ unitCube d ⊆ R := by
    intro x hx
    rw [Set.mem_pi]
    intro i _
    have hi := hx.1 i
    rw [clampUnit_eq (x i) (hx.2 i)] at hi
    constructor
    · apply (div_le_iff₀ hkp).mpr <;> grind
    · apply (le_div_iff₀ hkp).mpr <;> grind
  have hvol : volume R = ENNReal.ofReal ((2 / (k : ℝ)) ^ d) := by
    dsimp [R]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc]
    have hwidth (i : Fin d) : (((j i).val + 1 : ℝ) / k) - (((j i).val - 1 : ℝ) / k) = 2 / k := by ring
    simpa [hwidth] using (ENNReal.ofReal_pow (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hkp.le) d).symm
  have hbound : cubeVolume d (gridPatch d k j) ≤ ENNReal.ofReal ((2 / (k : ℝ)) ^ d) := by
    rw [cubeVolume, Measure.restrict_apply (gridPatch_measurable d k j), ← hvol] <;> gcongr
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end

def gridNeighbors (k : ℕ) (j : Fin (k + 1)) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun l => |(j.val : ℝ) - l.val| ≤ 2)

theorem gridNeighbors_card (k : ℕ) (j : Fin (k + 1)) : (gridNeighbors k j).card ≤ 5 := by
  have hsub : (gridNeighbors k j).image Fin.val ⊆ Finset.Icc (j.val - 2) (j.val + 2) := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    have hdist := (Finset.mem_filter.mp hi).2
    have hl1 : j.val ≤ i.val + 2 := by exact_mod_cast (by grind :
      (j.val : ℝ) ≤ i.val + 2)
    have hl2 : i.val ≤ j.val + 2 := by exact_mod_cast (by grind :
      (i.val : ℝ) ≤ j.val + 2)
    simp_all
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h
  omega

def gridTensorNeighbors (d k : ℕ) (j : Fin d → Fin (k + 1)) : Finset (Fin d → Fin (k + 1)) :=
  Fintype.piFinset (fun i => gridNeighbors k (j i))

section
variable (d k : ℕ)

theorem gridTensorNeighbors_card (j : Fin d → Fin (k + 1)) :
    (gridTensorNeighbors d k j).card ≤ 5 ^ d := by
  rw [gridTensorNeighbors, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 5 := Finset.prod_le_prod (fun i _ => gridNeighbors_card k (j i))
    _ = _ := by simp

theorem gridPatch_common_point_neighbors (j l : Fin d → Fin (k + 1))
    (x : Covariate d) (hj : x ∈ gridPatch d k j) (hl : x ∈ gridPatch d k l) :
    l ∈ gridTensorNeighbors d k j := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hj' := abs_le.mp (hj i)
  have hl' := abs_le.mp (hl i)
  grind

end

/-- Every actual observation-support graph has uniformly bounded closed degree. -/
theorem grid_observed_patch_degree (d k n : ℕ) (x : Fin n → Covariate d)
    (j : Fin d → Fin (k + 1)) :
    (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l)).card ≤ 5 ^ d := by
  have hsub : (Finset.univ.filter fun l : Fin d → Fin (k + 1) =>
      ¬Disjoint (Finset.univ.filter fun i => x i ∈ gridPatch d k j)
        (Finset.univ.filter fun i => x i ∈ gridPatch d k l)) ⊆ gridTensorNeighbors d k j := by
    intro l hl
    obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hl).2
    exact gridPatch_common_point_neighbors d k j l (x i) (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hi').2
  exact (Finset.card_le_card hsub).trans (gridTensorNeighbors_card d k j)

end NearlyMinimax
