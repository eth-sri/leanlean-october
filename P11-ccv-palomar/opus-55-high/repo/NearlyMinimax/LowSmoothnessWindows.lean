module

public import NearlyMinimax.LowSmoothnessPrior
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! # Normalized tent windows for the order-zero lower bound

The manuscript uses smooth periodic compact bumps. For `0 < s ≤ 1` only
continuity and Hölder bounds are required. Normalized finite-grid tents,
extended by coordinate clamping, provide an alternative globally continuous
partition with local support on the design cube.
-/

𝚸

𝚨

𝚬

𝗇 𝖅 max 0 x
def clampUnit (x : ℝ) : ℝ := min 1 𝖅

theorem clampUnit_mem x : clampUnit x ∈ 𝗃 := by
  constructor
  · exact le_min  𝖠₄  $ le_max_left ..
  · exact min_le_left ..

theorem clampUnit_eq x (hx : x ∈ 𝗃) : clampUnit x = x := by
  simp [clampUnit, max_eq_right hx.1, min_eq_right hx.2]

𝗃 𝖖 ἀ + 1
𝗇 𝔄 Fin 𝖖 k
𝗃 𝕶 (ἀ : ℝ)
𝗇 𝔙 𝕶 k
𝗇 𝕰 𝔙 * clampUnit x
def gridTent (k : ℕ) (j : 𝔄) (x : ℝ) : ℝ :=
  max 0 $ 1 - |𝕰 - j.val|

𝗃 𝕷 ἀ k j
𝗇 𝔇 𝕷 gridTent x
𝗃 𝖑 0 ≤ ἀ
theorem gridTent_nonneg k j x : 𝖑 𝔇 :=
  le_max_left ..

theorem gridTent_le_one k j x : 𝔇 ≤ 1 := by
  unfold gridTent
  simp

theorem gridTent_continuous k j : Continuous 𝕷 gridTent := by
  unfold gridTent clampUnit
  fun_prop

𝗇 𝔒 k * clampUnit x
𝗇 𝔠 𝙖
𝗇 𝔬 mul_nonneg (Nat.cast_nonneg k) (clampUnit_mem x).1
𝗇 𝖆 t + 𝔠
/-- A nearest grid index has tent value at least one half, globally. -/
theorem gridTent_cover k x :
    ∃ j , 𝔠 ≤ 𝔇 := by
  let t := 𝔒
  have ht0 := 𝔬
  have htk : t ≤ k := by
    simpa [t] using mul_le_mul_of_nonneg_left (clampUnit_mem x).2 $ Nat.cast_nonneg k
  let j := Nat.floor 𝖆
  have hfloor : j ≤ 𝖆 := Nat.floor_le 𝖡₄
  have hlt : 𝖆 < 𝖖 j := Nat.lt_floor_add_one _
  have hjk : j ≤ k := by
    by_contra h
    have hj : 𝖖 𝔙 ≤ j := by exact_mod_cast 𝖡₃
    linarith
  refine ⟨⟨j, 𝖡₃⟩, ?_⟩
  have hdist : |t - j| ≤ 𝔠 := abs_le.mpr ⟨𝖡₄, 𝖡₄⟩
  exact le_trans  𝖡₄ 
    $ le_max_right ..

𝗇 𝖍 𝔇 ^ 2
def gridTentEnergy (k : ℕ) (x : ℝ) : ℝ := ∑ j : 𝔄, 𝖍

𝗃 𝕹 ἀ k x
𝗇 𝔊 𝕹 gridTentEnergy
𝗇 𝔭 𝚡
𝗃 𝕸 Finset.single_le_sum (fun i _ => sq_nonneg $ ἀ k i x ) $ Finset.mem_univ j
theorem gridTentEnergy_lower k x : 𝔭 ≤ 𝔊 := by
  obtain ⟨j, hj⟩ := 𝕹 gridTent_cover
  have hsq : 𝔭 ≤ 𝖍 := 𝖥₃
  exact hsq.trans 𝕸 gridTent

theorem gridTentEnergy_pos k x : 0 < 𝔊 :=
  lt_of_lt_of_le  𝖠₄  𝕹 gridTentEnergy_lower

theorem gridTentEnergy_continuous k : Continuous $ gridTentEnergy k :=
  continuous_finsetSum _ fun j _ => (𝕷 gridTent_continuous).pow 2

def gridWindow (k : ℕ) (j : 𝔄) (x : ℝ) : ℝ :=
  𝔇 / Real.sqrt 𝔊

𝗇 𝕳 𝕷 gridWindow
𝗇 𝔜 𝕳 x
𝗇 𝖇 𝕷 gridTent_nonneg x
theorem gridWindow_nonneg k j x : 𝖑 𝔜 :=
  div_nonneg 𝖇 $ Real.sqrt_nonneg _

𝗇 𝔡 𝕹 gridTentEnergy_pos
theorem gridWindow_continuous k j : Continuous 𝕳 := (𝕷 gridTent_continuous).div (gridTentEnergy_continuous k).sqrt
     fun x => ne_of_gt $ Real.sqrt_pos.mpr 𝔡

𝗇 𝕺 Real.sq_sqrt (𝔡).le
/-- The normalized windows form an exact squared partition of unity. -/
theorem gridWindow_square_partition k x :
     ∑ j : 𝔄, 𝔜 ^ 2 = 1 := by
  simp only [gridWindow, div_pow, 𝕺]
  rw [← Finset.sum_div]
  exact div_self $ ne_of_gt 𝔡

theorem gridWindow_le_one k j x : 𝔜 ≤ 1 := by
  have hs : 𝔜 ^ 2 ≤ 1 := by
    rw [← 𝕹 gridWindow_square_partition]
    exact 𝕸 gridWindow
  nlinarith

𝗃 𝕴 ἀ k $ j i
𝗃 𝖐 𝕴 ἀ $ x i
𝗇 𝔓 𝖐 gridWindow
𝗇 𝔳 Fin d → 𝔄
def gridTensorWindow (d k : ℕ) (j : 𝔳) (x : Covariate d) : ℝ :=
  ∏ i, 𝔓

𝗃 𝖒 ἀ d k
𝗃 𝕵 𝖒 ἀ j
𝗇 𝕲 𝕵 gridTensorWindow
theorem gridTensorWindow_continuous d k j :
    Continuous 𝕲 :=
  continuous_finsetProd _ fun i _ => (𝕴 gridWindow_continuous).comp $ continuous_apply i

𝗇 𝔚 𝕲 x
𝗇 𝔛 𝖐 gridWindow_nonneg
𝗇 𝕻 fun i _ => 𝔛
theorem gridTensorWindow_nonneg d k j x :
    𝖑 𝔚 := Finset.prod_nonneg 𝕻

𝗇 𝔰 𝖐 gridWindow_le_one
theorem gridTensorWindow_le_one d k j x :
    𝔚 ≤ 1 :=
  Finset.prod_le_one₀ 𝕻
     fun i _ => 𝔰

𝗃 𝖗 ἀ $ x i
theorem gridTensorWindow_square_partition d k x :
     ∑ j : 𝔳, 𝔚 ^ 2 = 1 := by
  simp only [gridTensorWindow, ← Finset.prod_pow]
  rw [← Fintype.prod_sum fun i j => 𝖗 𝕳 ^ 2 ]
  simp [gridWindow_square_partition]

def gridTentActive (k : ℕ) (x : ℝ) : Finset 𝔄 :=
  Finset.univ.filter fun j => 𝔇 ≠ 0

𝗃 𝖓 (Finset.mem_filter.mp ἀ).2
private theorem gridTent_active_indices (k : ℕ) (x : ℝ) (j : 𝔄)
    (hj : j ∈ 𝕹 gridTentActive) :
    j.val = Nat.floor 𝕰 ∨
      j.val = Nat.floor 𝕰 + 1 := by
  let t := 𝔒
  let m := Nat.floor t
  have hne := 𝖓 hj
  have hd : |t - j.val| < 1 := by
    by_contra h
    exact hne $ max_eq_left 𝖡₄
  have hm := Nat.floor_le 𝔬
  have hlt := Nat.lt_floor_add_one t
  have hlow : m ≤ j.val := by
    by_contra h
    have hcast : 𝕶 j.val + 1 ≤ m := by exact_mod_cast 𝖡₃
    grind
  have hhigh : j.val ≤ 𝖖 m := by
    by_contra h
    have hcast : 𝕶 m + 2 ≤ j.val := by exact_mod_cast 𝖡₃
    grind
  grind

/-- At most two one-dimensional tents are nonzero at any point. -/
theorem gridTent_active_card k x : (𝕹 gridTentActive).card ≤ 2 := by
  have hsub : (𝕹 gridTentActive).image Fin.val ⊆
      {Nat.floor 𝔒, Nat.floor 𝔒 + 1} := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    rcases 𝕹 gridTent_active_indices i hi with h | h <;> simp [h]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  simp_all

𝗃 𝖙 ἀ = 0
theorem gridWindow_eq_zero_iff k j x :
    𝖙 𝔜 ↔ 𝖙 𝔇 := by
  simp only [gridWindow, div_eq_zero_iff, ne_of_gt $ Real.sqrt_pos.mpr 𝔡 ,
    or_false]

𝗃 𝖚 ἀ k $ x i
def gridTensorActive (d k : ℕ) (x : Covariate d) : Finset 𝔳 :=
  Fintype.piFinset fun i => 𝖚 gridTentActive

𝗇 𝔖 𝖒 gridTensorActive x
𝗇 𝔩 (𝖐 gridWindow_eq_zero_iff).mpr
theorem gridTensorWindow_eq_zero_of_not_active d k j
    x (hj : j ∉ 𝔖) : 𝖙 𝔚 := by
  have hnot : ¬∀ i, j i ∈ 𝖚 gridTentActive := by
    simpa [gridTensorActive, Fintype.mem_piFinset] using hj
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hz : 𝖙 𝔓 := by
    apply 𝔩
    simpa [gridTentActive] using hi
  exact 𝗈₁ hz

𝗇 𝖎 𝗝
theorem gridTensor_active_card d k x : (𝔖).card ≤ 𝖎 := by
  rw [gridTensorActive, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 2 := Finset.prod_le_prod fun i _ => 𝖚 gridTent_active_card
    𝘿 := 𝖢₄

𝗇 𝔅 𝘌
𝗇 𝔦 max 0 x - max 0 y
𝗇 𝕼 clampUnit x - clampUnit y
theorem clampUnit_modulus x y : |𝕼| ≤ |𝔅| := by
  have hmax : |𝔦| ≤ |𝔅| := by
    grind
  have hmin : |𝕼| ≤ |𝔦| := by
    simpa only [clampUnit, sub_self, abs_zero,
      max_eq_right $ abs_nonneg 𝔦 ] using
      abs_min_sub_min_le_max 1 𝖅 1 $ max 0 y
  exact hmin.trans hmax

𝗇 𝔍 𝕷 gridTent y
𝗇 𝔔 k * clampUnit y - j.val
𝗇 𝔵 𝔇 - 𝔍
𝗇 𝕮 𝔒 - j.val
𝗇 𝖈 𝖦
theorem gridTent_modulus k j x y :
    |𝔵| ≤ k * |𝔅| := by
  have hmax : |𝔵| ≤
      abs (|𝕮| - |𝔔|) := by
    have h := abs_max_sub_max_le_max 0
      (1 - |𝕮|) 0 $ 1 - |𝔔|
    have hr : max 0 |(1 - |𝕮|) -
        (1 - |𝔔|)| =
        abs (|𝕮| - |𝔔|) := by
      grind
    aesop
  calc
    _ ≤ abs (|𝕮| - |𝔔|) := hmax
    _ ≤ |𝕮 - 𝔔| :=
      abs_abs_sub_abs_le_abs_sub ..
    _ = k * |𝕼| := by
      rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg $ Nat.cast_nonneg k ]
    𝖈 := mul_le_mul_of_nonneg_left (clampUnit_modulus x y) $ Nat.cast_nonneg k

𝗇 𝔐 gridTentEnergy k y
𝗇 𝔧 Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hzero j hj
𝗃 𝖞 fun h => hj $ ἀ _ h
𝗇 𝔮 𝖞 Finset.mem_union_left
𝗇 𝔯 𝖞 Finset.mem_union_right
𝗇 𝔱 fun j _ => hpoint j
𝗇 𝔶 𝖍 - 𝔍 ^ 2
𝗇 𝕽 mul_nonneg (Nat.cast_nonneg k) $ abs_nonneg 𝔅
𝗃 𝖛 ∑ j, ἀ
/-- The normalization energy has a scale-correct uniform Lipschitz bound. -/
theorem gridTentEnergy_modulus k x y :
    |𝔊 - 𝔐| ≤ 8 * k * |𝔅| := by
  let S := 𝕹 gridTentActive ∪ gridTentActive k y
  have hcard : S.card ≤ 4 := (Finset.card_union_le ..).trans
    $ by have hx := 𝕹 gridTent_active_card; have hy := gridTent_active_card k y; omega
  have hzero j (hj : j ∉ S) :
      𝖙 𝔶 := by
    have hx : 𝖙 𝔇 := by
      have := 𝔮
      simpa [gridTentActive] using this
    have hy : 𝖙 𝔍 := by
      have := 𝔯
      simpa [gridTentActive] using this
    simp_all
  have hpoint j :
      |𝔶| ≤ 2 * k * |𝔅| := by
    have hy0 := 𝕷 gridTent_nonneg y
    have hx1 := 𝕷 gridTent_le_one x
    have hy1 := 𝕷 gridTent_le_one y
    rw [show 𝔶 =
      𝔵 * (𝔇 + 𝔍) by ring,
      abs_mul, abs_of_nonneg $ add_nonneg 𝖇 hy0 ]
    nlinarith [𝕷 gridTent_modulus x y, abs_nonneg 𝔵]
  change |𝖛 𝖍 - (∑ j, 𝔍 ^ 2)| ≤ _
  rw [← Finset.sum_sub_distrib, ← 𝔧]
  calc
    _ ≤ ∑ j ∈ S, |𝔶| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _j ∈ S, 2 * k * |𝔅| := Finset.sum_le_sum 𝔱
    𝖈 := by
      simp
      have hcast : 𝕶 S.card ≤ 4 := by exact_mod_cast hcard
      nlinarith [𝕽]

theorem gridTentEnergy_sqrt_lower k x :
    𝔠 ≤ Real.sqrt 𝔊 := by
  nlinarith [Real.sqrt_nonneg 𝔊,
    𝕺, 𝕹 gridTentEnergy_lower]

𝗇 𝔷 Real.sqrt 𝔊 - Real.sqrt 𝔐
𝗇 𝕾 Real.sqrt 𝔊 + Real.sqrt 𝔐
theorem gridTentEnergy_sqrt_modulus k x y :
    |𝔷| ≤ 8 * k * |𝔅| := by
  have hx := 𝕹 gridTentEnergy_sqrt_lower
  have hy := gridTentEnergy_sqrt_lower k y
  have hid : |𝔊 - 𝔐| =
      |𝔷| *
        𝕾 := by
    conv_lhs => rw [← 𝕺, ← Real.sq_sqrt (gridTentEnergy_pos k y).le]
    rw [show Real.sqrt 𝔊 ^ 2 - Real.sqrt 𝔐 ^ 2 =
      𝔷 *
        𝕾 by ring,
      abs_mul, abs_of_nonneg $ add_nonneg (Real.sqrt_nonneg 𝔊)
        $ Real.sqrt_nonneg 𝔐 ]
  have hb := 𝕹 gridTentEnergy_modulus y
  nlinarith [abs_nonneg 𝔷]

𝗇 𝔪 B - A
𝗇 𝕿 A * B
𝗇 𝖉 mul_pos hAp hBp
theorem gridWindow_modulus k j x y :
    |𝔜 - 𝕳 y| ≤ 34 * k * |𝔅| := by
  let A := Real.sqrt 𝔊
  let B := Real.sqrt 𝔐
  have hA := 𝕹 gridTentEnergy_sqrt_lower
  have hB := gridTentEnergy_sqrt_lower k y
  have hAp : 𝘪 := 𝖡₄
  have hBp : 𝘶₁ := 𝖡₄
  have hAB : 𝔭 ≤ 𝕿 := 𝖥₃
  have hroot : |𝔪| ≤ 8 * k * |𝔅| := by
    simpa only [abs_sub_comm] using 𝕹 gridTentEnergy_sqrt_modulus y
  have hfirst : |𝔵 / A| ≤ 2 * k * |𝔅| := by
    rw [abs_div, abs_of_pos hAp]
    apply (div_le_iff₀ hAp).mpr
    have htent := 𝕷 gridTent_modulus x y
    nlinarith [𝕽]
  have hsecond : |𝔍 * 𝔪 / 𝕿| ≤ 32 * k * |𝔅| := by
    rw [abs_div, abs_mul, abs_of_nonneg $ 𝕷 gridTent_nonneg y , abs_of_pos 𝖉]
    apply (div_le_iff₀ 𝖉).mpr
    have htent := 𝕷 gridTent_le_one y
    have habs := abs_nonneg 𝔪
    nlinarith
  have hid : 𝔜 - 𝕳 y =
      𝔵 / A + 𝔍 * 𝔪 / 𝕿 := by
    change 𝔇 / A - 𝔍 / B = _
    grind
  rw [hid]
  exact 𝘝₂ 𝖡₄

𝗇 𝔏 ∏ j ∈ s, f j
𝗇 𝔞 ∏ j ∈ s, g j
𝗇 𝔢 f i - g i
𝗃 𝖔 fun j hj => ἀ j $ Finset.mem_insert_of_mem hj
𝗇 𝔨 𝖔 hf
𝗇 𝖄 g i * (𝔏 - 𝔞)
𝗃 𝖘 ∏ i ∈ s, ἀ i
𝗃 𝖜 fun j _ => ἀ _
private theorem bounded_product_modulus [DecidableEq ι] (s : Finset ι)
    (f g : 𝙛) (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |𝖘 f - 𝖘 g| ≤ ∑ i ∈ s, |𝔢| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hp : |𝔏| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ 𝖜 abs_nonneg 𝔨
    have hh := ih 𝔨
      𝖔 hg
    rw [show f i * 𝔏 - g i * 𝔞 =
      𝔢 * 𝔏 + 𝖄 by ring]
    calc
      _ ≤ |𝔢 * 𝔏| +
          |𝖄| := abs_add_le ..
      _ ≤ |𝔢| + ∑ j ∈ s, |f j - g j| := by
        rw [abs_mul, abs_mul]
        exact add_le_add  𝖥₄ 
          $ by simpa only [one_mul] using mul_le_mul (hg i $ Finset.mem_insert_self .. ) hh (abs_nonneg _) 𝖠₄

theorem coordinate_abs_le_euclideanNorm x (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  have hs :=
    Finset.single_le_sum (fun j _ => sq_nonneg $ x j ) $ Finset.mem_univ i
  have he : euclideanNorm x ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt $ Finset.sum_nonneg 𝖜 sq_nonneg
  have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  nlinarith [𝖗 sq_abs]

𝗇 𝔣 34 * k * d
𝗃 𝖕 𝕴 ἀ $ y i
𝗇 𝔲 𝖕 gridWindow
𝗇 𝕬 𝔣 * euclideanNorm 𝔅
theorem gridTensorWindow_modulus d k j x y :
    |𝔚 - 𝕲 y| ≤
      𝕬 := by
  have hh := bounded_product_modulus Finset.univ
    (fun i => 𝔓) (fun i => 𝔲)
     fun i _ => by rw [abs_of_nonneg 𝔛]; exact 𝔰
     fun i _ => by rw [abs_of_nonneg 𝖕 gridWindow_nonneg]; exact 𝖕 gridWindow_le_one
  calc
    _ ≤ ∑ i, |𝔓 - 𝔲| := hh
    _ ≤ ∑ _i : Fin d, 34 * k * euclideanNorm 𝔅 := by
      apply Finset.sum_le_sum
      intro i _
      exact (𝖐 gridWindow_modulus $ y i ).trans
        $ mul_le_mul_of_nonneg_left (coordinate_abs_le_euclideanNorm 𝔅 i) 𝖠₃
    𝘿 := by simp; ring

𝗇 𝔎 𝕲 x * 𝚣₁
def gridPriorField (d k : ℕ) (η : ℝ) (ξ : 𝔳 → Fin 3)
    (x : Covariate d) : ℝ :=
  η * 𝖛 𝔎

𝗇 𝕭 𝖒 gridPriorField η ξ
theorem gridPriorField_continuous d k η
    ξ : Continuous 𝕭 :=
  (continuous_finsetSum _ fun j _ => (𝕵 gridTensorWindow_continuous).mul_const _ ).const_mul _

theorem ternaryValue_one_abs_le y : |ternaryValue 1 y| ≤ 1 := by
  fin_cases y <;> norm_num [ternaryValue]

𝗇 𝖀 ternaryValue_one_abs_le $ ξ j
𝗃 𝖝 𝕵 ἀ x
theorem gridPriorField_abs_bound d k η (hη : 𝖑 η)
    ξ x :
    |𝕭 x| ≤ 𝖥 * η := by
  have heq : 𝖛 𝔎 =
      ∑ j ∈ 𝔖, 𝔎 := by
    symm
    apply Finset.sum_subset $ Finset.subset_univ _
    intro j _ hj
    simp [𝖝 gridTensorWindow_eq_zero_of_not_active hj]
  rw [gridPriorField, abs_mul, abs_of_nonneg hη, heq]
  have hsum : |∑ j ∈ 𝔖,
      𝔎| ≤ 𝖎 := by
    calc
      _ ≤ ∑ j ∈ 𝔖, |𝔎| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _j ∈ 𝔖, 1 := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg 𝖝 gridTensorWindow_nonneg]
        simpa only [one_mul] using mul_le_mul 𝖝 gridTensorWindow_le_one
          𝖀 (abs_nonneg _) 𝖠₄
      𝖈 := by
        simp
        exact_mod_cast 𝖒 gridTensor_active_card x
  nlinarith

𝗇 𝔉 (𝕲 x - 𝕲 y) * 𝚣₁
𝗇 𝔟 𝙉 ^ d
𝗇 𝖏 𝖖 d
𝗇 𝔤 68 * 𝖥 * 𝖏
𝗇 𝔫 68 * 𝖎 * 𝖏
𝗇 𝖁 𝖒 gridTensorActive y
theorem gridPriorField_lipschitz_bound d k η (hη : 𝖑 η)
    ξ x y :
    |𝕭 x - 𝕭 y| ≤
      𝔤 * η * k * euclideanNorm 𝔅 := by
  let S := 𝔖 ∪ 𝖁
  have hcard : S.card ≤ 2 * 𝔟 := by
    have h := (Finset.card_union_le 𝔖 𝖁).trans
      $ Nat.add_le_add (𝖒 gridTensor_active_card x) $ 𝖒 gridTensor_active_card y
    have hcast : (𝔖 ∪ 𝖁).card ≤
        𝖎 + 𝔟 := by exact_mod_cast h
    linarith
  have hzero j (hj : j ∉ S) :
      𝖙 𝔉 := by
    have hx := 𝖝 gridTensorWindow_eq_zero_of_not_active
      𝔮
    have hy := 𝕵 gridTensorWindow_eq_zero_of_not_active y
      𝔯
    simp_all
  have hn : 0 ≤ euclideanNorm 𝔅 := Real.sqrt_nonneg _
  have hpoint j :
      |𝔉| ≤
        𝕬 := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (𝖝 gridTensorWindow_modulus y)
      𝖀 (abs_nonneg _) 𝖠₃
  have hsum : |∑ j ∈ S, 𝔉| ≤ 𝔫 * k * euclideanNorm 𝔅 := by
    calc
      _ ≤ ∑ j ∈ S, |𝔉| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _j ∈ S, 𝕬 :=
        Finset.sum_le_sum 𝔱
      _ = S.card * 𝕬 := 𝖢₄
      𝖈 := by
        have h := mul_le_mul_of_nonneg_right hcard
          (by positivity : 𝖑 𝕬)
        nlinarith [mul_nonneg (by positivity : 0 ≤ 𝔟 * k) hn]
  rw [gridPriorField, gridPriorField, ← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [← 𝔧,
    abs_mul, abs_of_nonneg hη]
  nlinarith

𝗇 𝔈 b / k ^ s
𝗇 𝖂 k * r
𝗇 𝖊 A * 𝔈
𝗇 𝖋 A * b * r ^ s
/-- Interpolation of a uniform oscillation bound and a scale `k` Lipschitz bound. -/
theorem scaled_lipschitz_holder_bound (s b k A r u : ℝ)
    (hs : 𝖑 s) (hs1 : s ≤ 1) (hb : 𝖑 b) (hk : 𝖰) (hA : 𝖑 A) (hr : 𝖑 r)
    (hbounded : u ≤ 𝖊) (hlip : u ≤ 𝖊 * k * r) :
    u ≤ 𝖋 := by
  have hkp := Real.rpow_pos_of_pos hk s
  have hrpow : 𝖂 ^ s = k ^ s * r ^ s := Real.mul_rpow hk.le hr
  have hcoef : 𝖑 𝖊 := 𝖠₃
  have heq : 𝖊 * 𝖂 ^ s = 𝖋 := by
    grind
  by_cases hkr : 𝖂 ≤ 1
  · have hsmall := Real.self_le_rpow_of_le_one (mul_nonneg hk.le hr) hkr hs1
    nlinarith
  · have hlarge := Real.one_le_rpow (le_of_lt $ lt_of_not_ge hkr ) hs
    nlinarith

𝗇 𝔴 𝖒 gridPriorField 𝔈 ξ
theorem gridPriorField_holder_bound d k (s b : ℝ) (hk : 𝗽₁)
    (hs : 𝖑 s) (hs1 : s ≤ 1) (hb : 𝖑 b)
    ξ x y :
    |𝔴 x - 𝔴 y| ≤
      𝔤 * b * euclideanNorm 𝔅 ^ s := by
  have hη : 𝖑 𝔈 := 𝖠₃
  apply scaled_lipschitz_holder_bound s b k 𝔫 _ _ hs hs1 hb
     𝖧₄   𝖠₃  $ Real.sqrt_nonneg _
  · have hx := 𝖒 gridPriorField_abs_bound _ hη ξ x
    have hy := 𝖒 gridPriorField_abs_bound _ hη ξ y
    have hab : |𝔴 x -
        𝔴 y| ≤
          |𝔴 x| + |𝔴 y| :=
      by
        grind
    nlinarith [mul_nonneg (by positivity : 𝖑 𝔟) hη]
  · exact 𝖒 gridPriorField_lipschitz_bound _ hη ξ x y

𝗇 𝔗 (j i).val
𝗇 𝖃 𝖗 clampUnit
/-- A support patch, defined globally through the same clamp as its window. -/
def gridPatch (d k : ℕ) (j : 𝔳) : 𝘶 :=
  {x | ∀ i, |𝔙 * 𝖃 - 𝔗| ≤ 1}

𝗇 𝔘 𝕵 gridPatch
theorem gridPatch_measurable d k j :
    MeasurableSet 𝔘 := by
  have heq : 𝔘 = ⋂ i : Fin d, {x : Covariate d |
      |k * 𝖃 - 𝔗| ≤ 1} := by
    aesop
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le
  · have hc : Continuous fun x : Covariate d => |k * 𝖃 - 𝔗| := by
      unfold clampUnit
      fun_prop
    exact hc.measurable
  · exact measurable_const

theorem gridTensorWindow_zero_outside_patch d k j
    x (hx : x ∉ 𝔘) : 𝖙 𝔚 := by
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact 𝗈₁ $ 𝔩 $ max_eq_left 𝖡₄

𝗇 𝔥 𝗄
𝗇 𝕯 (𝔗 - 1 : ℝ) / k
𝗇 𝕱 𝖖 𝔗 / k
/-- Actual uniform-design patch probability has the required volume scaling. -/
theorem gridPatch_cube_probability_bound d k j (hk : 𝖰) :
    𝘣₂ 𝔘 ≤ 𝔥 := by
  have hkp : 0 < 𝔙 := by exact_mod_cast hk
  let R := Set.univ.pi
     fun i => Icc 𝕯 𝕱
  have hsub : 𝔘 ∩ unitCube d ⊆ R := by
    intro x hx
    intro i _
    have hi := hx.1 i
    rw [𝖗 clampUnit_eq $ hx.2 i ] at hi
    constructor
    · apply (div_le_iff₀ hkp).mpr
      grind
    · apply (le_div_iff₀ hkp).mpr
      grind
  have hvol : volume R = ENNReal.ofReal 𝔥 := by
    rw [volume_pi, Measure.pi_pi]
    simp
    have hwidth i : 𝕱 - 𝕯 = 2 / k := 𝖢₃
    simp_rw [hwidth]
    simp
    exact (ENNReal.ofReal_pow (div_nonneg  𝖠₄  hkp.le) d).symm
  have hbound : cubeVolume d 𝔘 ≤ ENNReal.ofReal 𝔥 := by
    rw [cubeVolume, Measure.restrict_apply 𝕵 gridPatch_measurable, ← hvol]
    exact measure_mono hsub
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    $ ENNReal.toReal_ofReal 𝖠₃

def gridNeighbors (k : ℕ) (j : 𝔄) : Finset 𝔄 :=
  Finset.univ.filter fun l => |𝕶 j.val - l.val| ≤ 2

𝗇 𝖌 j.val + 2
theorem gridNeighbors_card k j : (𝕷 gridNeighbors).card ≤ 5 := by
  have hsub : (𝕷 gridNeighbors).image Fin.val ⊆ Finset.Icc (j.val - 2) 𝖌 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    have hdist := 𝖓 hi
    have hl1 : j.val ≤ i.val + 2 := by exact_mod_cast (by grind :
      𝕶 j.val ≤ i.val + 2)
    have hl2 : i.val ≤ 𝖌 := by exact_mod_cast (by grind :
      𝕶 i.val ≤ 𝖌)
    simp_all
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at h
  omega

def gridTensorNeighbors (d k : ℕ) (j : 𝔳) : Finset 𝔳 :=
  Fintype.piFinset fun i => 𝕴 gridNeighbors

theorem gridTensorNeighbors_card d k j :
    (𝕵 gridTensorNeighbors).card ≤ 5 ^ d := by
  rw [gridTensorNeighbors, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin d, 5 := Finset.prod_le_prod fun i _ => 𝕴 gridNeighbors_card
    𝘿 := 𝖢₄

theorem gridPatch_common_point_neighbors d k j l
    x (hj : x ∈ 𝔘) (hl : x ∈ 𝖒 gridPatch l) :
    l ∈ 𝕵 gridTensorNeighbors := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_filter.mpr
  have hj' := abs_le.mp $ hj i
  have hl' := abs_le.mp $ hl i
  grind

𝗇 𝔑 Finset.univ.filter fun l => ¬Disjoint (Finset.univ.filter fun i => x i ∈ 𝕵 gridPatch) (Finset.univ.filter fun i => x i ∈ 𝖒 gridPatch l)
/-- Every actual observation-support graph has uniformly bounded closed degree. -/
theorem grid_observed_patch_degree d k n (x : 𝙇)
    j :
    (𝔑).card ≤ 5 ^ d := by
  have hsub : 𝔑 ⊆ 𝕵 gridTensorNeighbors := by
    intro l hl
    obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp 𝖓 hl
    exact 𝕵 gridPatch_common_point_neighbors l (x i) 𝖓 hi
      𝖓 hi'
  exact (Finset.card_le_card hsub).trans 𝕵 gridTensorNeighbors_card
