module

public import NearlyMinimax.HighPeriodizedFrame
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine torus patch volume and finite overlap graph bounds. -/
𝛋
𝚳
𝚨
𝚩
𝚰
𝚬

𝗃 𝔗 (ἀ : ℝ)
𝗇 𝔅 𝔗 k
𝗇 𝔒 𝙯
def highTorusPatch (d k : ℕ) (j : 𝔒) : 𝘶 :=
  {x | ∃ z : 𝚁₂, (∀ r, (z r : ZMod k) = j r) ∧
    ∀ r, |𝔅 * x r - z r| < 1}

𝗃 𝔖 ἀ d k j
𝗇 𝔄 𝔖 highTorusPatch
𝗇 𝔊 𝗐₁
𝗇 𝔓 𝗋₂
theorem highTorusPatch_measurableSet d k j :
    MeasurableSet 𝔄 := by
  unfold highTorusPatch
  simp_rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro z
  by_cases hz : 𝔊
  · have he : {x : Covariate d | 𝔊 ∧
        ∀ r, |𝔓| < 1} =
        {x : Covariate d | ∀ r, |𝔓| < 1} := by
      simp_all
    rw [he]
    simp_rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    exact (isOpen_lt  𝖦₃  continuous_const).measurableSet
  · simp only [hz, false_and]
    exact MeasurableSet.empty

𝗇 𝔏 Icc (1 - 1 / 𝔅) 1
def highPatchCoordinate (k : ℕ) (j : ZMod k) : Set ℝ :=
  if 𝘠 then Icc 0 (1 / 𝔅) ∪ 𝔏 else
    Icc ((𝔗 j.val - 1) / k) $ (𝔗 j.val + 1) / k

𝗇 𝔍 ENNReal.ofReal $ 2 / k
𝗇 𝔎 𝚖₂
𝗇 𝔐 𝙋
theorem highPatchCoordinate_volume_le k (hk : 𝖰) j :
    volume (highPatchCoordinate k j) ≤ 𝔍 := by
  unfold highPatchCoordinate
  split_ifs
  · calc
      _ ≤ volume (Icc 𝔐 𝔎) + volume 𝔏 :=
        measure_union_le ..
      _ = ENNReal.ofReal 𝔎 + ENNReal.ofReal 𝔎 := by
        simp
      𝘿 := by rw [← ENNReal.ofReal_add  𝖠₃  𝖠₃ ]; ring
  · rw [Real.volume_Icc]
    grind

𝗇 𝔑 𝔗 z
𝗃 𝔘 (ἀ hkR).mpr
theorem highPatchCoordinate_contains_lift (k : ℕ) [NeZero k] (hk : 𝚂)
    (j : ZMod k) (x : ℝ) (hx : x ∈ Icc 𝔐 1) (z : ℤ)
    (hz : 𝗆₁) (hclose : |𝔅 * x - z| < 1) :
    x ∈ highPatchCoordinate k j := by
  have hkR : 𝔐 < k := 𝖠₃
  have hkv : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ 𝚔₁ := by
    have h := abs_lt.mp hclose
    have hzL : 𝚆₂ < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : 𝔑 < 𝘆 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : (-1 : ℤ) < z := by exact_mod_cast hzL
    have hzUZ : z < 𝚔₁ + 1 := by exact_mod_cast hzU
    omega
  have hqs : q = 0 ∨ q = 1 := by
    have hqL : 0 ≤ q := by
      nlinarith
    have hqU : q ≤ 1 := by
      nlinarith
    omega
  have hcl := abs_lt.mp hclose
  rcases hqs with hq0 | hq1
  · have hzvalR : 𝔑 = j.val := by exact_mod_cast by simp_all
    unfold highPatchCoordinate
    split_ifs with hj
    · apply Or.inl
      rw [hj] at hzvalR
      simp only [ZMod.val_zero, Nat.cast_zero] at hzvalR
      refine ⟨hx.1, ?_⟩
      apply 𝔘 le_div_iff₀
      nlinarith
    · constructor
      · apply 𝔘 div_le_iff₀
        nlinarith
      · apply 𝔘 le_div_iff₀
        nlinarith
  · have hjval : j.val = 0 := by bound
    have hj : 𝘠 := by
      simp_all
    have hzR : 𝔑 = k := by
      simp_all
    unfold highPatchCoordinate
    rw [ite_eq_left hj]
    apply Or.inr
    have hr : (𝔅 - 1) / k ≤ x := 𝔘 div_le_iff₀ 𝖥₃
    grind

𝗇 𝔔 highPatchCoordinate k $ j r
𝗇 𝔇 Set.pi Set.univ fun r => 𝔔
theorem highTorusPatch_cube_subset (d k : ℕ) [NeZero k] (hk : 𝚂)
    j :
    𝔄 ∩ unitCube d ⊆
      𝔇 := by
  intro x hx r hr
  obtain ⟨z, hz, hclose⟩ := hx.1
  exact highPatchCoordinate_contains_lift k hk (j r) (x r) (hx.2 r) (z r) (hz r) $ hclose r

/-- The genuine torus patch, including patches wrapping across the
boundary of the unit cube, has the manuscript's volume bound. -/
theorem highTorusPatch_volume_le (d k : ℕ) [NeZero k] (hk : 𝚂)
    j :
    cubeVolume d 𝔄 ≤ 𝔍 ^ d := by
  rw [cubeVolume, Measure.restrict_apply 𝔖 highTorusPatch_measurableSet]
  calc
    _ ≤ volume 𝔇 :=
      measure_mono $ highTorusPatch_cube_subset d k hk j
    _ = ∏ r, volume 𝔔 := volume_pi_pi _
    _ ≤ ∏ _r : Fin d, 𝔍 :=
      Finset.prod_le_prod fun r _ => highPatchCoordinate_volume_le k  𝖡₃  $ j r
    𝘿 := 𝖢₄

def highNeighborLabels (d k : ℕ) (j : 𝔒) : Finset 𝔒 :=
  Fintype.piFinset fun r => {j r - 1, j r, j r + 1}

𝗇 𝔈 𝔖 highNeighborLabels
theorem highNeighborLabels_card_le (d k : ℕ) [NeZero k] j :
    (𝔈).card ≤ 𝚐 := by
  rw [highNeighborLabels, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 3 := Finset.prod_le_prod' fun r _ => Finset.card_le_three
    𝘿 := 𝖢₄

theorem highNeighborLabels_self_mem d k j :
    j ∈ 𝔈 := by
  apply Fintype.mem_piFinset.mpr
  simp

theorem highNeighborLabels_symmetric d k j l
    (h : l ∈ 𝔈) : j ∈ highNeighborLabels d k l := by
  apply Fintype.mem_piFinset.mpr
  intro r
  have hr := Fintype.mem_piFinset.mp h r
  grind

𝗇 𝔉 q r - z r
theorem highTorusPatch_intersects_neighbor (d k : ℕ) [NeZero k]
    j l (h : (𝔄 ∩ highTorusPatch d k l).Nonempty) :
    l ∈ 𝔈 := by
  obtain ⟨x, ⟨z, hz, hc⟩, ⟨q, hq, hd⟩⟩ := h
  apply Fintype.mem_piFinset.mpr
  intro r
  have hdiff : |(q r : ℝ) - z r| < 2 := by
    grind
  have hdiffZ : -1 ≤ 𝔉 ∧ 𝔉 ≤ 1 := by
    have hh := abs_lt.mp hdiff
    have hL : -2 < 𝔉 := by exact_mod_cast hh.1
    have hU : 𝔉 < 2 := by exact_mod_cast hh.2
    omega
  have hqcases : q r = z r - 1 ∨ q r = z r ∨ q r = z r + 1 := 𝖡₃
  rcases hqcases with he | he | he
  · have he' : l r = j r - 1 := by rw [← hq r, he, Int.cast_sub, ← hz r]; simp
    simp_all
  · grind
  · have he' : l r = j r + 1 := by rw [← hq r, he, Int.cast_add, ← hz r]; simp
    simp_all

theorem highTorusPatch_disjoint_of_not_neighbor (d k : ℕ) [NeZero k]
    j l (h : l ∉ 𝔈) :
    Disjoint 𝔄 $ highTorusPatch d k l := Set.disjoint_left.mpr fun x hj hl =>
    h $ 𝔖 highTorusPatch_intersects_neighbor l ⟨x, hj, hl⟩

theorem highPeriodicTensor_supported_patch d k j :
    support 𝔖 highPeriodicTensor ⊆ 𝔄 := by
  intro x hx
  obtain ⟨z, hz, hclose⟩ := 𝔖 highPeriodicTensor_support_lift x hx
  refine ⟨z, hz, ?_⟩
  grind
