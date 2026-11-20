module

public import NearlyMinimax.HighPeriodizedFrame

@[expose] public section

/-! Genuine torus patch volume and finite overlap graph bounds. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

variable {d k : ℕ} (j : HighWindowLabels d k)

def highTorusPatch : Set (Covariate d) :=
  {x | ∃ z : Fin d → ℤ, (∀ r, (z r) = j r) ∧
    ∀ r, |k * x r - z r| < 1}

theorem highTorusPatch_measurableSet (d k : ℕ) (j : HighWindowLabels d k) :
    MeasurableSet (highTorusPatch j) := by
  unfold highTorusPatch
  measurability

def highPatchCoordinate (j : ZMod k) : Set ℝ :=
  if j = 0 then Icc 0 (1 / k) ∪ Icc (1 - 1 / k) 1 else
    Icc ((j.val - 1) / k) ((j.val + 1) / k)

theorem highPatchCoordinate_volume_le (hk : 0 < k) (j : ZMod k) :
    volume (highPatchCoordinate j) ≤ ENNReal.ofReal (2 / k) := by
  unfold highPatchCoordinate
  split_ifs
  · calc
      _ ≤ _ :=
        measure_union_le _ _
      _ = ENNReal.ofReal (1 / k) + ENNReal.ofReal (1 / k) := by
        simp
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_rfl

theorem highPatchCoordinate_contains_lift [NeZero k] (hk : 2 ≤ k)
    {j : ZMod k} {x : ℝ} (hx : x ∈ Icc 0 1) {z : ℤ}
    (hz : z = j) (hclose : |k * x - z| < 1) :
    x ∈ highPatchCoordinate j := by
  have hkR : (0 : ℝ) < k := by positivity
  have hkv : j.val < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ k := by
    have h := abs_lt.mp hclose
    have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : (z : ℝ) < k + 1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : (-1) < z := by exact_mod_cast hzL
    have hzUZ : z < k + 1 := by exact_mod_cast hzU
    omega
  have hqs : q = 0 ∨ q = 1 := by
    have hqL : 0 ≤ q := by
      by_contra h
      nlinarith
    have hqU : q ≤ 1 := by
      by_contra h
      nlinarith
    omega
  have hcl := abs_lt.mp hclose
  rcases hqs with hq0 | hq1
  · have hzvalR : (z : ℝ) = j.val := by exact_mod_cast (by simp_all)
    unfold highPatchCoordinate
    split_ifs with hj
    · apply Or.inl
      rw [hj] at hzvalR
      simp only [ZMod.val_zero, Nat.cast_zero] at hzvalR
      refine ⟨hx.1, ?_⟩
      apply (le_div_iff₀ hkR).mpr
      nlinarith
    · constructor
      · apply (div_le_iff₀ hkR).mpr
        nlinarith
      · apply (le_div_iff₀ hkR).mpr
        nlinarith
  · have hjval : j.val = 0 := by rw [hq1, mul_one] at hq; omega
    have hj : j = 0 := by
      simp_all
    have hzR : (z : ℝ) = k := by
      simp_all
    unfold highPatchCoordinate
    rw [ite_eq_left hj]
    apply Or.inr
    refine ⟨?_, hx.2⟩
    have hr : (k - 1) / k ≤ x := (div_le_iff₀ hkR).mpr (by nlinarith)
    convert hr using 1
    field_simp

/-- The genuine torus patch, including patches wrapping across the
boundary of the unit cube, has the manuscript's volume bound. -/
theorem highTorusPatch_volume_le [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) :
    cubeVolume d (highTorusPatch j) ≤ ENNReal.ofReal (2 / k) ^ d := by
  rw [cubeVolume, Measure.restrict_apply (highTorusPatch_measurableSet ..)]
  calc
    _ ≤ _ :=
      measure_mono (by intro x hx r hr; obtain ⟨z, hz, hclose⟩ := hx.1; exact highPatchCoordinate_contains_lift hk (hx.2 r) (hz r) (hclose r))
    _ = _ := volume_pi_pi _
    _ ≤ _ :=
      Finset.prod_le_prod (fun r _ => highPatchCoordinate_volume_le (by omega) (j r))
    _ = _ := by simp

def highNeighborLabels : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {j r - 1, j r, j r + 1})

/-- Neighbor relation on the periodic grid. -/
abbrev windowDepends (d k : ℕ) (i j : HighWindowLabels d k) := j ∈ highNeighborLabels i

theorem highNeighborLabels_card_le [NeZero k] (j : HighWindowLabels d k) :
    (highNeighborLabels j).card ≤ 3 ^ d := by
  rw [highNeighborLabels, Fintype.card_piFinset]
  calc
    _ ≤ _ := Finset.prod_le_prod' (fun r _ => Finset.card_le_three)
    _ = _ := by simp

theorem highNeighborLabels_self_mem (d k : ℕ) (j : HighWindowLabels d k) :
    j ∈ highNeighborLabels j := by
  apply Fintype.mem_piFinset.mpr
  intro r
  simp

theorem highNeighborLabels_symmetric {j l : HighWindowLabels d k}
    (h : l ∈ highNeighborLabels j) : j ∈ highNeighborLabels l := by
  apply Fintype.mem_piFinset.mpr
  intro r
  have hr := Fintype.mem_piFinset.mp h r
  aesop

instance (d k : ℕ) : Std.Refl (windowDepends d k) := ⟨highNeighborLabels_self_mem d k⟩
instance (d k : ℕ) : Std.Symm (windowDepends d k) := ⟨fun _ _ => highNeighborLabels_symmetric⟩

theorem highTorusPatch_intersects_neighbor [NeZero k]
    (j l : HighWindowLabels d k) (h : (highTorusPatch j ∩ highTorusPatch l).Nonempty) :
    l ∈ highNeighborLabels j := by
  obtain ⟨x, ⟨z, hz, hc⟩, ⟨q, hq, hd⟩⟩ := h
  apply Fintype.mem_piFinset.mpr
  intro r
  have hdiff : |(q r : ℝ) - z r| < 2 := by
    grind
  have hdiffZ : -1 ≤ q r - z r ∧ q r - z r ≤ 1 := by
    have hh := abs_lt.mp hdiff
    have hL : (-2) < q r - z r := by exact_mod_cast hh.1
    have hU : q r - z r < 2 := by exact_mod_cast hh.2
    omega
  have hqcases : q r = z r - 1 ∨ q r = z r ∨ q r = z r + 1 := by omega
  rcases hqcases with he | he | he
  · have he' : l r = j r - 1 := by rw [← hq r, he, Int.cast_sub, ← hz r]; simp
    simp [he']
  · grind
  · have he' : l r = j r + 1 := by rw [← hq r, he, Int.cast_add, ← hz r]; simp
    simp [he']

theorem highTorusPatch_disjoint_of_not_neighbor [NeZero k]
    {j l : HighWindowLabels d k} (h : l ∉ highNeighborLabels j) :
    Disjoint (highTorusPatch j) (highTorusPatch l) := Set.disjoint_left.mpr (fun x hj hl =>
    h (highTorusPatch_intersects_neighbor j l ⟨x, hj, hl⟩))

theorem highPeriodicTensor_supported_patch :
    support (highPeriodicTensor j) ⊆ highTorusPatch j := by
  intro x hx
  obtain ⟨z, hz, hclose⟩ := highPeriodicTensor_support_lift hx
  refine ⟨z, hz, ?_⟩
  intro r
  exact (hclose r).trans (by norm_num)

end NearlyMinimax
