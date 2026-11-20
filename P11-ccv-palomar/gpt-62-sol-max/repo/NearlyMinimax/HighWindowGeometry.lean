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

def highTorusPatch (d k : ℕ) (j : HighWindowLabels d k) : Set (Covariate d) :=
  {x | ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
    ∀ r, |(k : ℝ) * x r - z r| < 1}

theorem highTorusPatch_measurableSet (d k : ℕ) (j : HighWindowLabels d k) :
    MeasurableSet (highTorusPatch d k j) := by
  unfold highTorusPatch
  simp_rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro z
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · have he : {x : Covariate d | (∀ r, (z r : ZMod k) = j r) ∧
        ∀ r, |(k : ℝ) * x r - z r| < 1} =
        {x : Covariate d | ∀ r, |(k : ℝ) * x r - z r| < 1} := by
      ext x
      exact and_iff_right hz
    rw [he]
    simp_rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  · simp only [hz, false_and, setOf_false]
    exact MeasurableSet.empty

def highPatchCoordinate (k : ℕ) (j : ZMod k) : Set ℝ :=
  if j = 0 then Icc 0 (1 / (k : ℝ)) ∪ Icc (1 - 1 / (k : ℝ)) 1 else
    Icc (((j.val : ℝ) - 1) / k) (((j.val : ℝ) + 1) / k)

section
variable (k : ℕ)

theorem highPatchCoordinate_volume_le (hk : 0 < k) (j : ZMod k) :
    volume (highPatchCoordinate k j) ≤ ENNReal.ofReal (2 / (k : ℝ)) := by
  unfold highPatchCoordinate
  split_ifs
  · calc
      _ ≤ volume (Icc (0 : ℝ) (1 / k)) + volume (Icc (1 - 1 / (k : ℝ)) 1) :=
        measure_union_le _ _
      _ = ENNReal.ofReal (1 / (k : ℝ)) + ENNReal.ofReal (1 / (k : ℝ)) := by
        rw [Real.volume_Icc, Real.volume_Icc] <;> simp
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)] <;> ring
  · rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_rfl

section
variable [NeZero k]
    (j : ZMod k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (z : ℤ)
include hx

theorem highPatch_lift_cube_cases
    (hz : (z : ZMod k) = j) (hclose : |(k : ℝ)*x-z| < 1) :
    z = (j.val : ℤ) ∨ (j = 0 ∧ z = (k : ℤ)) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have hkv : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ (k : ℤ) := by
    have hh := abs_lt.mp hclose
    have hzL : (-1 : ℝ) < z := by nlinarith [mul_nonneg hkR.le hx.1]
    have hzU : (z : ℝ) < k+1 := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le]
    have hzLZ : (-1 : ℤ) < z := by exact_mod_cast hzL
    have hzUZ : z < (k : ℤ)+1 := by exact_mod_cast hzU
    omega
  have hqcases : q = 0 ∨ q = 1 := by
    have hqL : 0 ≤ q := by
      by_contra h
      nlinarith
    have hqU : q ≤ 1 := by
      by_contra h
      nlinarith
    omega
  rcases hqcases with hq0 | hq1
  · exact Or.inl (by simpa [hq0] using hq)
  · rw [hq1, mul_one] at hq
    have hj : j.val = 0 := by omega
    exact Or.inr ⟨by simpa [hj] using (ZMod.natCast_zmod_val j).symm, by omega⟩

theorem highPatchCoordinate_contains_lift
    (hzmod : (z : ZMod k) = j) (hclose : |(k : ℝ) * x - z| < 1) :
    x ∈ highPatchCoordinate k j := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have hcl := abs_lt.mp hclose
  rcases highPatch_lift_cube_cases k j x hx z hzmod hclose with hz | ⟨hj0, heq⟩
  · have he : (z : ℝ) = j.val := by exact_mod_cast hz
    unfold highPatchCoordinate
    split_ifs with hj
    · simp only [hj, ZMod.val_zero, Nat.cast_zero] at he
      exact Or.inl ⟨hx.1, (le_div_iff₀ hkR).mpr (by linarith)⟩
    · exact ⟨(div_le_iff₀ hkR).mpr (by linarith), (le_div_iff₀ hkR).mpr (by linarith)⟩
  · have he : (z : ℝ) = k := by exact_mod_cast heq
    rw [highPatchCoordinate, if_pos hj0]
    refine Or.inr ⟨?_, hx.2⟩
    have hr : ((k : ℝ) - 1) / k ≤ x := (div_le_iff₀ hkR).mpr (by linarith)
    convert hr using 1
    field_simp

end

end

section
variable (d k : ℕ) [NeZero k]

theorem highTorusPatch_cube_subset
    (j : HighWindowLabels d k) :
    highTorusPatch d k j ∩ unitCube d ⊆
      Set.pi Set.univ (fun r => highPatchCoordinate k (j r)) := by
  intro x hx r hr
  obtain ⟨z, hz, hclose⟩ := hx.1
  exact highPatchCoordinate_contains_lift k (j r) (x r) (hx.2 r) (z r) (hz r) (hclose r)

/-- The genuine torus patch, including patches wrapping across the
boundary of the unit cube, has the manuscript's volume bound. -/
theorem highTorusPatch_volume_le (hk : 2 ≤ k)
    (j : HighWindowLabels d k) :
    cubeVolume d (highTorusPatch d k j) ≤ ENNReal.ofReal (2 / (k : ℝ)) ^ d := by
  rw [cubeVolume, Measure.restrict_apply (highTorusPatch_measurableSet d k j)]
  calc
    _ ≤ volume (Set.pi Set.univ (fun r => highPatchCoordinate k (j r))) :=
      measure_mono (highTorusPatch_cube_subset d k j)
    _ = ∏ r, volume (highPatchCoordinate k (j r)) := volume_pi_pi _
    _ ≤ ∏ _r : Fin d, ENNReal.ofReal (2 / (k : ℝ)) :=
      Finset.prod_le_prod (fun r _ => highPatchCoordinate_volume_le k (by omega) (j r))
    _ = _ := by simp

end

def highNeighborLabels (d k : ℕ) (j : HighWindowLabels d k) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {j r - 1, j r, j r + 1})

/-- Dependence relation on window labels used by the history laws. -/
abbrev highNeighbors (d k : ℕ) (i j : HighWindowLabels d k) : Prop :=
  j ∈ highNeighborLabels d k i

section
variable (d k : ℕ)

theorem highNeighborLabels_card_le [NeZero k] (j : HighWindowLabels d k) :
    (highNeighborLabels d k j).card ≤ 3 ^ d := by
  rw [highNeighborLabels, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 3 := Finset.prod_le_prod' (fun r _ => Finset.card_le_three)
    _ = _ := by simp

theorem highNeighborLabels_self_mem (j : HighWindowLabels d k) :
    j ∈ highNeighborLabels d k j := by
  apply Fintype.mem_piFinset.mpr
  intro r
  simp

theorem highNeighbors_symm ⦃j l : HighWindowLabels d k⦄
    (h : highNeighbors d k j l) : highNeighbors d k l j := by
  apply Fintype.mem_piFinset.mpr
  intro r
  have hr := Fintype.mem_piFinset.mp h r
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  rcases hr with hr | hr | hr
  · simp_all
  · right
    left
    exact hr.symm
  · left
    rw [hr]
    ring

section
variable [NeZero k]
    (j l : HighWindowLabels d k)

theorem highTorusPatch_intersects_neighbor (h : (highTorusPatch d k j ∩ highTorusPatch d k l).Nonempty) :
    l ∈ highNeighborLabels d k j := by
  obtain ⟨x, ⟨z, hz, hc⟩, ⟨q, hq, hd⟩⟩ := h
  apply Fintype.mem_piFinset.mpr
  intro r
  have hdiff : |(q r : ℝ) - z r| < 2 := by
    have hh := abs_sub_le (q r : ℝ) ((k : ℝ) * x r) (z r : ℝ)
    have hds : |(q r : ℝ) - (k : ℝ) * x r| < 1 := by
      simp_all [abs_sub_comm]
    exact hh.trans_lt (by linarith [hc r])
  have hdiffZ : -1 ≤ q r - z r ∧ q r - z r ≤ 1 := by
    have hh := abs_lt.mp hdiff
    have hL : (-2 : ℤ) < q r - z r := by exact_mod_cast hh.1
    have hU : q r - z r < (2 : ℤ) := by exact_mod_cast hh.2
    omega
  have hqcases : q r = z r - 1 ∨ q r = z r ∨ q r = z r + 1 := by omega
  rcases hqcases with he | he | he
  · have he' : l r = j r - 1 := by simp [← hq r, he, Int.cast_sub, ← hz r]
    simp only [he', Finset.mem_insert, true_or]
  · have he' : l r = j r := by rw [← hq r, he, hz r]
    simp only [he', Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · have he' : l r = j r + 1 := by simp [← hq r, he, Int.cast_add, ← hz r]
    simp only [he', Finset.mem_insert, Finset.mem_singleton, or_true]

theorem highTorusPatch_disjoint_of_not_neighbor (h : l ∉ highNeighborLabels d k j) :
    Disjoint (highTorusPatch d k j) (highTorusPatch d k l) := by
  exact Set.disjoint_left.mpr (fun x hj hl =>
    h (highTorusPatch_intersects_neighbor d k j l ⟨x, hj, hl⟩))

end

theorem highPeriodicTensor_supported_patch (j : HighWindowLabels d k) :
    support (highPeriodicTensor d k j) ⊆ highTorusPatch d k j := by
  intro x hx
  obtain ⟨z, hz, hclose⟩ := highPeriodicTensor_support_lift d k j x hx
  refine ⟨z, hz, ?_⟩
  intro r
  exact (hclose r).trans (by norm_num)

end

end NearlyMinimax
