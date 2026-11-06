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
    ∀ r, |↑k * x r - z r| < 1}

theorem highTorusPatch_measurableSet (d k j) :
    MeasurableSet (highTorusPatch d k j) := by
  unfold highTorusPatch
  simp_rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro z
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · have he : {x : Covariate d | (∀ r, (z r : ZMod k) = j r) ∧
        ∀ r, |k * x r - z r| < 1} =
        {x : Covariate d | ∀ r, |k * x r - z r| < 1} := by
      ext x
      exact and_iff_right hz
    rw [he]
    simp_rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro r
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  · simp only [hz, false_and, setOf_false]
    exact MeasurableSet.empty

def highPatchCoordinate (k ) (j : ZMod k) : Set ℝ :=
  if j = 0 then Icc 0 (1 / k) ∪ Icc (1 - 1 / k) 1 else
    Icc ((j.val - 1) / k) ((j.val + 1) / k)

def highNeighborLabels (d k ) (j : HighWindowLabels d k) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset (fun r => {j r - 1, j r, j r + 1})

theorem highNeighborLabels_card_le (d k ) [NeZero k] (j ) :
    (highNeighborLabels d k j).card ≤ 3 ^ d := by
  rw [highNeighborLabels, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _r : Fin d, 3 := Finset.prod_le_prod' (fun r _ => Finset.card_le_three)
    _ = _ := by simp

theorem highNeighborLabels_self_mem (d k j) :
    j ∈ highNeighborLabels d k j := by
  apply Fintype.mem_piFinset.mpr
  intro r
  simp

theorem highNeighborLabels_symmetric (d k j l)
    (h : l ∈ highNeighborLabels d k j) : j ∈ highNeighborLabels d k l := by
  apply Fintype.mem_piFinset.mpr
  intro r
  have hr := Fintype.mem_piFinset.mp h r
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  rcases hr with hr | hr | hr
  · right
    right
    rw [hr]
    ring
  · right
    left
    exact hr.symm
  · left
    rw [hr]
    ring

theorem highTorusPatch_disjoint_of_not_neighbor (d k ) [NeZero k]
    (j l ) (h : l ∉ highNeighborLabels d k j) :
    Disjoint (highTorusPatch d k j) (highTorusPatch d k l) := by
  have h_highTorusPatch_intersects_neighbor (h : (highTorusPatch d k j ∩ highTorusPatch d k l).Nonempty) : l ∈ highNeighborLabels d k j := by
    obtain ⟨x, ⟨z, hz, hc⟩, ⟨q, hq, hd⟩⟩ := h
    apply Fintype.mem_piFinset.mpr
    intro r
    have hdiff : |(q r : ℝ) - z r| < 2 := by
      have hh := abs_sub_le (q r : ℝ) (↑k * x r) (z r : ℝ)
      have : |(q r : ℝ) - ↑k * x r| < 1 := by
        rw [abs_sub_comm]
        exact hd r
      exact hh.trans_lt (by linarith [hc r])
    have : -1 ≤ q r - z r ∧ q r - z r ≤ 1 := by
      have hh := abs_lt.mp hdiff
      have : (-2 ) < q r - z r := by exact_mod_cast hh.1
      have : q r - z r < 2 := by exact_mod_cast hh.2
      omega
    have hqcases : q r = z r - 1 ∨ q r = z r ∨ q r = z r + 1 := by omega
    rcases hqcases with he | he | he
    · have he' : l r = j r - 1 := by rw [← hq r, he, Int.cast_sub, ← hz r]; simp
      simp only [he', Finset.mem_insert, true_or]
    · have he' : l r = j r := by rw [← hq r, he, hz r]
      simp only [he', Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · have he' : l r = j r + 1 := by rw [← hq r, he, Int.cast_add, ← hz r]; simp
      simp only [he', Finset.mem_insert, Finset.mem_singleton, or_true]
  exact Set.disjoint_left.mpr (fun x hj hl =>
    h (h_highTorusPatch_intersects_neighbor ⟨x, hj, hl⟩))

theorem highPeriodicTensor_supported_patch (d k : ℕ) (j : HighWindowLabels d k) :
    support (highPeriodicTensor d k j) ⊆ highTorusPatch d k j := by
  intro x hx
  have h_highPeriodicTensor_support_lift : ∃ z : Fin d → ℤ, (∀ i, (z i : ZMod k) = j i) ∧
      ∀ i, |↑k * x i - z i| < 3 / 4 := by
    have hcoordinate (i : Fin d) : highPeriodicWindow k (j i) (x i) ≠ 0 := by
      intro h
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
    choose z hz using fun i => highPeriodicWindow_support_lift k (j i) (x i) (hcoordinate i)
    exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩
  obtain ⟨z, hz, hclose⟩ := h_highPeriodicTensor_support_lift
  refine ⟨z, hz, ?_⟩
  intro r
  exact (hclose r).trans (by norm_num)

end NearlyMinimax
