module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicAddress

/-!
# Open covers from parabolic dyadic addresses

This file collects the countable boundary and first-entry infrastructure for
the parabolic dyadic address tree.  It contains no density, ink-spots, or
saturation data.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Function

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The part of a half-open addressed cell omitted by its open interior. -/
def parabolicDyadicAddressBoundary {d : Nat}
    (a : ParabolicDyadicAddress d) : HypoellipticAleksandrov.Parabolic.Region d :=
  parabolicDyadicHalfOpenCell a.2 \ parabolicDyadicOpenCell a.2

/-- The countable union of all addressed parabolic dyadic boundaries. -/
def parabolicDyadicAllBoundary (d : Nat) : HypoellipticAleksandrov.Parabolic.Region d :=
  ⋃ a : ParabolicDyadicAddress d, parabolicDyadicAddressBoundary a

variable {d : Nat}

/-- The non-root addressed cells that first become wholly contained in `U`. -/
def parabolicDyadicFirstEntry  (U : HypoellipticAleksandrov.Parabolic.Region d) :
    Set (ParabolicDyadicAddress d) :=
  fun a => match a with
    | ⟨0, _⟩ => False
    | ⟨_ + 1, index⟩ =>
        parabolicDyadicOpenCell index ⊆ U ∧
          ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ U

private theorem parabolicDyadicOpenCell_subset_of_firstEntry
    {U : HypoellipticAleksandrov.Parabolic.Region d} {a : ParabolicDyadicAddress d}
    (ha : a ∈ parabolicDyadicFirstEntry U) : parabolicDyadicOpenCell a.2 ⊆ U := by
  rcases a with ⟨n, index⟩
  cases n with
  | zero => exact False.elim ha
  | succ n => exact ha.1

/-- The open cell of a child is contained in the open cell of its parent. -/
theorem parabolicDyadicOpenCell_child_subset {d n : Nat}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicOpenCell (parabolicDyadicChildIndex index child) ⊆
      parabolicDyadicOpenCell index := by
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz ⊢
  rw [parabolicDyadicTimeCode_childIndex] at hz
  constructor
  · have hpow : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
    have hchild : 0 ≤ (child.1.val : ℝ) := by positivity
    have htime := hz.1
    norm_num [pow_succ] at htime ⊢
    field_simp [ne_of_gt hpow] at htime ⊢
    nlinarith
  constructor
  · have hpow : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _

    have hchild_le : (child.1.val + 1 : ℝ) ≤ 4 := by
      exact_mod_cast (Nat.succ_le_iff.mpr child.1.isLt)
    have htime := hz.2.1
    norm_num [pow_succ] at htime ⊢
    field_simp [ne_of_gt hpow] at htime ⊢
    nlinarith
  · intro coordinate
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _

    have hvelocity := hz.2.2 coordinate
    rw [parabolicDyadicVelocityCode_childIndex] at hvelocity
    constructor
    · norm_num [pow_succ] at hvelocity ⊢
      field_simp [ne_of_gt hpow] at hvelocity ⊢
      nlinarith [hvelocity.1]
    ·
      have hchild_le : ((child.2 coordinate).val + 1 : ℝ) ≤ 2 := by
        exact_mod_cast (Nat.succ_le_iff.mpr (child.2 coordinate).isLt)
      norm_num [pow_succ] at hvelocity ⊢
      field_simp [ne_of_gt hpow] at hvelocity ⊢
      nlinarith [hvelocity.2]

private theorem parabolicDyadicOpenCell_subset_truncate {d m n : Nat}
    (hmn : m ≤ n) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index ⊆
      parabolicDyadicOpenCell (parabolicDyadicTruncate hmn index) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n hmn ih =>
      calc
        parabolicDyadicOpenCell index ⊆
            parabolicDyadicOpenCell (parabolicDyadicParent index) := by
          simpa only [parabolicDyadicChildIndex_parent_last] using
            (parabolicDyadicOpenCell_child_subset
              (parabolicDyadicParent index) (index (Fin.last n)))
        _ ⊆ parabolicDyadicOpenCell
            (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) :=
          ih (parabolicDyadicParent index)
        _ = parabolicDyadicOpenCell
            (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
          congr 1

variable {d : Nat}

/-- An open addressed cell is contained in the open cell of every ancestor. -/
theorem parabolicDyadicOpenCell_subset_of_addressPrefix
    {a b : ParabolicDyadicAddress d} (hab : parabolicDyadicAddressPrefix a b) :
    parabolicDyadicOpenCell b.2 ⊆ parabolicDyadicOpenCell a.2 := by
  rcases hab with ⟨hmn, htruncate⟩
  rw [← htruncate]
  exact parabolicDyadicOpenCell_subset_truncate hmn b.2

variable (U : HypoellipticAleksandrov.Parabolic.Region d)

/-- First-entry addresses are an antichain for the address-prefix relation. -/
theorem isAntichain_parabolicDyadicFirstEntry   :
    IsAntichain (parabolicDyadicAddressPrefix (d := d))
      (parabolicDyadicFirstEntry U) := by
  rintro ⟨m, a⟩ ha ⟨n, b⟩ hb hne hab
  cases m with
  | zero =>
      change False at ha
      exact ha
  | succ m =>
      cases n with
      | zero =>
          change False at hb
          exact hb
      | succ n =>
          change parabolicDyadicOpenCell a ⊆ U ∧
            ¬ parabolicDyadicOpenCell (parabolicDyadicParent a) ⊆ U at ha
          change parabolicDyadicOpenCell b ⊆ U ∧
            ¬ parabolicDyadicOpenCell (parabolicDyadicParent b) ⊆ U at hb
          rcases hab with ⟨hmn, htruncate⟩
          change m + 1 ≤ n + 1 at hmn
          change parabolicDyadicTruncate hmn b = a at htruncate
          by_cases hmnEq : m + 1 = n + 1
          · have hmnEq' : m = n := by omega
            subst m
            have hba : b = a := by
              calc
                b = parabolicDyadicTruncate (le_refl (n + 1)) b :=
                  (parabolicDyadicTruncate_self b).symm
                _ = a := htruncate
            subst a
            exact hne rfl
          · have hlt  := lt_of_le_of_ne hmn hmnEq
            have hmn'  := Nat.lt_succ_iff.mp hlt
            have hprefix : parabolicDyadicAddressPrefix ⟨m + 1, a⟩
                ⟨n, parabolicDyadicParent b⟩ := by
              refine ⟨hmn', ?_⟩
              calc
                parabolicDyadicTruncate hmn' (parabolicDyadicParent b) =
                    parabolicDyadicTruncate (Nat.le_succ_of_le hmn') b := by
                  rfl
                _ = a := htruncate
            exact hb.2 ((parabolicDyadicOpenCell_subset_of_addressPrefix hprefix).trans ha.1)

/-- Open cells indexed by distinct first entries are pairwise disjoint. -/
theorem pairwiseDisjoint_parabolicDyadicFirstEntry_openCell
     :
    (parabolicDyadicFirstEntry U).Pairwise
      (Disjoint on (fun a  => parabolicDyadicOpenCell a.2)) := by
  rintro a ha b hb hab
  apply disjoint_parabolicDyadicOpenCell_of_incomparable
  · intro habPrefix
    exact isAntichain_parabolicDyadicFirstEntry U ha hb hab habPrefix
  · intro hbaPrefix
    exact isAntichain_parabolicDyadicFirstEntry U hb ha hab.symm hbaPrefix

variable (d : Nat) (U : HypoellipticAleksandrov.Parabolic.Region d) (hU : IsOpen U)

include hU in
/-- An open set captures an interior dyadic cell around each point off every
addressed boundary. -/
theorem exists_parabolicDyadicOpenCell_subset_of_mem_isOpen_off_boundary

    (z : TimeVelocity d) (hzRef : z ∈ parabolicDyadicReferenceCell d)
    (hzU : z ∈ U) (hzBoundary : z ∉ parabolicDyadicAllBoundary d) :
    ∃ a : ParabolicDyadicAddress d,
      z ∈ parabolicDyadicOpenCell a.2 ∧ parabolicDyadicOpenCell a.2 ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  obtain ⟨n, htime, hvelocity⟩ :=
    ((tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hε).and
      (tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hε)).exists
  rw [← iUnion_parabolicDyadicHalfOpenCell_eq_reference d n] at hzRef
  obtain ⟨index, hzHalf⟩ := Set.mem_iUnion.mp hzRef
  have hzOpen : z ∈ parabolicDyadicOpenCell index := by
    by_contra hzNotOpen
    apply hzBoundary
    exact Set.mem_iUnion.mpr ⟨⟨n, index⟩, ⟨hzHalf, hzNotOpen⟩⟩
  refine ⟨⟨n, index⟩, hzOpen, ?_⟩
  rintro ⟨time', velocity'⟩ hy
  apply hball
  have hyHalf  :=
    parabolicDyadicOpenCell_subset_halfOpenCell index hy
  rcases z with ⟨time, velocity⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  apply max_lt
  · exact (abs_sub_le_parabolicDyadicTimeWidth index hyHalf hzHalf).trans_lt htime
  · rw [dist_pi_lt_iff hε]
    intro coordinate
    exact (abs_sub_le_parabolicDyadicVelocityWidth index coordinate hyHalf hzHalf).trans_lt hvelocity

variable (hURef : U ⊆ parabolicDyadicOpenCell (fun i => Fin.elim0 i)) (hRoot : ¬ parabolicDyadicOpenCell (fun i => Fin.elim0 i) ⊆ U)

include hU hURef hRoot
private theorem exists_parabolicDyadicFirstEntry_of_mem_isOpen_off_boundary


    (z : TimeVelocity d) (hzU : z ∈ U) (hzBoundary : z ∉ parabolicDyadicAllBoundary d) :
    ∃ a : ParabolicDyadicAddress d,
      a ∈ parabolicDyadicFirstEntry U ∧ z ∈ parabolicDyadicOpenCell a.2 := by
  classical
  let root : ParabolicDyadicIndex d 0 := Fin.elim0
  have hzRoot  := hURef hzU
  have hzReference : z ∈ parabolicDyadicReferenceCell d := by
    rw [← parabolicDyadicHalfOpenCell_zero_eq_reference d root]
    exact parabolicDyadicOpenCell_subset_halfOpenCell root hzRoot
  obtain ⟨address, hzAddress, hAddressU⟩ :=
    exists_parabolicDyadicOpenCell_subset_of_mem_isOpen_off_boundary
      d U hU z hzReference hzU hzBoundary
  let P  := fun n => ∃ index : ParabolicDyadicIndex d n,
    z ∈ parabolicDyadicOpenCell index ∧ parabolicDyadicOpenCell index ⊆ U
  have hP : ∃ n, P n := ⟨address.1, address.2, hzAddress, hAddressU⟩
  have hnZero : Nat.find hP ≠ 0 := by
    intro hn
    have hZero : P 0 := by simpa only [hn] using Nat.find_spec hP
    obtain ⟨index, hzIndex, hIndexU⟩ := hZero
    apply hRoot
    assumption
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnZero
  have hSucc : P (m + 1) := by simpa only [hm] using Nat.find_spec hP
  obtain ⟨index, hzIndex, hIndexU⟩ := hSucc
  refine ⟨⟨m + 1, index⟩, ?_, hzIndex⟩
  change parabolicDyadicOpenCell index ⊆ U ∧
    ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ U
  refine ⟨hIndexU, ?_⟩
  intro hParentU
  have hzChild : z ∈ parabolicDyadicOpenCell
      (parabolicDyadicChildIndex (parabolicDyadicParent index) (index (Fin.last m))) := by
    simpa using hzIndex
  have hMin := Nat.find_min' hP (show P m from ⟨_,
    parabolicDyadicOpenCell_child_subset _ _
      hzChild, hParentU⟩)
  rw [hm] at hMin
  omega

/-- Subject to the root exclusion, an open subset of the root is a.e. the
union of its first-entry open cells. -/
theorem ae_eq_iUnion_parabolicDyadicFirstEntry_openCell

     :
    U =ᵐ[volume] ⋃ a ∈ parabolicDyadicFirstEntry U, parabolicDyadicOpenCell a.2 := (id
  (ae_eq_set.mpr
    ⟨measure_mono_null
        (fun ⦃z⦄ hz =>
          Classical.byContradiction fun hzBoundary =>
            Exists.casesOn
              (exists_parabolicDyadicFirstEntry_of_mem_isOpen_off_boundary d U hU hURef hRoot z hz.left hzBoundary)
              fun address h =>
              And.casesOn h fun hEntry hzAddress =>
                hz.right (mem_iUnion.mpr (Exists.intro address (mem_iUnion.mpr (Exists.intro hEntry hzAddress)))))
        (id (measure_iUnion_null fun a => (ae_eq_set.mp (parabolicDyadicOpenCell_ae_eq_halfOpenCell a.snd)).right)),
      Eq.mpr
        (id
          (congrArg (fun _a => volume _a = 0)
            (diff_eq_empty.mpr fun ⦃z⦄ hz =>
              Exists.casesOn (mem_iUnion.mp hz) fun address hzAddress =>
                Exists.casesOn (mem_iUnion.mp hzAddress) fun hEntry hzAddress =>
                  parabolicDyadicOpenCell_subset_of_firstEntry hEntry hzAddress)))
        measure_empty⟩))

end

end HypoellipticAleksandrov.Parabolic
