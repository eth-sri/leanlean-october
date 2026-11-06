module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicMeasure
public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Process.PartitionFiltration
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Grind
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Linarith



/-!
# Finite parabolic dyadic filtration

This file realizes the finite dyadic filtration on the subtype of the
half-open reference cell.  Each parabolic generation is enumerated by `d + 2`
binary generators: one for each velocity child bit and two for the base-four
time child.

The checkpoint theorem identifies the atoms after a complete generator block
with the addressed half-open cells.  No conditional-expectation formula or
Borel-generation assertion is made here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The subtype carrier of the parabolic dyadic reference cell. -/
abbrev ParabolicDyadicReferenceSpace (d : ℕ) : Type :=
  {z : TimeVelocity d // z ∈ parabolicDyadicReferenceCell d}

/-- The finite restricted product volume on the reference-cell subtype. -/
def parabolicDyadicReferenceMeasure (d : ℕ) :
    Measure (ParabolicDyadicReferenceSpace d) :=
  Measure.comap Subtype.val volume

variable (d k : ℕ)

/-- The generation block containing a scheduled binary generator. -/
def parabolicDyadicGeneratorBlock  : ℕ :=
  k / (d + 2)

/-- The location of a scheduled binary generator in its generation block. -/
def parabolicDyadicGeneratorSlot  : Fin (d + 2) :=
  ⟨k % (d + 2), Nat.mod_lt _ (by omega)⟩

/-- The `bit`-th binary digit of a base-four time child. -/
def parabolicDyadicTimeChildBit (child : Fin 4) (bit : Fin 2) : Prop :=
  (child.val / 2 ^ bit.val) % 2 = 1

/-- The binary coordinate of a simultaneous parabolic child selected by a
slot in a `d + 2` generator block. -/
def parabolicDyadicChildBit {d : ℕ} (child : ParabolicDyadicChild d)
    (slot : Fin (d + 2)) : Prop :=
  Fin.addCases
    (fun coordinate => (child.2 coordinate).val = 1)
    ((parabolicDyadicTimeChildBit child.1))
    slot

variable (d k : ℕ)

/-- The ambient union of all next-generation cells whose final child has the
scheduled binary value one. -/
def parabolicDyadicGeneratorAmbient  : HypoellipticAleksandrov.Parabolic.Region d := by
  classical
  exact ⋃ index : ParabolicDyadicIndex d (parabolicDyadicGeneratorBlock d k + 1),
    if parabolicDyadicChildBit
        (index (Fin.last (parabolicDyadicGeneratorBlock d k)))
        (parabolicDyadicGeneratorSlot d k)
    then parabolicDyadicHalfOpenCell index else ∅

/-- The scheduled binary generator, restricted to the reference subtype. -/
def parabolicDyadicGenerator  : Set (ParabolicDyadicReferenceSpace d) :=
  Subtype.val ⁻¹' parabolicDyadicGeneratorAmbient d k

/-- An addressed half-open cell, restricted to the reference subtype. -/
def parabolicDyadicRestrictedCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) : Set (ParabolicDyadicReferenceSpace d) :=
  Subtype.val ⁻¹' parabolicDyadicHalfOpenCell index

variable (d : ℕ)

/-- The reference-subtype measure of its whole carrier is the ambient measure
of the reference cell. -/
theorem parabolicDyadicReferenceMeasure_univ  :
    parabolicDyadicReferenceMeasure d Set.univ =
      volume (parabolicDyadicReferenceCell d) := by
  simpa only [parabolicDyadicReferenceMeasure, Set.image_univ,
    Subtype.range_coe_subtype, Set.setOf_mem_eq] using
    (comap_subtype_coe_apply (measurableSet_parabolicDyadicReferenceCell d) volume
      (Set.univ ))

/-- The total real reference-subtype volume is exactly `2^d`. -/
theorem parabolicDyadicReferenceMeasure_univ_toReal  :
    (parabolicDyadicReferenceMeasure d Set.univ).toReal = (2 : ℝ) ^ d := by
  let index : ParabolicDyadicIndex d 0 := Fin.elim0
  rw [parabolicDyadicReferenceMeasure_univ]
  rw [← parabolicDyadicHalfOpenCell_zero_eq_reference d index]
  simpa using volume_parabolicDyadicHalfOpenCell_toReal index

/-- The finite reference-subtype volume is not infinite. -/
theorem parabolicDyadicReferenceMeasure_univ_ne_top  :
    parabolicDyadicReferenceMeasure d Set.univ ≠ ∞ := by
  intro htop
  have hvolume := parabolicDyadicReferenceMeasure_univ_toReal d
  rw [htop] at hvolume

  simp only [ENNReal.toReal_top] at hvolume
  exact (pow_pos (by norm_num) _).ne' hvolume.symm

/-- Every restricted addressed cell is measurable. -/
theorem measurableSet_parabolicDyadicRestrictedCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    MeasurableSet (parabolicDyadicRestrictedCell index) :=
  measurable_subtype_coe (measurableSet_parabolicDyadicHalfOpenCell index)

/-- Every scheduled generator is measurable. -/
theorem measurableSet_parabolicDyadicGenerator (d k : ℕ) :
    MeasurableSet (parabolicDyadicGenerator d k) := by
  classical
  apply measurable_subtype_coe
  unfold parabolicDyadicGeneratorAmbient
  apply MeasurableSet.iUnion
  intro index
  split_ifs
  · exact measurableSet_parabolicDyadicHalfOpenCell index
  · exact MeasurableSet.empty

/-- The finite filtration generated by the scheduled parabolic dyadic bits. -/
def parabolicDyadicFiltration (d : ℕ) :=
  ProbabilityTheory.partitionFiltration (measurableSet_parabolicDyadicGenerator d)

/-- A point in a selected addressed cell belongs to the corresponding
scheduled generator. -/
theorem mem_parabolicDyadicGenerator_of_mem_cell {d k : ℕ}
    (index : ParabolicDyadicIndex d (parabolicDyadicGeneratorBlock d k + 1))
    (hbit : parabolicDyadicChildBit
      (index (Fin.last (parabolicDyadicGeneratorBlock d k)))
      (parabolicDyadicGeneratorSlot d k))
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    z ∈ parabolicDyadicGenerator d k := by
  classical
  refine Set.mem_preimage.mpr ?_
  unfold parabolicDyadicGeneratorAmbient
  refine Set.mem_iUnion.mpr ⟨index, ?_⟩
  simp only [hbit, ↓reduceIte]
  exact hz

/-- In a fixed generation cell, membership in a scheduled generator is
equivalent to the corresponding final-child bit. -/
theorem mem_parabolicDyadicGenerator_iff_childBit_of_mem_cell {d k q : ℕ}
    (hblock : parabolicDyadicGeneratorBlock d k = q)
    (index : ParabolicDyadicIndex d (q + 1))
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    z ∈ parabolicDyadicGenerator d k ↔
      parabolicDyadicChildBit
        (index (Fin.last q))
        (parabolicDyadicGeneratorSlot d k) := by
  classical
  subst q
  constructor
  · intro hgenerator
    change (z : TimeVelocity d) ∈ parabolicDyadicGeneratorAmbient d k at hgenerator
    unfold parabolicDyadicGeneratorAmbient at hgenerator
    obtain ⟨other, hother⟩ := Set.mem_iUnion.mp hgenerator
    change (z : TimeVelocity d) ∈
      if parabolicDyadicChildBit
          (other (Fin.last (parabolicDyadicGeneratorBlock d k)))
          (parabolicDyadicGeneratorSlot d k)
      then parabolicDyadicHalfOpenCell other else ∅ at hother
    by_cases hotherBit : parabolicDyadicChildBit
        (other (Fin.last (parabolicDyadicGeneratorBlock d k)))
        (parabolicDyadicGeneratorSlot d k)
    · by_contra hbit


      exact (Set.disjoint_left.mp
        (parabolicDyadicHalfOpenCell_disjoint_of_ne (show other ≠ index by
            intro heq
            subst other
            exact hbit hotherBit)) (by
            simpa [hotherBit] using hother) hz).elim
    · simp [hotherBit] at hother
  · exact fun hbit => mem_parabolicDyadicGenerator_of_mem_cell index hbit z hz

/-- Binary time-child bits separate the four time children. -/
theorem parabolicDyadicTimeChildBit_injective {child child' : Fin 4}
    (h : ∀ bit : Fin 2,
      parabolicDyadicTimeChildBit child bit ↔ parabolicDyadicTimeChildBit child' bit) :
    child = child' := by
  apply Fin.ext
  have hzero : child.val % 2 = 1 ↔ child'.val % 2 = 1 := by
    simpa [parabolicDyadicTimeChildBit] using h (0 )
  have hone : (child.val / 2) % 2 = 1 ↔ (child'.val / 2) % 2 = 1 := by
    exact h (1 )
  omega

/-- The full `d + 2` bit vector separates simultaneous parabolic children. -/
theorem parabolicDyadicChildBit_injective {d : ℕ} {child child' : ParabolicDyadicChild d}
    (h : ∀ slot : Fin (d + 2),
      parabolicDyadicChildBit child slot ↔ parabolicDyadicChildBit child' slot) :
    child = child' := by
  apply Prod.ext
  · apply parabolicDyadicTimeChildBit_injective
    intro bit
    simpa only [parabolicDyadicChildBit, Fin.addCases_right] using (h (Fin.natAdd d bit))
  · funext coordinate

    have hbit' : (child.2 coordinate).val = 1 ↔ (child'.2 coordinate).val = 1 := by
      simpa only [parabolicDyadicChildBit, Fin.addCases_left] using (h (Fin.castAdd 2 coordinate))
    omega

variable {α : Type*} (f : ℕ → Set α) (n : ℕ)

/-- Membership in a membership-partition atom is exactly equality of all
previous generator outcomes. -/
theorem mem_memPartitionSet_iff
    (a x : α) :
    x ∈ memPartitionSet f n a ↔
      ∀ k < n, (x ∈ f k ↔ a ∈ f k) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    by_cases ha : a ∈ f n
    · grind
    · grind

/-- A membership partition generated by `n` binary questions has at most
`2^n` members, including any empty branches retained by `memPartition`. -/
theorem ncard_memPartition_le  :
    (memPartition f n).ncard ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    let left  := (fun u  => u ∩ f n) '' memPartition f n
    let right  := (fun u  => u \ f n) '' memPartition f n
    have hpartition :
        {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n} = left ∪ right := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, left, right]
      constructor
      · grind
      · grind
    rw [hpartition]
    calc
      (left ∪ right).ncard ≤ left.ncard + right.ncard := Set.ncard_union_le _ _
      _ ≤ (memPartition f n).ncard + (memPartition f n).ncard := Nat.add_le_add
          (Set.ncard_image_le (finite_memPartition f n))
          (Set.ncard_image_le (finite_memPartition f n))
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih ih
      _ = 2 ^ (n + 1) := by
        rw [pow_succ, Nat.mul_comm]
        exact (two_mul (2 ^ n)).symm

variable {d n : ℕ}

variable (slot : Fin (d + 2))

/-- At a complete-generation offset, the generator block is the prescribed
generation. -/
theorem parabolicDyadicGeneratorBlock_at   :
    parabolicDyadicGeneratorBlock d ((d + 2) * n + slot.val) = n := by
  unfold parabolicDyadicGeneratorBlock
  rw [Nat.add_div_of_dvd_right (dvd_mul_right (d + 2) n)]
  simp [Nat.div_eq_of_lt slot.isLt]

/-- At a complete-generation offset, the generator slot is the prescribed
slot. -/
theorem parabolicDyadicGeneratorSlot_at   :
    parabolicDyadicGeneratorSlot d ((d + 2) * n + slot.val) = slot := by
  apply Fin.ext
  unfold parabolicDyadicGeneratorSlot
  change ((d + 2) * n + slot.val) % (d + 2) = slot.val
  simp [Nat.add_mod, slot.isLt]

/-- On a generation-`n + 1` cell, the generator in the `slot` of block `n`
reads exactly the corresponding final-child bit. -/
theorem mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell
    (index : ParabolicDyadicIndex d (n + 1)) (slot : Fin (d + 2))
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    z ∈ parabolicDyadicGenerator d ((d + 2) * n + slot.val) ↔
      parabolicDyadicChildBit (index (Fin.last n)) slot := by
  have hmembership := mem_parabolicDyadicGenerator_iff_childBit_of_mem_cell
    (parabolicDyadicGeneratorBlock_at slot) index z hz
  rw [parabolicDyadicGeneratorSlot_at slot] at hmembership
  exact hmembership

/-- At generation zero the unique restricted addressed cell is the whole
reference subtype. -/
theorem parabolicDyadicRestrictedCell_zero_eq_univ (d : ℕ)
    (index : ParabolicDyadicIndex d 0) :
    parabolicDyadicRestrictedCell index = Set.univ := by
  ext z
  change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index ↔ z ∈ Set.univ
  rw [parabolicDyadicHalfOpenCell_zero_eq_reference d index]
  simp

/-- Every addressed half-open parabolic dyadic cell has its upper endpoint as
a point.  This also covers `d = 0`, since the velocity verification is then
vacuous. -/
theorem parabolicDyadicHalfOpenCell_nonempty {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    (parabolicDyadicHalfOpenCell index).Nonempty := by
  refine ⟨((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n,
    fun coordinate =>
      -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
        (2 : ℝ) ^ n), ?_⟩
  rw [mem_parabolicDyadicHalfOpenCell_iff]
  constructor
  · rw [mem_parabolicDyadicTimeCell_iff]
    constructor
    · bound
    · rfl
  · rw [mem_parabolicDyadicVelocityCell_iff]
    intro coordinate
    constructor
    · bound
    · rfl

variable (d n k : ℕ)

private theorem parabolicDyadic_checkpoint_prefix_lt
    (hk : k < (d + 2) * n) :
    k < (d + 2) * (n + 1) := by
  linarith

section
variable (hprevious : ¬ k < (d + 2) * n)

include hprevious
private theorem parabolicDyadic_checkpoint_slot_lt

    (hk : k < (d + 2) * (n + 1)) :
    k - (d + 2) * n < d + 2 := by
  grind

private theorem parabolicDyadic_checkpoint_eq_block_add_sub
     : type_of% ((Nat.add_sub_of_le (Nat.le_of_not_gt hprevious)).symm) := (Nat.add_sub_of_le (Nat.le_of_not_gt hprevious)).symm
end


variable {d n : ℕ}

/-- Checkpoint atoms after `n` complete binary blocks are exactly the
generation-`n` addressed half-open cells containing their base point. -/
theorem memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell
     (index : ParabolicDyadicIndex d n)
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    memPartitionSet (parabolicDyadicGenerator d) ((d + 2) * n) z =
      parabolicDyadicRestrictedCell index := by
  induction n generalizing z with
  | zero =>
    simp_all [parabolicDyadicRestrictedCell_zero_eq_univ]
  | succ n ih =>
    let parent  := parabolicDyadicParent index
    let child  := index (Fin.last n)
    have hchildIndex : parabolicDyadicChildIndex parent child = index := parabolicDyadicChildIndex_parent_last index

    have hparentAtom := ih parent z (show (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell parent by
        apply parabolicDyadicHalfOpenCell_child_subset parent child
        simpa only [hchildIndex] using hz)
    apply Set.Subset.antisymm
    · intro y hy
      have hsignature := (mem_memPartitionSet_iff (parabolicDyadicGenerator d)
        ((d + 2) * (n + 1)) z y).mp hy
      have hyparentAtom  :=
        (mem_memPartitionSet_iff (parabolicDyadicGenerator d) ((d + 2) * n) z y).mpr
          (fun k hk => hsignature k (parabolicDyadic_checkpoint_prefix_lt d n k hk))


      obtain ⟨candidate, hycandidate⟩ := Set.mem_iUnion.mp (show (y : TimeVelocity d) ∈
          ⋃ candidate : ParabolicDyadicIndex d (n + 1),
            parabolicDyadicHalfOpenCell candidate by
          rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
          exact y.property)
      have hcandidateParent : parabolicDyadicParent candidate = parent := by
        by_contra hne

        have hsubset := parabolicDyadicHalfOpenCell_child_subset
          _ _ (show (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell
            (parabolicDyadicChildIndex (parabolicDyadicParent candidate)
              (candidate (Fin.last n))) by
              rw [parabolicDyadicChildIndex_parent_last]
              exact hycandidate)
        have hdisjoint := parabolicDyadicHalfOpenCell_disjoint_of_ne hne
        exact (Set.disjoint_left.mp hdisjoint hsubset (by
            rw [hparentAtom] at hyparentAtom
            exact hyparentAtom)).elim


      have hcandidate : candidate = index := by
        rw [← parabolicDyadicChildIndex_parent_last candidate,
          ← parabolicDyadicChildIndex_parent_last index, hcandidateParent, (parabolicDyadicChildBit_injective (show ∀ slot : Fin (d + 2),
          parabolicDyadicChildBit (candidate (Fin.last n)) slot ↔
            parabolicDyadicChildBit child slot by
              intro slot
              have hslot := hsignature ((d + 2) * n + slot.val) (by
                grind)
              rw [mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell candidate slot y
                hycandidate,
                mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell index slot z hz] at hslot
              exact hslot))]
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
      simpa only [hcandidate] using hycandidate
    · intro y hy
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
      apply (mem_memPartitionSet_iff (parabolicDyadicGenerator d)
        ((d + 2) * (n + 1)) z y).mpr
      intro k hk
      by_cases hprevious : k < (d + 2) * n
      ·

        exact (mem_memPartitionSet_iff (parabolicDyadicGenerator d) ((d + 2) * n) z y).mp
          (by
              rw [hparentAtom]
              exact (by
                  apply parabolicDyadicHalfOpenCell_child_subset parent child
                  simpa only [hchildIndex] using hy)) k hprevious
      · let slot : Fin (d + 2) := ⟨k - (d + 2) * n,
          parabolicDyadic_checkpoint_slot_lt d n k hprevious hk⟩
        have hslot : k = (d + 2) * n + slot.val := by
          dsimp [slot]
          exact parabolicDyadic_checkpoint_eq_block_add_sub d n k hprevious
        rw [hslot]
        rw [mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell index slot y hy,
          mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell index slot z hz]

/-- Different addresses determine different restricted half-open cells. -/
theorem parabolicDyadicRestrictedCell_injective  :
    Function.Injective
      (parabolicDyadicRestrictedCell :
        ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d)) := (fun ⦃index index'⦄ heq =>
  Decidable.byContradiction fun hne =>
    Exists.casesOn (parabolicDyadicHalfOpenCell_nonempty index) fun z hz =>
      id (fun hzIndex' => False.elim (disjoint_left.mp (parabolicDyadicHalfOpenCell_disjoint_of_ne hne) hz hzIndex'))
        (Eq.mpr
          (id (congrArg (fun _a => ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩ ∈ _a) (Eq.symm heq)))
          (id hz)))

/-- At every complete-generation checkpoint, the full membership-partition
family is precisely the family of restricted addressed half-open cells. -/
theorem memPartition_parabolicDyadicFiltration_checkpoint_eq_range (d n : ℕ) :
    memPartition (parabolicDyadicGenerator d) ((d + 2) * n) =
      Set.range (parabolicDyadicRestrictedCell :
        ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d)) := by
  let sharedTerm_841f8fb962 := (((d + 2) * n))
  symm
  apply Set.eq_of_subset_of_ncard_le
  · rintro cell ⟨index, rfl⟩
    obtain ⟨z, hz⟩ := parabolicDyadicHalfOpenCell_nonempty index
    let z' : ParabolicDyadicReferenceSpace d :=
      ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩

    rw [← memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell index z' (by
        change z ∈ parabolicDyadicHalfOpenCell index
        exact hz)]
    exact memPartitionSet_mem _ sharedTerm_841f8fb962 z'
  · calc
      (memPartition (parabolicDyadicGenerator d) sharedTerm_841f8fb962).ncard ≤
          2 ^ sharedTerm_841f8fb962 :=
        ncard_memPartition_le _ sharedTerm_841f8fb962
      _ = (Set.range (parabolicDyadicRestrictedCell :
          ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d))).ncard := by
        rw [Set.ncard_range_of_injective parabolicDyadicRestrictedCell_injective,
          Nat.card_eq_fintype_card, card_parabolicDyadicIndex_eq_two_pow]
  · exact finite_memPartition _ sharedTerm_841f8fb962

end

end HypoellipticAleksandrov.Parabolic
