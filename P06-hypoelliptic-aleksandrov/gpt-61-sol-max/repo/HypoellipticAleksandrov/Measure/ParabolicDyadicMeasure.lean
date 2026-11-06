module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicGrid
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Ring



/-!
# Finite parabolic dyadic measure geometry

This module develops the finite measure geometry of the parabolic dyadic
subdivision of `(0, 1] × (-1, 1]^d`.  A refinement quarters time and bisects
every velocity coordinate.  Half-open cells are the exact partition pieces;
their open interiors are used only modulo product Lebesgue null sets.

## Main definitions

* `parabolicDyadicReferenceCell` is the fixed half-open reference rectangle.
* `parabolicDyadicGenerationCells` is the unbundled finite family of cells at
  a fixed generation.

No filtration, generated sigma-algebra, conditional expectation, or metric
ball differentiation assertion is made here.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The half-open reference rectangle for the parabolic dyadic subdivision. -/
def parabolicDyadicReferenceCell (d : ℕ) : HypoellipticAleksandrov.Parabolic.Region d :=
  Ioc (0 : ℝ) 1 ×ˢ Set.univ.pi fun _ : Fin d => Ioc (-1 : ℝ) 1

variable (n : ℕ)

/-- The time width of a generation-`n` parabolic dyadic cell. -/
def parabolicDyadicTimeWidth  : ℝ :=
  ((4 : ℝ) ^ n)⁻¹

/-- The width in each velocity coordinate of a generation-`n` cell. -/
def parabolicDyadicVelocityWidth  : ℝ :=
  2 * ((2 : ℝ) ^ n)⁻¹

/-- The finite, unbundled family of generation-`n` half-open dyadic cells. -/
def parabolicDyadicGenerationCells (d n : ℕ) : Finset (HypoellipticAleksandrov.Parabolic.Region d) := by
  classical
  exact Finset.univ.image (fun index : ParabolicDyadicIndex d n =>
    parabolicDyadicHalfOpenCell index)

/-- Membership in the finite generation family is exactly representation by an
address of that generation. -/
theorem mem_parabolicDyadicGenerationCells_iff {d n : ℕ} {s : HypoellipticAleksandrov.Parabolic.Region d} :
    s ∈ parabolicDyadicGenerationCells d n ↔
      ∃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index = s := by
  simp_all [parabolicDyadicGenerationCells]

variable (d : ℕ)

/-- The reference cell is measurable for product Lebesgue measure. -/
theorem measurableSet_parabolicDyadicReferenceCell  :
    MeasurableSet (parabolicDyadicReferenceCell d) :=
  measurableSet_Ioc.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)

/-- Generation zero has precisely the reference half-open cell. -/
theorem parabolicDyadicHalfOpenCell_zero_eq_reference
    (index : ParabolicDyadicIndex d 0) :
    parabolicDyadicHalfOpenCell index = parabolicDyadicReferenceCell d := by
  ext z
  rcases z with ⟨time, velocity⟩
  simp only [parabolicDyadicHalfOpenCell, parabolicDyadicTimeCell,
    parabolicDyadicVelocityCell, parabolicDyadicReferenceCell,
    parabolicDyadicTimeCode, parabolicDyadicVelocityCode, Nat.cast_zero,
    pow_zero, div_one, zero_add, Set.mem_prod, Set.mem_Ioc, Set.mem_pi,
    Set.mem_univ, forall_true_left]
  norm_num

/-- The generation-zero finite family is the singleton reference cell. -/
theorem parabolicDyadicGenerationCells_zero  :
    parabolicDyadicGenerationCells d 0 = {parabolicDyadicReferenceCell d} := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨index, hindex⟩ := mem_parabolicDyadicGenerationCells_iff.mp hs
    simp only [Finset.mem_singleton]
    exact hindex.symm.trans (parabolicDyadicHalfOpenCell_zero_eq_reference d index)
  · simp_all [parabolicDyadicReferenceCell, ParabolicDyadicIndex, mem_parabolicDyadicGenerationCells_iff, parabolicDyadicHalfOpenCell_zero_eq_reference]

/-- The generation-zero family has union the reference cell. -/
theorem iUnion_parabolicDyadicGenerationCells_zero  :
    ⋃ s ∈ parabolicDyadicGenerationCells d 0, s = parabolicDyadicReferenceCell d := by
  rw [parabolicDyadicGenerationCells_zero]
  simp

variable (a h : ℝ)

/-- The four consecutive half-open intervals of equal width partition their
parent interval. -/
private theorem iUnion_Ioc_four_eq_Ioc  :
    (⋃ c : Fin 4, Ioc (a + c.1 * h) (a + (c.1 + 1) * h)) =
      Ioc a (a + 4 * h) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨c, hc⟩
    constructor
    · fin_cases c <;> norm_num at hc ⊢ <;> linarith
    · fin_cases c <;> norm_num at hc ⊢ <;> linarith
  · intro hx
    by_cases h₁ : x ≤ a + h
    · exact ⟨0, by norm_num; exact ⟨hx.1, h₁⟩⟩
    by_cases h₂ : x ≤ a + 2 * h
    · exact ⟨1, by norm_num; exact ⟨by linarith, h₂⟩⟩
    by_cases h₃ : x ≤ a + 3 * h
    · exact ⟨2, by norm_num; exact ⟨by linarith, h₃⟩⟩
    · exact ⟨3, by norm_num; exact ⟨by linarith, hx.2⟩⟩

/-- The two consecutive half-open intervals of equal width partition their
parent interval. -/
private theorem iUnion_Ioc_two_eq_Ioc  :
    (⋃ c : Fin 2, Ioc (a + c.1 * h) (a + (c.1 + 1) * h)) =
      Ioc a (a + 2 * h) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨c, hc⟩
    constructor
    · fin_cases c <;> norm_num at hc ⊢ <;> linarith
    · fin_cases c <;> norm_num at hc ⊢ <;> linarith
  · intro hx
    by_cases h : x ≤ a + h
    · exact ⟨0, by norm_num; exact ⟨hx.1, h⟩⟩
    · exact ⟨1, by norm_num; exact ⟨by linarith, hx.2⟩⟩

/-- Distinct consecutive `Fin 4` half-open intervals are disjoint. -/
private theorem disjoint_Ioc_four_of_ne
    {c c' : Fin 4} (hcc' : c ≠ c') :
    Disjoint (Ioc (a + c.1 * h) (a + (c.1 + 1) * h))
      (Ioc (a + c'.1 * h) (a + (c'.1 + 1) * h)) := by
  fin_cases c <;> fin_cases c' <;> try { exact (hcc' rfl).elim }
  all_goals
    grind

/-- Distinct consecutive `Fin 2` half-open intervals are disjoint. -/
private theorem disjoint_Ioc_two_of_ne
    {c c' : Fin 2} (hcc' : c ≠ c') :
    Disjoint (Ioc (a + c.1 * h) (a + (c.1 + 1) * h))
      (Ioc (a + c'.1 * h) (a + (c'.1 + 1) * h)) := by
  fin_cases c <;> fin_cases c' <;> try { exact (hcc' rfl).elim }
  all_goals
    grind

variable {d n : ℕ} (index : ParabolicDyadicIndex d n)

variable (child : ParabolicDyadicChild d)

/-- The time interval of a child is one of four consecutive equal subintervals
of its parent interval. -/
private theorem parabolicDyadicTimeCell_childIndex_eq   :
    parabolicDyadicTimeCell (parabolicDyadicChildIndex index child) =
      Ioc
        ((parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n +
          (child.1.1 : ℝ) / (4 : ℝ) ^ (n + 1))
        ((parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n +
          (child.1.1 + 1 : ℝ) / (4 : ℝ) ^ (n + 1)) := by
  rw [parabolicDyadicTimeCell, parabolicDyadicTimeCode_childIndex]
  congr 1 <;> field_simp <;> push_cast <;> ring

/-- One velocity coordinate interval of a child is one of two consecutive
equal subintervals of its parent's coordinate interval. -/
private theorem parabolicDyadicVelocityCell_childIndex_apply
    (coordinate : Fin d) :
    (fun coordinate =>
      Ioc (-1 + 2 * (parabolicDyadicVelocityCode (n + 1)
        (parabolicDyadicChildIndex index child) coordinate : ℝ) / (2 : ℝ) ^ (n + 1))
        (-1 + 2 * (parabolicDyadicVelocityCode (n + 1)
          (parabolicDyadicChildIndex index child) coordinate + 1 : ℝ) /
          (2 : ℝ) ^ (n + 1))) coordinate =
      Ioc
        (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n +
          2 * ((child.2 coordinate).1 : ℝ) / (2 : ℝ) ^ (n + 1))
        (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n +
          2 * ((child.2 coordinate).1 + 1 : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  dsimp
  rw [parabolicDyadicVelocityCode_childIndex]
  congr 1 <;> field_simp <;> push_cast <;> ring

/-- The full velocity rectangle of a child is the product of its two-way
coordinate subdivisions. -/
private theorem parabolicDyadicVelocityCell_childIndex_eq   :
    parabolicDyadicVelocityCell (parabolicDyadicChildIndex index child) =
      Set.univ.pi fun coordinate =>
        Ioc
          (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n +
            2 * ((child.2 coordinate).1 : ℝ) / (2 : ℝ) ^ (n + 1))
          (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n +
            2 * ((child.2 coordinate).1 + 1 : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  simp_all [parabolicDyadicVelocityCell, parabolicDyadicVelocityCell_childIndex_apply]

/-- The half-open children of an addressed cell have union exactly equal to
their parent cell. -/
theorem iUnion_parabolicDyadicHalfOpenCell_child_eq  :
    (⋃ child : ParabolicDyadicChild d,
      parabolicDyadicHalfOpenCell (parabolicDyadicChildIndex index child)) =
      parabolicDyadicHalfOpenCell index := by
  ext z
  rcases z with ⟨time, velocity⟩
  simp only [Set.mem_iUnion, mem_parabolicDyadicHalfOpenCell_iff]
  let a : ℝ := (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n
  let h : ℝ := ((4 : ℝ) ^ (n + 1))⁻¹
  have htimePartition :
      (⋃ c : Fin 4, Ioc (a + c.1 * h) (a + (c.1 + 1) * h)) =
        parabolicDyadicTimeCell index := by
    rw [iUnion_Ioc_four_eq_Ioc]
    unfold a h parabolicDyadicTimeCell
    congr 1
    all_goals
      field_simp
      ring
  constructor
  · rintro ⟨child, htime, hvelocity⟩
    constructor
    · rw [parabolicDyadicTimeCell_childIndex_eq] at htime
      have htimeChild : time ∈
          Ioc (a + child.1.1 * h) (a + (child.1.1 + 1) * h) := by
        exact htime
      rw [← htimePartition]
      exact Set.mem_iUnion.mpr ⟨child.1, htimeChild⟩
    · intro coordinate _
      let b : ℝ := -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
        (2 : ℝ) ^ n
      let k : ℝ := 2 * ((2 : ℝ) ^ (n + 1))⁻¹
      have hright : b + 2 * k =
          -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
            (2 : ℝ) ^ n := by
        unfold b k
        field_simp
        ring

      rw [parabolicDyadicVelocityCell_childIndex_eq] at hvelocity
      have hvelocityChild : velocity coordinate ∈
          Ioc (b + (child.2 coordinate).1 * k)
            (b + ((child.2 coordinate).1 + 1) * k) := by
        rw [mem_Ioc]
        have hcoordinate := hvelocity coordinate trivial
        constructor
        · convert hcoordinate.1 using 1
          all_goals
            unfold b k
            field_simp
        · convert hcoordinate.2 using 1
          all_goals
            unfold b k
            field_simp
      have hparent : velocity coordinate ∈ Ioc b (b + 2 * k) := by
        rw [← (iUnion_Ioc_two_eq_Ioc b k)]
        exact Set.mem_iUnion.mpr ⟨_, hvelocityChild⟩
      rw [mem_Ioc] at hparent ⊢
      simpa only [b, hright] using hparent
  · rintro ⟨htime, hvelocity⟩
    rw [mem_parabolicDyadicVelocityCell_iff] at hvelocity

    obtain ⟨timeChild, htimeChild⟩ := Set.mem_iUnion.mp (by
        rw [htimePartition]
        exact htime)
    have hvelocityChildExists : ∀ coordinate : Fin d, ∃ velocityChild : Fin 2,
        velocity coordinate ∈
          Ioc
            (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
                (2 : ℝ) ^ n + 2 * velocityChild.1 * ((2 : ℝ) ^ (n + 1))⁻¹)
            (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
                (2 : ℝ) ^ n + 2 * (velocityChild.1 + 1) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
      intro coordinate
      let b : ℝ := -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
        (2 : ℝ) ^ n
      let k : ℝ := 2 * ((2 : ℝ) ^ (n + 1))⁻¹
      have hright : b + 2 * k =
          -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
            (2 : ℝ) ^ n := by
        unfold b k
        field_simp
        ring


      obtain ⟨velocityChild, hvelocityChild⟩ := Set.mem_iUnion.mp (by
        rw [(iUnion_Ioc_two_eq_Ioc b k)]
        exact (by
            rw [mem_Ioc]
            rw [hright]
            exact hvelocity coordinate))
      exact ⟨velocityChild, by
        grind⟩
    choose velocityChild hvelocityChild using hvelocityChildExists
    refine ⟨(timeChild, velocityChild), ?_, ?_⟩
    · rw [parabolicDyadicTimeCell_childIndex_eq]
      exact htimeChild
    · rw [mem_parabolicDyadicVelocityCell_iff]
      intro coordinate
      rw [parabolicDyadicVelocityCode_childIndex]
      have hcoordinate := hvelocityChild coordinate
      rw [mem_Ioc] at hcoordinate
      constructor
      · convert hcoordinate.1 using 1
        all_goals
          field_simp
          push_cast
          ring
      · convert hcoordinate.2 using 1
        all_goals
          field_simp
          push_cast
          ring

/-- Two distinct children of an addressed cell are disjoint. -/
theorem disjoint_parabolicDyadicHalfOpenCell_child_of_ne  {child child' : ParabolicDyadicChild d}
    (hchild : child ≠ child') :
    Disjoint (parabolicDyadicHalfOpenCell (parabolicDyadicChildIndex index child))
      (parabolicDyadicHalfOpenCell (parabolicDyadicChildIndex index child')) := by
  by_cases htime : child.1 = child'.1
  ·
    obtain ⟨coordinate, hcoordinate⟩ : ∃ coordinate, child.2 coordinate ≠ child'.2 coordinate := by
      by_contra h
      push_neg at h
      exact (show child.2 ≠ child'.2 by
          intro hvelocity
          exact hchild (Prod.ext htime hvelocity)) (funext h)
    apply Set.disjoint_left.2
    intro z hz hz'
    rcases z with ⟨time, velocity⟩
    rw [mem_parabolicDyadicHalfOpenCell_iff] at hz hz'
    rw [parabolicDyadicVelocityCell_childIndex_eq] at hz hz'
    have hzcoordinate := hz.2 coordinate trivial
    have hzcoordinate' := hz'.2 coordinate trivial
    rw [mem_Ioc] at hzcoordinate hzcoordinate'
    let b : ℝ := -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n
    let k : ℝ := 2 * ((2 : ℝ) ^ (n + 1))⁻¹


    exact (Set.disjoint_left.1 (disjoint_Ioc_two_of_ne b k hcoordinate) (show velocity coordinate ∈
          Ioc (b + (child.2 coordinate).1 * k)
            (b + ((child.2 coordinate).1 + 1) * k) by
        rw [mem_Ioc]
        constructor
        · grind
        · grind) (by
        rw [mem_Ioc]
        constructor
        · grind
        · grind))
  · apply Set.disjoint_left.2
    intro z hz hz'
    rcases z with ⟨time, velocity⟩
    rw [mem_parabolicDyadicHalfOpenCell_iff] at hz hz'
    rw [parabolicDyadicTimeCell_childIndex_eq] at hz hz'
    let a : ℝ := (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n
    let h : ℝ := ((4 : ℝ) ^ (n + 1))⁻¹


    exact (Set.disjoint_left.1 (disjoint_Ioc_four_of_ne a h htime) (show time ∈ Ioc (a + child.1.1 * h) (a + (child.1.1 + 1) * h) by
        exact hz.1) (show time ∈ Ioc (a + child'.1.1 * h) (a + (child'.1.1 + 1) * h) by
        exact hz'.1))

/-- Every addressed child is contained in its parent cell. -/
theorem parabolicDyadicHalfOpenCell_child_subset  (child : ParabolicDyadicChild d) :
    parabolicDyadicHalfOpenCell (parabolicDyadicChildIndex index child) ⊆
      parabolicDyadicHalfOpenCell index := by
  rw [← iUnion_parabolicDyadicHalfOpenCell_child_eq index]
  exact Set.subset_iUnion (fun child =>
    parabolicDyadicHalfOpenCell (parabolicDyadicChildIndex index child)) child

/-- The finite half-open cells at every generation have union the reference
cell. -/
theorem iUnion_parabolicDyadicGenerationCells (d n : ℕ) :
    ⋃ s ∈ parabolicDyadicGenerationCells d n, s = parabolicDyadicReferenceCell d := by
  induction n with
  | zero => exact iUnion_parabolicDyadicGenerationCells_zero d
  | succ n ih =>
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨s, hs, hzs⟩ := hz
      obtain ⟨index, hindex⟩ := mem_parabolicDyadicGenerationCells_iff.mp hs
      rw [← hindex] at hzs
      let parent := parabolicDyadicParent index
      let child := index (Fin.last n)
      have hdecompose : parabolicDyadicChildIndex parent child = index := parabolicDyadicChildIndex_parent_last index


      rw [← ih]
      exact Set.mem_iUnion.mpr ⟨_,
        Set.mem_iUnion.mpr ⟨(show _ by
            rw [mem_parabolicDyadicGenerationCells_iff]
            exact ⟨parent, rfl⟩), (parabolicDyadicHalfOpenCell_child_subset parent child (by simpa only [hdecompose] using hzs))⟩⟩
    · intro hz
      rw [← ih] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨s, hs, hzs⟩ := hz
      obtain ⟨parent, hparent⟩ := mem_parabolicDyadicGenerationCells_iff.mp hs
      rw [← hparent] at hzs
      rw [← iUnion_parabolicDyadicHalfOpenCell_child_eq parent] at hzs
      obtain ⟨child, hzchild⟩ := Set.mem_iUnion.mp hzs
      let index := parabolicDyadicChildIndex parent child

      exact Set.mem_iUnion.mpr ⟨_,
        Set.mem_iUnion.mpr ⟨(show _ by
            rw [mem_parabolicDyadicGenerationCells_iff]
            exact ⟨index, rfl⟩), hzchild⟩⟩

/-- Distinct addresses at a fixed generation define disjoint half-open cells. -/
private theorem disjoint_parabolicDyadicHalfOpenCell_of_ne {d : ℕ} :
    ∀ {n : ℕ} (index index' : ParabolicDyadicIndex d n), index ≠ index' →
      Disjoint (parabolicDyadicHalfOpenCell index) (parabolicDyadicHalfOpenCell index')
  | 0, index, index', hindex => by
      exfalso
      apply hindex
      funext j
      exact Fin.elim0 j
  | n + 1, index, index', hindex => by

      let child' := index' (Fin.last n)
      have hchildIndex :
          parabolicDyadicChildIndex (parabolicDyadicParent index) (index (Fin.last n)) = index :=
        parabolicDyadicChildIndex_parent_last index
      have hchildIndex' :
          parabolicDyadicChildIndex (parabolicDyadicParent index') child' = index' :=
        parabolicDyadicChildIndex_parent_last index'
      by_cases hparent : parabolicDyadicParent index = parabolicDyadicParent index'
      ·
        have hchildIndex'' : parabolicDyadicChildIndex (parabolicDyadicParent index) child' =
            index' := by
          simpa only [hparent] using hchildIndex'
        rw [← hchildIndex, ← hchildIndex'']
        exact disjoint_parabolicDyadicHalfOpenCell_child_of_ne
          _ (by
              intro hchild
              apply hindex
              rw [← hchildIndex, ← hchildIndex', hparent, hchild])
      ·
        rw [← hchildIndex, ← hchildIndex']
        exact (disjoint_parabolicDyadicHalfOpenCell_of_ne _ _ hparent).mono
          (parabolicDyadicHalfOpenCell_child_subset _ _)
          (parabolicDyadicHalfOpenCell_child_subset _ _)

/-- Every addressed half-open cell is contained in the reference cell. -/
theorem parabolicDyadicHalfOpenCell_subset_reference {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicHalfOpenCell index ⊆ parabolicDyadicReferenceCell d := by
  intro z hz
  rw [← iUnion_parabolicDyadicGenerationCells d n]
  exact Set.mem_iUnion.mpr ⟨_,
    Set.mem_iUnion.mpr ⟨mem_parabolicDyadicGenerationCells_iff.mpr ⟨index, rfl⟩, hz⟩⟩

/-- The union of all addressed half-open cells at one generation is the
reference cell. -/
theorem iUnion_parabolicDyadicHalfOpenCell_eq_reference (d n : ℕ) :
    (⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index) =
      parabolicDyadicReferenceCell d := by
  rw [← iUnion_parabolicDyadicGenerationCells d n]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨index, hz⟩
    exact ⟨_,
      ⟨mem_parabolicDyadicGenerationCells_iff.mpr ⟨index, rfl⟩, hz⟩⟩
  · rintro ⟨s, hs, hz⟩
    obtain ⟨index, hindex⟩ := mem_parabolicDyadicGenerationCells_iff.mp hs
    exact ⟨index, hindex ▸ hz⟩

variable {d n : ℕ}

/-- Distinct addresses at one generation define disjoint half-open cells. -/
theorem parabolicDyadicHalfOpenCell_disjoint_of_ne
    {index index' : ParabolicDyadicIndex d n} (hindex : index ≠ index') :
    Disjoint (parabolicDyadicHalfOpenCell index) (parabolicDyadicHalfOpenCell index') :=
  disjoint_parabolicDyadicHalfOpenCell_of_ne index index' hindex

variable (index : ParabolicDyadicIndex d n)

/-- The exact width of the time interval of an addressed cell. -/
theorem parabolicDyadicTimeCell_width   :
    ((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n) -
        (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n =
      parabolicDyadicTimeWidth n := by
  unfold parabolicDyadicTimeWidth
  field_simp
  ring

/-- The exact width of one velocity coordinate interval of an addressed cell. -/
theorem parabolicDyadicVelocityCell_width
    (coordinate : Fin d) :
    (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
          (2 : ℝ) ^ n) -
        (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
          (2 : ℝ) ^ n) =
      parabolicDyadicVelocityWidth n := by
  unfold parabolicDyadicVelocityWidth
  field_simp
  ring

/-- The time widths shrink to zero. -/
theorem tendsto_parabolicDyadicTimeWidth_atTop :
    Tendsto parabolicDyadicTimeWidth atTop (𝓝 0) := by
  change Tendsto (fun n  => ((4 : ℝ) ^ n)⁻¹) atTop (𝓝 0)
  simpa only [← inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (4 : ℝ)⁻¹ by positivity)
      (show (4 : ℝ)⁻¹ < 1 by norm_num))

/-- The velocity-coordinate widths shrink to zero. -/
theorem tendsto_parabolicDyadicVelocityWidth_atTop :
    Tendsto parabolicDyadicVelocityWidth atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 2 * ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0)
  simpa only [← inv_pow, mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)).const_mul 2

variable {d n : ℕ} (index : ParabolicDyadicIndex d n)

/-- The open addressed cell agrees almost everywhere with its half-open
counterpart under product Lebesgue measure. -/
theorem parabolicDyadicOpenCell_ae_eq_halfOpenCell  :
    parabolicDyadicOpenCell index =ᵐ[volume] parabolicDyadicHalfOpenCell index := by
  rw [volume_timeVelocity_eq_prod]
  exact Measure.set_prod_ae_eq Ioo_ae_eq_Ioc Measure.pi_Ioo_ae_eq_pi_Ioc

/-- The real volume of an addressed time interval is its exact dyadic width. -/
theorem volume_parabolicDyadicTimeCell_toReal  :
    (volume (parabolicDyadicTimeCell index)).toReal = parabolicDyadicTimeWidth n := by
  simp_all [parabolicDyadicTimeCode, parabolicDyadicTimeCell_width, parabolicDyadicTimeWidth, parabolicDyadicTimeCell]

/-- The real volume of an addressed velocity rectangle is the product of its
equal coordinate widths. -/
theorem volume_parabolicDyadicVelocityCell_toReal  :
    (volume (parabolicDyadicVelocityCell index)).toReal =
      (parabolicDyadicVelocityWidth n) ^ d := by
  rw [parabolicDyadicVelocityCell, Real.volume_pi_Ioc_toReal]
  · simp_rw [parabolicDyadicVelocityCell_width]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro coordinate
    rw [← sub_nonneg]
    rw [parabolicDyadicVelocityCell_width]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity))

/-- The product-volume factorization of an addressed half-open cell. -/
theorem volume_parabolicDyadicHalfOpenCell_toReal_factor  :
    (volume (parabolicDyadicHalfOpenCell index)).toReal =
      parabolicDyadicTimeWidth n * (parabolicDyadicVelocityWidth n) ^ d := by
  rw [volume_timeVelocity_eq_prod, parabolicDyadicHalfOpenCell, Measure.prod_prod,
    ENNReal.toReal_mul, volume_parabolicDyadicTimeCell_toReal,
    volume_parabolicDyadicVelocityCell_toReal]

/-- The real volume of an addressed half-open cell has the source's exact
parabolic normalization. -/
theorem volume_parabolicDyadicHalfOpenCell_toReal  :
    (volume (parabolicDyadicHalfOpenCell index)).toReal =
      (2 : ℝ) ^ d / (2 : ℝ) ^ ((d + 2) * n) := by
  rw [volume_parabolicDyadicHalfOpenCell_toReal_factor]
  unfold parabolicDyadicTimeWidth parabolicDyadicVelocityWidth
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring

/-- Two times in one addressed cell differ by at most its exact time width. -/
theorem abs_sub_le_parabolicDyadicTimeWidth
    {time time' : ℝ} {velocity velocity' : PDE.Vec d}
    (h : (time, velocity) ∈ parabolicDyadicHalfOpenCell index)
    (h' : (time', velocity') ∈ parabolicDyadicHalfOpenCell index) :
    |time - time'| ≤ parabolicDyadicTimeWidth n := by
  rw [mem_parabolicDyadicHalfOpenCell_iff] at h h'
  rw [abs_sub_le_iff]
  rw [← parabolicDyadicTimeCell_width index]
  constructor <;> linarith [h.1.1, h.1.2, h'.1.1, h'.1.2]

/-- Two velocity coordinates in one addressed cell differ by at most its exact
coordinate width. -/
theorem abs_sub_le_parabolicDyadicVelocityWidth  (coordinate : Fin d)
    {time time' : ℝ} {velocity velocity' : PDE.Vec d}
    (h : (time, velocity) ∈ parabolicDyadicHalfOpenCell index)
    (h' : (time', velocity') ∈ parabolicDyadicHalfOpenCell index) :
    |velocity coordinate - velocity' coordinate| ≤ parabolicDyadicVelocityWidth n := by
  rw [mem_parabolicDyadicHalfOpenCell_iff] at h h'
  rw [mem_parabolicDyadicVelocityCell_iff] at h h'
  rw [abs_sub_le_iff]
  rw [← parabolicDyadicVelocityCell_width index coordinate]
  constructor <;> linarith [h.2 coordinate |>.1, h.2 coordinate |>.2,
    h'.2 coordinate |>.1, h'.2 coordinate |>.2]

end

end HypoellipticAleksandrov.Parabolic
