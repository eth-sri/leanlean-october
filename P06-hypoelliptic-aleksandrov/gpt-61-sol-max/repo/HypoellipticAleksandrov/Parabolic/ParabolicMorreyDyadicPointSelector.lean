module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedGeometry

/-!
# Point-indexed parabolic dyadic selectors

This module selects, at every finite generation, the unique half-open dyadic
cell containing a supplied point of the exact carrier `(0, 1] × (-1, 1]^d`.
It then records literal membership in the corresponding closed forward boxes.
The carrier is pointwise and half-open: this module makes no projection-limit,
representative, or almost-everywhere open-cell substitution assertion.
-/

@[expose] public section




namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Every half-open dyadic cell is contained pointwise in its literal closed
forward box. -/
theorem parabolicDyadicHalfOpenCell_subset_closedForwardBox
    {d n : Nat} (index : ParabolicDyadicIndex d n) :
    parabolicDyadicHalfOpenCell index ⊆
      parabolicClosedBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := by
  rintro ⟨time, velocity⟩ hcell
  rw [mem_parabolicDyadicHalfOpenCell_iff,
    mem_parabolicDyadicTimeCell_iff,
    mem_parabolicDyadicVelocityCell_iff] at hcell
  rw [mem_parabolicClosedBox_iff, mem_velocityClosedCube_iff]
  refine ⟨hcell.1.1.le, ?_, fun coordinate => ?_⟩
  · change time ≤
      (parabolicDyadicTimeCode n index : Real) / (4 : Real) ^ n +
        1 * (((2 : Real) ^ n)⁻¹) ^ 2
    have hradiusSq : (((2 : Real) ^ n)⁻¹) ^ 2 = ((4 : Real) ^ n)⁻¹ := by
      rw [inv_pow, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    calc
      time ≤ (parabolicDyadicTimeCode n index + 1 : Real) / (4 : Real) ^ n := hcell.1.2
      _ = (parabolicDyadicTimeCode n index : Real) / (4 : Real) ^ n +
          1 * (((2 : Real) ^ n)⁻¹) ^ 2 := by
        rw [hradiusSq]
        field_simp
  · rw [abs_le]
    have hcoordinate := hcell.2 coordinate
    change -((2 : Real) ^ n)⁻¹ ≤
        velocity coordinate -
          (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : Real) /
            (2 : Real) ^ n + ((2 : Real) ^ n)⁻¹) ∧
      velocity coordinate -
          (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : Real) /
            (2 : Real) ^ n + ((2 : Real) ^ n)⁻¹) ≤ ((2 : Real) ^ n)⁻¹
    constructor <;> field_simp at hcoordinate ⊢ <;> linarith

/-- A point of the exact reference carrier belongs to one unique half-open
dyadic cell at every fixed generation. -/
theorem existsUnique_parabolicDyadicIndex_mem_halfOpenCell
    {d n : Nat} (z : TimeVelocity d)
    (hz : z ∈ parabolicDyadicReferenceCell d) :
    ∃! index : ParabolicDyadicIndex d n,
      z ∈ parabolicDyadicHalfOpenCell index := (Exists.casesOn
  (Set.mem_iUnion.mp
    (Eq.mpr (id (congrArg (fun _a => z ∈ _a) (iUnion_parabolicDyadicHalfOpenCell_eq_reference d n))) hz))
  fun index hindex =>
  Exists.intro index
    ⟨hindex, fun index' hindex' =>
      Decidable.byContradiction fun hne =>
        False.elim (Set.disjoint_left.mp (parabolicDyadicHalfOpenCell_disjoint_of_ne hne) hindex' hindex)⟩)

variable (d : Nat) (z : TimeVelocity d) (hz : z ∈ parabolicDyadicReferenceCell d)

variable (n : Nat)

/-- The unique generation-`n` half-open dyadic index containing the supplied
reference point. -/
def parabolicDyadicIndexContaining
      :
    ParabolicDyadicIndex d n :=
  Classical.choose
    (ExistsUnique.exists
      (existsUnique_parabolicDyadicIndex_mem_halfOpenCell  z hz))

/-- The heterogeneous address obtained from the selected generation index. -/
def parabolicDyadicAddressContaining
      :
    ParabolicDyadicAddress d :=
  ⟨n, parabolicDyadicIndexContaining d z hz n⟩

/-- The selected fixed-generation index contains the supplied reference point. -/
theorem parabolicDyadicIndexContaining_mem_halfOpenCell
      :
    z ∈ parabolicDyadicHalfOpenCell
      (parabolicDyadicIndexContaining d z hz n) := Classical.choose_spec
    (ExistsUnique.exists
      (existsUnique_parabolicDyadicIndex_mem_halfOpenCell (n := n) z hz))

/-- Selected dyadic addresses are prefix-compatible across generations. -/
theorem parabolicDyadicAddressContaining_prefix

    {m n : Nat} (hmn : m ≤ n) :
    parabolicDyadicAddressPrefix
      (parabolicDyadicAddressContaining d z hz m)
      (parabolicDyadicAddressContaining d z hz n) := by
  refine ⟨hmn, ?_⟩
  have hselected := parabolicDyadicIndexContaining_mem_halfOpenCell d z hz n
  have hprefix : parabolicDyadicAddressPrefix
      ⟨m, parabolicDyadicTruncate hmn
        (parabolicDyadicIndexContaining d z hz n)⟩
      ⟨n, parabolicDyadicIndexContaining d z hz n⟩ :=
    ⟨hmn, rfl⟩
  have htruncated  :=
    parabolicDyadicHalfOpenCell_subset_of_addressPrefix hprefix hselected
  exact ((existsUnique_parabolicDyadicIndex_mem_halfOpenCell (n := m) z hz).unique
    (parabolicDyadicIndexContaining_mem_halfOpenCell d z hz m) htruncated).symm

/-- The supplied point belongs to every selected literal closed forward box. -/
theorem parabolicDyadicAddressContaining_mem_closedForwardBox
     (n : Nat) : type_of% (parabolicDyadicHalfOpenCell_subset_closedForwardBox _
    (parabolicDyadicIndexContaining_mem_halfOpenCell d z hz n)) :=
  parabolicDyadicHalfOpenCell_subset_closedForwardBox _
    (parabolicDyadicIndexContaining_mem_halfOpenCell d z hz n)

/-- The radii of selected dyadic source boxes shrink at the exact dyadic rate. -/
theorem tendsto_two_mul_parabolicDyadicIndexContaining_radius_atTop
     :
    Filter.Tendsto
      (fun n : Nat =>
        2 * (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d z hz n)).radius)
      Filter.atTop (nhds 0) := (id tendsto_two_mul_parabolicDyadicSourceBox_radius_atTop)

end

end HypoellipticAleksandrov.Parabolic
