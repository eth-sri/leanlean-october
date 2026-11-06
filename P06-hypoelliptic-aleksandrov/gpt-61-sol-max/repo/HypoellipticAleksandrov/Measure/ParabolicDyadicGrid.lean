module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring



/-!
# Finite parabolic dyadic address grids

This file records the finite address tree for the reference rectangle
`(0, 1] × (-1, 1]^d`.  A refinement quarters time and bisects every velocity
coordinate.  Half-open cells are the exact finite partition objects; open
cells are recorded separately for later interior arguments.
-/

@[expose] public section

open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- One simultaneous parabolic refinement choice: four time children and two
velocity children in each coordinate. -/
abbrev ParabolicDyadicChild (d : ℕ) : Type :=
  Fin 4 × (Fin d → Fin 2)

/-- A generation-`n` parabolic cell is addressed by its `n` successive
refinement choices. -/
abbrev ParabolicDyadicIndex (d n : ℕ) : Type :=
  Fin n → ParabolicDyadicChild d

variable {d n : ℕ}

/-- Remove the final refinement choice from an address. -/
def parabolicDyadicParent  :
    ParabolicDyadicIndex d (n + 1) → ParabolicDyadicIndex d n :=
  fun index j => index j.castSucc

variable (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d)

/-- Append one simultaneous refinement choice to an address. -/
def parabolicDyadicChildIndex   : ParabolicDyadicIndex d (n + 1) :=
  Fin.lastCases child index

@[simp] theorem parabolicDyadicParent_childIndex
     :
    parabolicDyadicParent (parabolicDyadicChildIndex index child) = index := by
  funext j
  simp [parabolicDyadicParent, parabolicDyadicChildIndex]

@[simp] theorem parabolicDyadicChildIndex_last
     :
    parabolicDyadicChildIndex index child (Fin.last n) = child := by
  simp [parabolicDyadicChildIndex]

/-- Decomposing an address into its prefix and final choice reconstructs it. -/
@[simp] theorem parabolicDyadicChildIndex_parent_last
    (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicChildIndex (parabolicDyadicParent index) (index (Fin.last n)) = index := by
  funext j
  obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
  · simp [parabolicDyadicParent, parabolicDyadicChildIndex]
  · simp

variable (d : ℕ)

/-- The source branching number is four time choices times two choices in each
velocity coordinate. -/
theorem card_parabolicDyadicChild  :
    Fintype.card (ParabolicDyadicChild d) = 4 * 2 ^ d := by
  simp [ParabolicDyadicChild]

/-- The source branching number in the paper's normalized power-of-two form. -/
theorem card_parabolicDyadicChild_eq_two_pow  :
    Fintype.card (ParabolicDyadicChild d) = 2 ^ (d + 2) := by
  simp_all [ParabolicDyadicChild, card_parabolicDyadicChild] <;> ring

variable (d n : ℕ)

/-- The generation-`n` address set has the expected branching cardinality. -/
theorem card_parabolicDyadicIndex  :
    Fintype.card (ParabolicDyadicIndex d n) = (4 * 2 ^ d) ^ n := by
  simp [ParabolicDyadicIndex, ParabolicDyadicChild]

/-- The generation cardinality in the paper's normalized power-of-two form. -/
theorem card_parabolicDyadicIndex_eq_two_pow  :
    Fintype.card (ParabolicDyadicIndex d n) = 2 ^ ((d + 2) * n) := (Trans.trans
  (Trans.trans (card_parabolicDyadicIndex d n)
    (congrArg (fun cardinality => cardinality ^ n)
      (Eq.trans (Eq.symm (card_parabolicDyadicChild d)) (card_parabolicDyadicChild_eq_two_pow d))))
  (Eq.symm (pow_mul 2 (d + 2) n)))

variable {d : ℕ}

/-- Read the base-four time address from a refinement word. -/
def parabolicDyadicTimeCode  : (n : ℕ) → ParabolicDyadicIndex d n → ℕ
  | 0, _ => 0
  | n + 1, index =>
      4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) +
        (index (Fin.last n)).1.val

/-- Read the base-two address in one fixed velocity coordinate from a refinement word. -/
def parabolicDyadicVelocityCode  : (n : ℕ) →
    ParabolicDyadicIndex d n → Fin d → ℕ
  | 0, _, _ => 0
  | n + 1, index, coordinate =>
      2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate +
        ((index (Fin.last n)).2 coordinate).val

variable {d n : ℕ}

variable (index : ParabolicDyadicIndex d n)

/-- The time code lies in the base-four range for its generation. -/
theorem parabolicDyadicTimeCode_lt_pow   :
    parabolicDyadicTimeCode n index < 4 ^ n := by
  induction n with
  | zero => simp [parabolicDyadicTimeCode]
  | succ n ih =>
      rw [parabolicDyadicTimeCode]

      calc
        4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) +
            (index (Fin.last n)).1.val <
            4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) + 4 :=
          Nat.add_lt_add_left ((index (Fin.last n)).1.isLt) _
        _ = 4 * (parabolicDyadicTimeCode n (parabolicDyadicParent index) + 1) := by omega
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 (Nat.succ_le_iff.mpr
          (ih (parabolicDyadicParent index)))
        _ = 4 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Every coordinate's velocity code lies in the base-two range for its generation. -/
theorem parabolicDyadicVelocityCode_lt_pow
     (coordinate : Fin d) :
    parabolicDyadicVelocityCode n index coordinate < 2 ^ n := by
  induction n with
  | zero => simp [parabolicDyadicVelocityCode]
  | succ n ih =>
      rw [parabolicDyadicVelocityCode]

      calc
        2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate +
            ((index (Fin.last n)).2 coordinate).val <
            2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 2 :=
          Nat.add_lt_add_left (((index (Fin.last n)).2 coordinate).isLt) _
        _ = 2 * (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 1) := by
          omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (Nat.succ_le_iff.mpr
          (ih (parabolicDyadicParent index)))
        _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

variable (child : ParabolicDyadicChild d)

/-- Appending a child appends its time digit in base four. -/
theorem parabolicDyadicTimeCode_childIndex
      :
    parabolicDyadicTimeCode (n + 1) (parabolicDyadicChildIndex index child) =
      4 * parabolicDyadicTimeCode n index + child.1.val := by
  simp [parabolicDyadicTimeCode]

/-- Appending a child appends each velocity digit in base two. -/
theorem parabolicDyadicVelocityCode_childIndex
      (coordinate : Fin d) :
    parabolicDyadicVelocityCode (n + 1) (parabolicDyadicChildIndex index child) coordinate =
      2 * parabolicDyadicVelocityCode n index coordinate + (child.2 coordinate).val := by
  simp [parabolicDyadicVelocityCode]

/-- The half-open time interval of an addressed cell in `(0, 1]`. -/
def parabolicDyadicTimeCell   : Set ℝ :=
  Ioc ((parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n)
    ((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n)

/-- The half-open velocity rectangle of an addressed cell in `(-1, 1]^d`. -/
def parabolicDyadicVelocityCell   : PDE.VelocityRegion d :=
  Set.univ.pi fun coordinate =>
    Ioc (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n)
      (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) / (2 : ℝ) ^ n)

/-- The half-open addressed cell.  These, rather than the open cells, are the
objects that later form the exact finite partition. -/
def parabolicDyadicHalfOpenCell   :
    HypoellipticAleksandrov.Parabolic.Region d :=
  parabolicDyadicTimeCell index ×ˢ parabolicDyadicVelocityCell index

/-- The open interior of an addressed cell.  It is not asserted here to form
an exact partition. -/
def parabolicDyadicOpenCell   :
    HypoellipticAleksandrov.Parabolic.Region d :=
  Ioo ((parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n)
    ((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n) ×ˢ
    Set.univ.pi (fun coordinate =>
      Ioo (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n)
        (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) / (2 : ℝ) ^ n))

variable {index : ParabolicDyadicIndex d n}

@[simp] theorem mem_parabolicDyadicTimeCell_iff
     {time : ℝ} :
    time ∈ parabolicDyadicTimeCell index ↔
      (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n < time ∧
        time ≤ (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n :=
  Iff.rfl

@[simp] theorem mem_parabolicDyadicVelocityCell_iff
     {velocity : PDE.Vec d} :
    velocity ∈ parabolicDyadicVelocityCell index ↔
      ∀ coordinate : Fin d,
        -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n <
            velocity coordinate ∧
          velocity coordinate ≤
            -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) / (2 : ℝ) ^ n := by
  simp [parabolicDyadicVelocityCell]

variable {time : ℝ} {velocity : PDE.Vec d}

@[simp] theorem mem_parabolicDyadicHalfOpenCell_iff
      :
    (time, velocity) ∈ parabolicDyadicHalfOpenCell index ↔
      time ∈ parabolicDyadicTimeCell index ∧ velocity ∈ parabolicDyadicVelocityCell index :=
  Iff.rfl

@[simp] theorem mem_parabolicDyadicOpenCell_iff
      :
    (time, velocity) ∈ parabolicDyadicOpenCell index ↔
      (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n < time ∧
        time < (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n ∧
          ∀ coordinate : Fin d,
            -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n <
                velocity coordinate ∧
              velocity coordinate <
                -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
                  (2 : ℝ) ^ n := by
  constructor
  · rintro ⟨⟨htlower, htupper⟩, hvelocity⟩
    refine ⟨htlower, htupper, fun coordinate => ?_⟩
    exact hvelocity coordinate trivial
  · rintro ⟨htlower, htupper, hvelocity⟩
    exact ⟨⟨htlower, htupper⟩, fun coordinate _ => hvelocity coordinate⟩

variable (index : ParabolicDyadicIndex d n)

/-- Half-open time intervals of addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicTimeCell
     : MeasurableSet (parabolicDyadicTimeCell index) :=
  measurableSet_Ioc

/-- Half-open velocity rectangles of addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicVelocityCell
     : MeasurableSet (parabolicDyadicVelocityCell index) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- Half-open addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicHalfOpenCell
     : MeasurableSet (parabolicDyadicHalfOpenCell index) :=
  (measurableSet_parabolicDyadicTimeCell index).prod
    (measurableSet_parabolicDyadicVelocityCell index)

/-- Open addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicOpenCell
     : MeasurableSet (parabolicDyadicOpenCell index) :=
  measurableSet_Ioo.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)

end

end HypoellipticAleksandrov.Parabolic
