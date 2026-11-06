/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneFiniteBountiful

/-! # Executable grade-one row queries

The executable data contains natural-number source ranks for every full
controller and triples recording the block-bottom implications at every nested
row. The interpretation of label zero is bottom, not ordinal zero. All other
label codes are proper natural ordinals. The checker uses only finite maxima,
natural comparisons, and Boolean flags; no ordinal comparison is executed.

The semantic adapter below requires exact source-order, source-bottom, and
nested-block identifications. A controller enumeration must be exhaustive.
Rejecting the resulting complete query is distinct from rejecting a proposed
witness. This file does not manufacture a consistent scheme from numerical data.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting.Executable

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-- Zero encodes bottom; positive codes encode proper natural ordinals. -/
noncomputable def value (n : ℕ) : ExtOrd := if n = 0 then ⊥ else ofOrd n

@[simp] theorem value_zero : value 0 = ⊥ := rfl

@[simp] theorem value_one : value 1 = ofOrd 1 := by simp [value]

@[simp] theorem value_eq_bot {n : ℕ} : value n = ⊥ ↔ n = 0 := by
  by_cases hn : n = 0 <;> simp [value, hn]

@[simp] theorem value_le {a b : ℕ} : value a ≤ value b ↔ a ≤ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb, ha, le_bot_iff]
  simp only [value, ite_eq_right ha, ite_eq_right hb, ofOrd_le_ofOrd]
  exact_mod_cast Iff.rfl

theorem value_mono : Monotone value := fun _ _ h => value_le.mpr h

@[simp] theorem value_lt {a b : ℕ} : value a < value b ↔ a < b := by
  simp only [lt_iff_le_not_ge, value_le]

@[simp] theorem value_inj {a b : ℕ} : value a = value b ↔ a = b := by
  simp only [le_antisymm_iff, value_le]

@[simp] theorem value_min (a b : ℕ) : value (min a b) = min (value a) (value b) :=
  value_mono.map_min

@[simp] theorem value_max (a b : ℕ) : value (max a b) = max (value a) (value b) :=
  value_mono.map_max

section Propagation

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Propagation

/-- Fixed finite data. A triple (c,d,e) records the implication at owner c
from a bottom capped reading at d to one at e. Cells remain distinct. -/
structure Data (Y C : Type*) where
  source : C → Y → ℕ
  blocks : Finset (Y × Y × Y)

namespace Data

variable {Y C X B : Type*} [Fintype Y] [Fintype C] [Fintype X] [Fintype B]
  [DecidableEq X] [DecidableEq Y]

/-- All nested-row bottom implications, including the actual owner cap. -/
def Blocks (T : Data Y C) (r : Y → ℕ) : Prop :=
  ∀ t ∈ T.blocks, (r t.2.1 = 0 ∨ r t.1 = 0) → (r t.2.2 = 0 ∨ r t.1 = 0)

/-- Lawfulness test: block implications and an exhaustive full-row order query. -/
def Respect (T : Data Y C) (r : Y → ℕ) : Prop :=
  T.Blocks r ∧ ∃ c, (∀ d e, T.source c d ≤ T.source c e → r d ≤ r e) ∧
    (∀ d, T.source c d = 0 → r d = 0)

/-- True flags denote bottom; the numerical seed one is the least positive label. -/
def seed (z : Y → Bool) (d : Y) : ℕ := if z d then 0 else 1

/-- Exact output query, not a test of a preselected witness. -/
def Lift (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) : Prop :=
  (γ = 0 ∧ ∃ c, ∃ z : Y → Bool,
    Propagation.Check (T.source c) embed p (seed z) 1 ∧ T.Blocks (seed z)) ∨
  (γ ≠ 0 ∧ ∃ c, Propagation.Check (T.source c) embed p q γ)

instance (T : Data Y C) (r : Y → ℕ) : Decidable (T.Blocks r) :=
  inferInstanceAs (Decidable (∀ t ∈ T.blocks, _))

instance (T : Data Y C) (r : Y → ℕ) : Decidable (T.Respect r) :=
  inferInstanceAs (Decidable (T.Blocks r ∧ ∃ _, _))

instance (E : Y → ℕ) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    Decidable (Propagation.Check E embed p q γ) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

instance (T : Data Y C) (embed : X → Y) (p : X → ℕ) (q : Y → ℕ) (γ : ℕ) :
    Decidable (T.Lift embed p q γ) :=
  inferInstanceAs (Decidable ((_ : Prop) ∨ (_ : Prop)))

/-- Universal bounded test; no ordinal-valued variables occur. -/
def Universal (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) : Prop :=
  ∀ (p : X → Fin (N + 1)) (q : Y → Fin (N + 1)) (γ : Fin (N + 1)),
    P.Respect (fun x => (p x).val) → T.Respect (fun y => (q y).val) →
    (∀ x, min (q (embed x)).val γ.val = min (p x).val γ.val) →
    T.Lift embed (fun x => (p x).val) (fun y => (q y).val) γ.val

instance (P : Data X B) (T : Data Y C) (embed : X → Y) (N : ℕ) :
    Decidable (Universal P T embed N) :=
  inferInstanceAs (Decidable (∀ (_ : X → Fin (N + 1)) (_ : Y → Fin (N + 1))
    (_ : Fin (N + 1)), _))

end Data

section Semantics

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ} {C B : Type*}

namespace Realizes

variable {T : Data (D.below BJ) C}

variable {X : Type*} [Fintype X] [Fintype (D.below BJ)]

variable [Fintype C]

end Realizes

variable [Fintype B] [Fintype C] [Fintype (D.below CI)] [Fintype (D.below BJ)]
  [DecidableEq (D.below CI)] [DecidableEq (D.below BJ)]

end Semantics

end VaughtConjecture.Knight.FullRowLifting.Executable
