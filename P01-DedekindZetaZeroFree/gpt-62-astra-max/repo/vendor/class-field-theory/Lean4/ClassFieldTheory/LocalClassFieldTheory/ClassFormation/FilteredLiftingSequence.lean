module

public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Recursive correction sequences

This file isolates the dependent-choice bookkeeping in the infinite-product
argument of the local class-field-axiom theorem.  A one-step lift in a filtered commutative
group produces compatible correction and remainder sequences.  No
cohomological input is hidden here: the existence of each one-step lift is an
explicit parameter, discharged for the normal-basis filtration in the next
file.
-/

noncomputable section

universe u

/-- Left-to-right finite products of a correction sequence. -/
def filteredCorrectionProduct {A : Type u} [Monoid A] (z : Nat → A) : Nat → A
  | 0 => 1
  | d + 1 => filteredCorrectionProduct z d * z d

section

variable {A : Type u} [Monoid A] (z : Nat → A)

/-- The empty correction product is the identity. -/
@[simp]
theorem filteredCorrectionProduct_zero :
    filteredCorrectionProduct z 0 = 1 :=
  rfl

/-- A successor correction product appends the correction at the preceding index. -/
@[simp]
theorem filteredCorrectionProduct_succ (d : Nat) :
    filteredCorrectionProduct z (d + 1) = filteredCorrectionProduct z d * z d :=
  rfl

end

/-- A remainder at depth `n + i`, carrying both its filtration condition and
the condition that must be preserved by one-step lifting. -/
structure FilteredLiftState (A : Type u) (P : Nat → A → Prop)
    (R : A → Prop) (n i : Nat) where
  /-- The current remainder at relative depth `i`. -/
  value : A
  /-- The current remainder lies in filtration level `n + i`. -/
  mem : P (n + i) value
  /-- The current remainder satisfies the condition preserved by each lifting step. -/
  stable : R value

/-- One correction step `a_i = F(b_i) a_(i+1)`. -/
structure FilteredLiftStep (A : Type u) [CommGroup A]
    (P : Nat → A → Prop) (R : A → Prop) (F : A →* A)
    (n i : Nat) (s : FilteredLiftState A P R n i) where
  /-- The correction chosen at relative depth `i`. -/
  correction : A
  /-- The correction lies in the same filtration level `n + i` as the current remainder. -/
  correction_mem : P (n + i) correction
  /-- The remainder state after removing the current correction, one level deeper. -/
  next : FilteredLiftState A P R n (i + 1)
  /-- The current remainder is the image of the correction under `F` times the next remainder. -/
  equation : s.value = F correction * next.value

/-- The recursively chosen remainder sequence. -/
noncomputable def chosenFilteredLiftStateSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) :
    (i : Nat) → FilteredLiftState A P R n i
  | 0 => initial
  | i + 1 =>
      (Classical.choice
        (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).next

variable (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop) (F : A →* A) (n : Nat)
    (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i), Nonempty (FilteredLiftStep A P R F n i s))

/-- The recursively chosen correction at depth `n + i`. -/
noncomputable def chosenFilteredLiftCorrectionSequence (i : Nat) : A :=
  (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).correction

/-- The chosen filtered-lift sequence starts at the supplied initial state. -/
@[simp]
theorem chosenFilteredLiftStateSequence_zero :
    chosenFilteredLiftStateSequence A P R F n initial step 0 = initial :=
  rfl

/-- Each successor state is the next state of the chosen lifting step. -/
@[simp]
theorem chosenFilteredLiftStateSequence_succ (i : Nat) :
    chosenFilteredLiftStateSequence A P R F n initial step (i + 1) =
      (Classical.choice
        (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).next :=
  rfl

/-- Every chosen correction lies at the advertised filtration level. -/
theorem chosenFilteredLiftCorrectionSequence_mem (i : Nat) :
    P (n + i)
      (chosenFilteredLiftCorrectionSequence A P R F n initial step i) :=
  (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).correction_mem

/-- The defining one-step recurrence for the chosen sequences. -/
theorem chosenFilteredLiftStateSequence_equation (i : Nat) :
    (chosenFilteredLiftStateSequence A P R F n initial step i).value =
      F (chosenFilteredLiftCorrectionSequence A P R F n initial step i) *
        (chosenFilteredLiftStateSequence A P R F n initial step (i + 1)).value := (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).equation

/-- The initial remainder equals the image under `F` of the first `d`
corrections, times the depth-`d` remainder. -/
theorem filteredLift_initial_eq_correctionProduct_mul_state (d : Nat) :
    initial.value =
      F (filteredCorrectionProduct
          (chosenFilteredLiftCorrectionSequence A P R F n initial step) d) *
        (chosenFilteredLiftStateSequence A P R F n initial step d).value := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [filteredCorrectionProduct_succ, map_mul]
      rw [mul_assoc, ← chosenFilteredLiftStateSequence_equation
        A P R F n initial step d]
      exact ih

end
end LocalClassFieldTheory
