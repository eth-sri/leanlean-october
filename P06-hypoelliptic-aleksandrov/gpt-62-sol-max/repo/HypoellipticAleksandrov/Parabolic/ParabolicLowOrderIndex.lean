module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Tactic

/-!
# Parabolic multi-indices of weight at most two

This module gives the canonical classification of time--velocity multi-indices
whose parabolic weight is at most two.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex

/-- Canonical shapes of parabolic multi-indices of weight at most two. -/
inductive LowOrderClass (d : ℕ) where
  | zero
  | time
  | velocity (i : Fin d)
  | velocity₂ (i j : Fin d) (hij : i ≤ j)
  deriving DecidableEq, Fintype

/-- The zero index at parabolic bound two. -/
def zeroTwo (d : ℕ) : ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.zero d 2

@[local simp] private theorem weight_zeroTwo (d : ℕ) : (zeroTwo d).1.parabolicWeight = 0 := by
  simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight, VelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]

/-- The single time derivative at parabolic bound two. -/
def timeOne (d : ℕ) : ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.timeSucc (zeroTwo d) (by simp)

/-- A single velocity derivative at parabolic bound two. -/
def velocityOne {d : ℕ} (i : Fin d) :
    ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.velocitySucc (zeroTwo d) i (by simp)

/-- Two successive velocity derivatives at parabolic bound two, first in
coordinate `i` and then in coordinate `j`. -/
def velocityTwo {d : ℕ} (i j : Fin d) :
    ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.velocitySucc (velocityOne i) j (by
    simp only [velocityOne, parabolicWeight_velocitySucc, weight_zeroTwo]; decide)

/-- Interpret a canonical low-order shape as its bounded multi-index. -/
def LowOrderClass.toIndex {d : ℕ} :
    LowOrderClass d → ParabolicDerivativeIndex d 2
  | .zero => zeroTwo d
  | .time => timeOne d
  | .velocity i => velocityOne i
  | .velocity₂ i j _ => velocityTwo i j

@[simp] theorem coe_zeroTwo (d : ℕ) :
    (zeroTwo d).1 = (0 : TimeVelocityMultiIndex d) :=
  rfl

@[simp] theorem coe_timeOne (d : ℕ) :
    (timeOne d).1 = TimeVelocityMultiIndex.ofTimeVelocity 1 0 :=
  rfl

@[simp] theorem coe_velocityOne {d : ℕ} (i : Fin d) :
    (velocityOne i).1 =
      TimeVelocityMultiIndex.ofTimeVelocity 0 (Pi.single i 1) :=
  rfl

@[simp] theorem coe_velocityTwo {d : ℕ} (i j : Fin d) :
    (velocityTwo i j).1 =
      TimeVelocityMultiIndex.ofTimeVelocity 0
        (Function.update (Pi.single i 1) j
          ((Pi.single i 1 : Fin d → ℕ) j + 1)) :=
  rfl

@[simp] theorem LowOrderClass.toIndex_zero (d : ℕ) :
    (LowOrderClass.zero : LowOrderClass d).toIndex = zeroTwo d :=
  rfl

@[simp] theorem LowOrderClass.toIndex_time (d : ℕ) :
    (LowOrderClass.time : LowOrderClass d).toIndex = timeOne d :=
  rfl

section
variable {d : ℕ}

@[simp] theorem LowOrderClass.toIndex_velocity (i : Fin d) :
    (LowOrderClass.velocity i).toIndex = velocityOne i :=
  rfl

@[simp] theorem LowOrderClass.toIndex_velocity₂ (i j : Fin d) (hij : i ≤ j) :
    (LowOrderClass.velocity₂ i j hij).toIndex = velocityTwo i j :=
  rfl

section
variable (alpha : Fin d → ℕ)
include alpha

private noncomputable def velocityMultiset : Multiset (Fin d) :=
  Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm alpha)

private theorem count_velocityMultiset (i : Fin d) :
    (velocityMultiset alpha).count i = alpha i := by
  simp [velocityMultiset]

private theorem card_velocityMultiset :
    (velocityMultiset alpha).card = VelocityMultiIndex.order alpha := by
  classical
  simp [velocityMultiset, VelocityMultiIndex.order, Finsupp.card_toMultiset,
    Finsupp.sum_fintype]

end

private theorem count_singleton_eq_piSingle (i a : Fin d) :
    ({i} : Multiset (Fin d)).count a =
      (Pi.single i 1 : Fin d → ℕ) a := by
  by_cases h : a = i <;> simp [Pi.single_apply, h]

private theorem count_pair_eq_update (i j a : Fin d) :
    ({i, j} : Multiset (Fin d)).count a =
      Function.update (Pi.single i 1 : Fin d → ℕ) j
        ((Pi.single i 1 : Fin d → ℕ) j + 1) a := by
  by_cases haj : a = j
  · subst a
    by_cases hji : j = i <;> simp [Pi.single_apply, hji]
  · by_cases hai : a = i
    · subst a
      simp [haj]
    · simp [Pi.single_apply, haj, hai]

end

@[local simp] private theorem velocityMultiset_zero {d : ℕ} :
    velocityMultiset (0 : VelocityMultiIndex d) = 0 := by
  ext i
  simp [count_velocityMultiset]

@[local simp] private theorem velocityMultiset_one {d : ℕ} (i : Fin d) :
    velocityMultiset (Pi.single i 1) = {i} := by
  ext j
  rw [count_velocityMultiset, count_singleton_eq_piSingle]

@[local simp] private theorem velocityMultiset_two {d : ℕ} (i j : Fin d) :
    velocityMultiset (velocityTwo i j).1.velocity = {i, j} := by
  ext a
  rw [count_velocityMultiset, count_pair_eq_update]
  rfl

private theorem velocityTwo_class_eq_of_pair_eq {d : ℕ} {i j k l : Fin d}
    (hij : i ≤ j) (hkl : k ≤ l)
    (hpair : ({i, j} : Multiset (Fin d)) = {k, l}) :
    LowOrderClass.velocity₂ i j hij = LowOrderClass.velocity₂ k l hkl := by
  have hp : List.Perm [i, j] [k, l] := Multiset.coe_eq_coe.mp hpair
  have he := hp.eq_of_pairwise' (r := (· ≤ ·)) (by simpa using hij) (by simpa using hkl)
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rfl

/-- Canonical low-order shapes classify bounded indices of weight at most
 two bijectively. -/
theorem LowOrderClass.toIndex_bijective (d : ℕ) :
    Function.Bijective (@LowOrderClass.toIndex d) := by
  classical
  constructor
  · intro s t h
    have ht := congrArg (fun b : ParabolicDerivativeIndex d 2 => b.1.timeOrder) h
    have hw := congrArg (fun b : ParabolicDerivativeIndex d 2 => b.1.parabolicWeight) h
    have hm := congrArg (fun b : ParabolicDerivativeIndex d 2 => velocityMultiset b.1.velocity) h
    cases s <;> cases t <;> first
      | rfl
      | change 0 = 1 at ht; contradiction
      | change 1 = 0 at ht; contradiction
      | solve | simp only [toIndex_zero, toIndex_velocity, toIndex_velocity₂,
          velocityTwo, velocityOne, parabolicWeight_velocitySucc, weight_zeroTwo] at hw; omega
      | simpa using hm
      | exact velocityTwo_class_eq_of_pair_eq _ _ (by simpa only [toIndex_velocity₂, velocityMultiset_two] using hm)
  · intro beta
    let m := velocityMultiset beta.1.velocity
    have hb : 2 * beta.1.timeOrder + m.card ≤ 2 := by
      simpa [m, card_velocityMultiset, TimeVelocityMultiIndex.parabolicWeight,
        VelocityMultiIndex.parabolicWeight] using beta.2
    have index_eq (s : LowOrderClass d) (hq : s.toIndex.1.timeOrder = beta.1.timeOrder)
        (hm : velocityMultiset s.toIndex.1.velocity = m) : s.toIndex = beta := by
      have hv : s.toIndex.1.velocity = beta.1.velocity := by
        funext i
        simpa [m, count_velocityMultiset] using congrArg (fun a : Multiset (Fin d) => a.count i) hm
      apply Subtype.ext
      simpa only [TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity] using
        (congrArg₂ TimeVelocityMultiIndex.ofTimeVelocity hq hv)
    obtain hq | hq : beta.1.timeOrder = 0 ∨ beta.1.timeOrder = 1 := by omega
    · have hc : m.card ≤ 2 := by omega
      interval_cases hcard : m.card
      · refine ⟨.zero, index_eq .zero hq.symm ?_⟩
        exact (velocityMultiset_zero (d := d)).trans (Multiset.card_eq_zero.mp hcard).symm
      · obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hcard
        exact ⟨.velocity i, index_eq (.velocity i) hq.symm ((velocityMultiset_one i).trans hi.symm)⟩
      · obtain ⟨i, j, hij⟩ := Multiset.card_eq_two.mp hcard
        rcases le_total i j with h | h
        · exact ⟨.velocity₂ i j h, index_eq _ hq.symm ((velocityMultiset_two i j).trans hij.symm)⟩
        · rw [Multiset.pair_comm] at hij
          exact ⟨.velocity₂ j i h, index_eq _ hq.symm ((velocityMultiset_two j i).trans hij.symm)⟩
    · exact ⟨.time, index_eq .time hq.symm
        ((velocityMultiset_zero (d := d)).trans (Multiset.card_eq_zero.mp (by omega)).symm)⟩

/-- The canonical equivalence between bounded weight-two indices and their
four low-order shapes. -/
noncomputable def equivLowOrderClass (d : ℕ) :
    ParabolicDerivativeIndex d 2 ≃ LowOrderClass d :=
  (Equiv.ofBijective (@LowOrderClass.toIndex d)
    (LowOrderClass.toIndex_bijective d)).symm

@[simp] theorem equivLowOrderClass_symm_apply
    {d : ℕ} (s : LowOrderClass d) :
    (equivLowOrderClass d).symm s = s.toIndex :=
  rfl

@[simp] theorem LowOrderClass.toIndex_equivLowOrderClass_apply
    {d : ℕ} (beta : ParabolicDerivativeIndex d 2) :
    (equivLowOrderClass d beta).toIndex = beta :=
  (equivLowOrderClass d).symm_apply_apply beta

end HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
