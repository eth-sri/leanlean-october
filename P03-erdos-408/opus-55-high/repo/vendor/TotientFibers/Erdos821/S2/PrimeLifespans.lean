module

public import Erdos821.S2.LifespanAlgebra
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Abel

/-! The active-prime part of the exact lifespan expansion. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

/-- Independent-residue expectation for one prime and prescribed active visits. -/
def onePrimeExpectation (p n : ℕ) [NeZero p] (eta : Fin n → ℝ)
    (h : Fin n → ZMod p) (active : Finset (Fin n)) : ℝ :=
  (p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i : Fin n,
    if i ∈ active then (if r + h i = 0 then 1 else 0)
    else 1 - eta i * if r + h i = 0 then 1 else 0

/-- Any active visit pins the residue. Compatibility of all other active
 offsets is retained explicitly. No later hit pays a reciprocal prime. -/
theorem onePrimeExpectation_active (p n : ℕ) [NeZero p] (eta : Fin n → ℝ)
    (h : Fin n → ZMod p) (active : Finset (Fin n)) (a : Fin n) (ha : a ∈ active) :
    onePrimeExpectation p n eta h active = (p : ℝ)⁻¹ *
      (if ∀ i ∈ active, h i = h a then
        ∏ i ∈ Finset.univ.filter (fun i => i ∉ active),
          (1 - eta i * if h i = h a then 1 else 0)
      else 0) := by
  have hh (i : Fin n) : -h a + h i = 0 ↔ h i = h a := by
    constructor
    · grind
    · simp_all
  unfold onePrimeExpectation
  congr 1
  rw [Finset.sum_eq_single (-h a)]
  · simp only [hh]
    by_cases hc : ∀ i ∈ active, h i = h a
    · rw [ite_eq_left hc]
      calc
        _ = ∏ i : Fin n, if i ∉ active then (1 - eta i * if h i = h a then 1 else 0) else 1 := by
          simp_all
        _ = _ := (Finset.prod_filter _ _).symm
    · rw [ite_eq_right hc]
      obtain ⟨i, hi, he⟩ : ∃ i ∈ active, h i ≠ h a := by
        simp_all
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp_all
  · intro r _ hr
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    grind
  simp

/-- Split the unmarked product into a prefix, gaps within the active span,
and a suffix. This is the interval decomposition used by the memory identity. -/
theorem unmarked_product_split {R : Type*} [CommMonoid R] (n : ℕ)
    (f : Fin n → R) (active : Finset (Fin n)) (a z : Fin n)
    (ha : a ∈ active) (hz : z ∈ active)
    (hfirst : ∀ i ∈ active, a ≤ i) (hlast : ∀ i ∈ active, i ≤ z) :
    (∏ i ∈ Finset.univ.filter (fun i => i ∉ active), f i) =
      (∏ i ∈ Finset.univ.filter (fun i => i < a), f i) *
      (∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < z ∧ i ∉ active), f i) *
      (∏ i ∈ Finset.univ.filter (fun i => z < i), f i) := by
  simp only [Finset.prod_filter, ← Finset.prod_mul_distrib]
  grind

/-- Prefix/suffix ghost endpoints are charged only at their own visits.
The middle product records pending hits between the first and last activity. -/
theorem active_lifespan_expansion (n : ℕ) (f : Fin n → ℝ)
    (active : Finset (Fin n)) (a z : Fin n) (ha : a ∈ active) (hz : z ∈ active)
    (hfirst : ∀ i ∈ active, a ≤ i) (hlast : ∀ i ∈ active, i ≤ z) :
    (∏ i ∈ Finset.univ.filter (fun i => i ∉ active), (1 - f i)) =
      (1 - ∑ j ∈ Finset.univ.filter (fun j => j < a),
        f j * ∏ i ∈ Finset.univ.filter (fun i => j < i ∧ i < a), (1 - f i)) *
      (∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < z ∧ i ∉ active), (1 - f i)) *
      (1 - ∑ j ∈ Finset.univ.filter (fun j => z < j),
        f j * ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < j), (1 - f i)) := by
  rw [unmarked_product_split n (fun i => 1 - f i) active a z ha hz hfirst hlast]
  have hp : (∏ i ∈ Finset.univ.filter (fun i => i < a), (1 - f i)) =
      1 - ∑ j ∈ Finset.univ.filter (fun j => j < a),
        f j * ∏ i ∈ Finset.univ.filter (fun i => j < i ∧ i < a), (1 - f i) := by
    simpa only [Finset.filter_filter, and_comm] using
      Erdos821.S2.prefix_ghost_ordered (Finset.univ.filter (fun i => i < a)) f
  have hs : (∏ i ∈ Finset.univ.filter (fun i => z < i), (1 - f i)) =
      1 - ∑ j ∈ Finset.univ.filter (fun j => z < j),
        f j * ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < j), (1 - f i) := by
    simpa only [Finset.filter_filter] using
      Finset.prod_one_sub_ordered (Finset.univ.filter (fun i => z < i)) f
  simp_all


end Erdos821.S2Core
