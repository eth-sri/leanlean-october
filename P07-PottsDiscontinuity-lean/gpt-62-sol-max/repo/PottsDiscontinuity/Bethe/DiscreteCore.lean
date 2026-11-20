module

public import Mathlib
public import PottsDiscontinuity.Bethe.Theta

/-!
# Discrete Bethe map and its symmetric domain

This file formalizes the finite dimensional definitions in Section 2.2 of
arXiv:1611.09877v2.  The map is defined on all vectors; `S_n` records the
strictly ordered, symmetric configurations used by the source.
-/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

section

variable (n : ℕ)

/-- The centered quantum number `I_j = j - (n+1)/2`, with Lean's `Fin n`
index corresponding to the source's one-based index `j+1`. -/
noncomputable def discreteBetheIndex (j : Fin n) : ℝ :=
  (j.val : ℝ) + 1 - ((n : ℝ) + 1) / 2

/-- Reflection of the source index `j` to `n+1-j`. -/
theorem discreteBetheIndex_rev (j : Fin n) :
    discreteBetheIndex n (Fin.rev j) = -discreteBetheIndex n j := by
  unfold discreteBetheIndex
  have hv : (Fin.rev j).val + j.val + 1 = n := by
    grind
  have hv' : ((Fin.rev j).val : ℝ) + (j.val : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hv
  linarith

/-- The symmetric subspace `R^n_sym = {q : q_(n+1-j) = -q_j}`. -/
def R_n_sym : Submodule ℝ (Fin n → ℝ) where
  carrier := {p | ∀ j, p (Fin.rev j) = -p j}
  zero_mem' := by
    intro j
    simp
  add_mem' := by
    intro p q hp hq j
    simp only [Pi.add_apply, hp j, hq j]
    ring
  smul_mem' := by
    intro c p hp j
    simp_all

/-- The ordered symmetric configuration space `S_n`. -/
def S_n : Set (Fin n → ℝ) :=
  {p | (∀ j, -Real.pi < p j ∧ p j < Real.pi) ∧ StrictMono p ∧ p ∈ R_n_sym n}

end

section

variable (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ)

/-- The Bethe fixed point map, defined on every vector in `R^n`. -/
noncomputable def discreteBetheMap : Fin n → ℝ :=
  fun j => 2 * Real.pi * discreteBetheIndex n j / (N : ℝ) -
    (∑ k : Fin n, theta Δ (p j) (p k)) / (N : ℝ)

/-- The discrete Bethe equations with the source's centered choice of `I_j`. -/
def DiscreteBetheEquation : Prop :=
  ∀ j, (N : ℝ) * p j =
    2 * Real.pi * discreteBetheIndex n j - ∑ k : Fin n, theta Δ (p j) (p k)

end

/-- The equation `T(p)=p` is exactly (BE_Δ), provided `N` is positive. -/
theorem discreteBetheMap_fixed_iff_equation {Δ : ℝ} {N n : ℕ}
    (hN : 0 < N) (p : Fin n → ℝ) :
    discreteBetheMap Δ N n p = p ↔ DiscreteBetheEquation Δ N n p := by
  have hNc : (N : ℝ) ≠ 0 := by positivity
  rw [funext_iff]
  unfold DiscreteBetheEquation
  refine forall_congr' fun j => ?_
  unfold discreteBetheMap
  constructor <;> intro h <;> field_simp [hNc] at h ⊢ <;> linarith

/-- The inverse-parameter version of the Bethe map, defined using `thetaInv`.
At `ε=0` this is the extension of the source's map to `Δ=-∞`. -/
noncomputable def discreteBetheMapInv (ε : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun j => 2 * Real.pi * discreteBetheIndex n j / (N : ℝ) -
    (∑ k : Fin n, thetaInv ε (p j) (p k)) / (N : ℝ)

/-- The finite-`Δ` map preserves the symmetric subspace, as required for the
implicit-function argument in the source. -/
theorem discreteBetheMap_mem_R_n_sym (Δ : ℝ) (N n : ℕ)
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) :
    discreteBetheMap Δ N n p ∈ R_n_sym n := by
  change ∀ j, discreteBetheMap Δ N n p (Fin.rev j) = -discreteBetheMap Δ N n p j
  change ∀ j, p (Fin.rev j) = -p j at hp
  intro j
  have hsum :
      (∑ k : Fin n, theta Δ (p (Fin.rev j)) (p k)) =
        -(∑ k : Fin n, theta Δ (p j) (p k)) := by
    rw [hp j, ← Equiv.sum_comp Fin.revPerm (fun k => theta Δ (-p j) (p k))]
    simp only [Fin.revPerm_apply, hp, theta_neg_neg, Finset.sum_neg_distrib]
  rw [discreteBetheMap, discreteBetheMap, discreteBetheIndex_rev, hsum]
  ring

/-- On `Δ<-1`, the inverse-parameter map at `ε=1/Δ` agrees with the source's
finite-parameter map. -/
theorem discreteBetheMap_eq_inv {Δ : ℝ} (hΔ : Δ < -1) (N n : ℕ)
    (p : Fin n → ℝ) :
    discreteBetheMap Δ N n p = discreteBetheMapInv (1 / Δ) N n p := by
  funext j
  simp only [discreteBetheMap, discreteBetheMapInv]
  simp_rw [theta_eq_thetaInv hΔ]

end PottsDiscontinuity.Bethe
