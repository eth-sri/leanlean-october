module

public import PottsDiscontinuity.BetheAnsatz.Regular
public import PottsDiscontinuity.BetheAnsatz.ZeroRootAlgebra
public import PottsDiscontinuity.BetheAnsatz.ZeroRootPhases

/-!
# The two constant words in the zero-root limit

This is the corrected T₀ calculation. The boundary contribution uses
`L(z) * (z^(-N)-1)`, whose limit is `+c²N` as proved in `BoundaryLimit`.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- A cyclic predecessor followed by rotation selects the original coordinate,
except at the seam where it is smaller by N. -/
theorem cyclicPredecessor_rotate {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ)
    (k : Fin (n + 1)) :
    cyclicPredecessorPositions N x (finRotate (n + 1) k) =
      x k - if k = Fin.last n then (N : ℤ) else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k <;> simp

section
variable (t : ℝ)
/-- Negative integer phases are inverse natural powers. -/
theorem positionPhase_neg_nat (d : ℕ) :
    positionPhase t (-(d : ℤ)) = (z t ^ d)⁻¹ := by
  have hmul : positionPhase t (-(d : ℤ)) * z t ^ d = 1 := by
    rw [← positionPhase_nat, ← positionPhase_add]
    simp [positionPhase]
  grind

/-- Shifting an integer coordinate down by N contributes the inverse Nth phase. -/
theorem positionPhase_sub_nat (y : ℤ) (N : ℕ) :
    positionPhase t (y - (N : ℤ)) = positionPhase t y * (z t ^ N)⁻¹ := by
  rw [show y - (N : ℤ) = y + (-(N : ℤ)) by ring, positionPhase_add,
    positionPhase_neg_nat]
end

section
variable {n : ℕ} (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ) (f : ℝ → ℂ)
/-- Product over the non-root indices is unchanged by the perturbation. -/
theorem prod_perturbed_erase_eq  :
    (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (perturbedMomenta p l t j)) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) :=
  Finset.prod_congr rfl fun j hj => by rw [perturbedMomenta_of_ne p l j t (mem_erase.mp hj).1]

/-- Product of a one-root perturbed sequence is its root factor times the fixed remainder. -/
theorem prod_perturbed_factor  :
    (∏ j, f (perturbedMomenta p l t j)) =
      f (p l + t) * ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) := by
  rw [← Finset.mul_prod_erase _ _ (mem_univ l)]
  simp [prod_perturbed_erase_eq]
end

section
variable {N n : ℕ}
/-- The fixed-amplitude contribution of the two constant words at perturbation t. -/
noncomputable def constantWordSumPerturbed (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), amplitude (anisotropy c) p σ *
    (wordCoefficient c (perturbedMomenta p l t) σ (fun _ => false) *
        wordPhase (N := N) x (perturbedMomenta p l t) σ (fun _ => false) +
     wordCoefficient c (perturbedMomenta p l t) σ (fun _ => true) *
        wordPhase (N := N) x (perturbedMomenta p l t) σ (fun _ => true))

/-- Reindexing identity for the L constant word with its one-root phase. -/
theorem toroidal_zero_root_L_phase {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (x : Fin (n + 1) → ℤ) (l : Fin (n + 1)) (t : ℝ) :
    (∑ σ, amplitude Δ p σ * positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
        planeWave p σ (cyclicPredecessorPositions N x)) =
      ∑ σ, amplitude Δ p σ * positionPhase t
        (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l)) *
        planeWave p σ x := by
  let f := fun σ =>
    positionPhase t (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l))
  have h := toroidal_change_of_variables hΔ p hBE x f
  aesop

/-- Exact T₀ decomposition before taking the limit. -/
theorem constantWordSumPerturbed_eq {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (t : ℝ) :
    constantWordSumPerturbed (N := N) c x p l t =
      (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
      ∑ σ, amplitude (anisotropy c) p σ *
        positionPhase t (x (σ.symm l)) * planeWave p σ x *
        (M c (z t) + L c (z t) *
          if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1) := by
  have hrot : (∑ σ, amplitude (anisotropy c) p σ * positionPhase t
        (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l)) * planeWave p σ x) =
      ∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
        planeWave p σ x * (if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1) := by
    refine sum_congr rfl fun σ _ => ?_
    rw [show (σ * (finRotate (n + 1))⁻¹).symm l = finRotate (n + 1) (σ.symm l) from rfl,
      cyclicPredecessor_rotate]
    grind [Fin.last, positionPhase_sub_nat]
  have := congrArg (· * (L c (z t) * ∏ j ∈ univ.erase l, M c (z (p j))))
    ((toroidal_zero_root_L_phase (anisotropy_lt_neg_one hc) p hBE x l t).trans hrot)
  simp only [sum_mul] at this
  unfold constantWordSumPerturbed
  simp_rw [wordCoefficient_false, wordCoefficient_true, wordPhase_false, wordPhase_true,
    planeWave_perturbed_zero p l hpl t]
  rw [prod_perturbed_factor p l t (fun r => M c (z r)), prod_perturbed_factor p l t (fun r => L c (z r)), hpl, zero_add,
    prod_L_eq_prod_M_of_zero hc p hp hinj l hpl hBE, mul_sum, ← sub_eq_zero, ← sum_sub_distrib, ← sub_eq_zero.2 this,
    ← sum_sub_distrib]
  exact sum_congr rfl fun σ _ => by ring
end

end PottsDiscontinuity.BetheAnsatz
