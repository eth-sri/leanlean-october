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
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [finRotate_last, cyclicPredecessorPositions_zero]; simp
  · have hrot : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
    rw [hrot, cyclicPredecessorPositions_succ]
    simp [Fin.castSucc_ne_last]

/-- Negative integer phases are inverse natural powers. -/
theorem positionPhase_neg_nat (t : ℝ) (d : ℕ) :
    positionPhase t (-(d : ℤ)) = (z t ^ d)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← positionPhase_nat, ← positionPhase_add]
  simp [positionPhase]

/-- Shifting an integer coordinate down by N contributes the inverse Nth phase. -/
theorem positionPhase_sub_nat (t : ℝ) (y : ℤ) (N : ℕ) :
    positionPhase t (y - (N : ℤ)) = positionPhase t y * (z t ^ N)⁻¹ := by
  rw [show y - (N : ℤ) = y + (-(N : ℤ)) by ring, positionPhase_add, positionPhase_neg_nat]

/-- Product over the non-root indices is unchanged by the perturbation. -/
theorem prod_perturbed_erase_eq {n : ℕ} (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (f : ℝ → ℂ) :
    (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (perturbedMomenta p l t j)) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) :=
  Finset.prod_congr rfl fun j hj => by rw [perturbedMomenta_of_ne p l j t (mem_erase.mp hj).1]

/-- Product of a one-root perturbed sequence is its root factor times the fixed remainder. -/
theorem prod_perturbed_factor {n : ℕ} (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (f : ℝ → ℂ) :
    (∏ j, f (perturbedMomenta p l t j)) =
      f (p l + t) * ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ l), perturbedMomenta_at,
    prod_perturbed_erase_eq p l t f]

/-- The fixed-amplitude contribution of the two constant words at perturbation t. -/
noncomputable def constantWordSumPerturbed {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), amplitude (anisotropy c) p σ *
    (wordCoefficient c (perturbedMomenta p l t) σ (fun _ => false) *
        wordPhase (N := N) x (perturbedMomenta p l t) σ (fun _ => false) +
     wordCoefficient c (perturbedMomenta p l t) σ (fun _ => true) *
        wordPhase (N := N) x (perturbedMomenta p l t) σ (fun _ => true))

/-- Reindexing identity for the L constant word with its one-root phase. -/
theorem toroidal_zero_root_L_phase {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (x : Fin (n + 1) → ℤ) (l : Fin (n + 1)) (t : ℝ) :
    (∑ σ, amplitude Δ p σ * positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
        planeWave p σ (cyclicPredecessorPositions N x)) =
      ∑ σ, amplitude Δ p σ * positionPhase t
        (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l)) *
        planeWave p σ x := by
  let f : Equiv.Perm (Fin (n + 1)) → ℂ := fun σ =>
    positionPhase t (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l))
  have hf (σ) : f (σ * finRotate (n + 1)) =
      positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) := by
    dsimp [f]; rw [show (σ * finRotate (n + 1)) * (finRotate (n + 1))⁻¹ = σ by group]
  simpa only [f, hf, mul_assoc] using (toroidal_change_of_variables hΔ p hBE x f).symm

/-- Exact T₀ decomposition before taking the limit. -/
theorem constantWordSumPerturbed_eq {N n : ℕ} {c : ℝ} (hc : 2 < c)
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
  let P := ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))
  have hLM := prod_L_eq_prod_M_of_zero hc p hp hinj l hpl hBE
  have hM : (∏ j, M c (z (perturbedMomenta p l t j))) = M c (z t) * P := by
    rw [prod_perturbed_factor p l t (fun r => M c (z r)), hpl, zero_add]
  have hL : (∏ j, L c (z (perturbedMomenta p l t j))) = L c (z t) * P := by
    rw [prod_perturbed_factor p l t (fun r => L c (z r)), hpl, zero_add, hLM]
  have htor := toroidal_zero_root_L_phase (anisotropy_lt_neg_one hc) p hBE x l t
  have hrot :
      (∑ σ, amplitude (anisotropy c) p σ *
        positionPhase t (cyclicPredecessorPositions N x
          ((σ * (finRotate (n + 1))⁻¹).symm l)) * planeWave p σ x) =
      ∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
        planeWave p σ x * (if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hidx : (σ * (finRotate (n + 1))⁻¹).symm l = finRotate (n + 1) (σ.symm l) := by
      have hperm : (σ * (finRotate (n + 1))⁻¹)⁻¹ = finRotate (n + 1) * σ⁻¹ := by group
      simpa only [Equiv.Perm.inv_def, Equiv.Perm.mul_apply] using
        congrArg (fun ρ : Equiv.Perm (Fin (n + 1)) => ρ l) hperm
    rw [hidx, cyclicPredecessor_rotate]
    by_cases hk : σ.symm l = Fin.last n <;> simp [hk, positionPhase_sub_nat]; ring
  rw [hrot] at htor
  unfold constantWordSumPerturbed
  simp_rw [wordCoefficient_false, wordCoefficient_true, hM, hL,
    wordPhase_false, wordPhase_true, planeWave_perturbed_zero p l hpl t]
  rw [show (∑ σ : Equiv.Perm (Fin (n + 1)), amplitude (anisotropy c) p σ *
        (M c (z t) * P * (positionPhase t (x (σ.symm l)) * planeWave p σ x) +
         L c (z t) * P * (positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
           planeWave p σ (cyclicPredecessorPositions N x)))) =
      P * M c (z t) * (∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) * planeWave p σ x) +
      P * L c (z t) * (∑ σ, amplitude (anisotropy c) p σ *
        positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
        planeWave p σ (cyclicPredecessorPositions N x)) by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring,
    htor, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end PottsDiscontinuity.BetheAnsatz
