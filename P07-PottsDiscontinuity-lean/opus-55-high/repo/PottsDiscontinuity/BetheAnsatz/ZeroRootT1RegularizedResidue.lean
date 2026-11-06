module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1FinitePairs
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperStep

/-!
# The T₁ residue is the regularized word coefficient

For a word with a unique cyclic ML edge, the pole residue at that edge is the
product of the L/M weights with the zero-root slot omitted. This is the precise
bridge between the analytic pair limit and the zipper invariant.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ}
/-- The residue factor at a unique ML edge is the product of all nonsingular
letter weights, with the zero-root slot omitted. -/
theorem wordCoefficientEraseEdge_eq_zeroRootRegularizedProduct (c : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a b : Fin (n + 1))
    (hrot : b = finRotate (n + 1) a) (hσ : σ b = l)
    (hleft : w a = false) (hright : w b = true)
    (hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true → k = a) :
    M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a =
      zeroRootRegularizedProduct c p l σ w := by
  have hroot : σ.symm l = b := by simp [← hσ]
  have h1 : M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a =
      (∏ k, if w k ∧ w (finRotate (n + 1) k) then L c (z (p (σ (finRotate (n + 1) k)))) else 1) *
        ∏ k, if w k then 1 else M c (z (p (σ k))) := by
    rw [← Finset.prod_mul_distrib, wordCoefficientEraseEdge, ← Finset.mul_prod_erase univ _ (mem_univ a)]
    congr 1
    · simp [hleft]
    · refine Finset.prod_congr rfl fun k hk => ?_
      have := hunique k
      cases hk : w k <;> cases hn : w (finRotate (n + 1) k) <;> simp_all [wordEdgeFactor]
  have h2 : zeroRootRegularizedProduct c p l σ w =
      (∏ k, if w k ∧ k ≠ b then L c (z (p (σ k))) else 1) *
        ∏ k, if w k then 1 else M c (z (p (σ k))) := by
    rw [← Finset.prod_mul_distrib, zeroRootRegularizedProduct, hroot, ← Finset.mul_prod_erase univ _ (mem_univ b), ← one_mul (∏ k ∈ univ.erase b, _)]
    congr 1
    · simp [hright]
    · refine Finset.prod_congr rfl fun k hk => ?_
      cases hw : w k <;> simp_all [zeroRootLetterWeight]
  rw [h1, h2, ← Equiv.prod_comp (finRotate (n + 1)) fun k => if w k ∧ k ≠ b then L c (z (p (σ k))) else 1]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have := hunique k
  by_cases hka : k = a
  · simp_all
  · have : finRotate (n + 1) k ≠ b := by rw [hrot]; exact (finRotate (n + 1)).injective.ne hka
    cases hk : w k <;> cases hn : w (finRotate (n + 1) k) <;> simp_all

/-- For `T1PairIndex`, the pole residue coefficient is exactly its zipper
regularized product. -/
theorem t1Pair_residue_eq_regularizedProduct {l : Fin (n + 1)}
    (c : ℝ) (p : Fin (n + 1) → ℝ)
    (i : T1PairIndex n l) :
    M c (z (p (i.σ (t1EdgeLeft i.edge)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) i.σ i.w
          (t1EdgeLeft i.edge) =
      zeroRootRegularizedProduct c p l i.σ i.w := by
  rw [show perturbedMomenta p l 0 = p by simp [perturbedMomenta]]
  exact wordCoefficientEraseEdge_eq_zeroRootRegularizedProduct c p l i.σ i.w
    (t1EdgeLeft i.edge) (t1EdgeRight i.edge) (t1EdgeLeft_rotate _).symm i.hσ i.hleft i.hright i.hunique
end

/-- The finite pair limit is the regularized word term times its corrected
phase derivative. -/
theorem t1PairLimit_eq_regularizedWordTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w *
        (zeroRootPhaseDerivative (N := N) (anisotropy c) (p (i.σ (t1EdgeLeft i.edge))) (i.edge = none) : ℂ) := by
  rw [t1PairLimit, zeroRootRegularizedWordTerm, ← t1Pair_residue_eq_regularizedProduct]
  ring

end PottsDiscontinuity.BetheAnsatz
