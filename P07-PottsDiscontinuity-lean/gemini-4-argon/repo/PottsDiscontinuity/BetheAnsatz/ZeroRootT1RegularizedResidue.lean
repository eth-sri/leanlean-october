module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1FinitePairs
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperStep

/-!
# The T₁ residue is the regularized word coefficient

For a word with a unique cyclic ML edge, the pole residue at that edge is the
product of the L/M weights with the zero-root slot omitted. This is the precise
bridge between the analytic pair limit and the zipper invariant.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The residue factor at a unique ML edge is the product of all nonsingular
letter weights, with the zero-root slot omitted. -/
theorem wordCoefficientEraseEdge_eq_zeroRootRegularizedProduct {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a b : Fin (n + 1))
    (hrot : b = finRotate (n + 1) a) (hσ : σ b = l)
    (hleft : w a = false) (hright : w b = true)
    (hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true → k = a) :
    M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a =
      zeroRootRegularizedProduct c p l σ w := by
  let τ := finRotate (n + 1)
  let E : Finset (Fin (n + 1)) := univ.filter (fun k => w k = true ∧ w (τ k) = true)
  let F : Finset (Fin (n + 1)) := univ.filter (fun k => w k = false)
  let J : Finset (Fin (n + 1)) := univ.filter (fun j => w j = true ∧ j ≠ b)
  let qL (j : Fin (n + 1)) := L c (z (p (σ j)))
  let qM (j : Fin (n + 1)) := M c (z (p (σ j)))
  have hroot : σ.symm l = b := σ.injective (by simpa using hσ.symm)
  have hJimage : E.image τ = J := by
    ext j
    simp only [E, J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, fun ⟨hjw, hjne⟩ => ?_⟩
    · rintro ⟨k, ⟨hkw, hnext⟩, rfl⟩
      refine ⟨hnext, fun he => ?_⟩
      have := τ.injective (he.trans hrot)
      subst k; simp [hleft] at hkw
    · have hτj : finRotate (n + 1) (τ.symm j) = j := τ.apply_symm_apply j
      refine ⟨τ.symm j, ⟨by_contra fun h => hjne ?_, by rwa [hτj]⟩, hτj⟩
      rw [← hτj, hunique (τ.symm j) (Bool.eq_false_of_not_eq_true h) (by rwa [hτj]), ← hrot]
  let G (k : Fin (n + 1)) : ℂ :=
    if w k then (if w (τ k) then qL (τ k) else 1) else qM k
  let H (k : Fin (n + 1)) : ℂ :=
    if k = a then qM a else wordEdgeFactor c p σ w k
  have hlocal (k : Fin (n + 1)) : H k = G k := by
    by_cases hka : k = a
    · subst k; simp [H, G, hleft, qM]
    · by_cases hwk : w k = true <;> by_cases hwn : w (τ k) = true
      · simp [H, G, hwk, wordEdgeFactor, qL, qM, τ, hka]
      · simp [H, G, hwk, wordEdgeFactor, qL, qM, τ, hka]
      · exact False.elim (hka (hunique k (by simpa using hwk) (by simpa [τ] using hwn)))
      · have hwn'' : w (k + 1) = false := by
          simpa using (Bool.eq_false_of_not_eq_true hwn : w (finRotate (n + 1) k) = false)
        change (if k = a then qM a else wordEdgeFactor c p σ w k) =
          (if w k then (if w (τ k) then qL (τ k) else 1) else qM k)
        simp [hwk, hwn'', wordEdgeFactor, qM, hka]
  have hprodH : (∏ k, H k) = M c (z (p (σ a))) * wordCoefficientEraseEdge c p σ w a := by
    rw [← Finset.mul_prod_erase univ H (mem_univ a)]
    simp only [H, ite_true, qM, wordCoefficientEraseEdge]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by simp [(Finset.mem_erase.mp hk).1]
  have hprodG : (∏ k, G k) = (∏ k ∈ E, qL (τ k)) * ∏ k ∈ F, qM k := by
    rw [show (∏ k, G k) = (∏ k, if w k = true ∧ w (τ k) = true then qL (τ k) else 1) *
        ∏ k, if w k = false then qM k else 1 by
      rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun k _ => ?_
      cases hw : w k <;> cases hn : w (τ k) <;> simp [G, hw, hn]]
    simpa [E, F] using congrArg₂ (· * ·)
      (Finset.prod_filter (s := univ) (fun k => w k = true ∧ w (τ k) = true) (fun k => qL (τ k))).symm
      (Finset.prod_filter (s := univ) (fun k => w k = false) qM).symm
  have htarget : zeroRootRegularizedProduct c p l σ w = (∏ j ∈ J, qL j) * ∏ j ∈ F, qM j := by
    unfold zeroRootRegularizedProduct
    rw [hroot, show (∏ j ∈ univ.erase b, zeroRootLetterWeight c p σ w j) =
        ∏ j, if j = b then (1 : ℂ) else zeroRootLetterWeight c p σ w j by
      rw [← Finset.mul_prod_erase univ (fun j => if j = b then (1 : ℂ) else zeroRootLetterWeight c p σ w j) (mem_univ b)]
      simp only [ite_true, one_mul]
      exact Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_erase.mp hj).1],
      show (∏ j, if j = b then (1 : ℂ) else zeroRootLetterWeight c p σ w j) =
        (∏ j, if w j = true ∧ j ≠ b then qL j else 1) * ∏ j, if w j = false then qM j else 1 by
      rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = b
      · subst j; simp [hright, qL, qM]
      · cases hw : w j <;> simp [zeroRootLetterWeight, qL, qM, hj, hw]]
    simpa [J, F] using congrArg₂ (· * ·)
      (Finset.prod_filter (s := univ) (fun j => w j = true ∧ j ≠ b) qL).symm
      (Finset.prod_filter (s := univ) (fun j => w j = false) qM).symm
  rw [← hprodH, Finset.prod_congr rfl fun k _ => hlocal k, hprodG, htarget,
    ← hJimage, Finset.prod_image τ.injective.injOn]

/-- For `T1PairIndex`, the pole residue coefficient is exactly its zipper
regularized product. -/
theorem t1Pair_residue_eq_regularizedProduct {n : ℕ} {l : Fin (n + 1)}
    (c : ℝ) (p : Fin (n + 1) → ℝ)
    (i : T1PairIndex n l) :
    M c (z (p (i.σ (t1EdgeLeft i.edge)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) i.σ i.w
          (t1EdgeLeft i.edge) =
      zeroRootRegularizedProduct c p l i.σ i.w := by
  rw [show perturbedMomenta p l 0 = p by funext k; by_cases hk : k = l <;> simp [perturbedMomenta, hk]]
  exact wordCoefficientEraseEdge_eq_zeroRootRegularizedProduct c p l i.σ i.w
    (t1EdgeLeft i.edge) (t1EdgeRight i.edge)
    (by cases i.edge with | none => exact finRotate_last.symm | some a => exact (finRotate_of_lt a.isLt).symm)
    i.hσ i.hleft i.hright i.hunique

/-- The finite pair limit is the regularized word term times its corrected
phase derivative. -/
theorem t1PairLimit_eq_regularizedWordTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w *
        (match i.edge with
        | some a => (zeroRootPhaseDerivative (N := N) (anisotropy c)
            (p (i.σ a.castSucc)) False : ℂ)
        | none => (zeroRootPhaseDerivative (N := N) (anisotropy c)
            (p (i.σ (Fin.last n))) True : ℂ)) := by
  have hres := t1Pair_residue_eq_regularizedProduct (c := c) p (l := l) i
  cases hEdge : i.edge <;> simp [hEdge, t1EdgeLeft] at hres <;>
    simp only [t1PairLimit, hEdge, zeroRootRegularizedWordTerm, ← hres] <;> ring

end PottsDiscontinuity.BetheAnsatz
