module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Analytic
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Ordinary
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Pairing
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Phase

/-!
# Residue and cancellation for an ordinary T₁ pair

At an ordinary ML edge carrying the moved zero root on its L end, exactly one
word-coefficient edge factor has a pole. The fixed-amplitude pair cancels that
pole against the first-order scattering phase.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The coefficient product with one selected cyclic edge removed. -/
noncomputable def wordCoefficientEraseEdge {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin (n + 1)) : ℂ :=
  ∏ k ∈ (univ : Finset (Fin (n + 1))).erase a, wordEdgeFactor c p σ w k

section
variable {N n : ℕ} {c : ℝ}
include c
/-- The pole residue of the amplitude-weighted ordinary word term. -/
theorem tendsto_t_mul_perturbedWordTerm (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (e : Fin (n + 1))
    (hsig : σ (finRotate (n + 1) e) = l) (ha : w e = false) (hb : w (finRotate (n + 1) e) = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ e))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w e *
        wordPhase (N := N) x p σ w))) := by
  have hσa : σ e ≠ l := fun h => by simp [← σ.injective (h.trans hsig.symm), ha] at hb
  let m := M c (z (p (σ e)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w e
  let rest (t : ℝ) := ∏ k ∈ (univ : Finset (Fin (n + 1))).erase e,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    dsimp [edge, q, m]
    have hroot : z (perturbedMomenta p l t (σ (finRotate (n + 1) e))) = z t := by
      simp_all
    have hother := perturbedMomenta_of_ne p l (σ e) t hσa
    unfold wordEdgeFactor
    grind
  have hrest (t : ℝ) : rest t = rest 0 := by
    refine prod_congr rfl fun k hk => ?_
    have hka : k ≠ e := by simp_all
    have hnext := (finRotate _).injective.ne hka
    have hσnext : σ (finRotate (n + 1) k) ≠ l := by aesop
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t hσnext
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 hσnext
    unfold wordEdgeFactor
    cases hw : w k <;> cases hn : w (finRotate (n + 1) k)
    iterate 2
      have hσk : σ k ≠ l := by aesop
      have h1 := perturbedMomenta_of_ne p l (σ k) t hσk
      have h2 := perturbedMomenta_of_ne p l (σ k) 0 hσk
      grind
    · rfl
    grind
  have hprod (t : ℝ) : wordCoefficient c (q t) σ w = edge t * rest t := by
    change (∏ k, wordEdgeFactor c (q t) σ w k) = _
    simpa [edge, rest] using (Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
      (fun k => wordEdgeFactor c (q t) σ w k) (mem_univ e)).symm
  have hlocalLimit : Tendsto (fun t : ℝ => (t : ℂ) * edge t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (m * (I * (c : ℂ)^2))) := by
    have heq : (fun t : ℝ => (t : ℂ) * edge t) =
        fun (t : ℝ) => m * ((t : ℂ) * L c (z t)) - (t : ℂ) := by
      grind
    rw [heq]
    simpa using (tendsto_const_nhds.mul (tendsto_t_mul_L_z_zero c)).sub
      ((continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
  have hphase : Continuous (fun t : ℝ =>
      wordPhase (N := N) x (q t) σ w) := by
    unfold wordPhase positionPhase q perturbedMomenta
    fun_prop
  have hphaseT : Tendsto (fun t : ℝ => wordPhase (N := N) x (q t) σ w)
      (𝓝[≠] (0 : ℝ)) (𝓝 (wordPhase (N := N) x p σ w)) := by
    have h0 : q 0 = p := by simp [q, perturbedMomenta]
    convert hphase.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp_all
  have hfun : (fun t : ℝ => (t : ℂ) * perturbedWordTerm (N := N) c x p l t σ w) =
      fun (t : ℝ) => amplitude (anisotropy c) p σ *
        ((t : ℂ) * edge t * rest 0 * wordPhase (N := N) x (q t) σ w) := by
    grind [perturbedWordTerm]
  rw [hfun]
  convert tendsto_const_nhds.mul ((hlocalLimit.mul tendsto_const_nhds).mul hphaseT) using 2
  simp only [wordCoefficientEraseEdge, rest, m, q]
  ring

end

end PottsDiscontinuity.BetheAnsatz
