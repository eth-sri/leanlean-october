module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Residue
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPair

/-!
# The seam residue and paired limit

At a seam ML edge the unique pole is the cyclic edge from the last slot to
slot zero. Its residue combines with the corrected phase slope containing `N`.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The amplitude-weighted seam word term has an explicit pole residue. -/
theorem tendsto_t_mul_perturbedWordTerm_seam {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (_hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ (Fin.last n)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
        wordPhase (N := N) x p σ w))) := by
  let u := Fin.last n
  have hu0 : u ≠ (0 : Fin (n + 1)) := fun h => by have := congrArg Fin.val h; simp [u] at this; omega
  have hrot : finRotate (n + 1) u = 0 := by simp [u]
  have hσu : σ u ≠ l := fun h => hu0 (σ.injective (h.trans hsig.symm))
  let m := M c (z (p (σ u)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w u
  let rest (t : ℝ) := ∏ k ∈ (univ : Finset (Fin (n + 1))).erase u,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    dsimp [edge, q, m]
    unfold wordEdgeFactor
    rw [hrot, hLast, hZero]
    simp [hsig, perturbedMomenta_at, hpl, perturbedMomenta_of_ne p l (σ u) t hσu]
  have hrest (t : ℝ) : rest t = rest 0 := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hku : k ≠ u := (mem_erase.mp hk).1
    have hσnext : σ (finRotate (n + 1) k) ≠ l := fun h =>
      hku ((finRotate (n + 1)).injective ((σ.injective (h.trans hsig.symm)).trans hrot.symm))
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t hσnext
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 hσnext
    unfold wordEdgeFactor
    cases hw : w k <;> cases hnxt : w (finRotate (n + 1) k)
    · have hσk : σ k ≠ l := fun h => by subst hsig; cases σ.injective h; simp [hZero] at hw
      simp only [q, Bool.false_eq_true, ↓reduceIte,
        perturbedMomenta_of_ne p l (σ k) t hσk, perturbedMomenta_of_ne p l (σ k) 0 hσk]
    · have hσk : σ k ≠ l := fun h => by subst hsig; cases σ.injective h; simp [hZero] at hw
      simp only [q, Bool.false_eq_true, ↓reduceIte, h3, h4,
        perturbedMomenta_of_ne p l (σ k) t hσk, perturbedMomenta_of_ne p l (σ k) 0 hσk]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [q, ↓reduceIte, h3, h4]
  have hlocalLimit : Tendsto (fun t : ℝ => (t : ℂ) * edge t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (m * (I * (c : ℂ)^2))) := by
    rw [show (fun t : ℝ => (t : ℂ) * edge t) = fun t : ℝ => m * ((t : ℂ) * L c (z t)) - (t : ℂ) by
      funext t; rw [hlocal]; ring]
    simpa using (tendsto_const_nhds.mul (tendsto_t_mul_L_z_zero c)).sub
      ((continuous_ofReal.continuousAt : ContinuousAt (fun t : ℝ => (t : ℂ)) 0).tendsto.mono_left nhdsWithin_le_nhds)
  have hphase : Continuous (fun t : ℝ => wordPhase (N := N) x (q t) σ w) := by
    unfold wordPhase positionPhase q perturbedMomenta; fun_prop
  have hphaseT : Tendsto (fun t : ℝ => wordPhase (N := N) x (q t) σ w)
      (𝓝[≠] (0 : ℝ)) (𝓝 (wordPhase (N := N) x p σ w)) := by
    rw [show p = q 0 by funext k; by_cases hk : k = l <;> simp [q, perturbedMomenta, hk]]
    exact hphase.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_const_nhds (x := amplitude (anisotropy c) p σ)).mul
    ((hlocalLimit.mul (tendsto_const_nhds (x := rest 0))).mul hphaseT)
  rw [show amplitude (anisotropy c) p σ *
      (m * (I * (c : ℂ)^2) * rest 0 * wordPhase (N := N) x p σ w) =
      I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ * m *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w u *
        wordPhase (N := N) x p σ w) by change _ = I * (_ * rest 0 * _); ring] at hlim
  refine hlim.congr fun t => ?_
  unfold perturbedWordTerm
  have hprod : wordCoefficient c (q t) σ w = edge t * rest t :=
    (Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
      (fun k => wordEdgeFactor c (q t) σ w k) (mem_univ u)).symm
  change amplitude (anisotropy c) p σ *
    ((t : ℂ) * edge t * rest 0 * wordPhase (N := N) x (q t) σ w) =
    (t : ℂ) * (amplitude (anisotropy c) p σ * wordCoefficient c (q t) σ w *
      wordPhase (N := N) x (q t) σ w)
  rw [hprod, hrest t]; ring

/-- The seam-paired terms have a finite limit with the corrected phase slope,
including the additional `N` contribution. -/
theorem tendsto_seamT1_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    Tendsto (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap (Fin.last n) 0) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (((c : ℂ)^2 * amplitude (anisotropy c) p σ *
          M c (z (p (σ (Fin.last n)))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
          wordPhase (N := N) x p σ w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (σ (Fin.last n))) True : ℂ))) := by
  let f : ℝ → ℂ := fun t => Complex.exp (I *
    (zeroRootPhaseExponent (N := N) (anisotropy c)
      (p (σ (Fin.last n))) True t : ℂ))
  have hcancel := tendsto_pole_mul_one_sub_of_hasDerivAt
    (hasDerivAt_zeroRootPhaseExp (N := N) (c := c) (p := p (σ (Fin.last n))) hc True)
    (by simp [f, zeroRootPhaseExponent] : f 0 = 1)
    (tendsto_t_mul_perturbedWordTerm_seam (N := N) (c := c) x p hinj l hpl σ w hn hsig hLast hZero)
  refine hcancel.congr' ?_
  filter_upwards [eventually_z_ne_one_zero] with t ht
  rw [perturbedWordTerm_seam_pair hc x p hp hinj l hpl hBE t ht σ w hn hsig hLast hZero]
  simp only [zeroRootPhaseExponent, ite_true, Pi.sub_apply, Pi.add_apply,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  ring

end PottsDiscontinuity.BetheAnsatz
