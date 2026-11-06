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

/-- The pole residue of the amplitude-weighted ordinary word term. -/
theorem tendsto_t_mul_perturbedWordTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (_hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ a.castSucc))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
        wordPhase (N := N) x p σ w))) := by
  have hrot : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hσa : σ a.castSucc ≠ l := fun h => Fin.castSucc_lt_succ.ne (σ.injective (h.trans hsig.symm))
  let m := M c (z (p (σ a.castSucc)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w a.castSucc
  let rest (t : ℝ) := ∏ k ∈ (univ : Finset (Fin (n + 1))).erase a.castSucc,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    dsimp [edge, q, m]
    unfold wordEdgeFactor
    rw [hrot, ha, hb]
    simp [hsig, perturbedMomenta_at, hpl, perturbedMomenta_of_ne p l (σ a.castSucc) t hσa]
  have hrest (t : ℝ) : rest t = rest 0 := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hka : k ≠ a.castSucc := (mem_erase.mp hk).1
    have hσnext : σ (finRotate (n + 1) k) ≠ l := fun h =>
      hka ((finRotate (n + 1)).injective ((σ.injective (h.trans hsig.symm)).trans hrot.symm))
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t hσnext
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 hσnext
    unfold wordEdgeFactor
    cases hw : w k <;> cases hn : w (finRotate (n + 1) k)
    · have hσk : σ k ≠ l := fun h => by subst hsig; cases σ.injective h; simp [hb] at hw
      simp only [q, Bool.false_eq_true, ↓reduceIte,
        perturbedMomenta_of_ne p l (σ k) t hσk, perturbedMomenta_of_ne p l (σ k) 0 hσk]
    · have hσk : σ k ≠ l := fun h => by subst hsig; cases σ.injective h; simp [hb] at hw
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
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
        wordPhase (N := N) x p σ w) by change _ = I * (_ * rest 0 * _); ring] at hlim
  refine hlim.congr fun t => ?_
  unfold perturbedWordTerm
  have hprod : wordCoefficient c (q t) σ w = edge t * rest t :=
    (Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
      (fun k => wordEdgeFactor c (q t) σ w k) (mem_univ a.castSucc)).symm
  change amplitude (anisotropy c) p σ *
    ((t : ℂ) * edge t * rest 0 * wordPhase (N := N) x (q t) σ w) =
    (t : ℂ) * (amplitude (anisotropy c) p σ * wordCoefficient c (q t) σ w *
      wordPhase (N := N) x (q t) σ w)
  rw [hprod, hrest t]; ring

/-- The ordinary-edge paired terms have a finite limit, given by the phase slope
times the explicit pole residue. -/
theorem tendsto_ordinaryT1_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    Tendsto (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap a.castSucc a.succ) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (((c : ℂ)^2 * amplitude (anisotropy c) p σ *
          M c (z (p (σ a.castSucc))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
          wordPhase (N := N) x p σ w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (σ a.castSucc)) False : ℂ))) := by
  let f : ℝ → ℂ := fun t => Complex.exp (I *
    (zeroRootPhaseExponent (N := N) (anisotropy c)
      (p (σ a.castSucc)) False t : ℂ))
  have hcancel := tendsto_pole_mul_one_sub_of_hasDerivAt
    (hasDerivAt_zeroRootPhaseExp (N := N) (c := c) (p := p (σ a.castSucc)) hc False)
    (by simp [f, zeroRootPhaseExponent] : f 0 = 1)
    (tendsto_t_mul_perturbedWordTerm (N := N) (c := c) x p hinj l hpl σ w a hsig ha hb)
  refine hcancel.congr' ?_
  filter_upwards [eventually_z_ne_one_zero] with t ht
  rw [perturbedWordTerm_adjacent_pair hc x p hp hinj l hpl t ht σ w a hsig ha hb]
  simp only [zeroRootPhaseExponent, ite_false, add_zero, Pi.sub_apply, Complex.ofReal_sub]
  ring

end PottsDiscontinuity.BetheAnsatz
