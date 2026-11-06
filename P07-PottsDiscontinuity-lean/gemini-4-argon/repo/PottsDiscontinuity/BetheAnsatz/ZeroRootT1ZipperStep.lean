module

public import PottsDiscontinuity.BetheAnsatz.WordRotation

/-!
# Regularized zero-root word terms and an ordinary zipper move

The corrected move takes an `L` at the zero-root slot across the next `L`,
changing that letter to `M` and transposing the two momentum slots. -/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The letter weight at a nonzero-root slot. -/
noncomputable def zeroRootLetterWeight {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (k : Fin (n + 1)) : ℂ :=
  if w k then L c (z (p (σ k))) else M c (z (p (σ k)))

/-- The regularized product omits the slot occupied by the zero root. -/
noncomputable def zeroRootRegularizedProduct {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∏ k ∈ (univ : Finset (Fin (n + 1))).erase (σ.symm l),
    zeroRootLetterWeight c p σ w k

/-- The source's `ĝσ(w)`, with a zero momentum label `l` and zero-based positions. -/
noncomputable def zeroRootRegularizedWordTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ * (c : ℂ)^2 *
    zeroRootRegularizedProduct c p l σ w * wordPhase (N := N) x p σ w

/-- Updating an ordinary zipper letter leaves its position phase at the
transposed root slots unchanged, since the moved root has momentum zero. -/
theorem wordPhase_zipper_ordinary {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hb : p (σ a.castSucc) = 0) (hc : w a.succ = true) :
    wordPhase (N := N) x p (σ * Equiv.swap a.castSucc a.succ)
        (Function.update w a.castSucc false) =
      wordPhase (N := N) x p σ w := by
  change planeWave p (σ * Equiv.swap a.castSucc a.succ)
      (wordPositions N x (Function.update w a.castSucc false)) =
    planeWave p σ (wordPositions N x w)
  rw [planeWave_swap]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hkb : k = a.castSucc
  · subst k; simp [wordPositions, hb]
  · by_cases hkc : k = a.succ
    · subst k; simp [wordPositions, hc, cyclicPredecessorPositions_succ]
    · simp [wordPositions, hkb, Equiv.swap_apply_of_ne_of_ne hkb hkc]

/-- One ordinary zipper step preserves the regularized word term. -/
theorem zeroRootRegularizedWordTerm_zipper_ordinary {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.castSucc = l) (hcw : w a.succ = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
        (σ * Equiv.swap a.castSucc a.succ) (Function.update w a.castSucc false) =
      zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  let b := a.castSucc
  let d := a.succ
  have hbd : b ≠ d := Fin.castSucc_lt_succ.ne
  have hσb : σ b = l := hsig
  have hσd : σ d ≠ l := fun h => hbd (σ.injective (h.trans hσb.symm)).symm
  have hzd : z (p (σ d)) ≠ 1 := z_ne_one (hp (σ d)) fun h => hσd (hinj (h.trans hpl.symm))
  have hM : M c (z (p (σ d))) ≠ 0 := M_ne_zero hc hzd
  have hL : L c (z (p (σ d))) ≠ 0 := L_ne_zero hc hzd
  have hRoot' : (σ * Equiv.swap b d).symm l = d :=
    (σ * Equiv.swap b d).injective (by simp [Equiv.Perm.mul_apply, hσb])
  let S : Finset (Fin (n + 1)) := (univ.erase b).erase d
  have hcommon :
      (∏ k ∈ S, zeroRootLetterWeight c p (σ * Equiv.swap b d)
          (Function.update w b false) k) =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k :=
    Finset.prod_congr rfl fun k hk => by
      have hkb : k ≠ b := (mem_erase.mp (mem_erase.mp hk).2).1
      have hkd : k ≠ d := (mem_erase.mp hk).1
      simp [zeroRootLetterWeight, Function.update_of_ne hkb, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hkb hkd]
  have hOld : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ d))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    unfold zeroRootRegularizedProduct
    rw [show σ.symm l = b from σ.injective (by simpa using hσb.symm),
      ← Finset.mul_prod_erase (univ.erase b) _ (Finset.mem_erase.mpr ⟨hbd.symm, mem_univ d⟩)]
    simp [zeroRootLetterWeight, d, hcw, S]
  have hNew : zeroRootRegularizedProduct c p l
      (σ * Equiv.swap b d) (Function.update w b false) =
      M c (z (p (σ d))) * ∏ k ∈ S,
        zeroRootLetterWeight c p (σ * Equiv.swap b d)
          (Function.update w b false) k := by
    unfold zeroRootRegularizedProduct
    rw [hRoot', ← Finset.mul_prod_erase (univ.erase d) _ (Finset.mem_erase.mpr ⟨hbd, mem_univ b⟩),
      show (univ.erase d).erase b = S by ext; simp [S, and_comm]]
    simp [zeroRootLetterWeight]
  have hprodCross :
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
          (Function.update w b false) * L c (z (p (σ d))) =
        zeroRootRegularizedProduct c p l σ w * M c (z (p (σ d))) := by
    rw [hNew, hOld, hcommon]; ring
  have hAmp : amplitude (anisotropy c) p (σ * Equiv.swap b d) *
      M c (z (p (σ d))) =
    amplitude (anisotropy c) p σ * L c (z (p (σ d))) := by
    have hswap := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ
      (a := b) (b := d) (by simp [b, d])
    rw [hσb, hpl] at hswap
    rw [hswap, exp_I_theta_zero_eq_neg_L_div_M hc hzd]
    field_simp [hM]
  have hAP : amplitude (anisotropy c) p (σ * Equiv.swap b d) *
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
        (Function.update w b false) =
    amplitude (anisotropy c) p σ * zeroRootRegularizedProduct c p l σ w :=
    mul_right_cancel₀ hL (by
      linear_combination amplitude (anisotropy c) p (σ * Equiv.swap b d) * hprodCross +
        zeroRootRegularizedProduct c p l σ w * hAmp)
  unfold zeroRootRegularizedWordTerm
  rw [wordPhase_zipper_ordinary (N := N) x p σ w a (by rw [hsig, hpl]) hcw]
  change amplitude (anisotropy c) p (σ * Equiv.swap b d) * (c : ℂ)^2 *
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
        (Function.update w b false) * wordPhase (N := N) x p σ w = _
  linear_combination (c : ℂ) ^ 2 * wordPhase (N := N) x p σ w * hAP

end PottsDiscontinuity.BetheAnsatz
