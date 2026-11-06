module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamAmplitude
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperFinalStep

/-!
# The cyclic seam zipper move

The ordinary zipper identity also holds across the last-to-first edge. The
Bethe boundary relation and the `N`-shift in the position phase cancel exactly.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Move a zero root across two consecutive L letters at the cyclic seam. -/
theorem zeroRootRegularizedWordTerm_zipper_seam {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hσ : σ (Fin.last n) = l)
    (hZero : w 0 = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap (Fin.last n) 0) (Function.update w (Fin.last n) false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  let u := Fin.last n
  let σ' := σ * Equiv.swap u 0
  let w' := Function.update w u false
  have hu0 : u ≠ (0 : Fin (n + 1)) := fun h => by have := congrArg Fin.val h; simp [u] at this; omega
  have hσ0 : σ' 0 = l := by simpa [σ', Equiv.Perm.mul_apply] using hσ
  have hσ'u : σ' u = σ 0 := by simp [σ', Equiv.Perm.mul_apply]
  have hσ0ne : σ 0 ≠ l := fun h => hu0 (σ.injective (h.trans hσ.symm)).symm
  have hz : z (p (σ 0)) ≠ 1 := z_ne_one (hp (σ 0)) fun h => hσ0ne (hinj (h.trans hpl.symm))
  have hL : L c (z (p (σ 0))) ≠ 0 := L_ne_zero hc hz
  have hM : M c (z (p (σ 0))) ≠ 0 := M_ne_zero hc hz
  have hphaseFlip : wordPhase (N := N) x p σ w' = wordPhase (N := N) x p σ w :=
    Finset.prod_congr rfl fun k _ => by
      by_cases hku : k = u
      · subst k; simp [u, w', hσ, hpl, positionPhase]
      · simp [w', Function.update_of_ne hku]
  have hphase : wordPhase (N := N) x p σ' w' =
      z (p (σ 0)) ^ N * wordPhase (N := N) x p σ w := by
    simpa [σ', w', u, hσ, hpl, z_zero, hphaseFlip] using
      wordPhase_seam_swap (N := N) x p σ w' hn (by simp [w', u])
        (by simpa [w', Function.update_of_ne hu0.symm] using hZero)
  have hAmp : amplitude (anisotropy c) p σ =
      -(z (p (σ 0)) ^ N) *
        Complex.exp (I * (Bethe.theta (anisotropy c) (p (σ 0)) 0 : ℂ)) *
        amplitude (anisotropy c) p σ' := by
    have hAmp' := amplitude_seam_swap hc p hBE σ' hn (by rw [hσ0, hpl])
    rw [show σ' * Equiv.swap u 0 = σ by ext; simp [σ', u]] at hAmp'
    simpa [u, hσ'u] using hAmp'
  have hAmpCross : amplitude (anisotropy c) p σ' * z (p (σ 0)) ^ N *
      M c (z (p (σ 0))) = amplitude (anisotropy c) p σ * L c (z (p (σ 0))) := by
    rw [hAmp, Bethe.theta_swap (anisotropy c) 0 (p (σ 0)), Complex.ofReal_neg, mul_neg,
      Complex.exp_neg, exp_I_theta_zero_eq_neg_L_div_M hc hz]
    field_simp [hL, hM]
  let S : Finset (Fin (n + 1)) := (univ.erase u).erase 0
  have hcommon :
      (∏ k ∈ S, zeroRootLetterWeight c p σ' w' k) =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k :=
    Finset.prod_congr rfl fun k hk => by
      have hku : k ≠ u := (mem_erase.mp (mem_erase.mp hk).2).1
      have hk0 : k ≠ (0 : Fin (n + 1)) := (mem_erase.mp hk).1
      simp [σ', w', zeroRootLetterWeight, Function.update_of_ne hku,
        Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hku hk0]
  have hOld : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    unfold zeroRootRegularizedProduct
    rw [show σ.symm l = u from σ.injective (by simpa using hσ.symm),
      ← Finset.mul_prod_erase (univ.erase u) _ (Finset.mem_erase.mpr ⟨hu0.symm, mem_univ 0⟩)]
    simp [zeroRootLetterWeight, hZero, S]
  have hNew : zeroRootRegularizedProduct c p l σ' w' =
      M c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k := by
    unfold zeroRootRegularizedProduct
    rw [show σ'.symm l = 0 from σ'.injective (by simpa using hσ0.symm),
      ← Finset.mul_prod_erase (univ.erase 0) _ (Finset.mem_erase.mpr ⟨hu0, mem_univ u⟩),
      show (univ.erase 0).erase u = S by ext; simp [S, and_comm]]
    simp [zeroRootLetterWeight, w', hσ'u]
  unfold zeroRootRegularizedWordTerm
  rw [hOld, hNew, hcommon, hphase]
  linear_combination (c : ℂ) ^ 2 * (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
    wordPhase (N := N) x p σ w * hAmpCross

/-- The zero-root zipper move at an arbitrary cyclic edge. -/
theorem zeroRootRegularizedWordTerm_zipper_cyclic {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
    (a : Fin (n + 1)) (hσ : σ a = l) (hw : w a = true)
    (hnext : w (finRotate (n + 1) a) = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap a (finRotate (n + 1) a)) (Function.update w a false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  by_cases hlast : a = Fin.last n
  · subst a
    by_cases hn : 0 < n
    · simpa only [finRotate_last] using
        zeroRootRegularizedWordTerm_zipper_seam hc x p hp hinj l hpl hBE
          σ w hn hσ (by simpa [finRotate_last] using hnext)
    · obtain rfl : n = 0 := by omega
      rw [show σ * Equiv.swap (Fin.last 0) (finRotate 1 (Fin.last 0)) = σ by ext; simp]
      exact zeroRootRegularizedWordTerm_flipRoot (N := N) (n := 0) (c := c) x p l σ w 0 hσ hpl
  · let b : Fin n := ⟨a.val, by have := a.isLt; have : a.val ≠ n := fun h => hlast (Fin.ext h); omega⟩
    have hbc : b.castSucc = a := rfl
    have hbs : b.succ = finRotate (n + 1) a := (finRotate_of_lt b.isLt).symm
    simpa [hbc, hbs] using zeroRootRegularizedWordTerm_zipper_ordinary (N := N) hc x p hp hinj
      l hpl σ w b hσ (hbs.symm ▸ hnext)

end PottsDiscontinuity.BetheAnsatz
