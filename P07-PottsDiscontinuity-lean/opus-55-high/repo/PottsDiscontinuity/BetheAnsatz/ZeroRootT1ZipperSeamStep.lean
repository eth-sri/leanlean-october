module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamAmplitude
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperFinalStep

/-!
# The cyclic seam zipper move

The ordinary zipper identity also holds across the last-to-first edge. The
Bethe boundary relation and the `N`-shift in the position phase cancel exactly.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {N n : ℕ} {c : ℝ} (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
include c hc x p hp hinj hpl hBE
/-- Move a zero root across two consecutive L letters at the cyclic seam. -/
theorem zeroRootRegularizedWordTerm_zipper_seam (hn : 0 < n)
    (hσ : σ (Fin.last n) = l)
    (hZero : w 0 = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap (Fin.last n) 0) (Function.update w (Fin.last n) false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  let u := Fin.last n
  let σ' := σ * Equiv.swap u 0
  let w' := Function.update w u false
  have hu0 : u ≠ (0 : Fin (n + 1)) := by
    aesop
  have hσ0 : σ' 0 = l := by
    aesop
  have hσ'u : σ' u = σ 0 := by
    aesop
  have hσswap : σ' * Equiv.swap u 0 = σ := by
    aesop
  have hzero' : p (σ' 0) = 0 := by simp_all
  have hσ0ne : σ 0 ≠ l := by
    aesop
  have hpσ0 : p (σ 0) ≠ 0 := by
    grind
  have hz := z_ne_one (hp (σ 0)) hpσ0
  have hL := L_ne_zero hc hz
  have hM := M_ne_zero hc hz
  have hphaseFlip : wordPhase (N := N) x p σ w' =
      wordPhase (N := N) x p σ w := by
    apply Finset.prod_congr rfl
    intro k _
    by_cases hku : k = u
    · have hpσu : p (σ u) = 0 := by grind
      simp_all [positionPhase]
    · simp [w', Function.update_of_ne hku]
  have hphaseSwap := wordPhase_seam_swap (N := N) x p σ w' hn
    (by simp [w', u]) (by simpa [w', Function.update_of_ne hu0.symm] using hZero)
  have hphase : wordPhase (N := N) x p σ' w' =
      z (p (σ 0)) ^ N * wordPhase (N := N) x p σ w := by
    simpa [σ', w', u, hσ, hpl, z_zero, hphaseFlip] using hphaseSwap
  have hAmpSwap := amplitude_seam_swap hc p hBE σ' hn hzero'
  have hθ : Complex.exp (I * (Bethe.theta (anisotropy c)
      (p (σ 0)) 0 : ℂ)) = -M c (z (p (σ 0))) / L c (z (p (σ 0))) := by
    rw [Bethe.theta_swap (anisotropy c) 0 (p (σ 0)), Complex.ofReal_neg, mul_neg, Complex.exp_neg, (exp_I_theta_zero_eq_neg_L_div_M hc hz)]
    field_simp
  let S : Finset (Fin (n + 1)) := (univ.erase u).erase 0
  have hcommon :
      (∏ k ∈ S, zeroRootLetterWeight c p σ' w' k) =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hku := (mem_erase.mp (mem_erase.mp hk).2).1
    have hσk : σ' k = σ k := by simp [σ', Equiv.Perm.mul_apply, (Equiv.swap_apply_of_ne_of_ne hku ((mem_erase.mp hk).1))]
    simp [σ', w', zeroRootLetterWeight, Function.update_of_ne hku, hσk]
  have hOld : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    rw [zeroRootRegularizedProduct, show σ.symm l = u by simp [← hσ, u], ←
      (show zeroRootLetterWeight c p σ w 0 = L c (z (p (σ 0))) by simp [zeroRootLetterWeight, hZero])]
    exact (Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hu0.symm, mem_univ 0⟩)).symm
  have hNew : zeroRootRegularizedProduct c p l σ' w' =
      M c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k := by
    rw [zeroRootRegularizedProduct, show σ'.symm l = 0 by simp [← hσ0], ←
      (show zeroRootLetterWeight c p σ' w' u = M c (z (p (σ 0))) by simp [zeroRootLetterWeight, w', hσ'u]),
      show S = (univ.erase 0).erase u from Finset.erase_right_comm]
    exact (Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hu0, mem_univ u⟩)).symm
  unfold zeroRootRegularizedWordTerm
  rw [hOld, hNew, hcommon, hphase]
  calc
    _ = (amplitude (anisotropy c) p σ' * z (p (σ 0)) ^ N *
          M c (z (p (σ 0)))) * ((c : ℂ)^2 *
          (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
          wordPhase x p σ w) := by ring
    _ = (amplitude (anisotropy c) p σ * L c (z (p (σ 0)))) *
          ((c : ℂ)^2 * (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
          wordPhase (N := N) x p σ w) := by grind
    _ = _ := by ring

/-- The zero-root zipper move at an arbitrary cyclic edge. -/
theorem zeroRootRegularizedWordTerm_zipper_cyclic (a : Fin (n + 1)) (hσ : σ a = l) (hw : w a = true)
    (hnext : w (finRotate (n + 1) a) = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap a (finRotate (n + 1) a)) (Function.update w a false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  by_cases hlast : a = Fin.last n
  · subst a
    by_cases hn : 0 < n
    · simp_all [zeroRootRegularizedWordTerm_zipper_seam]
    · have hn0 : n = 0 := by omega
      subst n
      have hflip := zeroRootRegularizedWordTerm_flipRoot (N := N) (c := c) x p l σ w
        0 hσ hpl
      aesop
  · let b : Fin n := ⟨a.val, by
      grind⟩
    have hbc : b.castSucc = a := by
      rfl
    have hbs : b.succ = finRotate (n + 1) a := by
      rw [← hbc]
      simp
    have hstep := zeroRootRegularizedWordTerm_zipper_ordinary (N := N) hc x p hp hinj
      l hpl σ w b (by simp_all)
      (by simp_all)
    simp_all
end

end PottsDiscontinuity.BetheAnsatz
