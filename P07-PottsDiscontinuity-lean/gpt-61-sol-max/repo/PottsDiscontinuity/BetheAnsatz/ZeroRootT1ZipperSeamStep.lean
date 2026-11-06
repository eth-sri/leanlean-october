module
public import Mathlib

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

section

variable {N n : ℕ} {c : ℝ} (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
include hc hp hinj hpl hBE

/-- Move a zero root across two consecutive L letters at the cyclic seam. -/
theorem zeroRootRegularizedWordTerm_zipper_seam  (hn : 0 < n)
    (hσ : σ (Fin.last n) = l)
    (hZero : w 0 = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap (Fin.last n) 0) (Function.update w (Fin.last n) false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  let u := Fin.last n
  let σ' := σ * Equiv.swap u 0
  let w' := Function.update w u false
  have hu0 : u ≠  0  := by
    aesop
  have hσ0 : σ' 0 = l := by
    aesop
  have hσ'u : σ' u = σ 0 := by
    aesop
  have hσswap : σ' * Equiv.swap u 0 = σ := by
    
    simp [σ']
  
  have hσ0ne : σ 0 ≠ l := by
    
    aesop
  
  have hz  := z_ne_one (hp (σ 0)) (by
                                     grind)
  have hL  := L_ne_zero hc hz
  
  have hphaseFlip : wordPhase (N := N) x p σ w' =
      wordPhase (N := N) x p σ w := by
    
    apply Finset.prod_congr rfl
    intro k _
    by_cases hku : k = u
    · subst k
      
      simp [(by rw [hσ, hpl] : p (σ u) = 0), positionPhase]
    · simp [w', Function.update_of_ne hku]
  have hphaseSwap := wordPhase_seam_swap (N := N) x p σ w' hn
    (by simp [w', u]) (by simpa [w', Function.update_of_ne hu0.symm] using hZero)
  
  have hAmpSwap := amplitude_seam_swap hc p hBE σ' hn (by rw [hσ0, hpl])
  have hAmp : amplitude (anisotropy c) p σ =
      - z (p (σ 0)) ^ N  *
        Complex.exp (I *  Bethe.theta (anisotropy c) (p (σ 0)) 0 ) *
        amplitude (anisotropy c) p σ' := by
    grind
  
  
  have hθ : Complex.exp (I *  Bethe.theta (anisotropy c)
      (p (σ 0)) 0 ) = -M c (z (p (σ 0))) / L c (z (p (σ 0))) := by
    rw [(Bethe.theta_swap (anisotropy c) 0 (p (σ 0))), Complex.ofReal_neg, mul_neg, Complex.exp_neg,  exp_I_theta_zero_eq_neg_L_div_M hc hz ]
    field_simp 
  
  let S  := (univ.erase u).erase 0
  have hcommon :
       ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k  =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hku  := (mem_erase.mp (mem_erase.mp hk).2).1
    
    have hswap  := Equiv.swap_apply_of_ne_of_ne hku ((mem_erase.mp hk).1)
    have hσk : σ' k = σ k := by simp [σ', hswap]
    simp [w', zeroRootLetterWeight, Function.update_of_ne hku, hσk]
  have hroot : σ.symm l = u := by
    apply σ.injective
    simpa using hσ.symm
  have hroot' : σ'.symm l = 0 := by
    apply σ'.injective
    simpa using hσ0.symm
  have hletter : zeroRootLetterWeight c p σ w 0 = L c (z (p (σ 0))) := by
    simp [zeroRootLetterWeight, hZero]
  have hletter' : zeroRootLetterWeight c p σ' w' u =
      M c (z (p (σ 0))) := by
    simp [zeroRootLetterWeight, w', hσ'u]
  
  
  unfold zeroRootRegularizedWordTerm
  rw [(by
         unfold zeroRootRegularizedProduct
         rw [hroot]
         calc
            ∏ k ∈ univ.erase u, zeroRootLetterWeight c p σ w k  =
               zeroRootLetterWeight c p σ w 0 *
                 ∏ k ∈ (univ.erase u).erase 0, zeroRootLetterWeight c p σ w k :=
             (Finset.mul_prod_erase (univ.erase u)
               ((zeroRootLetterWeight c p σ w))
               (Finset.mem_erase.mpr ⟨hu0.symm, mem_univ 0⟩)).symm
           _ = L c (z (p (σ 0))) *
                 ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by rw [hletter] : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k), (by
               unfold zeroRootRegularizedProduct
               rw [hroot']
               have hset : (univ.erase 0).erase u = S := by
                 exact erase_right_comm
               calc
                  ∏ k ∈ univ.erase 0, zeroRootLetterWeight c p σ' w' k  =
                     zeroRootLetterWeight c p σ' w' u *
                       ∏ k ∈ (univ.erase 0).erase u, zeroRootLetterWeight c p σ' w' k :=
                   (Finset.mul_prod_erase (univ.erase 0)
                     ((zeroRootLetterWeight c p σ' w'))
                     (Finset.mem_erase.mpr ⟨hu0, mem_univ u⟩)).symm
                 _ = M c (z (p (σ 0))) *
                       ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k := by rw [hletter', hset] : zeroRootRegularizedProduct c p l σ' w' =
      M c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k), hcommon, (by
                              aesop : wordPhase (N := N) x p σ' w' =
      z (p (σ 0)) ^ N * wordPhase (N := N) x p σ w)]
  calc
    _ =  amplitude (anisotropy c) p σ' * z (p (σ 0)) ^ N *
          M c (z (p (σ 0)))  * ( c ^2 *
          (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
          wordPhase (N := N) x p σ w) := by ring
    _ =  amplitude (anisotropy c) p σ * L c (z (p (σ 0)))  *
          ( c ^2 * (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
          wordPhase (N := N) x p σ w) := by rw [(by
                                                   grind : amplitude (anisotropy c) p σ' * z (p (σ 0)) ^ N *
      M c (z (p (σ 0))) = amplitude (anisotropy c) p σ * L c (z (p (σ 0))))]
    _ = _ := by ring

/-- The zero-root zipper move at an arbitrary cyclic edge. -/
theorem zeroRootRegularizedWordTerm_zipper_cyclic 
    (a : Fin (n + 1)) (hσ : σ a = l) (hw : w a = true)
    (hnext : w (finRotate (n + 1) a) = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap a (finRotate (n + 1) a)) (Function.update w a false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  by_cases hlast : a = Fin.last n
  · subst a
    by_cases hn : 0 < n
    · simp_all [zeroRootRegularizedWordTerm_zipper_seam]
    · aesop
         (add
          unsafe
            apply [_root_.PottsDiscontinuity.BetheAnsatz.zeroRootRegularizedWordTerm_flipRoot, _root_.congrArg,
              _root_.of_eq_true, _root_.Eq.trans, _root_.congr, _root_.congrFun', _root_.Fin.last_zero,
              _root_.Equiv.swap_self, _root_.eq_self, _root_.Eq.symm])
  · let b : Fin n := ⟨a.val, by
      grind⟩
    have hbc : b.castSucc = a := by
      
      rfl
    have hbs : b.succ = finRotate (n + 1) a := (finRotate_of_lt b.isLt).symm
    
    simpa [hbc, hbs] using  zeroRootRegularizedWordTerm_zipper_ordinary (N := N) hc x p hp hinj
                              l hpl σ w b (hσ)
                              (by rw [hbs]; exact hnext) 

end

end PottsDiscontinuity.BetheAnsatz
