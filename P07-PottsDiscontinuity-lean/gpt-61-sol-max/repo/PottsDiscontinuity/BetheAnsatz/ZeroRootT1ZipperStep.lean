module
public import Mathlib

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
    (w : Fin (n + 1) → Bool) (k : Fin (n + 1))  :=
  if w k then L c (z (p (σ k))) else M c (z (p (σ k)))

/-- The regularized product omits the slot occupied by the zero root. -/
noncomputable def zeroRootRegularizedProduct {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)  :=
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
  
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hkb : k = a.castSucc
  · subst k
    simp [hb]
  · by_cases hkc : k = a.succ
    · simp_all [wordPositions]
    · grind [wordPositions]

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
  have hbd : b ≠ d := LT.lt.ne Fin.castSucc_lt_succ
  have hσb : σ b = l := hsig
  have hσd : σ d ≠ l := by
    aesop
  
  have hzd  := z_ne_one (hp (σ d)) (by
                                      grind)
  have hM  := M_ne_zero hc hzd
  
  have hRoot' : (σ * Equiv.swap b d).symm l = d := by
    apply (σ * Equiv.swap b d).injective
    simp_all
   
  
  have hcw' : w d = true := hcw
  
  let S  :=  (univ.erase b).erase d 
  have hcommon :
       ∏ k ∈ S, zeroRootLetterWeight c p (σ * Equiv.swap b d)
          (Function.update w b false) k  =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkb : k ≠ b := by
      grind
    
    have hσk : (σ * Equiv.swap b d) k = σ k := by
      aesop
    simp [zeroRootLetterWeight, Function.update_of_ne hkb, hσk]
  have hOld : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ d))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    
    have hletter : zeroRootLetterWeight c p σ w d =
        L c (z (p (σ d))) := by
      simp [zeroRootLetterWeight, hcw']
    unfold zeroRootRegularizedProduct
    rw [(by
           apply σ.injective
           simpa using hσb.symm : σ.symm l = b)]
    calc
       ∏ k ∈ univ.erase b, zeroRootLetterWeight c p σ w k  =
          zeroRootLetterWeight c p σ w d *
            ∏ k ∈ (univ.erase b).erase d, zeroRootLetterWeight c p σ w k :=
        (Finset.mul_prod_erase (univ.erase b)
           (zeroRootLetterWeight c p σ w) 
          (Finset.mem_erase.mpr ⟨hbd.symm, mem_univ d⟩)).symm
      _ = L c (z (p (σ d))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
        rw [hletter]
  have hNew : zeroRootRegularizedProduct c p l
      (σ * Equiv.swap b d) (Function.update w b false) =
      M c (z (p (σ d))) * ∏ k ∈ S,
        zeroRootLetterWeight c p (σ * Equiv.swap b d)
          (Function.update w b false) k := by
    have hletter : zeroRootLetterWeight c p (σ * Equiv.swap b d)
        (Function.update w b false) b = M c (z (p (σ d))) := by
      simp [zeroRootLetterWeight]
    have hset : (univ.erase d).erase b = S := by
      grind
    unfold zeroRootRegularizedProduct
    rw [hRoot']
    calc
       ∏ k ∈ univ.erase d,
          zeroRootLetterWeight c p (σ * Equiv.swap b d)
            (Function.update w b false) k  =
          zeroRootLetterWeight c p (σ * Equiv.swap b d)
              (Function.update w b false) b *
            ∏ k ∈ (univ.erase d).erase b,
              zeroRootLetterWeight c p (σ * Equiv.swap b d)
                (Function.update w b false) k :=
        (Finset.mul_prod_erase (univ.erase d)
          (fun k => zeroRootLetterWeight c p (σ * Equiv.swap b d)
            (Function.update w b false) k)
          (Finset.mem_erase.mpr ⟨hbd, mem_univ b⟩)).symm
      _ = M c (z (p (σ d))) * ∏ k ∈ S,
            zeroRootLetterWeight c p (σ * Equiv.swap b d)
              (Function.update w b false) k := by
        rw [hletter, hset]
  
  
  
  have hAmp : amplitude (anisotropy c) p (σ * Equiv.swap b d) *
      M c (z (p (σ d))) =
    amplitude (anisotropy c) p σ * L c (z (p (σ d))) := by
    have hθ := exp_I_theta_zero_eq_neg_L_div_M hc hzd
    
    have hswap := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ
      (a := b) (b := d) (by simp [b, d])
    grind
  have hAP : amplitude (anisotropy c) p (σ * Equiv.swap b d) *
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
        (Function.update w b false) =
    amplitude (anisotropy c) p σ * zeroRootRegularizedProduct c p l σ w := by
    grind
  unfold zeroRootRegularizedWordTerm
  rw [ wordPhase_zipper_ordinary (N := N) x p σ w a (by rw [hsig]; exact hpl) hcw ]
  change amplitude (anisotropy c) p (σ * Equiv.swap b d) *  c ^2 *
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
        (Function.update w b false) * wordPhase (N := N) x p σ w =
    amplitude (anisotropy c) p σ *  c ^2 *
      zeroRootRegularizedProduct c p l σ w * wordPhase (N := N) x p σ w
  calc
    _ =   amplitude (anisotropy c) p (σ * Equiv.swap b d) *
          zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
            (Function.update w b false)  *  c ^2  *
          wordPhase (N := N) x p σ w := by ring_nf
    _ =   amplitude (anisotropy c) p σ *
          zeroRootRegularizedProduct c p l σ w  *  c ^2  *
          wordPhase (N := N) x p σ w := by rw [hAP]
    _ = amplitude (anisotropy c) p σ *  c ^2 *
        zeroRootRegularizedProduct c p l σ w * wordPhase (N := N) x p σ w := by ring

end PottsDiscontinuity.BetheAnsatz
