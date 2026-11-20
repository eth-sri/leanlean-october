module

public import HypoellipticAleksandrov.Parabolic.HigherOrderNestedProductBoxChain
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftWeakDerivativeFamilyAddTwo
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2NormTruncate
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization

/-!
# Finite iteration of the generic pre-lift estimate

This module iterates the one-weight generic pre-lift theorem along a finite
nested product-box chain.  The resulting family retains the selected
weight-two representatives literally and satisfies a single seed-plus-source
energy estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise

private theorem chainBox_subset_zero
    {d N : ℕ} {q₀ s₀ s₁ q₁ : ℝ}
    {Ω O₀ O : Set (PDE.Vec d)}
    {left right : ℕ → ℝ} {spatial : ℕ → Set (PDE.Vec d)}
    (hchain : IsHigherOrderNestedProductBoxChain
      d N q₀ s₀ s₁ q₁ Ω O₀ O left right spatial)
    {k : ℕ} (hk : k ≤ N + 2) :
    Set.Ioo (left k) (right k) ×ˢ spatial k ⊆
      Set.Ioo (left 0) (right 0) ×ˢ spatial 0 := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih =>
      have hklt : k < N + 2 := by omega
      rcases hchain.step hklt with
        ⟨hl, _, hr, _, _, _, _, hs⟩
      exact (Set.prod_mono (Set.Ioo_subset_Ioo hl.le hr.le)
        (subset_closure.trans hs)).trans (ih (by omega))

/-- Iterate exactly `N` generic pre-lift calls along the first `N` gaps of a
higher-order nested product-box chain. -/
theorem exists_iterated_genericPrelift_weakDerivativeFamily_estimate
    (d N : ℕ) (hN : 1 ≤ N)
    (q₀ s₀ s₁ q₁ : ℝ)
    (Ω O₀ O : Set (PDE.Vec d))
    (left right : ℕ → ℝ)
    (spatial : ℕ → Set (PDE.Vec d))
    (hchain : IsHigherOrderNestedProductBoxChain
      d N q₀ s₀ s₁ q₁ Ω O₀ O left right spatial)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (BaMax : Fin d → Fin d →
      ParabolicDerivativeIndex d (N + 1) → ℝ)
    (BbMax : Fin d → ParabolicDerivativeIndex d N → ℝ)
    (BcMax : ParabolicDerivativeIndex d N → ℝ)
    (hBaMax : ∀ i j alpha, 0 ≤ BaMax i j alpha)
    (hBbMax : ∀ j alpha, 0 ≤ BbMax j alpha)
    (hBcMax : ∀ alpha, 0 ≤ BcMax alpha) :
    ∃ Citer : ℝ, 0 ≤ Citer ∧
      ∀ (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ)
        (u : TimeVelocity d → ℝ)
        (Dseed : ParabolicWeakDerivativeFamily d 2
          (Set.Ioo (left 0) (right 0) ×ˢ spatial 0) u)
        (Emax : ParabolicWeakDerivativeFamily d N
          (Set.Ioo (left 0) (right 0) ×ˢ spatial 0)
          (fun z : TimeVelocity d => F z.1 z.2)),
        PreliftCoefficientBounds (Ioo (left 0) (right 0) ×ˢ spatial 0)
          lam Lam BaMax BbMax BcMax a b c →
        ((fun z : TimeVelocity d =>
          Dseed.representative
              (ParabolicDerivativeIndex.timeOne d) z +
            (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j *
              Dseed.representative
                (ParabolicDerivativeIndex.velocityTwo j i) z) +
            (∑ j : Fin d, b z.1 z.2 j *
              Dseed.representative
                (ParabolicDerivativeIndex.velocityOne j) z) +
            c z.1 z.2 * Dseed.representative
              (ParabolicDerivativeIndex.zeroTwo d) z)
          =ᵐ[timeVelocityVolumeOn
            (Set.Ioo (left 0) (right 0) ×ˢ spatial 0)]
          fun z : TimeVelocity d => F z.1 z.2) →
        ∃ Dcore : ParabolicWeakDerivativeFamily d (N + 2)
            (Set.Ioo (left N) (right N) ×ˢ spatial N) u,
          (∀ alpha : ParabolicDerivativeIndex d 2,
            Dcore.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ N + 2) alpha) =
              Dseed.representative alpha) ∧
          ParabolicWeakDerivativeFamily.squaredL2Norm Dcore ≤
            Citer *
              (ParabolicWeakDerivativeFamily.squaredL2Norm Dseed +
                ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
  classical
  let Ba : (k : ℕ) → k < N → Fin d → Fin d →
      ParabolicDerivativeIndex d (k + 2) → ℝ := fun k hk i j alpha =>
    BaMax i j (ParabolicDerivativeIndex.castLE (by omega) alpha)
  let Bb : (k : ℕ) → k < N → Fin d →
      ParabolicDerivativeIndex d (k + 1) → ℝ := fun k hk j alpha =>
    BbMax j (ParabolicDerivativeIndex.castLE (by omega) alpha)
  let Bc : (k : ℕ) → k < N → ParabolicDerivativeIndex d (k + 1) → ℝ :=
    fun k hk alpha => BcMax (ParabolicDerivativeIndex.castLE (by omega) alpha)
  let hstepConstant (k : ℕ) (hk : k < N) :=
    let g := hchain.step (show k < N + 2 by omega)
    exists_genericPrelift_addTwo_weakDerivativeFamily_estimate
      d (k + 1) (by omega) (left k) (left (k + 1)) (right (k + 1))
      (right k) g.1 g.2.1 g.2.2.1 (spatial k) (spatial (k + 1)) g.2.2.2.1 g.2.2.2.2.1
      g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2 lam Lam hlam hlamLam (Ba k hk) (Bb k hk) (Bc k hk)
      (fun i j alpha => hBaMax i j _) (fun j alpha => hBbMax j _)
      (fun alpha => hBcMax _)
  let Cstep : ℕ → ℝ := fun k => if hk : k < N then Classical.choose (hstepConstant k hk) else 0
  have hCstep (k : ℕ) (hk : k < N) : 0 ≤ Cstep k := by
    simp only [Cstep, dif_pos hk]
    exact (Classical.choose_spec (hstepConstant k hk)).1
  have hCstep_nonneg (k : ℕ) : 0 ≤ Cstep k := by
    by_cases hk : k < N
    · exact hCstep k hk
    · simp only [Cstep, dif_neg hk, le_refl]
  let K : ℕ → ℝ := fun k => Nat.rec 1 (fun n x => Cstep n * (x + 1)) k
  have hK : ∀ k, 0 ≤ K k := by
    intro k
    induction k with
    | zero => simp only [K, Nat.rec_zero, zero_le_one]
    | succ k ih =>
        have hsum : 0 ≤ K k + 1 := add_nonneg ih zero_le_one
        have hprod : 0 ≤ Cstep k * (K k + 1) :=
          mul_nonneg (hCstep_nonneg k) hsum
        simpa only [K, Nat.rec_add_one] using hprod
  refine ⟨K N, hK N, ?_⟩
  intro a b c F u Dseed Emax hcoeff hEq
  let Q : ℕ → Set (TimeVelocity d) := fun k => Set.Ioo (left k) (right k) ×ˢ spatial k
  have hQsub (k : ℕ) (hk : k ≤ N) : Q k ⊆ Q 0 := chainBox_subset_zero hchain (by omega)
  have hiterate : ∀ k, k ≤ N →
      ∃ D : ParabolicWeakDerivativeFamily d (k + 2) (Q k) u,
        (∀ alpha : ParabolicDerivativeIndex d 2,
          D.representative (ParabolicDerivativeIndex.castLE (by omega) alpha) =
            Dseed.representative alpha) ∧
        ParabolicWeakDerivativeFamily.squaredL2Norm D ≤ K k *
          (ParabolicWeakDerivativeFamily.squaredL2Norm Dseed +
            ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
    intro k hk
    induction k with
    | zero =>
        refine ⟨Dseed, ?_, ?_⟩
        · intro alpha; rfl
        · simp only [K, Nat.rec_zero, one_mul]
          exact le_add_of_nonneg_right
            (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg Emax)
    | succ k ih =>
        have hkN : k < N := by omega
        obtain ⟨D, hDseed, hDnorm⟩ := ih (by omega)
        have hsub := hQsub k (by omega)
        let E : ParabolicWeakDerivativeFamily d (k + 1) (Q k)
            (fun z : TimeVelocity d => F z.1 z.2) :=
          (Emax.truncate (by omega)).restrict hsub
        have hEnorm : ParabolicWeakDerivativeFamily.squaredL2Norm E ≤
            ParabolicWeakDerivativeFamily.squaredL2Norm Emax :=
          (ParabolicWeakDerivativeFamily.squaredL2Norm_restrict_le
            (Emax.truncate (by omega)) hsub).trans
            (ParabolicWeakDerivativeFamily.squaredL2Norm_truncate_le Emax (by omega))
        have hEqD : (D.backwardOperator (by omega) a b c
          =ᵐ[timeVelocityVolumeOn (Q k)] fun z => F z.1 z.2) := by
          filter_upwards [hEq.filter_mono
            (ae_mono (Measure.restrict_mono_set volume hsub))] with z hz
          simpa only [ParabolicWeakDerivativeFamily.backwardOperator, hDseed] using hz
        have hcall' := (Classical.choose_spec (hstepConstant k hkN)).2 a b c F u D E
          (hcoeff.restrict hsub (show k + 1 ≤ N by omega)) hEqD
        have hCstep_eq : Cstep k =
            Classical.choose (hstepConstant k hkN) := by
          simp only [Cstep, dif_pos hkN]
        rw [← hCstep_eq] at hcall'
        rcases hcall' with ⟨H, Dnext, hDold, _, _, hDnextNorm⟩
        refine ⟨Dnext, ?_, ?_⟩
        · intro alpha
          exact (hDold (ParabolicDerivativeIndex.castLE (by omega) alpha)).trans
            (hDseed alpha)
        · calc
            ParabolicWeakDerivativeFamily.squaredL2Norm Dnext ≤
                Cstep k * (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                  ParabolicWeakDerivativeFamily.squaredL2Norm E) := hDnextNorm
            _ ≤ Cstep k * (K k *
                  (ParabolicWeakDerivativeFamily.squaredL2Norm Dseed +
                    ParabolicWeakDerivativeFamily.squaredL2Norm Emax) +
                  ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
                exact mul_le_mul_of_nonneg_left (add_le_add hDnorm hEnorm) (hCstep k hkN)
            _ ≤ Cstep k * ((K k + 1) *
                  (ParabolicWeakDerivativeFamily.squaredL2Norm Dseed +
                    ParabolicWeakDerivativeFamily.squaredL2Norm Emax)) := by
                apply mul_le_mul_of_nonneg_left _ (hCstep k hkN)
                have hseed := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg Dseed
                ring_nf
                nlinarith [hK k,
                  ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg Emax]
            _ = K (k + 1) *
                  (ParabolicWeakDerivativeFamily.squaredL2Norm Dseed +
                    ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
                change Cstep k * ((K k + 1) * _) =
                  (Cstep k * (K k + 1)) * _
                ring
  simpa only [Q] using hiterate N le_rfl

end HypoellipticAleksandrov.Parabolic
