module
public import OAI.NumberTheory.DirichletL.Moments.ChildAssembly
public import OAI.NumberTheory.DirichletL.Moments.PlainChildEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDescent
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by pm_2939

set_option hygiene false in
macro "pf_53" x1:term:max x2:term:max : tactic => `(tactic| (
  have he (I : Ideal ActualEisensteinCubic.O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff ($x1:term) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff ($x1:term) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff ($x1:term) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff ($x1:term) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff ($x1:term) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right ($x2:term)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 ; ring
  have h := weighted_norm_sum L (fun I=> (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I=> ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff ($x1:term) χ ξ*F I χ ξ)
    r hr (fun I=> (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring))
theorem finite_ray_divisor_bound (L : Finset (Ideal O)) (D E : O)
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by pf_53 (phaseTable D E) (phaseTable_mass D E)

end SevenEighths.CenteredMomentSecondDescent

end

end OAI
