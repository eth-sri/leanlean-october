module
public import OAI.NumberTheory.DirichletL.Moments.FirstColumns
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstColumns CenteredMomentMobiusRegroup CenteredMomentChildAssembly
open CenteredMomentGaussEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def originalPhase (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
    (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b))

theorem originalPhase_eq (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    originalPhase e r ρ a b=firstExtension e r ρ a b :=
  first_phase_columns e r a b ρ hρ ha hb hpa hpb hab

theorem first_divisor_pair {α β : Type*} (L : Ideal O)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ) (h : O)
    (i : α) (j : β) (K : ℂ) :
    (if L∣Ideal.span {a i} ∧ L∣Ideal.span {b j} then
      firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K else 0) =
    ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*
        ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
          star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
            gaussRow (b j) (hb j) (-h)))*K := by
  by_cases hi : L∣Ideal.span {a i}
  · by_cases hj : L∣Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [firstExtension_separated e r (a i) (b j) ρ (ha i) (hb j)]
      simp only [Finset.mul_sum,Finset.sum_mul,star_mul,rayCharacter_inverse_star]
      pm_3397 χ hχ ξ hξ
      ring
    pm_1279
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,mul_zero,Finset.sum_const_zero]

theorem finite_first_children {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (h : O) (K : α → β → ℂ) :
    (∑ i∈S,∑ j∈T,(if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
      (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j) =
    ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
      (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e *
        ∑ χ : RayCharacter,∑ ξ : RayCharacter,
          pairCoeff firstPhaseTable χ ξ*∑ i∈S,∑ j∈T,
            ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
              star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                gaussRow (b j) (hb j) (-h)))*K i j := by
  have ht (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
        (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
          (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j else 0 := by
    pm_7690 hc
    · simp only [hc,ite_true,originalPhase_eq e r (a i) (b j) ρ hρ (ha i) (hb j) (hpa i) (hpb j) hc]
    · simp only [hc,ite_false,zero_mul]
  simp_rw [ht]
  rw [finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1)]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [first_divisor_pair L a b ha hb c d e r ρ h]
  simp_rw [← Finset.mul_sum (s:=T),← Finset.mul_sum (s:=S)]
  rw [pair_ray_fubini]
  ring

end SevenEighths.CenteredMomentFirstAssembly

end

end OAI
