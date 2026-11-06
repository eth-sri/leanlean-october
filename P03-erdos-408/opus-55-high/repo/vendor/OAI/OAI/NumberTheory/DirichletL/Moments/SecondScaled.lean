module

public import OAI.NumberTheory.DirichletL.Moments.SecondDescent
public import OAI.NumberTheory.DirichletL.Moments.Partition
public import OAI.NumberTheory.DirichletL.Moments.ChildRows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def movingCoefficient {α : Type*} (A : ActualEisensteinCubic.O) (a : α → ActualEisensteinCubic.O) (c : α → ℂ) (i : α) : ℂ :=
  c i*idealRowHom A (Ideal.span {a i})

theorem divisorCoefficient_moving {α : Type*} (L : Ideal ActualEisensteinCubic.O) (A : ActualEisensteinCubic.O) (a : α → ActualEisensteinCubic.O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  grind

theorem actual_scaled_row_children {α β : Type*} (rows : Finset ActualEisensteinCubic.O) (S : Finset α) (T : Finset β)
    (D E A₀ : ActualEisensteinCubic.O) (a : α → ActualEisensteinCubic.O) (b : β → ActualEisensteinCubic.O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : ActualEisensteinCubic.O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : ActualEisensteinCubic.O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

end SevenEighths.CenteredMomentSecondScaled

end

end OAI
