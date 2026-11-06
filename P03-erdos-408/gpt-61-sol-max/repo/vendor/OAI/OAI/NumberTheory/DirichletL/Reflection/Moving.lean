module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.Rows

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section


def reflectedExponent {φ ρ σ } (jF : φ → ℕ) : φ ⊕ (ρ ⊕ σ) → ℕ :=
  Sum.elim jF (Sum.elim (fun _ => 1) (fun _ => 0))

def frozenIndices (φ ρ σ ) [Fintype φ]  :=
  @Finset.image φ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) Sum.inl Finset.univ

def residualIndices (φ ρ σ ) [Fintype ρ]  :=
  @Finset.image ρ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inl) Finset.univ

def slotIndices (φ ρ σ ) [Fintype σ]  :=
  @Finset.image σ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inr) Finset.univ

lemma reflected_indices_partition  φ ρ σ  [Fintype φ] [Fintype ρ] [Fintype σ] :
    Disjoint (residualIndices φ ρ σ) (slotIndices φ ρ σ) ∧
    Disjoint (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) (frozenIndices φ ρ σ) ∧
    (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) ∪ frozenIndices φ ρ σ = Finset.univ := by
  classical
  simp only [residualIndices, slotIndices, frozenIndices, Finset.disjoint_left,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Function.comp_apply]
  grind

lemma reflected_residual_exponent  {φ ρ σ}  [Fintype ρ]  jF  :
    ∀ i ∈ residualIndices φ ρ σ, reflectedExponent jF i = 1 := by
  let : DecidableEq (φ ⊕ (ρ ⊕ σ)) := Classical.decEq _
  rintro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

namespace PrimeFamily
section
variable {φ σ : Type*} [Fintype φ] [Fintype σ] (F : PrimeFamily φ) (K : Ideal ActualEisensteinCubic.O)

lemma reflected_residual_product      
         hK   S  :
    (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = K := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, residualIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inl_injective).injOn]
  exact residual_product K hK

lemma reflected_slot_product      
         hK   S  :
    (∏ i ∈ slotIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = ∏ i, S.ideal i := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, slotIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inr_injective).injOn]
  rfl

end
end PrimeFamily

end
end SevenEighths.InverseReflectedPhase

end OAI
