module
public import OAI.NumberTheory.DirichletL.Moments.AddedZero
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

section
variable {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι)
include ι n e v
lemma tupleEquiv_slot (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  pm_7788
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    aesop
  grind

lemma tupleEquiv_plain (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  pm_7788
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    aesop
  grind
end

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
