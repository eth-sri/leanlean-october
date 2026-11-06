module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.AddedZero

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

abbrev Tuple (ι ) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι } {n } (e : ι ≃ Fin n)  := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι } {n } (e : ι ≃ Fin n)  :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι } [Fintype ι] (v : Tuple ι)  := ∏ i, v i

section
variable {ι : Type*}
include ι

section
variable {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι)
include n e v

lemma tupleEquiv_slot         (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  simp_all [coordinateEquiv]

lemma tupleEquiv_plain          j  :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  simp_all [coordinateEquiv]

end

theorem tupleProduct_reindex   [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n)  v  :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := (coordinateEquiv e).symm.prod_comp v

end

def originalFiniteCoefficient {ι } [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι)  :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n)  c   χ 
     R   t   ν   Wslot   P 
     W₁ W₂   X₁ X₂ Y₁ Y₂   b₁ b₂ s   v  :
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
