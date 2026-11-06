module

public import OAI.NumberTheory.DirichletL.Moments.ChildEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentReflectedChild
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth CenteredMomentChildEnergy

theorem finite_reflected_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset ActualEisensteinCubic.O)
    (hW : ∀ z : ActualEisensteinCubic.O, 0 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c (-z)‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hh := finite_energy_le_gaussEnergy S a ha c W K hK (rows.image Neg.neg) hW
    (by simp_all)
  simp_all

theorem whole_kernel_reflected_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset ActualEisensteinCubic.O) (S : Finset α) (T : Finset β)
        (a : α → ActualEisensteinCubic.O) (b : β → ActualEisensteinCubic.O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : ActualEisensteinCubic.O → ℝ) (η : ActualEisensteinCubic.O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : ActualEisensteinCubic.O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) (-z))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) (-z)) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (by positivity)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_reflected_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentReflectedChild

end

end OAI
