module
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.GlobalEstimatesFromShells
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.FiniteSupportQuadraticForms

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma card_boundedNormIdeals_eq_natCard (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card =
      Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} := by
  have hset : ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X) : Set (Ideal (𝓞 F))) =
      {I | (Ideal.absNorm I : ℝ) ≤ X} := by
    ext I; exact DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals
  rw [(Set.ncard_coe_finset (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X)).symm, hset]
  exact (Nat.card_coe_set_eq ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X})).symm

private alias exists_ideal_count_bound := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound

theorem shell_bound_to_target_finsum
    (F : Type) [Field F] [NumberField F]
    (𝔠 : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F 𝔠)
    (hShell : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
        (∑ 𝔞 ∈ paperShell F 𝔠 M,
          ‖∑ 𝔟 ∈ paperShell F 𝔠 N, lam 𝔟 * (𝓕.χ 𝔟) 𝔞‖ ^ 2) ≤
            C * (M * N) ^ δ * (M + N) *
              ∑ 𝔟 ∈ paperShell F 𝔠 N, ‖lam 𝔟‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ), 1 ≤ M → 1 ≤ N →
        ∑ᶠ 𝔞 : Ideal (𝓞 F), (if Squarefree 𝔞 ∧ 𝔞 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ M then
            ‖∑ᶠ 𝔟 : Ideal (𝓞 F), (if Squarefree 𝔟 ∧ 𝔟 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ N then
              lam 𝔟 * (𝓕.χ 𝔟) 𝔞 else 0)‖ ^ 2 else 0) ≤
          D * (M * N) ^ ε * (M + N) *
            ∑ᶠ 𝔟 : Ideal (𝓞 F), (if Squarefree 𝔟 ∧ 𝔟 ⊔ 𝔠 = ⊤ ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ N then
              ‖lam 𝔟‖ ^ 2 else 0) := by
  classical
  obtain ⟨A, hA1, hcount⟩ := exists_ideal_count_bound F
  intro ε hε
  obtain ⟨D, hD0, hD⟩ := global_from_shell_bounds F 𝔠 𝓕 A hA1 hcount hShell ε hε
  refine ⟨D, hD0, ?_⟩
  intro M N lam hM hN
  rw [finsum_energy_eq_sum, finsum_coeff_norm_sq_eq_sum]
  exact hD M N hM hN lam

end DedekindZetaZeroFree.LargeSieve.Sieve
