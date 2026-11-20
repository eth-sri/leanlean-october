module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SmoothThetaAndGramKernels
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

variable (F : Type) [Field F] [NumberField F]

theorem initial_theta_diagonal :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ M : ℝ, 1 ≤ M → ∀ v : Ideal (𝓞 F) → ℂ, (∀ I, ‖v I‖ ≤ 1) →
        ‖initialTheta F (fun I => v I * (starRingEnd ℂ) (v I)) M‖ ≤ D * M := by
  obtain ⟨C, hC, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound F
  refine ⟨(5 / 2) * C, mul_nonneg (by norm_num) (by linarith), ?_⟩
  intro M hM v hv
  have hweight : ∀ t : ℝ, ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight t : ℂ))‖ ≤ 1 := by
    intro t
    have h : ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight t : ℂ))‖ = DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight t :=
      RCLike.norm_of_nonneg (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_nonneg t)
    rw [h]
    exact DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_le_one t
  have hterm : ∀ I : Ideal (𝓞 F),
      ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / M) : ℂ)) *
        (v I * (starRingEnd ℂ) (v I))‖ ≤ 1 := by
    intro I
    rw [norm_mul]
    refine mul_le_one₀ (hweight _) (norm_nonneg _) ?_
    rw [norm_mul, starRingEnd_apply, Complex.star_def, Complex.norm_conj]
    exact mul_le_one₀ (hv I) (norm_nonneg _) (hv I)
  let boundedNormIdeals₀ := DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)
  have h1 : ‖initialTheta F (fun I => v I * (starRingEnd ℂ) (v I)) M‖ ≤
      (((boundedNormIdeals₀).filter (fun I => I ≠ ⊥)).card : ℝ) := by
    rw [initialTheta]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ I ∈ (boundedNormIdeals₀).filter (fun I => I ≠ ⊥),
            ‖((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm I : ℝ) / M) : ℂ)) *
              (v I * (starRingEnd ℂ) (v I))‖
        ≤ ∑ _I ∈ (boundedNormIdeals₀).filter (fun I => I ≠ ⊥),
            (1 : ℝ) := Finset.sum_le_sum fun I _ => hterm I
      _ = (((boundedNormIdeals₀).filter (fun I => I ≠ ⊥)).card : ℝ) := by
          simp
  have h2 : (((boundedNormIdeals₀).filter (fun I => I ≠ ⊥)).card : ℝ) ≤
      (5 / 2) * C * M := by
    calc _
        ≤ ((boundedNormIdeals₀).card : ℝ) := (by
          exact_mod_cast Finset.card_filter_le _ _)
      _ ≤ C * ((5 / 2) * M) := hcount ((5 / 2) * M) (by linarith)
      _ = (5 / 2) * C * M := by ring
  linarith

theorem initialGram_diagonal_bound :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c),
        ∀ M : ℝ, 1 ≤ M → ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
          ‖initialGram F Q M b b‖ ≤ D * M := by
  obtain ⟨D, hD, hbound⟩ := initial_theta_diagonal F
  refine ⟨D, hD, ?_⟩
  intro c Q M hM b hb hbc
  exact hbound M hM (fun I => (Q.χ b) I)
    (fun I => DedekindZetaZeroFree.LargeSieve.quadraticFamily_norm_le_one Q hb hbc I)

end DedekindZetaZeroFree.LargeSieve.Sieve
