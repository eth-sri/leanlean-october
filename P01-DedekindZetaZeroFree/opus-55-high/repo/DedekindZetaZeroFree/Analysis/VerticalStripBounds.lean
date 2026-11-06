module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.GaussianStripRegulator

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

theorem strip_bound_of_tail_bound {a b : ℝ} (f : ℂ → ℂ)
    (hf : ContinuousOn f {s : ℂ | s.re ∈ Set.Icc a b})
    (htail : ∃ B : ℝ, 0 ≤ B ∧ ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (σ t : ℝ), σ ∈ Set.Icc a b →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := htail

  have hK : IsCompact {s : ℂ | s.re ∈ Set.Icc a b ∧ |s.im| ≤ 1} := by
    have h : IsCompact (Complex.equivRealProdCLM.toHomeomorph ⁻¹'
        (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1)) :=
      Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
        (isCompact_Icc.prod isCompact_Icc)
    convert h using 1
    ext s
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq, abs_le]
    tauto
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono (fun s hs => hs.1))
  refine ⟨max C B, hB0.trans (le_max_right _ _), fun σ t hσ => ?_⟩
  by_cases h1 : |t| ≤ 1
  ·
    simp_all
  ·
    exact (hB σ t hσ (not_le.mp h1).le).trans (le_max_right _ _)
