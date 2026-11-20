module

public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.MellinTailBounds
public import DedekindZetaZeroFree.Analysis.EntireFunctions.OrderOneFromLogarithmicGrowth
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TailRemainder

@[expose] public section

namespace DedekindZetaZeroFree.Hecke.WeakFEPair

variable (P : _root_.WeakFEPair ℂ) (hk : P.k = 1)
    (hdecay : ∃ A a p : ℝ, 0 ≤ A ∧ 0 < a ∧ 0 < p ∧ ∀ t : ℝ, 1 ≤ t → (‖P.f t - P.f₀‖ ≤ A * Real.exp (-a * Real.rpow t p) ∧ ‖P.g t - P.g₀‖ ≤ A * Real.exp (-a * Real.rpow t p)))

include hk hdecay in
theorem rlogrBound_Λ₀ :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ,
      ‖P.Λ₀ s‖ ≤ C * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨A, a, p, hA, ha, hp, hd⟩ := hdecay
  have hfm : MeasureTheory.AEStronglyMeasurable (fun t => P.f t - P.f₀)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    simpa using
      (mellinSplitRemainder_f_integrable P hk 1).aestronglyMeasurable
  have hgm : MeasureTheory.AEStronglyMeasurable (fun t => P.g t - P.g₀)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    simpa using
      (mellinSplitRemainder_g_integrable P hk 0).aestronglyMeasurable
  obtain ⟨Cf, Kf, hCf, hKf, hf⟩ := mellinTail_norm_le
    (fun t => P.f t - P.f₀) A a p hA ha hp hfm (fun t ht => (hd t ht).1)
  obtain ⟨Cg, Kg, hCg, hKg, hg⟩ := mellinTail_norm_le
    (fun t => P.g t - P.g₀) A a p hA ha hp hgm (fun t ht => (hd t ht).2)
  refine ⟨Cf + ‖P.ε‖ * Cg, max Kf Kg,
    add_nonneg hCf (mul_nonneg (norm_nonneg _) hCg),
    le_trans hKf (le_max_left _ _), ?_⟩
  intro s
  have hsecond := hg (1 - s) ‖s‖ (norm_nonneg _) (by
    simp only [Complex.sub_re, Complex.one_re]
    have := Complex.re_le_norm (-s)
    simp only [Complex.neg_re, norm_neg] at this
    linarith)
  simp only [sub_sub_cancel_left] at hsecond
  let exp₀ := Real.exp (max Kf Kg * (1 + ‖s‖) * Real.log (2 + ‖s‖))
  have hmax (K : ℝ) (hK : K ≤ max Kf Kg) :
      Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
        exp₀ := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (by positivity)) (Real.log_nonneg (by
        have := norm_nonneg s
        linarith))
  rw [mellinSplitRemainder P hk s]
  calc
    _ ≤ ‖∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) * (P.f t - P.f₀)‖ +
        ‖P.ε‖ * ‖∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s) * (P.g t - P.g₀)‖ := by
      simpa using norm_add_le
        (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) * (P.f t - P.f₀))
        (P.ε * ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s) * (P.g t - P.g₀))
    _ ≤ Cf * exp₀ +
        ‖P.ε‖ * (Cg * exp₀) :=
      add_le_add ((hf s ‖s‖ (norm_nonneg _) (by
        grind [Complex.re_le_norm])).trans (mul_le_mul_of_nonneg_left
        (hmax Kf (le_max_left _ _)) hCf)) (mul_le_mul_of_nonneg_left (hsecond.trans (mul_le_mul_of_nonneg_left
        (hmax Kg (le_max_right _ _)) hCg)) (norm_nonneg _))
    _ = _ := by ring

include hk hdecay in
theorem orderOneBound_Λ₀ :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      ‖P.Λ₀ s‖ ≤ C * Real.exp (Real.rpow ‖s‖ (1 + ε)) := by
  obtain ⟨C, K, hC, hK, hbound⟩ := rlogrBound_Λ₀ P hk hdecay
  solve_by_elim [orderOneBound_of_rlogr]

end DedekindZetaZeroFree.Hecke.WeakFEPair
