module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.AxisIdentity
public import DedekindZetaZeroFree.Nonvanishing.Mellin.HolomorphicZeroTransfer

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RecipeZeroFree

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

theorem zetaSCont_analytic :
    AnalyticOnNhd ℂ D.zetaSCont {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := by
  have hE : Differentiable ℂ (fun s : ℂ => ∏ v ∈ D.recipe.A.Sf,
      (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) := by
    apply Differentiable.fun_finsetProd
    intro v _
    unfold comparisonRealPower
    fun_prop
  have hfun : D.zetaSCont = fun s : ℂ => D.recipe.continuation.L s *
      ∏ v ∈ D.recipe.A.Sf,
        (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)) := rfl
  have hd : DifferentiableOn ℂ D.zetaSCont {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := by
    rw [hfun]
    exact (D.recipe.continuation.L_holo.mono (by
      rintro s ⟨hs1, hs2⟩
      exact ⟨lt_trans (by norm_num) hs1, hs2⟩)).mul hE.differentiableOn
  exact hd.analyticOnNhd ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne)

theorem recipe_zero_free (s : ℂ) (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) :
    D.zetaSCont s ≠ 0 := by
  have h1 : IsOpen {s : ℂ | 31 / 32 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hU : IsOpen {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := h1.inter h2
  have key := DedekindZetaZeroFree.mellin_holomorphic_zero_transfer (31 / 32) (by norm_num)
    D.zetaSCont (DedekindZetaZeroFree.Quantitative.MellinTransform.T D)
    (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2) * DedekindZetaZeroFree.Quantitative.Spectral.H D s)
    (zetaSCont_analytic D) (((DedekindZetaZeroFree.Quantitative.MellinHolomorphic.T_differentiableOn D).mono
      (fun z hz => hz.1)).analyticOnNhd hU) (((DedekindZetaZeroFree.Quantitative.SpectralData.numerator_differentiableOn D).mono
      (fun z hz => hz.1)).analyticOnNhd hU)
    (fun t : ℝ => DedekindZetaZeroFree.Quantitative.MellinAxis.zetaS_mul_T_axis D t)
    (fun s hs => DedekindZetaZeroFree.Quantitative.SpectralData.numerator_ne_zero D s hs.1)
  exact key s (⟨hs, hs1⟩)

end

end DedekindZetaZeroFree.Quantitative.RecipeZeroFree
