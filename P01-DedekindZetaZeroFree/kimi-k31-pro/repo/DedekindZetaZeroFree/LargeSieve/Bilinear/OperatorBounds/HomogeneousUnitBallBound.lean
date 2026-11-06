module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction
open scoped NumberField Classical

theorem unit_ball_lift
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K A : ℝ) (hA : 0 ≤ A)
    (hform : ∀ lam : Ideal (𝓞 F) → ℂ,
      Q2 F c Q W M N K lam ≤ A * energy F c N lam) :
    B2 F c Q W M N K ≤ A := by
  rw [B2]
  apply csSup_le
  · norm_num
  · rintro x (rfl | ⟨lam, hlam, rfl⟩)
    · positivity
    · calc Q2 F c Q W M N K lam ≤ A * energy F c N lam := hform lam
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hlam hA
        _ = A := mul_one A

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction

end
