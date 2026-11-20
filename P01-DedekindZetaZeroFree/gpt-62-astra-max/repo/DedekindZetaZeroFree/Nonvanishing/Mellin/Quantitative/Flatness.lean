module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralRegularity
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ShiftedKernelFlatness

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.TransformFlat

noncomputable section

open DedekindZetaZeroFree NumberField Filter Asymptotics Topology MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def g (Z : ℝ) : ℂ := ((Z ^ (61 / 100 : ℝ) : ℝ) : ℂ) * Spectral.f D Z

private def integrandH (x : ℝ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
    Spectral.G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)

private lemma g_hinv (x : ℝ) (hx : 0 < x) :
    g D x = mellinInv (-2) (fun z : ℂ => Spectral.G D (-z)) x := by
  have h1 : g D x = comparisonVerticalIntegral 2
      (fun s => (x : ℂ) ^ s * Spectral.G D s) := by
    rw [← SpectralData.rpow_mul_f D x hx]
    unfold g
    rw [Complex.ofReal_cpow hx.le]
    congr 1
    norm_num
  rw [h1]
  have hint : ∀ y : ℝ,
      (x : ℂ) ^ (-(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
        Spectral.G D (-(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = integrandH D x (-y) := by
    intro y
    unfold integrandH
    have e1 : -(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        = ((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I := by
      push_cast <;> ring
    rw [e1]
  unfold comparisonVerticalIntegral mellinInv
  simp only [Complex.real_smul, smul_eq_mul]
  congr 1
  · push_cast <;> ring
  · simp_rw [hint]
    exact (integral_neg_eq_self (integrandH D x) volume).symm

private lemma G_decay (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, ∀ t : ℝ,
      ‖Spectral.G D ((r : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, h⟩ := SpectralData.G_bound D a b ha hab
  exact ⟨C, hC.le, fun r hr t => h r t hr.1 hr.2⟩

private lemma g_package :
    ContinuousOn (g D) (Set.Ioi (0 : ℝ)) ∧
    LocallyIntegrableOn (g D) (Set.Ioi (0 : ℝ)) ∧
    (∀ b : ℝ, g D =O[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Real.rpow x b)) ∧
    (∀ c : ℝ, 2 < c → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 < x → x ≤ 1 → ‖g D x‖ ≤ C * Real.rpow x c) :=
  DedekindZetaZeroFree.mellin_right_shift_flat (Spectral.G D) (g D) (SpectralData.G_differentiableOn D)
    (G_decay D) (g_hinv D)

theorem g_continuousOn : ContinuousOn (g D) (Set.Ioi (0 : ℝ)) :=
  (g_package D).1

theorem g_locallyIntegrableOn : LocallyIntegrableOn (g D) (Set.Ioi (0 : ℝ)) :=
  (g_package D).2.1

theorem g_isBigO_zero (b : ℝ) :
    g D =O[𝓝[>] (0 : ℝ)] (fun Z : ℝ => Z ^ b) :=
  (g_package D).2.2.1 b

end

end DedekindZetaZeroFree.Quantitative.TransformFlat
