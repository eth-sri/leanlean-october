module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Height
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDiskBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ReciprocalLogDisk

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight
open DedekindZetaZeroFree.Quantitative.ReciprocalLogDiskAux
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def R₀ : ℝ := 111995 / 100000

def r₂ : ℝ := 1119925 / 1000000

def r₀ : ℝ := 999 / 1000

def eulerLog (ω : Detector.PrimitiveFrequencyCharacter F) (s : ℂ) : ℂ :=
  ∑' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥},
    ∑' k : ℕ, ω.character (P.1 ^ (k + 1)) /
      (((k : ℂ) + 1) * (Ideal.absNorm P.1 : ℂ) ^ (((k : ℂ) + 1) * s))

theorem disk_subset_zero_free_region (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → ∀ t : ℝ, |t| ≤ 2 * U ^ ρ →
      Metric.ball ((2 : ℂ) + (t : ℂ) * Complex.I) R₀ ⊆
        {s : ℂ | σ₀ < s.re ∧ |s.im| < 4 * U ^ ρ} := by
  refine ⟨2, le_refl _, fun U hU t ht s hs => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have hre : |(s - ((2 : ℂ) + (t : ℂ) * Complex.I)).re| < R₀ :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hs
  have him : |(s - ((2 : ℂ) + (t : ℂ) * Complex.I)).im| < R₀ :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) hs
  have e1 : (s - ((2 : ℂ) + (t : ℂ) * Complex.I)).re = s.re - 2 := by simp
  have e2 : (s - ((2 : ℂ) + (t : ℂ) * Complex.I)).im = s.im - t := by simp
  rw [e1] at hre
  rw [e2] at him
  have hR : R₀ = 111995 / 100000 := rfl
  rw [hR] at hre him
  have hU1 : (1 : ℝ) ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρ.le
  obtain ⟨h1, h2⟩ := abs_lt.mp hre
  obtain ⟨h3, h4⟩ := abs_lt.mp him
  obtain ⟨h5, h6⟩ := abs_le.mp ht
  refine ⟨?_, ?_⟩
  · unfold σ₀
    linarith
  · rw [abs_lt]
    constructor <;> linarith

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)


end

end DedekindZetaZeroFree.Quantitative.ReciprocalLogDisk
