module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.FrequencyHeightPrefix
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.FrequencyMaximalSieve
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.CountCore
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.RightHalfPlane
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.MaximalSieve

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDetectorCount31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
  DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.DetectorPrefix DedekindZetaZeroFree.Quantitative.DetectorSieve
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
  DedekindZetaZeroFree.Quantitative.RawDetectorMaximal31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem rawExceptionalSet_card (A ρ : ℝ) (hA : 0 ≤ A) (hρ : RawDetectorHeightPrefix31.HeightSpec D A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      (FixedData.rawExceptionalSet D ρ U).Finite ∧
        ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α := by
  obtain ⟨c₁, hc₁, U₁, hU₁, hpre⟩ := RawDetectorHeightPrefix31.detector_prefix D A ρ hρ
  obtain ⟨Clog, hClog, hsieve⟩ := RawDetectorMaximal31.detector_maximal_sieve D
  obtain ⟨Cs, hCs, hs⟩ := hsieve (1 / 100000) (by norm_num)
  refine DetectCount.count (fun U u => u ≠ principalFrequency D.recipe ∧
        U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U)
    (fun u => (FixedData.primMinus D u).character) (FixedData.rawExceptionalSet D ρ) (RawDetectorMaximal31.rowMaximalSum D)
    ρ c₁ U₁ Clog Cs hρ.1 hρ.2.1 hc₁ hClog hCs ?_ ?_ hs
  · intro U hU u hu
    obtain ⟨hu₁, hq₁, hq₂, s, hL, hσ, him⟩ := hu
    obtain ⟨N, y, hN, hN', hNy, hy, hlow⟩ := hpre U hU u ⟨hu₁, hq₁, hq₂, s, hL, hσ, him⟩ s hL hσ
      (DetectEuler.IsLZero.re_le_one hL) him
    exact ⟨⟨hu₁, hq₁, hq₂⟩, s.im, N, y, him, hN, hN', hNy, hy, hlow⟩
  · intro U M T δ b hU hδ
    exact card_dyad_le_rowMaximalSum D U M T δ b (by linarith) hδ _ (fun _ hu => ⟨hu.1.1, hu.1.2.1, hu.1.2.2, hu.2⟩)

end

end DedekindZetaZeroFree.Quantitative.RawDetectorCount31
