module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CubicPowerPushforward
public import DedekindZetaZeroFree.CharacterSums.Gauss.TameCubicShellIntegrals

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ValuativeRel Classical ENNReal Pointwise

namespace DedekindZetaZeroFree.NonarchimedeanHaarScaling

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

export IntrinsicHaarScaling (residue_index_measure uniformizer_image_integerRing uniformizer_image_measure)


lemma char_abs (μ : Measure K) [μ.IsAddHaarMeasure] (c : Kˣ) :
    (distribHaarChar K c : ℝ) = KPCubicHaar.abs K (c : K) :=
  IntrinsicHaarScaling.char_abs K μ c

theorem map_mul (μ : Measure K) [μ.IsAddHaarMeasure] (c : K) (hc : c ≠ 0) :
    Measure.map (fun x : K => c * x) μ =
      (ENNReal.ofReal (KPCubicHaar.abs K c))⁻¹ • μ :=
  IntrinsicHaarScaling.map_mul K μ c hc

theorem closedBall_measure (μ : Measure K) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ {x : K | KPCubicHaar.abs K x ≤
        (Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) : ℝ) ^ k} =
      ENNReal.ofReal
        ((Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) : ℝ) ^ k) *
          μ ((ValuativeRel.valuation K).integer : Set K) :=
  IntrinsicHaarScaling.closedBall_measure K μ k

end DedekindZetaZeroFree.NonarchimedeanHaarScaling

end
