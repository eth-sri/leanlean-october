module
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
public import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma choose_first_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→ V≤Z ^B→0<Tsec→ Tsec≤Z ^B→
      V ^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z ^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z ^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((4*B+saving)/(ξ/4))
  have horder:4*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:4*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  pm_2962
  calc
    _≤(Z ^B)^2*((1+Real.exp (2*HN))^2*(Z ^B)^2)*Z ^(-(ξ/4)*(Adec:ℝ)):=by
      pm_1215 hd
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 2) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z ^(4*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z ^(B*(2:ℝ))*((1+Real.exp (2*HN))^2*Z ^(B*(2:ℝ)))*Z ^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z ^(B*2)*Z ^(B*2)*Z ^(-(ξ/4)*(Adec:ℝ))) by ring]
      pm_7490
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI
