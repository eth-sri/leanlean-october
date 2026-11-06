module
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
public import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate

lemma choose_first_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→V≤Z^B→0<Tsec→Tsec≤Z^B→
      V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((4*B+saving)/(ξ/4))
  have horder:4*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:4*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^2*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 2) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(4*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(2:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*2)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)
