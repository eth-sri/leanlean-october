module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Moments.FirstChildLower

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

def exponent (A D P q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (A+P+ε) q))

structure Ready {ι:Type*}[Fintype ι](s:Input ι)(R:Ideal HeckeFamily.O)(K Z ξ B:ℝ):Prop where
  puncture_ne : R≠0
  scale_pos : 0<K
  volume_cap : volume s≤Z^B
  source_nonneg : 0≤sourceRadius s
  source_cap : sourceRadius s≤Z^B
  conductor_cap : (s.η.modulus.absNorm:ℝ)≤Z^B
  puncture_cap : (R.absNorm:ℝ)≤Z^B
  nominal_pos : 0<nominal s K
  nominal_cap : nominal s K≤Z^B
  frequency_pos : 0<frequencyRadius (nominal s K) Z ξ
  frequency_cap : frequencyRadius (nominal s K) Z ξ≤Z^B

theorem normalized_zero {ι:Type*}[Fintype ι](s:Input ι)(R seed:Ideal HeckeFamily.O)
    (hz:∀I:Ideal HeckeFamily.O,(original s R seed).beta I=0)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource s R seed W K=0:=by
  simp [normalizedGaussSource,sourceGaussEnergy,gaussEnergy,gaussPolynomial,hz]

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
