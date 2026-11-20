module

public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
public import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
public import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailAggregate

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
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

omit [DecidableEq ι] in
theorem local_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨SΦ,C,hC,hbound⟩ := uniform_input_tail_bound (Θ := O × O) 1
    (fun x η t S c Φ K V _ Z ξ =>
      CenteredMomentFirstSectorLocalization.discardedEnergy η x.1 x.2 t S c Φ K V Z ξ)
    hi wlo whi B ξ saving hhi hwlo hwhi hB hξ fun Adec => by
      obtain ⟨SΦ,C,hC,h⟩ := local_discarded_energy_bound Adec 1 zero_lt_one
      refine ⟨SΦ,C,hC,?_⟩
      intro x η t S c Φ K V HN Tsec Z hK hV hZ hn hnom ht
      convert h η x.1 x.2 t S c Φ K V HN Tsec Z 1 ξ hK hV hZ le_rfl hn hnom (by simpa using ht) using 1
      simp only [pow_one, Real.rpow_one]
      ring
  refine ⟨SΦ,C,hC,hbound.mono fun Z hZ => ⟨hZ.1,?_⟩⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A
  exact hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi (m,A)

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
