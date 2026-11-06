module

public import OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
public import OAI.NumberTheory.DirichletL.Energy.ZeroComparison
public import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyLowFixedRadialEntry
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyOriginalSource
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentEnergyPhysicalEntry
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy

variable {ι:Type*}[Fintype ι][DecidableEq ι]


omit [DecidableEq ι] in
lemma zero_control (s:Input ι) hz₁  hz₂  W₁ W₂ :
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

theorem original_low_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(a b B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(ha:0<a)(hb:0≤b)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧0<Ctail ∧∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),∀he₁:s.W₁=W₁,∀he₂:s.W₂=W₂,
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      (∀i,s.hi i≤hi i) →∀(R:Ideal HeckeFamily.O)(r:Radial),
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume s≤Z^B → r.scale⁻¹≤Z^B →
      let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁;
      let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂;
      energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
        s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass (zeroInput s hz₁ hz₂) R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    bΦ hbΦ hi a b B ε ξ saving hhi ha hb hB hε hξ
  refine ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  dsimp only
  let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁
  let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂
  have hh:=hz.2 (zeroInput s hz₁ hz₂) W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  change energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
    s.P s.X₁ s.X₂ r.keep r.profile r.scale≤_+2*energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero,zeroInput_volume,zero_control] at hh
  exact hh

end SevenEighths.CenteredMomentEnergyLowFixedRadialEntry

end

end OAI
