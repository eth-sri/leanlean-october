module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
public import OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorSupport
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy CenteredMomentSecondDivisorSupport CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

theorem supported_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(Ds : Finset (Ideal O))(D : Ideal O)(H : ℝ),H/(D.absNorm:ℝ)≤Z^B →
      (∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds D H hcap
  exact hz.2 _ (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hcap)

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

end SevenEighths.CenteredMomentFirstDivisorSupport

end

end OAI
