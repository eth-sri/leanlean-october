module
public import OAI.NumberTheory.DirichletL.Moments.SecondOriginalChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSupportedChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound CenteredMomentSecondDivisorSupport CenteredMomentSourceRow Filter CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren

theorem right_source_energy_zero
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (L:Ideal O) (hL:Hsource/(D.absNorm:ℝ)<L.absNorm)
    (keep:O→Prop) (f:Ideal O→ℂ) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) :
    sourceRestrictedEnergy keep (residualPool D hD.1 S)
      (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0) f Φ H=0 := by
  have hc (I:supportedColumns (residualPool D hD.1 S)) :
      (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then β (D*I) else 0)=0 := by
    split_ifs with hi
    · by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 β Hsource hβ hn hi.2)
    · rfl
  simp only [sourceRestrictedEnergy,restrictedEnergy,rowPolynomial,hc,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide:2≠0),ite_self,tsum_zero]

theorem actual_block_from_supported_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₂/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨K,hK,hkernel⟩:=CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let live (L:Ideal O):Prop:=(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let Ds:=divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
  let coarse (L:Ideal O):ℝ:=QuadraticInitialBound.diagonalControl Φ*max 1 H*
    (∑I∈residualPool C hC.1 S,‖if IsCoprime C I ∧ L∣I then β (C*I) else 0‖)^2
  have hcoarse (L:Ideal O):0≤coarse L:=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=>if live L then E₁/(L.absNorm:ℝ) else coarse L
  let F₂:Ideal O→ℝ:=fun L=>if live L then E₂/(L.absNorm:ℝ) else 0
  have hF₁ (L:Ideal O):0≤F₁ L:=by
    dsimp only [F₁];split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact hcoarse L
  have hF₂ (L:Ideal O):0≤F₂ L:=by
    dsimp only [F₂];split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact le_rfl
  have hk:=hkernel r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl hsf χ v
      · have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (τ χ) v
          (nonexceptional η χ Q m A) Φ H hH
        exact hh.trans (by simpa only [F₁,ite_eq_right hl] using
          le_mul_of_one_le_right (hcoarse L) (one_le_pow₀ (by linarith [norm_nonneg v]) (n:=2*J₁))))
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₂,ite_eq_left hl] using hright L hL hl hsf χ v
      · rw [right_source_energy_zero D hD S β Hsource hβ L (lt_of_not_ge hl)]
        simp only [F₂,ite_eq_right hl,zero_mul,le_refl])
  have he:(∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L)))=
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hl:live L
    · rw [ite_eq_left hl]
      simp only [F₁,F₂,ite_eq_left hl]
      rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
      ring
    · have hl' : ¬(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ):=hl
      simp only [F₂,live,ite_eq_right hl',windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  have hmass':(∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤Cm*Z^δ:=
    hZ.2 (Ds.filter live) (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hn)
  apply hk.trans
  change K*(∑L∈Ds,_)≤_
  rw [he]
  calc
    _≤K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass'
        (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))) hK
    _≤max 1 K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
          (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    _=_:=by ring
