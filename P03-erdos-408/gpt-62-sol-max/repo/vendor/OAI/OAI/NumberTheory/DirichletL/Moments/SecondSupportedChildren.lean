module

public import OAI.NumberTheory.DirichletL.Moments.SecondOriginalChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSupportedChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns
open CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound
open CenteredMomentSecondDivisorSupport CenteredMomentSourceRow Filter CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum
open CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren
local notation "O" => ActualEisensteinCubic.O

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

set_option maxHeartbeats 600000 in
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
  obtain ⟨K,hK,hbound⟩ := actual_nonexceptional_block_bound W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let live (L:Ideal O):Prop:=(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let Ds:=divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
  let coarse (G : Ideal O) (hg : G≠0) (L:Ideal O) := QuadraticInitialBound.diagonalControl Φ*max 1 H*
    (∑I∈residualPool G hg S,‖if IsCoprime G I ∧ L∣I then β (G*I) else 0‖)^2
  have hcoarse G hg L : 0 ≤ coarse G hg L :=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  have hsource (G:Ideal O) (hg:G≠0) (L:Ideal O) (χ:RayCharacter) (v:ℝ) (J:ℕ):
      sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool G hg S)
        (fun I=>if IsCoprime G I ∧ L∣I then β (G*I) else 0)
        (heightCoeff (τ χ) v) Φ H≤coarse G hg L*(1+‖v‖)^(2*J):=by
    have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool G hg S)
      (fun I=>if IsCoprime G I ∧ L∣I then β (G*I) else 0) (τ χ) v
      (nonexceptional η χ Q m A) Φ H hH
    apply hh.trans
    exact le_mul_of_one_le_right (hcoarse G hg L) (one_le_pow₀ (by linarith [norm_nonneg v]))
  let F₁ := fun L => if Squarefree L ∧ live L then E₁/(L.absNorm:ℝ) else coarse C hC.1 L
  let F₂ := fun L => if Squarefree L then (if live L then E₂/(L.absNorm:ℝ) else 0) else coarse D hD.1 L
  have hF₁ L : 0≤F₁ L := by
    dsimp only [F₁]; split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact hcoarse ..
  have hF₂ L : 0≤F₂ L := by
    dsimp only [F₂]; split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · rfl
    · exact hcoarse ..
  have hk := hbound r hr η t S β C D hC hD hCD U R rows ρ x
    (fun I => Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun J => Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y)) Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor
    (fun L => windowBudget J₁ t (F₁ L)) (fun L => windowBudget J₂ t (F₂ L))
    (fun L _ => windowBudget_nonneg _ _ _) (fun L _ => windowBudget_nonneg _ _ _)
    (by
      intro L hL χ w
      refine (original_window_from_masked_source η (τ χ) χ A C hC
        (fun I hi hc v => hτ χ I hi (Or.inl hc) v) S β L _ t w X hX J₁ Φ H hH
        (by simpa only [normValue_eq_embedding] using hΦ) (F₁ L) (hF₁ L) ?_).trans
        (shifted_window_budget J₁ t w (F₁ L) (hF₁ L))
      intro v
      dsimp only [F₁]
      split_ifs with h
      · exact hleft L hL h.2 h.1 χ v
      · exact hsource C hC.1 L χ v J₁)
    (by
      intro L hL χ w
      simp only [star_logAnnulus_column]
      refine (original_window_from_masked_source η (τ χ) χ A D hD
        (fun I hi hc v => hτ χ I hi (Or.inr hc) v) S β L _ t (-w) Y hY J₂ Φ H hH
        (by simpa only [normValue_eq_embedding] using hΦ) (F₂ L) (hF₂ L) ?_).trans
        (conjugate_shifted_window_budget J₂ t w (F₂ L) (hF₂ L))
      intro v
      dsimp only [F₂]
      split_ifs with h h'
      · exact hright L hL h' h χ v
      · rw [right_source_energy_zero D hD S β Hsource hβ L (lt_of_not_ge h'), zero_mul]
      · exact hsource D hD.1 L χ v J₂)
  have he:(∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L)))=
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hμ : (UniqueFactorizationMonoid.moebius L:ℂ)=0
    · simp [hμ]
    have hsf := CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hμ
    by_cases hl:live L
    · rw [if_pos hl]
      simp only [hl, hsf, true_and, if_true, F₁, F₂]
      rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
      ring
    · rw [if_neg hl]
      simp only [F₂, if_pos hsf, if_neg hl, windowBudget, Real.sqrt_zero, zero_mul, mul_zero]
  have hmass':=
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

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentSecondSupportedChildren

end

end OAI
