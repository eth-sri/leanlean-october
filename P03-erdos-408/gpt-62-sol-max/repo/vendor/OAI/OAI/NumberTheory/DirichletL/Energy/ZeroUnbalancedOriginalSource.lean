module

public import OAI.NumberTheory.DirichletL.Energy.ZeroReferenceReflection
public import OAI.NumberTheory.DirichletL.Energy.ZeroReferenceError
public import OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
public import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalSource
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound CenteredMomentEnergyState
open CenteredMomentEnergyBands CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroReferenceReflection CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReferenceError
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O

theorem original_from_low (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤s.width/6 →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →Real.logb Z X₁≤s.width/4 →1≤X₂ →
      s.plainEnergy p t X₁ X₂ ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4))):=by
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilonDelete hepsilonDelete
  obtain ⟨Ce,hCe,he⟩:=short_energy_bound b
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Ce,Cweight,hC,mul_pos hD hCe,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hshort hlong
  have hZpos:=zero_lt_one.trans hZ.1
  apply hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith)
    (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
    t X₁ X₂ _ 0
  · simp
  · simp
  · simp
  · simp
  · exact hX₁
  · exact hX₂
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simp only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_zero]
    let W₁ := p.profile 0
    let W₂ := p.profile 1
    have hs₁ := p.support 0
    have hs₂ := p.support 1
    let N₁ : ℝ := (∏ I∈D₁, I).absNorm
    let N₂ : ℝ := (∏ I∈D₂, I).absNorm
    let short := Real.logb Z X₁ - Real.logb Z N₁
    let along := Real.logb Z X₂ - Real.logb Z N₂
    obtain ⟨hn₁,_⟩ := divisor_norm s D₁ hD₁
    obtain ⟨hn₂, hc₂⟩ := divisor_norm s D₂ hD₂
    have hl₁ := Real.logb_nonneg hZ.1 hn₁
    have hl₂ := Real.logb_nonneg hZ.1 hlong
    have hu₂ := (Real.logb_le_iff_le_rpow hZ.1 (zero_lt_one.trans_le hn₂)).mpr hc₂
    have hM := s.width_nonneg
    have hshort' : short ≤ s.width/4 := by dsimp [short,N₁]; linarith
    have hshortL : short ≤ L := by linarith
    have hsmax : max 0 short ≤ s.width/4 := max_le (by linarith) hshort'
    have hgap : s.width - along ≤ Mcap+Bmask := by dsimp [along,N₂]; linarith
    have hL0 : 0 ≤ L := by linarith
    have hwindow : max 0 (s.width-along+xi) ≤ L := max_le hL0 (by linarith)
    have hlog := (Real.log_pos hZ.1).le
    have hdg := diagonalControl_nonneg s.radial.profile
    rw [←divided_scale_power Z X₁ _ hZ.1 hX₁ (zero_lt_one.trans_le hn₁),
      ←divided_scale_power Z X₂ _ hZ.1 hX₂ (zero_lt_one.trans_le hn₂)]
    have hlen (v : ℝ) : length Z (Z^v) = max 0 v := by
      rcases le_total 0 v with hv | hv
      · rw [length, max_eq_right (Real.one_le_rpow hZ.1.le hv),
          Real.logb_rpow hZpos hZ.1.ne', max_eq_right hv]
      · rw [length, max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.1.le hv),
          Real.logb_one, max_eq_left hv]
    by_cases hd : max 0 short + max 0 along ≤ 5*s.width/6
    · have hlongL : along ≤ L := by linarith [le_max_right (0:ℝ) along, le_max_left (0:ℝ) short]
      have hdirect := independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S K hlow hBmask ha
        s hQ hs W₁ W₂ hs₁ hs₂ t t (Z^short) (Z^along)
        (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
        (Real.rpow_le_rpow_of_exponent_le hZ.1.le hshortL)
        (Real.rpow_le_rpow_of_exponent_le hZ.1.le hlongL) (by rwa [hlen, hlen])
      exact hdirect.trans (le_add_of_nonneg_right (by positivity))
    · have halong : 0 < along := by
        by_contra! hn
        rw [max_eq_left hn] at hd
        linarith
      rw [max_eq_right halong.le] at hd
      have hrel : max 0 (s.width-along+xi) + length Z (Z^short) ≤ 5*s.width/6 := by
        rw [hlen, ←le_sub_iff_add_le]
        exact max_le (by linarith) (by linarith)
      have hh := hZ.2 Bmask L Mcap ε Q degree K hK hlow hBmask s hQ hs
        W₂ W₁ hs₂ hs₁ t along short (by linarith) hwindow hshortL hrel
      dsimp only at hh
      have he₁ := he W₁ (fun x hx => (hs₁ hx).2) (naturalCharacter s.character)
        t (Z^short) s.radial.scale s.radial.profile (effectiveState s).radial.keep
        (Real.rpow_pos_of_pos hZpos _) s.radial.scale_pos s.radial.nonneg
      simp_rw [mul_comm (polynomial _ false (p.profile 0) _ 0 t) (polynomial _ false (p.profile 1) _ 0 t)]
      apply hh.trans
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      apply add_le_add
      · gcongr <;> rfl
      · have hs₁' : _ ≤ Ce*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4) := he₁.trans (by
          have hZ1 := hZ.1.le
          gcongr)
        convert mul_le_mul_of_nonneg_left hs₁'
          (show 0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
            (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving) by positivity) using 1 <;>
          dsimp [sourceControl, W₁, W₂] <;> ring

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginalSource

end

end OAI
