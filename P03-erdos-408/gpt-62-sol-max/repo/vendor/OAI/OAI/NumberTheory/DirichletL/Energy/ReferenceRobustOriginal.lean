module

public import OAI.NumberTheory.DirichletL.Energy.DeletedRobustGeometry
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowChild
public import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
public import OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowError

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometry
open CenteredMomentEnergyReferenceLowChild CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource CenteredMomentCommonMaskEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentOriginalRadialComparison
open CenteredMomentAllocatedNaturalRadial CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentPrimeSlot
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentEnergyProfiles
open CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentOriginalRadialComparison
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowError
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem reference_from_low (robust : Bool)
    (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hdefect:0≤defect)(hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi+11*defect/7≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      ReflectionWindow robust Z s.width X₁ X₂ (∑i,w i) κ defect →
      let Y := reflectionScales robust Z s.width X₁ X₂
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) Y.1 Y.2
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=>bslot) (fun _=>Bslot) (fun _=>hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨Cerr,hCerr,herr⟩:=relative_slot_error (Finset.univ : Finset α) Wslot aslot bslot lo hi b haslot hsSlot hcSlot
  obtain ⟨n,T,Dchild,hDc,hcontrol⟩:=reflected_child_control a b ha hlo hhi S degree
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving (Mcap+Bmask) ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cerr,Cweight,hC,mul_pos hD hCerr,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hwindow
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  let Y := reflectionScales robust Z s.width X₁ X₂
  have hp : 0 < Y.1 ∧ 0 < Y.2 := by
    cases robust
    · exact ⟨hX₁, hX₂⟩
    · exact comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t Y.1 Y.2 _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simp only [Real.rpow_zero, mul_one]
    let short := Real.logb Z (Y.1 / ((∏ P ∈ D₁, P).absNorm : ℝ))
    let along := Real.logb Z (Y.2 / ((∏ P ∈ D₂, P).absNorm : ℝ))
    let F := Finset.univ \ J
    have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=>hw i)
    have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ F) (fun i _ _=>hw i)
    have hg:=reference_deleted_gates robust s hZ.1 hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi defect hs hL
      hX₁ hX₂ (Finset.sum_nonneg (fun i _=>hw i)) hsum hsumle hκ hxi hdefect hxiM hwindow D₁ D₂ hD₁ hD₂
    dsimp only at hg
    rw [←hg.1,←hg.2.1]
    have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
      (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
      (fun i _ _=>Real.one_le_rpow hZ.1.le (hw i))
    rcases hg.2.2.2.2.2.2.2 with hd|hr
    · have hdirect:=independent_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
        η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        s hQ hs W₁ W₂ hs₁ hs₂ t t (Z^short) (Z^along)
        (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
        (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
        (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
      exact hdirect.trans (le_add_of_nonneg_right (by positivity))
    · have hh := hZ.2 Bmask s W₂ W₁ hs₂ hs₁ α F
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t)
        (fun i=>Z^(w i)) t along short
        (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
          (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) hg.2.2.2.2.2.1 (by positivity) (by
        intro v j k x hx
        have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
        let W₀ := (annulusSeed a b hlo hhi).profile
        have h₀ := derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j
        have h₁ := derivativeChoice_support _ _ _ hs₁ k
        have hh:=independent_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
          η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
          (derivativeChoice W₀ j) (derivativeChoice W₁ k) h₀ h₁ (-2*Real.pi*v) t
          (Real.exp x) (Z^short) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
          (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.2.2.1))
          (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
          (by linarith [hwindow.1, hr.1, hr.2]) (by linarith [hwindow.1, hr.1, hr.2])
        have he:(W₀:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=funext annulusTemplate_apply
        simp only [derivativeChoice_apply,he] at hh
        have hb:=hcontrol W₁ hs₁ j k v t height hheight
        dsimp only [reflectionProfiles] at hb
        have hp:0≤K*diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
        have hz:0≤Z^(s.width+ε):=Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _
        have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
        refine hh.trans ?_
        convert hmul using 1 <;> ring)
      have he:=herr F (Finset.subset_univ F) W₁ (fun x hx=>(hs₁ hx).2)
        (naturalCharacter s.character) (fun i=>relativeCharacter M H hH η₀ (θ i))
        (fun i=>primePool M H bslot (Z^(w i))) (fun i=>Z^(w i)) σ freq t
        (Z^short) s.radial.scale s.radial.profile (effectiveState s).radial.keep
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) s.radial.scale_pos
        (fun i _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
        (fun i _=>hσlo i) (fun i _=>hσhi i)
        (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1) s.radial.nonneg
      have hcoeff:0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving):=by positivity
      conv_lhs =>
        arg 1
        ext z
        rw [mul_comm (polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t)]
      simp only [sourceControl] at hh hcoeff ⊢
      apply hh.trans
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      apply add_le_add
      · gcongr
        exact hg.2.2.2.2.2.2.1
      · have he' : _ ≤ Cerr*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)*∏i,Z^(w i) :=
          he.trans (by
            gcongr <;> first | exact hZ.1.le | exact hg.2.2.1)
        convert mul_le_mul_of_nonneg_left he' hcoeff using 1 <;> ring

end SevenEighths.CenteredMomentEnergyReferenceRobustOriginal

end

end OAI
