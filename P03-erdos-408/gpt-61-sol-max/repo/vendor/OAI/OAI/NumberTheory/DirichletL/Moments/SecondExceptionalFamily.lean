module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondLiveFamily
public import OAI.NumberTheory.DirichletL.Moments.ReflectedSource
public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
public import OAI.NumberTheory.DirichletL.Hecke.PrimeScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource


theorem span_thirty_six_norm : (Ideal.span {(36:HeckeFamily.O)}).absNorm=1296 := by
  have h := ActualEisensteinCubic.rational_modulus_card 36 (by norm_num)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  exact h

section
variable (C D : Ideal HeckeFamily.O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D) (S U : Finset (CommonIndex C D))


theorem reflected_modulus_bound  τ  :
    (reflected τ).modulus.absNorm≤1296*τ.modulus.absNorm := by
  have h := HeckePrimeScale.product_modulus_bound τ (HeckeUnitRows.character (-1:HeckeFamily.Oˣ))
  change (reflected τ).modulus.absNorm≤τ.modulus.absNorm*(Ideal.span {(36:HeckeFamily.O)}).absNorm at h
  simpa only [span_thirty_six_norm,mul_comm] using h

include hC hCD in
theorem common_subproduct_dvd_left    
        :
    (∏P∈S,P.val)∣C := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (leftExponent_pos C D P))
  rw [left_ideal_product C D hC hCD] at h₂
  exact h₁.trans h₂

include hC hD hCD in
theorem common_subproduct_dvd_right      
        :
    (∏P∈S,P.val)∣D := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (rightExponent_pos C D P))
  rw [right_ideal_product C D hC hD hCD] at h₂
  exact h₁.trans h₂

include hC in
theorem selected_nonunit_product    
      :
    (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}=
      ∏P∈U∪nonunitPartitionSet C D U,P.val := by
  have hd : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hd,nonunitFrequencyGenerator_span]
  simp only [unitIdeal,commonPrime_span C D hC]

include hC hD hCD in
theorem selected_nonunit_dvd      
        :
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣C) ∧
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣D) := by
  simp_all [selected_nonunit_product, common_subproduct_dvd_left, common_subproduct_dvd_right]

include hC hD hCD in
theorem selected_nonunit_norm      
        :
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤C.absNorm ∧
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤D.absNorm := by
  obtain ⟨h₁,h₂⟩ := selected_nonunit_dvd C D hC hD hCD U
  constructor
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm h₁)
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm h₂)

end

structure Family (η:Character) (C D:Ideal HeckeFamily.O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (τ:RayCharacter→Character) : Prop where
  element_eq : ∀χ n,elementCoeff (τ χ) n=
    rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime D I)→∀t,
    heightCoeff (τ χ) t I=heightCoeff η t I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
      rayCharacter χ (primaryGenerator I)
  physical_budget : ∀(t:ℝ)(S:Finset (Ideal HeckeFamily.O))(β:Ideal HeckeFamily.O→ℂ)(R:ℝ)(rows:Finset HeckeFamily.O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
    ∀Z:ℝ,1<Z→∀z∈liveRows C D U R rows,
      Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
        Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))

theorem exists_exceptional_family  η   C D 
     hC   hD  (hCD:primeSupport C=primeSupport D)
     U  : ∃τ,Family η C D hC hD U τ := by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

namespace Family
variable {η:Character} {C D:Ideal HeckeFamily.O} {hC:Supported C} {hD:Supported D}
  {U:Finset (CommonIndex C D)} {τ:RayCharacter→Character}

section
variable (h : Family η C D hC hD U τ) (hCD : primeSupport C=primeSupport D) (t : ℝ) (S : Finset (Ideal HeckeFamily.O)) (β : Ideal HeckeFamily.O→ℂ) (R : ℝ) (rows : Finset HeckeFamily.O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) (hne : physicalBlock η t S β C D hC hD U R rows W K n≠0) (χ : RayCharacter) (Q : Ideal HeckeFamily.O) (m z : HeckeFamily.O) (hm : m≠0) (hz : z≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:HeckeFamily.O)∣m)


include h hm hml hm2 in
theorem nonexceptional_iff    
              :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_nonexceptional_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hml hm2

include h hm hz hml hm2 in
theorem inducing_iff    
           
        :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_reduced_inducing_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hz hml hm2

include h hCD hK hne in
theorem physical_conductor_bounds  
     
         
        
       :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*C.absNorm ∧
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*D.absNorm := by
  have hN := (h.physical_budget t S β R rows W K hK n hne χ).1
  obtain ⟨h₁,h₂⟩ := selected_nonunit_norm C D hC hD hCD U
  constructor
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₁)
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₂)

end

end Family

def expandedConductor (τ:Character)(R C:Ideal HeckeFamily.O)(z:HeckeFamily.O) :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:HeckeFamily.O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:Character) :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:HeckeFamily.O)}).absNorm

theorem expanded_conductor_bounds {η:Character}{C D:Ideal HeckeFamily.O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal HeckeFamily.O))(β:Ideal HeckeFamily.O→ℂ)(radius:ℝ)(rows:Finset HeckeFamily.O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
     χ ξ  R  z  :
    expandedConductor (τ χ) R C z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm ∧
    expandedConductor (reflected (τ ξ)) R D z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm := by
  have hl := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne χ).2
  have hr := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne ξ).1
  have hl' : (τ χ).modulus.absNorm≤1296*(η.modulus.absNorm*fixedFactor*D.absNorm) := hl.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr' := (reflected_modulus_bound (τ ξ)).trans (Nat.mul_le_mul_left 1296 hr)
  constructor
  · calc
      expandedConductor (τ χ) R C z≤
        (1296*(η.modulus.absNorm*fixedFactor*D.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:HeckeFamily.O)}).absNorm*
          (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring
  · calc
      expandedConductor (reflected (τ ξ)) R D z≤
        (1296*(η.modulus.absNorm*fixedFactor*C.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:HeckeFamily.O)}).absNorm*
          (R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring

theorem live_norm_le_four_radius (C D:Ideal HeckeFamily.O)(U:Finset (CommonIndex C D))
     radius (rows:Finset HeckeFamily.O) z (hz:z∈liveRows C D U radius rows) :
    normValue z≤4*radius := by
  obtain ⟨hr,hg,hv,_,_,hn,_⟩ := retained_geometry radius
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U radius rows z hz)
  have hG := normValue_ge_one _ hg
  have hV := normValue_ge_one _ hv
  have hprod : 1≤normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U) := by
    nlinarith
  exact hn.trans (div_le_self (by positivity) hprod)

end SevenEighths.CenteredMomentSecondExceptionalFamily

end

end OAI
