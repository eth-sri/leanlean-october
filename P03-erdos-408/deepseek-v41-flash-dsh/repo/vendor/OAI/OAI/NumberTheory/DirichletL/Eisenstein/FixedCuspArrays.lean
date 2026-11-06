module

public import OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics
open scoped ContDiff FourierTransform SchwartzMap BigOperators Classical
open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_full_support (j:Fin 3) (h:Eis) (hh:h≠0)
    (hc:(sourceCuspCoefficients j).value h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  have hs : ∃u:Eisˣ,∃m:ℕ,∃I J:Ideal Eis,Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u:Eis)*ActualEisensteinCubic.lambda^m*primaryGenerator I*(primaryGenerator J)^3 := by
    fin_cases j
    · exact sourceResidualFourierCoefficient_full_squarefree_cube_support h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support false h hh hc
    · exact ramifiedBesselValue_squarefree_cube_support true h hh hc
  obtain ⟨u,m,I,J,hI,hIg,hJg,he⟩:=hs
  exact ⟨(u,m,(⟨I,hI,hIg⟩,⟨J,hJg⟩)),he.symm⟩

lemma sourceCuspRadialCoefficient_full_support (j:Fin 3) (z:ℂ) (h:Eis)
    (hh:h≠0) (hc:sourceCuspRadialCoefficient j z h≠0) :
    ∃p:ThetaFullIndex,thetaFullFrequency p=h := by
  apply sourceCuspCoefficients_full_support j h hh
  intro hz
  apply hc
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,hz,
    star_zero,mul_zero,zero_div,zero_mul]

theorem sourceCuspRadialCoefficient_tsum_full_index (j:Fin 3) (z:ℂ) (w:Eis→ℂ) :
    (∑'h:Eis,w h*sourceCuspRadialCoefficient j z h)=
      ∑'p:ThetaFullIndex,w (thetaFullFrequency p)*
        sourceCuspRadialCoefficient j z (thetaFullFrequency p) := by
  have hs:Function.support (fun h:Eis=>w h*sourceCuspRadialCoefficient j z h)⊆
      {h:Eis|h≠0}:=by
    intro h hh hz
    subst h
    exact hh (by
      change w 0*sourceCuspRadialCoefficient j z 0=0
      rw [sourceCuspRadialCoefficient_zero,mul_zero])
  calc
    _=∑'h:{h:Eis//h≠0},w h.val*sourceCuspRadialCoefficient j z h.val:=
      (tsum_subtype_eq_of_support_subset hs).symm
    _=_:=thetaFullFrequency_tsum (sourceCuspRadialCoefficient j z) w
      (sourceCuspRadialCoefficient_full_support j z)

lemma SourceCuspDatum.smoothedKernel_full_index (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
          CubicReflectionKernel.paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  rw [d.smoothedKernel_eq]
  congr 1
  have he:=sourceCuspRadialCoefficient_tsum_full_index d.index d.dualPoint
    (fun h=>CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength h/(27*(sourceCuspScale d.index)^2*d.heightScale^2)))
  simpa only [mul_comm] using he

lemma SourceCuspDatum.smoothedKernel_full_index_norm_summable
    (d:SourceCuspDatum) (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    Summable (fun p:ThetaFullIndex=>
      ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/
            (27*(sourceCuspScale d.index)^2*d.heightScale^2))‖) := by
  have hs:=paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient d.index d.dualPoint)
    (sourceCuspRadialCoefficient_weighted_summable _ _)
    (Vstar W) v0 v1 hv0 (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))
    (by have := sourceCuspScale_pos d.index; have := d.heightScale_pos; positivity)
  have hp:=hs.comp_injective thetaFullFrequency_injective
  apply hp.congr
  intro p
  exact congrArg (fun y:ℝ=>‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
    CubicReflectionKernel.paperKernel (Vstar W) y‖)
    (by ring :
      X/(27*(sourceCuspScale d.index)^2*d.heightScale^2)*sourceCuspRadialLength (thetaFullFrequency p)=
        X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspCoefficientBound : ℝ :=
  Classical.choose three_cusp_coefficients_squarefree_cube_bound

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

def fixedCuspArrayIndex (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  (u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3

def fixedCuspArrayEligible (I J:Ideal Eis) : Prop :=
  Squarefree I ∧ primaryGenerator I≠0 ∧ primaryGenerator J≠0

def fixedCuspArrayWeight (m:ℕ) (J:Ideal Eis) : ℝ :=
  (3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ)

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb:=(Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).2
    I J hI hJ hsq u m
  rw [primaryGenerator_norm J hJ] at hb
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.1
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 false
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 true

def fixedCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  if fixedCuspArrayEligible I J then
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J) /
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)
  else 0

lemma fixedCuspArray_zero_of_ineligible (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:¬fixedCuspArrayEligible I J) : fixedCuspArray j u m I J=0 := by
  simp only [fixedCuspArray,ite_eq_right h]

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,ite_eq_left h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,ite_eq_right h,norm_zero,zero_le_one]

lemma fixedCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedCuspArray j u m I J := by
  have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
  rw [fixedCuspArray,ite_eq_left h,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

def fixedConjugateCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  star (fixedCuspArray j u m I J)

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

lemma fixedConjugateCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedConjugateCuspArray j u m I J := by
  rw [fixedCuspArray_reconstruct j u m I J h,star_mul]
  simp only [fixedConjugateCuspArray,Complex.star_def,Complex.conj_ofReal]
  ring

end CubicEisenstein

section
open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace IdealGaussCRT
open CubicEisenstein

end IdealGaussCRT

namespace LocalReflectionBrackets

section
open CubicEisenstein
variable {F : Type*} [Field F] [Fintype F]

def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h=0 then 1 else (((χ⁻¹)^2) ((σ:F)*h))*ψ (((ε:F)*x)*h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t=>(χ^j) t) h*frequencyMultiplier χ ψ σ ε x h

lemma frequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) :
    (∑h:Fˣ,frequencyRow χ ψ j σ ε x h)=activeRow χ ψ j σ ε x := by
  unfold frequencyRow finiteAdditiveFourierCoeff frequencyMultiplier activeRow
  simp only [Units.ne_zero,ite_false,Units.val_inv_eq_inv_val,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  ring_nf

open ActualEisensteinCubic CompletedGauss
noncomputable local instance quotientFieldFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeFrequency (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _

theorem canonical_frequencyRow_units (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hgood : lambda∉P) (hchar : ringChar (ActualEisensteinCubic.O⧸P)≠2) (ψ : AddChar (ActualEisensteinCubic.O⧸P) ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : j<6) (σ ε : (ActualEisensteinCubic.O⧸P)ˣ) (x : ActualEisensteinCubic.O⧸P) :
    (∑h:(ActualEisensteinCubic.O⧸P)ˣ,frequencyRow (actualSextic P hgood) ψ j σ ε x h)=
      (((actualSextic P hgood)⁻¹)^2) σ *
        phase (actualSextic P hgood) ψ j ε*bracket (actualSextic P hgood) j x := by
  rw [frequencyRow_units]
  simpa only [actualSextic] using canonical_A5_normalized P hgood hchar ψ hψ j hj σ ε x

end

open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end LocalReflectionBrackets
end

namespace CubicEisenstein
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_bottom (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 1 0=M 1 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_top (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 0 0=M 0 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

lemma upper_right_removed_last (M T:SL(2,Eis)) :
    (M*T⁻¹) 1 1= -M 1 0*T 0 1+M 1 1*T 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma upper_diagonal_product (T:SL(2,Eis)) (hT:T 1 0=0) : T 0 0*T 1 1=1 := by
  have hd:=T.property
  simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd

structure FixedCuspShape (H:SL(2,Eis)) where
  gamma : levelTwo
  index : Fin 3
  upper : SL(2,Eis)
  lower_zero : upper 1 0=0
  upper_unit : IsUnit (upper 0 0)
  lower_unit : IsUnit (upper 1 1)
  factorization : H=(gamma:SL(2,Eis))*cuspRepresentative index*upper

lemma exists_fixedCuspShape (H:SL(2,Eis)) : Nonempty (FixedCuspShape H) := by
  obtain ⟨G,j,T,hT,hT0,hT1,he⟩:=three_cusp_decomposition H
  exact ⟨⟨G,j,T,hT,hT0,hT1,he⟩⟩

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma removed_eq : (g:SL(2,Eis))*H*s.upper⁻¹=
    ((g*s.gamma:levelTwo):SL(2,Eis))*cuspRepresentative s.index := by
  calc
    _ = (g:SL(2,Eis))*((s.gamma:SL(2,Eis))*cuspRepresentative s.index*s.upper)*s.upper⁻¹ :=
      congrArg (fun K:SL(2,Eis)=>(g:SL(2,Eis))*K*s.upper⁻¹) s.factorization
    _ = _ := by simp only [Subgroup.coe_mul]; group

def datum (h:((g:SL(2,Eis))*H) 1 0≠0) : SourceCuspDatum where
  gamma := g*s.gamma
  index := s.index
  lower_ne_zero := by
    rw [←map_mul,←s.removed_eq g,integralComplexMatrix_apply,
      upper_right_removed_bottom _ _ s.lower_zero,map_mul]
    exact mul_ne_zero (eisEmbedding_ne_zero h) (eisEmbedding_ne_zero s.lower_unit.ne_zero)

lemma datum_matrix (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).matrix=integralComplexMatrix ((g:SL(2,Eis))*H*s.upper⁻¹) := by
  rw [s.removed_eq g,map_mul]
  rfl

lemma datum_point (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).point=
      eisEmbedding (((g:SL(2,Eis))*H) 0 0)/eisEmbedding (((g:SL(2,Eis))*H) 1 0) := by
  rw [SourceCuspDatum.point,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,
    upper_right_removed_top _ _ s.lower_zero,upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_mul]
  exact mul_div_mul_right _ _ (eisEmbedding_ne_zero s.lower_unit.ne_zero)

lemma datum_heightScale (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).heightScale=‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul,norm_mul]
  have hn:‖eisEmbedding (s.upper 1 1)‖=1 := by
    rcases s.lower_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hn,mul_one]

lemma datum_dualPoint (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).dualPoint=
      eisEmbedding (s.upper 0 0*s.upper 0 1)-
        eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0)) := by
  rw [SourceCuspDatum.dualPoint,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,upper_right_removed_last,
    upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_add,map_neg,map_mul]
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  field_simp [hc,ht]
  linear_combination (eisEmbedding (s.upper 0 0)*eisEmbedding (((g:SL(2,Eis))*H) 1 1)-
    eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 0 1))*hd

lemma datum_multiplier (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).multiplier=
      -star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma)*
        eisEmbedding (s.upper 0 0)^2/eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [SourceCuspDatum.multiplier,s.datum_matrix,integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero,map_mul]
  change -star (levelTwoComplexCharacter (g*s.gamma))/
    (eisEmbedding (((g:SL(2,Eis))*H) 1 0)*eisEmbedding (s.upper 1 1))^2=_
  rw [map_mul,star_mul]
  have hc:=eisEmbedding_ne_zero h
  have ht:=eisEmbedding_ne_zero s.lower_unit.ne_zero
  have hd:eisEmbedding (s.upper 0 0)*eisEmbedding (s.upper 1 1)=1 := by
    rw [←map_mul,upper_diagonal_product _ s.lower_zero,map_one]
  have hp:eisEmbedding (s.upper 0 0)^2*eisEmbedding (s.upper 1 1)^2=1 := by
    rw [←mul_pow,hd,one_pow]
  field_simp [hc,ht]
  linear_combination (star (levelTwoComplexCharacter g)*star (levelTwoComplexCharacter s.gamma))*hp

lemma datum_additive_phase (h:((g:SL(2,Eis))*H) 1 0≠0) (freq:ℂ) (scale:ℂ) :
    ShortDraftTrace.breveE (-freq*(s.datum g h).dualPoint/scale)=
      ShortDraftTrace.breveE (-freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale)*
      ShortDraftTrace.breveE (freq*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/scale) := by
  rw [s.datum_dualPoint]
  rw [show -freq*(eisEmbedding (s.upper 0 0*s.upper 0 1)-
      eisEmbedding (s.upper 0 0)^2*(eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)))/scale=
    -freq*eisEmbedding (s.upper 0 0*s.upper 0 1)/scale+
      freq*eisEmbedding (s.upper 0 0)^2*eisEmbedding (((g:SL(2,Eis))*H) 1 1)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)/scale by ring]
  simp only [AddChar.map_add_eq_mul,mul_div_assoc]

end FixedCuspShape
end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

end ReflectedBranchData
end CompletedGauss

end

end OAI
