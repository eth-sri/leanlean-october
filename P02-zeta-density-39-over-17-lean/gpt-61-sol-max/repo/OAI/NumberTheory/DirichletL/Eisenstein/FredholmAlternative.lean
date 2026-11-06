module
import Mathlib
public import OAI.NumberTheory.DirichletL.CubicSieve.ClosedRecursion

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
                        
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
                     
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
           
                    
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
                    
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
           
                    
                    
                                                       
                                     
                    
                       
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
                                                               
                                                               
                                                               
                                                               
                       
                                     
                    
open Filter Asymptotics Ideal NumberField
           
                                     
                    
                                     
                    
                                     
                    
                       
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
                                  
                                  
open scoped BigOperators Classical SchwartzMap ContDiff
                                                       
                                  
                                                       
                                  
                                                       
                                                       
                                                       
                                  
                                                       
open MeasureTheory Set
                        
                                  
                                  
open ActualEisensteinCubic UniqueFactorizationMonoid
                        
                        
open scoped BigOperators Classical SchwartzMap
                                  

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

section

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma ker_orthogonal_restriction_injective (T : E→L[ℂ]F) :
    Function.Injective (T.domRestrict T.kerᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact T.ker.inner_right_of_mem_orthogonal hu u.2

lemma ker_orthogonal_restriction_range (T : E→L[ℂ]F) :
    Set.range (T.domRestrict T.kerᗮ)=Set.range T := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨u.1,rfl⟩
  · rintro _ ⟨u,rfl⟩
    refine ⟨⟨u-T.ker.starProjection u,T.ker.sub_starProjection_mem_orthogonal u⟩,?_⟩
    change T (u-T.ker.starProjection u)=T u
    rw [map_sub]
    have hz : T (T.ker.starProjection u)=0 := T.ker.starProjection_apply_mem u
    rw [hz,sub_zero]

section
variable (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2)
include T K hK A B hest

lemma ker_orthogonal_restriction_antilipschitz  :
    ∃D : NNReal,AntilipschitzWith D (T.domRestrict T.kerᗮ) := by
  apply antilipschitz_of_injective_compact_estimate (T.domRestrict T.kerᗮ)
    (K.domRestrict T.kerᗮ) (hK.comp_clm T.kerᗮ.subtypeL) A B
      (fun u => hest u) (ker_orthogonal_restriction_injective T)

lemma closed_range_of_compact_estimate  : IsClosed (Set.range T) := by
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  rw [←ker_orthogonal_restriction_range T]
  exact hD.isClosed_range (T.domRestrict T.kerᗮ).uniformContinuous
end


lemma selfAdjoint_range_eq_ker_orthogonal (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (hrange : IsClosed (Set.range T)) : T.range=T.kerᗮ := by
  have hh := T.orthogonal_ker
  rw [hT.adjoint_eq] at hh
  rw [hrange.submodule_topologicalClosure_eq] at hh
  exact hh.symm

end

section
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma selfAdjoint_fredholm_of_compact_estimate (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (K : E→L[ℂ]G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : T.IsFredholm := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : FiniteDimensional ℂ T.ker := finiteDimensional_ker_of_compact_estimate T K hK A B hest
  let : T.kerᗮ.CoFG :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  have hrange := closed_range_of_compact_estimate T K hK A B hest
  have heq := selfAdjoint_range_eq_ker_orthogonal T hT hrange
  let : T.range.CoFG := heq.symm ▸ (inferInstance : T.kerᗮ.CoFG)
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  have hf : (T.domRestrict T.kerᗮ).IsFredholm := by
    apply (hD.isClosedEmbedding (T.domRestrict T.kerᗮ).uniformContinuous).isFredholm
    have he : (T.domRestrict T.kerᗮ).range=T.range := by
      apply SetLike.coe_injective
      exact ker_orthogonal_restriction_range T
    simp_all
  exact (ContinuousLinearMap.isFredholm_domRestrict_iff T.ker.isClosed_orthogonal).mp hf

end

def kernelSpectralFormOperator (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ContinuousLinearMap.id ℂ KernelEnergyGraph-
    (z+1)•(kernelEnergyMass.adjoint.comp kernelEnergyMass)

lemma kernelSpectralFormOperator_inner (z : ℂ) (u : KernelEnergyGraph) :
    inner ℂ u (kernelSpectralFormOperator z u)=
      ((‖kernelEnergyGradient u‖^2:ℝ):ℂ)-z*((‖kernelEnergyMass u‖^2:ℝ):ℂ) := by
  change inner ℂ u (u-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass u))=_
  rw [inner_sub_right,inner_smul_right u (kernelEnergyMass.adjoint (kernelEnergyMass u)) (z + 1),kernelEnergyMass.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← ofReal_pow, kernelEnergyGraph_norm_sq, ofReal_add]
  ring

lemma kernelSpectralFormOperator_selfAdjoint (spectralParam : ℝ) :
    IsSelfAdjoint (kernelSpectralFormOperator (spectralParam:ℂ)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro u
  have hh := kernelSpectralFormOperator_inner (spectralParam:ℂ) u
  have hr : inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u=
      (((‖kernelEnergyGradient u‖^2-spectralParam*‖kernelEnergyMass u‖^2):ℝ):ℂ) := by
    simpa using congrArg (starRingEnd ℂ) hh
  change (starRingEnd ℂ) (inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u)=
    inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u
  rw [hr,Complex.conj_ofReal]

lemma scalar_compact_energy_estimate (m g n t k spectralParam C : ℝ)
    (_hn : 0≤n) (_ht : 0≤t) (hspectralParam : 0≤ spectralParam) (hspectralParamone : spectralParam<1) (hC : 0≤C)
    (hspace : n^2=m^2+g^2) (hcore : m^2≤g^2+C*k^2)
    (hform : g^2-spectralParam*m^2≤n*t) :
    n^2≤(4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2 := by
  have hd : 0<1-spectralParam := sub_pos.mpr hspectralParamone
  have hlow : (1-spectralParam)/2*n^2≤n*t+C*k^2 := by
    nlinarith [mul_nonneg (show 0≤1+spectralParam by linarith) (sub_nonneg.mpr hcore),
      mul_nonneg hd.le (mul_nonneg hC (sq_nonneg k))]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0≤4*(1-spectralParam) by positivity)
  have hsq : (1-spectralParam)^2*n^2≤4*t^2+4*(1-spectralParam)*C*k^2 := by
    nlinarith [sq_nonneg ((1-spectralParam)*n-2*t)]
  have he : (4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2=
      (4*t^2+4*(1-spectralParam)*C*k^2)/(1-spectralParam)^2 := by
    field_simp [hd.ne']
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith [hsq])

lemma kernelSpectralFormOperator_compact_estimate
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ) (hC : 0≤C)
    (hcore : ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
      C*‖kernelEnergyMassRestriction K hK u‖^2)
    (spectralParam : ℝ) (hspectralParam : 0≤ spectralParam) (hspectralParamone : spectralParam<1) (u : KernelEnergyGraph) :
    ‖u‖^2≤(4/(1-spectralParam)^2)*‖kernelSpectralFormOperator (spectralParam:ℂ) u‖^2+
      (4*C/(1-spectralParam))*‖kernelEnergyMassRestriction K hK u‖^2 := by
  apply scalar_compact_energy_estimate ‖kernelEnergyMass u‖ ‖kernelEnergyGradient u‖
    ‖u‖ ‖kernelSpectralFormOperator (spectralParam:ℂ) u‖ ‖kernelEnergyMassRestriction K hK u‖ spectralParam C
    (norm_nonneg _) (norm_nonneg _) hspectralParam hspectralParamone hC (kernelEnergyGraph_norm_sq u) (hcore u)
  have hh := re_inner_le_norm (𝕜 := ℂ) u (kernelSpectralFormOperator (spectralParam:ℂ) u)
  rw [kernelSpectralFormOperator_inner] at hh
  simpa only [RCLike.re_to_complex,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hh

lemma kernelSpectralFormOperator_solution_graph (z : ℂ) (F : KernelQuotientL2)
    (v : KernelEnergyGraph) (hv : kernelSpectralFormOperator z v=kernelVariationalSolution F) :
    (kernelEnergyMass v,F+z•kernelEnergyMass v)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  have hh : v-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass v)=kernelEnergyMass.adjoint F := hv
  have hv' : kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v)=v := by
    rw [map_add,map_smul]
    exact (sub_eq_iff_eq_add.mp hh).symm
  have he : kernelEnergyMass v+(F+z•kernelEnergyMass v)=F+(z+1)•kernelEnergyMass v := by
    rw [add_smul,one_smul]
    abel
  rw [he]
  change kernelEnergyMass (kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v))=kernelEnergyMass v
  rw [hv']

lemma kernelSpectralFormOperator_of_domain (z : ℂ) (u : kernelEnergyLaplacian.domain) :
    kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u))=
      kernelVariationalSolution (kernelEnergyLaplacian u-z•(u:KernelQuotientL2)) := by
  have hu : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  change kernelVariationalSolution (kernelEnergyLaplacian u+u)-
    (z+1)•kernelVariationalSolution (kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=_
  rw [hu,←map_smul,←map_sub]
  congr 1
  rw [add_smul,one_smul]
  abel

theorem kernelSpectralFormOperator_isFredholm (spectralParam : ℝ)
    (hzero : 0≤ spectralParam) (hone : spectralParam<1) :
    (kernelSpectralFormOperator (spectralParam:ℂ)).IsFredholm := by
  obtain ⟨K,hK,C,hC,hcompact,hcoercive⟩ := kernel_global_exterior_coercivity
  exact selfAdjoint_fredholm_of_compact_estimate _
    (kernelSpectralFormOperator_selfAdjoint spectralParam)
    (kernelEnergyMassRestriction K hK.measurableSet) hcompact
    (4/(1-spectralParam)^2) (4*C/(1-spectralParam))
    (kernelSpectralFormOperator_compact_estimate K hK.measurableSet C hC hcoercive spectralParam hzero hone)

theorem kernel_theta_spectral_fredholm :
    (kernelSpectralFormOperator (8/9:ℂ)).IsFredholm := by
  convert kernelSpectralFormOperator_isFredholm (8/9) (by norm_num) (by norm_num) using 1
  norm_num

end CubicEisenstein

namespace CanonicalRowCompletion
open SecondPassArithmetic

theorem cubeLogRange_sq_small_power (b ε : ℝ) (_hb : 0≤b) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X Z : ℝ,0≤X → 1≤Z → X≤Z^3 →
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^ε := by
  let B:=max 1 b
  let deltaLoss:=ε/2
  let C₀:=1+Real.log B+3/deltaLoss
  have hB : 1≤B:=le_max_left _ _
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hδ : 0<deltaLoss:=by dsimp [deltaLoss];positivity
  have hlogB :=Real.log_nonneg hB
  have hC₀ : 0<C₀:=by dsimp [C₀];positivity
  refine ⟨C₀^2,by positivity,?_⟩
  intro X Z hX hZ hXZ
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hZ3 : 1≤Z^3:=one_le_pow₀ hZ
  have hY : 1≤B*Z^3:=one_le_mul_of_one_le_of_one_le hB hZ3
  have hxY : max 1 (b*X)≤B*Z^3 := by
    apply max_le hY
    calc
      b*X ≤ B*X:=mul_le_mul_of_nonneg_right (le_max_right _ _) hX
      _ ≤ B*Z^3:=mul_le_mul_of_nonneg_left hXZ hB0.le
  have hcard : ((cubeLogRange b X).card:ℝ)≤1+Real.log B+3*Real.log Z := by
    rw [cubeLogRange_card,Nat.cast_add,Nat.cast_one]
    have hlog:=normLogBin_le_log_upper (max 1 (b*X)) (B*Z^3)
      (zero_lt_one.trans_le (le_max_left _ _)) hxY hY
    rw [Real.log_mul hB0.ne' (pow_pos hZ0 3).ne',Real.log_pow] at hlog
    norm_num at hlog
    linarith
  have hr :=Real.one_le_rpow hZ hδ.le
  have hl :=Real.log_le_rpow_div hZ0.le hδ
  have hc : 1+Real.log B+3*Real.log Z≤C₀*Z^deltaLoss := by
    calc
      _ ≤ (1+Real.log B)*Z^deltaLoss+3*(Z^deltaLoss/deltaLoss) := by
        gcongr
        exact le_mul_of_one_le_right (by linarith) hr
      _ = _:=by dsimp [C₀];ring
  calc
    _ ≤ (C₀*Z^deltaLoss)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard.trans hc) 2
    _ = C₀^2*Z^ε:=by
      rw [mul_pow,←Real.rpow_natCast (Z^deltaLoss) 2,←Real.rpow_mul hZ0.le]
      congr 1
      dsimp [deltaLoss]
      simp

end CanonicalRowCompletion





open scoped BigOperators Classical SchwartzMap ContDiff



open MeasureTheory
                                                       





