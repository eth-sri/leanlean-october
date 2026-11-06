module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.CompactProfiles

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 

 
namespace SecondPassArithmetic
 
open JointLogSeparation (frequencyTwist)



end SecondPassArithmetic

namespace CubicEisenstein
 
open scoped       MatrixGroups Matrix Pointwise

local notation "O" => ActualEisensteinCubic.O

lemma complex_norm_mul_add_sq (a b c d : ℂ) :
    ‖a*c+b*d‖^2≤(‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have ht : ‖a*c+b*d‖≤‖a‖*‖c‖+‖b‖*‖d‖ := by simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  have hs := pow_le_pow_left₀ (norm_nonneg (a*c+b*d)) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]

lemma matrixFrobenius_nonneg  g  : 0≤matrixFrobenius g := by
  unfold matrixFrobenius rowEnergy
  positivity

lemma matrixFrobenius_mul_le  g h  :
    matrixFrobenius (g*h)≤matrixFrobenius g*matrixFrobenius h := by
  have hb (i j : Fin 2) := complex_norm_mul_add_sq (g i 0) (g i 1) (h 0 j) (h 1 j)
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  nlinarith only [hb 0 0,hb 0 1,hb 1 0,hb 1 1]

lemma matrixFrobenius_inv  g  : matrixFrobenius g⁻¹=matrixFrobenius g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow]
  change ‖g 1 1‖^2+‖-g 0 1‖^2+(‖-g 1 0‖^2+‖g 0 0‖^2)=_
  simp only [norm_neg]
  ring

lemma hyperbolicFrobenius_nonneg  w  : 0≤hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ g => exact matrixFrobenius_nonneg g

lemma matrixFrobenius_le_displacement  g   w  :
    matrixFrobenius g≤hyperbolicFrobenius (g • w)*hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change matrixFrobenius g≤matrixFrobenius (g*h)*matrixFrobenius h
    have hb := matrixFrobenius_mul_le (g*h) h⁻¹
    simpa only [mul_inv_cancel_right,matrixFrobenius_inv] using hb

instance integralSubgroupContinuousAction (H : Subgroup (SL(2,O))) :
    ContinuousConstSMul H HyperbolicSpace :=
  ⟨fun M => continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))⟩

instance integralSubgroupProperlyDiscontinuous (H : Subgroup (SL(2,O))) :
    ProperlyDiscontinuousSMul H HyperbolicSpace where
  finite_disjoint_inter_image := by
    intro source target hsource htarget
    obtain ⟨C,hC⟩ := hsource.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    obtain ⟨D,hD⟩ := htarget.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    have hfin : Set.Finite {M : H | matrixFrobenius (integralComplexMatrix (M:SL(2,O)))≤
        max D 0*max C 0} := by
      have hf := Set.Finite.preimage (f := fun M : H => (M:SL(2,O))) Subtype.val_injective.injOn
        (integral_frobenius_sublevel_finite 1 (max D 0*max C 0))
      simpa only [mul_one,Set.preimage_ofPred_eq] using hf
    apply hfin.subset
    rintro M ⟨u,⟨w,hw,rfl⟩,hu⟩
    have hb := matrixFrobenius_le_displacement (integralComplexMatrix (M:SL(2,O))) w
    apply hb.trans
    apply mul_le_mul
    · exact ((le_abs_self _).trans (hD _ hu)).trans (le_max_left _ _)
    · exact ((le_abs_self _).trans (hC _ hw)).trans (le_max_left _ _)
    · exact hyperbolicFrobenius_nonneg _
    · exact le_max_right _ _

end CubicEisenstein

 
open scoped       MatrixGroups Pointwise

namespace CubicEisenstein

section
local notation "O" => ActualEisensteinCubic.O

instance upperCoordinatesLocallyCompact : LocallyCompactSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).locallyCompactSpace
instance hyperbolicLocallyCompact : LocallyCompactSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
instance hyperbolicSecondCountable : SecondCountableTopology HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.secondCountableTopology

instance upperCoordinatesPolish : PolishSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).polishSpace
instance hyperbolicPolish : PolishSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isClosedEmbedding.polishSpace

lemma integralOrbitRel_eq  H  :
    integralOrbitRel H=MulAction.orbitRel H HyperbolicSpace := by
  ext u v
  solve_by_elim

instance integralOrbitQuotientT2 (H : Subgroup (SL(2,O))) : T2Space (IntegralOrbitQuotient H) := by
  change T2Space (Quotient (integralOrbitRel H))
  rw [integralOrbitRel_eq]
  infer_instance

lemma integralSubgroupFree (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCancelSMul H HyperbolicSpace :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (subgroup_action_free H hH)

lemma integralOrbitProjection_eq_iff  H   u v  :
    integralOrbitProjection H u=integralOrbitProjection H v ↔ u∈MulAction.orbit H v := by
  constructor
  · intro he
    obtain ⟨M,hM⟩ := Quotient.exact he.symm
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨M,hM⟩

theorem integralOrbitProjection_quotientCovering  H 
    (hH : H≤CubicKubota.levelThree) : IsQuotientCoveringMap (integralOrbitProjection H) H := by
  let : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  have hq : Topology.IsQuotientMap (integralOrbitProjection H) := isQuotientMap_quotient_mk'
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (integralOrbitProjection_eq_iff H _ _)

lemma integralOrbitProjection_covering  H  (hH : H≤CubicKubota.levelThree) :
    IsCoveringMap (integralOrbitProjection H) :=
  (integralOrbitProjection_quotientCovering H hH).isCoveringMap

lemma integralOrbitProjection_openQuotient  H  (hH : H≤CubicKubota.levelThree) :
    IsOpenQuotientMap (integralOrbitProjection H) :=
  ⟨Quotient.mk_surjective,continuous_integralOrbitProjection H,
    (integralOrbitProjection_covering H hH).isOpenMap⟩

instance kernelQuotientLocallyCompact : LocallyCompactSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).locallyCompactSpace
instance kernelQuotientSecondCountable : SecondCountableTopology (IntegralOrbitQuotient globalKubotaKernel) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree)

instance kernelQuotientBorel : BorelSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  Quotient.borelSpace

lemma kernelQuotient_localHomeomorph : IsLocalHomeomorph (integralOrbitProjection globalKubotaKernel) :=
  (integralOrbitProjection_covering globalKubotaKernel globalKubotaKernel_le_levelThree).isLocalHomeomorph

end

 
open scoped           ENNReal

lemma integralOrbitProjection_preimage_image  H 
     S  :
    integralOrbitProjection H ⁻¹' (integralOrbitProjection H '' S)=⋃M:H,M • S := by
  ext w
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff H w u).mp he.symm
    exact Set.mem_iUnion.mpr ⟨M,⟨u,hu,hM⟩⟩
  · intro hw
    obtain ⟨M,u,hu,rfl⟩ := Set.mem_iUnion.mp hw
    exact ⟨u,hu,(integralOrbitProjection_eq H M u).symm⟩

lemma kernelProjection_translates_disjoint (S : Set HyperbolicSpace)
    (hS : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    Pairwise (fun M N : globalKubotaKernel => Disjoint (M • S) (N • S)) := by
  let : IsCancelSMul globalKubotaKernel HyperbolicSpace :=
    integralSubgroupFree globalKubotaKernel globalKubotaKernel_le_levelThree
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w,hw,rfl⟩ ⟨u,hu,he⟩
  have hwu : w=u := hS hw hu (by
    calc
      integralOrbitProjection globalKubotaKernel w=
          integralOrbitProjection globalKubotaKernel (M • w) := (integralOrbitProjection_eq _ M w).symm
      _=integralOrbitProjection globalKubotaKernel (N • u) := congrArg _ he.symm
      _=integralOrbitProjection globalKubotaKernel u := integralOrbitProjection_eq _ N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)

theorem kernelProjection_measure_image  S  (hS : MeasurableSet S)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    integralQuotientVolume globalKubotaKernel (integralOrbitProjection globalKubotaKernel '' S)=
      hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn hinj
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image,Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (globalKubotaKernel_isFundamentalDomain.measure_eq_tsum S).symm
  · intro M N hMN
    exact (kernelProjection_translates_disjoint S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)

theorem kernelProjection_measurePreserving_on  U  (hU : MeasurableSet U)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) U) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict U)
      ((integralQuotientVolume globalKubotaKernel).restrict (integralOrbitProjection globalKubotaKernel '' U)) := by
  refine ⟨measurable_integralOrbitProjection _,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.restrict_apply hB]
  have hset : B∩(integralOrbitProjection globalKubotaKernel '' U)=
      integralOrbitProjection globalKubotaKernel '' (integralOrbitProjection globalKubotaKernel ⁻¹' B∩U) := by
    grind
  rw [hset,kernelProjection_measure_image _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]

theorem kernelL2_continuous_compact_approx (f : KernelQuotientL2)  ε  (hε : ε≠0) :
    ∃g : IntegralOrbitQuotient globalKubotaKernel → ℂ,
      HasCompactSupport g ∧ eLpNorm ((f : _ → ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)≤ε ∧
      Continuous g ∧ MemLp g 2 (integralQuotientVolume globalKubotaKernel) := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε

end CubicEisenstein

 
namespace SecondPassArithmetic

section
 
open FirstPassCubeLabels (primeProductNorm columnLog b0Label)



namespace GlobalFirstData
variable {ι : Type*}

end GlobalFirstData

namespace GlobalSecondData
variable {ι : Type*}




end GlobalSecondData



variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

 
open FirstPassCubeLabels (primeProductNorm columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
