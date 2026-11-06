module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups

section
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

instance complexSLTopology : TopologicalSpace (SL(2,ℂ)) :=
  inferInstanceAs (TopologicalSpace {A : Matrix (Fin 2) (Fin 2) ℂ // A.det=1})

lemma continuous_complexSL_coe :
    Continuous (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
  continuous_subtype_val

lemma continuous_complexSL_mul (g : SL(2,ℂ)) :
    Continuous (fun h : SL(2,ℂ) => g*h) := by
  apply Continuous.subtype_mk
  change Continuous (fun h : SL(2,ℂ) =>
    (g : Matrix (Fin 2) (Fin 2) ℂ)*(h : Matrix (Fin 2) (Fin 2) ℂ))
  fun_prop

lemma continuous_coordinateSection : Continuous coordinateSection := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  pm_1043
  have hne : ∀w : UpperCoordinates,(Real.sqrt w.1.2 : ℂ)≠0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  fin_cases i <;> fin_cases j
  simp_all
  fun_prop
  · exact continuous_const
  fun_prop

lemma continuous_hyperbolicProjection :
    Continuous (fun g : SL(2,ℂ) => (g : HyperbolicSpace)) :=
  continuous_quotient_mk'

lemma continuous_upperCoordinates :
    Continuous (fun w : UpperCoordinates => upperPoint w.1.1 w.1.2 w.2) :=
  continuous_hyperbolicProjection.comp continuous_coordinateSection

lemma continuous_translatedUpperCoordinates (g : SL(2,ℂ)) :
    Continuous (fun w : UpperCoordinates => g • upperPoint w.1.1 w.1.2 w.2) := by
  exact continuous_hyperbolicProjection.comp
    ((continuous_complexSL_mul g).comp continuous_coordinateSection)

def integralOrbitRel (H : Subgroup (SL(2,O))) : Setoid HyperbolicSpace where
  r w w' := ∃h : H, integralComplexMatrix (h:SL(2,O)) • w = w'
  iseqv := ⟨by intro w; exact ⟨1,by simp⟩,
    by
      rintro w w' ⟨h,hh⟩
      refine ⟨h⁻¹,?_⟩
      rw [←hh]
      simp [←mul_smul],
    by
      rintro w w' w'' ⟨h,hh⟩ ⟨k,hk⟩
      refine ⟨k*h,?_⟩
      simpa only [Subgroup.coe_mul,map_mul,mul_smul,hh] using hk⟩

abbrev IntegralOrbitQuotient (H : Subgroup (SL(2,O))) := Quotient (integralOrbitRel H)

def integralOrbitProjection (H : Subgroup (SL(2,O))) :
    HyperbolicSpace → IntegralOrbitQuotient H := Quotient.mk _

section
variable (H : Subgroup (SL(2,O)))
include H
lemma continuous_integralOrbitProjection :
    Continuous (integralOrbitProjection H) := continuous_quotient_mk'

lemma integralOrbitProjection_eq (h : H) (w : HyperbolicSpace) :
    integralOrbitProjection H (integralComplexMatrix (h:SL(2,O)) • w)=
      integralOrbitProjection H w := by
  apply Eq.symm
  exact Quotient.sound ⟨h,rfl⟩
end

end

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

def truncatedFordLift (T : ℝ) (p : truncatedFordBox T) : UpperCoordinates :=
  ⟨p.1,lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/3)) p.2.2.1⟩

lemma continuous_truncatedFordLift (T : ℝ) : Continuous (truncatedFordLift T) :=
  continuous_subtype_val.subtype_mk _

def fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) (p : UpperCoordinates) :
    IntegralOrbitQuotient H := integralOrbitProjection H
      (integralComplexMatrix r⁻¹ • upperPoint p.1.1 p.1.2 p.2)

lemma continuous_fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) :
    Continuous (fordOrbitChart H r) :=
  (continuous_integralOrbitProjection H).comp
    (continuous_translatedUpperCoordinates (integralComplexMatrix r⁻¹))

def compactFordCore (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  ⋃r∈S, Set.range (fun p : truncatedFordBox T => fordOrbitChart H r (truncatedFordLift T p))

lemma compactFordCore_isCompact (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    IsCompact (compactFordCore H S T) := by
  let : CompactSpace (truncatedFordBox T) :=
    isCompact_iff_compactSpace.mp (truncatedFordBox_isCompact T)
  apply S.isCompact_biUnion
  intro r hr
  exact isCompact_range ((continuous_fordOrbitChart H r).comp (continuous_truncatedFordLift T))

def fordCuspTail (H : Subgroup (SL(2,O))) (r : SL(2,O)) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  fordOrbitChart H r '' {p : UpperCoordinates | Complex.normSq p.1.1≤1/3 ∧
    Real.sqrt (2/3)≤p.1.2 ∧ T<p.1.2}

theorem finiteIndex_compact_core_cusp_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore H S T) ∧
      Set.univ=compactFordCore H S T ∪ ⋃r∈S, fordCuspTail H r T := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  refine ⟨S,fun T => ⟨compactFordCore_isCompact H S T,?_⟩⟩
  apply Set.Subset.antisymm
  · intro q hq
    induction q using Quotient.inductionOn with | _ w =>
      obtain ⟨h,r,hr,z,v,hv,heq,hz,hfloor⟩ := hS w
      have hqeq : integralOrbitProjection H w=fordOrbitChart H r ⟨(z,v),hv⟩ := by
        rw [←integralOrbitProjection_eq H h w,heq]
        rfl
      change integralOrbitProjection H w∈_
      rw [hqeq]
      by_cases hT : v≤T
      · apply Or.inl
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),mem_truncatedFordBox z v T hz hfloor hT⟩,rfl⟩
      · apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),hv⟩,⟨hz,hfloor,lt_of_not_ge hT⟩,rfl⟩
  · exact Set.subset_univ _

theorem globalKubotaKernel_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore globalKubotaKernel S T) ∧
      Set.univ=compactFordCore globalKubotaKernel S T ∪ ⋃r∈S, fordCuspTail globalKubotaKernel r T := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_compact_core_cusp_cover globalKubotaKernel

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped Classical SchwartzMap FourierTransform
open MeasureTheory

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open JointLogSeparation (outerWindow)

local instance {ι : Type*} : Nonempty (GlobalSecondData ι) :=
  ⟨⟨⟨0,0,∅,∅⟩,∅,∅,∅,⟨∅,∅,∅,0⟩⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open JointLogSeparation (outerWindow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct jLabel b0Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end

end SecondPassArithmetic

end

end OAI
