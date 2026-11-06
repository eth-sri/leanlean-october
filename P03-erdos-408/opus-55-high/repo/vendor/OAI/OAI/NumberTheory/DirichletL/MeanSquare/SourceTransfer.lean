module

public import OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped SchwartzMap
open Finset Complex
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped ArithmeticFunction.Moebius
open Filter
open scoped ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped SchwartzMap
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open Set
open scoped Classical
open scoped Classical

open scoped Classical SchwartzMap
namespace InitialMeanSquare

section
open SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm columnLog)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end

end

open SecondPassArithmetic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def sourceObservation (x : SecondExpansionData ι) : O×O :=
  (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*x.frequency,
   primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*∏i∈x.overlap,p i)

end

end InitialMeanSquare

namespace CubicEisenstein

section
open Filter MeasureTheory LineDeriv
open scoped Classical SchwartzMap LineDeriv

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)
abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2

lemma euclideanL2Distribution_injective : Function.Injective euclideanL2Distribution := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker

lemma mem_euclideanWeakGradientGraph (f : EuclideanL2) (g : EuclideanGradientL2) :
    (f,g)∈euclideanWeakGradientGraph ↔ ∀j,
      ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)=euclideanL2Distribution (g j) := by
  change (fun j => ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)-
    euclideanL2Distribution (g j))=0 ↔ _
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

lemma euclideanWeakGradientGraph_unique (x : EuclideanL2 × EuclideanGradientL2)
    (hx : x∈euclideanWeakGradientGraph) (hzero : x.1=0) : x.2=0 := by
  have hh := (mem_euclideanWeakGradientGraph x.1 x.2).mp hx
  apply (WithLp.equiv 2 (Fin 3 → EuclideanL2)).injective
  funext j
  change x.2 j=(0:EuclideanL2)
  apply euclideanL2Distribution_injective
  simpa only [hzero,map_zero,lineDerivOp_zero,WithLp.ofLp_zero,Pi.zero_apply] using (hh j).symm

lemma schwartz_mem_euclideanWeakGradientGraph (f : 𝓢(EuclideanSpatial,ℂ)) :
    (f.toLp 2 volume,WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} f).toLp 2 volume))∈euclideanWeakGradientGraph := by
  apply (mem_euclideanWeakGradientGraph _ _).mpr
  intro j
  dsimp only [euclideanL2Distribution]
  simp only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq («μ» := volume) f _

end

open Filter MeasureTheory
open scoped Classical SchwartzMap LineDeriv

abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe

def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

lemma euclideanH1Embedding_eq_zero (u : EuclideanH1) (hu : euclideanH1Embedding u=0) : u=0 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (EuclideanL2 × EuclideanGradientL2)).injective
  apply Prod.ext
  · exact hu
  · exact euclideanWeakGradientGraph_unique u.1.ofLp u.2 hu

lemma euclideanH1Embedding_injective : Function.Injective euclideanH1Embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply euclideanH1Embedding_eq_zero
  rw [map_sub,huv,sub_self]

lemma euclideanH1_norm_sq (u : EuclideanH1) :
    ‖u‖^2=‖euclideanH1Embedding u‖^2+‖euclideanH1Gradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

end CubicEisenstein

open scoped Classical
namespace InitialMeanSquare
open ConcretePrimeRowBridge
open FirstCauchyArithmetic

def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp

lemma pool_support_product (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    idealSupport F (∏i∈S,i.val)=S := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏i∈S,i.val)≠(0:Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  ext i
  rw [mem_idealSupport_iff,UniqueFactorizationMonoid.mem_normalizedFactors_iff hn]
  simp only [family_prime_dvd_product_iff _ Subtype.val_injective S i,hp,true_and]

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · simp
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (by grind)⟩
    apply Finset.mem_filter.mpr
    refine ⟨by grind,?_⟩
    rwa [idealSupport_product_eq F hI (by grind)]
  simp

def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0

end InitialMeanSquare

open scoped Classical SchwartzMap
namespace InitialMeanSquare
open SecondPassArithmetic JointLogSeparation

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def sourceChildEnergy (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑u∈T,‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative)
    u.2 (if rowNegative then -u.1 else u.1)‖^2

def sourceGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2)*
    Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)

end

end InitialMeanSquare

end

end OAI
