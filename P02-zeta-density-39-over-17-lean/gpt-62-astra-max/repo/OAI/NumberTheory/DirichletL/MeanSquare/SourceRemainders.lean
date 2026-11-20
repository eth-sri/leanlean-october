module
public import OAI.NumberTheory.DirichletL.MeanSquare.HighRadialBounds
public import OAI.NumberTheory.DirichletL.CubicSieve.PaddedPassage

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i:S=>p i.val) (fun i=>hp i.val) (columnPrimeCoprime p hcop S)
    (fun i=>hg i.val) (fun i=>hc i.val) (fun i=>e i.val)
    (fun i=>threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i.val i.property)
    (fun i=>threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i.val i.property)
  change ‖star (columnCoefficient p hp hcop hg N*C₁ N)*
    (columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S=>p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val)*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖ := by
  have hn : 0<‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end

theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)

end FirstPassCubeLabels

end

end OAI
