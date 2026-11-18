module
public import OAI.NumberTheory.DirichletL.MeanSquare.PolynomialHeight
public import OAI.NumberTheory.DirichletL.CubicSieve.RankMargins

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

namespace CompletedHeight

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O

end

open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O

end CompletedHeight

open scoped BigOperators Classical
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open UnrestrictedIdealReindex (unitIdealEquiv span_unit_generator)
local instance : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def rowUnit (z : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ :=
  if hz : z=0 then 1 else (unitIdealEquiv.symm ⟨z,hz⟩).1

lemma rowUnit_spec (z : ActualEisensteinCubic.O) (hz : z≠0) :
    (rowUnit z).val * idealGenerator (Ideal.span {z}) = z := by
  let p := unitIdealEquiv.symm ⟨z,hz⟩
  have hp : p.1.val*idealGenerator p.2.val=z :=
    congrArg Subtype.val (unitIdealEquiv.apply_symm_apply ⟨z,hz⟩)
  have hI : p.2.val=Ideal.span {z} := by
    rw [←hp,span_unit_generator]
  simpa only [rowUnit,dite_eq_right hz,←hI] using hp

def unitIdealPoint (z : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ × Ideal ActualEisensteinCubic.O := (rowUnit z,Ideal.span {z})

lemma unitIdealPoint_inj (z w : ActualEisensteinCubic.O) (hz : z≠0) (hw : w≠0)
    (h : unitIdealPoint z=unitIdealPoint w) : z=w := by
  have hu : rowUnit z=rowUnit w := congrArg Prod.fst h
  have hI : Ideal.span {z}=Ideal.span {w} := congrArg Prod.snd h
  rw [←rowUnit_spec z hz,←rowUnit_spec w hw,hu,hI]

theorem sum_nonzero_element_le_units (T : Finset ActualEisensteinCubic.O) (hT : ∀z∈T,z≠0)
    (v : ActualEisensteinCubic.O→ℝ) (hv : ∀z,0≤v z) :
    (∑z∈T,v z) ≤ ∑u : ActualEisensteinCubic.Oˣ,∑I∈T.image (fun z=>Ideal.span {z}),
      v (u.val*idealGenerator I) := by
  let f : ActualEisensteinCubic.Oˣ×Ideal ActualEisensteinCubic.O→ℝ := fun p=>v (p.1.val*idealGenerator p.2)
  have hinj : Set.InjOn unitIdealPoint T := by
    intro z hz w hw he
    exact unitIdealPoint_inj z w (hT z hz) (hT w hw) he
  have he : (∑z∈T,v z)=∑p∈T.image unitIdealPoint,f p := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [f,unitIdealPoint]
    rw [rowUnit_spec z (hT z hz)]
  have hsub : T.image unitIdealPoint ⊆
      (Finset.univ : Finset ActualEisensteinCubic.Oˣ) ×ˢ T.image (fun z=>Ideal.span {z}) := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  rw [he]
  calc
    _ ≤ ∑p∈(Finset.univ : Finset ActualEisensteinCubic.Oˣ) ×ˢ T.image (fun z=>Ideal.span {z}),f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>hv _)
    _ = _ := by rw [Finset.sum_product]

lemma image_span_nonzero_norm (T : Finset ActualEisensteinCubic.O) (K : ℝ)
    (hT : ∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤K) :
    ∀I∈T.image (fun z=>Ideal.span {z}),I≠0 ∧ (Ideal.absNorm I:ℝ)≤K := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  exact ⟨Ideal.span_singleton_eq_bot.not.mpr (hT z hz).1,(hT z hz).2⟩

lemma unit_card : Fintype.card ActualEisensteinCubic.Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end CompletedUnitRows

end

end OAI
