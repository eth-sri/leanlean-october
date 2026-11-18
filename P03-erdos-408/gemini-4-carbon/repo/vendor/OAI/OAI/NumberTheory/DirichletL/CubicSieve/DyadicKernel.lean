module

public import OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
public import OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open ActualEisensteinCubic ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open scoped ContDiff
open Set

namespace SecondPassArithmetic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma multiplicityRow_norm_le_one (B : Finset ι) (v : ι→ℕ) (z:O) :
    ‖multiplicityRow (fun i=>Ideal.span {p i}) hg B v z‖≤1 := by
  simp only [multiplicityRow,norm_prod,norm_pow]
  calc
    _ ≤ ∏i∈B,(1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun i hi=>by positivity)
      intro i hi
      apply pow_le_one₀ (norm_nonneg _)
      let : Fintype (O⧸Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma multiplicityRow_support (B : Finset ι) (v : ι→₀ℕ) (hv : v.support⊆B) (z:O) :
    multiplicityRow (fun i=>Ideal.span {p i}) hg B v z =
      multiplicityRow (fun i=>Ideal.span {p i}) hg v.support v z := by
  unfold multiplicityRow
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

end SecondPassArithmetic


namespace CompletedDyadic

def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0<ramifiedScale ρ q m := by unfold ramifiedScale; positivity


end CompletedDyadic

namespace CompletedGauss

theorem finite_tsum_energy_bound {κ α : Type*} [Fintype κ]
    (f : α→κ→ℂ) (g : α→ℝ) (hg0 : ∀i,0≤g i) (hg : Summable g)
    (hbound : ∀i,(∑k,‖f i k‖^2)≤(g i)^2) :
    (∀k,Summable (fun i => ‖f i k‖)) ∧
    (∑k,‖∑'i,f i k‖^2)≤(∑'i,g i)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : α→EuclideanSpace ℂ κ := fun i => e.symm (f i)
  have hF (i : α) : ‖F i‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    rw [EuclideanSpace.norm_sq_eq]
    exact hbound i
  have hpoint (k : κ) (i : α) : ‖f i k‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖f i j‖) (Finset.mem_univ k)).trans
      (hbound i)
  have hsum (k : κ) : Summable (fun i => ‖f i k‖) :=
    hg.of_nonneg_of_le (fun i => norm_nonneg _) (hpoint k)
  have hfp : Summable f := Pi.summable.mpr (fun k => (hsum k).of_norm)
  have he : (∑'i,F i)=e.symm (fun k => ∑'i,f i k) := by
    rw [show (fun i => F i)=(fun i => e.symm (f i)) from rfl,←e.symm.map_tsum]
    congr 1
    funext k
    exact Pi.tsum_apply hfp
  have hn : ‖e.symm (fun k => ∑'i,f i k)‖≤∑'i,g i := by
    rw [←he]
    exact tsum_of_norm_bounded hg.hasSum hF
  refine ⟨hsum,?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq] at hs
  exact hs

open CanonicalQuadraticSieve CompletedDyadic


end CompletedGauss

end

end OAI
