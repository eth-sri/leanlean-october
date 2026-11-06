module

public import OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
public import OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open Finset Complex
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open Filter
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
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open Set
open scoped Classical
open scoped Classical

open scoped Classical
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
      apply Finset.prod_le_prod₀ (by simp)
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
  simp_all

end SecondPassArithmetic

open scoped Classical
namespace CompletedGauss

def completedDualScale (X r C K U B : ℝ) (D E : Ideal O) : ℝ :=
  r^3*(Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)^3*U*B^3*X/(K^2*C^2)

end CompletedGauss

namespace CompletedDyadic

def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0<ramifiedScale ρ q m := by unfold ramifiedScale; positivity

def normMajorant (deltaLoss A K t r H U B : ℝ) : ℝ :=
  K^deltaLoss/(r*Real.sqrt H)*
    (Real.sqrt K*B^(deltaLoss-1/2)*U^deltaLoss+B^deltaLoss*U^(deltaLoss+1/2))/(1+t*r^3*B^3*U)^A

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
    exact (Finset.single_le_sum (by simp) (Finset.mem_univ k)).trans
      (hbound i)
  have hsum (k : κ) : Summable (fun i => ‖f i k‖) :=
    hg.of_nonneg_of_le (by simp) (hpoint k)
  have hfp := Pi.summable.mpr (fun k => (hsum k).of_norm)
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

def completedSmoothDyadicBlock (V₀ V₁ V₂ W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  ∑n∈S i,∑v∈T i,quadraticRow k.val (primaryGenerator (n*v))*β i n v*
    (V₀ (Real.log ((Ideal.absNorm k.val:ℝ)/K))*
      V₁ (Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2))*
      V₂ (Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
          Real.exp (-2*Real.log ((Ideal.absNorm k.val:ℝ)/K)+
            Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
              3*Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))))

end CompletedGauss

end

end OAI
