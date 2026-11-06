module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
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
namespace CanonicalQuadraticSieve
open ConcretePrimeRowBridge
open EisensteinSchwartzPoisson

def squarefreeIdealRange (K : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊K⌋₊).filter Squarefree

theorem mem_squarefreeIdealRange {K : ℝ} {I : Ideal O} :
    I ∈ squarefreeIdealRange K ↔ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K := by
  rw [squarefreeIdealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, hs⟩
    refine ⟨hs, ?_⟩
    have hK : 0 ≤ K := by
      by_contra hn
      have hz : ⌊K⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hK)
  · rintro ⟨hs, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => hs.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, hs⟩

theorem tsum_squarefree_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : squarefreeIdealRange K, f B.val := by
  let e : squarefreeIdealRange K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    apply Subtype.ext
    exact by grind
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (ite_eq_right hn)
    exact ⟨⟨B.val, mem_squarefreeIdealRange.mpr (by grind)⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact ite_eq_left (mem_squarefreeIdealRange.mp B.property).2

theorem dualSquarefreeLow_principal_finite
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    dualSquarefreeLow I J W t K =
      ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val *
        dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
          (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) := by
  rw [dualSquarefreeLow_principal I J hI hJ hray W t K ht]
  exact tsum_squarefree_norm_cutoff K (fun B => unrestrictedPairCharacter I J B *
    dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
      (Real.sqrt (1 / (t * (Ideal.absNorm B : ℝ)))))

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondDiagonalMass (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : ℝ :=
  ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 *
    ∏ i ∈ G, (1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i}))

include hinj in

theorem truncatedSecondZero_eq_density
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) :
    truncatedSecondZero p hg F Ψ m c d H W Y K =
      (Y : ℂ) * paperRadialFourier W 0 * (secondDiagonalMass p hg F Ψ m c d H : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold truncatedSecondZero secondDiagonalMass
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro G hG
  have hd : (∑ E : G.powerset, if (0 : O) ∈ K G E.val then
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)
      else 0) = ∏ i ∈ G, (1 - (1 : ℂ) / Ideal.absNorm (Ideal.span {p i})) := by
    have hi (E : G.powerset) := hzero G hG E.val E.property
    simp only [hi, ite_true, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast]
    rw [Finset.sum_coe_sort (s := G.powerset) (f := fun E : Finset ι =>
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (Ideal.absNorm (∏ i ∈ E, Ideal.span {p i}) : ℂ))]
    exact primeSubset_moebius_norm_sum _ hprime hinj G
  rw [hd]
  have hi : secondInputCoefficient p hg Ψ m c d H G =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) G * H G := by
    simp only [secondInputCoefficient, mul_one]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hi, norm_mul, mul_pow, Complex.ofReal_mul]
  grind

omit [DecidableEq ι] in
theorem secondDiagonalMass_nonneg_le
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) :
    0 ≤ secondDiagonalMass p hg F Ψ m c d H ∧
      secondDiagonalMass p hg F Ψ m c d H ≤
        ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 := by
  constructor
  · exact Finset.sum_nonneg (fun G hG => mul_nonneg (sq_nonneg _)
      (primeDensity_nonneg_le_one (fun i => Ideal.span {p i}) G).1)
  · apply Finset.sum_le_sum
    intro G hG
    exact mul_le_of_le_one_right (sq_nonneg _)
      (primeDensity_nonneg_le_one (fun i => Ideal.span {p i}) G).2

include hinj in

theorem truncatedSecondZero_norm_le
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      |Y| * ‖paperRadialFourier W 0‖ *
        ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 := by
  rw [truncatedSecondZero_eq_density p hg hinj F Ψ m c d H W Y K hzero]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_of_nonneg (secondDiagonalMass_nonneg_le p hg F Ψ m c d H).1]
  exact mul_le_mul_of_nonneg_left (secondDiagonalMass_nonneg_le p hg F Ψ m c d H).2
    (by positivity)

end
section


def secondDyadicSector {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (fun x => label R x = j)

theorem sum_secondDyadicSector {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (H : SecondExpansionData ι → ℂ) :
    (∑ j : κ, ∑ x ∈ secondDyadicSector F K R label j, H x) =
      ∑ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R, H x := by
  simp only [secondDyadicSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem truncatedSecondSource_eq_zero_add_dyadic
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondDyadicSector F K R label j) H H W Y := by
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro R hR
  simp only [secondExpansionSource, sum_secondDyadicSector]

end

section

open scoped Classical SchwartzMap
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (columnLog jLabel b0Label)
open JointLogSeparation (tripleCoefficient)

end

open scoped Classical SchwartzMap
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

namespace SecondPassIntegration

section

open scoped Classical SchwartzMap
open SecondPassFiber (OldTuple newLabel newRow Valid)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end


end SecondPassIntegration

open scoped Classical SchwartzMap
namespace SecondPassArithmetic
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
