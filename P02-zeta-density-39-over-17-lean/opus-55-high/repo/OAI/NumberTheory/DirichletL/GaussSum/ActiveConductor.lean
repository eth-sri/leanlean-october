module
public import OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
public import OAI.NumberTheory.DirichletL.Poisson.RadialFourier
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

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
open ActualEisensteinCubic
open ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic

section

 theorem activeSupport_nonempty_of_ne {α : Type*} [DecidableEq α]
    {S T : Finset α} (h : S ≠ T) : (activeSupport S T).Nonempty := by
  by_contra hn
  apply h
  have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  ext i
  simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
  grind

open ConcreteTraceCRT EisensteinSchwartzPoisson

 theorem finiteSexticRow_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 1 := by
  simp [finiteSexticRow]

 theorem finitePrimeModulus_norm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) : ‖eisEmbedding (finitePrimeModulus P)‖ = 1 := by
  have h := finitePrimeModulus_norm_sq P
  simp only [Finset.univ_eq_empty, Finset.prod_empty, map_one, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (finitePrimeModulus P))]

 theorem canonicalGaussSum_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalGaussSum P hcop hgood j = 1 := by
  let c := finitePrimeModulus P
  have hc : Ideal.span {c} = ⊤ := by
    simpa only [c, Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top] using
      span_finitePrimeModulus P
  have hzero (r : O ⧸ Ideal.span {c}) : r = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hc]; trivial)
  let : Subsingleton (O ⧸ Ideal.span {c}) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  unfold canonicalGaussSum
  change (∑ r : O ⧸ Ideal.span {c}, _ ) = 1
  rw [Fintype.sum_subsingleton _ 0]
  simp [principalSexticRow, finiteSexticQuotientRow]

 theorem canonicalNormalizedGauss_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j = 1 := by
  rw [canonicalNormalizedGauss, canonicalGaussSum_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, div_one]

noncomputable def squarefreePairPoissonZeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        (star (row 0) * paperRadialFourier W 0)

end

open EisensteinSchwartzPoisson

theorem primeSubset_moebius_norm_sum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  pm_7229
  simp only [Finset.prod_const_one, mul_one,  map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

theorem primeDensity_nonneg_le_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    0 ≤ (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ∧
      (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ≤ 1 := by
  have hfactor (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (P i) ∧
      1 - (1 : ℝ) / Ideal.absNorm (P i) ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Ideal.absNorm (P i) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (P i)))
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hnorm)
    · have : 0 ≤ (1 : ℝ) / Ideal.absNorm (P i) := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i _ => (hfactor i).1),
    Finset.prod_le_one₀ (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)⟩

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

noncomputable def idealPairPoissonZeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  pm_3474
  exact squarefreePairPoissonZeroMode (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def idealPrimeDensity (F : Finset (Ideal O)) (I : Ideal O) : ℝ :=
  ∏ i ∈ idealSupport F I, (1 - (1 : ℝ) / Ideal.absNorm i.val)

theorem idealPrimeDensity_mem_Icc
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥) (I : Ideal O) :
    idealPrimeDensity F I ∈ Set.Icc (0 : ℝ) 1 := by
  pm_1477 hFpos
  exact primeDensity_nonneg_le_one (fun i : primePool F => i.val) (idealSupport F I)

end ConcretePrimeRowBridge

namespace ShortDraftHeckeBridge

end ShortDraftHeckeBridge

namespace ConcretePrimeRowBridge

section
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

end

open ActualEisensteinCubic ShortDraftHeckeBridge

section
variable (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F)
include F I hI
theorem idealSupport_image_eq_factors :
    (idealSupport F I).image Subtype.val =
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
  ext P
  simp only [Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_idealSupport_iff F I p).mp hp
  · intro hP
    pm_5257 I hI
    exact ⟨p, (mem_idealSupport_iff F I p).mpr hP, rfl⟩

theorem idealSupport_product_eq (hsI : Squarefree I) :
    (∏ i ∈ idealSupport F I, i.val) = I := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    hsI.ne_zero).mp hsI
  calc
    _ = ∏ P ∈ (idealSupport F I).image Subtype.val, P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P := by
      rw [idealSupport_image_eq_factors F hI]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod = _
      rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hsI.ne_zero
end

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem activeSupport_product_mul_common_sq
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (P : ι → M) (S T : Finset ι) :
    (∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i) ^ 2 =
      (∏ i ∈ S, P i) * (∏ i ∈ T, P i) := by
  have hset : activeSupport S T = (S ∪ T) \ (S ∩ T) := by
    ext i
    simp only [activeSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  calc
    _ = ((∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i)) *
      (∏ i ∈ S ∩ T, P i) := by rw [pow_two, mul_assoc]
    _ = (∏ i ∈ S ∪ T, P i) * (∏ i ∈ S ∩ T, P i) := by
      rw [hset, Finset.prod_sdiff hsub]
    _ = _ := Finset.prod_union_inter

theorem activePrimeModulus_norm_sq
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S T : Finset ι) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ activeSupport S T, P i) : ℝ) := by
  rw [finitePrimeModulus_norm_sq]
  congr 2
  exact Finset.prod_coe_sort (activeSupport S T) P

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

end ConcretePrimeRowBridge

end

end OAI
