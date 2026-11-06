module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.UnrestrictedCharacters

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

end SecondPassIntegration


namespace SecondPassArithmetic

section
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem secondPreColumn_zero_of_common_overlap
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (G S : Finset ι)
    (hSG : ¬ Disjoint S G) :
    secondPreColumn p hp hcop hg Ψ (m * ∏ i ∈ G, p i) c d e k H S = 0 := by
  have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S (m * ∏ i ∈ G, p i) = 0 := by
    rw [FirstPassCubeLabels.mask_mul _ hg S,
      commonProduct_mask p hg hinj S G, ite_eq_right hSG, mul_zero]
  simp only [secondPreColumn, hm, mul_zero, zero_mul]

theorem weighted_secondChildKernelPair_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k₁ k₂ : O)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ lengthScale := by
  dsimp only
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let w := secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  have hcoeff :
      w * (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M) =
      supportMobius (fun i => Ideal.span {p i}) V *
        star (secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N)) *
        secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) := by
    rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hVN,
      secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hVM]
    simp only [w, secondCommonWeight, star_mul]
    ring
  change w * (_ * K (V∪N) (V∪M)) = w * (_ * lengthScale (V∪N) (V∪M))
  conv_lhs => rw [← mul_assoc w, hcoeff]
  conv_rhs => rw [← mul_assoc w, hcoeff]
  by_cases hGN : Disjoint G (V∪N)
  · by_cases hGM : Disjoint G (V∪M)
    · rw [hKL _ _ hGN hGM]
    · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₂ m c d e k₂
        (fun _ => 1) G (V∪M) (fun h => hGM h.symm)
      rw [secondMaskQuotient_spec p E G hEG] at hz
      change secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) = 0 at hz
      rw [hz]
      ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₁ m c d e k₁
      (fun _ => 1) G (V∪N) (fun h => hGN h.symm)
    rw [secondMaskQuotient_spec p E G hEG] at hz
    change secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N) = 0 at hz
    rw [hz, star_zero]
    ring

theorem weighted_secondRayChild_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (z : SecondRayIndex)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) K =
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) lengthScale := by
  dsimp only
  simp only [secondTotalWeight, mul_assoc]
  congr 1
  exact weighted_secondChildKernelPair_congr_off_common p hp hcop hg hinj hpr G E hEG F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m c d k (-k) K lengthScale hKL

end
section


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

section
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

end
section

open FirstPassCubeLabels (columnLog primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondExpansionQuotient (x : SecondExpansionData ι) : O :=
  if h : x.divisor ⊆ x.sourceCommon then
    secondMaskQuotient p x.divisor x.sourceCommon h else 0

omit [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondExpansionQuotient_of_subset (x : SecondExpansionData ι)
    (h : x.divisor ⊆ x.sourceCommon) :
    secondExpansionQuotient p x = secondMaskQuotient p x.divisor x.sourceCommon h := by
  simp [secondExpansionQuotient, h]

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondExpansionSource
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ x ∈ s,
    ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    (secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap) *
    secondChildKernelPair p hp hcop hg F x.overlap (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency)
      (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (fun A => H₁ (x.sourceCommon∪A)) (fun A => H₂ (x.sourceCommon∪A)) W Y))

end

open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le (Ψ : O →* ℂ) (m c d : O) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ≤ ‖Ψ (∏ i ∈ G, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondInputCoefficient, norm_mul, norm_pow,  mul_one]
  calc
    _ ≤ ‖Ψ (∏ i ∈ G, p i)‖ * 1 * 1 ^ 4 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg G _
    _ = _ := by ring

end SecondPassArithmetic


namespace CubicEisenstein
open CubicJacobiGlobal

lemma isUnit_quotient_span_iff (c d : O) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) d) ↔ IsCoprime c d := by
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hd
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hdiv : c ∣ d*b-1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    obtain ⟨k,hk⟩ := hdiv
    exact ⟨-k,b,by linear_combination hk⟩
  · rintro ⟨a,b,hab⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (Ideal.span {c}) b, ?_⟩
    have hc : Ideal.Quotient.mk (Ideal.span {c}) c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {c})) hab
    simpa only [map_add,map_mul,map_one,hc,mul_zero,zero_mul,zero_add,mul_comm] using h

abbrev AffineUnitResidue (c : O) :=
  {u : O ⧸ Ideal.span {c} // IsUnit (1+3*u)}

lemma affine_representative_condition (c : O) (u : AffineUnitResidue c) :
    denominatorCondition c (1+3*GaussianShiftedPartition.representative c u.1) := by
  refine ⟨(isUnit_quotient_span_iff c _).mp ?_, ⟨_,by ring⟩⟩
  simpa only [map_add,map_mul,map_one,map_ofNat,
    GaussianShiftedPartition.representative_spec] using u.2

def affineResidueMap (c : O) (u : AffineUnitResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c})
    (1+3*GaussianShiftedPartition.representative c u.1), by
    apply (denominatorCondition_congr c _
      (1+3*GaussianShiftedPartition.representative c u.1) ?_).mpr
      (affine_representative_condition c u)
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact denominatorRep_spec c _⟩

lemma affineResidueMap_bijective (c : O) : Function.Bijective (affineResidueMap c) := by
  constructor
  · intro u v huv
    have hdiv : 3*c ∣ (1+3*GaussianShiftedPartition.representative c u.1)-
        (1+3*GaussianShiftedPartition.representative c v.1) := by
      apply Ideal.mem_span_singleton.mp
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Subtype.val huv)
    obtain ⟨k,hk⟩ := hdiv
    have hk' : GaussianShiftedPartition.representative c u.1-
        GaussianShiftedPartition.representative c v.1=c*k := by
      have h3 : (3:O) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3
      linear_combination hk
    apply Subtype.ext
    rw [← GaussianShiftedPartition.representative_spec c u.1,
      ← GaussianShiftedPartition.representative_spec c v.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr ⟨k,hk'⟩)
  · intro r
    obtain ⟨u,hu⟩ := r.2.2
    have hd : denominatorRep c r.1=1+3*u := by linear_combination hu
    let q : AffineUnitResidue c := ⟨Ideal.Quotient.mk (Ideal.span {c}) u, by
      have hh := (isUnit_quotient_span_iff c _).mpr r.2.1
      simpa only [hd,map_add,map_one,map_mul,map_ofNat] using hh⟩
    refine ⟨q,Subtype.ext ?_⟩
    change Ideal.Quotient.mk (Ideal.span {3*c})
      (1+3*GaussianShiftedPartition.representative c q.1)=r.1
    rw [← denominatorRep_spec c r.1,hd]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hrep : c ∣ GaussianShiftedPartition.representative c q.1-u := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact GaussianShiftedPartition.representative_spec c q.1
    obtain ⟨k,hk⟩ := hrep
    exact ⟨k,by linear_combination 3*hk⟩

def affineResidueEquiv (c : O) : AffineUnitResidue c ≃ AdmissibleResidue c :=
  Equiv.ofBijective (affineResidueMap c) (affineResidueMap_bijective c)

def unitsSubtypeEquiv (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

def quotientProductEquiv (a b : O) (hab : IsCoprime a b) :
    (O ⧸ Ideal.span {a*b}) ≃+* (O ⧸ Ideal.span {a}) × (O ⧸ Ideal.span {b}) :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _ ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))

def affineCRTEq (a b : O) (hab : IsCoprime a b) :
    AffineUnitResidue (a*b) ≃ AffineUnitResidue a × AffineUnitResidue b :=
  ((quotientProductEquiv a b hab).toEquiv.subtypeEquiv (fun q => by
    rw [← MulEquiv.isUnit_map (quotientProductEquiv a b hab) (x := 1+3*q)]
    simp only [map_add,map_one,map_mul,map_ofNat,Prod.isUnit_iff]
    rfl)).trans Equiv.subtypeProdEquivProd

lemma affine_ramified_unit (n : ℕ) (q : O ⧸ Ideal.span {lambda^n}) : IsUnit (1+3*q) := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  have hcop : IsCoprime lambda (1+3*d) :=
    coprime_of_dvd_sub_one _ _ (by convert hlam3.mul_right d using 1 ; ring)
  have h := (isUnit_quotient_span_iff (lambda^n) (1+3*d)).mpr hcop.pow_left
  simpa only [map_add,map_one,map_mul,map_ofNat] using h

def affineRamifiedEquiv (n : ℕ) : AffineUnitResidue (lambda^n) ≃ (O ⧸ Ideal.span {lambda^n}) :=
  Equiv.subtypeUnivEquiv (affine_ramified_unit n)

def affineUnramifiedEquiv (m : O) (hm : IsCoprime m (3:O)) :
    AffineUnitResidue m ≃ (O ⧸ Ideal.span {m})ˣ := by
  let h3 : IsUnit (3 : O ⧸ Ideal.span {m}) := by
    simpa only [map_ofNat] using (isUnit_quotient_span_iff m 3).mpr hm
  let e : (O ⧸ Ideal.span {m}) ≃ (O ⧸ Ideal.span {m}) :=
    h3.unit.mulLeft.trans (Equiv.addLeft 1)
  refine (e.subtypeEquiv (fun q => ?_)).trans (unitsSubtypeEquiv _).symm
  change IsUnit (1+3*q) ↔ IsUnit (1+(h3.unit : O ⧸ Ideal.span {m})*q)
  rw [h3.unit_spec]

def idealTotient (I : Ideal O) : ℕ := Nat.card (O ⧸ I)ˣ

lemma card_admissible_ramified_product (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) (hlamm : IsCoprime lambda m) :
    Nat.card (AdmissibleResidue (lambda^n*m)) =
      Nat.card (O ⧸ Ideal.span {lambda^n}) * idealTotient (Ideal.span {m}) := by
  calc
    _ = Nat.card (AffineUnitResidue (lambda^n*m)) :=
      Nat.card_congr (affineResidueEquiv _).symm
    _ = Nat.card (AffineUnitResidue (lambda^n) × AffineUnitResidue m) :=
      Nat.card_congr (affineCRTEq _ _ hlamm.pow_left)
    _ = Nat.card ((O ⧸ Ideal.span {lambda^n}) × (O ⧸ Ideal.span {m})ˣ) :=
      Nat.card_congr (Equiv.prodCongr (affineRamifiedEquiv n) (affineUnramifiedEquiv m hm))
    _ = _ := Nat.card_prod _ _

lemma absNorm_span_lambda : Ideal.absNorm (Ideal.span {lambda})=3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclotomicExtension {3^(0+1)} ℚ ActualEisensteinCubic.K := by
    simpa using (inferInstance : IsCyclotomicExtension {3} ℚ ActualEisensteinCubic.K)
  exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 3 0
    (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K)

lemma card_quotient_lambda_pow (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {lambda^n})=3^n := by
  change Ideal.absNorm (Ideal.span {lambda^n})=3^n
  rw [← Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

theorem card_admissible_lambda_pow_mul (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) :
    Nat.card (AdmissibleResidue (lambda^n*m)) = 3^n * idealTotient (Ideal.span {m}) := by
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  rw [card_admissible_ramified_product n m hm
    (hm.symm.of_isCoprime_of_dvd_left hlam3),card_quotient_lambda_pow]
