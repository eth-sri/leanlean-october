module

public import OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage

@[expose] public section

namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
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
open scoped Classical

open scoped Classical

section
open IdealMobiusDivisorSum hiding O
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

abbrev PrimeIdeal := {P : Ideal ActualEisensteinCubic.O // Prime P}

def primeProduct (s : Finset PrimeIdeal) : Ideal ActualEisensteinCubic.O := ∏ P ∈ s, P.val

def primeSet (I : Ideal ActualEisensteinCubic.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)

@[simp] theorem mem_primeSet (I : Ideal ActualEisensteinCubic.O) (P : PrimeIdeal) :
    P ∈ primeSet I ↔ P.val ∈ primeSupport I := by
  simp only [primeSet, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · grind
  · intro h
    exact ⟨⟨P.val,h⟩,rfl⟩

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      simp_all)
  simpa

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  grind

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    simp_all

def mobiusPrimeCoeff (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open Filter

lemma prime_norm_two_le (P : PrimeIdeal) : 2 ≤ Ideal.absNorm P.val := by
  have h0 : Ideal.absNorm P.val ≠ 0 := fun h => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.val ≠ 1 := by
    intro h
    apply P.property.not_isUnit
    rw [Ideal.absNorm_eq_one_iff.mp h]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal ActualEisensteinCubic.O) from isUnit_one)
  omega

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  positivity

def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) :=
  Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he := (sub_eq_zero.mp h).symm
  simp_all

lemma prime_norm_series_summable (σ : ℝ) (hσ : 0<σ) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-(1+σ))) := by
  have ht := (CubicEisenstein.fullIdealWeight_summable_norm (1+(σ:ℂ)) (by simp_all)).comp_injective
    (i := fun P : PrimeIdeal => P.val) Subtype.val_injective
  apply ht.congr
  intro P
  simp only [Function.comp_def,CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
  simpa only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-(1+(σ:ℂ))))

end

section
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal ActualEisensteinCubic.O) (f : Ideal ActualEisensteinCubic.O→M) :
    (∏P∈primeSet I,f P.val)=∏P∈primeSupport I,f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    simp_all

end


open scoped Classical
open ShortDraftHeckeBridge hiding O

lemma normFiber_tsum (a : Ideal ActualEisensteinCubic.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := ActualEisensteinCubic.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈FiniteSFactor.fiber n,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,FiniteSFactor.mem_fiber.mp hI⟩ : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}))
  · simp
  · simp
  · intro I hI
    exact ⟨I.val,FiniteSFactor.mem_fiber.mpr I.property,rfl⟩
  simp

lemma idealDirichlet_fiber (a : Ideal ActualEisensteinCubic.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by grind)
      rw [CubicEisenstein.fullIdealWeight,ite_eq_right hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

lemma idealDirichlet_summable (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1) (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal ActualEisensteinCubic.O => a I*CubicEisenstein.fullIdealWeight s I) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (by grind)
    (fun I => ?_) (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem idealDirichlet_eq_LSeries (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1)
    (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,a I*CubicEisenstein.fullIdealWeight s I)=LSeries (normFiberCoeff a) s := by
  have hh := (idealDirichlet_summable a ha s hs).hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},
    a I.val*CubicEisenstein.fullIdealWeight s I.val) _ at hh
  simp_rw [idealDirichlet_fiber] at hh
  exact hh.tsum_eq.symm

end SmoothMobiusCorrection

end

end OAI
