module

public import CCDN.ClassGroup.TwoTorsion
public import CCDN.Height.Box
public import CCDN.Noether.BivariateTotalDegree
public import Mathlib.LinearAlgebra.Charpoly.Basic
import CCDN.Plane.GridHeight
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField nonZeroDivisors Real
open NumberField NumberField.InfinitePlace MeasureTheory MeasureTheory.Measure
open Polynomial FractionalIdeal NNReal

section Discriminant
variable (K : Type*) [Field K] [NumberField K]

lemma numberField_discriminant_natAbs_cast :
    ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
    congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (discr K))

lemma numberField_discriminant_natAbs_pos : 0 < (discr K).natAbs :=
  Int.natAbs_pos.mpr (discr_ne_zero K)

lemma one_le_abs_discr : 1 ≤ |(discr K : ℝ)| :=
  mod_cast Int.one_le_abs (discr_ne_zero K)

lemma three_le_abs_discr (hn : 2 ≤ Module.finrank ℚ K) : 3 ≤ |(discr K : ℝ)| := by
  have := abs_discr_gt_two (K := K) (by omega : 1 < Module.finrank ℚ K)
  exact_mod_cast (by omega : (3 : ℤ) ≤ |discr K|)

lemma one_le_log_abs_discr (hn : 2 ≤ Module.finrank ℚ K) :
    1 ≤ Real.log |(discr K : ℝ)| := by
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.le.trans (three_le_abs_discr K hn))

end Discriminant

private lemma generator_absolute_norm_of_ideal_square (K : Type*) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) {β : 𝓞 K} (hI : I ^ 2 = Ideal.span {β}) :
    (Algebra.norm ℤ β).natAbs = Ideal.absNorm I ^ 2 := by
  rw [← Ideal.absNorm_span_singleton, ← hI, map_pow]

private theorem rescale_integral_ideal_square {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (Ideal R)⁰) {α : R} (hα : α ≠ 0) (hIα : (I : Ideal R) ^ 2 = Ideal.span {α})
    {κ : K} (hκ : κ ≠ 0) (hκI : κ ∈ (I : FractionalIdeal R⁰ K)⁻¹) :
    ∃ J : (Ideal R)⁰, ∃ β : R,
      ClassGroup.mk0 J = ClassGroup.mk0 I ∧ β ≠ 0 ∧
      algebraMap R K β = algebraMap R K α * κ ^ 2 ∧
      (J : Ideal R) ^ 2 = Ideal.span {β} := by
  let F : FractionalIdeal R⁰ K := spanSingleton R⁰ κ * (I : FractionalIdeal R⁰ K)
  have hI0 : (I : FractionalIdeal R⁰ K) ≠ 0 := coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I)
  have hF0 : F ≠ 0 := mul_ne_zero (spanSingleton_ne_zero_iff.mpr hκ) hI0
  have hFle : F ≤ 1 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_singleton_mul.mp hx
    exact (mem_inv_iff hI0).mp hκI y hy
  obtain ⟨J₀, hJ₀⟩ := le_one_iff_exists_coeIdeal.mp hFle
  have hJ0 : J₀ ≠ 0 := fun h => hF0 (by simp [← hJ₀, h])
  let J : (Ideal R)⁰ := ⟨J₀, mem_nonZeroDivisors_of_ne_zero hJ0⟩
  have hJ : (J : FractionalIdeal R⁰ K) = F := hJ₀
  have hsq : (J : FractionalIdeal R⁰ K) ^ 2 = spanSingleton R⁰ (algebraMap R K α * κ ^ 2) := by
    rw [hJ]; dsimp only [F]
    rw [mul_pow, ← coeIdeal_pow, hIα, coeIdeal_span_singleton, ← map_pow, ← map_mul, mul_comm]
  have hβmem : algebraMap R K α * κ ^ 2 ∈ (1 : FractionalIdeal R⁰ K) := by
    have hsle : (J : FractionalIdeal R⁰ K) ^ 2 ≤ 1 := by
      rw [← coeIdeal_pow]; exact coeIdeal_le_one
    rw [hsq] at hsle; exact spanSingleton_le_iff_mem.mp hsle
  obtain ⟨β, hβ⟩ := (mem_one_iff R⁰).mp hβmem
  have hαK : algebraMap R K α ≠ 0 := fun hz => hα ((IsFractionRing.injective R K) (by simpa using hz))
  have hβ0 : β ≠ 0 := fun hb =>
    mul_ne_zero hαK (pow_ne_zero 2 hκ) (by rw [← hβ, hb, map_zero])
  refine ⟨J, β, ((ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mpr ⟨κ, hκ, hJ.symm⟩).symm,
    hβ0, hβ, coeIdeal_injective (K := K) ?_⟩
  change (((J : Ideal R) ^ 2 : Ideal R) : FractionalIdeal R⁰ K) =
    ((Ideal.span {β} : Ideal R) : FractionalIdeal R⁰ K)
  rw [coeIdeal_pow, coeIdeal_span_singleton, hβ]; exact hsq

def boundedArchimedeanIntegers (K : Type*) [Field K] [NumberField K] (B : ℝ) : Set (𝓞 K) :=
  {α | ∀ w : InfinitePlace K, w (α : K) ≤ B}

lemma boundedArchimedeanIntegers_finite (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    (boundedArchimedeanIntegers K B).Finite :=
  Set.Finite.of_injOn (f := fun β : 𝓞 K => (β : K))
    (t := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B})
    (fun β hβ => ⟨β.isIntegral_coe, fun φ => hβ (InfinitePlace.mk φ)⟩)
    RingOfIntegers.coe_injective.injOn (Embeddings.finite_of_norm_le K ℂ B)

def boundedSquareNormIntegers (K : Type*) [Field K] [NumberField K] (B : ℝ) : Set (𝓞 K) :=
  {β | β ≠ 0 ∧ (∀ w : InfinitePlace K, w (β : K) ≤ B) ∧
    ∃ m : ℕ, (Algebra.norm ℤ β).natAbs = m ^ 2}

lemma boundedSquareNormIntegers_finite (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    (boundedSquareNormIntegers K B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset fun _ h => h.2.1

theorem classGroupTwoTorsionCard_le_boundedSquareNormIntegers
    (K : Type*) [Field K] [NumberField K] :
    classGroupTwoTorsionCard K ≤
      (boundedSquareNormIntegers K
        (9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard := by
  classical
  have hD : 0 < |(discr K : ℝ)| := zero_lt_one.trans_le (one_le_abs_discr K)
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := mod_cast hn.ne'
  let T : ℝ≥0 := ⟨3 * |(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ))), by positivity⟩
  have hTn : (T : ℝ) ^ Module.finrank ℚ K = 3 ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)| := by
    change (3 * |(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ)))) ^ Module.finrank ℚ K = _
    rw [mul_pow, ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul hD.le,
      show 1 / (2 * (Module.finrank ℚ K : ℝ)) * (Module.finrank ℚ K : ℝ) = 1 / 2 by field_simp,
      ← Real.sqrt_eq_rpow]
  have hT2 : (T : ℝ) ^ 2 = 9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
    change (3 * |(discr K : ℝ)| ^ (1 / (2 * (Module.finrank ℚ K : ℝ)))) ^ 2 = _
    rw [mul_pow, ← Real.rpow_natCast (_ ^ _) 2, ← Real.rpow_mul hD.le]
    norm_num only [Nat.cast_ofNat]
    rw [show 1 / (2 * (Module.finrank ℚ K : ℝ)) * (2 : ℝ) =
      1 / (Module.finrank ℚ K : ℝ) by ring]
  have hT : (2 : ℝ) ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)| <
      (T : ℝ) ^ Module.finrank ℚ K := by
    rw [hTn]
    exact mul_lt_mul_of_pos_right
      (pow_lt_pow_left₀ (by norm_num : (2 : ℝ) < 3) (by norm_num) hn.ne') (Real.sqrt_pos.mpr hD)
  have hgen (c : classGroupTwoTorsion K) :
      ∃ J : (Ideal (𝓞 K))⁰, ∃ β : 𝓞 K,
        ClassGroup.mk0 J = c ∧ β ≠ 0 ∧ (J : Ideal (𝓞 K)) ^ 2 = Ideal.span {β} ∧
        ∀ w : InfinitePlace K, w (β : K) ≤ (T : ℝ) ^ 2 := by
    obtain ⟨I, hIc⟩ := ClassGroup.mk0_surjective c.val
    have hIsq : (ClassGroup.mk0 I) ^ 2 = 1 := hIc.symm ▸ c.property
    obtain ⟨α, hα, hIα⟩ : ∃ α : 𝓞 K, α ≠ 0 ∧ (I : Ideal (𝓞 K)) ^ 2 = Ideal.span {α} := by
      simpa only [pow_two] using ClassGroup.mk0_eq_mk0_inv_iff.mp
        (eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hIsq))
    let f : InfinitePlace K → ℝ≥0 := fun w => T / NNReal.sqrt (Real.toNNReal (w (α : K)))
    have hN : 0 < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) :=
      mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
    have hprod : (∏ w : InfinitePlace K, f w ^ mult w) =
        T ^ Module.finrank ℚ K / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0) := by
      simp_rw [f, div_pow]
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq]
      congr 1
      have hp : (∏ w : InfinitePlace K, Real.toNNReal (w (α : K)) ^ mult w) =
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0) ^ 2 := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_prod, NNReal.coe_pow, Real.coe_toNNReal _ (apply_nonneg _ _),
          NNReal.coe_natCast, prod_eq_abs_norm, ← Algebra.coe_norm_int]
        norm_cast
        rw [← Int.natCast_natAbs, generator_absolute_norm_of_ideal_square K _ hIα, Nat.cast_pow]
      have hsqh : (∏ w : InfinitePlace K, (NNReal.sqrtHom (Real.toNNReal (w (α : K)))) ^ mult w) =
          NNReal.sqrtHom (∏ w : InfinitePlace K, Real.toNNReal (w (α : K)) ^ mult w) := by
        simp only [map_prod, map_pow]
      exact hsqh.trans (by change NNReal.sqrt _ = _; rw [hp, NNReal.sqrt_sq])
    have hvol : volume (mixedEmbedding.convexBodyLT K f) =
        ((mixedEmbedding.convexBodyLTFactor K *
          (T ^ Module.finrank ℚ K / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ≥0)) : ℝ≥0) : ENNReal) := by
      rw [mixedEmbedding.convexBodyLT_volume, ← ENNReal.coe_mul, hprod]
    have hmink : (mixedEmbedding.minkowskiBound K (FractionalIdeal.mk0 K I)⁻¹).toReal =
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)⁻¹ *
          (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| *
            2 ^ Module.finrank ℚ K := by
      simp only [mixedEmbedding.minkowskiBound,
        mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
        mixedEmbedding.volume_fundamentalDomain_latticeBasis,
        ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]
      rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
      simp only [Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coe_mk0,
        FractionalIdeal.coeIdeal_absNorm, Rat.cast_inv, Rat.cast_natCast,
        Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]; ring
    have hm : mixedEmbedding.minkowskiBound K (FractionalIdeal.mk0 K I)⁻¹ <
        volume (mixedEmbedding.convexBodyLT K f) := by
      apply (ENNReal.toReal_lt_toReal
        (ne_of_lt (mixedEmbedding.minkowskiBound_lt_top K _)) (by rw [hvol]; finiteness)).mp
      rw [hmink, hvol, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
        NNReal.coe_natCast]
      have hc : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hf : (1 : ℝ) ≤ mixedEmbedding.convexBodyLTFactor K :=
        NNReal.coe_le_coe.mpr (mixedEmbedding.one_le_convexBodyLTFactor K)
      calc _ ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)⁻¹ *
            Real.sqrt |(discr K : ℝ)| * 2 ^ Module.finrank ℚ K := by
            gcongr; simpa using mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hN.le)
        _ = ((2 : ℝ) ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)|) /
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by ring
        _ < (T : ℝ) ^ Module.finrank ℚ K / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) :=
            div_lt_div_of_pos_right hT hN
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hf
    obtain ⟨κ, hκI, hκ, hκw⟩ :=
      mixedEmbedding.exists_ne_zero_mem_ideal_lt K (FractionalIdeal.mk0 K I)⁻¹ hm
    obtain ⟨J, β, hJ, hβ, heq, hsq⟩ := rescale_integral_ideal_square (K := K) I hα hIα hκ hκI
    refine ⟨J, β, hJ.trans hIc, hβ, hsq, fun w => ?_⟩
    have hαw : 0 < w (α : K) := InfinitePlace.pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr hα)
    have hk : w κ < (T : ℝ) / Real.sqrt (w (α : K)) := by
      simpa only [f, NNReal.coe_div, Real.coe_sqrt, Real.coe_toNNReal _ (apply_nonneg _ _)]
        using hκw w
    change (β : K) = (α : K) * κ ^ 2 at heq
    rw [heq, map_mul, map_pow]
    exact (mul_lt_mul_of_pos_left
      (pow_lt_pow_left₀ hk (apply_nonneg _ _) (by decide : (2 : ℕ) ≠ 0)) hαw).le.trans_eq
      (by rw [div_pow, Real.sq_sqrt hαw.le]; field_simp)
  choose J β hc hβ hsq hw using hgen
  have hinj : Function.Injective β := fun c e hce => Subtype.ext <| by
    rw [← hc c, ← hc e]; congr 1; apply Subtype.ext
    have hp : (J c : Ideal (𝓞 K)) ^ 2 = (J e : Ideal (𝓞 K)) ^ 2 := by rw [hsq c, hsq e, hce]
    exact le_antisymm
      (Ideal.le_of_dvd ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 2) (by norm_num)).mp (hp ▸ dvd_rfl)))
      (Ideal.le_of_dvd ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 2) (by norm_num)).mp (hp.symm ▸ dvd_rfl)))
  rw [classGroupTwoTorsionCard, ← Set.ncard_range_of_injective hinj]
  refine Set.ncard_le_ncard ?_ (boundedSquareNormIntegers_finite K _)
  rintro _ ⟨c, rfl⟩
  exact ⟨hβ c, fun w => (hw c w).trans_eq hT2,
    Ideal.absNorm (J c : Ideal (𝓞 K)), generator_absolute_norm_of_ideal_square K _ (hsq c)⟩

def integerNormPolynomial (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) : ℤ[X] :=
  (Algebra.lmul ℤ (𝓞 K) β).charpoly

lemma integerNormPolynomial_monic (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) :
    (integerNormPolynomial K β).Monic :=
  LinearMap.charpoly_monic _

lemma integerNormPolynomial_natDegree (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) :
    (integerNormPolynomial K β).natDegree = Module.finrank ℚ K := by
  rw [integerNormPolynomial, LinearMap.charpoly_natDegree, RingOfIntegers.rank]

lemma integerNormPolynomial_eval (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) (x : ℤ) :
    (integerNormPolynomial K β).eval x = Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [integerNormPolynomial, LinearMap.eval_charpoly, Algebra.norm_apply,
    map_sub (Algebra.lmul ℤ (𝓞 K)), Algebra.lmul_algebraMap]; rfl

def signedNormCurvePolynomial (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) (ε : ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  (bivariatePolynomialEquiv ℤ).symm (X ^ 2 - C (C ε * integerNormPolynomial K β))

def squareNormTranslateFiber (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) (B : ℝ) : Set (𝓞 K) :=
  {α | α ∈ boundedSquareNormIntegers K B ∧ ∃ x : ℤ, α = algebraMap ℤ (𝓞 K) x - β}

lemma squareNormTranslateFiber_finite (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) (B : ℝ) :
    (squareNormTranslateFiber K β B).Finite :=
  (boundedSquareNormIntegers_finite K B).subset fun _ h => h.1

def signedNormCurveLocus (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) (ε : ℤ) :
    Set (RatPoint 2) :=
  zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) (signedNormCurvePolynomial K β ε))

theorem squareNormTranslateFiber_count_le (K : Type*) [Field K] [NumberField K]
    (β : 𝓞 K) {B : ℝ} (hβ : ∀ w : InfinitePlace K, w (β : K) ≤ B) :
    (squareNormTranslateFiber K β B).ncard ≤
      count (signedNormCurveLocus K β 1) (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
      count (signedNormCurveLocus K β (-1)) (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) := by
  classical
  let S := squareNormTranslateFiber K β B
  let H := max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))
  let Z := signedNormCurveLocus K β 1 ∪ signedNormCurveLocus K β (-1)
  let P := integralPoints Z H
  choose x hx using fun α : S => α.property.2
  choose m hm using fun α : S => α.property.1.2.2
  have hpoint (α : S) : ![(m α : ℤ), x α] ∈ P := by
    refine mem_integralPoints.mpr ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · have hsq : (m α : ℝ) ^ 2 ≤ B ^ Module.finrank ℚ K := by
          rw [← Nat.cast_pow, ← hm α]
          have he : (∏ w : InfinitePlace K, w (α.val : K) ^ mult w) =
              ((Algebra.norm ℤ α.val).natAbs : ℝ) := by
            rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
            norm_cast
            exact (Nat.cast_natAbs (Algebra.norm ℤ α.val)).symm
          rw [← he, ← sum_mult_eq (K := K), ← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_le_prod₀ (fun w _ => by positivity)
            fun w _ => pow_le_pow_left₀ (apply_nonneg _ _) (α.property.1.2.1 w) _
        change |((m α : ℤ) : ℝ)| ≤ H
        simp only [Int.cast_natCast]; rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact (Real.le_sqrt_of_sq_le hsq).trans (le_max_right (2 * B) _)
      · let w : InfinitePlace K := Classical.arbitrary _
        have hxK : (x α : K) = (α.val : K) + (β : K) := by
          have hh := congrArg (fun z : 𝓞 K => (z : K)) (hx α)
          simp only [map_sub, RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply] at hh
          change (α.val : K) = (x α : K) - (β : K) at hh
          exact (eq_sub_iff_add_eq.mp hh).symm
        calc |(x α : ℝ)| = w (x α : K) := by rw [w.map_intCast, Int.norm_eq_abs]
          _ = w ((α.val : K) + (β : K)) := congrArg w hxK
          _ ≤ w (α.val : K) + w (β : K) := w.val.add_le _ _
          _ ≤ 2 * B := by linarith [α.property.1.2.1 w, hβ w]
          _ ≤ H := le_max_left _ _
    · have ha : |Algebra.norm ℤ (algebraMap ℤ (𝓞 K) (x α) - β)| = (m α : ℤ) ^ 2 := by
        rw [← hx α]
        simpa only [Int.natCast_natAbs, Nat.cast_pow] using congrArg (Nat.cast : ℕ → ℤ) (hm α)
      have heval (ε : ℤ) : MvPolynomial.eval ![(m α : ℤ), x α]
          (signedNormCurvePolynomial K β ε) =
          (m α : ℤ) ^ 2 - ε * Algebra.norm ℤ (algebraMap ℤ (𝓞 K) (x α) - β) := by
        rw [← bivariatePolynomialEquiv_eval _ (m α : ℤ) (x α)]
        simp [signedNormCurvePolynomial, integerNormPolynomial_eval]
      rcases (_root_.abs_eq (by positivity)).mp ha with hp | hn
      · left
        have hz : MvPolynomial.eval ![(m α : ℤ), x α] (signedNormCurvePolynomial K β 1) = 0 := by
          rw [heval, hp]; ring
        have hc := congrArg (Int.castRingHom ℚ) hz
        rw [MvPolynomial.map_eval, map_zero] at hc; exact hc
      · right
        have hz : MvPolynomial.eval ![(m α : ℤ), x α] (signedNormCurvePolynomial K β (-1)) = 0 := by
          rw [heval, hn]; ring
        have hc := congrArg (Int.castRingHom ℚ) hz
        rw [MvPolynomial.map_eval, map_zero] at hc; exact hc
  let ι : S → P := fun α => ⟨![(m α : ℤ), x α], hpoint α⟩
  have hi : Function.Injective ι := fun α γ he => by
    have hh : x α = x γ := congrArg (fun p : P => p.val 1) he
    exact Subtype.ext (by rw [hx α, hx γ, hh])
  have hcard : S.ncard ≤ count Z H := by
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe, count, P] using
      Nat.card_le_card_of_injective ι hi
  exact hcard.trans (count_union_le _ _ _)

abbrev IntegerTranslationQuotient (K : Type*) [Field K] [NumberField K] :=
  (𝓞 K) ⧸ AddSubgroup.zmultiples (1 : 𝓞 K)

def boundedSquareNormTranslationClasses (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    Finset (IntegerTranslationQuotient K) := by
  classical
  exact (boundedSquareNormIntegers_finite K B).toFinset.image
    fun α : 𝓞 K => (α : IntegerTranslationQuotient K)

theorem exists_norm_translate_cover (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    ∃ β : boundedSquareNormTranslationClasses K B → 𝓞 K,
      Function.Injective β ∧
      (∀ q, ∀ w : InfinitePlace K, w (β q : K) ≤ B) ∧
      ∀ α ∈ boundedSquareNormIntegers K B,
        ∃ q, α ∈ squareNormTranslateFiber K (β q) B := by
  classical
  let Q := boundedSquareNormTranslationClasses K B
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ boundedSquareNormIntegers K B ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  refine ⟨fun q => -r q, fun q t h => Subtype.ext (by rw [← hq q, ← hq t, neg_injective h]),
    fun q w => ?_, fun α hα => ?_⟩
  · change w.val (-((r q : 𝓞 K) : K)) ≤ B; rw [AbsoluteValue.map_neg]; exact (hr q).2.1 w
  · let q : Q := ⟨(α : IntegerTranslationQuotient K), Finset.mem_image.mpr
      ⟨α, (boundedSquareNormIntegers_finite K B).mem_toFinset.mpr hα, rfl⟩⟩
    obtain ⟨x, hx⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (QuotientAddGroup.eq_iff_sub_mem.mp (hq q).symm)
    have hx' : (algebraMap ℤ (𝓞 K) x) = α - r q := by simpa using hx
    refine ⟨q, hα, x, ?_⟩
    change α = algebraMap ℤ (𝓞 K) x - -r q; rw [hx']; abel

theorem boundedSquareNormTranslationClasses_packing
    (K : Type*) [Field K] [NumberField K] (B R : ℝ) :
    (boundedSquareNormTranslationClasses K B).card * (2 * ⌊R⌋ + 1).toNat ≤
      (boundedArchimedeanIntegers K (B + R)).ncard := by
  classical
  let Q := boundedSquareNormTranslationClasses K B
  let Z := Finset.Icc (-⌊R⌋) ⌊R⌋
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ boundedSquareNormIntegers K B ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  have hzbound (z : Z) : |(z.val : ℝ)| ≤ R := by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp z.property
    refine abs_le.mpr ⟨?_, Int.le_floor.mp hu⟩
    have hh := Int.le_floor.mp (by omega : -z.val ≤ ⌊R⌋)
    push_cast at hh; linarith
  let a : Q × Z → 𝓞 K := fun t => r t.1 + (t.2.val : 𝓞 K)
  have ha (t : Q × Z) : a t ∈ boundedArchimedeanIntegers K (B + R) := fun w => by
    change w.val (((r t.1 : 𝓞 K) : K) + (t.2.val : K)) ≤ _
    calc _ ≤ w ((r t.1 : 𝓞 K) : K) + w (t.2.val : K) := w.val.add_le _ _
      _ = w ((r t.1 : 𝓞 K) : K) + |(t.2.val : ℝ)| := by rw [w.map_intCast, Int.norm_eq_abs]
      _ ≤ _ := add_le_add ((hr t.1).2.1 w) (hzbound t.2)
  have haQ (t : Q × Z) : (a t : IntegerTranslationQuotient K) = t.1.val := by
    have hz : ((t.2.val : 𝓞 K) : IntegerTranslationQuotient K) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.intCast_mem_zmultiples_one t.2.val)
    change QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : 𝓞 K)) (r t.1 + (t.2.val : 𝓞 K)) = _
    rw [map_add]
    change (r t.1 : IntegerTranslationQuotient K) + ((t.2.val : 𝓞 K) : IntegerTranslationQuotient K) = _
    rw [hz, add_zero, hq]
  have hi : Function.Injective a := by
    rintro ⟨q, z⟩ ⟨q', z'⟩ he
    have hqeq : q = q' := Subtype.ext (by rw [← haQ (q, z), ← haQ (q', z'), he])
    subst q'
    exact Prod.ext rfl (Subtype.ext (Int.cast_injective (add_left_cancel he : (z.val : 𝓞 K) = (z'.val : 𝓞 K))))
  let := (boundedArchimedeanIntegers_finite K (B + R)).fintype
  have hcard := Nat.card_le_card_of_injective
    (fun t : Q × Z => (⟨a t, ha t⟩ : boundedArchimedeanIntegers K (B + R)))
    (fun s t h => hi (congrArg Subtype.val h))
  have hZ : Z.card = (2 * ⌊R⌋ + 1).toNat := by simp only [Z, Int.card_Icc]; congr 1; omega
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    Set.fintypeCard_eq_ncard, hZ] using hcard

end
end CCDN
