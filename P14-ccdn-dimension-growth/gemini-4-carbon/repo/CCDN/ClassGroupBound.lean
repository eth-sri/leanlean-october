module

public import CCDN.ClassGroup.TwoTorsion
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.NumberFieldLatticeBox
import CCDN.ClassGroup.NumberFieldShortBasis
import CCDN.ClassGroup.QuadraticClassGroupDescent
import CCDN.ClassGroup.SmallSubfieldIntegerCount
import CCDN.Noether.ShearNormalization
import CCDN.Plane.AffinePlaneBadPrimeCount
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Polynomial.IsIntegral

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped NumberField IntermediateField
universe u

private theorem classGroup_discriminant_bound_of_balanced_radius
    {D A N : ℝ} (hD : 0 < D) {n : ℕ} (hn : 0 < n)
    (h : N * Real.sqrt D ≤
      A * ((9 * D ^ (1 / (n : ℝ))) ^ (n - 1) * Real.sqrt (9 * D ^ (1 / (n : ℝ))))) :
    N ≤ (A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
  have hn0 : (n : ℝ) ≠ 0 := mod_cast hn.ne'
  have hsqrt : Real.sqrt (9 * D ^ (1 / (n : ℝ))) = 3 * D ^ (1 / (2 * (n : ℝ))) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num : (9 : ℝ) = 3 ^ 2),
      Real.sqrt_eq_rpow, ← Real.rpow_mul hD.le]
    congr 2; field_simp
  have hp : (D ^ (1 / (n : ℝ))) ^ (n - 1) = D ^ (((n - 1 : ℕ) : ℝ) / n) := by
    rw [← Real.rpow_mul_natCast hD.le]; congr 1; ring
  have hexp : ((n - 1 : ℕ) : ℝ) / n + 1 / (2 * (n : ℝ)) =
      (1 / 2 - 1 / (2 * (n : ℝ))) + 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]; field_simp; ring
  have hid : (9 * D ^ (1 / (n : ℝ))) ^ (n - 1) * Real.sqrt (9 * D ^ (1 / (n : ℝ))) =
      (3 * (9 : ℝ) ^ (n - 1)) * D ^ (1 / 2 - 1 / (2 * (n : ℝ))) * Real.sqrt D := by
    rw [mul_pow, hp, hsqrt, Real.sqrt_eq_rpow]
    calc _ = (3 * (9 : ℝ) ^ (n - 1)) *
            (D ^ (((n - 1 : ℕ) : ℝ) / n) * D ^ (1 / (2 * (n : ℝ)))) := by ring
      _ = (3 * (9 : ℝ) ^ (n - 1)) *
            (D ^ (1 / 2 - 1 / (2 * (n : ℝ))) * D ^ (1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hD, hexp, Real.rpow_add hD]
      _ = _ := by ring
  rw [hid] at h
  exact (mul_le_mul_iff_left₀ (Real.sqrt_pos.mpr hD)).mp (by nlinarith only [h])

private lemma normCurveBoxHeight_root_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    (max (2 * B) (Real.sqrt (B ^ n))) ^ (1 / (n : ℝ)) ≤ 2 * Real.sqrt B := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hs : 1 ≤ Real.sqrt B := by simpa using Real.sqrt_le_sqrt hB
  have hsq : (2 * Real.sqrt B) ^ 2 = 4 * B := by rw [mul_pow, Real.sq_sqrt hB0]; ring
  have hpow : (2 * Real.sqrt B) ^ 2 ≤ (2 * Real.sqrt B) ^ n :=
    pow_le_pow_right₀ (by linarith) hn
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * Real.sqrt B) ^ n := by
    refine max_le (by rw [hsq] at hpow; linarith)
      ((Real.sqrt_le_left (pow_nonneg (by positivity) _)).mpr ?_)
    calc B ^ n ≤ ((2 * Real.sqrt B) ^ 2) ^ n := pow_le_pow_left₀ hB0 (by rw [hsq]; linarith) n
      _ = ((2 * Real.sqrt B) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm n 2]
  have hh := Real.rpow_le_rpow (by positivity) hH (by positivity : 0 ≤ 1 / (n : ℝ))
  rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)] at hh
  simpa only [one_div] using hh

private lemma normCurveBoxHeight_log_le {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 1 ≤ B) :
    Real.log (max (2 * B) (Real.sqrt (B ^ n))) + n ≤ 2 * (n : ℝ) * (Real.log B + 1) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hpow : 1 ≤ B ^ n := one_le_pow₀ hB
  have hH : max (2 * B) (Real.sqrt (B ^ n)) ≤ (2 * B) ^ n :=
    max_le (by simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 2 * B) (by omega : 1 ≤ n))
      (((Real.sqrt_le_left (by positivity)).mpr (by nlinarith)).trans
        (pow_le_pow_left₀ hB0.le (by linarith) n))
  have hlog := Real.log_le_log (lt_of_lt_of_le (by positivity) (le_max_left _ _)) hH
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB0.ne'] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have := Nat.cast_nonneg (α := ℝ) n
  have := Real.log_nonneg hB
  nlinarith

private theorem boundedSquareNormTranslationClasses_uniform_count
    (K : Type*) [Field K] [NumberField K] (hn : 2 ≤ Module.finrank ℚ K)
    {B : ℝ} (hB1 : 1 ≤ B) (hB : |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) ((Module.finrank ℚ K : ℝ) ^ 3) *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  obtain ⟨b, hb, hnorm⟩ := exists_numberField_short_basis K hn
  exact boundedSquareNormTranslationClasses_count_of_relative_short_basis K b hb hB1
    (by positivity) fun i => (hnorm i).trans (mul_le_mul_of_nonneg_left hB (by positivity))

section NormCurvePoly
open Polynomial IntermediateField

private lemma double_cover_bivariateTotalDegree {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (hp : 2 ≤ p.natDegree) :
    bivariateTotalDegree (X ^ 2 - C p : R[X][X]) = p.natDegree := by
  refine le_antisymm ?_ ?_
  · rw [bivariateTotalDegree_le_iff]; intro i j hij
    by_cases hi : i = 2
    · subst i
      have hc : ((X ^ 2 - C p : R[X][X]).coeff 2).coeff j = (1 : R[X]).coeff j := by simp
      rw [hc] at hij
      have hj : j = 0 := by by_contra h; simp [coeff_one, h] at hij
      omega
    · by_cases hi0 : i = 0
      · subst i; exact le_natDegree_of_ne_zero (by simpa using hij)
      · simp [coeff_sub, coeff_X_pow, coeff_C, hi, hi0] at hij
  · have hp0 : p ≠ 0 := fun h => by simp [h] at hp
    simpa using bivariateTotalDegree_coeff_le (X ^ 2 - C p : R[X][X]) 0 p.natDegree
      (by simpa using neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp0))

private lemma signedNormCurvePolynomial_bivariate_map
    (K E : Type*) [Field K] [NumberField K] [Field E] (β : 𝓞 K) (ε : ℤ) :
    bivariatePolynomialEquiv E
      (MvPolynomial.map (Int.castRingHom E) (signedNormCurvePolynomial K β ε)) =
      X ^ 2 - C (C (ε : E) * (integerNormPolynomial K β).map (Int.castRingHom E)) := by
  rw [← bivariatePolynomialEquiv_map]
  simp only [signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
  change Polynomial.map (Polynomial.mapRingHom (Int.castRingHom E))
    (X ^ 2 - C (C ε * integerNormPolynomial K β)) = _
  simp

private theorem signedNormCurvePolynomial_totalDegree
    (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hn : 2 ≤ Module.finrank ℚ K) :
    (signedNormCurvePolynomial K β ε).totalDegree = Module.finrank ℚ K := by
  have hd : (C ε * integerNormPolynomial K β).natDegree = Module.finrank ℚ K := by
    rw [natDegree_C_mul hε, integerNormPolynomial_natDegree]
  change bivariateTotalDegree (X ^ 2 - C (C ε * integerNormPolynomial K β)) = _
  rw [double_cover_bivariateTotalDegree _ (by omega), hd]

private theorem signedNormCurvePolynomial_map_totalDegree
    (K E : Type*) [Field K] [NumberField K] [Field E] (β : 𝓞 K)
    {ε : ℤ} (hε : (ε : E) ≠ 0) (hn : 2 ≤ Module.finrank ℚ K) :
    (MvPolynomial.map (Int.castRingHom E) (signedNormCurvePolynomial K β ε)).totalDegree =
      Module.finrank ℚ K := by
  have hd : (C (ε : E) * (integerNormPolynomial K β).map (Int.castRingHom E)).natDegree =
      Module.finrank ℚ K := by
    rw [natDegree_C_mul hε, (integerNormPolynomial_monic K β).natDegree_map,
      integerNormPolynomial_natDegree]
  have hh : bivariateTotalDegree (bivariatePolynomialEquiv E
      (MvPolynomial.map (Int.castRingHom E) (signedNormCurvePolynomial K β ε))) =
      Module.finrank ℚ K := by
    rw [signedNormCurvePolynomial_bivariate_map, double_cover_bivariateTotalDegree _ (by omega), hd]
  simpa only [bivariateTotalDegree, AlgEquiv.symm_apply_apply] using hh

private theorem signedNormCurvePolynomial_map_irreducible_in_every_characteristic
    (K E : Type*) [Field K] [NumberField K] [Field E] (β : 𝓞 K)
    {ε : ℤ} (hε : (ε : E) ≠ 0) (hn : Odd (Module.finrank ℚ K)) :
    Irreducible (MvPolynomial.map (Int.castRingHom E) (signedNormCurvePolynomial K β ε)) := by
  apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv E)).mp
  rw [signedNormCurvePolynomial_bivariate_map]
  let p := C (ε : E) * (integerNormPolynomial K β).map (Int.castRingHom E)
  have hp : Odd p.natDegree := by
    rwa [natDegree_C_mul hε, (integerNormPolynomial_monic K β).natDegree_map,
      integerNormPolynomial_natDegree]
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc E) (monic_X_pow_sub_C p (by decide : (2 : ℕ) ≠ 0))).mpr
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b he => ?_
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  have hb : b ≠ 0 := fun h => hp0 ((IsFractionRing.injective E[X] (RatFunc E))
    (by simpa [h] using he.symm))
  have hd := congrArg RatFunc.intDegree he
  rw [sq, RatFunc.intDegree_mul hb hb, RatFunc.intDegree_polynomial] at hd
  obtain ⟨k, hk⟩ := hp
  have hk' := congrArg (Nat.cast : ℕ → ℤ) hk; push_cast at hk'; omega

private theorem signed_norm_curve_log_free_count
    (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) {ε : ℤ} (hε : IsUnit ε)
    (hn : 2 ≤ Module.finrank ℚ K) (hodd : Odd (Module.finrank ℚ K)) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      (3 * affineHypersurfaceAuxiliaryConstant 0) *
        (Module.finrank ℚ K : ℝ) ^ 4 * B ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  have hprim : PrimitiveIntegerPolynomial (signedNormCurvePolynomial K β ε) := fun c hc => by
    have hcoef : (signedNormCurvePolynomial K β ε).coeff (Finsupp.cons 2 (Finsupp.single 0 0)) = 1 := by
      rw [← bivariatePolynomialEquiv_coeff, signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]; norm_num
    exact isUnit_iff_dvd_one.mpr (hcoef ▸ hc (Finsupp.cons 2 (Finsupp.single 0 0)))
  have hirQ := signedNormCurvePolynomial_map_irreducible_in_every_characteristic K ℚ β
    (hε.map (Int.castRingHom ℚ)).ne_zero hodd
  have hirQbar := signedNormCurvePolynomial_map_irreducible_in_every_characteristic K
    (AlgebraicClosure ℚ) β (hε.map (Int.castRingHom (AlgebraicClosure ℚ))).ne_zero hodd
  have hdZ := signedNormCurvePolynomial_totalDegree K β hε.ne_zero hn
  have hbad_empty (p : ℕ) : p ∈ (∅ : Finset ℕ) ↔
      stepanovThreshold (signedNormCurvePolynomial K β ε).totalDegree < p ∧
        HypersurfaceBadReduction (signedNormCurvePolynomial K β ε) p := by
    simp only [Finset.notMem_empty, false_iff, not_and]
    rintro _ ⟨hp, hbad⟩
    let : Fact p.Prime := ⟨hp⟩
    have hεp := (hε.map (Int.castRingHom (AlgebraicClosure (ZMod p)))).ne_zero
    exact hbad.elim
      (fun h => h ((signedNormCurvePolynomial_map_totalDegree K (AlgebraicClosure (ZMod p)) β hεp hn).trans hdZ.symm))
      (fun h => h (signedNormCurvePolynomial_map_irreducible_in_every_characteristic K
        (AlgebraicClosure (ZMod p)) β hεp hodd))
  have hbf : hypersurfaceBadPrimeFactor (signedNormCurvePolynomial K β ε) = 1 := by
    rw [hypersurfaceBadPrimeFactor_eq_exp (signedNormCurvePolynomial K β ε) hirQbar rfl ∅ hbad_empty]
    simp
  have hh := affine_plane_count_bad_prime (signedNormCurvePolynomial K β ε) hprim hirQ (by omega) hB
  rw [hdZ, hbf] at hh
  convert hh using 1; ring

private lemma rootMultiplicity_pow_exact {F : Type*} [Field F] (p : F[X]) (hp : p ≠ 0)
    (a : F) (n : ℕ) : rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih]; ring

private theorem signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K)) :
    AbsolutelyIrreducible (signedNormCurvePolynomial K β ε) := by
  have hnorm_poly : (integerNormPolynomial K β).map (Int.castRingHom (AlgebraicClosure ℚ)) =
      (minpoly ℚ (β : K)).map (algebraMap ℚ (AlgebraicClosure ℚ)) ^
        Module.finrank ℚ⟮(β : K)⟯ K := by
    have hQ : (integerNormPolynomial K β).map (Int.castRingHom ℚ) =
        minpoly ℚ (β : K) ^ Module.finrank ℚ⟮(β : K)⟯ K := by
      refine Polynomial.eq_of_infinite_eval_eq _ _
        ((Set.infinite_range_of_injective (Int.cast_injective : Function.Injective (fun x : ℤ => (x : ℚ)))).mono ?_)
      rintro _ ⟨x, rfl⟩
      change ((integerNormPolynomial K β).map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) x) =
        (minpoly ℚ (β : K) ^ Module.finrank ℚ⟮(β : K)⟯ K).eval (x : ℚ)
      rw [Polynomial.eval_map_apply, integerNormPolynomial_eval]
      change (Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) : ℚ) = _
      rw [Algebra.coe_norm_int, Polynomial.eval_pow]
      let L := ℚ⟮(β : K)⟯
      let γ : L := AdjoinSimple.gen ℚ (β : K)
      have hβi : IsIntegral ℚ (β : K) := IsIntegral.of_finite ℚ (β : K)
      let pb := IntermediateField.adjoin.powerBasis hβi
      have he : algebraMap L K (algebraMap ℚ L (x : ℚ) - γ) = algebraMap ℚ K (x : ℚ) - (β : K) := by
        simp [γ, L]
      have hsub : ((algebraMap ℤ (𝓞 K) x - β : 𝓞 K) : K) = algebraMap ℚ K (x : ℚ) - (β : K) := by
        simp [RingOfIntegers.coe_eq_algebraMap]
      rw [hsub, ← he, ← Algebra.norm_norm (S := L),
        Algebra.norm_algebraMap_of_basis (Module.Free.chooseBasis L K), map_pow,
        ← Module.finrank_eq_card_chooseBasisIndex]
      have hg : pb.gen = γ := IntermediateField.adjoin.powerBasis_gen hβi
      have hdet : ((algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ)) (x : ℚ) -
          (Algebra.leftMulMatrix pb.basis) pb.gen).det = (minpoly ℚ pb.gen).eval (x : ℚ) := by
        rw [← charpoly_leftMulMatrix pb, Matrix.eval_charpoly]; rfl
      rw [← hg, Algebra.norm_eq_matrix_det pb.basis, map_sub,
        (Algebra.leftMulMatrix pb.basis).commutes, hdet, hg, IntermediateField.minpoly_gen]
    have he : Int.castRingHom (AlgebraicClosure ℚ) =
        (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) := by ext; simp
    rw [he, ← Polynomial.map_map, hQ, Polynomial.map_pow]
  apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv (AlgebraicClosure ℚ))).mp
  rw [← bivariatePolynomialEquiv_map]
  simp only [signedNormCurvePolynomial, AlgEquiv.apply_symm_apply]
  change Irreducible (Polynomial.map
    (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure ℚ)))
    (X ^ 2 - C (C ε * integerNormPolynomial K β)))
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_mul, hnorm_poly]
  have hβ : IsIntegral ℚ (β : K) := IsIntegral.of_finite ℚ (β : K)
  let p := (minpoly ℚ (β : K)).map (algebraMap ℚ (AlgebraicClosure ℚ))
  have hp_sep : p.Separable := (minpoly.irreducible hβ).separable.map
  have hp_deg : 0 < p.natDegree := by
    dsimp [p]; rw [(minpoly.monic hβ).natDegree_map]; exact minpoly.natDegree_pos hβ
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp_deg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (Polynomial.natDegree_pos_iff_degree_pos.mp hp_deg).ne'
  have hm : rootMultiplicity a p = 1 :=
    le_antisymm (rootMultiplicity_le_one_of_separable hp_sep a) ((rootMultiplicity_pos hp0).mpr ha)
  have hc : (ε : AlgebraicClosure ℚ) ≠ 0 := mod_cast hε
  let q := C (ε : AlgebraicClosure ℚ) * p ^ Module.finrank ℚ⟮(β : K)⟯ K
  have hq0 : q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ hp0)
  have hq_odd : Odd (rootMultiplicity a q) := by
    dsimp [q]
    rw [rootMultiplicity_mul hq0, rootMultiplicity_C, rootMultiplicity_pow_exact _ hp0, hm,
      mul_one, zero_add]
    exact hindex
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc (AlgebraicClosure ℚ)) (monic_X_pow_sub_C q (by decide : (2 : ℕ) ≠ 0))).mpr
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b he => ?_
  have hi := IsFractionRing.injective (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ))
  have hd : algebraMap _ (RatFunc (AlgebraicClosure ℚ)) b.denom ≠ 0 := fun h =>
    b.denom_ne_zero (hi (by simpa using h))
  have hb : b ≠ 0 := fun h => hq0 (hi (by simpa [h] using he.symm))
  have hnum : b.num ≠ 0 := RatFunc.num_ne_zero hb
  have hpoly : b.num ^ 2 = q * b.denom ^ 2 := hi <| by
    rw [map_pow, map_mul, map_pow, (div_eq_iff hd).mp b.num_div_denom, mul_pow, he]
  have hmr := congrArg (rootMultiplicity a) hpoly
  rw [rootMultiplicity_pow_exact _ hnum,
    rootMultiplicity_mul (mul_ne_zero hq0 (pow_ne_zero _ b.denom_ne_zero)),
    rootMultiplicity_pow_exact _ b.denom_ne_zero] at hmr
  obtain ⟨k, hk⟩ := hq_odd; omega

private theorem signed_norm_curve_count_of_odd_subfield_index
    (K : Type*) [Field K] [NumberField K] (β : 𝓞 K) {ε : ℤ} (hε : ε ≠ 0)
    (hn : 2 ≤ Module.finrank ℚ K) (hindex : Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ)
      (signedNormCurvePolynomial K β ε))) B : ℝ) ≤
      (4 * affineHypersurfaceAuxiliaryConstant 0) * (Module.finrank ℚ K : ℝ) ^ 3 *
        B ^ (1 / (Module.finrank ℚ K : ℝ)) * (Real.log B + Module.finrank ℚ K) := by
  have hεQ : (ε : ℚ) ≠ 0 := mod_cast hε
  have hd := signedNormCurvePolynomial_map_totalDegree K ℚ β hεQ hn
  have hir_abs : AbsolutelyIrreducibleRat
      (MvPolynomial.map (Int.castRingHom ℚ) (signedNormCurvePolynomial K β ε)) :=
    (absolutelyIrreducibleRat_map_iff _).mpr
      (signedNormCurvePolynomial_absolute_irreducible_of_odd_subfield_index K β hε hindex)
  have hir := mvPolynomial_irreducible_of_field_map (algebraMap ℚ (AlgebraicClosure ℚ)) _ hir_abs
  have hh := rational_plane_curve_count _ hir (by omega) hB
  rw [hd] at hh
  simpa only [curveBound, mul_assoc] using hh

end NormCurvePoly

private theorem odd_degree_classGroup_two_torsion_bound (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
      (classGroupTwoTorsionCard K : ℝ) ≤
        K₀ * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
  classical
  let P := 12 * affineHypersurfaceAuxiliaryConstant 0 * (n : ℝ) ^ 4
  let A := numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n
  have hP0 : 0 < P := by
    have := affineHypersurfaceAuxiliaryConstant_pos 0; dsimp [P]; positivity
  have hA0 : 0 ≤ A := mul_nonneg (numberFieldLatticeBoxConstant_nonneg n (by positivity)) (by positivity)
  refine ⟨P * A * (3 * (9 : ℝ) ^ (n - 1)) + 1, by positivity, fun K _ _ hdeg => ?_⟩
  have hnK : 2 ≤ Module.finrank ℚ K := hdeg ▸ hn
  have hoddK : Odd (Module.finrank ℚ K) := hdeg ▸ hodd
  have hD1 := one_le_abs_discr K
  have hD : 0 < |(discr K : ℝ)| := zero_lt_one.trans_le hD1
  let B := 9 * |(discr K : ℝ)| ^ (1 / (n : ℝ))
  have hroot1 : 1 ≤ |(discr K : ℝ)| ^ (1 / (n : ℝ)) := Real.one_le_rpow hD1 (by positivity)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBroot : |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ B := by
    rw [hdeg]; dsimp [B]; linarith
  obtain ⟨β, _, hb, hcov⟩ := exists_norm_translate_cover K B
  let Q := boundedSquareNormTranslationClasses K B
  let sf := (boundedSquareNormIntegers_finite K B).toFinset
  let tf (q : Q) := (squareNormTranslateFiber_finite K (β q) B).toFinset
  have hsub : sf ⊆ Finset.univ.biUnion tf := fun α hα => by
    obtain ⟨q, hq⟩ := hcov α ((boundedSquareNormIntegers_finite K B).mem_toFinset.mp hα)
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _,
      (squareNormTranslateFiber_finite K (β q) B).mem_toFinset.mpr hq⟩
  let H := max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))
  have hH : 1 ≤ H := le_trans (by linarith) (le_max_left _ _)
  have hroot : H ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ 2 * Real.sqrt B :=
    normCurveBoxHeight_root_le hnK hB
  have hS : ((boundedSquareNormIntegers K B).ncard : ℝ) ≤ P * Q.card * Real.sqrt B := by
    have hnat : (boundedSquareNormIntegers K B).ncard ≤
        ∑ q : Q, (count (signedNormCurveLocus K (β q) 1) H +
          count (signedNormCurveLocus K (β q) (-1)) H) := calc
      (boundedSquareNormIntegers K B).ncard = sf.card := Set.ncard_eq_toFinset_card _ _
      _ ≤ ∑ q : Q, (tf q).card := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun q _ => by
        rw [← Set.ncard_eq_toFinset_card _ (squareNormTranslateFiber_finite K (β q) B)]
        exact squareNormTranslateFiber_count_le K (β q) (hb q)
    refine (Nat.cast_le.mpr hnat).trans ?_
    rw [Nat.cast_sum]
    refine (Finset.sum_le_sum (g := fun _ => P * Real.sqrt B) fun q _ => ?_).trans_eq
      (by simp [Q]; ring)
    have hp := signed_norm_curve_log_free_count K (β q) (ε := 1) isUnit_one hnK hoddK hH
    have hm := signed_norm_curve_log_free_count K (β q) (ε := -1) (by simp) hnK hoddK hH
    change (count (signedNormCurveLocus K (β q) 1) H : ℝ) ≤ _ at hp
    change (count (signedNormCurveLocus K (β q) (-1)) H : ℝ) ≤ _ at hm
    rw [Nat.cast_add]
    have hsum2 : (count (signedNormCurveLocus K (β q) 1) H : ℝ) +
        (count (signedNormCurveLocus K (β q) (-1)) H : ℝ) ≤
        2 * (3 * affineHypersurfaceAuxiliaryConstant 0 * (n : ℝ) ^ 4) *
          (2 * Real.sqrt B) := by
      rw [hdeg] at hp hm hroot
      exact (by linarith : _ ≤ 2 * (3 * affineHypersurfaceAuxiliaryConstant 0 * (n : ℝ) ^ 4) *
        H ^ (1 / (n : ℝ))).trans (mul_le_mul_of_nonneg_left hroot (by linarith [hP0]))
    exact hsum2.trans_eq (by dsimp [P]; ring)
  have hQ := boundedSquareNormTranslationClasses_uniform_count K hnK hB hBroot
  rw [hdeg] at hQ
  have hcard : (classGroupTwoTorsionCard K : ℝ) ≤ (boundedSquareNormIntegers K B).ncard := by
    have hh := classGroupTwoTorsionCard_le_boundedSquareNormIntegers K
    rw [hdeg] at hh; exact Nat.cast_le.mpr hh
  have hpre : (classGroupTwoTorsionCard K : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (P * A) * (B ^ (n - 1) * Real.sqrt B) := by
    have h1 := mul_le_mul_of_nonneg_right (hcard.trans hS) (Real.sqrt_nonneg |(discr K : ℝ)|)
    have h2 := mul_le_mul_of_nonneg_left hQ (mul_nonneg hP0.le (Real.sqrt_nonneg B))
    nlinarith only [h1, h2]
  exact (classGroup_discriminant_bound_of_balanced_radius hD (by omega : 0 < n) hpre).trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

private theorem no_index_two_classGroup_two_torsion_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
      (∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) →
      (classGroupTwoTorsionCard K : ℝ) ≤
        K₀ * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) * Real.log |(discr K : ℝ)| := by
  classical
  let C₀ := 4 * affineHypersurfaceAuxiliaryConstant 0
  let P := 8 * C₀ * (n : ℝ) ^ 4
  let A := numberFieldLatticeBoxConstant n ((n : ℝ) ^ 3) * (2 : ℝ) ^ n
  let E := smallSubfieldIntegerCountConstant n * (9 : ℝ) ^ ((n : ℝ) / 4)
  let K₀ := (P * A * (3 * (9 : ℝ) ^ (n - 1))) * (Real.log 9 + 2) + E
  have hC₀ : 0 < C₀ := mul_pos (by norm_num) (affineHypersurfaceAuxiliaryConstant_pos 0)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hA : 0 ≤ A := mul_nonneg (numberFieldLatticeBoxConstant_nonneg n (by positivity)) (by positivity)
  have hE : 0 < E := mul_pos (smallSubfieldIntegerCountConstant_pos n) (by positivity)
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  refine ⟨K₀, by dsimp [K₀]; positivity, fun K _ _ hdeg hnoTwo => ?_⟩
  have hnK : 2 ≤ Module.finrank ℚ K := hdeg ▸ hn
  let D := |(discr K : ℝ)|
  let B := 9 * D ^ (1 / (n : ℝ))
  let a := 1 / 2 - 1 / (2 * (n : ℝ))
  have hnpos : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := mod_cast hn
  have hD3 : 3 ≤ D := three_le_abs_discr K hnK
  have hD1 : 1 ≤ D := by linarith
  have hD : 0 < D := by linarith
  have hlog : 1 ≤ Real.log D := one_le_log_abs_discr K hnK
  have hroot1 : 1 ≤ D ^ (1 / (n : ℝ)) := Real.one_le_rpow hD1 (by positivity)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBroot : D ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ B := by rw [hdeg]; dsimp [B]; linarith
  have hlogB : 0 ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB]
  obtain ⟨β, _, hb, hcov⟩ := exists_norm_translate_cover K B
  let Q := boundedSquareNormTranslationClasses K B
  let sf := (boundedSquareNormIntegers_finite K B).toFinset
  let ef := (boundedSmallSubfieldIntegers_finite K B).toFinset
  let tf (q : Q) := if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
    (squareNormTranslateFiber_finite K (β q) B).toFinset else ∅
  have hsub : sf ⊆ ef ∪ Finset.univ.biUnion tf := fun α hα => by
    obtain ⟨q, hq⟩ := hcov α ((boundedSquareNormIntegers_finite K B).mem_toFinset.mp hα)
    by_cases ho : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, ?_⟩)
      dsimp only [tf]; rw [ite_eq_left ho]
      exact (squareNormTranslateFiber_finite K (β q) B).mem_toFinset.mpr hq
    · refine Finset.mem_union_left _ ((boundedSmallSubfieldIntegers_finite K B).mem_toFinset.mpr ?_)
      let L := ℚ⟮(β q : K)⟯
      have he : Even (Module.finrank L K) := (Nat.even_or_odd _).resolve_right ho
      have hpos : 0 < Module.finrank L K := Module.finrank_pos
      have hne := hnoTwo L
      have hfour : 4 ≤ Module.finrank L K := by obtain ⟨k, hk⟩ := he; omega
      have hdim : 4 * Module.finrank ℚ L ≤ Module.finrank ℚ K := by
        have ht := Module.finrank_mul_finrank ℚ L K; nlinarith
      refine ⟨hq.1.2.1, L, hdim, ?_⟩
      obtain ⟨x, hx⟩ := hq.2; rw [hx]
      change algebraMap ℤ K x - (β q : K) ∈ L
      exact L.sub_mem (L.intCast_mem x) (IntermediateField.mem_adjoin_simple_self ℚ (β q : K))
  let H := max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))
  have hH : 1 ≤ H := le_trans (by linarith) (le_max_left _ _)
  have hroot : H ^ (1 / (Module.finrank ℚ K : ℝ)) ≤ 2 * Real.sqrt B :=
    normCurveBoxHeight_root_le hnK hB
  have hlogH : Real.log H + Module.finrank ℚ K ≤
      2 * (Module.finrank ℚ K : ℝ) * (Real.log B + 1) :=
    normCurveBoxHeight_log_le hnK hB
  have hS : ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      (boundedSmallSubfieldIntegers K B).ncard +
        P * Q.card * Real.sqrt B * (Real.log B + 1) := by
    have hnat : (boundedSquareNormIntegers K B).ncard ≤
        (boundedSmallSubfieldIntegers K B).ncard +
          ∑ q : Q, if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
            count (signedNormCurveLocus K (β q) 1) H +
              count (signedNormCurveLocus K (β q) (-1)) H else 0 := calc
      (boundedSquareNormIntegers K B).ncard = sf.card := Set.ncard_eq_toFinset_card _ _
      _ ≤ ef.card + ∑ q : Q, (tf q).card :=
          (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_left Finset.card_biUnion_le _))
      _ ≤ _ := by
        rw [← Set.ncard_eq_toFinset_card _ (boundedSmallSubfieldIntegers_finite K B)]
        refine Nat.add_le_add_left (Finset.sum_le_sum fun q _ => ?_) _
        by_cases ho : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
        · dsimp only [tf]; rw [ite_eq_left ho, ite_eq_left ho,
            ← Set.ncard_eq_toFinset_card _ (squareNormTranslateFiber_finite K (β q) B)]
          exact squareNormTranslateFiber_count_le K (β q) (hb q)
        · dsimp only [tf]; rw [ite_eq_right ho, ite_eq_right ho, Finset.card_empty]
    refine (Nat.cast_le.mpr hnat).trans ?_
    rw [Nat.cast_add, Nat.cast_sum]
    refine add_le_add le_rfl
      ((Finset.sum_le_sum (g := fun _ => P * Real.sqrt B * (Real.log B + 1)) fun q _ => ?_).trans_eq
        (by simp [Q]; ring))
    by_cases ho : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
    · rw [ite_eq_left ho, Nat.cast_add]
      have hp := signed_norm_curve_count_of_odd_subfield_index K (β q) (ε := 1) (by norm_num) hnK ho hH
      have hm := signed_norm_curve_count_of_odd_subfield_index K (β q) (ε := -1) (by norm_num) hnK ho hH
      change (count (signedNormCurveLocus K (β q) 1) H : ℝ) ≤ _ at hp
      change (count (signedNormCurveLocus K (β q) (-1)) H : ℝ) ≤ _ at hm
      rw [hdeg] at hp hm hroot hlogH
      have hprod : H ^ (1 / (n : ℝ)) * (Real.log H + n) ≤
          (2 * Real.sqrt B) * (2 * (n : ℝ) * (Real.log B + 1)) :=
        mul_le_mul hroot hlogH (by linarith [Real.log_nonneg hH]) (by positivity)
      calc (count (signedNormCurveLocus K (β q) 1) H : ℝ) +
              (count (signedNormCurveLocus K (β q) (-1)) H : ℝ)
          ≤ 2 * (C₀ * (n : ℝ) ^ 3) * (H ^ (1 / (n : ℝ)) * (Real.log H + n)) := by
            dsimp only [C₀]; linarith
        _ ≤ 2 * (C₀ * (n : ℝ) ^ 3) * ((2 * Real.sqrt B) * (2 * (n : ℝ) * (Real.log B + 1))) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = P * Real.sqrt B * (Real.log B + 1) := by dsimp [P]; ring
    · rw [ite_eq_right ho, Nat.cast_zero]; positivity
  have hQ := boundedSquareNormTranslationClasses_uniform_count K hnK hB hBroot
  rw [hdeg] at hQ
  have hmain : P * Q.card * Real.sqrt B * (Real.log B + 1) ≤
      (P * A * (3 * (9 : ℝ) ^ (n - 1))) * D ^ a * (Real.log B + 1) := by
    have hm := mul_le_mul_of_nonneg_left hQ (mul_nonneg (mul_nonneg hP (Real.sqrt_nonneg B)) hlogB)
    have hpre : (P * Q.card * Real.sqrt B * (Real.log B + 1)) * Real.sqrt D ≤
        (P * A * (Real.log B + 1)) * (B ^ (n - 1) * Real.sqrt B) := by convert hm using 1 <;> ring
    convert classGroup_discriminant_bound_of_balanced_radius hD hnpos hpre using 1; ring
  have hblog : Real.log B + 1 ≤ (Real.log 9 + 2) * Real.log D := by
    have hn1 : (1 : ℝ) ≤ n := mod_cast hnpos
    have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one (zero_lt_one.trans_le hn1)).mpr hn1
    dsimp [B]
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hD _).ne', Real.log_rpow hD]
    nlinarith
  have hmain' : P * Q.card * Real.sqrt B * (Real.log B + 1) ≤
      (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) * D ^ a * Real.log D :=
    hmain.trans ((mul_le_mul_of_nonneg_left hblog (by positivity)).trans_eq (by ring))
  have hexc : ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤ E * D ^ a * Real.log D := by
    have hh := boundedSmallSubfieldIntegers_balanced_count K hD1
    rw [hdeg] at hh
    have ha : (1 / 4 : ℝ) ≤ a := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ 2 * n)
      dsimp [a]; linarith
    calc ((boundedSmallSubfieldIntegers K B).ncard : ℝ)
        ≤ E * D ^ (1 / 4 : ℝ) := hh
      _ ≤ E * D ^ a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD1 ha) hE.le
      _ ≤ E * D ^ a * Real.log D := le_mul_of_one_le_right (by positivity) hlog
  have hcard : (classGroupTwoTorsionCard K : ℝ) ≤ (boundedSquareNormIntegers K B).ncard := by
    have hh := classGroupTwoTorsionCard_le_boundedSquareNormIntegers K
    rw [hdeg] at hh; exact Nat.cast_le.mpr hh
  calc (classGroupTwoTorsionCard K : ℝ) ≤ _ := hcard.trans hS
    _ ≤ E * D ^ a * Real.log D +
          (P * A * (3 * (9 : ℝ) ^ (n - 1)) * (Real.log 9 + 2)) * D ^ a * Real.log D :=
        add_le_add hexc hmain'
    _ = K₀ * D ^ a * Real.log D := by dsimp [K₀]; ring

private theorem two_pow_primeFactors_subpower (a : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ D : ℕ, 1 ≤ D →
      (2 : ℝ) ^ (a * D.primeFactors.card) ≤ K₀ * (D : ℝ) ^ ε := by
  let R : ℝ := 2 ^ a
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by positivity
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp (Real.log R / ε))
  have hM0 : (0 : ℝ) < M := (Real.exp_pos _).trans hM
  have hcut : Real.log R ≤ ε * Real.log (M : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hM.le
    rw [Real.log_exp] at hh
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hh
  refine ⟨Real.exp ((M : ℝ) * Real.log R), Real.exp_pos _, fun D hD => ?_⟩
  have hD0 : (0 : ℝ) < D := mod_cast (by omega : 0 < D)
  have hsmall : (D.primeFactors.filter (· < M)).card ≤ M :=
    (Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2).trans_eq
      (Finset.card_range M)
  have hsum_log : ∑ p ∈ D.primeFactors, Real.log (p : ℝ) ≤ Real.log (D : ℝ) := by
    have hpos : ∀ p ∈ D.primeFactors, (0 : ℝ) < p := fun p hp =>
      Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
    rw [← Real.log_prod fun p hp => (hpos p hp).ne']
    exact Real.log_le_log (Finset.prod_pos hpos) (by
      rw [← Nat.cast_prod]
      exact Nat.cast_le.mpr (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd D)))
  have hsum : (D.primeFactors.card : ℝ) * Real.log R ≤
      (M : ℝ) * Real.log R + ε * Real.log (D : ℝ) := calc
    (D.primeFactors.card : ℝ) * Real.log R = ∑ _p ∈ D.primeFactors, Real.log R := by simp
    _ ≤ ∑ p ∈ D.primeFactors, ((if p < M then Real.log R else 0) + ε * Real.log (p : ℝ)) :=
      Finset.sum_le_sum fun p hp => by
        by_cases hpm : p < M
        · rw [ite_eq_left hpm]
          exact le_add_of_nonneg_right (mul_nonneg hε.le
            (Real.log_nonneg (mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)))
        · rw [ite_eq_right hpm, zero_add]
          exact hcut.trans (mul_le_mul_of_nonneg_left
            (Real.log_le_log hM0 (mod_cast Nat.le_of_not_gt hpm)) hε.le)
    _ = (D.primeFactors.filter (· < M)).card * Real.log R +
          ε * ∑ p ∈ D.primeFactors, Real.log (p : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum]; simp
    _ ≤ (M : ℝ) * Real.log R + ε * Real.log (D : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right (mod_cast hsmall) hlogR)
        (mul_le_mul_of_nonneg_left hsum_log hε.le)
  have hexp := Real.exp_le_exp.mpr hsum
  rw [← Real.log_pow, Real.exp_log (pow_pos hR0 _)] at hexp
  rw [pow_mul]
  refine hexp.trans_eq ?_
  rw [Real.rpow_def_of_pos hD0, ← Real.exp_add]; congr 1; ring

private theorem quadratic_class_group_numeric_descent (m : ℕ) (hm : 2 ≤ m)
    (C : ℝ) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ D : ℕ, 1 ≤ D → ∀ x h H : ℝ,
      1 ≤ x → x ^ 2 ≤ (D : ℝ) → 0 ≤ h →
      h ≤ C * x ^ (1 / 2 - 1 / (2 * (m : ℝ))) * (Real.log x + 1) →
      H ≤ (h * (2 : ℝ) ^ ((2 * m) * D.primeFactors.card + m)) ^ 2 →
      H ≤ A * (D : ℝ) ^ (1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ))) := by
  have hmR : (2 : ℝ) ≤ m := mod_cast hm
  let ε : ℝ := 1 / (4 * (m : ℝ))
  have hhalf : 0 < ε / 2 := by dsimp [ε]; positivity
  obtain ⟨A₀, hA₀, hprime⟩ := two_pow_primeFactors_subpower (4 * m) hhalf
  let L : ℝ := (Nat.factorial 2 : ℝ) / (ε / 2) ^ 2 * Real.exp (ε / 2)
  have hL : 0 < L := by dsimp [L]; positivity
  let A := A₀ * L
  refine ⟨C ^ 2 * (2 : ℝ) ^ (2 * m) * A, by dsimp [A]; positivity,
    fun D hD x h H hx hxD hh hbound hH => ?_⟩
  have hDR : (1 : ℝ) ≤ D := mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hx0 : 0 < x := by linarith
  have hxD' : x ≤ (D : ℝ) := by nlinarith
  have hlog := logarithm_add_one_pow_le_rpow 2 hhalf hDR
  change (Real.log (D : ℝ) + 1) ^ 2 ≤ L * (D : ℝ) ^ (ε / 2) at hlog
  have hwt : (2 : ℝ) ^ ((4 * m) * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ 2 ≤
      A * (D : ℝ) ^ ε :=
    (mul_le_mul (hprime D hD) hlog (by positivity) (by positivity)).trans_eq
      (by dsimp [A]; rw [show (D : ℝ) ^ ε = (D : ℝ) ^ (ε / 2) * (D : ℝ) ^ (ε / 2) by
        rw [← Real.rpow_add hD0]; congr 1; ring]; ring)
  let α : ℝ := 1 / 2 - 1 / (2 * (m : ℝ))
  have hα : 0 ≤ α := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 * m)
    dsimp [α]; linarith
  have hgeom : (x ^ α) ^ 2 ≤ (D : ℝ) ^ α := by
    rw [Real.rpow_pow_comm hx0.le]; exact Real.rpow_le_rpow (sq_nonneg x) hxD hα
  have hlogs : (Real.log x + 1) ^ 2 ≤ (Real.log (D : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hx]) (by linarith [Real.log_le_log hx0 hxD']) 2
  let P : ℝ := (2 : ℝ) ^ ((2 * m) * D.primeFactors.card + m)
  have hP : P ^ 2 = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ ((4 * m) * D.primeFactors.card) := by
    dsimp [P]; rw [← pow_mul, ← pow_add]; congr 1; ring
  have hmain : C ^ 2 * (x ^ α) ^ 2 * (Real.log x + 1) ^ 2 ≤
      C ^ 2 * (D : ℝ) ^ α * (Real.log (D : ℝ) + 1) ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hgeom (sq_nonneg C)) hlogs (sq_nonneg _) (by positivity)
  have hexp : α + ε = 1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ)) := by
    dsimp [α, ε]; push_cast; field_simp; ring
  calc H ≤ ((C * x ^ α * (Real.log x + 1)) * P) ^ 2 := hH.trans
        (pow_le_pow_left₀ (mul_nonneg hh (by positivity))
          (mul_le_mul_of_nonneg_right hbound (by positivity)) 2)
    _ = (C ^ 2 * (x ^ α) ^ 2 * (Real.log x + 1) ^ 2) * P ^ 2 := by ring
    _ ≤ (C ^ 2 * (D : ℝ) ^ α * (Real.log (D : ℝ) + 1) ^ 2) * P ^ 2 :=
        mul_le_mul_of_nonneg_right hmain (sq_nonneg P)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m)) * (D : ℝ) ^ α *
          ((2 : ℝ) ^ ((4 * m) * D.primeFactors.card) * (Real.log (D : ℝ) + 1) ^ 2) := by
        rw [hP]; ring
    _ ≤ (C ^ 2 * (2 : ℝ) ^ (2 * m)) * (D : ℝ) ^ α * (A * (D : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hwt (by positivity)
    _ = (C ^ 2 * (2 : ℝ) ^ (2 * m) * A) * (D : ℝ) ^ (1 / 2 - 1 / (2 * ((2 * m : ℕ) : ℝ))) := by
        rw [← hexp, Real.rpow_add hD0]; ring

private theorem classGroup_uniform_logarithmic_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
      (classGroupTwoTorsionCard K : ℝ) ≤
        C * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
          (Real.log ((discr K).natAbs : ℝ) + 1) := by
  classical
  have hlog1 (K : Type u) [Field K] [NumberField K] :
      1 ≤ Real.log ((discr K).natAbs : ℝ) + 1 := by
    rw [numberField_discriminant_natAbs_cast]
    linarith [Real.log_nonneg (one_le_abs_discr K)]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n = 2
    · subst n
      obtain ⟨C₀, hC₀, hb₀⟩ := two_pow_primeFactors_subpower 4 (by norm_num : (0 : ℝ) < 1 / 4)
      refine ⟨4 * C₀, by positivity, fun K _ _ hdeg => ?_⟩
      have hh : (classGroupTwoTorsionCard K : ℝ) ≤
          (2 : ℝ) ^ (4 * (discr K).natAbs.primeFactors.card + 2) :=
        mod_cast quadratic_field_classGroupTwoTorsionCard_le K hdeg
      have hb : (classGroupTwoTorsionCard K : ℝ) ≤
          (4 * C₀) * ((discr K).natAbs : ℝ) ^ (1 / 4 : ℝ) := by
        have h1 := hb₀ (discr K).natAbs (numberField_discriminant_natAbs_pos K)
        rw [pow_add] at hh; norm_num at hh; linarith
      convert hb.trans (le_mul_of_one_le_right (by positivity) (hlog1 K)) using 1
      norm_num
    obtain ⟨C_no2, hC_no2, hno2_raw⟩ := no_index_two_classGroup_two_torsion_bound.{u} n hn
    have hno2_bd (K : Type u) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = n)
        (hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2) :
        (classGroupTwoTorsionCard K : ℝ) ≤
          C_no2 * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log ((discr K).natAbs : ℝ) + 1) := by
      rw [numberField_discriminant_natAbs_cast]
      exact (hno2_raw K hdeg hno).trans
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    by_cases hm : 2 ≤ n / 2
    · obtain ⟨C, hC, hbase⟩ := ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) hm
      obtain ⟨A, hA, hstep⟩ := quadratic_class_group_numeric_descent (n / 2) hm C hC
      let T := max A C_no2
      have hAT : A ≤ T := le_max_left _ _
      have hNT : C_no2 ≤ T := le_max_right _ _
      refine ⟨T, hA.trans_le hAT, fun K _ _ hdeg => ?_⟩
      have hD : 1 ≤ (discr K).natAbs := numberField_discriminant_natAbs_pos K
      by_cases hno : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2
      · exact (hno2_bd K hdeg hno).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNT (by positivity)) (by linarith [hlog1 K]))
      push Not at hno
      obtain ⟨L, hL⟩ := hno
      have ht := Module.finrank_mul_finrank ℚ L K
      rw [hL, hdeg] at ht
      have hLdeg : Module.finrank ℚ L = n / 2 := by omega
      have hnEq : n = 2 * (n / 2) := by omega
      have hgenus : (classGroupTwoTorsionCard K : ℝ) ≤
          ((classGroupTwoTorsionCard L : ℝ) *
            (2 : ℝ) ^ ((2 * (n / 2)) * (discr K).natAbs.primeFactors.card + n / 2)) ^ 2 := by
        have hh := quadratic_classGroupTwoTorsion_descent L K hL
        rw [hdeg, hLdeg] at hh; nth_rw 1 [hnEq] at hh; exact_mod_cast hh
      have hh := hstep (discr K).natAbs hD ((discr L).natAbs : ℝ)
        (classGroupTwoTorsionCard L : ℝ) (classGroupTwoTorsionCard K : ℝ)
        (mod_cast numberField_discriminant_natAbs_pos L)
        (mod_cast quadratic_absolute_discriminant_square_le K L hL)
        (by positivity) (hbase L hLdeg) hgenus
      have hh' : (classGroupTwoTorsionCard K : ℝ) ≤
          A * ((discr K).natAbs : ℝ) ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
        simpa only [← hnEq] using hh
      exact hh'.trans ((mul_le_mul_of_nonneg_right hAT (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) (hlog1 K)))
    · refine ⟨C_no2, hC_no2, fun K _ _ hdeg => hno2_bd K hdeg fun L hL => ?_⟩
      have ht := Module.finrank_mul_finrank ℚ L K
      rw [hL, hdeg] at ht; omega

theorem classGroup_two_torsion_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [NumberField K], Module.finrank ℚ K = n →
        (classGroupTwoTorsionCard K : ℝ) ≤
          C * |(discr K : ℝ)| ^ (1 / 2 - 1 / (2 * (n : ℝ))) *
            (Real.log |(discr K : ℝ)|) ^ (1 - n % 2) := by
  by_cases hodd : Odd n
  · obtain ⟨C, hC, hbd⟩ := odd_degree_classGroup_two_torsion_bound.{u} n (by omega) hodd
    refine ⟨C, hC, fun K _ _ hdeg => ?_⟩
    rw [Nat.odd_iff.mp hodd, Nat.sub_self, pow_zero, mul_one]
    exact hbd K hdeg
  · obtain ⟨C, hC, hbound⟩ := classGroup_uniform_logarithmic_bound.{u} n (by omega)
    refine ⟨2 * C, by positivity, fun K _ _ hdeg => ?_⟩
    rw [Nat.not_odd_iff.mp hodd, Nat.sub_zero, pow_one]
    have hlog : 1 ≤ Real.log |(discr K : ℝ)| := one_le_log_abs_discr K (by omega)
    have hh := hbound K hdeg
    rw [numberField_discriminant_natAbs_cast] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left
      (show Real.log |(discr K : ℝ)| + 1 ≤ 2 * Real.log |(discr K : ℝ)| by linarith)
      (by positivity))).trans_eq (by ring)

end
end CCDN
