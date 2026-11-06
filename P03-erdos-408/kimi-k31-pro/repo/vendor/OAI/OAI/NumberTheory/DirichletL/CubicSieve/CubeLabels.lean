module

public import OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid

section
namespace FirstPassCubeLabels
open MixedCrossSeparation (crossSymbol quadraticCrossPhase)

private theorem cross_sixth {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg i k ^ 6 = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  simpa only [crossSymbol, map_pow, ite_eq_right hnot] using
    canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem reverse_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg k i = crossSymbol p hg i k *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) := by
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  symm
  calc
    _ = crossSymbol p hg i k ^ 4 *
        (crossSymbol p hg k i ^ 2 * crossSymbol p hg k i) := by ring
    _ = crossSymbol p hg i k ^ 6 * crossSymbol p hg k i := by rw [← hr]; ring
    _ = _ := by rw [cross_sixth p hcop hg i k hik, one_mul]

private theorem local_quadratic_sq {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^ 2 = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, cross_sixth p hcop hg i k hik,
    cross_sixth p hcop hg k i hik.symm, one_mul]

private theorem crt_exponent_table (side parityBit ε₁ ε₂ : Bool)
    (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) % 6 =
      ((if side then 5 else 1) * crtExponent side parityBit ε₁ ε₂) % 6 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    first | exact False.elim (he (by decide)) | decide

theorem active_cube_cross_local {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^
        (conductorExponent parityBit ε₁ ε₂).val := by
  let x := crossSymbol p hg i k
  let q := crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3
  have hrev : crossSymbol p hg k i = x * q := reverse_cross_eq_quadratic p hcop hg hpr i k hik
  have h6 : x ^ 6 = 1 := cross_sixth p hcop hg i k hik
  have hs : star x = x ^ 5 := by
    have h := canonicalSextic_conj_as_row_label (Ideal.span {p i}) (hg i) (p k)
    change star x = x * x ^ 4 at h
    rw [h]
    ring
  calc
    _ = x ^ ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) *
        q ^ (conductorExponent parityBit ε₁ ε₂).val := by rw [hrev, mul_pow, pow_add]; ring
    _ = _ := by
      congr 1
      cases side
      · change x ^ (1 + (conductorExponent parityBit ε₁ ε₂).val) = x ^ crtExponent false parityBit ε₁ ε₂
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using crt_exponent_table false parityBit ε₁ ε₂ he
      · change x ^ (5 + (conductorExponent parityBit ε₁ ε₂).val) = star (x ^ crtExponent true parityBit ε₁ ε₂)
        rw [star_pow, hs, ← pow_mul]
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        exact crt_exponent_table true parityBit ε₁ ε₂ he

def cubeOddSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1

def mixedCubeCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) : ℂ :=
  ∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val

private theorem cube_cross_local_if {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) :
    (if conductorExponent parityBit ε₁ ε₂ ≠ 0 then
      crossSymbol p hg i k ^ (if side then 5 else 1) *
        crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val else 1) =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (if (conductorExponent parityBit ε₁ ε₂).val % 2 = 1 then
        crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
  by_cases he : conductorExponent parityBit ε₁ ε₂ = 0
  · simp [he, crtExponent]
  · rw [ite_eq_left he, active_cube_cross_local p hcop hg hpr i k hik side parityBit ε₁ ε₂ he]
    congr 1
    rw [pow_eq_pow_mod _ (local_quadratic_sq p hcop hg i k hik)]
    by_cases ho : (conductorExponent parityBit ε₁ ε₂).val % 2 = 1
    · simp [ho]
    · have hz : (conductorExponent parityBit ε₁ ε₂).val % 2 = 0 := by omega
      simp [ hz]

theorem mixedCubeCross_eq_row_quadratic {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂) := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
      (crtLabel p B v ε₁ ε₂ side) =
      ∏ i ∈ U, ∏ k ∈ B, crossSymbol p hg i k ^
        crtExponent side (parity (v k)) (ε₁ k) (ε₂ k) := by
    simp only [finiteSquarefreeRow, crtLabel, primeProduct, map_prod, map_pow, crossSymbol]
  calc
    _ = (∏ i ∈ U, ∏ k ∈ B,
        if side then star (crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k))
        else crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k)) *
      (∏ i ∈ U, ∏ k ∈ B,
        if (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1 then
          crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
      simp only [mixedCubeCross, Finset.prod_filter, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro k hk
      apply cube_cross_local_if p hcop hg hpr i k
      exact fun he => Finset.disjoint_left.mp hd hi (he ▸ hk)
    _ = _ := by
      congr 1
      · rw [hr]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, star_prod]
      · simp only [quadraticCrossPhase, cubeOddSupport, Finset.prod_filter]

end FirstPassCubeLabels

open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel
abbrev O := ActualEisensteinCubic.O

def squarePart (I : Ideal O) : Ideal O := (exists_sq_mul_squarefree I).choose

def squarefreePart (I : Ideal O) : Ideal O :=
  (exists_sq_mul_squarefree I).choose_spec.choose

theorem squarePart_sq_mul_squarefreePart (I : Ideal O) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.1

theorem squarefree_squarefreePart (I : Ideal O) : Squarefree (squarefreePart I) :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.2

theorem squarePart_ne_zero {I : Ideal O} (hI : I ≠ 0) : squarePart I ≠ 0 := by
  intro hz
  have h := squarePart_sq_mul_squarefreePart I
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact hI h.symm

theorem squarefree_decomposition_unique {A B D E : Ideal O}
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : Squarefree D) (hE : Squarefree E)
    (h : A ^ 2 * D = B ^ 2 * E) : A = B ∧ D = E := by
  have hf := congrArg normalizedFactors h
  rw [normalizedFactors_mul (pow_ne_zero _ hA) hD.ne_zero,
    normalizedFactors_mul (pow_ne_zero _ hB) hE.ne_zero,
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have hd := (squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD
  have he := (squarefree_iff_nodup_normalizedFactors hE.ne_zero).mp hE
  have hcount (P : Ideal O) :
      (normalizedFactors A).count P = (normalizedFactors B).count P ∧
      (normalizedFactors D).count P = (normalizedFactors E).count P := by
    have hc := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hd1 := Multiset.nodup_iff_count_le_one.mp hd P
    have he1 := Multiset.nodup_iff_count_le_one.mp he P
    omega
  constructor
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hA hB).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).1)
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hD.ne_zero hE.ne_zero).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).2)

theorem squarePart_mul_squarefree {A D : Ideal O} (hA : A ≠ 0) (hD : Squarefree D) :
    squarePart (A ^ 2 * D) = A ∧ squarefreePart (A ^ 2 * D) = D :=
  squarefree_decomposition_unique
    (squarePart_ne_zero (mul_ne_zero (pow_ne_zero _ hA) hD.ne_zero)) hA
    (squarefree_squarefreePart _) hD (squarePart_sq_mul_squarefreePart _)

def decompositionEquiv : {I : Ideal O // I ≠ 0} ≃
    {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D} where
  toFun I := (⟨squarePart I.val, squarePart_ne_zero I.property⟩,
    ⟨squarefreePart I.val, squarefree_squarefreePart I.val⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val, mul_ne_zero (pow_ne_zero _ p.1.property) p.2.property.ne_zero⟩
  left_inv I := Subtype.ext (squarePart_sq_mul_squarefreePart I.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).2

theorem norm_decomposition (I : Ideal O) :
    Ideal.absNorm (squarePart I) ^ 2 * Ideal.absNorm (squarefreePart I) = Ideal.absNorm I := by
  simpa only [map_mul, map_pow] using congrArg Ideal.absNorm (squarePart_sq_mul_squarefreePart I)

open ActualEisensteinCubic QuadraticInitialBound CompletedGauss

theorem quadraticRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    quadraticRow P hg S (a * b) = quadraticRow P hg S a * quadraticRow P hg S b := by
  rw [quadraticRow, finiteSquarefreeRow_mul, mul_pow]
  rfl

theorem quadraticRow_square {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    quadraticRow P hg S (a ^ 2) = rowCoprimeMask P S a := by
  have heq : quadraticRow P hg S (a ^ 2) = finiteSquarefreeRow P hg S (a ^ 6) := by
    simp only [quadraticRow, finiteSquarefreeRow, map_pow, ← Finset.prod_pow, ← pow_mul]
  rw [heq, finiteSquarefreeRow_sixth_power]
  rfl

end QuadraticSquarefreeKernel
end

namespace QuadraticMainBoundary
open UniqueFactorizationMonoid
abbrev O := ActualEisensteinCubic.O
open QuadraticSquarefreeKernel

def cutoffDifference (K : ℝ) (H D : Ideal O) : ℝ :=
  (if (Ideal.absNorm (H * D) : ℝ) ≤ K then 1 else 0) -
    (if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0)

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

theorem cutoffDifference_nonzero_iff (K : ℝ) (H D : Ideal O) (hD : D ≠ 0) :
    cutoffDifference K H D ≠ 0 ↔
      (Ideal.absNorm H : ℝ) ≤ K ∧ K < (Ideal.absNorm (H * D) : ℝ) := by
  have hmono : (Ideal.absNorm H : ℝ) ≤ Ideal.absNorm (H * D) := by
    rw [map_mul, Nat.cast_mul]
    nlinarith [norm_one_le hD, Nat.cast_nonneg (α := ℝ) (Ideal.absNorm H)]
  unfold cutoffDifference
  split_ifs <;> simp_all ; linarith

theorem cutoffDifference_eq_neg_one_of_nonzero (K : ℝ) (H D : Ideal O) (hD : D ≠ 0)
    (h : cutoffDifference K H D ≠ 0) : cutoffDifference K H D = -1 := by
  obtain ⟨hH, hHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  simp only [cutoffDifference, ite_eq_right (not_le.mpr hHD), ite_eq_left hH]
  norm_num

theorem cutoffDifference_eq_zero_of_product_le (K : ℝ) {H D E : Ideal O}
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hB : (Ideal.absNorm (H * D * E) : ℝ) ≤ K) : cutoffDifference K H D = 0 := by
  by_contra h
  have hh := (cutoffDifference_nonzero_iff K H D hD).mp h
  have he := norm_one_le hE
  rw [map_mul, Nat.cast_mul] at hB
  have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
  nlinarith

end QuadraticMainBoundary

namespace QuadraticDivisorCancellation
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound QuadraticSquarefreeKernel

theorem double_divisor_factorization {κ : Type*} [DecidableEq κ]
    (z : κ → ℂ) (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (-1 : ℂ) ^ E.card * (∏ i ∈ D, z i) * ∏ i ∈ E, z i) =
    (∏ i ∈ T, (1 - z i ^ 2)) *
      ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i := by
  have hm (V : Finset κ) :
      (∑ E ∈ V.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) =
      ∏ i ∈ V, (1 - z i) := by
    rw [Finset.prod_sub]
    simp only [Finset.prod_const_one, mul_one]
  calc
    _ = (∑ D ∈ T.powerset, ∏ i ∈ D, z i) *
        (∑ E ∈ (T ∪ U).powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = (∏ i ∈ T, (1 + z i)) * ((∏ i ∈ T, (1 - z i)) * ∏ i ∈ U, (1 - z i)) := by
      rw [← Finset.prod_one_add, hm, Finset.prod_union hTU]
    _ = (∏ i ∈ T, (1 - z i ^ 2)) * ∏ i ∈ U, (1 - z i) := by
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by rw [hm]

end QuadraticDivisorCancellation

end

end OAI
