module

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SupportedIdelePowerLocalUnitQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Supported idele power quotient

This file expresses the supported idele quotient as the product of its local
archimedean and finite-place power indices and evaluates its cardinality.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The middle term in the supported exact sequence, evaluated as the
product of its actual local power indices.  The archimedean factors are
the sign indices, while each finite factor is the finite local
power index.  The following product-formula step evaluates the remaining
finite defect product. -/
theorem card_supportedIdeleQuotient_eq_localPowerIndexProduct
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) =
      (∏ w : InfinitePlace K,
          if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
        ∏ v : ↥S,
          (n : ℕ) *
            ((n : ℕ) *
              finitePlaceNthPowerDefect (K := K) n v.1) := by
  classical
  rw [
    card_supportedIdeleQuotient_eq_localPowerClasses
       n S T,
    Nat.card_prod,
    Nat.card_pi,
    Nat.card_pi]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    exact card_infinitePlace_nthPowerQuotient n w
  · apply Finset.prod_congr rfl
    intro v _
    exact
      card_finitePlace_nthPowerQuotient_eq_defect
         n hmu v.1

section

variable (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 K)} → v ∈ S)

include hS in
/-- The finite-place product-formula calculation, stated directly for
the prime-ideal factors of the principal ideal `(n)`.
The hypothesis says exactly that `S` contains every finite place
dividing `n`; places added to `S` contribute the factor `1`. -/
theorem prod_absNorm_maxPowDividing_natCast :
    (∏ v : ↥S,
        Ideal.absNorm
          (v.1.maxPowDividing
            (Ideal.span {((n : ℕ) : 𝓞 K)}))) =
      (n : ℕ) ^ Module.finrank ℚ K := by
  classical
  let I :=
    Ideal.span {((n : ℕ) : 𝓞 K)}
  have hI : I ≠ 0 := by
    simp [I, n.ne_zero]
  let f : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => Ideal.absNorm (v.maxPowDividing I)
  have hsupport : Function.mulSupport f ⊆ S := by
    intro v hv
    apply hS v
    refine
      (Associates.count_ne_zero_iff_dvd
        hI v.irreducible).mp ?_
    intro hzero
    apply hv
    simp [f, IsDedekindDomain.HeightOneSpectrum.maxPowDividing,
      hzero]
  calc
    _ =
        ∏ v ∈ S, f v := by
      simpa [f, I] using Finset.prod_coe_sort S f
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v :=
      (finprod_eq_prod_of_mulSupport_subset f hsupport).symm
    _ =
        Ideal.absNorm
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            v.maxPowDividing I) := (Ideal.absNorm.map_finprod
              (Ideal.hasFiniteMulSupport hI)).symm
    _ = Ideal.absNorm I := by
      rw [Ideal.finprod_heightOneSpectrum_factorization hI]
    _ = (n : ℕ) ^ Module.finrank ℚ K := by
      change
        Ideal.absNorm
            (Ideal.span {(((n : ℕ) : ℕ) : 𝓞 K)}) =
          (n : ℕ) ^ Module.finrank ℚ K
      rw [Ideal.absNorm_span_natCast,
        NumberField.RingOfIntegers.rank]

include hS in
/-- Product of the actual finite-place power defects. -/
theorem prod_finitePlaceNthPowerDefect :
    (∏ v : ↥S,
        finitePlaceNthPowerDefect
          (K := K) n v.1) =
      (n : ℕ) ^ Module.finrank ℚ K := by
  calc
    (∏ v : ↥S,
        finitePlaceNthPowerDefect
           n v.1) =
        ∏ v : ↥S,
          Ideal.absNorm
            (v.1.maxPowDividing
              (Ideal.span
                {((n : ℕ) : 𝓞 K)})) := by
      apply Finset.prod_congr rfl
      intro v _
      exact
        finitePlaceNthPowerDefect_eq_absNorm_maxPowDividing
           n v.1
    _ = _ :=
      prod_absNorm_maxPowDividing_natCast
         n S hS

end

/-- The product of the archimedean local power indices.  Only real
places and an even exponent contribute a factor `2`. -/
theorem prod_infinitePlace_nthPowerIndex
    (n : ℕ+) :
    (∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) =
      if Even (n : ℕ) then
        2 ^ InfinitePlace.nrRealPlaces K
      else 1 := by
  classical
  by_cases hn : Even (n : ℕ)
  · rw [ite_eq_left hn]
    rw [InfinitePlace.prod_eq_prod_mul_prod]
    simp only [hn, and_true]
    have hr :
        (∏ w : {w : InfinitePlace K // w.IsReal},
            if w.1.IsReal then 2 else 1) =
          ∏ _w : {w : InfinitePlace K // w.IsReal}, 2 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [ite_eq_left w.2]
    have hc :
        (∏ w : {w : InfinitePlace K // w.IsComplex},
            if w.1.IsReal then 2 else 1) =
          ∏ _w : {w : InfinitePlace K // w.IsComplex}, 1 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [ite_eq_right
        (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)]
    rw [hr, hc]
    simp [InfinitePlace.nrRealPlaces]
  · simp [hn]

/-- The archimedean signature calculation used together with the finite
product formula.  If `K` contains a primitive `n`-th root with `n > 2`,
it has no real places; the remaining cases are `n = 1, 2`. -/
theorem prod_infinitePlace_nthPowerIndex_mul_natDegree
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
        (n : ℕ) ^ Module.finrank ℚ K =
      (n : ℕ) ^
        (2 * Fintype.card (InfinitePlace K)) := by
  classical
  have harch :=
    prod_infinitePlace_nthPowerIndex (K := K) n
  obtain ⟨ζ, hζ⟩ := hmu
  have hsignature :=
    InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  by_cases hlarge : 2 < (n : ℕ)
  · have hreal :=
      InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
        hlarge ((mem_primitiveRoots n.pos).mp hζ)
    rw [hreal, zero_add] at hsignature hplaces
    have hdegree :
        Module.finrank ℚ K =
          2 * Fintype.card (InfinitePlace K) := by
      omega
    rw [harch, hreal, hdegree]
    simp
  · have hnpos : 0 < (n : ℕ) := n.pos
    have hone_or_two :
        (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by
      omega
    rcases hone_or_two with hone | htwo
    · have hn : n = (1 : ℕ+) := Subtype.ext hone
      subst n
      rw [harch]
      simp
    · have hn : n = (2 : ℕ+) := Subtype.ext htwo
      subst n
      rw [harch]
      rw [ite_eq_left (by decide :
        Even (((2 : ℕ+) : ℕ)))]
      change
        2 ^ InfinitePlace.nrRealPlaces K *
            2 ^ Module.finrank ℚ K =
          2 ^ (2 * Fintype.card (InfinitePlace K))
      rw [← pow_add]
      congr 1
      omega

/-- The middle term of the supported exact sequence has cardinality
`n^(2s)`, where `s` is the number of infinite places plus the number of
finite places in `S`. -/
theorem card_supportedIdeleQuotient_eq_power_two_totalPlaceCard
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K)
              (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup
            (K := K) n S T) =
      (n : ℕ) ^
        (2 * totalPlaceCard (K := K) S) := by
  have hfinite :
      (∏ v : ↥S,
          (n : ℕ) *
            ((n : ℕ) *
              finitePlaceNthPowerDefect
                 n v.1)) =
        (n : ℕ) ^ (2 * S.card) *
          (n : ℕ) ^ Module.finrank ℚ K := by
    calc
      (∏ v : ↥S,
          (n : ℕ) *
            ((n : ℕ) *
              finitePlaceNthPowerDefect
                 n v.1)) =
          ∏ v : ↥S,
            (n : ℕ) ^ 2 *
              finitePlaceNthPowerDefect
                 n v.1 := by
        apply Finset.prod_congr rfl
        intro v _
        ring
      _ =
          (∏ _v : ↥S, (n : ℕ) ^ 2) *
            ∏ v : ↥S,
              finitePlaceNthPowerDefect
                 n v.1 := by
        rw [Finset.prod_mul_distrib]
      _ = _ := by
        rw [
          prod_finitePlaceNthPowerDefect
             n S hS]
        simp [pow_mul]
  rw [
    card_supportedIdeleQuotient_eq_localPowerIndexProduct
       n hmu S T,
    hfinite]
  calc
    _ =
        ((∏ w : InfinitePlace K,
            if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
          (n : ℕ) ^ Module.finrank ℚ K) *
            (n : ℕ) ^ (2 * S.card) := by
      ac_rfl
    _ =
        (n : ℕ) ^
            (2 * Fintype.card (InfinitePlace K)) *
          (n : ℕ) ^ (2 * S.card) := by
      rw [
        prod_infinitePlace_nthPowerIndex_mul_natDegree
           n hmu]
    _ =
        (n : ℕ) ^
          (2 * totalPlaceCard S) := by
      rw [← pow_add]
      congr 1
      unfold totalPlaceCard
      omega

end GlobalClassFieldTheory.ClassFieldAxiom

end
