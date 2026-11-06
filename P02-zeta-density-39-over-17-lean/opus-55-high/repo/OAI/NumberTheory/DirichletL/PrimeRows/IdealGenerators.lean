module
public import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical


namespace ConcretePrimeRowBridge

section
variable (J : Ideal O) (hJ : J ≠ ⊥)
include J hJ
theorem idealGenerator_ne_zero :
    idealGenerator J ≠ 0 := by
  intro h
  apply hJ
  rw [← span_idealGenerator J, h]
  simp

theorem tsum_ideal_eq_tsum_generator
    (f : O → ℂ) :
    (∑' u : O, if u ∈ J then f u else 0) =
      ∑' z : O, f (idealGenerator J * z) := by
  let d := idealGenerator J
  have hd : d ≠ 0 := idealGenerator_ne_zero J hJ
  let F : O → ℂ := fun u => if u ∈ J then f u else 0
  have hrange : Function.support F ⊆ Set.range (fun z : O => d * z) := by
    intro u hu
    have huJ : u ∈ J := by
      by_contra hn
      exact hu (by simp [F, hn])
    rw [← span_idealGenerator J, Ideal.mem_span_singleton] at huJ
    obtain ⟨z, hz⟩ := huJ
    exact ⟨z, hz.symm⟩
  have ht := (mul_right_injective₀ hd).tsum_eq hrange
  calc
    (∑' u : O, if u ∈ J then f u else 0) = ∑' z : O, F (d * z) := ht.symm
    _ = ∑' z : O, f (d * z) := by
      apply tsum_congr
      intro z
      have hz : d * z ∈ J := by
        rw [← span_idealGenerator J, Ideal.mem_span_singleton]
        exact ⟨z, rfl⟩
      simp only [F, ite_eq_left hz]
end

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem tsum_rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι)
    (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        ∑' u : O, if ∀ i ∈ E, u ∈ P i then f u else 0 := by
  have hterm (u : O) : rowCoprimeMask P S u * f u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0) := by
    pm_3419 rowCoprimeMask_subsets Finset.sum_mul E hE
    pm_6484
  have hsum (E : Finset ι) :
      Summable (fun u : O => (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0)) := by
    have hi := hf.indicator {u : O | ∀ i ∈ E, u ∈ P i}
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hi.mul_left ((-1 : ℂ) ^ E.card)
  pm_7096 E
  intro E hE
  exact tsum_mul_left

noncomputable def primeSubsetGenerator {ι : Type*}
    (P : ι → Ideal O) (E : Finset ι) : O :=
  ConcretePrimeRowBridge.idealGenerator (∏ i ∈ E, P i)

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  pm_1160

theorem tsum_rowCoprimeMask_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          ∑' z : O, f (primeSubsetGenerator P E * z) := by
  rw [tsum_rowCoprimeMask_subsets P S f hf]
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  pm_7229
  congr 1
  have hJ : (∏ i ∈ E, P i) ≠ ⊥ := by
    pm_1160
  calc
    _ = ∑' u : O, if u ∈ (∏ i ∈ E, P i) then f u else 0 := by
      apply tsum_congr
      intro u
      rw [mem_prime_product_iff P hinj E u]
      pm_6484
    _ = _ := ConcretePrimeRowBridge.tsum_ideal_eq_tsum_generator _ hJ f

open ConcreteTraceCRT

theorem tsum_masked_radial_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) (S : Finset ι)
    (r : O → ℂ) (hr : ∀ a b, r (a * b) = r a * r b)
    (W : ℝ → ℂ) (scale : ℝ)
    (hsum : Summable (fun u : O => r u * W (‖eisEmbedding u‖ ^ 2 / scale))) :
    (∑' u : O, rowCoprimeMask P S u * r u * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          r (primeSubsetGenerator P E) *
          ∑' z : O, r z *
            W (‖eisEmbedding z‖ ^ 2 / (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  calc
    _ = ∑' u : O, rowCoprimeMask P S u *
        (r u * W (‖eisEmbedding u‖ ^ 2 / scale)) := by
      apply tsum_congr
      intro u
      ring
    _ = _ := by
      rw [tsum_rowCoprimeMask_dilations P hinj S _ hsum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [mul_assoc]
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      pm_265 hr map_mul norm_mul mul_pow div_div_eq_mul_div
      ring_nf

open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem primeSubset_reducedScale_pos {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset α)
    {scale : ℝ} (hscale : 0 < scale) :
    0 < scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 := by
  exact div_pos hscale (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))

section
variable {α ι : Type*} [DecidableEq α] [Fintype ι] (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal] (hcop : Pairwise (Function.onFun IsCoprime Q)) (hgood : ∀ i, lambda ∉ Q i)
include α ι P hinj S Q hcop hgood
theorem canonical_masked_radial_dilations (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j (primeSubsetGenerator P E) *
          ∑' z : O, finiteSexticRow Q hgood j z *
            W (‖eisEmbedding z‖ ^ 2 /
              (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  exact tsum_masked_radial_dilations P hinj S (finiteSexticRow Q hgood j)
    (finiteSexticRow_mul Q hgood j) W scale
    (finiteSexticRow_radial_summable Q hcop hgood j W scale hscale)

theorem canonical_masked_radial_poisson
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator P E
        let reducedScale := scale / ‖eisEmbedding d‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j d *
          ((reducedScale : ℂ) * canonicalNormalizedGauss Q hcop hgood j /
            (‖eisEmbedding c‖ : ℂ)) *
          ∑' h : O, star (finiteSexticRow Q hgood j h) *
            paperRadialFourier W
              (reducedScale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  dsimp only
  rw [canonical_masked_radial_dilations P hinj S Q hcop hgood j W scale hscale]
  apply Finset.sum_congr rfl
  intro E hE
  rw [canonical_radial_poisson_normalized Q hcop hgood hchar j hj0 hj6 W
    (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hscale)]
  ring

theorem canonical_masked_radial_poisson_collected
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss Q hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator P E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
            finiteSexticRow Q hgood j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
            ∑' h : O, star (finiteSexticRow Q hgood j h) *
              paperRadialFourier W
                (scale * ‖eisEmbedding h‖ ^ 2 /
                  (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2)) := by
  dsimp only
  rw [canonical_masked_radial_poisson P hinj S Q hcop hgood hchar j hj0 hj6 W scale hscale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  have harg (h : O) :
      scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [harg]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
end

end ActualEisensteinCubic

namespace GeneralPrimitiveTrace
open Complex EisensteinEmbedding ConcreteTraceCRT
open scoped ComplexConjugate

theorem complex_exp_trace_integer {t : ℂ}
    (ht : Complex.exp (2 * Real.pi * Complex.I * t) = 1) :
    ∃ n : ℤ, t = n := by
  pm_6972
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (mul_ne_zero
      (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)) Complex.I_ne_zero
  pm_3518

theorem phase_integer {z : ℂ}
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1) :
    ∃ n : ℤ, z / eisLam + conj (z / eisLam) = n :=
  complex_exp_trace_integer hz

theorem omega_conj : conj omega3 = omega3 ^ 2 := by
  pm_3519

theorem reconstruction (z : ℂ) :
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := by pf_194

theorem in_coordinate_lattice_of_two_phases (z : ℂ)
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by pf_133

theorem eisTraceModChar_breveE_primitive (c : ActualEisensteinCubic.O) (hc : c ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc).IsPrimitive := by
  intro a ha hshift
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  let z : ℂ := eisEmbedding x / eisEmbedding c
  have hci : eisEmbedding c ≠ 0 := eisEmbedding_ne_zero hc
  have hbase : ∀ y : ActualEisensteinCubic.O,
      ShortDraftTrace.breveE (eisEmbedding (x * y) / (eisEmbedding c * eisLam)) = 1 := by
    intro y
    have hp := congrArg (fun f : AddChar (ActualEisensteinCubic.O ⧸ Ideal.span {c}) ℂ =>
      f (Ideal.Quotient.mk (Ideal.span {c}) y)) hshift
    simpa only [AddChar.mulShift_apply, ← map_mul, eisTraceModChar,
      IdealGaussCRT.traceModChar_mk, AddChar.one_apply] using hp
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert hbase 1 using 1
    simp only [mul_one]
    dsimp [z]
    ring_nf
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert hbase pb.gen using 1
    rw [map_mul, show eisEmbedding pb.gen = omega3 from embedding_gen omega3 omega3_sq]
    dsimp [z]
    ring_nf
  pm_5410 hiq eisEmbedding
  have hcq : c * q = x := by
    apply eisEmbedding_injective
    rw [map_mul, hiq]
    dsimp [z]
    field_simp
  apply ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨q, hcq.symm⟩

end GeneralPrimitiveTrace

namespace IdealGaussCRT

section
variable {ι T : Type*} [Fintype ι] (R : ι → Type*) [CommRing T]
include ι T R
theorem coordinateAddChar_isPrimitive [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (hψ : ψ.IsPrimitive) (i : ι) :
    (coordinateAddChar R e ψ i).IsPrimitive := by
  classical
  intro a ha hshift
  let b : T := e.symm (Pi.single i a)
  have hb : b ≠ 0 := by
    intro hz
    have hh := congrArg (fun z : T => e z i) hz
    exact ha (by simpa [b] using hh)
  apply hψ hb
  ext x
  change ψ (b * x) = 1
  have hx := congrArg (fun φ : AddChar (R i) ℂ => φ (e x i)) hshift
  change ψ (e.symm (Pi.single i (a * e x i))) = 1 at hx
  have hvec : Pi.single i a * e x = Pi.single i (a * e x i) := by
    funext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  have hprod : b * x = e.symm (Pi.single i (a * e x i)) := by
    apply e.injective
    rw [map_mul]
    simp only [b, e.apply_symm_apply]
    exact hvec
  rw [hprod]
  exact hx

theorem norm_gauss_finite_crt_sq [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1)
    (hψ : ∀ i, (coordinateAddChar R e ψ i).IsPrimitive) :
    ‖∑ x : T, (∏ i, χ i (e x i)) * ψ x‖ ^ 2 = (Fintype.card T : ℝ) := by
  pm_3246
  rw [hbase, norm_prod, ← Finset.prod_pow]
  have hlocal (i : ι) : ‖gaussSum (χ i) (coordinateAddChar R e ψ i)‖ ^ 2 =
      (Fintype.card (R i) : ℝ) := by
    rw [ShortDraftGauss.norm_gaussSum_eq_sqrt_card (χ i)
      (coordinateAddChar R e ψ i) (hχ i) (hψ i), Real.sq_sqrt (by positivity)]
  simp_rw [hlocal]
  rw [Fintype.card_congr e.toEquiv, Fintype.card_pi, Nat.cast_prod]
end

end IdealGaussCRT

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

section
variable {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hcop : Pairwise (Function.onFun IsCoprime P)) (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
include ι P hcop hgood hchar j hj0 hj6
theorem norm_canonicalGaussSum :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  pm_3409
  pm_3406
  pm_3407
  pm_3403
  pm_3451
  pm_3452 canonicalSextic
  have hχ : ∀ i, χ i ≠ 1 := fun i =>
    canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)
  pm_3450

theorem norm_canonicalNormalizedGauss :
    ‖canonicalNormalizedGauss P hcop hgood j‖ = 1 := by
  pm_5675
  rw [canonicalNormalizedGauss, norm_div,
    norm_canonicalGaussSum P hcop hgood hchar j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]
end

theorem finiteSquarefreeRow_norm_le_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) :
    ‖finiteSquarefreeRow P hgood S u‖ ≤ 1 := by
  have hpair := finiteSquarefreeRow_self_pair P hgood S u
  have hmask : ‖rowCoprimeMask P S u‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hsq : ‖finiteSquarefreeRow P hgood S u‖ ^ 2 ≤ 1 := by
    calc
      _ = ‖star (finiteSquarefreeRow P hgood S u) *
          finiteSquarefreeRow P hgood S u‖ := by rw [norm_mul, norm_star, pow_two]
      _ = ‖rowCoprimeMask P S u‖ := congrArg norm hpair
      _ ≤ 1 := hmask
  nlinarith [norm_nonneg (finiteSquarefreeRow P hgood S u)]

theorem finiteSquarefreeRow_pair_radial_summable
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O =>
      (star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u) *
        W (‖eisEmbedding u‖ ^ 2 / scale)) := by
  pm_3453 hW u scale hscale
  pm_5055 u hW
  simp only [norm_mul, norm_star]
  calc
    ‖finiteSquarefreeRow P hgood S u‖ * ‖finiteSquarefreeRow P hgood T u‖ *
        ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖ ≤
      1 * 1 * ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖ := by
        gcongr
        · exact finiteSquarefreeRow_norm_le_one P hgood S u
        · exact finiteSquarefreeRow_norm_le_one P hgood T u
    _ = _ := by ring

private theorem norm_sq_finite_row_sum {β : Type*}
    (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  pm_3454

theorem finiteSquarefreeRow_smoothed_mean_square_summable
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (C : Finset β) (support : β → Finset ι) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O => W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖∑ n ∈ C, a n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn =>
    summable_sum (s := C) (fun m hm =>
      (finiteSquarefreeRow_pair_radial_summable P hgood (support n) (support m)
        W scale hscale).mul_left (star (a n) * a m)))
  apply hs.congr
  intro u
  rw [norm_sq_finite_row_sum]
  simp only [Finset.mul_sum]
  pm_3397 n hn m hm
  ring

end ActualEisensteinCubic

end

end OAI
