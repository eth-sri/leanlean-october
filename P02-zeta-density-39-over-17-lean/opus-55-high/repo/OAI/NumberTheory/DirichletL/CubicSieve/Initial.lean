module
public import OAI.NumberTheory.DirichletL.CubicSieve.Poisson
public import OAI.NumberTheory.DirichletL.CubicSieve.Algebra
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CompletedGauss ConcretePrimeRowBridge ShortDraftHeckeBridge QuadraticInitialBound
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicFiniteRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 2

theorem cubicFiniteRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    cubicFiniteRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 2) z := by pf_217 cubicFiniteRow 2 actualSextic

def activeCubicExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 4 else 2

section
variable {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
include α P
theorem activeCubicExponent_nonprincipal (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (i : activeSupport S T) :
    actualSextic (P i.val) (hg i.val) ^ activeCubicExponent S T i ≠ 1 := by
  have h := cubicExponent_nonprincipal (P i.val) (hg i.val)
    (decide (i.val ∈ S \ T))
  simpa only [cubicExponent, activeCubicExponent, decide_eq_true_eq] using h

theorem cubicFiniteRow_pair_kernel
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α) (z : O) :
    star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
          (activeCubicExponent S T) z := by
  have h := congrArg (fun v : ℂ => v ^ 2) (finiteSquarefreeRow_pair_activeSupport P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 2 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hrow : finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeExponent S T) z ^ 2 =
      finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeCubicExponent S T) z := by
    unfold finiteSexticRow
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have h6 : actualSextic (P i.val) (hg i.val) ^ 6 = 1 :=
      (pow_mul _ 2 3).trans <|
        (congrArg (fun φ : MulChar (O ⧸ P i.val) ℂ => φ ^ 3)
          (canonicalSextic_pow_two (P i.val) (hg i.val))).trans <|
            (MulChar.ringHomComp_pow _ _ _).trans <|
              (congrArg (fun φ : MulChar (O ⧸ P i.val) O => φ.ringHomComp eisEmbedding)
                (cubicChar_pow_three (P i.val) (hg i.val))).trans
                  (MulChar.ringHomComp_one eisEmbedding)
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
    apply congrArg (fun χ : MulChar (O ⧸ P i.val) ℂ => χ (Ideal.Quotient.mk (P i.val) z))
    change (actualSextic (P i.val) (hg i.val) ^ activeExponent S T i) ^ 2 = _
    unfold activeExponent activeCubicExponent
    split_ifs
    · rw [← pow_mul, show (5 * 2 : ℕ) = 4 + 6 by decide, pow_add, h6, mul_one]
    · simp
  simpa only [mul_pow, ← star_pow, hm, hrow, cubicFiniteRow] using h

theorem cubic_gram_offdiagonal (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  pm_6187 cubicFiniteRow_pair_kernel
  exact canonical_masked_polya_vinogradov_of_nontrivial P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (activeCubicExponent S T) (activeCubicExponent_nonprincipal P hg S T) W M hM

theorem cubic_gram_offdiagonal_of_norm_le (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (cubic_gram_offdiagonal P hinj hg S T hne W M hM).trans
  pm_5831
end

section
variable {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, goodLambda ∉ P i)
include α P hg
theorem cubicFiniteRow_norm_le_one (S : Finset α) (z : O) :
    ‖cubicFiniteRow P hg S z‖ ≤ 1 := by
  pm_8455 cubicFiniteRow_eq_canonical finiteSexticRow_norm_le_one

theorem cubic_pair_summable (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
        have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
          simpa only [scaledRadialTest_apply] using
            actual_eisenstein_summable_norm (scaledRadialTest W M hM)
        apply Summable.of_norm
        apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
        intro z
        rw [norm_mul, norm_mul, norm_star]
        exact mul_le_of_le_one_left (norm_nonneg _)
          ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg T z)
            (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem cubic_gram_diagonal (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
          have hMp : 0 < M := by linarith
          have hs := (cubic_pair_summable P hg S S W M hMp).norm
          have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
            simpa only [scaledRadialTest_apply] using
              actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
          refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
            (radial_weight_lattice_bound W M hM))
          intro z
          rw [norm_mul, norm_mul, norm_star]
          exact mul_le_of_le_one_left (norm_nonneg _)
            ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg S z)
              (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
end

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

section
variable {α β : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M)
include α β P hg C support a W M hM
theorem cubic_mean_summable :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) := by pm_3015 cubic_pair_summable

theorem cubic_mean_expand :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
            let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
              ((star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
                W (‖eisEmbedding z‖ ^ 2 / M))
            have hf (n m : β) : Summable (f n m) :=
              (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left _
            have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
                (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ) =
                  ∑ n ∈ C, ∑ m ∈ C, f n m z := by
              rw [norm_sq_finite_sum]
              simp only [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              apply Finset.sum_congr rfl
              intro m hm
              dsimp [f]
              ring
            rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
            apply Finset.sum_congr rfl
            intro n hn
            rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
            apply Finset.sum_congr rfl
            intro m hm
            exact tsum_mul_left
end

section
variable {α β : Type*} [DecidableEq α] [DecidableEq β] (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β)) (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N) (a : β → ℂ)
include α β P hinj hg C support hsupp N hN hNorm a
theorem cubic_initial_mean_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  pm_3019
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    pm_1240 cubic_gram_diagonal
    · simp only [hnm, ite_false, zero_add]
      exact cubic_gram_offdiagonal_of_norm_le P hinj hg _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  pm_3018
  rw [cubic_mean_expand P hg C support a W M hMp]
  pm_3017

theorem cubic_initial_finite_bound (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  pm_7983 cubic_mean_summable
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      pm_3023
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := cubic_initial_mean_bound P hinj hg C support hsupp N hN hNorm
      a sieveCutoff M hM
end

theorem ideal_initial_cubic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := cubic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  pm_3024

end
end SevenEighths.CubicSieve

end OAI
