module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.CubicSieve.Algebra

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss ConcretePrimeRowBridge ShortDraftHeckeBridge QuadraticInitialBound
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicFiniteRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 2


def activeCubicExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 4 else 2

def cubicExponent (negative : Bool) : ℕ := if negative then 4 else 2

theorem cubicExponent_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (negative : Bool) :
    actualSextic P hg ^ cubicExponent negative ≠ 1 := by
  let χ := actualSextic P hg ^ 2
  have hχ : χ ≠ 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg]
    exact (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one P hg)
  have h3 : χ ^ 3 = 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg, MulChar.ringHomComp_pow, cubicChar_pow_three P hg, MulChar.ringHomComp_one]
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = χ ^ 2 * χ := by rw [h, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := h3
  cases negative with
  | false => simpa only [cubicExponent, Bool.false_eq_true, ite_false,
      ] using hχ
  | true =>
      have he : actualSextic P hg ^ 4 = χ ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      simpa only [cubicExponent, ite_true, he] using h2

theorem activeCubicExponent_nonprincipal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (i : activeSupport S T) :
    actualSextic (P i.val) (hg i.val) ^ activeCubicExponent S T i ≠ 1 := by
  simpa only [cubicExponent, decide_eq_true_eq, activeCubicExponent] using
    cubicExponent_nonprincipal (P i.val) (hg i.val) (decide (i.val ∈ S \ T))

theorem cubicFiniteRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
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

theorem cubic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [cubicFiniteRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov_of_nontrivial P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (activeCubicExponent S T) (activeCubicExponent_nonprincipal P hg S T) W M hM

theorem cubic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (cubic_gram_offdiagonal P hinj hg S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)


theorem ideal_initial_cubic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 :=
  ideal_initial_power_sieve 2 F hFpos hFgood hsq N hN hnorm a M hM R hR
    (by
      letI := primePool_maximal F hFpos
      intro S T hne hS hT
      exact cubic_gram_offdiagonal_of_norm_le Subtype.val
        Subtype.val_injective (primePool_good F hFgood) S T hne N (Nat.cast_nonneg _)
        hS hT sieveCutoff M (zero_lt_one.trans_le hM))

end
end SevenEighths.CubicSieve

end OAI
