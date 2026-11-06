module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CanonicalQuadraticSieve

section
open CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

def weightedRayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O)
    (v : m → ℝ) : Matrix n n ℂ :=
  fun j k => ∑ i, (v i : ℂ) *
    (if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
      star (quadraticRow (cols j) (primaryGenerator (rows i))) *
        quadraticRow (cols k) (primaryGenerator (rows i)) else 0)

end

section
open CompletedGauss FiniteSieveRestriction QuadraticSquarefreeKernel

def rayPairValue (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) : ℂ :=
  ∑ J : idealRange N, ∑ lengthScale : idealRange N,
    gcdTerm D (fun _ : Unit => I) (fun J : idealRange N => J.val)
      (sectorCoefficient (fun J : idealRange N => columnRay J.val) c a) () J lengthScale

theorem rayPairValue_eq (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) :
    rayPairValue N D c a I = ∑ J : idealRange N, ∑ lengthScale : idealRange N,
      if gcd J.val lengthScale.val = D ∧ columnRay J.val = c ∧ columnRay lengthScale.val = c then
        star (quadraticRow J.val (primaryGenerator I) * a J) *
          (quadraticRow lengthScale.val (primaryGenerator I) * a lengthScale) else 0 := by
  simpa only [rayPairValue, rayGcdBlock, gcdBlock, Fintype.sum_unique, gcdTerm] using
    rayGcdBlock_eq D c (fun _ : Unit => I) (fun J : idealRange N => J.val) a

end

open CompletedGauss FiniteSieveOperator

def highKernelShellRange (M K : ℝ) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => M / 2 < (Ideal.absNorm I : ℝ))

theorem exists_dyadic_shell (n lengthScale : ℕ) (hn : 1 ≤ n) (hL : (n : ℝ) ≤ (2 : ℝ) ^ lengthScale) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ (2 : ℝ) ^ j := by
  have hex : ∃ j : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ j := ⟨lengthScale, hL⟩
  let j := Nat.find hex
  have hj : (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ lengthScale := Nat.find_min' hex hL
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, hj⟩
  have hjfind : j = Nat.find hex := rfl
  rcases j with _ | j
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · have hprev : ¬ (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_min hex (by omega)
    have hp := lt_of_not_ge hprev
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp

end CanonicalQuadraticSieve

namespace QuadraticInitialBound

def annularSieveBump : ContDiffBump (3 / 4 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def annularSieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    annularSieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annularSieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem annularSieveCutoff_apply (t : ℝ) : annularSieveCutoff t = (annularSieveBump t : ℂ) := rfl

theorem annularSieveBump_eq_one {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) : annularSieveBump t = 1 := by
  apply annularSieveBump.one_of_mem_closedBall
  change dist t (3 / 4) ≤ 1 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

theorem annularSieveBump_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem annularSieveBump_zero_of_ge {t : ℝ} (ht : 5 / 4 ≤ t) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

@[simp] theorem annularSieveCutoff_zero : annularSieveCutoff 0 = 0 := by
  rw [annularSieveCutoff_apply, annularSieveBump_zero_of_le (by norm_num), Complex.ofReal_zero]

end QuadraticInitialBound

namespace CanonicalQuadraticSieve

section
open CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def annularHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.annularSieveBump ((Ideal.absNorm I : ℝ) / M)

def annularHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2

def annularRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val) a

end


open CompletedGauss FiniteSieveRestriction QuadraticSquarefreeKernel

theorem annularHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2 * M ≤ (Ideal.absNorm I : ℝ)) : annularHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ) / M := (le_div_iff₀ hM).mpr (by linarith)
  exact QuadraticInitialBound.annularSieveBump_zero_of_ge (by linarith)

theorem annularRayGcdBlock_eq_finite (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : highKernelRange (2 * M) K, (annularHighWeight M I.val : ℂ) * rayPairValue N D c a I.val := by
  rfl

theorem annularRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.annularSieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by
  rw [annularRayGcdBlock_eq_finite,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => (annularHighWeight M I : ℂ) * rayPairValue N D c a I)]
  symm
  rw [tsum_eq_sum (s := highKernelRange (2 * M) K) (fun I hI => ?_)]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
      have h := mem_highKernelRange.mp hI
      exact ⟨h.1, h.2.2⟩
    rw [ite_eq_left hp, QuadraticInitialBound.annularSieveCutoff_apply]
    rfl
  · by_cases hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ)
    · have hn : 2 * M < (Ideal.absNorm I : ℝ) := by
        by_contra hh
        exact hI (mem_highKernelRange.mpr ⟨hp.1, le_of_not_gt hh, hp.2⟩)
      rw [ite_eq_left hp, QuadraticInitialBound.annularSieveCutoff_apply]
      change (annularHighWeight M I : ℂ) * _ = 0
      rw [annularHighWeight_eq_zero M hM I hn.le]
      simp
    · exact ite_eq_right hp
