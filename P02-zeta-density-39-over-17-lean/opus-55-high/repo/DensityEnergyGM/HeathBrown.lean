module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Order.Chebyshev
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalPowering
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesDefinitions
public import GuthMaynard.NativeSource.GuthMaynard.Separated
public import GuthMaynard.NativeSource.GuthMaynard.MeanValueProof
public import DensityEnergyGM.LargeValuesLocalization
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Finset
open scoped ComplexConjugate

namespace GuthMaynard.NativeMoment

/-!
# Heath--Brown difference-set mean square

This file begins the native proof of Heath--Brown's 1979 large-values
estimate in the exact finite language needed by Guth--Maynard Proposition
6.1.  The definitions below retain the two ordinate variables until after
the finite expansion.  This makes the source majorant principle a purely
algebraic theorem, independent of the later analytic estimates.
-/

/-- The negative-sign phase used in Heath--Brown's difference-set mean
square.  Positivity of the integer is needed only when this phase is related
to a one-variable Dirichlet polynomial, not for the finite algebra below. -/
noncomputable def heathBrownPhase (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) ^ (-t * I)

/-- The two-ordinate polynomial before replacing the pair by its difference.
This is the form whose square expands into a positive majorant kernel. -/
noncomputable def heathBrownDifferencePolynomial (s : Finset ℕ)
    (a : ℕ → ℂ) (t u : ℝ) : ℂ :=
  ∑ n ∈ s, a n * heathBrownPhase n t * star (heathBrownPhase n u)

/-- Heath--Brown's finite mean square over the ordered difference set. -/
noncomputable def heathBrownDifferenceMoment (s : Finset ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownDifferencePolynomial s a t u‖ ^ 2

/-- The positive kernel which occurs after expanding the difference-set
mean square and interchanging its four finite sums. -/
noncomputable def heathBrownMajorantKernel (W : Finset ℝ)
    (n m : ℕ) : ℝ :=
  ‖∑ t ∈ W, star (heathBrownPhase n t) * heathBrownPhase m t‖ ^ 2

/-- The exact source-level Heath--Brown theorem recalled immediately before
Guth--Maynard equation (6.3).  The coefficient-one reduction below is one
input to this statement; the analytic estimate itself is not postulated. -/
def HeathBrownDifferenceSetMeanSquare : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly N a (t - u)‖ ^ 2) ≤
          C * T ^ ε *
            (((W.card : ℝ) ^ 2 * N) +
              ((W.card : ℝ) * N ^ 2) +
              ((W.card : ℝ) ^ (5 / 4 : ℝ) *
                T ^ (1 / 2 : ℝ) * N))

/-- Strictly narrower coefficient-one analytic core of Heath--Brown's
mean-square theorem.  The positive-kernel majorant proves that this core is
enough for arbitrary unit-bounded coefficients. -/
def HeathBrownCoefficientOneMeanSquare : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < N → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) ≤
          C * T ^ ε *
            (((W.card : ℝ) ^ 2 * N) +
              ((W.card : ℝ) * N ^ 2) +
              ((W.card : ℝ) ^ (5 / 4 : ℝ) *
                T ^ (1 / 2 : ℝ) * N))

/-- The critical-line coefficient used in the Jutila--Heath--Brown
second moment `S(N)`: on the source interval it is exactly `n⁻¹ᐟ²`. -/
noncomputable def heathBrownHalfWeight (n : ℕ) : ℝ :=
  1 / Real.sqrt n

/-- Jutila's weighted ordered-difference moment `S(N)`, in the exact
positive-sign and endpoint convention used by this project. -/
noncomputable def heathBrownWeightedMoment (N : ℕ)
    (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖sourceDirichletPoly N
      (fun n => (heathBrownHalfWeight n : ℂ)) (t - u)‖ ^ 2

/-- The `2k`-th ordered-difference moment appearing after Hölder in
Heath--Brown's powering lemma. -/
noncomputable def heathBrownWeightedPowerMoment (N k : ℕ)
    (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖sourceDirichletPoly N
      (fun n => (heathBrownHalfWeight n : ℂ)) (t - u)‖ ^ (2 * k)

/-- The weighted Jutila--Heath--Brown second-moment theorem.  Multiplying
this statement by the exact factor `2N` gives the coefficient-one source
theorem, while its three summands correspond verbatim to the three cases
of Montgomery--Vaughan Lemma 29.10. -/
def HeathBrownWeightedMeanSquare : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        0 < N → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownWeightedMoment N W ≤
          C * T ^ ε *
            (((W.card : ℝ) ^ 2) +
              ((W.card : ℝ) * N) +
              ((W.card : ℝ) ^ (5 / 4 : ℝ) *
                T ^ (1 / 2 : ℝ)))

/-- Auxiliary-factor/source-index pairs used in the exact product
collection of Montgomery--Vaughan Lemma 29.7. -/
def heathBrownTransferTuples (P : Finset ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  P ×ˢ dyadicInterval N

/-- All products `p*n` arising from the auxiliary and source intervals. -/
def heathBrownTransferSupport (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (heathBrownTransferTuples P N).image (fun x => x.1 * x.2)

/-- The grouped nonnegative critical-line coefficient at a product `l`.
It is the literal sum of `(pn)^{-1/2}` over all representations `pn=l`. -/
noncomputable def heathBrownTransferCoeff
    (P : Finset ℕ) (N l : ℕ) : ℝ :=
  ∑ x ∈ (heathBrownTransferTuples P N).filter (fun x => x.1 * x.2 = l),
    heathBrownHalfWeight (x.1 * x.2)

/-- The auxiliary dyadic interval used in the transfer principle. -/
def heathBrownTransferAuxiliary (J : ℕ) : Finset ℕ :=
  Finset.Ioc J (2 * J)

/-- The ungrouped auxiliary-times-source difference polynomial. -/
noncomputable def heathBrownTransferredDifferencePolynomial
    (P : Finset ℕ) (N : ℕ) (t u : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ n ∈ dyadicInterval N,
    (heathBrownHalfWeight (p * n) : ℂ) *
      heathBrownPhase (p * n) t * star (heathBrownPhase (p * n) u)

/-- The ordered-pair second moment of the ungrouped transferred polynomial. -/
noncomputable def heathBrownTransferredDifferenceMoment
    (P : Finset ℕ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖heathBrownTransferredDifferencePolynomial P N t u‖ ^ 2

/-- The positive fourfold kernel obtained after multiplying the critical-line
block by a finite auxiliary Dirichlet polynomial.  Keeping the prime/factor
indices ungrouped makes the diagonal `p = q` in Montgomery--Vaughan Lemma
29.7 literal; grouping equal products is performed by a later bridge. -/
noncomputable def heathBrownTransferredKernelMoment
    (P : Finset ℕ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    ∑ n ∈ dyadicInterval N, ∑ m ∈ dyadicInterval N,
      heathBrownHalfWeight (p * n) * heathBrownHalfWeight (q * m) *
        heathBrownMajorantKernel W (p * n) (q * m)

theorem heathBrownDifferenceMoment_nonneg (s : Finset ℕ)
    (W : Finset ℝ) (a : ℕ → ℂ) :
    0 ≤ heathBrownDifferenceMoment s W a := by
  unfold heathBrownDifferenceMoment
  positivity

theorem heathBrownMajorantKernel_nonneg (W : Finset ℝ) (n m : ℕ) :
    0 ≤ heathBrownMajorantKernel W n m := by
  unfold heathBrownMajorantKernel
  positivity

/-- The exact Hölder step in Heath--Brown's powering lemma (Montgomery--
Vaughan Lemma 29.9).  It is stated on the ordered pair set, so the cardinal
factor is literally `(|W|²)^(k-1)`. -/
theorem heathBrownWeightedMoment_pow_le
    (N k : ℕ) (W : Finset ℝ) (hk : 0 < k) :
    heathBrownWeightedMoment N W ^ k ≤
      ((W.card : ℝ) ^ 2) ^ (k - 1) *
        heathBrownWeightedPowerMoment N k W := by
  let f : ℝ × ℝ → ℝ := fun p =>
    ‖sourceDirichletPoly N
      (fun n => (heathBrownHalfWeight n : ℂ)) (p.1 - p.2)‖ ^ 2
  have h := pow_sum_le_card_mul_sum_pow
    (s := W.product W) (f := f)
    (by aesop) (k - 1)
  pm_4077
  have hPower :
      (∑ t ∈ W, ∑ u ∈ W,
          (‖sourceDirichletPoly N
            (fun n => (heathBrownHalfWeight n : ℂ)) (t - u)‖ ^ 2) ^ k) =
        heathBrownWeightedPowerMoment N k W := by
    unfold heathBrownWeightedPowerMoment
    pm_90 Finset.sum_congr t ht u hu
    rw [← pow_mul]
  pm_4078
  aesop

/-- On a positive integer, the real Heath--Brown weight and the positive
imaginary phase combine to the critical-line monomial.  This is the exact
normalization needed to feed the existing finite-power expansion. -/
theorem heathBrownHalfWeight_mul_phase_eq_cpow
    (n : ℕ) (t : ℝ) (hn : 0 < n) :
    (heathBrownHalfWeight n : ℂ) * (n : ℂ) ^ (t * I) =
      (n : ℂ) ^ (-((1 / 2 : ℂ) - (t : ℂ) * I)) := by
  have hw : heathBrownHalfWeight n =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    unfold heathBrownHalfWeight
    rw [Real.sqrt_eq_rpow, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  pm_8019 hw
  rw [← Complex.cpow_add _ _ (by aesop)]
  congr 2
  push_cast
  ring

/-- The weighted source polynomial is literally the first finite power of
the coefficient-one critical-line polynomial. -/
theorem sourceDirichletPoly_halfWeight_eq_finitePowPoly
    (N : ℕ) (t : ℝ) :
    sourceDirichletPoly N
        (fun n => (heathBrownHalfWeight n : ℂ)) t =
      finitePowPoly N 1 (fun _ => (1 : ℂ))
        ((1 / 2 : ℂ) - (t : ℂ) * I) := by
  unfold sourceDirichletPoly finitePowPoly dyadicInterval
  rw [pow_one]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [one_mul]
  exact heathBrownHalfWeight_mul_phase_eq_cpow n t (by omega)

/-- The `k`-th power of the weighted critical-line block is the project's
generic finite-power polynomial with coefficient one. -/
theorem sourceDirichletPoly_halfWeight_pow_eq_finitePowPoly
    (N k : ℕ) (t : ℝ) :
    (sourceDirichletPoly N
        (fun n => (heathBrownHalfWeight n : ℂ)) t) ^ k =
      finitePowPoly N k (fun _ => (1 : ℂ))
        ((1 / 2 : ℂ) - (t : ℂ) * I) := by
  rw [sourceDirichletPoly_halfWeight_eq_finitePowPoly]
  simp [finitePowPoly]

theorem heathBrown_poweredBlock_subset
    (N k r m : ℕ) (hr : r < k)
    (hm : m ∈ Ioc (2 ^ r * N ^ k) (2 * (2 ^ r * N ^ k))) :
    m ∈ Ioc (N ^ k) (2 ^ k * N ^ k) := by
  rw [Finset.mem_Ioc] at hm ⊢
  constructor
  · exact lt_of_le_of_lt
      (Nat.le_mul_of_pos_left _ (pow_pos (by omega) r)) hm.1
  · have hrSucc : r + 1 ≤ k := by omega
    have hPow : 2 ^ (r + 1) ≤ (2 : ℕ) ^ k :=
      pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hrSucc
    calc
      m ≤ 2 * (2 ^ r * N ^ k) := hm.2
      _ = 2 ^ (r + 1) * N ^ k := by grind
      _ ≤ 2 ^ k * N ^ k := Nat.mul_le_mul_right _ hPow

/-- Reversing the ordinate changes the negative-sign polynomial into the
source positive-sign convention without changing coefficients. -/
theorem dirichletPoly_neg_eq_sourceDirichletPoly
    (M : ℕ) (a : ℕ → ℂ) (y : ℝ) :
    dirichletPoly M a (-y) = sourceDirichletPoly M a y := by
  unfold dirichletPoly sourceDirichletPoly
  pm_8456 n hn

/-- For fixed `u`, translate the difference ordinates `t-u` into the base
interval `[0,2T]` on which the Montgomery mean-value theorem is stated. -/
noncomputable def heathBrownDifferenceTranslateSet
    (T u : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun t => t - u + T)

theorem heathBrownDifferenceTranslateSet_separated
    (T u : ℝ) (W : Finset ℝ) (hSep : IsSeparated 1 W) :
    IsSeparated 1 (heathBrownDifferenceTranslateSet T u W) := by
  pm_874 heathBrownDifferenceTranslateSet
  have hxy' : x' ≠ y' := by
    intro h
    subst y'
    grind
  have hd : dist (x' - u + T) (y' - u + T) = dist x' y' := by
    simp only [Real.dist_eq]
    congr 1
    ring_nf
  rw [hd]
  aesop

theorem heathBrownDifferenceTranslateSet_mem_base
    {T u : ℝ} {W : Finset ℝ}
    (hBase : InBaseInterval T W) (hu : u ∈ W) :
    InBaseInterval (2 * T) (heathBrownDifferenceTranslateSet T u W) := by
  intro x hx
  rw [heathBrownDifferenceTranslateSet, Finset.mem_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  pm_268 htBounds hBase t ht huBounds u hu
  rw [Set.mem_Icc] at htBounds huBounds ⊢
  grind

section
variable (N : ℕ)
include N
/-- Exact phase identity used before applying Montgomery mean value on the
translated difference set. -/
theorem dirichletPoly_difference_eq_translated (a : ℕ → ℂ) (T t u : ℝ) :
    dirichletPoly N a (t - u) =
      dirichletPoly N (phaseShiftCoeffs (-T) a) (t - u + T) := by
  have h := dirichletPoly_translate N a (-T) (t - u + T)
  convert h using 1
  ring_nf

/-- Reindex one row of the ordered difference moment onto `[0,2T]`. -/
theorem sum_difference_eq_sum_differenceTranslateSet (a : ℕ → ℂ) (T u : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ‖dirichletPoly N a (t - u)‖ ^ 2) =
      ∑ x ∈ heathBrownDifferenceTranslateSet T u W,
        ‖dirichletPoly N (phaseShiftCoeffs (-T) a) x‖ ^ 2 := by
  unfold heathBrownDifferenceTranslateSet
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [dirichletPoly_difference_eq_translated]
  · intro x hx y hy hxy
    linarith

/-- Direct Montgomery mean value on every row of the ordered difference
set.  This is the elementary `R(T+N)` bound for the weighted moments; the
Heath--Brown powering and reflection steps improve its `RT` term. -/
theorem sourceDirichletPoly_orderedDifference_meanValue (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N a (t - u)‖ ^ 2) ≤
      (3 * (2 + 2 * (5 * Real.pi + 1))) * (W.card : ℝ) *
        (2 * T + (N : ℝ)) *
          ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := by
  let a' : ℕ → ℂ := conjugateCoeffs a
  pm_6620 C
  have hRow : ∀ u ∈ W,
      (∑ t ∈ W, ‖dirichletPoly N a' (t - u)‖ ^ 2) ≤
        C * (2 * T + (N : ℝ)) *
          ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := by
    intro u hu
    rw [sum_difference_eq_sum_differenceTranslateSet N a' T u W]
    have hMV := montgomery_mean_value_estimate N (2 * T)
      (heathBrownDifferenceTranslateSet T u W)
      (phaseShiftCoeffs (-T) a') hN (by linarith)
      (heathBrownDifferenceTranslateSet_separated T u W hSep)
      (heathBrownDifferenceTranslateSet_mem_base hBase hu)
    calc
      (∑ x ∈ heathBrownDifferenceTranslateSet T u W,
          ‖dirichletPoly N (phaseShiftCoeffs (-T) a') x‖ ^ 2) ≤
          C * (2 * T + (N : ℝ)) *
            ∑ n ∈ Ioc N (2 * N),
              ‖phaseShiftCoeffs (-T) a' n‖ ^ 2 := by
        simpa only [dirichletPoly, dyadicInterval, C] using hMV
      _ = C * (2 * T + (N : ℝ)) *
          ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := by
        pm_739 n hn norm_phaseShiftCoeffs
        change ‖conjugateCoeffs a n‖ ^ 2 = ‖a n‖ ^ 2
        rw [norm_conjugateCoeffs]
  have hSign : ∀ y : ℝ,
      ‖sourceDirichletPoly N a y‖ = ‖dirichletPoly N a' y‖ := by
    intro y
    have h := norm_sourceDirichletPoly_conjugateCoeffs N a' y
    have hcc : conjugateCoeffs a' = a := by
      funext n
      simp only [a', conjugateCoeffs, star_star]
    rw [hcc] at h
    exact h
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N a (t - u)‖ ^ 2) =
        ∑ t ∈ W, ∑ u ∈ W,
          ‖dirichletPoly N a' (t - u)‖ ^ 2 := by
      pm_90 Finset.sum_congr t ht u hu
      rw [hSign]
    _ = ∑ u ∈ W, ∑ t ∈ W,
          ‖dirichletPoly N a' (t - u)‖ ^ 2 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ u ∈ W,
        C * (2 * T + (N : ℝ)) *
          ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := by
      exact Finset.sum_le_sum hRow
    _ = (3 * (2 + 2 * (5 * Real.pi + 1))) * (W.card : ℝ) *
        (2 * T + (N : ℝ)) *
          ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := by
      simp only [sum_const, nsmul_eq_mul, C]
      ring

/-- The square-sum of `n⁻¹ᐟ²` over `(N,2N]` is at most one.  This
elementary normalization is what removes the polynomial length from the
direct ordered-difference mean-value bound. -/
theorem sum_heathBrownHalfWeight_sq_le_one (hN : 0 < N) :
    (∑ n ∈ Ioc N (2 * N), ‖(heathBrownHalfWeight n : ℂ)‖ ^ 2) ≤ 1 := by
  have hTerm : ∀ n ∈ Ioc N (2 * N),
      ‖(heathBrownHalfWeight n : ℂ)‖ ^ 2 ≤ 1 / (N : ℝ) := by
    intro n hn
    have hnBounds := Finset.mem_Ioc.mp hn
    have hnPosNat : 0 < n := by omega
    pm_74 hnPos n hnPosNat
    pm_74 hNPos N hN
    pm_6504
    have hInv : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by
      exact one_div_le_one_div_of_le hNPos hNle
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by unfold heathBrownHalfWeight; positivity), heathBrownHalfWeight,
      div_pow, one_pow, Real.sq_sqrt hnPos.le]
    exact hInv
  calc
    (∑ n ∈ Ioc N (2 * N), ‖(heathBrownHalfWeight n : ℂ)‖ ^ 2) ≤
        ∑ _n ∈ Ioc N (2 * N), 1 / (N : ℝ) :=
      Finset.sum_le_sum hTerm
    _ = (N : ℝ) * (1 / (N : ℝ)) := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Ioc]
      rw [show 2 * N - N = N by omega]
    _ = 1 := by field_simp

/-- The direct (unreflected) weighted ordered-difference estimate.  This is
the base case inserted into Heath--Brown's powering/reflection recurrence. -/
theorem heathBrownWeightedMoment_direct_meanValue (T : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W) :
    heathBrownWeightedMoment N W ≤
      (3 * (2 + 2 * (5 * Real.pi + 1))) * (W.card : ℝ) *
        (2 * T + (N : ℝ)) := by
  have hMV := sourceDirichletPoly_orderedDifference_meanValue N T W
    (fun n => (heathBrownHalfWeight n : ℂ)) hN hT hSep hBase
  have hL2 := sum_heathBrownHalfWeight_sq_le_one N hN
  have hFactor : 0 ≤
      (3 * (2 + 2 * (5 * Real.pi + 1))) * (W.card : ℝ) *
        (2 * T + (N : ℝ)) := by positivity
  calc
    heathBrownWeightedMoment N W ≤
        (3 * (2 + 2 * (5 * Real.pi + 1))) * (W.card : ℝ) *
          (2 * T + (N : ℝ)) *
            ∑ n ∈ Ioc N (2 * N),
              ‖(heathBrownHalfWeight n : ℂ)‖ ^ 2 := by
      simpa only [heathBrownWeightedMoment] using hMV
    _ ≤ (3 * (2 + 2 * (5 * Real.pi + 1))) * (W.card : ℝ) *
        (2 * T + (N : ℝ)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL2 hFactor
end

/-- Three-term Cauchy--Schwarz in the exact norm form used to pass from the
sharp source block to the three smooth localization pieces. -/
theorem norm_add_add_sq_le_three (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hTri : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    exact (norm_add_le (a + b) c).trans (by linarith [norm_add_le a b])
  have hLeft : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  have hRight : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by positivity
  have hSquare : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := by
    nlinarith
  have hCS : (‖a‖ + ‖b‖ + ‖c‖) ^ 2 ≤
      3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
      sq_nonneg (‖b‖ - ‖c‖)]
  exact hSquare.trans hCS

section
variable (s : Finset ℕ) (W : Finset ℝ)
include s W
/-- Exact finite expansion underlying the Heath--Brown majorant principle.
This is equation (3) in the standard difference-set proof, before taking the
coefficient majorant. -/
theorem ofReal_heathBrownDifferenceMoment_eq_kernel_sum (a : ℕ → ℂ) :
    ((heathBrownDifferenceMoment s W a : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s,
        star (a n) * a m * (heathBrownMajorantKernel W n m : ℂ) := by
  unfold heathBrownDifferenceMoment
  have hcast :
      (((∑ t ∈ W, ∑ u ∈ W,
          ‖heathBrownDifferencePolynomial s a t u‖ ^ 2 : ℝ)) : ℂ) =
        ∑ t ∈ W, ∑ u ∈ W,
          ((‖heathBrownDifferencePolynomial s a t u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  simp_rw [← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]
  unfold heathBrownDifferencePolynomial
  simp only [map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  let F : ℝ → ℝ → ℕ → ℕ → ℂ := fun y x n m =>
    star (a n) * star (heathBrownPhase n y) *
        star (star (heathBrownPhase n x)) *
      (a m * heathBrownPhase m y * star (heathBrownPhase m x))
  change (∑ y ∈ W, ∑ x ∈ W, ∑ n ∈ s, ∑ m ∈ s, F y x n m) = _
  calc
    _ = ∑ y ∈ W, ∑ n ∈ s, ∑ x ∈ W, ∑ m ∈ s, F y x n m := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ n ∈ s, ∑ y ∈ W, ∑ x ∈ W, ∑ m ∈ s, F y x n m := by
      exact Finset.sum_comm
    _ = ∑ n ∈ s, ∑ y ∈ W, ∑ m ∈ s, ∑ x ∈ W, F y x n m := by
      pm_90 Finset.sum_congr n hn y hy
      exact Finset.sum_comm
    _ = ∑ n ∈ s, ∑ m ∈ s, ∑ y ∈ W, ∑ x ∈ W, F y x n m := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = ∑ n ∈ s, ∑ m ∈ s, ∑ x ∈ W, ∑ y ∈ W, F y x n m := by
      pm_4079
      exact Finset.sum_comm
    _ = ∑ n ∈ s, ∑ m ∈ s,
          star (a n) * a m * (heathBrownMajorantKernel W n m : ℂ) := by
      pm_4079
      unfold heathBrownMajorantKernel
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_conj_mul_self]
      unfold F
      simp only [map_sum, map_mul, star_star]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      have hstarstar (z : ℂ) : (starRingEnd ℂ) (star z) = z :=
        star_star z
      simp_rw [hstarstar]
      pm_90 Finset.sum_congr x hx y hy
      simp only [Complex.star_def]
      ring

/-- For nonnegative real coefficients, the positive-kernel expansion is
itself real and has the expected coefficient product. -/
theorem heathBrownDifferenceMoment_ofReal_eq_kernel_sum (b : ℕ → ℝ) :
    heathBrownDifferenceMoment s W (fun n => (b n : ℂ)) =
      ∑ n ∈ s, ∑ m ∈ s,
        b n * b m * heathBrownMajorantKernel W n m := by
  apply Complex.ofReal_injective
  rw [ofReal_heathBrownDifferenceMoment_eq_kernel_sum]
  push_cast
  simp only [Complex.star_def, Complex.conj_ofReal]

/-- Heath--Brown's coefficient-majorant principle for the ordered
difference-set second moment.  This is the exact finite inequality used
before the analytic treatment of the nonnegative envelope. -/
theorem heathBrownDifferenceMoment_le_of_norm_le (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hb : ∀ n ∈ s, 0 ≤ b n)
    (hab : ∀ n ∈ s, ‖a n‖ ≤ b n) :
    heathBrownDifferenceMoment s W a ≤
      heathBrownDifferenceMoment s W (fun n => (b n : ℂ)) := by
  rw [heathBrownDifferenceMoment_ofReal_eq_kernel_sum]
  calc
    heathBrownDifferenceMoment s W a =
        ‖((heathBrownDifferenceMoment s W a : ℝ) : ℂ)‖ := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg
        (heathBrownDifferenceMoment_nonneg s W a)]
    _ = ‖∑ n ∈ s, ∑ m ∈ s,
          star (a n) * a m * (heathBrownMajorantKernel W n m : ℂ)‖ := by
      rw [ofReal_heathBrownDifferenceMoment_eq_kernel_sum]
    _ ≤ ∑ n ∈ s, ‖∑ m ∈ s,
          star (a n) * a m * (heathBrownMajorantKernel W n m : ℂ)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ s, ∑ m ∈ s,
          ‖star (a n) * a m * (heathBrownMajorantKernel W n m : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ s, ∑ m ∈ s,
          b n * b m * heathBrownMajorantKernel W n m := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, norm_mul, norm_star, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (heathBrownMajorantKernel_nonneg W n m)]
      exact mul_le_mul
        (mul_le_mul (hab n hn) (hab m hm) (norm_nonneg _) (hb n hn))
        (le_refl _) (heathBrownMajorantKernel_nonneg W n m)
        (mul_nonneg (hb n hn) (hb m hm))
end

/-- The two Heath--Brown phases combine to the negative-sign Dirichlet
phase at the ordinate difference. -/
theorem heathBrownPhase_mul_star (n : ℕ) (hn : 0 < n) (t u : ℝ) :
    heathBrownPhase n t * star (heathBrownPhase n u) =
      heathBrownPhase n (t - u) := by
  have hnNeRealCast : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  pm_4834
  pm_4836
  pm_6566 hConj u hnArg
  pm_298 map_mul map_neg Complex.conj_ofReal Complex.conj_I hConj
  have hstar : star ((((n : ℝ) : ℂ) ^ ((-(u : ℂ)) * I))) =
      (((n : ℝ) : ℂ) ^ ((-(u : ℂ)) * (-I))) := by
    simpa only [Complex.star_def] using hConj.symm
  unfold heathBrownPhase
  rw [hnCast, hstar, ← Complex.cpow_add _ _ hnNeRealCast]
  congr 1
  push_cast
  ring

/-- The conjugated negative phase at `n` times the negative phase at `m`
is the ratio phase `(n/m)^{it}` used by Guth--Maynard's `R`-sum. -/
theorem star_heathBrownPhase_mul_eq_ratio_cpow
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    star (heathBrownPhase n t) * heathBrownPhase m t =
      (((n : ℝ) / m : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
  pm_96 hn0 n
  pm_96 hm0 m
  pm_7059 hmarg m hm0
  have hstar : star (heathBrownPhase n t) =
      (((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) := by
    pm_6172 n
    pm_7059 hnarg n hn0
    pm_6566 h t hnarg
    pm_298 map_mul map_neg Complex.conj_ofReal Complex.conj_I h
    rw [Complex.star_def, ← h]
    congr 1
    ring
  rw [hstar]
  pm_6172 m
  rw [show ((-(t : ℂ)) * I) = -((t : ℂ) * I) by ring,
    Complex.cpow_neg]
  rw [← Complex.inv_cpow _ _ hmarg]
  calc
    (((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) *
        ((((m : ℝ) : ℂ)⁻¹) ^ ((t : ℂ) * I)) =
      ((((n : ℝ) * (m : ℝ)⁻¹ : ℝ) : ℂ) ^ ((t : ℂ) * I)) := by
        simpa only [ofReal_mul, ofReal_inv] using
          (Complex.mul_cpow_ofReal_nonneg hn0
            (inv_nonneg.mpr hm0) ((t : ℂ) * I)).symm
    _ = (((n : ℝ) / m : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      rw [div_eq_mul_inv]

/-- The positive majorant kernel is exactly the squared norm of the
Guth--Maynard ratio sum `R(n/m)`. -/
theorem heathBrownMajorantKernel_eq_norm_gmR_ratio
    (W : Finset ℝ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    heathBrownMajorantKernel W n m =
      ‖gmR W ((n : ℝ) / m)‖ ^ 2 := by
  unfold heathBrownMajorantKernel gmR
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  rw [star_heathBrownPhase_mul_eq_ratio_cpow n m hn hm t]
  have hpos : 0 < (n : ℝ) / m :=
    div_pos (by exact_mod_cast hn) (by exact_mod_cast hm)
  rw [abs_of_pos hpos]

/-- A common positive dilation leaves the Heath--Brown ratio kernel
unchanged.  This is the exact invariance used in Lemma 29.8. -/
theorem heathBrownMajorantKernel_mul_left_right
    (W : Finset ℝ) (q n m : ℕ)
    (hq : 0 < q) (hn : 0 < n) (hm : 0 < m) :
    heathBrownMajorantKernel W (q * n) (q * m) =
      heathBrownMajorantKernel W n m := by
  rw [heathBrownMajorantKernel_eq_norm_gmR_ratio W (q * n) (q * m)
      (Nat.mul_pos hq hn) (Nat.mul_pos hq hm),
    heathBrownMajorantKernel_eq_norm_gmR_ratio W n m hn hm]
  congr 3
  push_cast
  field_simp

section
variable (N : ℕ)
include N
/-- The ordered difference polynomial is the project's actual dyadic
negative-sign Dirichlet polynomial evaluated at `t - u`. -/
theorem heathBrownDifferencePolynomial_dyadic_eq_dirichletPoly (a : ℕ → ℂ) (t u : ℝ) :
    heathBrownDifferencePolynomial (dyadicInterval N) a t u =
      dirichletPoly N a (t - u) := by
  unfold heathBrownDifferencePolynomial dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, heathBrownPhase_mul_star]
  · rfl
  · rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega

/-- Consequently the ordered difference moment is exactly the finite
second moment of the actual dyadic polynomial over all ordinate pairs. -/
theorem heathBrownDifferenceMoment_dyadic_eq_dirichletPoly (W : Finset ℝ) (a : ℕ → ℂ) :
    heathBrownDifferenceMoment (dyadicInterval N) W a =
      ∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly N a (t - u)‖ ^ 2 := by
  unfold heathBrownDifferenceMoment
  simp_rw [heathBrownDifferencePolynomial_dyadic_eq_dirichletPoly]

/-- Unit-bounded coefficients are dominated by the coefficient-one
difference moment on the actual dyadic interval. -/
theorem dirichletPoly_differenceMoment_le_one (W : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) :
    (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly N a (t - u)‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W,
        ‖dirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2 := by
  rw [← heathBrownDifferenceMoment_dyadic_eq_dirichletPoly,
    ← heathBrownDifferenceMoment_dyadic_eq_dirichletPoly]
  exact heathBrownDifferenceMoment_le_of_norm_le
    (dyadicInterval N) W a (fun _ => 1)
    (by intro n hn; positivity) ha

/-- The source positive-sign convention is the negative-sign convention
with pointwise conjugated coefficients, at the level of norms. -/
theorem norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs (a : ℕ → ℂ) (t : ℝ) :
    ‖sourceDirichletPoly N a t‖ =
      ‖dirichletPoly N (conjugateCoeffs a) t‖ := by
  have h := norm_sourceDirichletPoly_conjugateCoeffs
    N (conjugateCoeffs a) t
  have hcc : conjugateCoeffs (conjugateCoeffs a) = a := by
    funext n
    unfold conjugateCoeffs
    exact star_star _
  rw [hcc] at h
  exact h

/-- Source-facing form of the coefficient-one majorant, with the sign and
interval conventions used in Guth--Maynard Theorem 1.1 and Section 6. -/
theorem sourceDirichletPoly_differenceMoment_le_one (W : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N a (t - u)‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2 := by
  simp_rw [norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
  have hone : conjugateCoeffs (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) := by
    funext n
    unfold conjugateCoeffs
    exact star_one ℂ
  rw [hone]
  exact dirichletPoly_differenceMoment_le_one N W (conjugateCoeffs a)
    (by
      intro n hn
      rw [norm_conjugateCoeffs]
      exact ha n hn)

/-- Source-sign form of Jutila's coefficient-majorant lemma.  The proof is
the positive-kernel identity, so it loses only the displayed pointwise
majorant and no cardinality or scale factor. -/
theorem sourceDirichletPoly_differenceMoment_le_of_norm_le (W : Finset ℝ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hb : ∀ n ∈ dyadicInterval N, 0 ≤ b n)
    (hab : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ b n) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N a (t - u)‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun n => (b n : ℂ)) (t - u)‖ ^ 2 := by
  simp_rw [norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
  have hreal : conjugateCoeffs (fun n => (b n : ℂ)) =
      fun n => (b n : ℂ) := by
    funext n
    unfold conjugateCoeffs
    exact Complex.conj_ofReal (b n)
  rw [hreal]
  rw [← heathBrownDifferenceMoment_dyadic_eq_dirichletPoly,
    ← heathBrownDifferenceMoment_dyadic_eq_dirichletPoly]
  exact heathBrownDifferenceMoment_le_of_norm_le
    (dyadicInterval N) W (conjugateCoeffs a) b hb
    (by
      intro n hn
      rw [norm_conjugateCoeffs]
      exact hab n hn)

/-- Kernel form of Jutila's weighted moment.  This is equation (29.34)
expanded before any reflection or powering argument. -/
theorem heathBrownWeightedMoment_eq_kernel_sum (W : Finset ℝ) :
    heathBrownWeightedMoment N W =
      ∑ n ∈ dyadicInterval N, ∑ m ∈ dyadicInterval N,
        heathBrownHalfWeight n * heathBrownHalfWeight m *
          heathBrownMajorantKernel W n m := by
  have hconj : conjugateCoeffs
      (fun n => (heathBrownHalfWeight n : ℂ)) =
        fun n => (heathBrownHalfWeight n : ℂ) := by
    funext n
    unfold conjugateCoeffs
    exact Complex.conj_ofReal _
  unfold heathBrownWeightedMoment
  simp_rw [norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs]
  rw [hconj, ← heathBrownDifferenceMoment_dyadic_eq_dirichletPoly]
  exact heathBrownDifferenceMoment_ofReal_eq_kernel_sum
    (dyadicInterval N) W heathBrownHalfWeight
end

theorem heathBrownHalfWeight_nonneg (n : ℕ) :
    0 ≤ heathBrownHalfWeight n := by
  unfold heathBrownHalfWeight
  positivity

/-- Critical-line weights transform exactly under a common positive
dilation.  The factor `q` is the square of the `sqrt q` coefficient loss
in the scaled polynomial. -/
theorem natCast_mul_heathBrownHalfWeight_mul
    (q n m : ℕ) (hq : 0 < q) (hn : 0 < n) (hm : 0 < m) :
    (q : ℝ) * heathBrownHalfWeight (q * n) *
        heathBrownHalfWeight (q * m) =
      heathBrownHalfWeight n * heathBrownHalfWeight m := by
  pm_74 hqR q hq
  pm_74 hnR n hn
  pm_74 hmR m hm
  pm_5455 hqRoot q hqR
  pm_5455 hnRoot n hnR
  pm_5455 hmRoot m hmR
  unfold heathBrownHalfWeight
  push_cast
  rw [Real.sqrt_mul (le_of_lt hqR), Real.sqrt_mul (le_of_lt hqR)]
  field_simp [hqRoot.ne', hnRoot.ne', hmRoot.ne']
  rw [Real.sq_sqrt hqR.le]

section
variable (P : Finset ℕ)
include P
/-- Exact finite collection of the product of the auxiliary polynomial and
the critical-line source block.  This is the coefficient identity `A(l)` in
Montgomery--Vaughan Lemma 29.7, including collisions of distinct products. -/
theorem heathBrownTransfer_polynomial_identity (N : ℕ) (t u : ℝ) :
    (∑ p ∈ P, ∑ n ∈ dyadicInterval N,
        (heathBrownHalfWeight (p * n) : ℂ) *
          heathBrownPhase (p * n) t * star (heathBrownPhase (p * n) u)) =
      ∑ l ∈ heathBrownTransferSupport P N,
        (heathBrownTransferCoeff P N l : ℂ) *
          heathBrownPhase l t * star (heathBrownPhase l u) := by
  pm_7543
  have hMaps : ∀ x ∈ tuples, x.1 * x.2 ∈ support := by
    pm_4831 x hx
  rw [show (∑ p ∈ P, ∑ n ∈ dyadicInterval N,
      (heathBrownHalfWeight (p * n) : ℂ) *
        heathBrownPhase (p * n) t * star (heathBrownPhase (p * n) u)) =
      ∑ x ∈ tuples,
        (heathBrownHalfWeight (x.1 * x.2) : ℂ) *
          heathBrownPhase (x.1 * x.2) t *
            star (heathBrownPhase (x.1 * x.2) u) by
      simp only [tuples, heathBrownTransferTuples, Finset.sum_product]]
  calc
    (∑ x ∈ tuples,
        (heathBrownHalfWeight (x.1 * x.2) : ℂ) *
          heathBrownPhase (x.1 * x.2) t *
            star (heathBrownPhase (x.1 * x.2) u)) =
      ∑ l ∈ support,
        ∑ x ∈ tuples with x.1 * x.2 = l,
          (heathBrownHalfWeight (x.1 * x.2) : ℂ) *
            heathBrownPhase (x.1 * x.2) t *
              star (heathBrownPhase (x.1 * x.2) u) :=
        (Finset.sum_fiberwise_of_maps_to hMaps _).symm
    _ = ∑ l ∈ support,
        (heathBrownTransferCoeff P N l : ℂ) *
          heathBrownPhase l t * star (heathBrownPhase l u) := by
      apply Finset.sum_congr rfl
      intro l hl
      calc
        (∑ x ∈ tuples with x.1 * x.2 = l,
            (heathBrownHalfWeight (x.1 * x.2) : ℂ) *
              heathBrownPhase (x.1 * x.2) t *
                star (heathBrownPhase (x.1 * x.2) u)) =
          ∑ x ∈ tuples with x.1 * x.2 = l,
            (heathBrownHalfWeight (x.1 * x.2) : ℂ) *
              (heathBrownPhase l t * star (heathBrownPhase l u)) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hprod := (Finset.mem_filter.mp hx).2
            rw [hprod]
            ring
        _ = (∑ x ∈ tuples with x.1 * x.2 = l,
              (heathBrownHalfWeight (x.1 * x.2) : ℂ)) *
              (heathBrownPhase l t * star (heathBrownPhase l u)) := by
            rw [Finset.sum_mul]
        _ = (heathBrownTransferCoeff P N l : ℂ) *
              heathBrownPhase l t * star (heathBrownPhase l u) := by
            simp only [heathBrownTransferCoeff, tuples]
            push_cast
            ring
    _ = _ := rfl

/-- The grouped coefficient really represents the ungrouped transferred
difference polynomial, not merely a coefficient-wise majorant. -/
theorem heathBrownTransferredDifferencePolynomial_eq_grouped (N : ℕ) (t u : ℝ) :
    heathBrownTransferredDifferencePolynomial P N t u =
      heathBrownDifferencePolynomial (heathBrownTransferSupport P N)
        (fun l => (heathBrownTransferCoeff P N l : ℂ)) t u := by
  unfold heathBrownTransferredDifferencePolynomial
    heathBrownDifferencePolynomial
  exact heathBrownTransfer_polynomial_identity P N t u

/-- Exact moment-level grouping of all colliding products. -/
theorem heathBrownTransferredDifferenceMoment_eq_grouped (N : ℕ) (W : Finset ℝ) :
    heathBrownTransferredDifferenceMoment P N W =
      heathBrownDifferenceMoment (heathBrownTransferSupport P N) W
        (fun l => (heathBrownTransferCoeff P N l : ℂ)) := by
  unfold heathBrownTransferredDifferenceMoment heathBrownDifferenceMoment
  simp_rw [heathBrownTransferredDifferencePolynomial_eq_grouped]

/-- The grouped transfer coefficient is nonnegative. -/
theorem heathBrownTransferCoeff_nonneg (N l : ℕ) :
    0 ≤ heathBrownTransferCoeff P N l := by
  unfold heathBrownTransferCoeff
  exact Finset.sum_nonneg fun x hx =>
    heathBrownHalfWeight_nonneg (x.1 * x.2)

/-- The product fiber defining a transfer coefficient injects into the
positive divisors of its product.  This is the exact arithmetic content of
the coefficient bound in Montgomery--Vaughan Lemma 29.7. -/
theorem heathBrownTransfer_fiber_card_le_divisors (N l : ℕ) (hl : 0 < l)
    (hP : ∀ p ∈ P, 0 < p) :
    ((heathBrownTransferTuples P N).filter
      (fun x => x.1 * x.2 = l)).card ≤ l.divisors.card := by
  let fiber := (heathBrownTransferTuples P N).filter
    (fun x => x.1 * x.2 = l)
  change fiber.card ≤ l.divisors.card
  apply Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => x.1)
  · intro x hx
    have hxFilter := Finset.mem_filter.mp hx
    have hxTuple := Finset.mem_product.mp hxFilter.1
    change x.1 ∈ l.divisors
    rw [Nat.mem_divisors]
    exact ⟨⟨x.2, hxFilter.2.symm⟩, hl.ne'⟩
  · intro x hx y hy hxy
    change x.1 = y.1 at hxy
    have hxFilter := Finset.mem_filter.mp hx
    have hyFilter := Finset.mem_filter.mp hy
    have hxTuple := Finset.mem_product.mp hxFilter.1
    have hyTuple := Finset.mem_product.mp hyFilter.1
    have hxPos : 0 < x.1 := hP x.1 hxTuple.1
    apply Prod.ext hxy
    apply Nat.mul_left_cancel hxPos
    calc
      x.1 * x.2 = l := hxFilter.2
      _ = y.1 * y.2 := hyFilter.2.symm
      _ = x.1 * y.2 := by rw [hxy]

/-- Every summand in a transfer fiber has the same critical-line weight,
so the grouped coefficient is exactly the fiber cardinality times
`l⁻¹ᐟ²`. -/
theorem heathBrownTransferCoeff_eq_card_mul_halfWeight (N l : ℕ) :
    heathBrownTransferCoeff P N l =
      (((heathBrownTransferTuples P N).filter
        (fun x => x.1 * x.2 = l)).card : ℝ) * heathBrownHalfWeight l := by
  unfold heathBrownTransferCoeff
  calc
    (∑ x ∈ (heathBrownTransferTuples P N).filter
        (fun x => x.1 * x.2 = l),
        heathBrownHalfWeight (x.1 * x.2)) =
      ∑ _x ∈ (heathBrownTransferTuples P N).filter
        (fun x => x.1 * x.2 = l), heathBrownHalfWeight l := by
      pm_275 Finset.sum_congr x hx Finset.mem_filter.mp
    _ = (((heathBrownTransferTuples P N).filter
        (fun x => x.1 * x.2 = l)).card : ℝ) * heathBrownHalfWeight l := by
      simp
end

/-- Uniform divisor bound for the grouped transfer coefficient.  The
The constant depends only on the requested epsilon and is independent of both
source scales and the auxiliary interval. -/
theorem exists_heathBrownTransferCoeff_bound
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset ℕ) (N l : ℕ), 0 < l →
        (∀ p ∈ P, 0 < p) →
        heathBrownTransferCoeff P N l ≤
          C * (l : ℝ) ^ η * heathBrownHalfWeight l := by
  pm_98 C hC hDivisor divisorCountBound_native η hη
  pm_435 C hC P N l hl hP
  rw [heathBrownTransferCoeff_eq_card_mul_halfWeight]
  have hCardNat := heathBrownTransfer_fiber_card_le_divisors P N l hl hP
  have hCardReal :
      (((heathBrownTransferTuples P N).filter
        (fun x => x.1 * x.2 = l)).card : ℝ) ≤ (l.divisors.card : ℝ) := by
    exact_mod_cast hCardNat
  have hWeightNonneg := heathBrownHalfWeight_nonneg l
  exact mul_le_mul_of_nonneg_right
    (hCardReal.trans (hDivisor l hl)) hWeightNonneg

/-- Every auxiliary factor is positive. -/
theorem heathBrownTransferAuxiliary_pos
    (J p : ℕ) (hp : p ∈ heathBrownTransferAuxiliary J) : 0 < p := by
  rw [heathBrownTransferAuxiliary, Finset.mem_Ioc] at hp
  omega

/-- The harmonic mass of `(J,2J]` is at least one half.  This prevents the
transfer diagonal from losing the scale ratio `P/N`. -/
theorem one_half_le_heathBrownTransferAuxiliary_harmonic
    (J : ℕ) (hJ : 0 < J) :
    (1 / 2 : ℝ) ≤
      ∑ p ∈ heathBrownTransferAuxiliary J, (p : ℝ)⁻¹ := by
  have hTerm : ∀ p ∈ heathBrownTransferAuxiliary J,
      (1 / (2 * J : ℝ)) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hpBounds := Finset.mem_Ioc.mp hp
    have hpPos : (0 : ℝ) < p := by
      exact_mod_cast (lt_of_lt_of_le hJ hpBounds.1.le)
    have hpUpper : (p : ℝ) ≤ 2 * J := by exact_mod_cast hpBounds.2
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hpPos hpUpper
  have hCard : (heathBrownTransferAuxiliary J).card = J := by
    simp [heathBrownTransferAuxiliary]
    omega
  calc
    (1 / 2 : ℝ) = (J : ℝ) * (1 / (2 * J : ℝ)) := by
      field_simp
    _ = ∑ _p ∈ heathBrownTransferAuxiliary J,
          (1 / (2 * J : ℝ)) := by
      simp [hCard]
    _ ≤ ∑ p ∈ heathBrownTransferAuxiliary J, (p : ℝ)⁻¹ := by
      exact Finset.sum_le_sum hTerm

/-- Products in the auxiliary transfer occupy exactly two adjacent dyadic
blocks, from `JN` to `4JN`. -/
theorem heathBrownTransferSupport_subset_two_dyadic
    (J N : ℕ) (hJ : 0 < J) (hN : 0 < N) :
    heathBrownTransferSupport (heathBrownTransferAuxiliary J) N ⊆
      dyadicInterval (J * N) ∪ dyadicInterval (2 * (J * N)) := by
  intro l hl
  pm_4080 heathBrownTransferSupport hl x hx
  have hxTuple := Finset.mem_product.mp hx
  have hpBounds := Finset.mem_Ioc.mp hxTuple.1
  have hnBounds := Finset.mem_Ioc.mp hxTuple.2
  have hLower : J * N < x.1 * x.2 := by
    calc
      J * N < x.1 * N := Nat.mul_lt_mul_of_pos_right hpBounds.1 hN
      _ < x.1 * x.2 :=
        Nat.mul_lt_mul_of_pos_left hnBounds.1
          (lt_of_lt_of_le hJ hpBounds.1.le)
  have hUpper : x.1 * x.2 ≤ 4 * (J * N) := by
    calc
      x.1 * x.2 ≤ (2 * J) * (2 * N) :=
        Nat.mul_le_mul hpBounds.2 hnBounds.2
      _ = 4 * (J * N) := by ring
  by_cases hMid : x.1 * x.2 ≤ 2 * (J * N)
  · apply Finset.mem_union.mpr
    exact Or.inl (by
      rw [dyadicInterval, Finset.mem_Ioc]
      exact ⟨hLower, hMid⟩)
  · apply Finset.mem_union.mpr
    exact Or.inr (by
      rw [dyadicInterval, Finset.mem_Ioc]
      exact ⟨Nat.lt_of_not_ge hMid, hUpper.trans_eq (by ring)⟩)

/-- A coefficient bounded by `B n⁻¹ᐟ²` on one dyadic block has moment at
most `B² S(N)`.  The proof is the positive-kernel majorant, not a
pointwise triangle inequality. -/
theorem heathBrownDifferenceMoment_dyadic_le_weighted
    (N : ℕ) (W : Finset ℝ) (a : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (ha : ∀ n ∈ dyadicInterval N,
      ‖a n‖ ≤ B * heathBrownHalfWeight n) :
    heathBrownDifferenceMoment (dyadicInterval N) W a ≤
      B ^ 2 * heathBrownWeightedMoment N W := by
  have hb : ∀ n ∈ dyadicInterval N,
      0 ≤ B * heathBrownHalfWeight n := by
    intro n hn
    exact mul_nonneg hB (heathBrownHalfWeight_nonneg n)
  have hMajorant := heathBrownDifferenceMoment_le_of_norm_le
    (dyadicInterval N) W a (fun n => B * heathBrownHalfWeight n) hb ha
  calc
    heathBrownDifferenceMoment (dyadicInterval N) W a ≤
        heathBrownDifferenceMoment (dyadicInterval N) W
          (fun n => ((B * heathBrownHalfWeight n : ℝ) : ℂ)) := hMajorant
    _ = B ^ 2 * heathBrownWeightedMoment N W := by
      rw [heathBrownDifferenceMoment_ofReal_eq_kernel_sum,
        heathBrownWeightedMoment_eq_kernel_sum]
      pm_224 mul_assoc Finset.mul_sum n hn
      pm_4886 m hm

/-- Adjacent dyadic intervals are disjoint.  This is the finite endpoint
convention needed to split the product support without duplicating its
middle boundary. -/
theorem dyadicInterval_disjoint_double (Q : ℕ) :
    Disjoint (dyadicInterval Q) (dyadicInterval (2 * Q)) := by
  rw [Finset.disjoint_left]
  intro n hnQ hn2Q
  rw [dyadicInterval, Finset.mem_Ioc] at hnQ hn2Q
  omega

/-- The collected auxiliary-times-source polynomial is exactly the sum of
its two adjacent dyadic restrictions.  Coefficients outside the genuine
product support are set to zero, so this is an identity rather than a
majorization. -/
theorem heathBrownTransferredDifferencePolynomial_eq_two_dyadic
    (J N : ℕ) (t u : ℝ) (hJ : 0 < J) (hN : 0 < N) :
    heathBrownTransferredDifferencePolynomial
        (heathBrownTransferAuxiliary J) N t u =
      heathBrownDifferencePolynomial (dyadicInterval (J * N))
          (fun l => if l ∈ heathBrownTransferSupport
              (heathBrownTransferAuxiliary J) N then
            (heathBrownTransferCoeff
              (heathBrownTransferAuxiliary J) N l : ℂ) else 0) t u +
      heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N)))
          (fun l => if l ∈ heathBrownTransferSupport
              (heathBrownTransferAuxiliary J) N then
            (heathBrownTransferCoeff
              (heathBrownTransferAuxiliary J) N l : ℂ) else 0) t u := by
  classical
  let S := heathBrownTransferSupport (heathBrownTransferAuxiliary J) N
  let D₁ := dyadicInterval (J * N)
  let D₂ := dyadicInterval (2 * (J * N))
  pm_824
  rw [heathBrownTransferredDifferencePolynomial_eq_grouped]
  change heathBrownDifferencePolynomial S
      (fun l => (heathBrownTransferCoeff
        (heathBrownTransferAuxiliary J) N l : ℂ)) t u =
    heathBrownDifferencePolynomial D₁ a t u +
      heathBrownDifferencePolynomial D₂ a t u
  have hS : S ⊆ D₁ ∪ D₂ :=
    heathBrownTransferSupport_subset_two_dyadic J N hJ hN
  have hDisjoint : Disjoint D₁ D₂ :=
    dyadicInterval_disjoint_double (J * N)
  unfold heathBrownDifferencePolynomial
  rw [← Finset.sum_union hDisjoint]
  calc
    (∑ l ∈ S,
        (heathBrownTransferCoeff
          (heathBrownTransferAuxiliary J) N l : ℂ) *
          heathBrownPhase l t * star (heathBrownPhase l u)) =
        ∑ l ∈ S,
          a l * heathBrownPhase l t * star (heathBrownPhase l u) := by
      apply Finset.sum_congr rfl
      intro l hlS
      simp [a, hlS]
    _ = ∑ l ∈ D₁ ∪ D₂,
        a l * heathBrownPhase l t * star (heathBrownPhase l u) := by
      apply Finset.sum_subset hS
      intro l hlUnion hlS
      simp [a, hlS]

/-- Pointwise divisor-bound majorant for the zero-extended transfer
coefficient on either of its two dyadic blocks. -/
theorem heathBrownTransferCoeff_two_dyadic_bound
    (η C : ℝ) (hη : 0 < η) (hCNonneg : 0 ≤ C)
    (hC : ∀ (P : Finset ℕ) (N l : ℕ), 0 < l →
      (∀ p ∈ P, 0 < p) →
      heathBrownTransferCoeff P N l ≤
        C * (l : ℝ) ^ η * heathBrownHalfWeight l)
    (J N Q l : ℕ) (hJ : 0 < J) (hN : 0 < N)
    (hQ : Q = J * N ∨ Q = 2 * (J * N))
    (hl : l ∈ dyadicInterval Q) :
    ‖if l ∈ heathBrownTransferSupport (heathBrownTransferAuxiliary J) N then
        (heathBrownTransferCoeff
          (heathBrownTransferAuxiliary J) N l : ℂ) else 0‖ ≤
      (C * (4 * (J * N) : ℝ) ^ η) * heathBrownHalfWeight l := by
  classical
  by_cases hlS : l ∈ heathBrownTransferSupport
      (heathBrownTransferAuxiliary J) N
  · simp only [hlS, ite_true, norm_real, Real.norm_eq_abs]
    pm_5027 hlPos l hl
    have hCoeffNonneg := heathBrownTransferCoeff_nonneg
      (heathBrownTransferAuxiliary J) N l
    rw [abs_of_nonneg hCoeffNonneg]
    have hCoeff := hC (heathBrownTransferAuxiliary J) N l hlPos
      (heathBrownTransferAuxiliary_pos J)
    have hlUpperNat : l ≤ 4 * (J * N) := by
      rcases hQ with rfl | rfl
      · rw [dyadicInterval, Finset.mem_Ioc] at hl
        omega
      · rw [dyadicInterval, Finset.mem_Ioc] at hl
        omega
    have hlUpper : (l : ℝ) ≤ ((4 * (J * N) : ℕ) : ℝ) := by
      exact_mod_cast hlUpperNat
    have hPow : (l : ℝ) ^ η ≤ ((4 * (J * N) : ℕ) : ℝ) ^ η := by
      exact Real.rpow_le_rpow (Nat.cast_nonneg l) hlUpper hη.le
    have hWeight := heathBrownHalfWeight_nonneg l
    calc
      heathBrownTransferCoeff (heathBrownTransferAuxiliary J) N l
          ≤ C * (l : ℝ) ^ η * heathBrownHalfWeight l := hCoeff
      _ ≤ C * ((4 * (J * N) : ℕ) : ℝ) ^ η * heathBrownHalfWeight l := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPow hCNonneg) hWeight
      _ = (C * (4 * (J * N) : ℝ) ^ η) *
          heathBrownHalfWeight l := by norm_num
  · simp only [hlS, ite_false, norm_zero]
    exact mul_nonneg (mul_nonneg hCNonneg (Real.rpow_nonneg (by positivity) _))
      (heathBrownHalfWeight_nonneg l)

/-- Montgomery--Vaughan Lemma 29.7 at the exact finite level: the
auxiliary transfer moment is controlled by the two adjacent Jutila
moments which contain its product support.  The constant has only the
divisor-bound loss `(4JN)^η`; in particular there is no factor `J/N`. -/
theorem exists_heathBrownTransferredDifferenceMoment_two_dyadic_bound
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J N : ℕ) (W : Finset ℝ), 0 < J → 0 < N →
        heathBrownTransferredDifferenceMoment
            (heathBrownTransferAuxiliary J) N W ≤
          2 * (C * (4 * (J * N) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (J * N) W +
              heathBrownWeightedMoment (2 * (J * N)) W) := by
  pm_98 C hC hCoeff exists_heathBrownTransferCoeff_bound η hη
  pm_435 C hC J N W hJ hN
  let S := heathBrownTransferSupport (heathBrownTransferAuxiliary J) N
  pm_824
  let B : ℝ := C * (4 * (J * N) : ℝ) ^ η
  have hB : 0 ≤ B := by
    exact mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  have ha₁ : ∀ l ∈ dyadicInterval (J * N),
      ‖a l‖ ≤ B * heathBrownHalfWeight l := by
    intro l hl
    exact heathBrownTransferCoeff_two_dyadic_bound η C hη hC.le hCoeff
      J N (J * N) l hJ hN (Or.inl rfl) hl
  have ha₂ : ∀ l ∈ dyadicInterval (2 * (J * N)),
      ‖a l‖ ≤ B * heathBrownHalfWeight l := by
    intro l hl
    exact heathBrownTransferCoeff_two_dyadic_bound η C hη hC.le hCoeff
      J N (2 * (J * N)) l hJ hN (Or.inr rfl) hl
  have hPoint : ∀ t ∈ W, ∀ u ∈ W,
      ‖heathBrownTransferredDifferencePolynomial
          (heathBrownTransferAuxiliary J) N t u‖ ^ 2 ≤
        2 * (‖heathBrownDifferencePolynomial (dyadicInterval (J * N))
              a t u‖ ^ 2 +
          ‖heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N)))
              a t u‖ ^ 2) := by
    intro t ht u hu
    rw [heathBrownTransferredDifferencePolynomial_eq_two_dyadic
      J N t u hJ hN]
    change ‖heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u +
          heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u‖ ^ 2 ≤
      2 * (‖heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u‖ ^ 2 +
        ‖heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u‖ ^ 2)
    have hNorm := norm_add_le
      (heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u)
      (heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u)
    have hNormSq :
        ‖heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u +
          heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u‖ ^ 2 ≤
        (‖heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u‖ +
          ‖heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hNorm
    have hSq := sq_nonneg
      (‖heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u‖ -
        ‖heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u‖)
    calc
      _ ≤ (‖heathBrownDifferencePolynomial (dyadicInterval (J * N)) a t u‖ +
          ‖heathBrownDifferencePolynomial (dyadicInterval (2 * (J * N))) a t u‖) ^ 2 :=
        hNormSq
      _ ≤ _ := by nlinarith
  have hMomentSplit :
      heathBrownTransferredDifferenceMoment
          (heathBrownTransferAuxiliary J) N W ≤
        2 * (heathBrownDifferenceMoment (dyadicInterval (J * N)) W a +
          heathBrownDifferenceMoment (dyadicInterval (2 * (J * N))) W a) := by
    unfold heathBrownTransferredDifferenceMoment heathBrownDifferenceMoment
    calc
      (∑ t ∈ W, ∑ u ∈ W,
          ‖heathBrownTransferredDifferencePolynomial
            (heathBrownTransferAuxiliary J) N t u‖ ^ 2) ≤
          ∑ t ∈ W, ∑ u ∈ W,
            2 * (‖heathBrownDifferencePolynomial (dyadicInterval (J * N))
                    a t u‖ ^ 2 +
              ‖heathBrownDifferencePolynomial
                    (dyadicInterval (2 * (J * N))) a t u‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        exact hPoint t ht u hu
      _ = 2 * ((∑ t ∈ W, ∑ u ∈ W,
              ‖heathBrownDifferencePolynomial (dyadicInterval (J * N))
                a t u‖ ^ 2) +
            (∑ t ∈ W, ∑ u ∈ W,
              ‖heathBrownDifferencePolynomial
                (dyadicInterval (2 * (J * N))) a t u‖ ^ 2)) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hFirst := heathBrownDifferenceMoment_dyadic_le_weighted
    (J * N) W a B hB ha₁
  have hSecond := heathBrownDifferenceMoment_dyadic_le_weighted
    (2 * (J * N)) W a B hB ha₂
  calc
    heathBrownTransferredDifferenceMoment
        (heathBrownTransferAuxiliary J) N W ≤
      2 * (heathBrownDifferenceMoment (dyadicInterval (J * N)) W a +
        heathBrownDifferenceMoment (dyadicInterval (2 * (J * N))) W a) :=
      hMomentSplit
    _ ≤ 2 * (B ^ 2 * heathBrownWeightedMoment (J * N) W +
        B ^ 2 * heathBrownWeightedMoment (2 * (J * N)) W) := by
      gcongr
    _ = 2 * (C * (4 * (J * N) : ℝ) ^ η) ^ 2 *
        (heathBrownWeightedMoment (J * N) W +
          heathBrownWeightedMoment (2 * (J * N)) W) := by
      dsimp only [B]
      ring

section
variable (P : Finset ℕ) (N : ℕ) (W : Finset ℝ)
include P N W
/-- Expanding the exact grouped product moment recovers the positive
fourfold transferred kernel.  Thus the diagonal lower bound below applies
to the actual collected Dirichlet polynomial, including product collisions. -/
theorem heathBrownTransferredDifferenceMoment_eq_kernel :
    heathBrownTransferredDifferenceMoment P N W =
      heathBrownTransferredKernelMoment P N W := by
  pm_7543
  let prod : ℕ × ℕ → ℕ := fun x => x.1 * x.2
  let F : (ℕ × ℕ) → (ℕ × ℕ) → ℝ := fun x y =>
    heathBrownHalfWeight (prod x) * heathBrownHalfWeight (prod y) *
      heathBrownMajorantKernel W (prod x) (prod y)
  have hMaps : ∀ x ∈ tuples, prod x ∈ support := by
    pm_4831 x hx
  rw [heathBrownTransferredDifferenceMoment_eq_grouped,
    heathBrownDifferenceMoment_ofReal_eq_kernel_sum]
  change (∑ l ∈ support, ∑ k ∈ support,
      heathBrownTransferCoeff P N l * heathBrownTransferCoeff P N k *
        heathBrownMajorantKernel W l k) = _
  calc
    (∑ l ∈ support, ∑ k ∈ support,
        heathBrownTransferCoeff P N l * heathBrownTransferCoeff P N k *
          heathBrownMajorantKernel W l k) =
      ∑ l ∈ support, ∑ k ∈ support,
        ∑ x ∈ tuples with prod x = l,
          ∑ y ∈ tuples with prod y = k, F x y := by
      pm_90 Finset.sum_congr l hl k hk
      simp only [heathBrownTransferCoeff, tuples, prod, F]
      pm_1063 Finset.sum_mul x hx
      pm_266 Finset.mul_sum Finset.sum_mul Finset.sum_congr y hy
      pm_547 hxProd Finset.mem_filter.mp hx hyProd hy
      rw [hxProd, hyProd]
    _ = ∑ l ∈ support,
        ∑ x ∈ tuples with prod x = l,
          ∑ k ∈ support,
            ∑ y ∈ tuples with prod y = k, F x y := by
      apply Finset.sum_congr rfl
      intro l hl
      exact Finset.sum_comm
    _ = ∑ x ∈ tuples,
          ∑ k ∈ support,
            ∑ y ∈ tuples with prod y = k, F x y := by
      exact Finset.sum_fiberwise_of_maps_to hMaps _
    _ = ∑ x ∈ tuples, ∑ y ∈ tuples, F x y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_fiberwise_of_maps_to hMaps _
    _ = heathBrownTransferredKernelMoment P N W := by
      pm_188 tuples heathBrownTransferTuples F prod Finset.sum_product
      unfold heathBrownTransferredKernelMoment
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_comm

/-- On the common-factor diagonal, dilation invariance of the majorant
kernel and the critical-line weight identity leave exactly the harmonic
factor `1/p`. -/
theorem heathBrownTransferredKernel_diagonal_eq
    (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P,
        ∑ n ∈ dyadicInterval N, ∑ m ∈ dyadicInterval N,
          heathBrownHalfWeight (p * n) * heathBrownHalfWeight (p * m) *
            heathBrownMajorantKernel W (p * n) (p * m)) =
      (∑ p ∈ P, (p : ℝ)⁻¹) * heathBrownWeightedMoment N W := by
  pm_266 Finset.sum_mul heathBrownWeightedMoment_eq_kernel_sum Finset.sum_congr p hp
  pm_388 Finset.mul_sum n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hpPos := hP p hp
  pm_4835
  pm_5027 hmPos m hm
  rw [heathBrownMajorantKernel_mul_left_right W p n m hpPos hnPos hmPos]
  have hWeight :=
    natCast_mul_heathBrownHalfWeight_mul p n m hpPos hnPos hmPos
  pm_74 hpReal p hpPos
  calc
    heathBrownHalfWeight (p * n) * heathBrownHalfWeight (p * m) *
        heathBrownMajorantKernel W n m =
      (p : ℝ)⁻¹ *
        ((p : ℝ) * heathBrownHalfWeight (p * n) *
          heathBrownHalfWeight (p * m)) *
            heathBrownMajorantKernel W n m := by
      field_simp [hpReal.ne']
    _ = (p : ℝ)⁻¹ *
        (heathBrownHalfWeight n * heathBrownHalfWeight m *
          heathBrownMajorantKernel W n m) := by rw [hWeight]; ring

/-- The product moment dominates its common-factor diagonal.  This is the
positive-kernel form of the Parseval step in Montgomery--Vaughan Lemma 29.7.
No cancellation or asymptotic estimate is used. -/
theorem harmonic_mul_heathBrownWeightedMoment_le_transferred
    (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, (p : ℝ)⁻¹) * heathBrownWeightedMoment N W ≤
      heathBrownTransferredKernelMoment P N W := by
  rw [← heathBrownTransferredKernel_diagonal_eq P N W hP]
  unfold heathBrownTransferredKernelMoment
  apply Finset.sum_le_sum
  intro p hp
  have hnonneg : ∀ q ∈ P, 0 ≤
      ∑ n ∈ dyadicInterval N, ∑ m ∈ dyadicInterval N,
        heathBrownHalfWeight (p * n) * heathBrownHalfWeight (q * m) *
          heathBrownMajorantKernel W (p * n) (q * m) := by
    intro q hq
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg
      (mul_nonneg (heathBrownHalfWeight_nonneg (p * n))
        (heathBrownHalfWeight_nonneg (q * m)))
      (heathBrownMajorantKernel_nonneg W (p * n) (q * m))
  exact Finset.single_le_sum hnonneg hp
end

/-- Complete auxiliary transfer principle (Montgomery--Vaughan Lemma
29.7): after choosing the whole auxiliary interval `(J,2J]`, the harmonic
diagonal and divisor bound transfer `S(N)` to the two adjacent moments at
scale `JN`, with only an arbitrarily small power loss. -/
theorem exists_heathBrownWeightedMoment_transfer
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J N : ℕ) (W : Finset ℝ), 0 < J → 0 < N →
        heathBrownWeightedMoment N W ≤
          4 * (C * (4 * (J * N) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (J * N) W +
              heathBrownWeightedMoment (2 * (J * N)) W) := by
  pm_4081 C hC hUpper exists_heathBrownTransferredDifferenceMoment_two_dyadic_bound η hη
  pm_435 C hC J N W hJ hN
  let H : ℝ := ∑ p ∈ heathBrownTransferAuxiliary J, (p : ℝ)⁻¹
  have hH : (1 / 2 : ℝ) ≤ H :=
    one_half_le_heathBrownTransferAuxiliary_harmonic J hJ
  have hMomentNonneg : 0 ≤ heathBrownWeightedMoment N W := by
    unfold heathBrownWeightedMoment
    positivity
  have hHalf : (1 / 2 : ℝ) * heathBrownWeightedMoment N W ≤
      H * heathBrownWeightedMoment N W :=
    mul_le_mul_of_nonneg_right hH hMomentNonneg
  have hDiagonal : H * heathBrownWeightedMoment N W ≤
      heathBrownTransferredDifferenceMoment
        (heathBrownTransferAuxiliary J) N W := by
    rw [heathBrownTransferredDifferenceMoment_eq_kernel]
    exact harmonic_mul_heathBrownWeightedMoment_le_transferred
      (heathBrownTransferAuxiliary J) N W
      (heathBrownTransferAuxiliary_pos J)
  have hTransfer := hUpper J N W hJ hN
  calc
    heathBrownWeightedMoment N W ≤
        2 * (H * heathBrownWeightedMoment N W) := by
      nlinarith
    _ ≤ 2 * heathBrownTransferredDifferenceMoment
        (heathBrownTransferAuxiliary J) N W := by
      gcongr
    _ ≤ 2 * (2 * (C * (4 * (J * N) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (J * N) W +
            heathBrownWeightedMoment (2 * (J * N)) W)) := by
      gcongr
    _ = 4 * (C * (4 * (J * N) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (J * N) W +
            heathBrownWeightedMoment (2 * (J * N)) W) := by ring

/-- On `(N,2N]`, multiplication by `sqrt(2N)` dominates the coefficient
one by the critical-line weight.  This is the exact normalization used
between the unweighted source theorem and Jutila's `S(N)`. -/
theorem one_le_sqrt_two_mul_mul_heathBrownHalfWeight
    {N n : ℕ} (hn : n ∈ dyadicInterval N) :
    1 ≤ Real.sqrt (2 * N) * heathBrownHalfWeight n := by
  have hnBounds : N < n ∧ n ≤ 2 * N := by
    simpa [dyadicInterval] using (Finset.mem_Ioc.mp hn)
  have hnPosNat : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnBounds.1
  pm_74 hnPos n hnPosNat
  pm_4891 hrootPos n hnPos
  have hcastLe : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnBounds.2
  have hrootLe : Real.sqrt n ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hcastLe
  unfold heathBrownHalfWeight
  rw [one_div, ← div_eq_mul_inv]
  exact (one_le_div₀ hrootPos).2 hrootLe

/-- Pulling a fixed real scalar out of a source Dirichlet polynomial. -/
theorem sourceDirichletPoly_real_smul_coeffs
    (N : ℕ) (b : ℕ → ℝ) (B t : ℝ) :
    sourceDirichletPoly N (fun n => ((B * b n : ℝ) : ℂ)) t =
      (B : ℂ) * sourceDirichletPoly N (fun n => (b n : ℂ)) t := by
  unfold sourceDirichletPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

/-- Exact Jutila normalization: the coefficient-one ordered-difference
moment is at most `2N` times the weighted moment `S(N)`. -/
theorem sourceCoefficientOne_differenceMoment_le_two_mul_weighted
    (N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) ≤
      (2 * N : ℝ) * heathBrownWeightedMoment N W := by
  let B : ℝ := Real.sqrt (2 * N)
  pm_7263
  have hMajorant := sourceDirichletPoly_differenceMoment_le_of_norm_le
    N W (fun _ => (1 : ℂ)) b
    (by
      intro n hn
      exact mul_nonneg (Real.sqrt_nonneg _) (heathBrownHalfWeight_nonneg n))
    (by
      intro n hn
      simpa only [norm_one, b, B] using
        one_le_sqrt_two_mul_mul_heathBrownHalfWeight hn)
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly N (fun n => (b n : ℂ)) (t - u)‖ ^ 2 :=
      hMajorant
    _ = B ^ 2 * heathBrownWeightedMoment N W := by
      unfold heathBrownWeightedMoment b
      simp_rw [sourceDirichletPoly_real_smul_coeffs]
      pm_4082
      pm_6738
    _ = (2 * N : ℝ) * heathBrownWeightedMoment N W := by
      pm_7841

/-- The common terminal scale used in the source powering lemma. -/
def heathBrownPoweredTargetScale (N k c : ℕ) : ℕ :=
  2 ^ c * N ^ k

/-- Every powered dyadic block embeds exactly into the common terminal scale
by an integral power-of-two auxiliary factor. -/
theorem heathBrownPoweredBlock_mul_aux_eq_target
    (N k c r : ℕ) (hrc : r ≤ c) :
    2 ^ (c - r) * (2 ^ r * N ^ k) =
      heathBrownPoweredTargetScale N k c := by
  unfold heathBrownPoweredTargetScale
  calc
    2 ^ (c - r) * (2 ^ r * N ^ k) =
        (2 ^ (c - r) * 2 ^ r) * N ^ k := by ring
    _ = 2 ^ ((c - r) + r) * N ^ k := by rw [pow_add]
    _ = 2 ^ c * N ^ k := by rw [Nat.sub_add_cancel hrc]

/-- Montgomery--Vaughan Lemma 29.10 in its weighted form implies the
coefficient-one Heath--Brown theorem with no change of exponents.  The only
normalization loss is the explicit factor `2N` proved above. -/
theorem heathBrownCoefficientOneMeanSquare_of_weighted
    (hWeighted : HeathBrownWeightedMeanSquare) :
    HeathBrownCoefficientOneMeanSquare := by
  intro ε hε
  pm_4083 C T₀ hC hT₀ hWeightedBound hWeighted ε hε
  refine ⟨2 * C, T₀, by positivity, hT₀, ?_⟩
  intro N T W hN hT hSep hInterval
  have hNormalize :=
    sourceCoefficientOne_differenceMoment_le_two_mul_weighted N W
  have hCore := hWeightedBound N T W hN hT hSep hInterval
  pm_96 hN0 N
  have hTwoN0 : (0 : ℝ) ≤ 2 * N := by positivity
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hCT0 : 0 ≤ C * T ^ ε := by
    exact mul_nonneg hC.le (Real.rpow_nonneg hT0 _)
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) ≤
        (2 * N : ℝ) * heathBrownWeightedMoment N W := hNormalize
    _ ≤ (2 * N : ℝ) *
        (C * T ^ ε *
          (((W.card : ℝ) ^ 2 + (W.card : ℝ) * N +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)))) :=
      mul_le_mul_of_nonneg_left hCore hTwoN0
    _ = (2 * C) * T ^ ε *
        (((W.card : ℝ) ^ 2 * N) +
          ((W.card : ℝ) * N ^ 2) +
          ((W.card : ℝ) ^ (5 / 4 : ℝ) *
            T ^ (1 / 2 : ℝ) * N)) := by ring

/-- Exact identity between Heath--Brown's coefficient-one difference moment
and the discrete ratio moment in Guth--Maynard Lemma 11.5. -/
theorem sourceCoefficientOne_differenceMoment_eq_gmR_ratioMoment
    (N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) =
      ∑ n ∈ dyadicInterval N, ∑ m ∈ dyadicInterval N,
        ‖gmR W ((n : ℝ) / m)‖ ^ 2 := by
  have hone : conjugateCoeffs (fun _ => (1 : ℂ)) =
      fun _ => (1 : ℂ) := by
    funext n
    unfold conjugateCoeffs
    exact star_one ℂ
  simp_rw [norm_sourceDirichletPoly_eq_dirichletPoly_conjugateCoeffs, hone]
  rw [← heathBrownDifferenceMoment_dyadic_eq_dirichletPoly]
  calc
    heathBrownDifferenceMoment (dyadicInterval N) W (fun _ => (1 : ℂ)) =
        ∑ n ∈ dyadicInterval N, ∑ m ∈ dyadicInterval N,
          (1 : ℝ) * 1 * heathBrownMajorantKernel W n m := by
      simpa using heathBrownDifferenceMoment_ofReal_eq_kernel_sum
        (dyadicInterval N) W (fun _ => (1 : ℝ))
    _ = _ := by
      simp only [one_mul]
      pm_4079
      apply heathBrownMajorantKernel_eq_norm_gmR_ratio
      · rw [dyadicInterval, Finset.mem_Ioc] at hn
        omega
      · rw [dyadicInterval, Finset.mem_Ioc] at hm
        omega

/-- Exact decomposition of an ordered double sum into its diagonal and
off-diagonal parts. -/
theorem orderedPairSum_eq_diagonal_add_offDiagonal
    {α : Type} [DecidableEq α] (W : Finset α) (f : α → α → ℝ) :
    (∑ t ∈ W, ∑ u ∈ W, f t u) =
      (∑ t ∈ W, f t t) +
        ∑ t ∈ W, ∑ u ∈ W.erase t, f t u := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact (Finset.add_sum_erase W (fun u => f t u) ht).symm

/-- Ordinates in `[0,T]` have pairwise difference at most `T`. -/
theorem abs_sub_le_height_of_mem_baseInterval
    {T : ℝ} {W : Finset ℝ} (hInterval : InBaseInterval T W)
    {t u : ℝ} (ht : t ∈ W) (hu : u ∈ W) :
    |t - u| ≤ T := by
  pm_268 htBounds hInterval t ht huBounds u hu
  rw [Set.mem_Icc] at htBounds huBounds
  rw [abs_le]
  constructor <;> linarith

/-- The exact source-level coefficient-majorant reduction: proving the
coefficient-one analytic estimate proves Heath--Brown's theorem for every
unit-bounded complex sequence. -/
theorem heathBrownDifferenceSetMeanSquare_of_coefficientOne
    (hOne : HeathBrownCoefficientOneMeanSquare) :
    HeathBrownDifferenceSetMeanSquare := by
  intro ε hε
  pm_4083 C T₀ hC hT₀ hOneBound hOne ε hε
  pm_4084
  intro N T W a hN hT hSep hInterval ha
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N a (t - u)‖ ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2 :=
      sourceDirichletPoly_differenceMoment_le_one N W a ha
    _ ≤ C * T ^ ε *
          (((W.card : ℝ) ^ 2 * N) +
            ((W.card : ℝ) * N ^ 2) +
            ((W.card : ℝ) ^ (5 / 4 : ℝ) *
              T ^ (1 / 2 : ℝ) * N)) :=
      hOneBound N T W hN hT hSep hInterval

end GuthMaynard.NativeMoment
