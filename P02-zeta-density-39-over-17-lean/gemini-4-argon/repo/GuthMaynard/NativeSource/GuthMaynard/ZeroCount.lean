module
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Complex.Basic
-- Force rebuild
public import Mathlib.Data.Finset.Basic
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import GuthMaynard.NativeSource.GuthMaynard.ZetaBounds
public import MathCollab.Density.ZetaJensenInputs
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

open Complex Filter MeromorphicOn
open scoped Topology ArithmeticFunction.Moebius ComplexOrder

namespace GuthMaynard.NativeMoment

/-- A precise rectangle in the complex plane: σ_min ≤ Re(s) ≤ σ_max, T_min ≤ Im(s) ≤ T_max -/
def ZeroRectangle (σ_min σ_max T_min T_max : ℝ) : Set ℂ :=
  { s : ℂ | σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max }

lemma mem_ZeroRectangle (σ_min σ_max T_min T_max : ℝ) (s : ℂ) :
  s ∈ ZeroRectangle σ_min σ_max T_min T_max ↔ σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max := by
  rfl

lemma ZeroRectangle_subset (σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 : ℝ)
  (h_sigma_min : σ_min2 ≤ σ_min1)
  (h_sigma_max : σ_max1 ≤ σ_max2)
  (h_T_min : T_min2 ≤ T_min1)
  (h_T_max : T_max1 ≤ T_max2) :
  ZeroRectangle σ_min1 σ_max1 T_min1 T_max1 ⊆ ZeroRectangle σ_min2 σ_max2 T_min2 T_max2 := by
  intro s hs
  rw [mem_ZeroRectangle] at hs ⊢
  rcases hs with ⟨h1, h2, h3, h4⟩
  exact ⟨le_trans h_sigma_min h1, le_trans h2 h_sigma_max, le_trans h_T_min h3, le_trans h4 h_T_max⟩

lemma isCompact_ZeroRectangle (σ_min σ_max T_min T_max : ℝ) :
    IsCompact (ZeroRectangle σ_min σ_max T_min T_max) := by
  have hRectangle :
      ZeroRectangle σ_min σ_max T_min T_max =
        Set.Icc σ_min σ_max ×ℂ Set.Icc T_min T_max := by
    ext z
    simp [ZeroRectangle, Complex.mem_reProdIm, and_assoc]
  rw [hRectangle]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- Analytic order of vanishing for a complex function. -/
noncomputable def analyticVanishingOrder (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  analyticOrderNatAt f s

export MathCollab.Density.ZetaGrowth (zeta_jensen_sphere_bound moebius_coeff_norm_le_one
  moebius_LSeries_norm_lt_five_thirds euler_product_lower_bound_2)
alias finset_analyticVanishingOrder_le_finsum_divisor :=
  MathCollab.Density.ZetaGrowth.finset_analyticOrderNatAt_le_finsum_divisor

/-- The zeros of the Riemann zeta function in a compact rectangle form a finite set. -/
theorem riemannZeta_finite_zeros_in_rect (σ_min σ_max T_min T_max : ℝ) :
    (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite := by
  simpa only [riemannZetaZeros, Set.preimage, Set.mem_singleton_iff] using
    (isCompact_ZeroRectangle σ_min σ_max T_min T_max).inter_riemannZetaZeros_finite

open scoped BigOperators

/-- The exact finite set of distinct zeros in a bounded rectangle. -/
noncomputable def zerosInRect (σ_min σ_max T_min T_max : ℝ) : Finset ℂ :=
  (riemannZeta_finite_zeros_in_rect σ_min σ_max T_min T_max).toFinset

/-- Number of zeros in the rectangle counting analytical multiplicity. -/
noncomputable def zeroCountRect (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  ∑ s ∈ zerosInRect σ_min σ_max T_min T_max, analyticVanishingOrder riemannZeta s

lemma zerosInRect_subset_of_rect_subset (σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 : ℝ)
  (h : ZeroRectangle σ_min1 σ_max1 T_min1 T_max1 ⊆ ZeroRectangle σ_min2 σ_max2 T_min2 T_max2) :
  zerosInRect σ_min1 σ_max1 T_min1 T_max1 ⊆ zerosInRect σ_min2 σ_max2 T_min2 T_max2 := by
  intro s
  rw [zerosInRect, zerosInRect, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_inter_iff]
  rintro ⟨h1, h2⟩
  exact ⟨h h1, h2⟩

lemma zeroCountRect_mono (σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 : ℝ)
  (h_sigma_min : σ_min2 ≤ σ_min1)
  (h_sigma_max : σ_max1 ≤ σ_max2)
  (h_T_min : T_min2 ≤ T_min1)
  (h_T_max : T_max1 ≤ T_max2) :
  zeroCountRect σ_min1 σ_max1 T_min1 T_max1 ≤ zeroCountRect σ_min2 σ_max2 T_min2 T_max2 := by
  unfold zeroCountRect
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply zerosInRect_subset_of_rect_subset
    exact ZeroRectangle_subset σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 h_sigma_min h_sigma_max h_T_min h_T_max
  · intro s _ _
    exact Nat.zero_le _

lemma zerosInRect_subset (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zerosInRect σ_min σ_max T₁ T₃ ⊆ zerosInRect σ_min σ_max T₁ T₂ ∪ zerosInRect σ_min σ_max T₂ T₃ := by
  intro s
  rw [zerosInRect, zerosInRect, zerosInRect, Finset.mem_union, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
      ZeroRectangle, ZeroRectangle, ZeroRectangle, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  rintro ⟨⟨hσ1, hσ2, hT1, hT3⟩, hzero⟩
  by_cases h : s.im ≤ T₂
  · left; exact ⟨⟨hσ1, hσ2, hT1, h⟩, hzero⟩
  · right; push Not at h; exact ⟨⟨hσ1, hσ2, le_of_lt h, hT3⟩, hzero⟩

lemma zeroCountRect_split (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zeroCountRect σ_min σ_max T₁ T₃ ≤ zeroCountRect σ_min σ_max T₁ T₂ + zeroCountRect σ_min σ_max T₂ T₃ := by
  unfold zeroCountRect
  have h1 : ∑ s ∈ zerosInRect σ_min σ_max T₁ T₃, analyticVanishingOrder riemannZeta s ≤ ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂ ∪ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact zerosInRect_subset σ_min σ_max T₁ T₂ T₃
    · intros; exact Nat.zero_le _
  have h2 : ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂ ∪ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s + ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂ ∩ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s = ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂, analyticVanishingOrder riemannZeta s + ∑ s ∈ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s := Finset.sum_union_inter
  omega

/-- The classical zero-counting function N(σ, T): number of zeros (with analytic multiplicity)
    with Re(s) ≥ σ and |Im(s)| ≤ T (i.e. -T ≤ Im(s) ≤ T). -/
noncomputable def N (σ T : ℝ) : ℕ :=
  zeroCountRect σ 1 (-T) T

/-- Conjugating both the argument and value of zeta gives an analytic function
on the complement of the pole. -/
private noncomputable def conjugateRiemannZeta (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z))

theorem riemannZeta_conj (z : ℂ) (_hz : z ≠ 1) :
    riemannZeta (star z) = star (riemannZeta z) :=
  _root_.riemannZeta_conj z

theorem iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n.succ by omega, iteratedDeriv_succ, ih,
        deriv_conj_conj, ← iteratedDeriv_succ]

theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) :
    analyticOrderAt ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) (star z) =
      analyticOrderAt f z := by
  let g := (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)
  have hg : AnalyticAt ℂ g (star z) := by
    change AnalyticAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) (star z)
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hfd := Complex.analyticAt_iff_eventually_differentiableAt.mp hf
    have ht : Tendsto (starRingEnd ℂ) (𝓝 (star z)) (𝓝 z) := by
      have ht0 : Tendsto (starRingEnd ℂ) (𝓝 (star z)) (𝓝 (star (star z))) := Complex.continuous_conj.continuousAt
      simpa using ht0
    filter_upwards [ht.eventually hfd] with w hw
    exact differentiableAt_conj_conj_iff.mpr hw
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  constructor
  · intro h i hi
    have hgi := h i hi
    rw [iteratedDeriv_conj_conj f i] at hgi
    simpa [Function.comp_apply] using congrArg star hgi
  · intro h i hi
    rw [iteratedDeriv_conj_conj f i]
    simp [Function.comp_apply, h i hi]

theorem analyticVanishingOrder_conj (z : ℂ) (hz : z ≠ 1) :
    analyticVanishingOrder riemannZeta (star z) =
      analyticVanishingOrder riemannZeta z := by
  have hEvent : riemannZeta =ᶠ[𝓝 (star z)] conjugateRiemannZeta :=
    Filter.EventuallyEq.of_eq (funext fun w => by
      simp [conjugateRiemannZeta, _root_.riemannZeta_conj])
  have hAnalytic : AnalyticAt ℂ riemannZeta z :=
    analyticOn_riemannZeta z (by simpa using hz)
  exact congrArg ENat.toNat ((analyticOrderAt_congr hEvent).trans
    (analyticOrderAt_conj_conj riemannZeta z hAnalytic))

/-- Negative and positive ordinate rectangles contain the same zeta-zero
multiplicity, by conjugation. -/
theorem zeroCountRect_neg_eq_pos (σ T : ℝ) :
    zeroCountRect σ 1 (-T) 0 = zeroCountRect σ 1 0 T := by
  unfold zeroCountRect
  have hNegPos : ∀ z ∈ zerosInRect σ 1 (-T) 0, star z ∈ zerosInRect σ 1 0 T := by
    intro z hz
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hz ⊢
    rcases hz with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect ⊢
    change riemannZeta z = 0 at hzZero
    have hzNe : z ≠ 1 := by
      intro h
      subst z
      exact riemannZeta_one_ne_zero hzZero
    refine ⟨⟨by simpa using hzRect.1, by simpa using hzRect.2.1,
      by simp; linarith, by simp; linarith⟩, ?_⟩
    change riemannZeta (star z) = 0
    rw [riemannZeta_conj z hzNe, hzZero]
    simp
  have hPosNeg : ∀ z ∈ zerosInRect σ 1 0 T, star z ∈ zerosInRect σ 1 (-T) 0 := by
    intro z hz
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hz ⊢
    rcases hz with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect ⊢
    change riemannZeta z = 0 at hzZero
    have hzNe : z ≠ 1 := by
      intro h
      subst z
      exact riemannZeta_one_ne_zero hzZero
    refine ⟨⟨by simpa using hzRect.1, by simpa using hzRect.2.1,
      by simp; linarith, by simp; linarith⟩, ?_⟩
    change riemannZeta (star z) = 0
    rw [riemannZeta_conj z hzNe, hzZero]
    simp
  exact Finset.sum_bij' (fun z _ => star z) (fun z _ => star z)
    hNegPos hPosNeg
    (fun z _ => by simp)
    (fun z _ => by simp)
    (fun z hz => by
      have hzNe : z ≠ 1 := by
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hz
        have hzZero : riemannZeta z = 0 := hz.2
        intro h
        subst z
        exact riemannZeta_one_ne_zero hzZero
      exact (analyticVanishingOrder_conj z hzNe).symm)

/-- Iterating `zeroCountRect_split` decomposes a positive-height rectangle into
the fixed low rectangle `[0,1]` and the first `m` dyadic slabs. -/
theorem zeroCountRect_zero_two_pow_le (σ : ℝ) (m : ℕ) :
    zeroCountRect σ 1 0 (((2 : ℕ) ^ m : ℕ) : ℝ) ≤
      zeroCountRect σ 1 0 1 +
        ∑ i ∈ Finset.range m,
          zeroCountRect σ 1 (((2 : ℕ) ^ i : ℕ) : ℝ)
            (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hSplit := zeroCountRect_split σ 1 0
        (((2 : ℕ) ^ m : ℕ) : ℝ) (((2 : ℕ) ^ (m + 1) : ℕ) : ℝ)
      rw [Finset.sum_range_succ]
      omega

/- 
F-02: Dyadic zero reduction proposition.
This is mathematically redundant as a standalone assumption.
The partition of the total zero count N(σ, T) into dyadic slabs
is an internal algebraic step deferred to the AlgebraicCombinationHypothesis proof.
-/

/-- Bound for zeta in the right half-plane `Re(s) ≥ 2`, obtained by comparing
the absolutely convergent Dirichlet series termwise with the series at `2`. -/
theorem zeta_right_half_plane_bound (σ t : ℝ) (hσ : σ ≥ 2) :
    ‖riemannZeta (σ + t * I)‖ ≤ 2 := by
  let s : ℂ := σ + t * I
  have hsRe : s.re = σ := by simp [s]
  have hs : 1 < s.re := by rw [hsRe]; linarith
  have hSumS : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hSumTwo : LSeriesSummable 1 (2 : ℂ) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  rw [← LSeries_one_eq_riemannZeta hs, LSeries]
  calc
    ‖∑' n, LSeries.term 1 s n‖ ≤ ∑' n, ‖LSeries.term 1 s n‖ :=
      norm_tsum_le_tsum_norm hSumS.norm
    _ ≤ ∑' n, ‖LSeries.term 1 (2 : ℂ) n‖ := by
      apply hSumS.norm.tsum_le_tsum _ hSumTwo.norm
      intro n
      exact LSeries.norm_term_le_of_re_le_re 1 (by simpa [hsRe] using hσ) n
    _ = (LSeries 1 (2 : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hSumTwo]
      apply tsum_congr
      intro n
      have hn : (0 : ℂ) ≤ LSeries.term 1 (2 : ℝ) n :=
        LSeries.term_nonneg (by simp) 2
      have heq := congrArg Complex.re (Complex.norm_of_nonneg' hn)
      simpa using heq
    _ = (riemannZeta (2 : ℂ)).re := by
      rw [LSeries_one_eq_riemannZeta (by norm_num)]
    _ = Real.pi ^ 2 / 6 := by
      rw [riemannZeta_two]
      norm_cast
    _ ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

