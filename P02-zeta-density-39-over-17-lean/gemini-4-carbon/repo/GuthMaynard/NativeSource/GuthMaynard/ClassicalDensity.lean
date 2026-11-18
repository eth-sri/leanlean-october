module
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import GuthMaynard.NativeSource.GuthMaynard.DyadicTransfer
public import GuthMaynard.NativeSource.GuthMaynard.InghamBound
public import GuthMaynard.NativeSource.GuthMaynard.ZeroCount

@[expose] public section

open Complex Finset Filter MeromorphicOn Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace GuthMaynard.NativeMoment

/-- The finite Möbius mollifier used in the classical Ingham zero-density
argument. The lower endpoint excludes the junk value of `Nat`-indexed
Dirichlet monomials at zero. -/
noncomputable def zetaMollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 X,
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)

/-- The finite Möbius mollifier as an arithmetic function. -/
noncomputable def truncatedMoebius (X : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Icc 1 X then
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0
  map_zero' := by simp

@[simp] theorem truncatedMoebius_apply (X n : ℕ) :
    truncatedMoebius X n = if n ∈ Icc 1 X then
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0 := rfl

theorem truncatedMoebius_hasFiniteSupport (X : ℕ) :
    Function.HasFiniteSupport (truncatedMoebius X) := by
  apply Set.Finite.subset (Icc 1 X).finite_toSet
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  by_contra hnMem
  have hnMem' : n ∉ Icc 1 X := by simpa using hnMem
  exact hn (by rw [truncatedMoebius_apply, ite_eq_right hnMem'])

theorem truncatedMoebius_LSeriesSummable (X : ℕ) (s : ℂ) :
    LSeriesSummable (truncatedMoebius X) s := by
  unfold LSeriesSummable
  exact summable_of_hasFiniteSupport <|
    (truncatedMoebius_hasFiniteSupport X).subset (by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn ⊢
      contrapose! hn
      rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
      simp [hn])

/-- The finite-sum definition of the mollifier agrees exactly with its
L-series representation. -/
theorem zetaMollifier_eq_LSeries (X : ℕ) (s : ℂ) :
    zetaMollifier X s = LSeries (truncatedMoebius X) s := by
  rw [zetaMollifier, LSeries, tsum_eq_sum (s := Icc 1 X)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
    simp only [truncatedMoebius_apply, ite_eq_left hn]
  · intro n hn
    rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
    simp [hn]

/-- Ingham's zero-containing auxiliary function
`1 - (ζ M_X - 1)^2 = (2 - ζ M_X) ζ M_X`.  The factored definition makes the
zeta-zero multiplicity transparent. -/
noncomputable def inghamZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  (2 - riemannZeta s * zetaMollifier X s) *
    (riemannZeta s * zetaMollifier X s)

/-- There are no zeta zeros in a rectangle whose real interval is the
singleton `{1}`. -/
theorem zerosInRect_one_eq_empty (T₁ T₂ : ℝ) :
    zerosInRect 1 1 T₁ T₂ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hs
  rcases hs with ⟨hsRect, hsZero⟩
  rw [mem_ZeroRectangle] at hsRect
  exact riemannZeta_ne_zero_of_one_le_re hsRect.1 hsZero

/-- The symmetric zeta-zero count vanishes identically at `σ = 1`. -/
@[simp] theorem N_one (T : ℝ) : N 1 T = 0 := by
  rw [N, zeroCountRect, zerosInRect_one_eq_empty]
  simp

/-- All zeta zeros in one unit-height bin of a positive dyadic slab. -/
noncomputable def zeroUnitBin (σ T : ℝ) (z : ℤ) : Finset ℂ :=
  (zerosInRect σ 1 T (2 * T)).filter
    (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1)

/-- A pole-safe Jensen estimate for every zero in a unit-height bin. Unlike
`typeI_unit_bin_sum_le_jensen`, this theorem has no detector-class filter and
is valid down to the critical line. -/
theorem zeroUnitBin_multiplicity_le_jensen (σ T : ℝ) (z : ℤ)
    (hσLower : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ zeroUnitBin σ T z,
        analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
  let S := zeroUnitBin σ T z
  by_cases hSEmpty : S = ∅
  · change ((∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤ _
    rw [hSEmpty]
    simp only [Finset.sum_empty, Nat.cast_zero]
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hRatio : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
      norm_num at hM ⊢
      nlinarith
    exact div_nonneg (Real.log_nonneg hRatio) hLogDen.le
  · have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    obtain ⟨ρ₀, hρ₀⟩ := hSNonempty
    have hρ₀Data := Finset.mem_filter.mp hρ₀
    have hρ₀Rect : ρ₀ ∈ zerosInRect σ 1 T (2 * T) := hρ₀Data.1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hρ₀Rect
    have hzRange : (z : ℝ) ∈ Set.Icc (T - 1) (2 * T) := by
      constructor
      · linarith [hρ₀Rect.1.2.2.1, hρ₀Data.2.2]
      · linarith [hρ₀Rect.1.2.2.2, hρ₀Data.2.1]
    let c : ℂ := 2 + I * (((z : ℝ) + 1 / 2 : ℝ) : ℂ)
    let U : Set ℂ := Metric.closedBall c (7 / 4 : ℝ)
    have hUAnalytic : AnalyticOnNhd ℂ riemannZeta U := by
      apply analyticOn_riemannZeta.mono
      intro w hw
      have hwNorm : ‖w - c‖ ≤ 7 / 4 := by
        simpa [U, Metric.mem_closedBall, dist_eq_norm] using hw
      have hwImDiff : |w.im - ((z : ℝ) + 1 / 2)| ≤ 7 / 4 := by
        calc
          |w.im - ((z : ℝ) + 1 / 2)| = |(w - c).im| := by simp [c]
          _ ≤ ‖w - c‖ := abs_im_le_norm _
          _ ≤ 7 / 4 := hwNorm
      have hwIm : 1 < w.im := by
        have := (abs_le.mp hwImDiff).1
        linarith [hzRange.1]
      intro hwOne
      subst w
      norm_num at hwIm
    have hcLower : (0.6 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa [c] using euler_product_lower_bound_2 (z : ℝ)
    have hcNe : riemannZeta c ≠ 0 := by
      intro hcZero
      rw [hcZero, norm_zero] at hcLower
      norm_num at hcLower
    have hcOrder : analyticOrderAt riemannZeta c ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hcNe)]
      exact ENat.natCast_ne_top 0
    have hSU : ∀ ρ ∈ S, ρ ∈ Metric.closedBall c (8 / 5 : ℝ) := by
      intro ρ hρ
      have hρData := Finset.mem_filter.mp hρ
      have hρRect : ρ ∈ zerosInRect σ 1 T (2 * T) := hρData.1
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hρRect
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hreLower : -(3 / 2 : ℝ) ≤ (ρ - c).re := by
        norm_num [c]
        linarith [hσLower, hρRect.1.1]
      have hreUpper : (ρ - c).re ≤ -1 := by
        norm_num [c]
        linarith [hρRect.1.2.1]
      have himLower : -(1 / 2 : ℝ) ≤ (ρ - c).im := by
        norm_num [c]
        linarith [hρData.2.1]
      have himUpper : (ρ - c).im ≤ 1 / 2 := by
        norm_num [c]
        linarith [hρData.2.2]
      rw [mul_self_le_mul_self_iff (norm_nonneg _) (by norm_num)]
      rw [Complex.norm_mul_self_eq_normSq, normSq_apply]
      nlinarith [sq_nonneg ((ρ - c).re + 3 / 2),
        sq_nonneg ((ρ - c).im + 1 / 2),
        sq_nonneg ((ρ - c).im - 1 / 2)]
    let V : Set ℂ := Metric.closedBall c (8 / 5 : ℝ)
    have hVAnalytic : AnalyticOnNhd ℂ riemannZeta V :=
      hUAnalytic.mono
        (Metric.closedBall_subset_closedBall (by norm_num : (8 / 5 : ℝ) ≤ 7 / 4))
    have hBridge := finset_analyticVanishingOrder_le_finsum_divisor hVAnalytic
      (isCompact_closedBall c (8 / 5 : ℝ))
      (convex_closedBall c (8 / 5 : ℝ)).isPreconnected (by
        simp only [V, Metric.mem_closedBall, dist_self]
        norm_num) hcOrder S
      (by simpa [V] using hSU)
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hUAnalyticAbs : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall c |(7 / 4 : ℝ)|) := by
      simpa [U, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hUAnalytic
    have hJensen := hUAnalyticAbs.sum_divisor_le
      (r := (8 / 5 : ℝ)) (R := (7 / 4 : ℝ))
      (M := 100 * T ^ (3 : ℝ)) (by norm_num) (by norm_num) hM hcNe (by
        intro w hw
        exact zeta_jensen_sphere_bound T (z : ℝ) hT hzRange w (by
          simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hw))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)] at hJensen
    change ((∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤ _
    refine hBridge.trans (le_trans (by simpa [c, V] using hJensen) ?_)
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    apply div_le_div_of_nonneg_right _ hLogDen.le
    have hMPos : 0 < 100 * T ^ (3 : ℕ) := by positivity
    have hcNormPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcNe
    have hRatioLe : (100 * T ^ (3 : ℕ)) / ‖riemannZeta c‖ ≤
        (100 * T ^ (3 : ℕ)) / (0.6 : ℝ) :=
      div_le_div_of_nonneg_left hMPos.le (by norm_num) hcLower
    exact Real.log_le_log
      (div_pos hMPos (by simpa [c] using hcNormPos)) (by simpa [c] using hRatioLe)

/-- Summing the unit-bin Jensen estimate gives an explicit bound for a full
positive dyadic slab. -/
theorem zeroCountRect_dyadic_le_jensen (σ T : ℝ)
    (hσLower : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (T + 2) *
        (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by
  let S := zerosInRect σ 1 T (2 * T)
  let bins : Finset ℤ := Finset.Icc ⌊T⌋ ⌊2 * T⌋
  let floorIm : ℂ → ℤ := fun ρ => ⌊ρ.im⌋
  let mult : ℂ → ℕ := fun ρ => analyticVanishingOrder riemannZeta ρ
  have hFloorMem : ∀ ρ ∈ S, floorIm ρ ∈ bins := by
    intro ρ hρ
    change ρ ∈ zerosInRect σ 1 T (2 * T) at hρ
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hρ
    change floorIm ρ ∈ Finset.Icc ⌊T⌋ ⌊2 * T⌋
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_mono hρ.1.2.2.1, Int.floor_mono hρ.1.2.2.2⟩
  have hAll : S.filter (fun ρ => floorIm ρ ∈ bins) = S :=
    Finset.filter_eq_self.mpr hFloorMem
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S bins floorIm mult
  rw [hAll] at hFiber
  have hEach : ∀ z ∈ bins,
      ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
        Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    intro z _hz
    have hSubset : S.filter (fun w => floorIm w = z) ⊆ zeroUnitBin σ T z := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rw [zeroUnitBin, Finset.mem_filter]
      refine ⟨by simpa [S] using hρ.1, ?_⟩
      have hFloorLe : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ ρ.im := Int.floor_le ρ.im
      have hLtFloor : ρ.im < ((⌊ρ.im⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one ρ.im
      change (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1
      simpa [floorIm, hρ.2] using And.intro hFloorLe hLtFloor
    have hNat :
        ∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ ≤
          ∑ ρ ∈ zeroUnitBin σ T z, mult ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro _ _ _
      exact Nat.zero_le _
    have hNatReal :
        ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ zeroUnitBin σ T z, mult ρ : ℕ) : ℝ) := by
      exact_mod_cast hNat
    exact hNatReal.trans (by
      simpa [mult] using zeroUnitBin_multiplicity_le_jensen σ T z hσLower hT)
  have hSum :
      ∑ z ∈ bins,
          ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
        ∑ _z ∈ bins,
          Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    exact Finset.sum_le_sum hEach
  have hFiberReal := congrArg (fun n : ℕ => (n : ℝ)) hFiber
  simp only [Nat.cast_sum] at hFiberReal
  have hTotal : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (bins.card : ℝ) *
        (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by
    rw [zeroCountRect]
    change ((∑ ρ ∈ S, mult ρ : ℕ) : ℝ) ≤ _
    calc
      ((∑ ρ ∈ S, mult ρ : ℕ) : ℝ) =
          ∑ ρ ∈ S, (mult ρ : ℝ) := by simp
      _ = ∑ z ∈ bins, ∑ ρ ∈ S.filter (fun w => floorIm w = z),
          (mult ρ : ℝ) := hFiberReal.symm
      _ ≤ ∑ _z ∈ bins,
          Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
        simpa only [Nat.cast_sum] using hSum
      _ = (bins.card : ℝ) *
          (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by simp
  have hab : ⌊T⌋ ≤ ⌊2 * T⌋ + 1 := by
    have hmono : ⌊T⌋ ≤ ⌊2 * T⌋ := Int.floor_mono (by linarith)
    omega
  have hCardInt : (bins.card : ℤ) = ⌊2 * T⌋ + 1 - ⌊T⌋ := by
    simpa [bins] using Int.card_Icc_of_le ⌊T⌋ ⌊2 * T⌋ hab
  have hCardReal : (bins.card : ℝ) =
      (⌊2 * T⌋ : ℝ) + 1 - (⌊T⌋ : ℝ) := by
    exact_mod_cast hCardInt
  have hCard : (bins.card : ℝ) ≤ T + 2 := by
    rw [hCardReal]
    have hUpper : (⌊2 * T⌋ : ℝ) ≤ 2 * T := Int.floor_le (2 * T)
    have hLower : T - 1 < (⌊T⌋ : ℝ) := Int.sub_one_lt_floor T
    linarith
  have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    apply Real.log_pos
    norm_num
  have hM : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
    have hTPos : 0 < T := by linarith
    have : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      nlinarith [sq_nonneg T]
    norm_num at this ⊢
    nlinarith
  have hJNonneg : 0 ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
    div_nonneg (Real.log_nonneg hM) hLogDen.le
  exact hTotal.trans (mul_le_mul_of_nonneg_right hCard hJNonneg)

/-- The full positive dyadic zeta-zero count is `T^(1+ε)`-bounded uniformly
for every fixed vertical line at or to the right of the critical line. -/
theorem dyadic_zero_count_epsilon_one (σ : ℝ) (hσLower : 1 / 2 ≤ σ) :
    EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ (1 : ℝ)) := by
  intro ε hε
  let D : ℝ := Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))
  let C : ℝ := 125 / (D * ε)
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hC : 0 < C := div_pos (by norm_num) (mul_pos hD hε)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_ge_atTop (max (Real.exp 2) 8)] with T hT
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hT
  have hTExp : Real.exp 2 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTNonneg : 0 ≤ T := hTPos.le
  have hLogTwo : 2 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) hTExp
    simpa using this
  have hNumerator :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) ≤ 100 * Real.log T := by
    have hConst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500 / 3 by norm_num)
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) =
          Real.log ((500 / 3 : ℝ) * T ^ (3 : ℝ)) := by
        congr 1
        ring
      _ = Real.log (500 / 3 : ℝ) + Real.log (T ^ (3 : ℝ)) := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTPos 3).ne']
      _ = Real.log (500 / 3 : ℝ) + 3 * Real.log T := by
        rw [Real.log_rpow hTPos]
      _ ≤ 100 * Real.log T := by nlinarith
  have hJensenBound :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) / D ≤
        100 * Real.log T / D :=
    div_le_div_of_nonneg_right hNumerator hD.le
  have hLogPow : Real.log T ≤ T ^ ε / ε :=
    Real.log_le_rpow_div hTNonneg hε
  have hRaw := zeroCountRect_dyadic_le_jensen σ T hσLower hTEight
  have hCount : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      C * (T ^ ε * T) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          (T + 2) *
            (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) / D) := by
        simpa [D] using hRaw
      _ ≤ (T + 2) * (100 * Real.log T / D) := by
        exact mul_le_mul_of_nonneg_left hJensenBound (by linarith)
      _ ≤ ((5 / 4 : ℝ) * T) * (100 * (T ^ ε / ε) / D) := by
        gcongr
        · linarith
      _ = C * (T ^ ε * T) := by
        dsimp [C]
        field_simp [hD.ne', hε.ne']
        ring
  calc
    ‖|(zeroCountRect σ 1 T (2 * T) : ℝ)|‖ =
        (zeroCountRect σ 1 T (2 * T) : ℝ) := by
      simp
    _ ≤ C * (T ^ ε * T) := hCount
    _ = C * ‖T ^ ε * |T ^ (1 : ℝ)|‖ := by
      rw [Real.rpow_one, abs_of_nonneg hTNonneg, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hTNonneg ε) hTNonneg)]

/-- The coarse exponent-one estimate for the full symmetric count, obtained
from the dyadic Jensen bound. -/
theorem global_zero_count_epsilon_one (σ : ℝ) (hσLower : 1 / 2 ≤ σ) :
    EpsilonPowerBound (fun T => (N σ T : ℝ)) (fun T => T ^ (1 : ℝ)) :=
  dyadicToGlobalZeroCount σ 1 (by norm_num) (dyadic_zero_count_epsilon_one σ hσLower)

/-- The `σ = 1/2` endpoint required by Ingham's density theorem. -/
theorem ingham_zero_density_at_half_native :
    EpsilonPowerBound (fun T => (N (1 / 2) T : ℝ))
      (fun T => T ^ (3 * (1 - (1 / 2 : ℝ)) / (2 - 1 / 2))) := by
  convert global_zero_count_epsilon_one (1 / 2) (by norm_num) using 1
  norm_num

end GuthMaynard.NativeMoment
