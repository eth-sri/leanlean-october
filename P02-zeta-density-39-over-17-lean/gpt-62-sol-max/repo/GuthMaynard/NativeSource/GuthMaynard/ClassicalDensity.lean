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
public import MathCollab.Density.ZetaJensenInputs

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
  simp only [analyticVanishingOrder]
  apply MathCollab.Density.ZetaGrowth.finset_unit_bin_le_jensen _ (a := 1/2) hT
    (by norm_num) (by norm_num) (by norm_num)
  intro ρ hρ
  obtain ⟨hm, hb, hc⟩ := Finset.mem_filter.mp hρ
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_ZeroRectangle] at hm
  exact ⟨hσLower.trans hm.1.1, hm.1.2.1, hm.1.2.2.1, hm.1.2.2.2, hb, hc⟩

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
  exact hTotal.trans (mul_le_mul_of_nonneg_right hCard
    (MathCollab.Density.ZetaGrowth.jensen_unit_bound_nonneg hT (by norm_num) (by norm_num)))

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
  have hNumerator := MathCollab.Density.ZetaGrowth.jensen_log_height_bound hTPos hLogTwo
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
