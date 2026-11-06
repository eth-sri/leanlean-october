module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.NumberTheory.Harmonic.Bounds
public import GuthMaynard.NativeSource.GuthMaynard.HalaszMontgomery
public import GuthMaynard.NativeSource.GuthMaynard.LogarithmicKernel
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightedGram
public import MathCollab.Density.Stronger.Fourth.PrefixMean
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Finset Set
open scoped ComplexConjugate

namespace GuthMaynard.NativeMoment

/-!
# Classical Montgomery--Halász--Huxley large values

This file proves the finite large-values estimate used by the classical
zero-density argument.  Its analytic input is the pair of kernel estimates in
`LogarithmicKernel`; all remaining arguments here are finite duality,
separated-set counting, localization, and subdivision.
-/

export MathCollab.Density.Stronger.Atkinson (sum_norm_sq_sum_le_gram phaseAlign_mul norm_phaseAlign_le_one phaseAlign)

private theorem norm_conj_eq (z : ℂ) : ‖conj z‖ = ‖z‖ := by simp_all

export MathCollab.Density.Stronger.Fourth (norm_sum_mul_sq_le)

private theorem dirichletPoly_eq_logarithmicPhase
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPoly N a t =
      ∑ n ∈ dyadicInterval N, a n * unitaryPhase (logarithmicPhase t n) := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  pm_4835
  exact (unitaryPhase_logarithmicPhase_eq_cpow t n hnPos).symm

private theorem logarithmicPhase_sub (t u : ℝ) (n : ℕ) :
    logarithmicPhase u n - logarithmicPhase t n = logarithmicPhase (u - t) n := by
  simp only [logarithmicPhase]
  ring

theorem logarithmicPhase_gram_eq_kernel (N : ℕ) (t u : ℝ) :
    (∑ n ∈ dyadicInterval N,
        conj (unitaryPhase (logarithmicPhase t n)) *
          unitaryPhase (logarithmicPhase u n)) =
      logarithmicKernel N (u - t) := by
  unfold logarithmicKernel
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm, ← unitaryPhase_sub, logarithmicPhase_sub]
  pm_4835
  exact unitaryPhase_logarithmicPhase_eq_cpow (u - t) n hnPos

/-- Phase-aligned finite Halász--Montgomery duality, specialized to the
project's dyadic Dirichlet polynomials. -/
theorem halasz_montgomery_duality
    (N : ℕ) (V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    ((W.card : ℝ) * V) ^ 2 ≤
      (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖ := by
  let D : ℝ → ℂ := fun t => dirichletPoly N a t
  let c : ℝ → ℂ := fun t => phaseAlign (D t)
  let y : ℝ → ℕ → ℂ := fun t n => unitaryPhase (logarithmicPhase t n)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := by
    intro t ht
    exact norm_phaseAlign_le_one (D t)
  have hsumNorm : (W.card : ℝ) * V ≤ ∑ t ∈ W, ‖D t‖ := by
    calc
      (W.card : ℝ) * V = ∑ t ∈ W, V := by simp
      _ ≤ ∑ t ∈ W, ‖D t‖ := Finset.sum_le_sum fun t ht => hLarge t ht
  have halign :
      ‖∑ t ∈ W, c t * D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have heq : (∑ t ∈ W, c t * D t) = ((∑ t ∈ W, ‖D t‖ : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro t ht
      exact phaseAlign_mul (D t)
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hexpand :
      (∑ t ∈ W, c t * D t) =
        ∑ n ∈ dyadicInterval N, a n * (∑ t ∈ W, c t * y t n) := by
    simp only [D, dirichletPoly_eq_logarithmicPhase, y, Finset.mul_sum]
    pm_4842 Finset.sum_comm n hn t ht
    ring
  have hcs := norm_sum_mul_sq_le (dyadicInterval N) a
    (fun n => ∑ t ∈ W, c t * y t n)
  rw [← hexpand] at hcs
  have hgram := sum_norm_sq_sum_le_gram (dyadicInterval N) W c y hc
  have hcorr : ∀ t ∈ W, ∀ u ∈ W,
      (∑ n ∈ dyadicInterval N, conj (y t n) * y u n) =
        logarithmicKernel N (u - t) := by
    intro t ht u hu
    exact logarithmicPhase_gram_eq_kernel N t u
  have hgram' :
      (∑ n ∈ dyadicInterval N, ‖∑ t ∈ W, c t * y t n‖ ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖ := by
    calc
      _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          ‖∑ n ∈ dyadicInterval N, conj (y t n) * y u n‖ := hgram
      _ = _ := by
        pm_4279
        rw [hcorr t ht u hu]
  have henergy : 0 ≤ ∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2 := by positivity
  calc
    ((W.card : ℝ) * V) ^ 2 ≤ ‖∑ t ∈ W, c t * D t‖ ^ 2 := by
      rw [halign]
      have hleft : 0 ≤ (W.card : ℝ) * V := mul_nonneg (by positivity) hV
      have hright : 0 ≤ ∑ t ∈ W, ‖D t‖ := by positivity
      nlinarith
    _ ≤ (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        (∑ n ∈ dyadicInterval N, ‖∑ t ∈ W, c t * y t n‖ ^ 2) := hcs
    _ ≤ (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖ :=
      mul_le_mul_of_nonneg_left hgram' henergy

private theorem separated_subset_card_le_one_of_diameter
    (W S : Finset ℝ) (hSep : IsSeparated 1 W) (hSW : S ⊆ W)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| < 1) :
    S.card ≤ 1 := by
  pm_4795

/-- A unit-width annulus about a point contains at most one separated point on
each side. -/
theorem separated_annulus_card_le_two
    (W : Finset ℝ) (t : ℝ) (k : ℕ) (hSep : IsSeparated 1 W) :
    ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}).card ≤ 2 := by
  let S := {u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}
  pm_8591 t
  have hpos : (S.filter P).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter W (S.filter P) hSep
    pm_6766
    · intro x hx y hy
      pm_5883
      rw [abs_of_nonneg (sub_nonneg.mpr hxData.2)] at hxS
      rw [abs_of_nonneg (sub_nonneg.mpr hyData.2)] at hyS
      pm_7863
  have hneg : (S.filter (fun u => ¬ P u)).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter W (S.filter (fun u => ¬ P u)) hSep
    pm_6766
    · intro x hx y hy
      pm_5883
      have hxt : x - t ≤ 0 := by linarith
      have hyt : y - t ≤ 0 := by linarith
      rw [abs_of_nonpos hxt] at hxS
      rw [abs_of_nonpos hyt] at hyS
      pm_7863
  pm_7009

section
variable (N : ℕ) (W : Finset ℝ)
include N W
/-- The reciprocal distances from one point to the other separated points in
its `N`-neighborhood have harmonic, rather than linear, total mass. -/
theorem sum_inv_distance_near_le_harmonic (t : ℝ) (hSep : IsSeparated 1 W) (ht : t ∈ W) :
    (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}, 1 / |u - t|) ≤
      2 * (((harmonic N : ℚ) : ℝ)) := by
  let S := {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}
  pm_1481 t
  have hmaps : ∀ u ∈ S, shell u ∈ Finset.Icc 1 N := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have hu := huData.1
    have hne := huData.2.1
    have hsep := hSep t ht u hu (Ne.symm hne)
    have hqOne : 1 ≤ |u - t| := by simpa only [Real.dist_eq, abs_sub_comm] using hsep
    pm_5905 hqNonneg u t
    have hfloorPos : 0 < shell u := by
      exact Nat.floor_pos.mpr hqOne
    have hfloorLeReal : ((shell u : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact (Nat.floor_le hqNonneg).trans huData.2.2
    have hfloorLe : shell u ≤ N := by exact_mod_cast hfloorLeReal
    exact Finset.mem_Icc.mpr ⟨hfloorPos, hfloorLe⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun u => 1 / |u - t|)]
  calc
    (∑ k ∈ Finset.Icc 1 N, ∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
        ∑ k ∈ Finset.Icc 1 N, 2 * (1 / (k : ℝ)) := by
      apply Finset.sum_le_sum
      pm_7579 k hk hkPos
      have hfiberCard : ({u ∈ S | shell u = k}).card ≤ 2 := by
        calc
          ({u ∈ S | shell u = k}).card ≤
              ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧
                |u - t| < (k : ℝ) + 1}).card := by
            apply Finset.card_le_card
            pm_4796
            pm_4932 hlow hfloor hqNonneg hhigh
          _ ≤ 2 := separated_annulus_card_le_two W t k hSep
      calc
        (∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
            ∑ u ∈ S with shell u = k, 1 / (k : ℝ) := by
          apply Finset.sum_le_sum
          pm_4796
          have hkq : (k : ℝ) ≤ |u - t| := by
            rw [← hfloor]
            exact Nat.floor_le hqNonneg
          exact one_div_le_one_div_of_le (by exact_mod_cast hkPos) hkq
        _ = (({u ∈ S | shell u = k}).card : ℝ) * (1 / (k : ℝ)) := by simp
        _ ≤ 2 * (1 / (k : ℝ)) := by
          gcongr
          exact_mod_cast hfiberCard
    _ = 2 * (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [inv_eq_one_div]
      rw [Finset.mul_sum]

/-- Row-sum bound for the logarithmic Gram kernel on a localized interval.
The near terms contribute a harmonic loss; the far terms are controlled by
the B-process and are small enough to be absorbed after choosing the interval
length. -/
theorem logarithmicKernel_row_sum_le (t A L : ℝ) (hN : 0 < N)
    (hSep : IsSeparated 1 W) (ht : t ∈ W)
    (hInterval : ∀ u ∈ W, u ∈ Set.Icc A (A + L))
    (hLN : L ≤ (N : ℝ) ^ 2) :
    (∑ u ∈ W, ‖logarithmicKernel N (u - t)‖) ≤
      (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
        100 * (W.card : ℝ) * Real.sqrt L := by
  have hpoint : ∀ u ∈ W,
      ‖logarithmicKernel N (u - t)‖ ≤
        (if u = t then (N : ℝ) else 0) +
          6 * Real.pi * (N : ℝ) *
            (if u ≠ t ∧ |u - t| ≤ (N : ℝ) then 1 / |u - t| else 0) +
          100 * Real.sqrt L := by
    intro u hu
    by_cases hut : u = t
    · subst u
      rw [sub_self, norm_logarithmicKernel_zero]
      pm_93 ite_true ne_eq not_true_eq_false false_and ite_false
      nlinarith [Real.sqrt_nonneg L]
    · have hsep := hSep u hu t ht hut
      have hqOne : 1 ≤ |u - t| := hsep
      by_cases hqN : |u - t| ≤ (N : ℝ)
      · simp [hut, hqN]
        exact (norm_logarithmicKernel_le_div N (u - t) hN (by simpa using hqOne) (by simpa using hqN)).trans
          (le_add_of_nonneg_right (by positivity : 0 ≤ 100 * Real.sqrt L))
      · have hNt : (N : ℝ) ≤ |u - t| := le_of_not_ge hqN
        pm_268 huI hInterval u hu htI t ht
        pm_5754 hqL L
        have hqN2 : |u - t| ≤ (N : ℝ) ^ 2 := hqL.trans hLN
        have hfar := norm_logarithmicKernel_le_sqrt N (u - t) hN
          (by simpa using hNt) (by simpa using hqN2)
        have hsqrt : Real.sqrt |u - t| ≤ Real.sqrt L := Real.sqrt_le_sqrt hqL
        pm_316 hut ite_false hqN and_false zero_add mul_zero
        exact hfar.trans (by gcongr)
  calc
    (∑ u ∈ W, ‖logarithmicKernel N (u - t)‖) ≤
        ∑ u ∈ W, ((if u = t then (N : ℝ) else 0) +
          6 * Real.pi * (N : ℝ) *
            (if u ≠ t ∧ |u - t| ≤ (N : ℝ) then 1 / |u - t| else 0) +
          100 * Real.sqrt L) := Finset.sum_le_sum hpoint
    _ = (N : ℝ) + 6 * Real.pi * (N : ℝ) *
          (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}, 1 / |u - t|) +
          100 * (W.card : ℝ) * Real.sqrt L := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq', ite_eq_left ht]
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      rw [← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ (N : ℝ) + 6 * Real.pi * (N : ℝ) *
          (2 * (((harmonic N : ℚ) : ℝ))) +
          100 * (W.card : ℝ) * Real.sqrt L := by
      gcongr
      exact sum_inv_distance_near_le_harmonic N W t hSep ht
    _ = (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
          100 * (W.card : ℝ) * Real.sqrt L := by ring
end

/-- Localized large-value count after absorption of the B-process term. -/
theorem local_classical_large_values
    (N : ℕ) (V A L : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hV : 0 < V)
    (hSep : IsSeparated 1 W)
    (hInterval : ∀ t ∈ W, t ∈ Set.Icc A (A + L))
    (hLN : L ≤ (N : ℝ) ^ 2)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖)
    (hAbsorb : 200 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) * Real.sqrt L ≤ V ^ 2) :
    (W.card : ℝ) ≤
      2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2 := by
  by_cases hW : W = ∅
  · subst W
    pm_4797
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let R : ℝ := W.card
  pm_6526
  let B : ℝ := (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW))
  pm_82 hG G
  have hB : 0 ≤ B := by
    dsimp only [B]
    pm_4797
    positivity
  have hdual := halasz_montgomery_duality N V W a hV.le hLarge
  have hrows :
      (∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖) ≤
        R * (B + 100 * R * Real.sqrt L) := by
    calc
      _ ≤ ∑ t ∈ W, (B + 100 * R * Real.sqrt L) := by
        apply Finset.sum_le_sum
        intro t ht
        simpa only [B, R] using
          logarithmicKernel_row_sum_le N W t A L hN hSep ht hInterval hLN
      _ = R * (B + 100 * R * Real.sqrt L) := by
        simp only [sum_const, nsmul_eq_mul, R]
  have hmain : (R * V) ^ 2 ≤ G * (R * (B + 100 * R * Real.sqrt L)) := by
    exact hdual.trans (mul_le_mul_of_nonneg_left hrows hG)
  have hhalf :
      100 * G * R ^ 2 * Real.sqrt L ≤ (V ^ 2 / 2) * R ^ 2 := by
    have habs : 100 * G * Real.sqrt L ≤ V ^ 2 / 2 := by
      change 200 * G * Real.sqrt L ≤ V ^ 2 at hAbsorb
      nlinarith
    calc
      100 * G * R ^ 2 * Real.sqrt L =
          (100 * G * Real.sqrt L) * R ^ 2 := by ring
      _ ≤ (V ^ 2 / 2) * R ^ 2 :=
        mul_le_mul_of_nonneg_right habs (sq_nonneg R)
  have hcancel : R * V ^ 2 ≤ 2 * G * B := by
    have hquad : R ^ 2 * V ^ 2 ≤ 2 * G * R * B := by
      nlinarith [hmain, hhalf]
    have hfactored : R * (R * V ^ 2) ≤ R * (2 * G * B) := by
      nlinarith
    exact le_of_mul_le_mul_left hfactored hR
  change R ≤ 2 * G * B / V ^ 2
  rw [le_div_iff₀ (sq_pos_of_pos hV)]
  simpa only [mul_assoc] using hcancel

section
variable (N : ℕ)
include N
/-- Subdivision of `[0,T]` into equal real intervals transfers the local
absorbed estimate to the full separated set. -/
theorem classical_large_values_of_local_scale (T V L : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hV : 0 < V) (hL : 0 < L)
    (hLN : L ≤ (N : ℝ) ^ 2)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖)
    (hAbsorb : 200 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) * Real.sqrt L ≤ V ^ 2) :
    (W.card : ℝ) ≤
      ((Nat.floor (T / L) + 1 : ℕ) : ℝ) *
        (2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2) := by
  pm_726
  pm_4800 hL
  have hfiber (k : ℕ) (hk : k ∈ Finset.range K) :
      (({t ∈ W | bin t = k}).card : ℝ) ≤
        2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2 := by
    pm_4799
    have hWkInterval : ∀ t ∈ Wk, t ∈ Set.Icc ((k : ℝ) * L) ((k : ℝ) * L + L) := by
      pm_1508 hL.le
      pm_4798
      pm_8285 hL
      · rw [hbin] at hhighFloor
        have := (div_lt_iff₀ hL).mp hhighFloor
        nlinarith
    have hWkLarge : ∀ t ∈ Wk, V ≤ ‖dirichletPoly N a t‖ := by
      intro t ht
      exact hLarge t (Finset.mem_filter.mp ht).1
    change (Wk.card : ℝ) ≤ _
    exact local_classical_large_values N V ((k : ℝ) * L) L Wk a hN hV hWkSep
      hWkInterval hLN hWkLarge hAbsorb
  pm_947
  calc
    (W.card : ℝ) = ∑ k ∈ Finset.range K, (({t ∈ W | bin t = k}).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ k ∈ Finset.range K,
        (2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2) := by
      exact Finset.sum_le_sum hfiber
    _ = ((Nat.floor (T / L) + 1 : ℕ) : ℝ) *
        (2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2) := by
      simp only [sum_const, card_range, nsmul_eq_mul, K]

theorem dyadic_energy_le_length (a : ℕ → ℂ)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) :
    (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) ≤ (N : ℝ) := by
  calc
    (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) ≤
        ∑ n ∈ dyadicInterval N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [ha n hn, norm_nonneg (a n)]
    _ = (N : ℝ) := by
      pm_188 sum_const nsmul_eq_mul mul_one dyadicInterval Nat.card_Ioc
      pm_7564

/-- A nonempty set of values of height at least `V` forces the coefficient
energy to be at least `V²/N`. -/
theorem threshold_sq_le_length_mul_energy (V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hV : 0 ≤ V) (hW : W.Nonempty)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    V ^ 2 ≤ (N : ℝ) * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) := by
  obtain ⟨t, ht⟩ := hW
  have hcs := norm_sum_mul_sq_le (dyadicInterval N) a
    (fun n => unitaryPhase (logarithmicPhase t n))
  rw [← dirichletPoly_eq_logarithmicPhase] at hcs
  have hphase :
      (∑ n ∈ dyadicInterval N, ‖unitaryPhase (logarithmicPhase t n)‖ ^ 2) =
        (N : ℝ) := by
    simp only [norm_unitaryPhase, one_pow, sum_const, nsmul_eq_mul, mul_one,
      dyadicInterval, Nat.card_Ioc]
    pm_7564
  rw [hphase] at hcs
  have hlarge := hLarge t ht
  have hnorm : 0 ≤ ‖dirichletPoly N a t‖ := norm_nonneg _
  nlinarith
end

/-- The Huxley (`V⁻⁶`) branch for bounded coefficients. -/
theorem classical_large_values_sixth_branch
    (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hT : 0 ≤ T) (hV : 0 < V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    (W.card : ℝ) ≤
      4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
        ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) := by
  by_cases hW : W = ∅
  · subst W
    pm_4797
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  pm_6526
  pm_82 hG G
  have hGleN : G ≤ (N : ℝ) := by
    dsimp only [G]
    exact dyadic_energy_le_length N a ha
  have hthreshold : V ^ 2 ≤ (N : ℝ) * G := by
    dsimp only [G]
    exact threshold_sq_le_length_mul_energy N V W a hV.le
      (Finset.nonempty_iff_ne_empty.mpr hW) hLarge
  have hGpos : 0 < G := by
    pm_4649
    nlinarith [sq_pos_of_pos hV]
  let x : ℝ := V ^ 2 / (200 * G)
  let L : ℝ := x ^ 2
  pm_116 hx x
  pm_4801
  have hsqrtL : Real.sqrt L = x := by
    dsimp only [L]
    rw [Real.sqrt_sq hx.le]
  have hxN : x ≤ (N : ℝ) := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity : 0 < 200 * G)]
    nlinarith
  have hLN : L ≤ (N : ℝ) ^ 2 := by
    dsimp only [L]
    exact pow_le_pow_left₀ (by positivity) hxN 2
  have hAbsorb : 200 * G * Real.sqrt L ≤ V ^ 2 := by
    rw [hsqrtL]
    dsimp only [x]
    field_simp [hGpos.ne']
    norm_num
  have hlocal := classical_large_values_of_local_scale N T V L W a hN hV hL hLN
    hSep hBase hLarge (by simpa only [G] using hAbsorb)
  pm_4797
  have hB :
      (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) ≤
        49 * (N : ℝ) * (1 + (((harmonic N : ℚ) : ℝ))) := by
    pm_4802 hNreal N
    have hpi : 12 * Real.pi ≤ 48 := by nlinarith [Real.pi_lt_four]
    have hpiMul := mul_le_mul_of_nonneg_right hpi (mul_nonneg hNreal hH)
    nlinarith
  have hlocalFactor :
      2 * G * ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) /
          V ^ 2 ≤
        98 * (1 + (((harmonic N : ℚ) : ℝ))) * G * (N : ℝ) / V ^ 2 := by
    pm_5914 htwoG G
    have hmul := mul_le_mul_of_nonneg_left hB htwoG
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hV)).2
    nlinarith
  pm_6530 hqNonneg T L hT hL.le
  have hK : ((Nat.floor (T / L) + 1 : ℕ) : ℝ) ≤ T / L + 1 := by
    have hf := Nat.floor_le hqNonneg
    push_cast
    linarith
  have hrough :
      (W.card : ℝ) ≤ (T / L + 1) *
        (98 * (1 + (((harmonic N : ℚ) : ℝ))) * G * (N : ℝ) / V ^ 2) := by
    exact hlocal.trans (mul_le_mul hK hlocalFactor (by positivity) (by positivity))
  have hqIdentity : T / L = 40000 * T * G ^ 2 / V ^ 4 := by
    dsimp only [L, x]
    field_simp [hV.ne', hGpos.ne']
    ring
  rw [hqIdentity] at hrough
  have hGN : G * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hGleN (by positivity : 0 ≤ (N : ℝ))]
  have hG3 : G ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hG hGleN 3
  have hG3N : G ^ 3 * (N : ℝ) ≤ (N : ℝ) ^ 4 := by
    calc
      G ^ 3 * (N : ℝ) ≤ (N : ℝ) ^ 3 * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hG3 (by positivity)
      _ = (N : ℝ) ^ 4 := by ring
  have htarget :
      (40000 * T * G ^ 2 / V ^ 4 + 1) *
          (98 * (1 + (((harmonic N : ℚ) : ℝ))) * G * (N : ℝ) / V ^ 2) ≤
        4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) := by
    have hfirst : 98 * G * V ^ 4 ≤ 4000000 * (N : ℝ) * V ^ 4 := by
      have hc : (98 : ℝ) * G ≤ 4000000 * (N : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    have hsecond : 3920000 * T * G ^ 3 ≤ 4000000 * T * (N : ℝ) ^ 3 := by
      have hc : (3920000 : ℝ) * G ^ 3 ≤ 4000000 * (N : ℝ) ^ 3 := by nlinarith
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hc hT
    field_simp [hV.ne']
    nlinarith [hfirst, hsecond]
  exact hrough.trans htarget

/-- The basic Montgomery mean-value branch, normalized to bounded
coefficients and the same algebraic shape as the sixth-power branch. -/
theorem classical_large_values_second_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by
  rcases halasz_montgomery_lemma_native with ⟨C, hC, hHM⟩
  refine ⟨2 * C, by positivity, ?_⟩
  intro N T V W a hN hT hNT hV ha hSep hBase hLarge
  pm_4803
  have hTNonneg : 0 ≤ T := zero_le_one.trans hT
  have hTN : T + (N : ℝ) ≤ 2 * T := by linarith
  pm_4804
  calc
    (W.card : ℝ) ≤ C * (T + (N : ℝ)) * (1 / V ^ 2) *
        ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := hbound
    _ ≤ C * (2 * T) * (1 / V ^ 2) * (N : ℝ) := by
      gcongr
    _ ≤ (2 * C) * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by
      pm_4802 hNreal N
      have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
      field_simp [hV.ne']
      nlinarith [sq_nonneg (N : ℝ)]

/-- The mean-value branch does not intrinsically require `N ≤ T`. Keeping the
`N²/V²` diagonal term separately absorbs the additional `N` in `T+N`. This is
the form needed by the finite classical zero detector, whose convolution has
polynomially long support. -/
theorem classical_large_values_second_branch_unrestricted :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by
  rcases halasz_montgomery_lemma_native with ⟨C, hC, hHM⟩
  refine ⟨C, hC, ?_⟩
  intro N T V W a hN hT hV ha hSep hBase hLarge
  pm_4803
  pm_4804
  calc
    (W.card : ℝ) ≤ C * (T + (N : ℝ)) * (1 / V ^ 2) *
        ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := hbound
    _ ≤ C * (T + (N : ℝ)) * (1 / V ^ 2) * (N : ℝ) := by
      gcongr
    _ = C * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by ring

/-- The complete second/sixth-power classical estimate before logarithmic
absorption, valid for arbitrary positive polynomial length. -/
theorem classical_large_values_with_harmonic_unrestricted :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / V ^ 2 +
              T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  pm_1513 classical_large_values_second_branch_unrestricted
  intro N T V W a hN hT hV ha hSep hBase hLarge
  pm_4797
  pm_1316
  · rw [min_eq_left hBD]
    have hbasic := hSecond N T V W a hN hT hV ha hSep hBase hLarge
    pm_4807
    pm_4808
    have hCscale : C₂ ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) := by
      have hCnonneg : 0 ≤ C := (lt_of_lt_of_le hC₂ (le_max_left _ _)).le
      exact (le_max_left C₂ 4000000).trans <| by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (by linarith : 1 ≤ 1 + (((harmonic N : ℚ) : ℝ))) hCnonneg
    exact hbasic'.trans (mul_le_mul_of_nonneg_right hCscale hinner)
  · rw [min_eq_right (le_of_not_ge hBD)]
    pm_4806
    pm_4805
    exact hsixth'.trans (mul_le_mul_of_nonneg_right hcoef hinner)

/-- The two classical branches combined before absorbing the harmonic loss. -/
theorem classical_large_values_with_harmonic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / V ^ 2 +
              T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  pm_1513 classical_large_values_second_branch
  intro N T V W a hN hT hNT hV ha hSep hBase hLarge
  pm_4797
  have hA : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 := by positivity
  have hB : 0 ≤ (N : ℝ) / V ^ 2 := by positivity
  have hD : 0 ≤ (N : ℝ) ^ 4 / V ^ 6 := by positivity
  pm_1316
  · rw [min_eq_left hBD]
    have hbasic := hSecond N T V W a hN hT hNT hV ha hSep hBase hLarge
    pm_4807
    calc
      (W.card : ℝ) ≤ C₂ * ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2)) :=
        hbasic'
      _ ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2)) := by
        have hC₂C : C₂ ≤ C := le_max_left _ _
        pm_4808
        have hC : 0 ≤ C := (lt_of_lt_of_le hC₂ hC₂C).le
        have hCscale : C ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left
              (by linarith : 1 ≤ 1 + (((harmonic N : ℚ) : ℝ))) hC
        exact mul_le_mul_of_nonneg_right (hC₂C.trans hCscale) hinner
  · rw [min_eq_right (le_of_not_ge hBD)]
    pm_4806
    calc
      (W.card : ℝ) ≤ 4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6)) := hsixth'
      _ ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6)) := by
        pm_4805
        exact mul_le_mul_of_nonneg_right hcoef hinner

/-- The full finite Montgomery--Halász--Huxley estimate required by Package C
of Shitlist #15. -/
def ClassicalMontgomeryHalaszHuxley : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * T ^ ε *
            ((N : ℝ) ^ 2 / V ^ 2 +
              T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6))

theorem classical_montgomery_halasz_huxley_native :
    ClassicalMontgomeryHalaszHuxley := by
  intro ε hε
  rcases classical_large_values_with_harmonic with ⟨C₀, hC₀, hBound⟩
  refine ⟨C₀ * (2 + 1 / ε), by positivity, ?_⟩
  intro N T V W a hN hT hNT hV ha hSep hBase hLarge
  have hraw := hBound N T V W a hN hT hNT hV ha hSep hBase hLarge
  have hHlog : (((harmonic N : ℚ) : ℝ)) ≤ 1 + Real.log N :=
    harmonic_le_one_add_log N
  have hlogPow : Real.log N ≤ (N : ℝ) ^ ε / ε :=
    Real.log_natCast_le_rpow_div N hε
  have hpowMono : (N : ℝ) ^ ε ≤ T ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hNT hε.le
  have hpowOne : 1 ≤ T ^ ε := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hε.le
  have hfactor : 1 + (((harmonic N : ℚ) : ℝ)) ≤ (2 + 1 / ε) * T ^ ε := by
    have hdivMono : (N : ℝ) ^ ε / ε ≤ T ^ ε / ε :=
      div_le_div_of_nonneg_right hpowMono hε.le
    calc
      1 + (((harmonic N : ℚ) : ℝ)) ≤ 2 + Real.log N := by linarith
      _ ≤ 2 + (N : ℝ) ^ ε / ε := add_le_add_right hlogPow 2
      _ ≤ 2 + T ^ ε / ε := add_le_add_right hdivMono 2
      _ ≤ 2 * T ^ ε + T ^ ε / ε := by
        simpa only [add_comm] using
          add_le_add_right (by nlinarith [hpowOne] : (2 : ℝ) ≤ 2 * T ^ ε)
            (T ^ ε / ε)
      _ = (2 + 1 / ε) * T ^ ε := by ring
  have hinner : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 +
      T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) := by
    have hmin : 0 ≤ min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) := by positivity
    positivity
  calc
    (W.card : ℝ) ≤ C₀ * (1 + (((harmonic N : ℚ) : ℝ))) *
        ((N : ℝ) ^ 2 / V ^ 2 +
          T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := hraw
    _ ≤ (C₀ * (2 + 1 / ε)) * T ^ ε *
        ((N : ℝ) ^ 2 / V ^ 2 +
          T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
      have hscale := mul_le_mul_of_nonneg_left hfactor hC₀.le
      have hmul := mul_le_mul_of_nonneg_right hscale hinner
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul

end GuthMaynard.NativeMoment
