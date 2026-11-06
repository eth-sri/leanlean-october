module
import Mathlib
public import GuthMaynard.SecondOrderMeanValue

@[expose] public section

open Complex Finset
open scoped BigOperators InnerProductSpace

namespace RiemannZeta.GuthMaynard

/-!
# Weyl differencing for the logarithmic phase

The correlation phase below is the phase produced by one A-process shift.
Its curvature is controlled on a dyadic interval and is fed into the
multi-period B-process from `SecondDerivative.lean`.
-/

/-- Complex-correlation form of finite Weyl differencing. -/
theorem interval_weyl_differencing_complex
    (a : Int -> Complex) (N H : Nat) (C : Real)
    (ha : forall n, n ∈ Finset.Ico (0 : Int) N -> ‖a n‖ <= 1)
    (hC : 0 <= C)
    (hcorr : forall h, h ∈ Finset.range H -> forall k, k ∈ Finset.range H -> h ≠ k ->
      ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (paddedShift a N n h) * paddedShift a N n k‖ <= C) :
    (H : Real) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : Int) N, a n‖ ^ 2 <=
      ((N + H : Nat) : Real) * ((H : Real) * N + (H : Real) ^ 2 * C) := by
  apply interval_weyl_differencing a N H C ha hC
  intro h hh k hk hne
  let z := ∑ n ∈ Finset.Ico (-(H : Int)) N,
    star (paddedShift a N n h) * paddedShift a N n k
  have hre : (∑ n ∈ Finset.Ico (-(H : Int)) N,
      ⟪paddedShift a N n h, paddedShift a N n k⟫_ℝ) = z.re := by
    dsimp only [z]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    simp
    ring
  rw [hre]
  exact (abs_re_le_norm z).trans (hcorr h hh k hk hne)

section
variable (t A : Real)
include t A

section
variable (h k : Nat)
include h k

/-- Difference of two shifted logarithmic phases. -/
noncomputable def logarithmicDifferencePhase
     (x : Real) : Real :=
  logarithmicPhase t (A + x + h) - logarithmicPhase t (A + x + k)

section
variable {x : Real}
    (hh : A + x + h ≠ 0) (hk : A + x + k ≠ 0)
include x hh hk

theorem hasDerivAt_logarithmicDifferencePhase
     :
    HasDerivAt (logarithmicDifferencePhase t A h k)
      (-t / (A + x + h) + t / (A + x + k)) x := by
  have harg (m : Nat) : HasDerivAt (fun y : Real => A + y + m) 1 x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      HasDerivAt.add_const (m : Real)
        ((hasDerivAt_const x A).fun_add (hasDerivAt_id x))
  unfold logarithmicDifferencePhase
  convert ((hasDerivAt_logarithmicPhase t hh).comp x (harg h)).fun_sub
    ((hasDerivAt_logarithmicPhase t hk).comp x (harg k)) using 1
  all_goals (grind)

theorem hasDerivAt_logarithmicDifferencePhase_deriv
     :
    HasDerivAt (fun y => -t / (A + y + h) + t / (A + y + k))
      (t / (A + x + h) ^ 2 - t / (A + x + k) ^ 2) x := by
  have hleft : HasDerivAt (fun y : Real => -t / (A + y + h))
      (t / (A + x + h) ^ 2) x := by
    have hden : HasDerivAt (fun y : Real => A + y + h) 1 x := by
      simpa only [Pi.add_apply, id_eq, zero_add] using
        HasDerivAt.add_const (h : Real)
          ((hasDerivAt_const x A).fun_add (hasDerivAt_id x))
    convert (hasDerivAt_const x (-t)).div hden hh using 1
    simp_all
  have hright : HasDerivAt (fun y : Real => t / (A + y + k))
      (-t / (A + x + k) ^ 2) x := by
    have hden : HasDerivAt (fun y : Real => A + y + k) 1 x := by
      simpa only [Pi.add_apply, id_eq, zero_add] using
        HasDerivAt.add_const (k : Real)
          ((hasDerivAt_const x A).fun_add (hasDerivAt_id x))
    convert (hasDerivAt_const x t).div hden hk using 1
    simp_all
  convert hleft.add hright using 1
  ring_nf
end
end


/-- A unit discrete second difference of the shifted logarithmic correlation
equals its continuous second derivative at an intermediate point. -/
theorem logarithmicDifferencePhase_secondDifference
     (h k n : Nat) (hA : 0 < A) :
    exists xi, xi ∈ Set.Ioo (n : Real) (n + 2) ∧
      t / (A + xi + h) ^ 2 - t / (A + xi + k) ^ 2 =
        (logarithmicDifferencePhase t A h k (n + 2) -
          logarithmicDifferencePhase t A h k (n + 1)) -
        (logarithmicDifferencePhase t A h k (n + 1) -
          logarithmicDifferencePhase t A h k n) := by
  let F := logarithmicDifferencePhase t A h k
  let F' := fun x => -t / (A + x + h) + t / (A + x + k)
  let F'' := fun x =>
    t / (A + x + h) ^ 2 - t / (A + x + k) ^ 2
  have hmv := second_order_mean_value F F' F'' n
    (fun x hx => by grind [hasDerivAt_logarithmicDifferencePhase])
    (fun x hx => by grind [hasDerivAt_logarithmicDifferencePhase_deriv])
  grind
end


theorem logarithmicDifferenceCurvature_bounds
    (t A u v r : Real) (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (huLow : A <= u) (huv : u <= v) (hvHigh : v <= 2 * A)
    (hvu : v - u = r) :
    t * r / (8 * A ^ 3) <= t / u ^ 2 - t / v ^ 2 ∧
      t / u ^ 2 - t / v ^ 2 <= 4 * t * r / A ^ 3 := by
  have hu : 0 < u := hA.trans_le huLow
  have hv : 0 < v := hu.trans_le huv
  have hformula : t / u ^ 2 - t / v ^ 2 =
      t * r * (u + v) / (u ^ 2 * v ^ 2) := by
    field_simp [hu.ne', hv.ne']
    nlinarith
  have huHigh : u <= 2 * A := huv.trans hvHigh
  have hsumLow : 2 * A <= u + v := by linarith
  have hsumHigh : u + v <= 4 * A := by linarith
  have huSqLow : A ^ 2 <= u ^ 2 := by nlinarith
  have hvSqLow : A ^ 2 <= v ^ 2 := by nlinarith
  have huSqHigh : u ^ 2 <= (2 * A) ^ 2 := by nlinarith
  have hvSqHigh : v ^ 2 <= (2 * A) ^ 2 := by nlinarith
  have hdenLow : A ^ 4 <= u ^ 2 * v ^ 2 := by nlinarith
  have hdenHigh : u ^ 2 * v ^ 2 <= 16 * A ^ 4 := by nlinarith
  rw [hformula]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 8 * A ^ 3)
      (by positivity : 0 < u ^ 2 * v ^ 2)]
    have hcore : u ^ 2 * v ^ 2 <= 8 * A ^ 3 * (u + v) := by nlinarith
    calc
      t * r * (u ^ 2 * v ^ 2) <= t * r * (8 * A ^ 3 * (u + v)) :=
        mul_le_mul_of_nonneg_left hcore (mul_pos ht hr).le
      _ = t * r * (u + v) * (8 * A ^ 3) := by ring
  · rw [div_le_div_iff₀ (by positivity : 0 < u ^ 2 * v ^ 2)
      (by positivity : 0 < A ^ 3)]
    have hcore : A ^ 3 * (u + v) <= 4 * (u ^ 2 * v ^ 2) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hcore (mul_pos ht hr).le
    nlinarith

section
variable (t A : Real)
include t A

section
variable (h k N : Nat) (ht : 0 < t) (hA : 0 < A)
    (hhk : h < k)
include h k N ht hA hhk

theorem logarithmicDifference_secondDifference_bounds
     (hsize : (N + 1 + k : Nat) <= A) :
    forall n, n < N ->
      t * (k - h : Nat) / (8 * A ^ 3) <=
        (logarithmicDifferencePhase t A h k (n + 2) -
          logarithmicDifferencePhase t A h k (n + 1)) -
          (logarithmicDifferencePhase t A h k (n + 1) -
            logarithmicDifferencePhase t A h k n) ∧
      (logarithmicDifferencePhase t A h k (n + 2) -
          logarithmicDifferencePhase t A h k (n + 1)) -
          (logarithmicDifferencePhase t A h k (n + 1) -
            logarithmicDifferencePhase t A h k n) <=
        4 * t * (k - h : Nat) / A ^ 3 := by
  intro n hn
  obtain ⟨xi, hxi, heq⟩ :=
    logarithmicDifferencePhase_secondDifference t A h k n hA
  let u := A + xi + h
  let v := A + xi + k
  have hcastHK : ((k - h : Nat) : Real) = (k : Real) - h := by
    rw [Nat.cast_sub hhk.le]
  have hr : 0 < ((k - h : Nat) : Real) := by exact_mod_cast Nat.sub_pos_of_lt hhk
  have huLow : A <= u := by grind
  have huv : u <= v := by linarith
  have hvHigh : v <= 2 * A := by
    dsimp only [v]
    have hnk : (n : Real) + 2 + k <= A := by
      have hnat : n + 2 + k <= N + 1 + k := by omega
      have hcast : ((n + 2 + k : Nat) : Real) <= ((N + 1 + k : Nat) : Real) := by
        exact_mod_cast hnat
      calc
        (n : Real) + 2 + k = ((n + 2 + k : Nat) : Real) := by norm_num
        _ <= ((N + 1 + k : Nat) : Real) := hcast
        _ <= A := hsize
    linarith [hxi.2]
  have hvu : v - u = ((k - h : Nat) : Real) := by
    dsimp only [u, v]
    rw [hcastHK]
    ring
  have hb := logarithmicDifferenceCurvature_bounds t A u v
    ((k - h : Nat) : Real) ht hA hr huLow huv hvHigh hvu
  grind

/-- B-process estimate for every logarithmic correlation created by one
A-process shift on a dyadic block. -/
theorem logarithmicDifference_B_process
     (hsize : ((N + 1 + k : Nat) : Real) <= A) :
    ‖∑ n ∈ Finset.range (N + 1),
        unitaryPhase (logarithmicDifferencePhase t A h k n)‖ <=
      ((N : Real) * (4 * t * (k - h : Nat) / A ^ 3) /
          (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt (t * (k - h : Nat) / (8 * A ^ 3)) +
          2 * (Real.sqrt (t * (k - h : Nat) / (8 * A ^ 3)) /
            (t * (k - h : Nat) / (8 * A ^ 3)) + 1)) := by
  let lambda := t * (k - h : Nat) / (8 * A ^ 3)
  let Lambda := 4 * t * (k - h : Nat) / A ^ 3
  have hr : 0 < ((k - h : Nat) : Real) := by exact_mod_cast Nat.sub_pos_of_lt hhk
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    positivity
  have hbounds := logarithmicDifference_secondDifference_bounds
    t A h k N ht hA hhk hsize
  exact vanDerCorput_B_process
      (fun n : Nat => logarithmicDifferencePhase t A h k n)
      N lambda Lambda hlambda
        (fun n hn => by aesop)
        (fun n hn => by aesop)
end


/-- Integer-indexed logarithmic phase term used by zero-padded shifts. -/
noncomputable def integerLogarithmicTerm  (n : Int) : Complex :=
  unitaryPhase (logarithmicPhase t (A + n))

@[simp] theorem norm_integerLogarithmicTerm  (n : Int) :
    ‖integerLogarithmicTerm t A n‖ = 1 := by
  simp [integerLogarithmicTerm]

theorem padded_logarithmic_correlation_eq  (N H h k : Nat)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k) =
      star (∑ m ∈ Finset.range (N - (k - h)),
        unitaryPhase (logarithmicDifferencePhase t A 0 (k - h) m)) := by
  unfold paddedShift
  let s := (Finset.Ico (-(H : Int)) N).filter (fun n =>
    n + (h : Int) ∈ Finset.Ico (0 : Int) N ∧
      n + (k : Int) ∈ Finset.Ico (0 : Int) N)
  have hrestrict :
      (∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (if n + (h : Int) ∈ Finset.Ico (0 : Int) N then
          integerLogarithmicTerm t A (n + h) else 0) *
        (if n + (k : Int) ∈ Finset.Ico (0 : Int) N then
          integerLogarithmicTerm t A (n + k) else 0)) =
      ∑ n ∈ s, star (integerLogarithmicTerm t A (n + h)) *
        integerLogarithmicTerm t A (n + k) := by
    simp only [s, Finset.sum_filter]
    grind
  rw [hrestrict]
  have hsum :
      (∑ n ∈ s,
        star (integerLogarithmicTerm t A (n + h)) *
          integerLogarithmicTerm t A (n + k)) =
        ∑ m ∈ Finset.range (N - (k - h)),
          star (integerLogarithmicTerm t A m) *
            integerLogarithmicTerm t A (m + (k - h)) := by
    apply Finset.sum_bij (fun n _hn => Int.toNat (n + h))
    case hi =>
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnh := Finset.mem_Ico.mp hnData.2.1
      have hnk := Finset.mem_Ico.mp hnData.2.2
      apply Finset.mem_range.mpr
      have heq : n + (k : Int) = (n + h) + (k - h : Nat) := by
        omega
      rw [heq] at hnk
      have hcast : Int.toNat (n + h) + (k - h) < N := by omega
      omega
    case i_inj =>
      intro n₁ hn₁ n₂ hn₂ heq
      have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).2.1).1
      have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).2.1).1
      have heqInt := congrArg (fun m : Nat => (m : Int)) heq
      change ((Int.toNat (n₁ + h) : Nat) : Int) =
        ((Int.toNat (n₂ + h) : Nat) : Int) at heqInt
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at heqInt
      omega
    case i_surj =>
      intro m hm
      have hm' := Finset.mem_range.mp hm
      refine ⟨(m : Int) - h, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Ico.mpr
          constructor
          · have := hh
            omega
          · omega
        · constructor
          · apply Finset.mem_Ico.mpr
            constructor
            · omega
            · have hmk : m + (k - h) < N := by omega
              omega
          · apply Finset.mem_Ico.mpr
            constructor
            · omega
            · have hmk : m + (k - h) < N := by omega
              omega
      · simp
    case h =>
      intro n hn
      have hnonneg := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).2.1).1
      have hnat : ((Int.toNat (n + h) : Nat) : Int) = n + h := Int.toNat_of_nonneg hnonneg
      congr 2
      · rw [hnat]
      · rw [hnat]
        omega
  rw [hsum]
  change (∑ m ∈ Finset.range (N - (k - h)),
      star (integerLogarithmicTerm t A m) *
        integerLogarithmicTerm t A (m + (k - h))) =
    (starRingEnd Complex) (∑ m ∈ Finset.range (N - (k - h)),
      unitaryPhase (logarithmicDifferencePhase t A 0 (k - h) m))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  change star (integerLogarithmicTerm t A m) *
      integerLogarithmicTerm t A (m + (k - h)) =
    star (unitaryPhase (logarithmicDifferencePhase t A 0 (k - h) m))
  unfold integerLogarithmicTerm logarithmicDifferencePhase
  rw [unitaryPhase_sub]
  simp only [Nat.cast_zero, add_zero]
  rw [star_mul']
  rw [show star ((starRingEnd Complex)
      (unitaryPhase (logarithmicPhase t (A + (m : Real) + (k - h : Nat))))) =
      unitaryPhase (logarithmicPhase t (A + (m : Real) + (k - h : Nat))) by
    change star (star (unitaryPhase
      (logarithmicPhase t (A + (m : Real) + (k - h : Nat))))) = _
    rw [star_star]]
  congr 2
  push_cast
  rw [Nat.cast_sub hhk.le]
  ring_nf

/-- Explicit B-process majorant for a correlation at shift distance `r`. -/
noncomputable def logarithmicCorrelationBound
     (N r : Nat) : Real :=
  let M := N - r - 1
  ((M : Real) * (4 * t * r / A ^ 3) / (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t * r / (8 * A ^ 3)) +
      2 * (Real.sqrt (t * r / (8 * A ^ 3)) /
        (t * r / (8 * A ^ 3)) + 1))

theorem padded_logarithmic_correlation_norm_le_of_lt
     (N H h k : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ <=
      logarithmicCorrelationBound t A N (k - h) := by
  let M := N - (k - h) - 1
  have hlength : M + 1 = N - (k - h) := by
    dsimp only [M]
    omega
  have hsizeNat : M + 1 + (k - h) <= N := by
    dsimp only [M]
    omega
  have hsize : ((M + 1 + (k - h) : Nat) : Real) <= A := by
    exact (Nat.cast_le.mpr hsizeNat).trans hNA
  have hB := logarithmicDifference_B_process t A 0 (k - h) M ht hA
    (by omega) hsize
  rw [padded_logarithmic_correlation_eq t A N H h k hh hk hhk,
    norm_star, ← hlength]
  simpa only [logarithmicCorrelationBound, M, Nat.sub_zero] using hB
end


/-- Symmetric natural-number distance between two shifts. -/
def shiftDistance (h k : Nat) : Nat := (h - k) + (k - h)

theorem padded_logarithmic_correlation_norm_le
    (t A : Real) (N H h k : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ <=
      logarithmicCorrelationBound t A N (shiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmic_correlation_norm_le_of_lt
      t A N H h k ht hA hH hNA hh hk hhk
    simpa only [shiftDistance, Nat.sub_eq_zero_of_le hhk.le, zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmic_correlation_norm_le_of_lt
      t A N H k h ht hA hH hNA hk hh hkh
    let z := ∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k
    let w := ∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n k) *
        paddedShift (integerLogarithmicTerm t A) N n h
    have hzw : z = star w := by
      change (∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (paddedShift (integerLogarithmicTerm t A) N n h) *
          paddedShift (integerLogarithmicTerm t A) N n k) =
        (starRingEnd Complex) (∑ n ∈ Finset.Ico (-(H : Int)) N,
          star (paddedShift (integerLogarithmicTerm t A) N n k) *
            paddedShift (integerLogarithmicTerm t A) N n h)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      change star (paddedShift (integerLogarithmicTerm t A) N n h) *
          paddedShift (integerLogarithmicTerm t A) N n k =
        star (star (paddedShift (integerLogarithmicTerm t A) N n k) *
          paddedShift (integerLogarithmicTerm t A) N n h)
      rw [star_mul']
      rw [star_star]
      ring
    rw [show ‖z‖ = ‖w‖ by rw [hzw, norm_star]]
    simpa only [shiftDistance, Nat.sub_eq_zero_of_le hkh.le, add_zero] using hb

theorem integerLogarithmicSum_eq (t : Real) (A N : Nat) :
    (∑ n ∈ Finset.Ico (0 : Int) N, integerLogarithmicTerm t A n) =
      logarithmicSum t A (A + N) := by
  unfold logarithmicSum phaseSum
  apply Finset.sum_bij (fun n _hn => A + Int.toNat n)
  case hi =>
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · have hcast : Int.toNat n < N := by simp_all
      omega
  case i_inj =>
    intro n₁ hn₁ n₂ hn₂ heq
    have h1 := (Finset.mem_Ico.mp hn₁).1
    have h2 := (Finset.mem_Ico.mp hn₂).1
    have hnat : Int.toNat n₁ = Int.toNat n₂ := by omega
    have hcast := congrArg (fun m : Nat => (m : Int)) hnat
    change ((Int.toNat n₁ : Nat) : Int) = ((Int.toNat n₂ : Nat) : Int) at hcast
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hcast
    exact hcast
  case i_surj =>
    intro m hm
    have hm' := Finset.mem_Ico.mp hm
    refine ⟨(m - A : Nat), ?_, by omega⟩
    apply Finset.mem_Ico.mpr
    constructor
    · positivity
    · exact_mod_cast (show m - A < N by omega)
  case h =>
    intro n hn
    have hn0 := (Finset.mem_Ico.mp hn).1
    unfold integerLogarithmicTerm
    congr 3
    have hto : ((Int.toNat n : Nat) : Int) = n := Int.toNat_of_nonneg hn0
    have htoReal : ((Int.toNat n : Nat) : Real) = (n : Real) := by
      exact_mod_cast hto
    push_cast
    rw [htoReal]


