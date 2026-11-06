module
import Mathlib
public import GafniTao.HeathBrownChosenAlgebra

@[expose] public section

/-!
# Heath-Brown Lemma 2: source-scale finite form

This module completes the algebraic part of the refined counting lemma.  Its
public theorem has the source factors
`(1 + A * lambda * N)`, `N + lambda^(-2/k)`, and `1 + log N`, with an explicit
The constant depending only on `A` and `k`.
-/

namespace GafniTao

noncomputable section

def heathBrownRefinedCountConstant (k : ℕ) (A : ℝ) : ℝ :=
  16 * (1 + 2 * heathBrownChosenTotalConstant k A)

def heathBrownLemmaTwoConstant (k : ℕ) (A : ℝ) : ℝ :=
  heathBrownRefinedCountConstant k A * (1 + A)

theorem heathBrownRefinedCountConstant_pos
    (k : ℕ) {A : ℝ} (hA : 0 < A) :
    0 < heathBrownRefinedCountConstant k A := by
  unfold heathBrownRefinedCountConstant heathBrownChosenTotalConstant
  have hC₁ := heathBrownChosenFirstConstant_nonneg k hA.le
  have hC₂ := heathBrownChosenSecondConstant_nonneg k hA.le
  positivity

theorem heathBrownBlockParameter_cast_le
    {N : ℕ} {A lambda : ℝ} (hA : 0 ≤ A) (hlambda : 0 ≤ lambda) :
    (heathBrownBlockParameter A lambda N : ℝ) ≤
      1 + 4 * A * lambda * N := by
  unfold heathBrownBlockParameter
  push_cast
  gcongr
  exact Nat.floor_le (by positivity)

section
variable {N k : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1)
    (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hcoordLow : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLowD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hcoordLast : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLastD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
include N k f A lambda hk hN hA hlambda hlambdaOne hsmall hlargeH hcoordLow hcoordLowD hcoordLast hcoordLastD hraw hrawd hkBounds

theorem heathBrownPairCount_card_cast_le_source_scale
     :
    let H := heathBrownHChoice k A lambda
    ((heathBrownPairCount N k H f).card : ℝ) ≤
      heathBrownRefinedCountConstant k A *
        (1 + A * lambda * N) *
        (N + lambda ^ (-(2 / (k : ℝ)))) *
        (1 + Real.log N) := by
  dsimp only
  let K := heathBrownBlockParameter A lambda N
  let C := heathBrownChosenTotalConstant k A
  let S := (N : ℝ) + lambda ^ (-(2 / (k : ℝ)))
  let L := 1 + Real.log (N : ℝ)
  have hcount := heathBrownPairCount_card_cast_le_chosen_factor
    (N := N) (k := k) (f := f) (A := A) (lambda := lambda)
    hk hN hA hlambda hsmall hlargeH hcoordLow hcoordLowD hcoordLast
    hcoordLastD hraw hrawd hkBounds
  dsimp only at hcount
  have hshift := heathBrownChosenShiftFactor_le_source_sum
    (k := k) (N := N) (A := A) (lambda := lambda)
    hk hA hlambda hlambdaOne
  have hC : 0 ≤ C := by
    dsimp only [C, heathBrownChosenTotalConstant]
    have hC₁ := heathBrownChosenFirstConstant_nonneg k hA.le
    have hC₂ := heathBrownChosenSecondConstant_nonneg k hA.le
    positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg hNreal
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hL : 0 ≤ L := hLone.trans' (by norm_num)
  have hNleS : (N : ℝ) ≤ S := by
    dsimp only [S]
    linarith [Real.rpow_nonneg hlambda.le (-(2 / (k : ℝ)))]
  have hNleSL : (N : ℝ) ≤ S * L := by
    exact hNleS.trans (le_mul_of_one_le_right hS hLone)
  have hinside :
      (N : ℝ) + 2 * heathBrownChosenShiftFactor N k A lambda * L ≤
        (1 + 2 * C) * S * L := by nlinarith
  have hK : (K : ℝ) ≤ 1 + 4 * A * lambda * N := by
    exact heathBrownBlockParameter_cast_le
      (N := N) hA.le hlambda.le
  have hrightNonneg : 0 ≤ (1 + 2 * C) * S * L := by positivity
  calc
    ((heathBrownPairCount N k (heathBrownHChoice k A lambda) f).card : ℝ) ≤
        4 * K * ((N : ℝ) +
          2 * heathBrownChosenShiftFactor N k A lambda * L) := by
      simpa only [K, L, mul_assoc] using hcount
    _ ≤ 4 * K * ((1 + 2 * C) * S * L) := by gcongr
    _ ≤ 4 * (1 + 4 * A * lambda * N) *
        ((1 + 2 * C) * S * L) := by gcongr
    _ ≤ 16 * (1 + A * lambda * N) *
        ((1 + 2 * C) * S * L) := by linarith
    _ = heathBrownRefinedCountConstant k A *
        (1 + A * lambda * N) * S * L := by
      unfold heathBrownRefinedCountConstant
      dsimp only [C]
      ring
    _ = heathBrownRefinedCountConstant k A *
        (1 + A * lambda * N) *
        (N + lambda ^ (-(2 / (k : ℝ)))) *
        (1 + Real.log N) := by rfl

theorem heathBrownPairCount_card_cast_le_lemma_two
     :
    let H := heathBrownHChoice k A lambda
    ((heathBrownPairCount N k H f).card : ℝ) ≤
      heathBrownLemmaTwoConstant k A *
        (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
        (1 + Real.log N) := by
  dsimp only
  have hsource := heathBrownPairCount_card_cast_le_source_scale
    (N := N) (k := k) (f := f) (A := A) (lambda := lambda)
    hk hN hA hlambda hlambdaOne hsmall hlargeH hcoordLow hcoordLowD
    hcoordLast hcoordLastD hraw hrawd hkBounds
  dsimp only at hsource
  let P := lambda ^ (-(2 / (k : ℝ)))
  let B := (N : ℝ) + lambda * N ^ 2 + P
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hexp : 0 ≤ 1 - 2 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < k)]
    exact_mod_cast (by omega : 2 ≤ k)
  have hq :=
    Real.rpow_le_one hlambda.le hlambdaOne hexp
  have hcombine : lambda * P = lambda ^ (1 - 2 / (k : ℝ)) := by
    dsimp only [P]
    calc
      lambda * lambda ^ (-(2 / (k : ℝ))) =
          lambda ^ (1 : ℝ) * lambda ^ (-(2 / (k : ℝ))) := by simp
      _ = lambda ^ ((1 : ℝ) + -(2 / (k : ℝ))) := by
        rw [Real.rpow_add hlambda]
      _ = lambda ^ (1 - 2 / (k : ℝ)) := by rfl
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hproduct :
      (1 + A * lambda * (N : ℝ)) * (N + P) ≤ (1 + A) * B := by
    have hcross : A * (N : ℝ) * (lambda * P) ≤ A * N := by field_simp <;> nlinarith
    calc
      (1 + A * lambda * (N : ℝ)) * (N + P) =
          N + P + A * lambda * N ^ 2 + A * N * (lambda * P) := by ring
      _ ≤ N + P + A * lambda * N ^ 2 + A * N := by gcongr
      _ ≤ (1 + A) * B := by nlinarith
  have hlog : 0 ≤ 1 + Real.log (N : ℝ) := by positivity
  have hC :=
    (heathBrownRefinedCountConstant_pos k hA).le
  calc
    ((heathBrownPairCount N k (heathBrownHChoice k A lambda) f).card : ℝ) ≤
        heathBrownRefinedCountConstant k A *
          (1 + A * lambda * N) * (N + P) *
          (1 + Real.log N) := by simpa only [P] using hsource
    _ ≤ heathBrownRefinedCountConstant k A * ((1 + A) * B) *
        (1 + Real.log N) := by field_simp <;> nlinarith
    _ = heathBrownLemmaTwoConstant k A *
        (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
        (1 + Real.log N) := by
      unfold heathBrownLemmaTwoConstant
      dsimp only [B, P]
      ring
end






