module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Recovery
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror
public import QPBT.Games.Sandwich.Support
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore
public import QPBT.Games.ErrorFunctions
public import QPBT.Observables.WinImplications.FactorTransport

/-!
# Transporting a consistency relation along the recovery step

The recovery step of `lem:ld-combining-recovery` replaces a relation between a
point measurement of the original strategy read through a combination and a
measurement of the combined game read at a point of the combined space by a
relation between the point measurement itself and the same measurement read
through the recovered polynomial tuple.  This module isolates the consistency
calculus of that replacement, in a form which does not mention the low-degree
game.

Both relations are diagonal overlaps of the same pair of measurements placed on
opposite tensor factors, and the two relabellings differ only on the event that
the recovered outcome disagrees with the outcome of the point measurement while
the two relabellings agree.  The probability of that event, averaged over the
auxiliary sample, is bounded at each question by a quantity depending only on
the outcome of the second measurement; since the first measurement is complete,
the total Born weight of an outcome of the second measurement does not depend on
the question, and the bound may therefore be averaged over the question against
that weight.

The two conclusions of `lem:ld-soundness` transported here place the point
measurement on opposite tensor factors, so the calculus is recorded twice, once
for each placement; the two statements share the averaging estimate, which is
insensitive to the placement.

## Main statements

* `consistencyDefect_le_of_recoveryBound` — the transport of a consistency
  relation along a relabelling which is correct off a rare event, with the
  point measurement on the first tensor factor.
* `consistencyDefect_le_of_recoveryBound_right` — the same transport with the
  point measurement on the second tensor factor.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus
open SandwichProduct

noncomputable section

namespace RecoveryInternal

/-! ## Pair expansions of the diagonal overlap -/

/-- The diagonal overlap of a measurement against a relabelled measurement on the
opposite factor is the sum over pairs of outcomes with matching labels. -/
theorem diagonalRight_pair_sum {β Γ ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : Γ → β) :
    (∑ b : β, stateQForm ψ
      (heteroKron (A.effect b) ((B.postprocess f).effect b))) =
      ∑ b : β, ∑ g : Γ, if f g = b then
        stateQForm ψ (heteroKron (A.effect b) (B.effect g)) else 0 := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]

/-- The diagonal overlap of two relabelled measurements on opposite factors is
the sum over pairs of outcomes with matching labels. -/
theorem diagonalPair_pair_sum {β Γ R ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (e : β → R) (f : Γ → R) :
    (∑ r : R, stateQForm ψ
      (heteroKron ((A.postprocess e).effect r) ((B.postprocess f).effect r))) =
      ∑ b : β, ∑ g : Γ, if e b = f g then
        stateQForm ψ (heteroKron (A.effect b) (B.effect g)) else 0 := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, heteroKron_finset_sum_left,
    heteroKron_finset_sum_right, stateQForm_finset_sum]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp
  exact Finset.sum_comm

/-- The point defect of two measurements on opposite factors of a unit state. -/
theorem point_defect_heteroKron {α ιA ιB : Type*} [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α ιA) (B : Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    (∑ a : α, ∑ a' : α, if a = a' then 0 else stateQForm ψ (heteroKron (A.effect a) (B.effect a'))) =
      1 - ∑ a, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  have h := point_defect_eq (leftPlacedMeasurement (ιB := ιB) A)
    (rightPlacedMeasurement (ιA := ιA) B) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, placed_product_stateQForm_eq] at h
  rw [h, hψ, one_pow]

/-! ## The averaging estimate -/

/-- The averaging estimate underlying the recovery transport, stated for the
Born weights alone.  The weights `w x b g` of a pair of outcomes have fiber
sums `W g` independent of the question `x`, and the two diagonal overlaps
differ only on the discrepancy event, whose conditional probability is bounded
by `F x g`; averaging that bound against the fiber weights gives `η`. -/
theorem recovery_avg_le {X Y β Γ R : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    (w : X → β → Γ → ℝ) (W : Γ → ℝ)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hwnonneg : ∀ x b g, 0 ≤ w x b g) (hWnonneg : ∀ g, 0 ≤ W g)
    (hfiber : ∀ x g, (∑ b : β, w x b g) = W g) (hWsum : (∑ g : Γ, W g) = 1)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    avgOver (uniformDistribution X) (fun x =>
        avgOver (uniformDistribution Y) (fun y =>
          ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0)) ≤
      avgOver (uniformDistribution X)
        (fun x => ∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) + η := by
  have hstep (x : X) : avgOver (uniformDistribution Y) (fun y =>
      ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0) ≤
      ∑ b : β, ∑ g : Γ, ((if f x g = b then w x b g else 0) + w x b g * F x g) := by
    simp only [avgOver_sum]
    gcongr with b _ g _
    refine (avgOver_mono _ _ _ fun y => (?_ : _ ≤ (if f x g = b then w x b g else 0) +
      (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) * w x b g)).trans ?_
    · have := hwnonneg x b g
      split_ifs <;> simp_all
    · rw [avgOver_add, avgOver_uniform_const, avgOver_mul_const]
      nlinarith [mul_le_mul_of_nonneg_right (hFbound x b g) (hwnonneg x b g)]
  refine (avgOver_mono _ _ _ hstep).trans ?_
  have h (x : X) : ∑ b : β, ∑ g : Γ, w x b g * F x g = ∑ g : Γ, W g * F x g := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hfiber]
  simp only [Finset.sum_add_distrib, avgOver_add, h, avgOver_sum, avgOver_const_mul]
  have := (Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hFavg g) (hWnonneg g)).trans_eq
    (by rw [← Finset.sum_mul, hWsum, one_mul])
  linarith

end RecoveryInternal

/-! ## The transport of a consistency relation -/

open RecoveryInternal

variable {X Y β Γ R ιA ιB : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Transport of a consistency relation along the recovery relabelling, with
the point measurement on the first tensor factor.  The point measurement is
complete at every question, so the total Born weight of an outcome of the
second measurement does not depend on the question; the bound on the
discrepancy event may therefore be averaged over the question against that
weight, and the defect of the recovered relation exceeds the defect of the
relation with the auxiliary sample by at most the resulting average. -/
theorem consistencyDefect_le_of_recoveryBound
    (A : X → Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    consistencyDefect (uniformDistribution X)
        (fun x b => heteroKron ((A x).effect b) 1)
        (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
      consistencyDefect (uniformDistribution (X × Y))
        (fun z r => heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
        (fun z r => heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ + η := by
  have hW (x : X) (g : Γ) : ∑ b, stateQForm ψ (heteroKron ((A x).effect b) (B.effect g)) =
      stateQForm ψ (heteroKron 1 (B.effect g)) := by
    rw [← (A x).sum_eq_one, heteroKron_finset_sum_left, stateQForm_finset_sum]
  rw [consistencyDefect_placed_eq_avg_point, consistencyDefect_placed_eq_avg_point
    (uniformDistribution (X × Y)) (fun z => (A z.1).postprocess (e₁ z.1 z.2))
    (fun z => B.postprocess (f₁ z.1 z.2))]
  simp only [point_defect_heteroKron _ _ _ hψ, diagonalPair_pair_sum]
  simp only [diagonalRight_pair_sum, avgOver_sub, avgOver_uniform_const,
    avgOver_uniform_prod (fun x y => ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then
      stateQForm ψ (heteroKron ((A x).effect b) (B.effect g)) else 0)]
  linarith [recovery_avg_le (fun x b g => stateQForm ψ (heteroKron ((A x).effect b) (B.effect g)))
    (fun g => stateQForm ψ (heteroKron 1 (B.effect g))) f e₁ f₁ F η
    (fun x b g => stateQForm_nonneg ψ (kronecker_nonneg ((A x).pos b) (B.pos g)))
    (fun g => stateQForm_nonneg ψ (kronecker_nonneg (Matrix.PosSemidef.one.nonneg : (0 : Op ιA) ≤ 1)
      (B.pos g))) hW (by rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, B.sum_eq_one,
        heteroKron_one_one, stateQForm_one, hψ, one_pow]) hFbound hFavg]

end

end MIPStarRE.QPBT
