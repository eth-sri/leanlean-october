module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Recovery
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror
public import QPBT.Games.Sandwich.Support
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore
public import QPBT.Games.ErrorFunctions

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
measurement on opposite tensor factors, and the right-placement form follows by exchanging the two tensor factors.

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

private theorem postprocess_id {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (A : Measurement β ι) : A.postprocess id = A := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro b
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  simp

/-! ## The averaging estimate -/

set_option maxHeartbeats 1600000 in
/-- The averaging estimate underlying the recovery transport, stated for the
Born weights alone.  The weights `w x b g` of a pair of outcomes have fiber
sums `W g` independent of the question `x`, and the two diagonal overlaps
differ only on the discrepancy event, whose conditional probability is bounded
by `F x g`; averaging that bound against the fiber weights gives `η`. -/
private theorem recovery_avg_le {X Y β Γ R : Type*}
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
  classical
  let μ := uniformDistribution X
  let ν := uniformDistribution Y
  let A x b g := if f x g = b then w x b g else 0
  let H x y b g := if e₁ x y b = f₁ x y g then w x b g else 0
  have hterm x b g : avgOver ν (fun y => H x y b g) ≤ A x b g + w x b g * F x g := by
    have hp y : H x y b g ≤ A x b g +
        (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) * w x b g := by
      have hw := hwnonneg x b g
      by_cases he : e₁ x y b = f₁ x y g <;> by_cases hf : f x g = b <;> simp [A, H, he, hf, hw]
    refine (avgOver_mono ν _ _ hp).trans ?_
    rw [avgOver_add, avgOver_uniform_const, avgOver_mul_const, mul_comm (w x b g)]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (hFbound x b g) (hwnonneg x b g)) _
  have hstep x : avgOver ν (fun y => ∑ b, ∑ g, H x y b g) ≤
      (∑ b, ∑ g, A x b g) + ∑ g, W g * F x g := by
    simp_rw [avgOver_sum]
    refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun g _ => hterm x b g).trans_eq ?_
    simp only [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hfiber]
  have hlast : avgOver μ (fun x => ∑ g, W g * F x g) ≤ η := by
    simp_rw [avgOver_sum, avgOver_const_mul]
    exact (Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hFavg g) (hWnonneg g)).trans_eq
      (by rw [← Finset.sum_mul, hWsum, one_mul])
  refine (avgOver_mono μ _ _ hstep).trans ?_
  rw [avgOver_add]
  exact add_le_add_right hlast _

end RecoveryInternal

/-! ## The transport of a consistency relation -/

open RecoveryInternal

/-- Transport of a consistency relation along the recovery relabelling, with
the point measurement on the first tensor factor.  The point measurement is
complete at every question, so the total Born weight of an outcome of the
second measurement does not depend on the question; the bound on the
discrepancy event may therefore be averaged over the question against that
weight, and the defect of the recovered relation exceeds the defect of the
relation with the auxiliary sample by at most the resulting average. -/
theorem consistencyDefect_le_of_recoveryBound
    {X Y β Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → Measurement β ιA) (B : Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    bipartiteDefect (uniformDistribution X)
        A
        (fun x => B.postprocess (f x)) ψ ≤
      bipartiteDefect (uniformDistribution (X × Y))
        (fun z => (A z.1).postprocess (e₁ z.1 z.2))
        (fun z => B.postprocess (f₁ z.1 z.2)) ψ + η := by
  classical
  set w : X → β → Γ → ℝ := fun x b g =>
    stateQForm ψ (heteroKron ((A x).effect b) (B.effect g)) with hwdef
  have hwnonneg : ∀ x b g, 0 ≤ w x b g := fun x b g =>
    stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg ((A x).pos b) (B.pos g))
  set W : Γ → ℝ := fun g => stateQForm ψ (heteroKron (1 : Op ιA) (B.effect g))
    with hWdef
  have hWnonneg : ∀ g, 0 ≤ W g := fun g =>
    stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : (0 : Op ιA) ≤ 1) (B.pos g))
  have hfiber : ∀ x g, (∑ b : β, w x b g) = W g := by
    intro x g
    rw [hwdef, hWdef]
    simp only
    rw [← (A x).sum_eq_one, heteroKron_finset_sum_left, stateQForm_finset_sum]
  have hWsum : (∑ g : Γ, W g) = 1 := by
    rw [hWdef]
    simp only
    rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, B.sum_eq_one,
      heteroKron_one_one, stateQForm_one, hψ, one_pow]
  rw [consistencyDefect_placed_eq_one_sub_overlap _ A
      (fun x => B.postprocess (f x)) ψ (uniformDistribution_isProbability X) hψ,
    consistencyDefect_placed_eq_one_sub_overlap _
      (fun z : X × Y => (A z.1).postprocess (e₁ z.1 z.2))
      (fun z => B.postprocess (f₁ z.1 z.2)) ψ (uniformDistribution_isProbability (X × Y)) hψ]
  have hdiag (x : X) := diagonal_postprocess_stateQForm_eq_pair_sum (A x) B ψ id (f x)
  simp only [postprocess_id, id_eq] at hdiag
  simp_rw [hdiag, diagonal_postprocess_stateQForm_eq_pair_sum]
  rw [avgOver_uniform_prod (fun x y => ∑ b, ∑ g,
    if e₁ x y b = f₁ x y g then w x b g else 0)]
  have h := recovery_avg_le w W f e₁ f₁ F η hwnonneg hWnonneg hfiber hWsum hFbound hFavg
  simp only [w, eq_comm (a := f _ _)] at h
  linarith

end

end MIPStarRE.QPBT
