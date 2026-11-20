/-
Copyright (c) 2025-2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import DOZZ.GFFStructure.MetricChaining
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Quantitative finite-dimensional metric covering

Adapted from the Brownian-motion formalization of Rémy Degenne and collaborators
(github.com/RemyDegenne/brownian-motion). Its covering predicate is the current Mathlib
`HasCoveringExponent` with identical fields. Haar translation uses current Mathlib primitives; the
volume and packing arguments supply the finite-dimensional constants required by the continuous
modification construction.
-/

@[expose] public section

open MeasureTheory _root_.Metric _root_.EMetric _root_.Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The covering predicate of the source formalization is exactly the current Mathlib
predicate. -/
abbrev HasBoundedCoveringNumber {T : Type*} [PseudoEMetricSpace T]
    (A : Set T) (c : ℝ≥0∞) (d : ℝ) : Prop := _root_.Metric.HasCoveringExponent A c d

/-- Translation does not change the volume of an extended closed metric ball. -/
theorem volume_closedEBall_center {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (x : E) (r : ℝ≥0∞) :
    volume (Metric.closedEBall x r) = volume (Metric.closedEBall (0 : E) r) := by
  obtain rfl | hr := eq_top_or_lt_top r
  · simp
  · lift r to ℝ≥0 using hr.ne
    simpa only [Metric.closedEBall_coe] using Measure.addHaar_closedBall_center volume x (r : ℝ)

section

open _root_.ENNReal _root_.NNReal

lemma Metric.IsSeparated.disjoint_closedBall {E : Type*} [PseudoEMetricSpace E] {s : Set E}
    {ε : ℝ≥0∞} (hs : IsSeparated ε s) : s.PairwiseDisjoint (Metric.closedEBall · (ε / 2)) := by
  intro x hx y hy hxy
  have hxy := hs hx hy hxy
  by_contra!
  obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.1 this
  refine lt_irrefl (edist x y) ?_ |>.elim
  calc
  edist x y ≤ edist x z + edist y z := edist_triangle_right x y z
  _ ≤ ε / 2 + ε / 2 := by grw [Metric.mem_closedEBall'.1 hz1, Metric.mem_closedEBall'.1 hz2]
  _ < edist x y := by rwa [ENNReal.add_halves]

@[simp]
lemma Metric.nonempty_closedEBall {E : Type*} [PseudoEMetricSpace E] {x : E} {r : ℝ≥0∞} :
    (closedEBall x r).Nonempty := ⟨x, mem_closedEBall_self⟩

open scoped Pointwise in
lemma Metric.closedEBall_add_closedEBall {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (x y : E) (r s : ℝ≥0∞) :
    closedEBall x r + closedEBall y s = closedEBall (x + y) (r + s) := by
  by_cases h : r = ⊤ ∨ s = ⊤
  · obtain rfl | rfl := h <;> simp [nonempty_closedEBall]
  simp only [not_or] at h
  lift r to ℝ≥0 using h.1
  lift s to ℝ≥0 using h.2
  norm_cast
  simp_rw [Metric.closedEBall_coe]
  rw [_root_.closedBall_add_closedBall, NNReal.coe_add]
  all_goals simp

end
section
lemma zero_mem_parallelepiped {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {v : ι → E} :
    0 ∈ parallelepiped v := ⟨0, by simp, by simp⟩

@[simp]
lemma nonempty_parallelepiped {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {v : ι → E} :
    (parallelepiped v).Nonempty := ⟨0, zero_mem_parallelepiped⟩

@[simp, nontriviality]
lemma volume_of_nonempty_of_subsingleton {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [Subsingleton E] {s : Set E} (hs : s.Nonempty) :
    volume s = 1 := by
  rw [Subsingleton.eq_univ_of_nonempty hs,
    ← Subsingleton.eq_univ_of_nonempty (nonempty_parallelepiped (v := stdOrthonormalBasis ℝ E))]
  exact (stdOrthonormalBasis ℝ E).toBasis.addHaar_self

lemma InnerProductSpace.volume_closedBall_div {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    volume (closedBall x r) / volume (closedBall y s) =
      ENNReal.ofReal (r / s) ^ (Module.finrank ℝ E) := by
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp [hr.le, hs.le, Module.finrank_zero_of_subsingleton]
  rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall,
    ENNReal.mul_div_mul_right _ _ (by positivity) (by simp)]
  simp_rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.div_rpow_of_nonneg _ _ (by simp), ENNReal.ofReal_div_of_pos hs]

lemma InnerProductSpace.volume_closedBall_div' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) (r s : ℝ≥0∞) :
    volume (Metric.closedEBall x r) / volume (Metric.closedEBall y s) =
      (r / s) ^ (Module.finrank ℝ E) := by
  nontriviality E
  have hdim : Module.finrank ℝ E ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
  obtain rfl | hr := eq_top_or_lt_top r <;> obtain rfl | hs := eq_top_or_lt_top s
  · simp [hdim]
  · lift s to ℝ≥0 using hs.ne
    simp [hdim, ENNReal.top_div, closedEBall_coe, (isCompact_closedBall _ _).measure_ne_top]
  · simp [hdim]
  · obtain rfl | hr' := eq_zero_or_pos r <;> obtain rfl | hs' := eq_zero_or_pos s
    · simp [hdim]
    · simp [hdim]
    · simp [hdim, ENNReal.div_zero, hr'.ne', Metric.measure_closedEBall_pos volume x hr'.ne' |>.ne']
    lift r to ℝ≥0 using hr.ne
    lift s to ℝ≥0 using hs.ne
    simp_rw [closedEBall_coe]
    rw [volume_closedBall_div, ENNReal.ofReal_div_of_pos]
    · simp
    all_goals simp_all

end
section

open _root_.EMetric _root_.Set _root_.Metric DOZZ.Proofs.Metric

section PseudoEMetricSpace

variable {E : Type*} [PseudoEMetricSpace E] {r ε ε' : ℝ≥0} {A B C : Set E}

lemma TotallyBounded.coveringNumber_ne_top (hA : TotallyBounded A) {r : ℝ≥0} (hr : r ≠ 0) :
    coveringNumber r A ≠ ⊤:= by
  obtain ⟨C, hC_subset, hC_finite, hC_cov⟩ := exists_finite_isCover_of_totallyBounded hr hA
  refine ne_top_of_le_ne_top (b := C.encard) ?_ (IsCover.coveringNumber_le_encard hC_subset hC_cov)
  simpa

end PseudoEMetricSpace

section Volume

open MeasureTheory

section PseudoEMetricSpace
variable {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0} {s N : Set X}

end PseudoEMetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ε : ℝ≥0} {A : Set E} {C : Set E}

open scoped Pointwise in
lemma le_volume_of_isSeparated_of_countable (hC_count : C.Countable)
    (hC : IsSeparated ε C) (h_subset : C ⊆ A) :
    C.encard * volume (Metric.closedEBall (0 : E) (ε / 2))
      ≤ volume (A + Metric.closedEBall (0 : E) (ε / 2)) := by
  calc
  C.encard * volume (Metric.closedEBall (0 : E) (ε / 2)) =
      ∑' x : C, volume (Metric.closedEBall (x : E) (ε / 2)) := by
    simp_rw [fun x ↦ volume_closedEBall_center x,
      ENNReal.tsum_const]
    simp
  _ = volume (⋃ x ∈ C, Metric.closedEBall x (ε / 2)) := by
    rw [measure_biUnion]
    · exact hC_count
    · exact DOZZ.Proofs.Metric.IsSeparated.disjoint_closedBall hC
    · exact fun _ _ ↦ Metric.isClosed_closedEBall.measurableSet
  _ ≤ volume (A + Metric.closedEBall (0 : E) (ε / 2)) := by
    refine measure_mono fun x hx ↦ ?_
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨y, hy, hx⟩ := hx
    refine ⟨y, h_subset hy, x - y, ?_, by simp⟩
    rwa [Metric.mem_closedEBall, edist_zero_right, ← edist_eq_enorm_sub]

open scoped Pointwise in
lemma le_volume_of_isSeparated (hC : IsSeparated ε C) (h_subset : C ⊆ A) :
    C.encard * volume (Metric.closedEBall (0 : E) (ε / 2))
      ≤ volume (A + Metric.closedEBall (0 : E) (ε / 2)) := by
  obtain rfl | hε := eq_zero_or_pos ε
  · simp only [ENNReal.coe_zero, ENNReal.zero_div, Metric.closedEBall_zero,
      Measure.addHaar_singleton, add_singleton, add_zero, image_id']
    obtain _ | _ := subsingleton_or_nontrivial E
    · simp only [singleton_nonempty, volume_of_nonempty_of_subsingleton, mul_one]
      obtain rfl | hA := Set.eq_empty_or_nonempty A
      · simp only [subset_empty_iff] at h_subset
        simp [h_subset]
      simp only [hA.eq_zero, Measure.addHaar_singleton, singleton_nonempty,
        volume_of_nonempty_of_subsingleton]
      norm_cast
      refine (Set.encard_le_encard h_subset).trans ?_
      simp [hA.eq_zero]
    · simp
  by_cases hC_encard : C.encard = ⊤
  swap
  · have hC_count : C.Countable := by
      refine Set.Finite.countable ?_
      simpa using hC_encard
    exact le_volume_of_isSeparated_of_countable hC_count hC h_subset
  suffices volume (A + Metric.closedEBall 0 (↑ε / 2)) = ∞ by simp [this]
  obtain ⟨C', hC'_subset, hC'_sep, hC'_count, hC'_encard⟩ :
      ∃ C' ⊆ C, IsSeparated ε C' ∧ C'.Countable ∧ C'.encard = ⊤ := by
    suffices ∃ C' ⊆ C, C'.Countable ∧ C'.encard = ⊤ by
      obtain ⟨C', hC'_subset, hC'_count, hC'_encard⟩ := this
      exact ⟨C', hC'_subset, hC.mono hC'_subset, hC'_count, hC'_encard⟩
    simp only [encard_eq_top_iff] at hC_encard ⊢
    refine ⟨Set.range (fun n : ℕ ↦ hC_encard.natEmbedding C n), fun x ↦ ?_, ?_, ?_⟩
    · simp only [mem_range, forall_exists_index]
      rintro _ ⟨n, rfl⟩
      simp
    · exact countable_range _
    · refine infinite_range_of_injective fun n m hnm ↦ ?_
      apply (hC_encard.natEmbedding C).injective
      exact SetCoe.ext hnm
  have h_le := le_volume_of_isSeparated_of_countable hC'_count hC'_sep (hC'_subset.trans h_subset)
  rw [hC'_encard, ENat.toENNReal_top, ENNReal.top_mul] at h_le
  · simpa using h_le
  · refine (Metric.measure_closedEBall_pos volume _ ?_).ne'
    simp [hε.ne']

open scoped Pointwise in
lemma volume_eq_top_of_packingNumber (A : Set E) (hε : 0 < ε)
    (h : packingNumber ε A = ⊤) : volume (A + Metric.closedEBall (0 : E) (ε / 2)) = ∞ := by
  set X := {C : Set E | C ⊆ A ∧ IsSeparated ε C}
  rw [packingNumber] at h
  have : ⨆ C : Set E, ⨆ (_ : C ⊆ A), ⨆ (_ : IsSeparated ε C),
      C.encard * volume (Metric.closedEBall (0 : E) (ε / 2)) = ⊤ := by
    simp_rw [← ENNReal.iSup_mul, ← ENat.toENNReal_iSup, h]
    rw [ENat.toENNReal_top, ENNReal.top_mul]
    exact Metric.measure_closedEBall_pos volume _
        (ENNReal.div_ne_zero.2 ⟨mod_cast hε.ne', by norm_num⟩) |>.ne'
  rw [eq_top_iff, ← this]
  exact iSup_le fun C ↦ iSup₂_le fun hC₁ hC₂ ↦ le_volume_of_isSeparated hC₂ hC₁

open scoped Pointwise in
lemma packingNumber_mul_le_volume (A : Set E) (ε : ℝ≥0) :
    packingNumber ε A * volume (Metric.closedEBall (0 : E) (ε / 2))
      ≤ volume (A + Metric.closedEBall (0 : E) (ε / 2)) := by
  obtain rfl | hε := eq_zero_or_pos ε
  · obtain _ | _ := subsingleton_or_nontrivial E
    · obtain rfl | hA := Set.eq_empty_or_nonempty A
      · simp
      rw [hA.eq_zero]
      simp
    · simp
  obtain h | h := eq_top_or_lt_top (packingNumber ε A)
  · simp [volume_eq_top_of_packingNumber A hε h]
  rw [← encard_maximalSeparatedSet h.ne]
  exact le_volume_of_isSeparated isSeparated_maximalSeparatedSet maximalSeparatedSet_subset

open scoped Pointwise in
lemma coveringNumber_le_volume_div (A : Set E) (hε₁ : 0 < ε) :
    coveringNumber ε A
      ≤ volume (A + Metric.closedEBall (0 : E) (ε / 2))
        / volume (Metric.closedEBall (0 : E) (ε / 2)) := by
  grw [coveringNumber_le_packingNumber, ENNReal.le_div_iff_mul_le,
    packingNumber_mul_le_volume]
  · exact Or.inl <| Metric.measure_closedEBall_pos volume _
      (ENNReal.div_ne_zero.2 ⟨mod_cast hε₁.ne', by norm_num⟩) |>.ne'
  · rw [show (ε : ℝ≥0∞) / 2 = ↑(ε / 2) by simp, Metric.closedEBall_coe]
    exact Or.inl <| ProperSpace.isCompact_closedBall _ _ |>.measure_ne_top

lemma coveringNumber_closedBall_le (ε : ℝ≥0) (x : E) (r : ℝ≥0) :
    (coveringNumber ε (Metric.closedEBall x r) : ℝ≥0∞)
      ≤ (2 * r / (ε : ℝ≥0∞) + 1) ^ (Module.finrank ℝ E) := by
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp only [Module.finrank_zero_of_subsingleton, pow_zero]
    norm_cast
    grw [coveringNumber_le_encard_self, Set.encard_le_one_iff]
    exact fun a b _ _ ↦ Subsingleton.allEq a b
  obtain rfl | hr := eq_zero_or_pos r
  · simp
  obtain rfl | hε' := eq_zero_or_pos ε
  · simp [ENNReal.div_zero, hr.ne', (Module.finrank_pos (R := ℝ) (M := E)).ne']
  grw [coveringNumber_le_volume_div (Metric.closedEBall x r),
    Metric.closedEBall_add_closedEBall, InnerProductSpace.volume_closedBall_div',
    ← ENNReal.div_mul, ENNReal.add_div, ← mul_one_div (ε / 2 : ℝ≥0∞), ← ENNReal.mul_div_mul_comm,
    mul_comm (ε : ℝ≥0∞) 1, ENNReal.mul_div_mul_right, add_mul, ENNReal.div_mul_cancel,
    ENNReal.mul_comm_div, mul_comm (2 : ℝ≥0∞), mul_div_assoc]
  all_goals simp_all [hε'.ne']

end Volume

end
section
variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {d : ℝ}
/-- The covering condition at scale `diam A` bounds the diameter of `A` by `c ^ (1/d)`. -/
lemma HasBoundedCoveringNumber.ediam_le
    (h : HasBoundedCoveringNumber A c d) (hd : 0 < d) :
    Metric.ediam A ≤ c ^ d⁻¹ := by
  rcases eq_or_ne (Metric.ediam A) 0 with h0 | h0
  · simp [h0]
  have hA : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at h0
  have hε : ((Metric.ediam A).toNNReal : ℝ≥0∞) = Metric.ediam A :=
    ENNReal.coe_toNNReal h.ediam_lt_top.ne
  have h1 : 1 ≤ c * (Metric.ediam A)⁻¹ ^ d := by
    refine le_trans ?_ (hε ▸ h.coveringNumber_le (Metric.ediam A).toNNReal hε.le)
    exact_mod_cast Order.one_le_iff_pos.mpr (coveringNumber_pos_iff.mpr hA)
  have h2 : Metric.ediam A ^ d ≤ c := by
    have := mul_le_mul' h1 (le_refl (Metric.ediam A ^ d))
    rwa [one_mul, mul_assoc, ← ENNReal.mul_rpow_of_ne_top (by simp [h0]) h.ediam_lt_top.ne,
      ENNReal.inv_mul_cancel h0 h.ediam_lt_top.ne, ENNReal.one_rpow, mul_one] at this
  calc Metric.ediam A = (Metric.ediam A ^ d) ^ d⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hd.ne', ENNReal.rpow_one]
    _ ≤ c ^ d⁻¹ := ENNReal.rpow_le_rpow h2 (by positivity)

end
structure IsCoverWithBoundedCoveringNumber {T : Type*} [PseudoEMetricSpace T]
    (C : ℕ → Set T) (A : Set T) (c : ℕ → ℝ≥0∞) (d : ℕ → ℝ)
    where
  c_ne_top : ∀ n, c n ≠ ∞
  d_pos : ∀ n, 0 < d n
  isOpen : ∀ n, IsOpen (C n)
  totallyBounded : ∀ n, TotallyBounded (C n)
  hasBoundedCoveringNumber : ∀ n, HasBoundedCoveringNumber (C n) (c n) (d n)
  mono : ∀ n m, n ≤ m → C n ⊆ C m
  subset_iUnion : A ⊆ ⋃ i, C i

/-- A closed ball in a nontrivial finite-dimensional Hilbert space has an explicit
covering exponent equal to the real dimension. -/
theorem hasCoveringExponent_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] (x : E) (r : ℝ≥0) (hr : 0 < r) :
    Metric.HasCoveringExponent (Metric.closedEBall x r)
      ((4*r : ℝ≥0∞) ^ (Module.finrank ℝ E)) (Module.finrank ℝ E) := by
  have hdim : Module.finrank ℝ E ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
  constructor
  · exact lt_of_le_of_lt Metric.ediam_closedEBall_le (by finiteness)
  · intro ε hε
    obtain rfl | hεpos := eq_zero_or_pos ε
    · simp [hdim, hr.ne']
    have hdiam : Metric.ediam (Metric.closedEBall x r) ≤ 2*r := Metric.ediam_closedEBall_le
    have hεle : (ε : ℝ≥0∞) ≤ 2*r := hε.trans hdiam
    have hrat : (1 : ℝ≥0∞) ≤ 2*r/ε := by
      rw [ENNReal.le_div_iff_mul_le]
      · simpa using hεle
      · simp [hεpos.ne']
      · simp
    calc
      _ ≤ (2*r/(ε : ℝ≥0∞)+1) ^ (Module.finrank ℝ E) := coveringNumber_closedBall_le ε x r
      _ ≤ (4*r/(ε : ℝ≥0∞)) ^ (Module.finrank ℝ E) := by
        apply pow_le_pow_left'
        calc
          _ ≤ 2*r/(ε : ℝ≥0∞)+2*r/(ε : ℝ≥0∞) := add_le_add le_rfl hrat
          _ = _ := by rw [← ENNReal.add_div, ← add_mul]; norm_num
      _ = _ := by
        simp only [div_eq_mul_inv, mul_pow, ENNReal.rpow_natCast]

/-- Increasing open balls give an explicit bounded-covering exhaustion of a
nontrivial finite-dimensional Hilbert parameter space. -/
theorem isCoverWithBoundedCoveringNumber_balls (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] :
    IsCoverWithBoundedCoveringNumber (fun n : ℕ => Metric.ball (0 : E) ((n : ℝ)+1))
      Set.univ (fun n => (2 : ℝ≥0∞)^(Module.finrank ℝ E) *
        (4*((n : ℝ≥0∞)+1))^(Module.finrank ℝ E)) (fun _ => (Module.finrank ℝ E : ℝ)) := by
  constructor
  · intro n
    finiteness
  · intro n
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  · intro n
    exact Metric.isOpen_ball
  · intro n
    exact (isCompact_closedBall (0 : E) ((n : ℝ)+1)).totallyBounded.subset
      Metric.ball_subset_closedBall
  · intro n
    have hcl := hasCoveringExponent_closedBall (0 : E) (n+1) (by positivity)
    simp only [Metric.closedEBall_coe, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at hcl
    have hs := Metric.HasCoveringExponent.subset hcl (Metric.ball_subset_closedBall
      (x := (0 : E)) (ε := ((n : ℝ)+1))) (Nat.cast_nonneg (Module.finrank ℝ E))
    simpa only [Metric.closedEBall_coe, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
      ENNReal.rpow_natCast, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one] using hs
  · intro n m hnm
    exact Metric.ball_subset_ball (add_le_add_left (Nat.cast_le.mpr hnm) 1)
  · intro x _
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hn.trans (lt_add_one _)

end DOZZ.Proofs
