/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume

/-! A finite set of lattice points gives disjoint translates of a
fundamental domain. A bounded basis therefore gives an explicit
finite-radius volume bound, without an asymptotic onset depending on the
lattice. -/

@[expose] public section
namespace CCDN
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped Pointwise NNReal

/-- Polynomial-radius form of the finite packing estimate. The constant
is explicit and depends only on the dimension and on the basis bound. -/
theorem superlattice_finite_packing_polynomial
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hb : ∀ i, b i ∈ L)
    (s : Finset L) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hs : ∀ x ∈ s, ‖(x : E)‖ ≤ B) (hnorm : ∀ i, ‖b i‖ ≤ M) :
    (s.card : ℝ) * ZLattice.covolume L ≤
      (2 * B + Fintype.card ι * M) ^ Module.finrank ℝ E *
        volume.real (Metric.ball (0 : E) 1) := by
  classical
  let L₀ := Submodule.span ℤ (Set.range b)
  have hle : L₀ ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' L₀ L hle
  have hpos : (0 : ℝ) < L₀.toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hratio]; exact div_pos (ZLattice.covolume_pos L₀) (ZLattice.covolume_pos L)
  have hindex : L₀.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := mod_cast hpos.ne'
  let H := L₀.toAddSubgroup.addSubgroupOf L.toAddSubgroup
  let Q := L ⧸ H
  let : Fintype Q := H.fintypeOfIndexNeZero hindex
  let q : L → Q := QuotientAddGroup.mk
  have hfiber (a : Q) :
      ((s.filter (fun x ↦ q x = a)).card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
        volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) := by
    let u := (s.filter (fun x ↦ q x = a)).image (fun x : L ↦ (x : E))
    have hcard : u.card = (s.filter (fun x ↦ q x = a)).card :=
      Finset.card_image_of_injective _ (Subtype.val_injective : Function.Injective (fun x : L ↦ (x : E)))
    rw [← hcard]
    obtain h0 | ⟨y, hy⟩ := u.eq_empty_or_nonempty
    · rw [h0]; simp only [Finset.card_empty, Nat.cast_zero, zero_mul]; exact ENNReal.toReal_nonneg
    have huB (x : E) (hx : x ∈ u) : ‖x‖ ≤ B := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hs z (Finset.mem_filter.mp hz).1
    have hucos (x : E) (hx : x ∈ u) (z : E) (hz : z ∈ u) : x - z ∈ L₀ := by
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
      exact QuotientAddGroup.eq_iff_sub_mem.mp
        ((Finset.mem_filter.mp hx').2.trans (Finset.mem_filter.mp hz').2.symm)
    have : MeasurableVAdd L₀ E := inferInstanceAs (MeasurableVAdd L₀.toAddSubgroup E)
    have : VAddInvariantMeasure L₀ E volume :=
      inferInstanceAs (VAddInvariantMeasure L₀.toAddSubgroup E volume)
    let e : u ↪ L₀ := ⟨fun x ↦ ⟨x.val - y, hucos x.val x.property y hy⟩,
      fun x z h ↦ Subtype.ext (sub_left_injective (congrArg Subtype.val h))⟩
    let t : Finset L₀ := Finset.univ.map e
    let F := ZSpan.fundamentalDomain b
    have hF := ZSpan.isAddFundamentalDomain b volume
    have hd : Pairwise (Function.onFun (AEDisjoint volume) (fun g : t ↦ g.val +ᵥ F)) :=
      fun x z hxz ↦ hF.aedisjoint fun h ↦ hxz (Subtype.ext h)
    have hm := measure_iUnion₀ hd (fun g : t ↦ hF.nullMeasurableSet.vadd g.val)
    rw [show (∑' g : t, volume (g.val +ᵥ F)) = (t.card : ENNReal) * volume F by
      simp [measure_vadd, tsum_fintype]] at hm
    have hsub : (⋃ g : t, g.val +ᵥ F) ⊆ Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖) := by
      refine Set.iUnion_subset fun g _ hmem ↦ ?_
      obtain ⟨x, _, hgx⟩ := Finset.mem_map.mp g.property
      obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hmem
      rw [mem_closedBall_zero_iff, ← hgx]
      change ‖(x.val - y) + z‖ ≤ _
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (by linarith [huB x.val x.property, huB y hy]))
        (by rw [← ZSpan.fract_eq_self.mpr hz]; exact ZSpan.norm_fract_le b z))
    have hh := hm ▸ measure_mono hsub
    have hfin : volume (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) ≠ ⊤ :=
      ne_of_lt (isCompact_closedBall (0 : E) _).measure_lt_top
    simpa [t, F, ENNReal.toReal_mul, ENNReal.toReal_natCast, Measure.real] using
      ENNReal.toReal_mono hfin hh
  have hi : Fintype.card Q = L₀.toAddSubgroup.relIndex L.toAddSubgroup :=
    (Nat.card_eq_fintype_card (α := Q)).symm
  have hp : (s.card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
      (L₀.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) *
        volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := q) (fun _ _ ↦ Finset.mem_univ _),
      Nat.cast_sum, Finset.sum_mul]
    exact (Finset.sum_le_sum fun a _ ↦ hfiber a).trans_eq (by simp [hi])
  have hvol : ZLattice.covolume L₀ = volume.real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L₀ volume
      (ZSpan.isAddFundamentalDomain b volume)
  have hc : ZLattice.covolume L₀ =
      (L₀.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L :=
    (div_eq_iff (ZLattice.covolume_pos L).ne').mp hratio
  rw [← hvol, hc] at hp
  have hpack : (s.card : ℝ) * ZLattice.covolume L ≤
      volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) :=
    (mul_le_mul_iff_right₀ hpos).mp (by nlinarith only [hp])
  have hsum : ∑ i, ‖b i‖ ≤ Fintype.card ι * M := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hnorm i
  exact (hpack.trans (measureReal_mono (Metric.closedBall_subset_closedBall (by linarith))
    (isCompact_closedBall (0 : E) _).measure_lt_top.ne)).trans_eq
    (volume.addHaar_real_closedBall (0 : E) (by positivity))

end
end CCDN
