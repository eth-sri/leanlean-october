/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume

/-! Reduce a fundamental domain modulo a short sublattice. The resulting
fundamental domain of the full lattice fits in the short parallelepiped,
so finite packing needs no count of cosets. -/

@[expose] public section
namespace CCDN
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped Pointwise NNReal

private theorem fundamentalDomain_finite_translate_packing
    {G E : Type*} [AddGroup G] [MeasurableSpace E] [AddAction G E]
    [MeasurableConstVAdd G E] (μ : Measure E) [VAddInvariantMeasure G E μ]
    {F U : Set E} (hF : IsAddFundamentalDomain G F μ)
    (s : Finset G) (hs : ∀ g ∈ s, g +ᵥ F ⊆ U) :
    (s.card : ENNReal) * μ F ≤ μ U := by
  classical
  have hd : Pairwise (Function.onFun (AEDisjoint μ) (fun g : s ↦ g.val +ᵥ F)) := by
    intro a b hab
    apply hF.aedisjoint
    exact fun h ↦ hab (Subtype.ext h)
  have hm := measure_iUnion₀ hd (fun g : s ↦ hF.nullMeasurableSet.vadd g.val)
  have he : (∑' g : s, μ (g.val +ᵥ F)) = (s.card : ENNReal) * μ F := by
    simp
  rw [he] at hm
  rw [← hm]
  apply measure_mono
  exact Set.iUnion_subset (fun g ↦ hs g.val g.property)

/-- Intersect the short parallelepiped with all short-lattice translates
of a fundamental domain of the ambient lattice. This folds the ambient
fundamental domain into the short one without changing its covolume. -/
private theorem exists_bounded_subdomain {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (b : Module.Basis ι ℝ E) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hb : ∀ i, b i ∈ L) (μ : Measure E) :
    ∃ F, IsAddFundamentalDomain L F μ ∧ F ⊆ ZSpan.fundamentalDomain b := by
  let Q := Submodule.span ℤ (Set.range b)
  have hQL := Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)
  let c := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hc := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  let U := ZSpan.fundamentalDomain b
  let V := ZSpan.fundamentalDomain c
  let F := U ∩ ⋃ q : Q, (q : E) +ᵥ V
  have hF {x : E} (hx : x ∈ F) : ZSpan.fract b (ZSpan.fract c x) = x := by
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx.2
    obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hq
    rw [vadd_eq_add, ZSpan.fract_zSpan_add c z (hc.ge (hQL q.property)), ZSpan.fract_eq_self.mpr hz,
      ← ZSpan.fract_zSpan_add b z q.property]
    exact ZSpan.fract_eq_self.mpr hx.1
  have hmeas : MeasurableSet F := (ZSpan.fundamentalDomain_measurableSet b).inter
    (MeasurableSet.iUnion fun q => MeasurableSet.const_vadd (ZSpan.fundamentalDomain_measurableSet c) (q : E))
  refine ⟨F, IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet ?_, Set.inter_subset_left⟩
  intro x
  let z := ZSpan.fract c x
  let q : Q := -ZSpan.floor b z
  let g : L := ⟨(q : E) - ZSpan.floor c x, L.sub_mem (hQL q.property) (hc.le (ZSpan.floor c x).property)⟩
  have hg : g +ᵥ x = ZSpan.fract b z := by
    change -(ZSpan.floor b z : E) - ZSpan.floor c x + x = _
    simp only [z, ZSpan.fract_apply]; abel
  refine ⟨g, ?_, fun k hk => ?_⟩
  · change g +ᵥ x ∈ F
    rw [hg]
    refine ⟨ZSpan.fract_mem_fundamentalDomain _ _, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    exact Set.mem_vadd_set.mpr ⟨z, ZSpan.fract_mem_fundamentalDomain _ _, by
      simp only [q, vadd_eq_add, Submodule.coe_neg, ZSpan.fract_apply]; abel⟩
  · apply Subtype.ext
    apply add_right_cancel (b := x)
    change k +ᵥ x = g +ᵥ x
    rw [hg, ← hF hk]
    exact congrArg (ZSpan.fract b) (ZSpan.fract_zSpan_add c x (hc.ge k.property))

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
      (B + Fintype.card ι * M) ^ Module.finrank ℝ E *
        volume.real (Metric.ball (0 : E) 1) := by
  have hsum : ∑ i, ‖b i‖ ≤ Fintype.card ι * M := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hnorm i)
  let R := B + Fintype.card ι * M
  have hR : 0 ≤ R := by positivity
  obtain ⟨F, hF, hsub⟩ := exists_bounded_subdomain b L hb volume
  have : VAddInvariantMeasure L E volume := inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E volume)
  have hm := fundamentalDomain_finite_translate_packing volume hF s
    (U := Metric.closedBall (0 : E) R) (by
      intro x hx y hy
      obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hy
      apply mem_closedBall_zero_iff.mpr
      rw [← ZSpan.fract_eq_self.mpr (hsub hz)]
      exact (norm_add_le _ _).trans (add_le_add (hs x hx) ((ZSpan.norm_fract_le b z).trans hsum)))
  have hr := ENNReal.toReal_mono (isCompact_closedBall (0 : E) _).measure_lt_top.ne hm
  change _ ≤ R ^ _ * _
  rw [← volume.addHaar_real_closedBall (0 : E) hR]
  simpa [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, ENNReal.toReal_mul, Measure.real] using hr

end
end CCDN
