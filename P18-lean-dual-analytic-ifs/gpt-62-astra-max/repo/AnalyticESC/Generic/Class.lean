module

public import AnalyticESC.Basic

@[expose] public section

/-!
# The classes `S^ω_ε(I)` and `S^ω(I)`

The inclusion `f(cl B_ε) ⊆ B_ε` in condition (B) of the class `S^ω_ε(I)` follows from the other
conditions. Hence the classes `S^ω_ε(I)` decrease as `ε` increases, and their union `S^ω(I)` is
described by conditions on `[0,1]`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Every point of `cl B_ε` lies within distance `ε` of a point of `I`. -/
theorem exists_mem_I_norm_sub_le {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  rw [nbhd_eq] at hz
  have hz' := closure_thickening_subset_cthickening ε _ hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall hε] at hz'
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
  exact ⟨x, hx, mem_closedBall_iff_norm.1 hzx⟩

/-- All finitely many maps satisfy the derivative constraints on a common open
neighbourhood of the interval. A sufficiently thin tube lies in it. -/
lemma common_class {N} {c : ℝ} (hc : c ∈ Ioo 0 1) {f : Maps N} {U : Set ℂ} (ho : IsOpen U) (hU : ∀ x ∈ I, (x:ℂ) ∈ U)
    (hd : ∀ i, DifferentiableOn ℂ (f i) U) (him : ∀ i (x:ℝ), (x:ℂ) ∈ U → (f i x).im = 0)
    (hI : ∀ i (x:ℝ), x ∈ I → (f i x).re ∈ I) (hr : ∀ i (x:ℝ), x ∈ I → ‖deriv (f i) x‖ ∈ Ioo 0 c) :
    ∃ ε > 0, (∀ i, InClass ε (f i)) ∧ Challenge.cmax ε f < c := by
  let V i := U ∩ (fun z => ‖deriv (f i) z‖) ⁻¹' Ioo 0 c
  have hV i : IsOpen (V i) := (hd i |>.deriv ho).continuousOn.norm.isOpen_inter_preimage ho isOpen_Ioo
  obtain ⟨r,h,hsub⟩ := isCompact_image_I.exists_thickening_subset_open (ho.inter (isOpen_iInter_of_finite hV))
    (show Complex.ofReal '' I ⊆ U ∩ ⋂ i, V i by rintro _ ⟨x,hx,rfl⟩; aesop)
  rw [← nbhd_eq] at hsub
  let ε := r/2
  have he := half_pos h
  have h2 : nbhd (2*ε) ⊆ U ∩ ⋂ i, V i := by grind
  have reg i z (hz : z ∈ closure (nbhd ε)) := (mem_iInter.mp (h2 (cl_two he hz)).2 i).2
  have H i : InClass ε (f i) := by
    refine ⟨(hd i).mono fun _ hz => (h2 hz).1,fun x hx => him i x (h2 hx).1,hI i,?_,
      fun z hz => norm_pos_iff.mp (reg i z hz).1,fun z hz => (reg i z hz).2.trans hc.2⟩
    intro z hz
    obtain ⟨x,hx,D⟩ := exists_mem_I_norm_sub_le he.le hz
    have L := (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hd i).differentiableAt (ho.mem_nhds (h2 (cl_two he hy)).1)) (fun y hy => (reg i y hy).2.le)
      (subset_closure (ofReal_mem_nbhd he hx)) hz
    refine ⟨_,hI i x hx,?_⟩
    rw [show (((f i x).re:ℝ):ℂ) = f i x from Complex.ext rfl (him i x (hU x hx)).symm]
    exact L.trans_lt ((mul_le_mul_of_nonneg_left D hc.1.le).trans_lt (mul_lt_of_lt_one_left he hc.2))
  exact ⟨ε,he,H,(⟨f,he,H⟩ : IFS N).cmax_lt hc.1 fun i z hz => (reg i z hz).2⟩

end AnalyticESC
