module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Continuation
public import PottsDiscontinuity.Bethe.Theorem23LocalSection

/-! # Compact continuation of analytic implicit roots -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × E → E} {C : Set E} (hC : IsCompact C) {a b : ℝ}
include E F C hC a b

/-- A compact state region with only interior regular roots has one unique root
at every parameter of an interval if its base fiber is unique. -/
theorem unique_implicit_roots_on_interval
    
    (hF : ∀ t ∈ Icc a b, ∀ x ∈ C, AnalyticAt ℝ F (t, x))
    (hregular : ∀ t ∈ Icc a b, ∀ x ∈ C, F (t, x) = 0 →
      x ∈ interior C ∧ ∃ e : E ≃L[ℝ] E,
        (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) = (e : E →L[ℝ] E))
    (t₀ : Icc a b) (hbase : ∃! x : C, F (t₀.val, x.val) = 0) :
    ∀ t : Icc a b, ∃! x : C, F (t.val, x.val) = 0 := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  
  apply unique_roots_of_compact_local_sections (fun t  => fun x : C => F (t.val, x.val) = 0)
    (isClosed_eq (by
                    apply continuous_iff_continuousAt.mpr
                    intro z
                    exact ContinuousAt.comp
                      (f := fun w :  Icc a b  × C => (w.1.val, w.2.val)) (g := F)
                      (hF z.1.val z.1.property z.2.val z.2.property).continuousAt
                      (by fun_prop)) continuous_const) _ t₀ hbase
  intro t x hx
  obtain ⟨hinterior, e, he⟩ := hregular t.val t.property x.val x.property hx
  exact local_section_of_analytic_regular_interior_zero t x
    (hF t.val t.property x.val x.property) hx hinterior e he

/-- Compact analytic continuation, with an open interval extending past the
right endpoint. The root selector is chosen only after every fiber has been
proved unique; local uniqueness identifies it with the analytic IFT branches. -/
theorem exists_analytic_implicit_family_on_open_interval
     (hab : a < b)
    (hF : ∀ t ∈ Icc a b, ∀ x ∈ C, AnalyticAt ℝ F (t, x))
    (hregular : ∀ t ∈ Icc a b, ∀ x ∈ C, F (t, x) = 0 →
      x ∈ interior C ∧ ∃ e : E ≃L[ℝ] E,
        (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) = (e : E →L[ℝ] E))
    (hbase : ∃! x : C, F (b, x.val) = 0) :
    ∃ b' : ℝ, b < b' ∧ ∃ ψ : ℝ → E,
      AnalyticOnNhd ℝ ψ (Ioo a b') ∧
      (∀ t ∈ Ioo a b', F (t, ψ t) = 0) ∧
       ∀ t ∈ Icc a b, ψ t ∈ C ∧ F (t, ψ t) = 0  := by
  
  have hunique := unique_implicit_roots_on_interval hC hF hregular
     ⟨b, ⟨hab.le, le_rfl⟩⟩  hbase
  let q  := fun t => (hunique t).choose
  have hq (t : Icc a b)  := (hunique t).choose_spec.1
  let tb : Icc a b := ⟨b, ⟨hab.le, le_rfl⟩⟩
  obtain ⟨hbInterior, eb, heb⟩ := hregular b tb.property (q tb).val (q tb).property (hq tb)
  obtain ⟨η, hηbase, hηanalytic, Wb, Vb, hWb, hVb, hWbbase, hVbbase, hηroot, hηunique⟩ :=
    PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction_with_local_uniqueness
      (hF b tb.property (q tb).val (q tb).property) (hq tb) eb heb
  
  
  let ψ  := fun t => if ht : t ∈ Icc a b then (q ⟨t, ht⟩).val else η t
  
  have hηψ : η =ᶠ[𝓝 b] ψ := by
    filter_upwards [ by
                       apply hηanalytic.continuousAt.eventually
                       rw [hηbase]
                       exact mem_interior_iff_mem_nhds.mp hbInterior ,  by
                            filter_upwards [hVb.mem_nhds hVbbase] with t ht
                            exact (hηroot t ht).2 ] with t ht hzero
    by_cases hmem : t ∈ Icc a b
    · have heq :  ⟨η t, ht⟩  = q ⟨t, hmem⟩ :=
        (hunique ⟨t, hmem⟩).unique hzero (hq ⟨t, hmem⟩)
      simpa only [ψ, dite_eq_left hmem] using congrArg Subtype.val heq
    · simp only [ψ, dite_eq_right hmem]
  
  have hψzerob : ∀ᶠ t in 𝓝 b, F (t, ψ t) = 0 := by
    filter_upwards [ by
                       filter_upwards [hVb.mem_nhds hVbbase] with t ht
                       exact (hηroot t ht).2 , hηψ] with t ht heq
    rw [← heq]
    exact ht
  obtain ⟨l, b', hlb, hnear⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hηanalytic.congr hηψ).eventually_analyticAt.and hψzerob)
  have hψanalyticInterior (t) (ht : t ∈ Ioo a b) : AnalyticAt ℝ ψ t := by
    let tt : Icc a b := ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
    obtain ⟨hinterior, e, he⟩ := hregular t tt.property (q tt).val (q tt).property (hq tt)
    obtain ⟨φ, hφbase, hφanalytic, hφzero⟩ :=
      PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction
        (hF t tt.property (q tt).val (q tt).property) (hq tt) e he
    
    apply hφanalytic.congr
    filter_upwards [ by
                       apply hφanalytic.continuousAt.eventually
                       rw [hφbase]
                       exact mem_interior_iff_mem_nhds.mp hinterior , hφzero, isOpen_Ioo.mem_nhds ht] with u hu hzero hIoo
    have hmem : u ∈ Icc a b := ⟨hIoo.1.le, hIoo.2.le⟩
    have heq :  ⟨φ u, hu⟩  = q ⟨u, hmem⟩ :=
      (hunique ⟨u, hmem⟩).unique hzero (hq ⟨u, hmem⟩)
    simpa only [ψ, dite_eq_left hmem] using congrArg Subtype.val heq
  refine ⟨b', hlb.2, ψ, ?_, ?_, (fun (t) (ht : t ∈ Icc a b) => by
                                   grind)⟩
  · intro t ht
    by_cases htb : t < b
    · exact hψanalyticInterior t ⟨ht.1, htb⟩
    · exact (hnear ⟨hlb.1.trans_le (le_of_not_gt htb), ht.2⟩).1
  · intro t ht
    by_cases htb : t ≤ b
    · grind
    · exact (hnear ⟨hlb.1.trans (lt_of_not_ge htb), ht.2⟩).2

end

end PottsDiscontinuity.Bethe
