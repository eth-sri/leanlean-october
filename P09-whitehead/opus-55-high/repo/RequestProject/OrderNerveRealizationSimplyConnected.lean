import RequestProject.OrderNerveRealizationVertexCoherence
import RequestProject.TopologyPaths.OpenCoverPaths
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory

/-- Combinatorial connectivity and simple connectivity imply genuine topological
simple connectivity of the poset-nerve realization. No finiteness is required. -/
theorem orderNerveRealization_simplyConnected P [PartialOrder P] [Nonempty P]
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    SimplyConnectedSpace (orderNerveRealization P) := by
  classical
  let a : P := Classical.choice inferInstance
  letI := orderNerveRealization_pathConnectedSpace P hconn
  obtain ⟨k, hk⟩ := orderNerveRealization_exists_vertex_coherence P a hconn hsc
  choose v r hr using (fun x : orderNerveRealization P => orderNerveRealization_exists_radial x)
  let R : ∀ x,
      FundamentalGroupoid.mk (orderNerveRealizationVertex a) ⟶ FundamentalGroupoid.mk x :=
    fun x => k _ ≫ Path.Homotopic.Quotient.mk (r x)
  have hstar (x : orderNerveRealization P) (b : P)
      (hx : x ∈ orderNerveRealizationOpenStar P b) :
      ∃ p : Path (orderNerveRealizationVertex b) x,
        Set.range p ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b)) ∧
        k b ≫ Path.Homotopic.Quotient.mk p = R x := by
    cases' hr x b hx with hcomp hrad
    have he : ∃ e : Path (orderNerveRealizationVertex b) (orderNerveRealizationVertex (v x)),
        Set.range e ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b)) ∧
        k b ≫ Path.Homotopic.Quotient.mk e = k _ := by
      rcases hcomp with h | h
      · refine ⟨(orderNerveRealizationEdgePath h).symm, ?_, ?_⟩
        · rwd [Path.symm_range]
          exact orderNerveRealizationEdgePath_supported h b (Or.inl h) (Or.inl le_rfl)
        · change k b ≫ Groupoid.inv (Path.Homotopic.Quotient.mk
            (orderNerveRealizationEdgePath h)) = k _
          simp_all
      · exact ⟨orderNerveRealizationEdgePath h,
          orderNerveRealizationEdgePath_supported h b (Or.inl le_rfl) (Or.inr h), hk h⟩
    obtain ⟨e, he, hke⟩ := he
    refine ⟨e.trans (r x), ?_, ?_⟩
    · grind
    · change k b ≫ (Path.Homotopic.Quotient.mk e ≫ Path.Homotopic.Quotient.mk (r x)) = _
      rwd [← Category.assoc, hke]
  have hlocal {x y : orderNerveRealization P} (p : Path x y)
      (hp : ∃ b, Set.range p ⊆ orderNerveRealizationOpenStar P b) :
      R x ≫ Path.Homotopic.Quotient.mk p = R y := by
    cases' hp with b hp
    obtain ⟨e, he, hke⟩ := hstar x b (hp p.source_mem_range)
    obtain ⟨f, hf, hkf⟩ := hstar y b (hp p.target_mem_range)
    letI := orderNerveRealization_closedStar_contractible b
    have hC : IsSimplyConnected (orderNerveRealizationSubcomplex P
        (orderNerveVertexStar P b) : Set (orderNerveRealization P)) := by
      change SimplyConnectedSpace _
      infer_instance
    have hh : (e.trans p).Homotopic f := paths_homotopic_of_range_subset hC _ _ (by
      grind [Path.trans_range]) hf
    rwd [← hke, ← hkf, Category.assoc]
    apply congrArg _
    exact Quotient.sound hh
  have hall {x y : orderNerveRealization P} (p : Path x y) :
      R x ≫ Path.Homotopic.Quotient.mk p = R y := by
    refine FiniteChains.OpenCoverPaths.path_induction
      (orderNerveRealizationOpenStar P) (orderNerveRealizationOpenStar_isOpen P)
      (orderNerveRealizationOpenStar_cover P)
      (fun {x y} q => R x ≫ Path.Homotopic.Quotient.mk q = R y) ?_ ?_ ?_ ?_ p
    · intro x
      exact Category.comp_id _
    · intro x y z p q hp hq
      change R x ≫ (Path.Homotopic.Quotient.mk p ≫ Path.Homotopic.Quotient.mk q) = R z
      grind
    · intro x y p q hpq hp
      have he : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := Quotient.sound hpq
      simp_all
    · exact hlocal
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x p => ?_⟩
  have he : (Path.Homotopic.Quotient.mk p) =
      𝟙 (FundamentalGroupoid.mk x) := by
    apply (cancel_epi (R x)).mp
    simp_all
  exact Quotient.exact he
