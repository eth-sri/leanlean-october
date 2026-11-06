module
public import Mathlib

public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.TorusLoops.FiniteEnergy

/-!
# The fixed FK graph of the cut diamond rectangle

The open rectangle graph from `RectangleCrossings` is the open subgraph of this
fixed finite graph. Interior indexed diamond edges are in bijection with its
simple-graph edges; excluding both seams makes the coordinatewise maximum of
the endpoints recover the original medial index.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- Medial indices whose indexed edge survives both rectangle cuts. -/
abbrev RectangleEdgeIndex := {v : Fin N × Fin M // v.1.val ≠ 0 ∧ v.2.val ≠ 0}

/-- The fixed simple graph containing all edges that survive the two cuts. -/
def rectangleBaseGraph (hN : Even N) (hM : Even M)  :=
  SimpleGraph.fromEdgeSet {p | ∃ v : RectangleEdgeIndex (N := N) (M := M),
    p = Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true)}

/-- Indexed torus edges deleted by the two rectangle seams. -/
def rectangleSeamIndices : Finset (Fin N × Fin M) :=
  Finset.univ.filter  fun v => v.1.val = 0 ∨ v.2.val = 0 

/-- The ordinary FK parameter pair whose edge parameter is the critical torus
edge probability and whose cluster parameter is `q`. -/
noncomputable def rectangleFKParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  ⟨q.val, q.property,
    ⟨(rcCriticalParameter q).val,
      PottsDiscontinuity.TorusRC.criticalParameter_pos q,
      PottsDiscontinuity.TorusRC.criticalParameter_lt_one q⟩⟩

section

variable (hN : Even N) (hM : Even M)
include hN hM

section

variable (v : Fin N × Fin M)


private theorem rectangleEndpointXFalse 
     :
    (faceEndpoint hN hM true v false).val.1.val =
      if checker v then v.1.val else (prv v.1).val := by
  grind [faceEndpoint, faceEndpointRaw]

private theorem rectangleEndpointXTrue 
     :
    (faceEndpoint hN hM true v true).val.1.val =
      if checker v then (prv v.1).val else v.1.val := by
  grind [faceEndpoint, faceEndpointRaw]

private theorem rectangleEndpointYFalse 
     :
    (faceEndpoint hN hM true v false).val.2.val = v.2.val := by
  grind [faceEndpoint, faceEndpointRaw]

private theorem rectangleEndpointYTrue 
     :
    (faceEndpoint hN hM true v true).val.2.val = (prv v.2).val := by
  grind [faceEndpoint, faceEndpointRaw]

end

private theorem rectangleEndpointMaxX 
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    max (faceEndpoint hN hM true v.val false).val.1.val
        (faceEndpoint hN hM true v.val true).val.1.val = v.val.1.val := by
  
  
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue]
  cases checker v.val <;> simp <;>
    exact Fin.one_le_of_ne_zero (by
                                   grind)

private theorem rectangleEndpointMaxY 
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    max (faceEndpoint hN hM true v.val false).val.2.val
        (faceEndpoint hN hM true v.val true).val.2.val = v.val.2.val := by
  have hp := prv_val_of_pos v.val.2 (Nat.pos_of_ne_zero v.property.2)
  rw [rectangleEndpointYFalse, rectangleEndpointYTrue]
  omega

private theorem rectangleEdgeIndex_endpoints_injective 
    (v w : RectangleEdgeIndex (N := N) (M := M))
    (he : Sym2.mk (faceEndpoint hN hM true v.val false)
        (faceEndpoint hN hM true v.val true) =
      Sym2.mk (faceEndpoint hN hM true w.val false)
        (faceEndpoint hN hM true w.val true)) : v = w := by
  rcases Sym2.eq_iff.mp he with ⟨hff, htt⟩ | ⟨hft, htf⟩
  · have hx : v.val.1.val = w.val.1.val := by
      grind [rectangleEndpointMaxX]
    have hy : v.val.2.val = w.val.2.val := by
      grind [rectangleEndpointMaxY]
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> assumption
  · have hx : v.val.1.val = w.val.1.val := by
      grind [rectangleEndpointMaxX]
    have hy : v.val.2.val = w.val.2.val := by
      grind [rectangleEndpointMaxY]
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> assumption

private theorem rectangleEndpoints_ne 
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    faceEndpoint hN hM true v.val false ≠ faceEndpoint hN hM true v.val true := by
  intro he
  have hx := congrArg (fun x  => x.val.1.val) he
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue] at hx
  
  have hp := prv_val_of_pos v.val.1 (Nat.pos_of_ne_zero v.property.1)
  
  all_goals grind

end

/-- The medial index embeds into the unordered edges of the fixed rectangle graph. -/
def rectangleBaseEdgeEmbedding (hN : Even N) (hM : Even M) :
    RectangleEdgeIndex (N := N) (M := M) ↪ (rectangleBaseGraph hN hM).edgeSet where
  toFun v := ⟨Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true), by
    rw [rectangleBaseGraph]
    refine ⟨⟨v, rfl⟩, ?_⟩
    intro hd
    simp only  at hd
    exact rectangleEndpoints_ne hN hM v hd
  ⟩
  inj' := by
    intro v w hvw
    apply rectangleEdgeIndex_endpoints_injective hN hM
    exact congrArg Subtype.val hvw

/-- Every edge of the rectangle graph is represented by a unique interior
medial index. -/
noncomputable def rectangleBaseEdgeEquiv (hN : Even N) (hM : Even M) :
    RectangleEdgeIndex (N := N) (M := M) ≃ (rectangleBaseGraph hN hM).edgeSet :=
  Equiv.ofBijective (rectangleBaseEdgeEmbedding hN hM) ⟨
    (rectangleBaseEdgeEmbedding hN hM).injective,
    by
      intro e
      have he := e.property
      simp only [rectangleBaseGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
      rcases he.1 with ⟨v, hv⟩
      exact ⟨v, Subtype.ext hv.symm⟩⟩

/-- The rectangle configuration induced by the interior states of a torus
configuration. -/
noncomputable def rectangleConfigurationOfRC (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : FK.Configuration (rectangleBaseGraph hN hM) :=
  (Finset.univ.filter  fun v : RectangleEdgeIndex => A v.val = true ).map
    (rectangleBaseEdgeEmbedding hN hM)

@[simp] theorem mem_rectangleConfigurationOfRC
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleBaseEdgeEmbedding hN hM v ∈ rectangleConfigurationOfRC hN hM A ↔
      A v.val = true := by
  simp_all [rectangleConfigurationOfRC]

/-- Extend a rectangle FK configuration to the full indexed torus by keeping
all seam states closed. -/
noncomputable def rectangleRCConfigOfConfiguration (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM)) : RCConfig N M := by
  classical
  exact fun v => if h : v.1.val ≠ 0 ∧ v.2.val ≠ 0 then
    decide (rectangleBaseEdgeEmbedding hN hM ⟨v, h⟩ ∈ C) else false

section

variable (hN : Even N) (hM : Even M)
include hN hM

section

variable (C : FK.Configuration (rectangleBaseGraph hN hM))


@[simp] theorem rectangleRCConfigOfConfiguration_interior
    
    
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleRCConfigOfConfiguration hN hM C v.val =
      decide (rectangleBaseEdgeEmbedding hN hM v ∈ C) := by
  
  simp [rectangleRCConfigOfConfiguration, v.property]

theorem rectangleRCConfigOfConfiguration_closedOnSeams
    
    
    (v : Fin N × Fin M) (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleRCConfigOfConfiguration hN hM C v = false := by
  grind +locals

theorem rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration
    
     :
    rectangleConfigurationOfRC hN hM
      (rectangleRCConfigOfConfiguration hN hM C) = C := by
  
  ext e
  
  have hev : rectangleBaseEdgeEmbedding hN hM ((rectangleBaseEdgeEquiv hN hM).symm e) = e :=
    (rectangleBaseEdgeEquiv hN hM).apply_symm_apply e
  rw [← hev]
  simp

end

section

variable (A : RCConfig N M)
include A

theorem rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
     
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleRCConfigOfConfiguration hN hM (rectangleConfigurationOfRC hN hM A) = A := by
  aesop  (add norm (by omega))
     (add simp [RectangleEdgeIndex, rectangleRCConfigOfConfiguration, rectangleConfigurationOfRC])
     (add
      unsafe
        apply [_root_.funext, _root_.congrArg, _root_.of_eq_true, _root_.Eq.trans, _root_.congrFun',
          _root_.Decidable.decide.congr_simp, _root_.And.intro, _root_.Finset.filter_congr, _root_.Iff.of_eq,
          _root_.Eq.refl, _root_.Finset.mem_map'._simp_1, _root_.Finset.mem_filter._simp_1, _root_.congr,
          _root_.Finset.mem_univ._simp_1, _root_.Bool.false_eq_true, _root_.eq_self])

theorem rectangleOpenEdges_eq 
     :
    FK.openEdges (rectangleBaseGraph hN hM) (rectangleConfigurationOfRC hN hM A) =
      {p | ∃ v : RectangleEdgeIndex (N := N) (M := M), A v.val = true ∧
        p = Sym2.mk (faceEndpoint hN hM true v.val false)
          (faceEndpoint hN hM true v.val true)} := by
  
  ext p
  constructor
  · rintro ⟨e, he, rfl⟩
    rcases Finset.mem_map.mp he with ⟨v, hv, hev⟩
    exact ⟨v, (Finset.mem_filter.mp hv).2, (congrArg Subtype.val hev).symm⟩
  · rintro ⟨v, hv, hp⟩
    refine ⟨rectangleBaseEdgeEmbedding hN hM v,
      (mem_rectangleConfigurationOfRC hN hM A v).2 hv, ?_⟩
    aesop

section

variable (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false)
include hclosed

/-- Closing the two indexed seams makes the torus primal open graph exactly the
FK open graph of the cut rectangle. -/
theorem rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams
     
     :
    FK.openGraph (rectangleBaseGraph hN hM) (rectangleConfigurationOfRC hN hM A) =
      diamondOpenGraph hN hM true A := by
  ext u w
  rw [FK.openGraph_adj, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj,
    rectangleOpenEdges_eq]
  constructor
  · rintro ⟨v, hv, hp⟩
    refine ⟨⟨v.val, hv, hp⟩, ?_⟩
    intro huw
    
    exact rectangleEndpoints_ne hN hM v (Sym2.mk_isDiag_iff.mp (by
                                                                  aesop))
  · rintro ⟨⟨v, hv, hp⟩, _⟩
    
    
    exact ⟨⟨v,  by
                  grind ,  by
                      grind ⟩, hv, hp⟩

theorem rectangleConfiguration_card_eq_openCount
     
     :
    (rectangleConfigurationOfRC hN hM A).card = openCount A := by
  
  let I : Finset (RectangleEdgeIndex (N := N) (M := M)) :=
    Finset.univ.filter  fun v => A v.val = true 
  let O  := Finset.univ.filter  fun v => A v = true 
  have hO : O = I.image Subtype.val := by
    ext v
    simp only [O, I, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · aesop
    · simp_all
  
  calc
    (rectangleConfigurationOfRC hN hM A).card = I.card :=  by
                                                             rw [rectangleConfigurationOfRC, Finset.card_map] 
    _ = (I.image Subtype.val).card :=
      (Finset.card_image_of_injective I Subtype.val_injective).symm
    _ = O.card := by rw [← hO]
    _ = openCount A := rfl

theorem rectangleFreeComponentCount_eq_clusterCount
     
     :
    FK.componentCount (rectangleBaseGraph hN hM) (FK.BoundaryCondition.free ∅)
      (rectangleConfigurationOfRC hN hM A) = clusterCount hN hM true A := by
  rw [FK.componentCount, FK.componentSetoid_free,
    rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams hN hM A hclosed]
  rfl

end

end

theorem rectangleBaseEdgeCount_add_seamCount  :
    Nat.card (rectangleBaseGraph hN hM).edgeSet +
      (rectangleSeamIndices (N := N) (M := M)).card = N * M := by
  
  let I : Finset (Fin N × Fin M) :=
    Finset.univ.filter  fun v => v.1.val ≠ 0 ∧ v.2.val ≠ 0 
  have hnot : Finset.univ.filter
      (fun v : Fin N × Fin M => ¬ (v.1.val ≠ 0 ∧ v.2.val ≠ 0)) =
      rectangleSeamIndices := by
    grind +locals
  have hsplit := Finset.card_filter_add_card_filter_not
    (s :=  Finset.univ )
    (p := fun v : Fin N × Fin M => v.1.val ≠ 0 ∧ v.2.val ≠ 0)
  rw [hnot] at hsplit
  
  have hedge : Nat.card (rectangleBaseGraph hN hM).edgeSet = I.card := Trans.trans (Trans.trans (Eq.symm (Nat.card_congr (rectangleBaseEdgeEquiv hN hM))) Nat.card_eq_fintype_card) (by
                                                                                                                                                                                       simp [I, Fintype.card_subtype])
  rw [hedge]
  simpa [I, Fintype.card_prod, Fintype.card_fin] using hsplit

theorem rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount
     (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    closedCount A = (rectangleSeamIndices (N := N) (M := M)).card +
      (Nat.card (rectangleBaseGraph hN hM).edgeSet -
        (rectangleConfigurationOfRC hN hM A).card) := by
  have htotal := openCount_add_closedCount A
  have hopen := rectangleConfiguration_card_eq_openCount hN hM A hclosed
  have hsplit := rectangleBaseEdgeCount_add_seamCount hN hM
  let : Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _
  have hle : (rectangleConfigurationOfRC hN hM A).card ≤
      Nat.card (rectangleBaseGraph hN hM).edgeSet := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

theorem torusRCWeight_eq_seamFactor_mul_rectangleFKWeight
     (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    torusRCWeight hN hM q A =
      (1 - (rcCriticalParameter q).val) ^
          (rectangleSeamIndices (N := N) (M := M)).card *
        FK.weight (rectangleBaseGraph hN hM) (rectangleFKParameters q)
          (FK.BoundaryCondition.free ∅) (rectangleConfigurationOfRC hN hM A) := by
  grind [torusRCWeight, FK.weight, rectangleFKParameters, FK.edgeParameter, rectangleConfiguration_card_eq_openCount,
    rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount, rectangleFreeComponentCount_eq_clusterCount]

end

end PottsDiscontinuity.TorusLoops
