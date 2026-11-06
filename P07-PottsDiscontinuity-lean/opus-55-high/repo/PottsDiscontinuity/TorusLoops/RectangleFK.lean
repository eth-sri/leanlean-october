module

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

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- Medial indices whose indexed edge survives both rectangle cuts. -/
abbrev RectangleEdgeIndex := {v : Fin N × Fin M // v.1.val ≠ 0 ∧ v.2.val ≠ 0}

/-- The fixed simple graph containing all edges that survive the two cuts. -/
def rectangleBaseGraph (hN : Even N) (hM : Even M) :
    SimpleGraph (FaceVertex N M true) :=
  SimpleGraph.fromEdgeSet {p | ∃ v : RectangleEdgeIndex (N := N) (M := M),
    p = Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true)}

/-- Indexed torus edges deleted by the two rectangle seams. -/
def rectangleSeamIndices : Finset (Fin N × Fin M) :=
  Finset.univ.filter (fun v => v.1.val = 0 ∨ v.2.val = 0)

/-- The ordinary FK parameter pair whose edge parameter is the critical torus
edge probability and whose cluster parameter is `q`. -/
def rectangleFKParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  ⟨q.val, q.property,
    ⟨(rcCriticalParameter q).val,
      PottsDiscontinuity.TorusRC.criticalParameter_pos q,
      PottsDiscontinuity.TorusRC.criticalParameter_lt_one q⟩⟩

section
variable (hN : Even N) (hM : Even M) (v : Fin N × Fin M)
theorem rectangleEndpointXFalse  :
    (faceEndpoint hN hM true v false).val.1.val =
      if checker v then v.1.val else (prv v.1).val := by
  grind [checker, faceEndpoint, faceEndpointRaw]

theorem rectangleEndpointXTrue  :
    (faceEndpoint hN hM true v true).val.1.val =
      if checker v then (prv v.1).val else v.1.val := by
  grind [checker, faceEndpoint, faceEndpointRaw]

theorem rectangleEndpointYFalse  :
    (faceEndpoint hN hM true v false).val.2.val = v.2.val := by
  grind [checker, faceEndpoint, faceEndpointRaw]

theorem rectangleEndpointYTrue  :
    (faceEndpoint hN hM true v true).val.2.val = (prv v.2).val := by
  grind [checker, faceEndpoint, faceEndpointRaw]
end

section
variable (hN : Even N) (hM : Even M) (v : RectangleEdgeIndex (N := N) (M := M))
include v
theorem rectangleEndpointMaxX  :
    max (faceEndpoint hN hM true v.val false).val.1.val
        (faceEndpoint hN hM true v.val true).val.1.val = v.val.1.val := by
  let  := v.val.1.neZero
  have hfin : v.val.1 ≠ 0 := by
    grind
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue]
  cases checker v.val <;> simp <;>
    exact Fin.one_le_of_ne_zero hfin

theorem rectangleEndpointMaxY  :
    max (faceEndpoint hN hM true v.val false).val.2.val
        (faceEndpoint hN hM true v.val true).val.2.val = v.val.2.val := by
  have hp := prv_val_of_pos v.val.2 (Nat.pos_of_ne_zero v.property.2)
  simp_all [rectangleEndpointYFalse, rectangleEndpointYTrue]
end

section
variable (hN : Even N) (hM : Even M)
include hN hM
theorem rectangleEdgeIndex_endpoints_injective (v w : RectangleEdgeIndex (N := N) (M := M))
    (he : Sym2.mk (faceEndpoint hN hM true v.val false)
        (faceEndpoint hN hM true v.val true) =
      Sym2.mk (faceEndpoint hN hM true w.val false)
        (faceEndpoint hN hM true w.val true)) : v = w := by
  rcases Sym2.eq_iff.mp he with ⟨hff, htt⟩ | ⟨hft, htf⟩
  · have hx : v.val.1.val = w.val.1.val := by
      grind [max, faceEndpoint, rectangleEndpointMaxX]
    grind [max, faceEndpoint, rectangleEndpointMaxY]
  · have hx : v.val.1.val = w.val.1.val := by
      grind [max, faceEndpoint, rectangleEndpointMaxX]
    have hy : v.val.2.val = w.val.2.val := by
      grind [max, faceEndpoint, rectangleEndpointMaxY]
    grind

theorem rectangleEndpoints_ne (v : RectangleEdgeIndex (N := N) (M := M)) :
    faceEndpoint hN hM true v.val false ≠ faceEndpoint hN hM true v.val true := by
  intro he
  have hx := congrArg (fun x : FaceVertex N M true => x.val.1.val) he
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue] at hx
  have hp := prv_val_of_pos v.val.1 (Nat.pos_of_ne_zero v.property.1)
  grind

/-- The medial index embeds into the unordered edges of the fixed rectangle graph. -/
def rectangleBaseEdgeEmbedding  :
    RectangleEdgeIndex (N := N) (M := M) ↪ (rectangleBaseGraph hN hM).edgeSet where
  toFun v := ⟨Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true), by
    rw [rectangleBaseGraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨v, rfl⟩, ?_⟩
    simp [rectangleEndpoints_ne]
  ⟩
  inj' := by
    intro v w hvw
    apply rectangleEdgeIndex_endpoints_injective hN hM
    simp_all

/-- Every edge of the rectangle graph is represented by a unique interior
medial index. -/
def rectangleBaseEdgeEquiv  :
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
def rectangleConfigurationOfRC (A : RCConfig N M) : FK.Configuration (rectangleBaseGraph hN hM) :=
  (Finset.univ.filter (fun v : RectangleEdgeIndex => A v.val = true)).map
    (rectangleBaseEdgeEmbedding hN hM)

@[simp] theorem mem_rectangleConfigurationOfRC
    (A : RCConfig N M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleBaseEdgeEmbedding hN hM v ∈ rectangleConfigurationOfRC hN hM A ↔
      A v.val = true := by
  rw [rectangleConfigurationOfRC, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, hew⟩
    have hvw := (rectangleBaseEdgeEmbedding hN hM).injective hew
    subst w
    exact (Finset.mem_filter.mp hw).2
  · intro hv
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
end

section
variable (hN : Even N) (hM : Even M) (C : FK.Configuration (rectangleBaseGraph hN hM))
include hN hM C
/-- Extend a rectangle FK configuration to the full indexed torus by keeping
all seam states closed. -/
def rectangleRCConfigOfConfiguration  : RCConfig N M := by
  classical
  exact fun v => if h : v.1.val ≠ 0 ∧ v.2.val ≠ 0 then
    decide (rectangleBaseEdgeEmbedding hN hM ⟨v, h⟩ ∈ C) else false

@[simp] theorem rectangleRCConfigOfConfiguration_interior
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleRCConfigOfConfiguration hN hM C v.val =
      decide (rectangleBaseEdgeEmbedding hN hM v ∈ C) := by
  simp [rectangleRCConfigOfConfiguration, v.property]

theorem rectangleRCConfigOfConfiguration_closedOnSeams
    (v : Fin N × Fin M) (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleRCConfigOfConfiguration hN hM C v = false := by
  grind [rectangleRCConfigOfConfiguration]

theorem rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration
     :
    rectangleConfigurationOfRC hN hM
      (rectangleRCConfigOfConfiguration hN hM C) = C := by
  ext e
  let v := (rectangleBaseEdgeEquiv hN hM).symm e
  have hev : rectangleBaseEdgeEmbedding hN hM v = e :=
    (rectangleBaseEdgeEquiv hN hM).apply_symm_apply e
  rw [← hev, mem_rectangleConfigurationOfRC,
    rectangleRCConfigOfConfiguration_interior]
  simp
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
theorem rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleRCConfigOfConfiguration hN hM (rectangleConfigurationOfRC hN hM A) = A := by
  funext v
  by_cases hs : v.1.val = 0 ∨ v.2.val = 0
  · grind [rectangleRCConfigOfConfiguration_closedOnSeams]
  · have hx : v.1.val ≠ 0 := by
      omega
    have hy : v.2.val ≠ 0 := by
      omega
    let w : RectangleEdgeIndex := ⟨v, hx, hy⟩
    change rectangleRCConfigOfConfiguration hN hM
      (rectangleConfigurationOfRC hN hM A) w.val = A w.val
    simp

theorem rectangleOpenEdges_eq  :
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
    tauto
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (hclosed : ∀ v : Fin N × Fin M, v.1.val = 0 ∨ v.2.val = 0 → A v = false)
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
    have hdiag : (Sym2.mk
        (faceEndpoint hN hM true v.val false)
        (faceEndpoint hN hM true v.val true)).IsDiag := by
      have hd := Sym2.mk_isDiag_iff.mpr huw
      grind
    exact rectangleEndpoints_ne hN hM v (Sym2.mk_isDiag_iff.mp hdiag)
  · rintro ⟨⟨v, hv, hp⟩, _⟩
    have hx : v.1.val ≠ 0 := by
      grind
    have hy : v.2.val ≠ 0 := by
      grind
    exact ⟨⟨v, hx, hy⟩, hv, hp⟩

theorem rectangleConfiguration_card_eq_openCount
     :
    (rectangleConfigurationOfRC hN hM A).card = openCount A := by
  let I : Finset (RectangleEdgeIndex) :=
    Finset.univ.filter (fun v => A v.val = true)
  let O := Finset.univ.filter (fun v => A v = true)
  have hO : O = I.image Subtype.val := by
    ext v
    simp only [O, I, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hv
      have hinterior : v.1.val ≠ 0 ∧ v.2.val ≠ 0 := by
        grind
      exact ⟨⟨v, hinterior⟩, hv, rfl⟩
    grind
  have hcardI : (rectangleConfigurationOfRC hN hM A).card = I.card := by
    grind [rectangleConfigurationOfRC]
  calc
    (rectangleConfigurationOfRC hN hM A).card = I.card := hcardI
    _ = (I.image Subtype.val).card :=
      (Finset.card_image_of_injective I Subtype.val_injective).symm
    _ = O.card := by grind
    _ = openCount A := rfl

theorem rectangleFreeComponentCount_eq_clusterCount
     :
    FK.componentCount (rectangleBaseGraph hN hM) (FK.BoundaryCondition.free ∅)
      (rectangleConfigurationOfRC hN hM A) = clusterCount hN hM true A := by
  rw [FK.componentCount, FK.componentSetoid_free,
    rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams hN hM A hclosed]
  rfl
end

section
variable (hN : Even N) (hM : Even M)
include hN hM
theorem rectangleBaseEdgeCount_add_seamCount  :
    Nat.card (rectangleBaseGraph hN hM).edgeSet +
      (rectangleSeamIndices (N := N) (M := M)).card = N * M := by
  let I : Finset (Fin N × Fin M) :=
    Finset.univ.filter (fun v => v.1.val ≠ 0 ∧ v.2.val ≠ 0)
  have hnot : Finset.univ.filter
      (fun v : Fin N × Fin M => ¬ (v.1.val ≠ 0 ∧ v.2.val ≠ 0)) =
      rectangleSeamIndices := by
    grind [rectangleSeamIndices]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N × Fin M)))
    (p := fun v : Fin N × Fin M => v.1.val ≠ 0 ∧ v.2.val ≠ 0)
  rw [hnot] at hsplit
  have hindex : Fintype.card (RectangleEdgeIndex (N := N) (M := M)) = I.card := by
    simp [RectangleEdgeIndex, I, Fintype.card_subtype]
  have hedge : Nat.card (rectangleBaseGraph hN hM).edgeSet = I.card := by
    calc
      Nat.card (rectangleBaseGraph hN hM).edgeSet =
          Nat.card (RectangleEdgeIndex) :=
        (Nat.card_congr (rectangleBaseEdgeEquiv hN hM)).symm
      _ = Fintype.card (RectangleEdgeIndex) :=
        Nat.card_eq_fintype_card
      _ = I.card := hindex
  rw [hedge]
  simpa using hsplit

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
  grind [torusRCWeight, FK.weight, rectangleConfiguration_card_eq_openCount, rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount, rectangleFreeComponentCount_eq_clusterCount, rectangleFKParameters, FK.edgeParameter]
end

end PottsDiscontinuity.TorusLoops
