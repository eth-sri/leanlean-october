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

@[expose] public section

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
noncomputable def rectangleFKParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  ⟨q.val, q.property,
    ⟨(rcCriticalParameter q).val,
      PottsDiscontinuity.TorusRC.criticalParameter_pos q,
      PottsDiscontinuity.TorusRC.criticalParameter_lt_one q⟩⟩

private theorem rectangleEndpointXFalse (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.1.val =
      if checker v then v.1.val else (prv v.1).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointXTrue (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.1.val =
      if checker v then (prv v.1).val else v.1.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYFalse (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.2.val = v.2.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYTrue (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.2.val = (prv v.2).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointMaxX (hN : Even N) (hM : Even M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    max (faceEndpoint hN hM true v.val false).val.1.val
        (faceEndpoint hN hM true v.val true).val.1.val = v.val.1.val := by
  let : NeZero N := v.val.1.neZero
  have hfin : v.val.1 ≠ 0 := by
    intro hz
    apply v.property.1
    simpa using congrArg Fin.val hz
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue]
  cases checker v.val <;> simp <;>
    exact Fin.one_le_of_ne_zero hfin

private theorem rectangleEndpointMaxY (hN : Even N) (hM : Even M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    max (faceEndpoint hN hM true v.val false).val.2.val
        (faceEndpoint hN hM true v.val true).val.2.val = v.val.2.val := by
  have hp := prv_val_of_pos v.val.2 (Nat.pos_of_ne_zero v.property.2)
  rw [rectangleEndpointYFalse, rectangleEndpointYTrue]
  omega

theorem rectangleEdgeIndex_endpoints_injective (hN : Even N) (hM : Even M)
    (v w : RectangleEdgeIndex (N := N) (M := M))
    (he : Sym2.mk (faceEndpoint hN hM true v.val false)
        (faceEndpoint hN hM true v.val true) =
      Sym2.mk (faceEndpoint hN hM true w.val false)
        (faceEndpoint hN hM true w.val true)) : v = w := by
  apply Subtype.ext; apply Prod.ext <;> apply Fin.ext
  · rw [← rectangleEndpointMaxX hN hM v, ← rectangleEndpointMaxX hN hM w]
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [rw [h1, h2]; rw [h1, h2, Nat.max_comm]]
  · rw [← rectangleEndpointMaxY hN hM v, ← rectangleEndpointMaxY hN hM w]
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [rw [h1, h2]; rw [h1, h2, Nat.max_comm]]

theorem rectangleEndpoints_ne (hN : Even N) (hM : Even M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    faceEndpoint hN hM true v.val false ≠ faceEndpoint hN hM true v.val true := by
  intro he
  have hx := congrArg (fun x : FaceVertex N M true => x.val.1.val) he
  have hp := prv_val_of_pos v.val.1 (Nat.pos_of_ne_zero v.property.1)
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue] at hx
  cases hc : checker v.val <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at hx <;>
    rw [hp] at hx <;> omega

/-- The medial index embeds into the unordered edges of the fixed rectangle graph. -/
def rectangleBaseEdgeEmbedding (hN : Even N) (hM : Even M) :
    RectangleEdgeIndex (N := N) (M := M) ↪ (rectangleBaseGraph hN hM).edgeSet where
  toFun v := ⟨Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true), by
    rw [rectangleBaseGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨v, rfl⟩, fun hd => rectangleEndpoints_ne hN hM v (Sym2.mk_isDiag_iff.mp hd)⟩⟩
  inj' _ _ hvw := rectangleEdgeIndex_endpoints_injective hN hM _ _ (congrArg Subtype.val hvw)

/-- Every edge of the rectangle graph is represented by a unique interior
medial index. -/
noncomputable def rectangleBaseEdgeEquiv (hN : Even N) (hM : Even M) :
    RectangleEdgeIndex (N := N) (M := M) ≃ (rectangleBaseGraph hN hM).edgeSet :=
  Equiv.ofBijective (rectangleBaseEdgeEmbedding hN hM) ⟨
    (rectangleBaseEdgeEmbedding hN hM).injective,
    fun e => by
      have he := e.property
      simp only [rectangleBaseGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
      rcases he.1 with ⟨v, hv⟩
      exact ⟨v, Subtype.ext hv.symm⟩⟩

/-- The rectangle configuration induced by the interior states of a torus
configuration. -/
noncomputable def rectangleConfigurationOfRC (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : FK.Configuration (rectangleBaseGraph hN hM) :=
  (Finset.univ.filter (fun v : RectangleEdgeIndex => A v.val = true)).map
    (rectangleBaseEdgeEmbedding hN hM)

@[simp] theorem mem_rectangleConfigurationOfRC
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleBaseEdgeEmbedding hN hM v ∈ rectangleConfigurationOfRC hN hM A ↔
      A v.val = true := by
  classical
  simp [rectangleConfigurationOfRC]

/-- Extend a rectangle FK configuration to the full indexed torus by keeping
all seam states closed. -/
noncomputable def rectangleRCConfigOfConfiguration (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM)) : RCConfig N M := by
  classical
  exact fun v => if h : v.1.val ≠ 0 ∧ v.2.val ≠ 0 then
    decide (rectangleBaseEdgeEmbedding hN hM ⟨v, h⟩ ∈ C) else false

@[simp] theorem rectangleRCConfigOfConfiguration_interior
    (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM))
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleRCConfigOfConfiguration hN hM C v.val =
      decide (rectangleBaseEdgeEmbedding hN hM v ∈ C) := by
  classical
  simp [rectangleRCConfigOfConfiguration, v.property]

theorem rectangleRCConfigOfConfiguration_closedOnSeams
    (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM))
    (v : Fin N × Fin M) (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleRCConfigOfConfiguration hN hM C v = false := by
  classical
  rcases hseam with hx | hy <;>
    [simp [rectangleRCConfigOfConfiguration, hx]; simp [rectangleRCConfigOfConfiguration, hy]]

theorem rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration
    (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM)) :
    rectangleConfigurationOfRC hN hM
      (rectangleRCConfigOfConfiguration hN hM C) = C := by
  classical
  ext e
  let v := (rectangleBaseEdgeEquiv hN hM).symm e
  have hev : rectangleBaseEdgeEmbedding hN hM v = e :=
    (rectangleBaseEdgeEquiv hN hM).apply_symm_apply e
  simp [← hev]

theorem rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleRCConfigOfConfiguration hN hM (rectangleConfigurationOfRC hN hM A) = A := by
  funext v
  by_cases hs : v.1.val = 0 ∨ v.2.val = 0
  · rw [rectangleRCConfigOfConfiguration_closedOnSeams hN hM _ v hs, hclosed v hs]
  · let w : RectangleEdgeIndex (N := N) (M := M) := ⟨v, not_or.mp hs⟩
    change rectangleRCConfigOfConfiguration hN hM
      (rectangleConfigurationOfRC hN hM A) w.val = A w.val
    rw [rectangleRCConfigOfConfiguration_interior]
    cases hav : A v <;> simp [rectangleConfigurationOfRC, hav, w]

private theorem rectangleOpenEdges_eq (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    FK.openEdges (rectangleBaseGraph hN hM) (rectangleConfigurationOfRC hN hM A) =
      {p | ∃ v : RectangleEdgeIndex (N := N) (M := M), A v.val = true ∧
        p = Sym2.mk (faceEndpoint hN hM true v.val false)
          (faceEndpoint hN hM true v.val true)} := by
  classical
  ext p
  constructor
  · rintro ⟨e, he, rfl⟩
    rcases Finset.mem_map.mp he with ⟨v, hv, hev⟩
    exact ⟨v, (Finset.mem_filter.mp hv).2, (congrArg Subtype.val hev).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨rectangleBaseEdgeEmbedding hN hM v,
      (mem_rectangleConfigurationOfRC hN hM A v).2 hv, rfl⟩

/-- Closing the two indexed seams makes the torus primal open graph exactly the
FK open graph of the cut rectangle. -/
theorem rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    FK.openGraph (rectangleBaseGraph hN hM) (rectangleConfigurationOfRC hN hM A) =
      diamondOpenGraph hN hM true A := by
  ext u w
  rw [FK.openGraph_adj, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj, rectangleOpenEdges_eq]
  refine ⟨fun ⟨v, hv, hp⟩ => ⟨⟨v.val, hv, hp⟩, fun huw =>
    rectangleEndpoints_ne hN hM v (Sym2.mk_isDiag_iff.mp (hp ▸ Sym2.mk_isDiag_iff.mpr huw))⟩, ?_⟩
  rintro ⟨⟨v, hv, hp⟩, _⟩
  exact ⟨⟨v, fun hz => by simp [hclosed v (Or.inl hz)] at hv,
    fun hz => by simp [hclosed v (Or.inr hz)] at hv⟩, hv, hp⟩

private theorem rectangleConfiguration_card_eq_openCount
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    (rectangleConfigurationOfRC hN hM A).card = openCount A := by
  classical
  rw [rectangleConfigurationOfRC, Finset.card_map, openCount,
    ← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1; ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨_, hv, h⟩ => h ▸ hv, fun hv =>
    ⟨⟨v, fun hz => by simp [hclosed v (Or.inl hz)] at hv,
      fun hz => by simp [hclosed v (Or.inr hz)] at hv⟩, hv, rfl⟩⟩

private theorem rectangleFreeComponentCount_eq_clusterCount
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    FK.componentCount (rectangleBaseGraph hN hM) (FK.BoundaryCondition.free ∅)
      (rectangleConfigurationOfRC hN hM A) = clusterCount hN hM true A := by
  rw [FK.componentCount, FK.componentSetoid_free,
    rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams hN hM A hclosed]
  rfl

private theorem rectangleBaseEdgeCount_add_seamCount (hN : Even N) (hM : Even M) :
    Nat.card (rectangleBaseGraph hN hM).edgeSet +
      (rectangleSeamIndices (N := N) (M := M)).card = N * M := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N × Fin M)))
    (p := fun v : Fin N × Fin M => v.1.val ≠ 0 ∧ v.2.val ≠ 0)
  rw [show Finset.univ.filter (fun v : Fin N × Fin M => ¬ (v.1.val ≠ 0 ∧ v.2.val ≠ 0)) =
      rectangleSeamIndices by
        ext v; by_cases hx : v.1.val = 0 <;> by_cases hy : v.2.val = 0 <;>
          simp [rectangleSeamIndices, hx, hy],
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_congr (rectangleBaseEdgeEquiv hN hM)] at hsplit
  simpa [Fintype.card_prod, Fintype.card_fin] using hsplit

private theorem rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
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
    rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
  omega

theorem torusRCWeight_eq_seamFactor_mul_rectangleFKWeight
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    torusRCWeight hN hM q A =
      (1 - (rcCriticalParameter q).val) ^
          (rectangleSeamIndices (N := N) (M := M)).card *
        FK.weight (rectangleBaseGraph hN hM) (rectangleFKParameters q)
          (FK.BoundaryCondition.free ∅) (rectangleConfigurationOfRC hN hM A) := by
  rw [torusRCWeight, FK.weight,
    ← rectangleConfiguration_card_eq_openCount hN hM A hclosed,
    rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount hN hM A hclosed,
    ← rectangleFreeComponentCount_eq_clusterCount hN hM A hclosed]
  simp only [rectangleFKParameters, FK.edgeParameter]
  rw [pow_add]
  ring

end PottsDiscontinuity.TorusLoops
