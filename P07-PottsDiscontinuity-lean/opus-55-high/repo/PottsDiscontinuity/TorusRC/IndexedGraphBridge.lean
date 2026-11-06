module

public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.SixVertex.InfinityEndpointOrder
public import PottsDiscontinuity.TorusLoops.FiniteEnergy
public import PottsDiscontinuity.TorusRC.IndexedFK

/-! # The large-period diamond torus is a simple graph -/

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusRC

open Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

section
variable {n : ℕ}
theorem prv_ne_self_of_two_le (hn : 2 ≤ n) (i : Fin n) :
    prv i ≠ i := by
  by_cases hi : i.val = 0
  · have hp := PottsDiscontinuity.SixVertex.prv_val_zero i hi
    omega
  · have hp := PottsDiscontinuity.SixVertex.prv_val_of_pos i
      (Nat.pos_of_ne_zero hi)
    omega

theorem prv_prv_ne_self_of_three_le (hn : 3 ≤ n) (i : Fin n) :
    prv (prv i) ≠ i := by
  by_cases hi0 : i.val = 0
  · have hprev := PottsDiscontinuity.SixVertex.prv_val_zero i hi0
    have hprevprev := PottsDiscontinuity.SixVertex.prv_val_of_pos
      (prv i) (by omega)
    omega
  · have hprev := PottsDiscontinuity.SixVertex.prv_val_of_pos i
      (Nat.pos_of_ne_zero hi0)
    by_cases hi1 : i.val = 1
    · have hprevprev := PottsDiscontinuity.SixVertex.prv_val_zero
        (prv i) (by omega)
      omega
    · have hprevprev := PottsDiscontinuity.SixVertex.prv_val_of_pos
        (prv i) (by omega)
      omega

end

section
variable (hN : Even N) (hM : Even M) (v : Fin N × Fin M)
theorem torusEndpointX0  :
    (faceEndpoint hN hM true v false).val.1 =
      if checker v then v.1 else prv v.1 := by
  grind [checker, faceEndpoint, faceEndpointRaw]

theorem torusEndpointX1  :
    (faceEndpoint hN hM true v true).val.1 =
      if checker v then prv v.1 else v.1 := by
  grind [checker, faceEndpoint, faceEndpointRaw]

theorem torusEndpointY0  :
    (faceEndpoint hN hM true v false).val.2 = v.2 := by
  grind [checker, faceEndpoint, faceEndpointRaw]

theorem torusEndpointY1  :
    (faceEndpoint hN hM true v true).val.2 = prv v.2 := by
  grind [checker, faceEndpoint, faceEndpointRaw]
end

section
variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N)
include hN4
theorem torusEndpoints_ne (v : Fin N × Fin M) :
    faceEndpoint hN hM true v false ≠ faceEndpoint hN hM true v true := by
  grind [torusEndpointX0, torusEndpointX1, checker, prv_ne_self_of_two_le]

theorem torusEndpointPair_injective (hM4 : 4 ≤ M) (v w : Fin N × Fin M)
    (he : Sym2.mk (faceEndpoint hN hM true v false)
          (faceEndpoint hN hM true v true) =
        Sym2.mk (faceEndpoint hN hM true w false)
          (faceEndpoint hN hM true w true)) : v = w := by
  rcases Sym2.eq_iff.mp he with ⟨h00, h11⟩ | ⟨h01, h10⟩
  · have h00x := congrArg (fun z : FaceVertex N M true => z.val.1) h00
    have h11x := congrArg (fun z : FaceVertex N M true => z.val.1) h11
    have h00y := congrArg (fun z : FaceVertex N M true => z.val.2) h00
    have h11y := congrArg (fun z : FaceVertex N M true => z.val.2) h11
    simp only [torusEndpointX0, torusEndpointX1, torusEndpointY0,
      torusEndpointY1] at h00x h11x h00y h11y
    cases hv : checker v <;> cases hw : checker w <;>
      simp only [hv, hw, Bool.false_eq_true, ite_true, ite_false] at h00x h11x h00y h11y
    · grind
    · grind [prv_prv_ne_self_of_three_le]
    · grind [prv_prv_ne_self_of_three_le]
    grind
  · have h01x := congrArg (fun z : FaceVertex N M true => z.val.1) h01
    have h10x := congrArg (fun z : FaceVertex N M true => z.val.1) h10
    have h01y := congrArg (fun z : FaceVertex N M true => z.val.2) h01
    have h10y := congrArg (fun z : FaceVertex N M true => z.val.2) h10
    simp only [torusEndpointX0, torusEndpointX1, torusEndpointY0,
      torusEndpointY1] at h01x h10x h01y h10y
    cases hv : checker v <;> cases hw : checker w <;>
      simp only [hv, hw, Bool.false_eq_true, ite_true, ite_false] at h01x h10x h01y h10y
    · grind [prv_prv_ne_self_of_three_le]
    · grind [prv_prv_ne_self_of_three_le]
    · grind [prv_prv_ne_self_of_three_le]
    · grind [prv_prv_ne_self_of_three_le]

/-- The indexed medial site embeds as a simple edge of the primal diamond graph. -/
def torusIndexedEdgeEmbedding (hM4 : 4 ≤ M) :
    (Fin N × Fin M) ↪ (fullDiamondGraph hN hM).edgeSet where
  toFun v := ⟨Sym2.mk (faceEndpoint hN hM true v false)
      (faceEndpoint hN hM true v true), by
    rw [fullDiamondGraph, diamondOpenGraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨v, rfl, rfl⟩, ?_⟩
    simp_all [torusEndpoints_ne]
  ⟩
  inj' := by
    intro v w hvw
    exact torusEndpointPair_injective hN hM hN4 hM4 v w
      (congrArg Subtype.val hvw)

/-- On periods at least four, every simple primal diamond edge has a unique
indexed medial site. -/
def torusIndexedEdgeEquiv (hM4 : 4 ≤ M) :
    (Fin N × Fin M) ≃ (fullDiamondGraph hN hM).edgeSet :=
  Equiv.ofBijective (torusIndexedEdgeEmbedding hN hM hN4 hM4) ⟨
    (torusIndexedEdgeEmbedding hN hM hN4 hM4).injective,
    by
      intro e
      have he := e.property
      simp only [fullDiamondGraph, diamondOpenGraph,
        SimpleGraph.edgeSet_fromEdgeSet] at he
      rcases he.1 with ⟨v, hv, hpair⟩
      exact ⟨v, Subtype.ext hpair.symm⟩⟩
end

def indexOpenSet (A : RCConfig N M) : Finset (Fin N × Fin M) :=
  Finset.univ.filter fun v => A v = true

def indexConfigurationEquiv (N M : ℕ) :
    RCConfig N M ≃ Finset (Fin N × Fin M) where
  toFun := indexOpenSet
  invFun := fun s v => decide (v ∈ s)
  left_inv := by
    grind [indexOpenSet]
  right_inv := by
    grind [indexOpenSet]

def finsetEquivOfEquiv {α β : Type*} (e : α ≃ β) : Finset α ≃ Finset β where
  toFun := fun s => s.map e.toEmbedding
  invFun := fun s => s.map e.symm.toEmbedding
  left_inv := by
    intro s
    aesop
  right_inv := by
    intro s
    aesop

section
variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
/-- The full indexed torus configuration is exactly a finite-graph edge set
once both periods are at least four. -/
def torusRCConfigurationEquiv  :
    RCConfig N M ≃ FK.Configuration (fullDiamondGraph hN hM) :=
  (indexConfigurationEquiv N M).trans
    (finsetEquivOfEquiv (torusIndexedEdgeEquiv hN hM hN4 hM4))

@[simp] theorem mem_torusRCConfigurationEquiv (A : RCConfig N M)
    (v : Fin N × Fin M) :
    torusIndexedEdgeEmbedding hN hM hN4 hM4 v ∈
        torusRCConfigurationEquiv hN hM hN4 hM4 A ↔ A v = true := by
  change torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈
      (indexOpenSet A).map (torusIndexedEdgeEquiv hN hM hN4 hM4).toEmbedding ↔
        A v = true
  simp [indexOpenSet]

theorem simpleConfiguration_eq_torusRCConfigurationEquiv
    (A : RCConfig N M) :
    simpleConfiguration hN hM A = torusRCConfigurationEquiv hN hM hN4 hM4 A := by
  ext e
  simp only [simpleConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
  let v := (torusIndexedEdgeEquiv hN hM hN4 hM4).symm e
  have hev : torusIndexedEdgeEmbedding hN hM hN4 hM4 v = e :=
    (torusIndexedEdgeEquiv hN hM hN4 hM4).apply_symm_apply e
  rw [← hev]
  constructor
  · rintro ⟨w, hw, hpair⟩
    have hwe : torusIndexedEdgeEmbedding hN hM hN4 hM4 w =
        torusIndexedEdgeEmbedding hN hM hN4 hM4 v := by
      aesop
    aesop
  · intro he
    have hv := (mem_torusRCConfigurationEquiv hN hM hN4 hM4 A v).1 he
    tauto
end

def torusRCFKParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  ⟨q.val, q.property,
    ⟨(rcCriticalParameter q).val, criticalParameter_pos q, criticalParameter_lt_one q⟩⟩

noncomputable local instance torusIndexedGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

section
variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
include hN4 hM4
theorem torusIndexedEdge_card  :
    Fintype.card (fullDiamondGraph hN hM).edgeSet = N * M := by
  rw [← Fintype.card_congr (torusIndexedEdgeEquiv hN hM hN4 hM4)]
  simp

theorem torusRCConfigurationEquiv_card (A : RCConfig N M) :
    (torusRCConfigurationEquiv hN hM hN4 hM4 A).card = openCount A := by
  simp [torusRCConfigurationEquiv, indexConfigurationEquiv, indexOpenSet,
    finsetEquivOfEquiv, openCount]

/-- For large even periods, the indexed torus weight `torusRCWeight`
(`Torus/DiamondGraph.lean`) is exactly the free FK
weight on the simple diamond torus graph. -/
theorem torusRCWeight_eq_fk_weight (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M) :
    torusRCWeight hN hM q A =
      FK.weight (fullDiamondGraph hN hM) (torusRCFKParameters q)
        (FK.BoundaryCondition.free ∅)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A) := by
  rw [Torus.torusRCWeight, FK.weight]
  have hcomp : clusterCount hN hM true A =
      FK.componentCount (fullDiamondGraph hN hM) (FK.BoundaryCondition.free ∅)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A) := by
    rw [clusterCount_eq_componentCount,
      simpleConfiguration_eq_torusRCConfigurationEquiv hN hM hN4 hM4 A]
  have hopen := torusRCConfigurationEquiv_card hN hM hN4 hM4 A
  have hclosed :
      Nat.card (fullDiamondGraph hN hM).edgeSet -
          (torusRCConfigurationEquiv hN hM hN4 hM4 A).card = closedCount A := by
    rw [Nat.card_eq_fintype_card, (torusIndexedEdge_card hN hM hN4 hM4), hopen]
    have hsplit := openCount_add_closedCount A
    omega
  grind [Nat.card, fullDiamondGraph, openCount, closedCount, torusRCFKParameters, FK.edgeParameter]
end

end PottsDiscontinuity.TorusRC
