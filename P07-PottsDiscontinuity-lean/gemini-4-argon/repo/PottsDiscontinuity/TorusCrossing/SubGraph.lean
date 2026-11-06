module

public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.TorusCrossing.Markov
public import PottsDiscontinuity.TorusCrossing.TwoBoard

/-!
# The graph of unexplored edges

For a set `Ex` of medial vertices of a board `Q` (the explored edges), the unexplored edges
`Un = Q.inner \ Ex` form a graph `subG` on the cells they touch; it embeds in `Q.pG`.  We express
the Markov property for the freezing of `Ex` in terms of cell-level events.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (Q : Rect) (Ex : Finset Cell)

/-- The unexplored medial vertices. -/
def unx : Finset Cell := Q.inner \ Ex

/-- Cells touched by an unexplored edge. -/
noncomputable def vrx : Finset Cell :=
  (Q.unx Ex).image (fun m => (primalEnds m).1) ∪ (Q.unx Ex).image (fun m => (primalEnds m).2)

variable {Q Ex}

theorem mem_unx {m : Cell} : m ∈ Q.unx Ex ↔ m ∈ Q.inner ∧ m ∉ Ex := Finset.mem_sdiff

theorem mem_vrx {c : Cell} : c ∈ Q.vrx Ex ↔ Vtx (Q.unx Ex) c := by
  unfold vrx Vtx
  simp only [Finset.mem_union, Finset.mem_image]
  exact ⟨by rintro (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩) <;> [exact ⟨m, hm, Or.inl rfl⟩; exact ⟨m, hm, Or.inr rfl⟩],
    by rintro ⟨m, hm, rfl | rfl⟩ <;> [exact Or.inl ⟨m, hm, rfl⟩; exact Or.inr ⟨m, hm, rfl⟩]⟩

variable (Q Ex)

theorem unx_subset_inner : Q.unx Ex ⊆ Q.inner := Finset.sdiff_subset

theorem subData : EndData primalEnds (Q.vrx Ex) (Q.unx Ex) where
  mem m hm := ⟨mem_vrx.2 ⟨m, hm, Or.inl rfl⟩, mem_vrx.2 ⟨m, hm, Or.inr rfl⟩⟩
  ne := primalEnds_ne
  inj _ _ h := primalEnds_inj h

theorem vrx_subset_pcells : Q.vrx Ex ⊆ Q.pcells := fun _c hc =>
  Vtx_mem_pcells (unx_subset_inner Q Ex) (mem_vrx.1 hc)

noncomputable abbrev subG : SimpleGraph (Q.vrx Ex) := endGraph primalEnds (Q.vrx Ex) (Q.unx Ex)

noncomputable def subEmb : (Q.vrx Ex) ↪ Q.pcells where
  toFun v := ⟨v.1, vrx_subset_pcells Q Ex v.2⟩
  inj' _ _ h := Subtype.ext (by simpa using congrArg Subtype.val h)

theorem subLe : (Q.subG Ex).map (subEmb Q Ex) ≤ Q.pG := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
  rw [endGraph_adj] at hab ⊢
  refine ⟨fun h => hab.1 ((subEmb Q Ex).injective h), ?_⟩
  rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ <;>
    [exact Or.inl ⟨m, unx_subset_inner Q Ex hm, h⟩; exact Or.inr ⟨m, unx_subset_inner Q Ex hm, h⟩]

noncomputable def remG : FK.Configuration Q.pG :=
  FK.subgraphRemovedEdges ((Q.subG Ex).map (Q.subEmb Ex)) Q.pG

theorem endEdge_mem_remG {m : Cell} (hm : m ∈ Q.inner) :
    endEdgeEquiv Q.pData ⟨m, hm⟩ ∈ Q.remG Ex ↔ m ∉ Q.unx Ex := by
  unfold remG
  rw [FK.mem_subgraphRemovedEdges, endEdgeEquiv_val, SimpleGraph.mem_edgeSet, SimpleGraph.map_adj]
  refine ⟨fun h hmU => h ⟨⟨(primalEnds m).1, mem_vrx.2 ⟨m, hmU, Or.inl rfl⟩⟩,
    ⟨(primalEnds m).2, mem_vrx.2 ⟨m, hmU, Or.inr rfl⟩⟩,
    (endGraph_adj _ _).2 ⟨fun h => primalEnds_ne m (congrArg Subtype.val h), Or.inl ⟨m, hmU, rfl⟩⟩,
    rfl, rfl⟩, fun h ⟨a, b, hab, ha, hb⟩ => h ?_⟩
  rw [endGraph_adj] at hab
  have ha' : a.1 = (primalEnds m).1 := congrArg Subtype.val ha
  have hb' : b.1 = (primalEnds m).2 := congrArg Subtype.val hb
  rcases hab.2 with ⟨m', hm', he⟩ | ⟨m', hm', he⟩
  · rwa [← (primalEnds_inj (Or.inl (by rw [he, ha', hb'])) : m' = m)]
  · rwa [← (primalEnds_inj (Or.inr (by rw [he, ha', hb']; rfl)) : m' = m)]

theorem embeddedEdge_endEdge {m : Cell} (hm : m ∈ Q.unx Ex) :
    FK.embeddedEdgeEmbedding (Q.subG Ex) Q.pG (Q.subEmb Ex) (Q.subLe Ex)
      (endEdgeEquiv (Q.subData Ex) ⟨m, hm⟩) =
        endEdgeEquiv Q.pData ⟨m, unx_subset_inner Q Ex hm⟩ :=
  Subtype.ext (by rw [FK.embeddedEdgeEmbedding_coe, endEdgeEquiv_val, endEdgeEquiv_val]; rfl)

theorem openMedials_restr (C : FK.Configuration Q.pG) :
    openMedials (Q.subData Ex)
      (FK.embeddedConfigurationRestriction (Q.subG Ex) Q.pG (Q.subEmb Ex) (Q.subLe Ex) C) =
        openMedials Q.pData C ∩ Q.unx Ex := by
  ext m
  rw [Finset.mem_inter, mem_openMedials, mem_openMedials]
  exact ⟨fun ⟨hm, h⟩ => ⟨⟨unx_subset_inner Q Ex hm, by
      rwa [FK.mem_embeddedConfigurationRestriction, embeddedEdge_endEdge] at h⟩, hm⟩,
    fun ⟨⟨_, h⟩, hmU⟩ => ⟨hmU, by rwa [FK.mem_embeddedConfigurationRestriction, embeddedEdge_endEdge]⟩⟩

variable {Q Ex}

theorem cfgOf_subset_remG {H₀ : Finset Cell} (hH : H₀ ⊆ Ex) :
    cfgOf Q.pData H₀ ⊆ Q.remG Ex := by
  intro e he
  obtain ⟨m, rfl⟩ := (endEdgeEquiv Q.pData).surjective e
  exact (endEdge_mem_remG Q Ex m.2).2 fun hU => (mem_unx.1 hU).2 (hH ((mem_cfgOf _ _ _).1 he))

noncomputable def froz {H₀ : Finset Cell} (hH : H₀ ⊆ Ex) :
    FK.RemovedConfiguration Q.pG (Q.remG Ex) :=
  ⟨cfgOf Q.pData H₀, cfgOf_subset_remG hH⟩

theorem mem_inter_remG (C : FK.Configuration Q.pG) {m : Cell}
    (hm : m ∈ Q.inner) :
    (endEdgeEquiv Q.pData ⟨m, hm⟩ ∈ C ∧ endEdgeEquiv Q.pData ⟨m, hm⟩ ∈ Q.remG Ex) ↔
      (m ∈ openMedials Q.pData C ∧ m ∈ Ex) := by
  rw [endEdge_mem_remG Q Ex hm, mem_openMedials, mem_unx]
  exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hm, h1⟩, by tauto⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, by tauto⟩⟩

theorem frozen_iff (hEx : Ex ⊆ Q.inner) {H₀ : Finset Cell} (hH : H₀ ⊆ Ex)
    (C : FK.Configuration Q.pG) :
    C ∈ FK.frozenStateEvent (Q.remG Ex) (froz hH) ↔ openMedials Q.pData C ∩ Ex = H₀ := by
  unfold FK.frozenStateEvent
  rw [Set.mem_ofPred_eq, Finset.ext_iff, Finset.ext_iff]
  simp only [Finset.mem_inter]
  exact ⟨fun h m => ⟨fun hm => (mem_cfgOf Q.pData H₀ ⟨m, hEx hm.2⟩).1
      ((h _).1 ((mem_inter_remG C (hEx hm.2)).2 hm)),
    fun hm => (mem_inter_remG C (hEx (hH hm))).1
      ((h _).2 ((mem_cfgOf Q.pData H₀ ⟨m, hEx (hH hm)⟩).2 hm))⟩,
    fun h e => by
      obtain ⟨m, rfl⟩ := (endEdgeEquiv Q.pData).surjective e
      rw [mem_inter_remG C m.2]
      exact (h m.1).trans (mem_cfgOf Q.pData H₀ m).symm⟩

def bcOfSetoid {V : Type*} (s : Setoid V) : FK.BoundaryCondition V where
  boundary := Set.univ
  partition := s
  supported _ := Or.inr ⟨Set.mem_univ _, Set.mem_univ _⟩

variable (Q Ex)

noncomputable def nuMeasure (θ : FK.Parameters) (P : Setoid Q.pcells) (𝒮 : Set (Finset Cell)) :
    ENNReal :=
  FK.measure (Q.subG Ex) θ (bcOfSetoid (Setoid.comap (Q.subEmb Ex) P))
    {C' | openMedials (Q.subData Ex) C' ∈ 𝒮}

variable {Q Ex}

attribute [local instance] FK.configurationMeasurableSpace in
theorem markov_cell (θ : FK.Parameters) (ξ : FK.BoundaryCondition Q.pcells) (hEx : Ex ⊆ Q.inner)
    {H₀ : Finset Cell} (hH : H₀ ⊆ Ex) (𝒮 : Set (Finset Cell)) :
    FK.measure Q.pG θ ξ {C | openMedials Q.pData C ∩ Ex = H₀ ∧
        openMedials Q.pData C ∩ Q.unx Ex ∈ 𝒮} =
      nuMeasure Q Ex θ (FK.componentSetoid Q.pG ξ (cfgOf Q.pData H₀)) 𝒮 *
        FK.measure Q.pG θ ξ {C | openMedials Q.pData C ∩ Ex = H₀} := by
  have h := embedded_frozen_measure_eq (Q.subG Ex) Q.pG (Q.subEmb Ex) (Q.subLe Ex) θ ξ (froz hH)
    {C' | openMedials (Q.subData Ex) C' ∈ 𝒮}
  rwa [show {C | FK.embeddedConfigurationRestriction (Q.subG Ex) Q.pG (Q.subEmb Ex)
        (Q.subLe Ex) C ∈ {C' | openMedials (Q.subData Ex) C' ∈ 𝒮}} ∩
      FK.frozenStateEvent (FK.subgraphRemovedEdges ((Q.subG Ex).map (Q.subEmb Ex)) Q.pG) (froz hH) =
        {C | openMedials Q.pData C ∩ Ex = H₀ ∧ openMedials Q.pData C ∩ Q.unx Ex ∈ 𝒮} by
      ext C; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, openMedials_restr]
      exact and_comm.trans (and_congr_left' (frozen_iff hEx hH C)),
    show FK.frozenStateEvent (FK.subgraphRemovedEdges ((Q.subG Ex).map (Q.subEmb Ex)) Q.pG)
        (froz hH) = {C | openMedials Q.pData C ∩ Ex = H₀} by ext C; exact frozen_iff hEx hH C] at h

theorem openMedials_mono' {C C' : FK.Configuration Q.pG} (h : C ⊆ C') :
    openMedials Q.pData C ⊆ openMedials Q.pData C' := fun m hm => by
  obtain ⟨hmI, he⟩ := (mem_openMedials Q.pData C m).1 hm
  exact (mem_openMedials Q.pData C' m).2 ⟨hmI, h he⟩

theorem openMedials_mono_sub {C C' : FK.Configuration (Q.subG Ex)} (h : C ⊆ C') :
    openMedials (Q.subData Ex) C ⊆ openMedials (Q.subData Ex) C' := fun m hm => by
  obtain ⟨hmI, he⟩ := (mem_openMedials (Q.subData Ex) C m).1 hm
  exact (mem_openMedials (Q.subData Ex) C' m).2 ⟨hmI, h he⟩

attribute [local instance] FK.configurationMeasurableSpace in
theorem nu_mono (θ : FK.Parameters) {P P' : Setoid Q.pcells}
    (hPP : ∀ x y : Q.pcells, Vtx (Q.unx Ex) x.1 → Vtx (Q.unx Ex) y.1 → P.r x y → P'.r x y)
    {𝒮 : Set (Finset Cell)} (h𝒮 : ∀ A B : Finset Cell, A ⊆ B → A ∈ 𝒮 → B ∈ 𝒮) :
    (nuMeasure Q Ex θ P 𝒮).toReal ≤ (nuMeasure Q Ex θ P' 𝒮).toReal :=
  FK.measure_boundary_comparison _ _ _
    (fun a b => hPP (Q.subEmb Ex a) (Q.subEmb Ex b) (mem_vrx.1 a.2) (mem_vrx.1 b.2)) _
    (fun _ _ hCC' => h𝒮 _ _ (openMedials_mono_sub hCC'))

end Rect

end PottsDiscontinuity.TorusCrossing
