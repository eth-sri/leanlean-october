module

public import PottsDiscontinuity.FK.EmbeddedClosedInteriorOuterComparison
public import PottsDiscontinuity.FK.FrozenLimitBridge
public import PottsDiscontinuity.FK.WiredBoxLaw

/-! Wired domain monotonicity on arbitrary finite induced lattice domains.
The exterior extension is open, exactly as for the existing wired box laws.
The restriction argument follows `FK/WiredBoxComparison.lean`. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK MeasureTheory
noncomputable section

abbrev domainGraph (S : Finset LatticeVertex) :=
  squareLattice.induce (S : Set LatticeVertex)

section
variable {S T : Finset LatticeVertex} (hST : S ⊆ T)
/-- Inclusion preserving the original vertices of finite lattice domains. -/
def domainVertexEmbedding  :
    (S : Set LatticeVertex) ↪ (T : Set LatticeVertex) where
  toFun x := ⟨x.1, hST x.2⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun z : (T : Set LatticeVertex) => z.val) h)

theorem domainGraph_map  :
    (domainGraph S).map (domainVertexEmbedding hST) ≤ domainGraph T := by
  intro x y h
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
  tauto
end

/-- The whole-lattice extension of a finite sample with every exterior edge open. -/
def wiredDomainConfiguration (S : Finset LatticeVertex) (A : Configuration (domainGraph S)) :
    LatticeConfiguration := fun e => decide (∀ f, frozenEdgeEmbedding S f = e → f ∈ A)


section
variable (θ : Parameters)
/-- The genuine wired FK law on a finite domain on the common configuration carrier. -/
def wiredDomainProbabilityMeasure (S : Finset LatticeVertex) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law (domainGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S))).map
    (wiredDomainConfiguration S)).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

theorem wiredDomainProbabilityMeasure_box (c : LatticeVertex) (r : ℕ) :
    wiredDomainProbabilityMeasure θ (latticeBox c r) = wiredBoxProbabilityMeasure θ c r := by
  unfold wiredDomainProbabilityMeasure wiredBoxProbabilityMeasure wiredBoxLaw
  rfl
end

section
variable (S : Finset LatticeVertex) (F : Finset squareLattice.edgeSet)
/-- The finite increasing cylinder event read under open exterior extension. -/
def wiredDomainCylinderEvent  :
    Set (Configuration (domainGraph S)) :=
  {A | ∀ e ∈ F, ∀ f, frozenEdgeEmbedding S f = e → f ∈ A}

theorem wiredDomainCylinderEvent_upper  : IsUpperSet (wiredDomainCylinderEvent S F) := by
  tauto
end

attribute [local instance] configurationMeasurableSpace

section
variable (θ : Parameters)
theorem wiredDomainProbabilityMeasure_allOpen (S : Finset LatticeVertex)
    (F : Finset squareLattice.edgeSet) :
    (wiredDomainProbabilityMeasure θ S : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) =
    measure (domainGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S))
      (wiredDomainCylinderEvent S F) := by
  change ((law _ θ _).map (wiredDomainConfiguration S)).toMeasure _ = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  ext A
  simp only [wiredDomainConfiguration, wiredDomainCylinderEvent,
    LatticeConfiguration.allOpen, Set.mem_preimage, Set.mem_ofPred_eq, decide_eq_true_eq]

/-- Wired all-open probabilities decrease under arbitrary finite-domain inclusion. -/
theorem wiredDomainProbabilityMeasure_allOpen_antitone (S T : Finset LatticeVertex) (hST : S ⊆ T) (F : Finset squareLattice.edgeSet) :
    (wiredDomainProbabilityMeasure θ T : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) ≤
    (wiredDomainProbabilityMeasure θ S : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) := by
  let f := domainVertexEmbedding hST
  have hGH := domainGraph_map hST
  have hclosed : ∀ ⦃x : (S : Set LatticeVertex)⦄, x ∉ frozenVertexBoundary S →
      ∀ ⦃y : (T : Set LatticeVertex)⦄, (domainGraph T).Adj (f x) y →
        ∃ z, f z = y ∧ (domainGraph S).Adj x z := by
    intro x hx y hxy
    have hy : y.1 ∈ S := by
      by_contra hy
      exact hx ⟨x.2, y.1, hxy, hy⟩
    exact ⟨⟨y.1, hy⟩, rfl, hxy⟩
  have havoid : ∀ ⦃x : (S : Set LatticeVertex)⦄, x ∉ frozenVertexBoundary S →
      f x ∉ (BoundaryCondition.wired (frozenVertexBoundary T)).boundary := by
    intro x hx ⟨_, y, hxy, hy⟩
    exact hx ⟨x.2, y, hxy, fun hyS => hy (hST hyS)⟩
  have hcmp := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ (BoundaryCondition.wired (frozenVertexBoundary T))
    (frozenVertexBoundary S) hclosed havoid
    (wiredDomainCylinderEvent S F) (wiredDomainCylinderEvent_upper S F)
  have hcompat (e : (domainGraph S).edgeSet) :
      frozenEdgeEmbedding T (embeddedEdgeEmbedding (domainGraph S) (domainGraph T) f hGH e) =
        frozenEdgeEmbedding S e := by
    apply Subtype.ext
    change Sym2.map Subtype.val (Sym2.map f e.1) = Sym2.map Subtype.val e.1
    rw [Sym2.map_map]
    rfl
  have hsub : wiredDomainCylinderEvent T F ⊆
      {A | embeddedConfigurationRestriction (domainGraph S) (domainGraph T) f hGH A ∈
        wiredDomainCylinderEvent S F} := by
    intro A hA e he g hg
    simp
    exact hA e he (embeddedEdgeEmbedding (domainGraph S) (domainGraph T) f hGH g)
      ((hcompat g).trans hg)
  rw [wiredDomainProbabilityMeasure_allOpen, wiredDomainProbabilityMeasure_allOpen]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans hcmp
end

end
end PottsDiscontinuity.Duality
