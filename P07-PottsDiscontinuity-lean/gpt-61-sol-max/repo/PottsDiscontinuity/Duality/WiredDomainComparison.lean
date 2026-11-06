module
public import Mathlib

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

/-- Inclusion preserving the original vertices of finite lattice domains. -/
def domainVertexEmbedding {S T : Finset LatticeVertex} (hST : S ⊆ T) :
    (S : Set LatticeVertex) ↪ (T : Set LatticeVertex) where
  toFun x := ⟨x.1, hST x.2⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun z : (T : Set LatticeVertex) => z.val) h)

lemma domainGraph_map {S T : Finset LatticeVertex} (hST : S ⊆ T) :
    (domainGraph S).map (domainVertexEmbedding hST) ≤ domainGraph T := SimpleGraph.map_le_iff_le_comap.mpr le_rfl

/-- The whole-lattice extension of a finite sample with every exterior edge open. -/
def wiredDomainConfiguration (S : Finset LatticeVertex) (A : Configuration (domainGraph S)) :
    LatticeConfiguration := fun e => decide (∀ f, frozenEdgeEmbedding S f = e → f ∈ A)



/-- The genuine wired FK law on a finite domain on the common configuration carrier. -/
def wiredDomainProbabilityMeasure (θ : Parameters) (S : Finset LatticeVertex) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law (domainGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S))).map
    (wiredDomainConfiguration S)).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

lemma wiredDomainProbabilityMeasure_box (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    wiredDomainProbabilityMeasure θ (latticeBox c r) = wiredBoxProbabilityMeasure θ c r := by
  unfold wiredDomainProbabilityMeasure wiredBoxProbabilityMeasure wiredBoxLaw
  rfl

/-- The finite increasing cylinder event read under open exterior extension. -/
def wiredDomainCylinderEvent (S : Finset LatticeVertex) (F : Finset squareLattice.edgeSet) :
    Set (Configuration (domainGraph S)) :=
  {A | ∀ e ∈ F, ∀ f, frozenEdgeEmbedding S f = e → f ∈ A}

lemma wiredDomainCylinderEvent_upper (S : Finset LatticeVertex)
    (F : Finset squareLattice.edgeSet) : IsUpperSet (wiredDomainCylinderEvent S F) := fun A B hAB hA e he f hf => hAB (hA e he f hf)



lemma wiredDomainProbabilityMeasure_allOpen (θ : Parameters) (S : Finset LatticeVertex)
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
theorem wiredDomainProbabilityMeasure_allOpen_antitone (θ : Parameters)
    (S T : Finset LatticeVertex) (hST : S ⊆ T) (F : Finset squareLattice.edgeSet) :
    (wiredDomainProbabilityMeasure θ T : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) ≤
    (wiredDomainProbabilityMeasure θ S : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) := by
  
  let f := domainVertexEmbedding hST
  have hGH := domainGraph_map hST
  
  
  
  have hcompat (e : (domainGraph S).edgeSet) :
      frozenEdgeEmbedding T (embeddedEdgeEmbedding (domainGraph S) (domainGraph T) f hGH e) =
        frozenEdgeEmbedding S e := by
    apply Subtype.ext
    change Sym2.map Subtype.val (Sym2.map f e.1) = Sym2.map Subtype.val e.1
    rw [Sym2.map_map]
    rfl
  
  rw [wiredDomainProbabilityMeasure_allOpen, wiredDomainProbabilityMeasure_allOpen]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (by
                                                                   intro A hA e he g hg
                                                                   rw [mem_embeddedConfigurationRestriction]
                                                                   exact hA e he (embeddedEdgeEmbedding (domainGraph S) (domainGraph T) f hGH g)
                                                                     ((hcompat g).trans hg)))).trans (embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
                                                                                                        f hGH θ (BoundaryCondition.wired (frozenVertexBoundary T))
                                                                                                        (frozenVertexBoundary S) (by
                                                                                                                                    intro x hx y hxy
                                                                                                                                    
                                                                                                                                    exact ⟨⟨y.1, (by
                                                                                                                                                    by_contra hy
                                                                                                                                                    exact hx ⟨x.2, y.1, hxy, hy⟩)⟩, rfl, hxy⟩) (by
                                                                                                                                            intro x hx ⟨_, y, hxy, hy⟩
                                                                                                                                            exact hx ⟨x.2, y, hxy, fun hyS => hy (hST hyS)⟩)
                                                                                                        (wiredDomainCylinderEvent S F) (wiredDomainCylinderEvent_upper S F))

end
end PottsDiscontinuity.Duality
