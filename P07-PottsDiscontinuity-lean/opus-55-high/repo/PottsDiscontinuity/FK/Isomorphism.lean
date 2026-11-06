/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.FK.ProbabilityProduct

@[expose] public section

namespace PottsDiscontinuity.FK
noncomputable section
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
section
variable (e : G ≃g H)
def boundaryConditionIso (ξ : BoundaryCondition V) : BoundaryCondition W where
 boundary := e '' ξ.boundary
 partition := Setoid.comap e.symm ξ.partition
 supported := by
  intro x y h
  rcases ξ.supported h with hEq | ⟨hx,hy⟩
  · simp_all
  · exact Or.inr ⟨⟨e.symm x,hx,e.apply_symm_apply x⟩,⟨e.symm y,hy,e.apply_symm_apply y⟩⟩
def configurationIsoEdgeEquiv  : G.edgeSet ≃ H.edgeSet := SimpleGraph.Iso.mapEdgeSet e
def configurationIso  : Configuration G ≃ Configuration H := (configurationIsoEdgeEquiv e).finsetCongr
end
section
variable (e : G ≃g H) (A : Configuration G)
@[simp] theorem configurationIso_val  :
 (configurationIso e A).val = A.val.map (configurationIsoEdgeEquiv e).toEmbedding := rfl

@[simp] theorem card_configurationIso  :
    (configurationIso e A).card = A.card :=
  Finset.card_map _

theorem openEdges_configurationIso  :
 openEdges H (configurationIso e A) = Sym2.map e '' openEdges G A := by
 ext z
 constructor
 · rintro ⟨b, hb, rfl⟩
   obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
   refine ⟨a.val, ⟨a, ha, rfl⟩, ?_⟩
   simpa [configurationIsoEdgeEquiv] using congrArg Subtype.val hab
 · rintro ⟨z₀, ⟨a, ha, hval⟩, hmap⟩
   subst z₀
   refine ⟨configurationIsoEdgeEquiv e a, ?_, ?_⟩
   · exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
   tauto
/-- The open graphs are isomorphic under the vertex relabeling. -/
def openGraphIso  :
    openGraph G A ≃g openGraph H (configurationIso e A) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    rw [openGraph_adj, openGraph_adj, openEdges_configurationIso]
    change (s(e u, e v) ∈ Sym2.map e '' openEdges G A) ↔ s(u, v) ∈ openEdges G A
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, hz, hzEq⟩
      have hz' : z = s(u, v) := by
        apply Sym2.map.injective e.injective
        simp_all
      simp_all
    tauto

theorem actualConnected_configurationIso (x y : V) :
    ActualConnected H (configurationIso e A) (e x) (e y) ↔ ActualConnected G A x y := by
  simpa [ActualConnected, openGraphIso] using
    (SimpleGraph.Iso.reachable_iff (φ := openGraphIso e A))
end

section
variable (e : G ≃g H) (ξ : BoundaryCondition V) (A : Configuration G)
theorem componentSetoid_configurationIso (x y : V) :
    (componentSetoid H (boundaryConditionIso e ξ) (configurationIso e A)).r (e x) (e y) ↔
      (componentSetoid G ξ A).r x y := by
  rw [componentSetoid_rel_iff, componentSetoid_rel_iff]
  have hmap : ∀ {a b : V},
      Relation.EqvGen (fun a b => ActualConnected G A a b ∨ ξ.partition.r a b) a b →
      Relation.EqvGen (fun a b =>
        ActualConnected H (configurationIso e A) a b ∨
          (boundaryConditionIso e ξ).partition.r a b) (e a) (e b) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        rcases hab with hac | hab
        · exact Relation.EqvGen.rel _ _ (Or.inl
            ((actualConnected_configurationIso e A a b).mpr hac))
        · exact Relation.EqvGen.rel _ _ (Or.inr (by change ξ.partition.r (e.symm (e a)) (e.symm (e b)); simp_all))
    | refl a => tauto
    | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  have hback : ∀ {a b : W},
      Relation.EqvGen (fun a b =>
        ActualConnected H (configurationIso e A) a b ∨
          (boundaryConditionIso e ξ).partition.r a b) a b →
      Relation.EqvGen (fun a b => ActualConnected G A a b ∨ ξ.partition.r a b)
        (e.symm a) (e.symm b) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        rcases hab with hac | hab
        · have hreach :=
            (actualConnected_configurationIso e A (e.symm a) (e.symm b)).mp
              (by simp_all)
          tauto
        · exact Relation.EqvGen.rel _ _ (Or.inr (by tauto))
    | refl a => tauto
    | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  constructor
  · intro h
    have hh := hback h
    simp_all
  simp_all

/-- The quotient by wired/open connectivity is carried bijectively; singleton
classes of isolated vertices are included because the quotient carrier is V/W. -/
def componentQuotientIso  :
    Quotient (componentSetoid G ξ A) ≃
      Quotient (componentSetoid H (boundaryConditionIso e ξ) (configurationIso e A)) where
  toFun := Quotient.map e (by
    simp [componentSetoid_configurationIso])
  invFun := Quotient.map e.symm (by
    intro x y h
    have hxy :
        (componentSetoid H (boundaryConditionIso e ξ) (configurationIso e A)).r
          (e (e.symm x)) (e (e.symm y)) := by simp_all
    exact (componentSetoid_configurationIso e ξ A (e.symm x) (e.symm y)).mp hxy)
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      simp
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      simp
end

section Finite
variable [Finite V] [Finite W]
local instance isomorphismTargetEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _

theorem componentCount_configurationIso (e : G ≃g H) (ξ : BoundaryCondition V)
    (A : Configuration G) :
    componentCount H (boundaryConditionIso e ξ) (configurationIso e A) =
      componentCount G ξ A :=
  Nat.card_congr (componentQuotientIso e ξ A).symm

section
variable (q : Parameters) (e : G ≃g H) (ξ : BoundaryCondition V)
theorem weight_configurationIso (A : Configuration G) :
    weight H q (boundaryConditionIso e ξ) (configurationIso e A) = weight G q ξ A := by
  rw [weight, weight, card_configurationIso, componentCount_configurationIso]
  have he := Nat.card_congr (configurationIsoEdgeEquiv e).symm
  grind

theorem partitionFunction_configurationIso  :
    partitionFunction H q (boundaryConditionIso e ξ) = partitionFunction G q ξ := by
  unfold partitionFunction FiniteProbability.partition
  rw [← (configurationIso e).sum_comp]
  simp_rw [weight_configurationIso]

theorem configurationProbability_configurationIso (A : Configuration G) :
    configurationProbability H q (boundaryConditionIso e ξ) (configurationIso e A) =
      configurationProbability G q ξ A := by
  simp [configurationProbability, weight_configurationIso, partitionFunction_configurationIso]

theorem law_configurationIso_map  :
    (law G q ξ).map (configurationIso e) = law H q (boundaryConditionIso e ξ) := by
  ext A
  obtain ⟨A, rfl⟩ := (configurationIso e).surjective A
  rw [FiniteProbability.map_equiv_apply, Equiv.symm_apply_apply, law_apply, law_apply,
    configurationProbability_configurationIso]
end
end Finite

end
end PottsDiscontinuity.FK
