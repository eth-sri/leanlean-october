/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.IsolatedExtension
public import Mathlib.Data.Setoid.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

/-- Pull back an arbitrary boundary partition along an injective vertex map. -/
def isolatedExtensionPullbackBoundary {V W : Type*} (f : V ↪ W)
    (ξ : BoundaryCondition W) : BoundaryCondition V where
  boundary := f ⁻¹' ξ.boundary
  partition := Setoid.comap f ξ.partition
  supported := by
    intro u v huv
    
    rcases ξ.supported ((Setoid.comap_rel f ξ.partition u v).mp huv) with heq | ⟨hu, hv⟩
    all_goals simp_all

def isolatedExtensionExteriorBoundaryClasses {V W : Type*} (f : V ↪ W)
    (ξ : BoundaryCondition W) :=
  {C : Quotient ξ.partition // ∀ v : V, Quotient.mk ξ.partition (f v) ≠ C}

def isolatedBoundaryComponentLabel {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) (x : W) :
    Sum (Quotient (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A))
      (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  classical
  by_cases hx : ∃ u : V, ξ.partition.r (f u) x
  · exact Sum.inl (Quotient.mk _ (Classical.choose hx))
  · exact Sum.inr ⟨Quotient.mk ξ.partition x, by
      intro u heq
      apply hx
      exact ⟨u, Quotient.exact heq⟩⟩

section

variable {V W : Type*} (G : SimpleGraph V) (f : V ↪ W)


private theorem isolatedBoundaryLabel_of_hit  (ξ : BoundaryCondition W) (A : Configuration G)
    (u : V) (x : W) (hux : ξ.partition.r (f u) x) :
    isolatedBoundaryComponentLabel G f ξ A x =
      Sum.inl (Quotient.mk _ u) := by
  
  unfold isolatedBoundaryComponentLabel
  rw [dite_eq_left ⟨u, hux⟩]
  apply congrArg Sum.inl
  apply Quotient.sound
  apply boundary_component G (isolatedExtensionPullbackBoundary f ξ) A
  
  let hhit : ∃ z : V, ξ.partition.r (f z) x := ⟨u, hux⟩
  
  exact Setoid.trans' ξ.partition (Classical.choose_spec hhit) (Setoid.symm' ξ.partition hux)

private theorem isolatedBoundaryLabel_of_no_hit  (ξ : BoundaryCondition W) (A : Configuration G)
    (x : W) (hx : ¬ ∃ u : V, ξ.partition.r (f u) x) :
    isolatedBoundaryComponentLabel G f ξ A x =
      Sum.inr ⟨Quotient.mk ξ.partition x, by
        intro u heq
        apply hx
        exact ⟨u, Quotient.exact heq⟩⟩ := by
  grind +locals

private theorem actualConnected_isolatedExtension_iff_explicit
     (A : Configuration G)
    (x y : W) :
    ActualConnected (G.map f) (isolatedExtensionConfigurationEquiv G f A) x y ↔
      x = y ∨ ∃ u v, ActualConnected G A u v ∧ f u = x ∧ f v = y := by
  simpa only [ActualConnected, openGraph_isolatedExtension] using
     reachable_isolatedExtension (openGraph G A) f x y 

private theorem isolatedBoundaryInnerRel_maps  (ξ : BoundaryCondition W) (A : Configuration G) {u v : V}
    (h : (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A).r u v) :
    (componentSetoid (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A)).r (f u) (f v) := by
  rw [componentSetoid_rel_iff] at h ⊢
  induction h with
  | rel u v huv =>
      rcases huv with hconn | hξ
      · exact Relation.EqvGen.rel _ _ (Or.inl
          ((actualConnected_isolatedExtension G f A u v).mpr hconn))
      · exact Relation.EqvGen.rel _ _ (Or.inr
          ((Setoid.comap_rel f ξ.partition u v).mp hξ))
  | refl u => exact Relation.EqvGen.refl _
  | symm u v huv ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v z huv hvz ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

end

def isolatedBoundaryComponentRelation {V W : Type*} (G : SimpleGraph V)
    (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) (x y : W)  :=
  ξ.partition.r x y ∨ ∃ u v : V,
    ξ.partition.r x (f u) ∧
    (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A).r u v ∧
    ξ.partition.r (f v) y

 section

variable {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G)


theorem componentSetoid_isolatedExtension_iff_boundaryRelation
     (x y : W) :
    (componentSetoid (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A)).r x y ↔
      isolatedBoundaryComponentRelation G f ξ A x y := by
  constructor
  · intro h
    rw [componentSetoid_rel_iff] at h
    induction h with
    | rel x y hxy =>
        rcases hxy with hconn | hξ
        · rcases (actualConnected_isolatedExtension_iff_explicit G f A x y).mp hconn with
            hEq | ⟨u, v, huv, rfl, rfl⟩
          · subst y
            exact Or.inl (Setoid.refl' ξ.partition _)
          · exact Or.inr ⟨u, v, Setoid.refl' ξ.partition _,
              actualConnected_component G (isolatedExtensionPullbackBoundary f ξ) A huv,
              Setoid.refl' ξ.partition _⟩
        · exact Or.inl hξ
    | refl x => exact Or.inl (Setoid.refl' ξ.partition _)
    | symm x y hxy ih =>
        rcases ih with hξ | ⟨u, v, hxu, huv, hvy⟩
        · exact Or.inl (Setoid.symm' ξ.partition hξ)
        · exact Or.inr ⟨v, u, Setoid.symm' ξ.partition hvy, Setoid.symm' (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A) huv, Setoid.symm' ξ.partition hxu⟩
    | trans x y z hxy hyz ih₁ ih₂ =>
        rcases ih₁ with hxy | ⟨u, v, hxu, huv, hvy⟩
        · rcases ih₂ with hyz | ⟨u', v', hyu', hu'v', hv'z⟩
          · exact Or.inl (Setoid.trans' ξ.partition hxy hyz)
          · exact Or.inr ⟨u', v', Setoid.trans' ξ.partition hxy hyu', hu'v', hv'z⟩
        · rcases ih₂ with hyz | ⟨u', v', hyu', hu'v', hv'z⟩
          · exact Or.inr ⟨u, v, hxu, huv, Setoid.trans' ξ.partition hvy hyz⟩
          · 
            
            exact Or.inr ⟨u, v', hxu, Setoid.trans' (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A) huv (Setoid.trans' (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A) (boundary_component G (isolatedExtensionPullbackBoundary f ξ) A ((Setoid.comap_rel f ξ.partition v u').mpr
                                                                                                                                                                                                                                                                          (Setoid.trans' ξ.partition hvy hyu'))) hu'v'), hv'z⟩
  · intro h
    rcases h with hξ | ⟨u, v, hxu, huv, hvy⟩
    · exact boundary_component (G.map f) ξ
        (isolatedExtensionConfigurationEquiv G f A) hξ
    · exact (componentSetoid (G.map f) ξ
        (isolatedExtensionConfigurationEquiv G f A)).trans
          (boundary_component (G.map f) ξ
            (isolatedExtensionConfigurationEquiv G f A) hxu)
          (Setoid.trans' (componentSetoid (G.map f) ξ
            (isolatedExtensionConfigurationEquiv G f A))
          (isolatedBoundaryInnerRel_maps G f ξ A huv)
            (boundary_component (G.map f) ξ
              (isolatedExtensionConfigurationEquiv G f A) hvy))

 theorem isolatedBoundaryRelation_iff_label_eq 
    (x y : W) :
    isolatedBoundaryComponentRelation G f ξ A x y ↔
      isolatedBoundaryComponentLabel G f ξ A x =
        isolatedBoundaryComponentLabel G f ξ A y := by
  
  constructor
  · intro h
    rcases h with hξ | ⟨u, v, hxu, huv, hvy⟩
    · by_cases hx : ∃ z : V, ξ.partition.r (f z) x
      · 
        rw [isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) x
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) y
              (Setoid.trans' ξ.partition (Classical.choose_spec hx) hξ)]
      · 
        rw [isolatedBoundaryLabel_of_no_hit G f ξ A x hx,
            isolatedBoundaryLabel_of_no_hit G f ξ A y (by
                                                         intro hy
                                                         rcases hy with ⟨z, hzy⟩
                                                         exact hx ⟨z, Setoid.trans' ξ.partition hzy (Setoid.symm' ξ.partition hξ)⟩)]
        congr 1
        apply Subtype.ext
        exact Quotient.sound hξ
    · rw [isolatedBoundaryLabel_of_hit G f ξ A u x (Setoid.symm' ξ.partition hxu),
        isolatedBoundaryLabel_of_hit G f ξ A v y hvy]
      exact congrArg Sum.inl (Quotient.sound huv)
  · intro h
    by_cases hx : ∃ u : V, ξ.partition.r (f u) x
    · by_cases hy : ∃ v : V, ξ.partition.r (f v) y
      · rw [isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hx) x
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_hit G f ξ A (Classical.choose hy) y
              (Classical.choose_spec hy)] at h
        
        
        exact Or.inr ⟨Classical.choose hx, Classical.choose hy,
          Setoid.symm' ξ.partition (Classical.choose_spec hx), (Quotient.exact (Sum.inl.inj h)),
          Classical.choose_spec hy⟩
      · grind +locals
    · by_cases hy : ∃ v : V, ξ.partition.r (f v) y
      · grind +locals
      · rw [isolatedBoundaryLabel_of_no_hit G f ξ A x hx,
            isolatedBoundaryLabel_of_no_hit G f ξ A y hy] at h
        
        
        exact Or.inl (Quotient.exact (congrArg Subtype.val (Sum.inr.inj h)))

 theorem isolatedBoundaryComponentLabel_surjective  :
    Function.Surjective (isolatedBoundaryComponentLabel G f ξ A) := by
  
  intro z
  rcases z with q | c
  · obtain ⟨u, rfl⟩ := Quotient.mk_surjective q
    exact ⟨f u, isolatedBoundaryLabel_of_hit G f ξ A u (f u)
      (Setoid.refl' ξ.partition (f u))⟩
  · obtain ⟨x, hx⟩ := Quotient.mk_surjective c.1
    
    refine ⟨x, ?_⟩
    rw [isolatedBoundaryLabel_of_no_hit G f ξ A x (by
                                                     rintro ⟨u, hrel⟩
                                                     apply c.2 u
                                                     exact (Quotient.sound hrel).trans hx)]
    congr 1
    apply Subtype.ext
    exact hx

end

/-- The component classes of an isolated vertex extension split into the
components represented by the original vertices and the exterior boundary
classes disjoint from the embedded vertex range. -/
noncomputable def isolatedExtensionComponentQuotientEquiv {V W : Type*}
    (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W) (A : Configuration G) :
    Quotient (componentSetoid (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A)) ≃
      Sum (Quotient (componentSetoid G (isolatedExtensionPullbackBoundary f ξ) A))
        (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  let F := isolatedBoundaryComponentLabel G f ξ A
  have hrel : componentSetoid (G.map f) ξ
      (isolatedExtensionConfigurationEquiv G f A) = Setoid.ker F := by
    apply Setoid.ext
    intro x y
    exact (componentSetoid_isolatedExtension_iff_boundaryRelation G f ξ A x y).trans
      (isolatedBoundaryRelation_iff_label_eq G f ξ A x y)
  exact (Quotient.congrRight  fun x y => hrel ▸ Iff.rfl ).trans
    (Setoid.quotientKerEquivOfSurjective F
      (isolatedBoundaryComponentLabel_surjective G f ξ A))

/-- The exact component count is the pullback-boundary component count plus
all boundary classes wholly outside the embedded vertex range. -/
theorem componentCount_isolatedExtension_boundary_pullback {V W : Type*}
    [Finite V] [Finite W] (G : SimpleGraph V) (f : V ↪ W)
    (ξ : BoundaryCondition W) (A : Configuration G) :
    componentCount (G.map f) ξ (isolatedExtensionConfigurationEquiv G f A) =
      componentCount G (isolatedExtensionPullbackBoundary f ξ) A +
        Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  
  let : Finite (isolatedExtensionExteriorBoundaryClasses f ξ) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  rw [componentCount, componentCount, ← Nat.card_sum]
  exact Nat.card_congr (isolatedExtensionComponentQuotientEquiv G f ξ A)

end
end PottsDiscontinuity.FK
