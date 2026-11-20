/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.IsolatedExtension
public import Mathlib.Data.Setoid.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

section
variable {V W : Type*} {G : SimpleGraph V} (f : V ↪ W) (ξ : BoundaryCondition W)
include f ξ

/-- Pull back an arbitrary boundary partition along an injective vertex map. -/
def isolatedExtensionPullbackBoundary : BoundaryCondition V where
  boundary := f ⁻¹' ξ.boundary
  partition := Setoid.comap f ξ.partition
  supported := by
    intro u v huv
    have h := (Setoid.comap_rel f ξ.partition u v).mp huv
    rcases ξ.supported h with heq | ⟨hu, hv⟩
    · exact Or.inl (f.injective heq)
    · exact Or.inr ⟨hu, hv⟩

def isolatedExtensionExteriorBoundaryClasses :=
  {C : Quotient ξ.partition // ∀ v : V, Quotient.mk ξ.partition (f v) ≠ C}

def isolatedBoundaryComponentLabel (A : Configuration G) (x : W) :
    Sum (Quotient (componentSetoid (isolatedExtensionPullbackBoundary f ξ) A))
      (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  classical
  by_cases hx : ∃ u, ξ.partition.r (f u) x
  · exact Sum.inl (Quotient.mk _ (Classical.choose hx))
  · exact Sum.inr ⟨Quotient.mk ξ.partition x, by
      intro u heq
      apply hx
      exact ⟨u, Quotient.exact heq⟩⟩

end

section
variable {V W : Type*} {G : SimpleGraph V} {f : V ↪ W} {ξ : BoundaryCondition W}
    (A : Configuration G) {u : V} {x : W}

private theorem isolatedBoundaryLabel_of_hit (hux : ξ.partition.r (f u) x) :
    isolatedBoundaryComponentLabel f ξ A x =
      Sum.inl (Quotient.mk _ u) := by
  classical
  unfold isolatedBoundaryComponentLabel
  rw [dite_eq_left ⟨u, hux⟩]
  apply congrArg Sum.inl
  apply Quotient.sound
  apply boundary_component G _ A
  apply (Setoid.comap_rel f ξ.partition _ _).mpr
  let hhit : ∃ z, ξ.partition.r (f z) x := ⟨u, hux⟩
  have hchoose :=
    Classical.choose_spec hhit
  solve_by_elim [Setoid.trans']

private theorem isolatedBoundaryLabel_of_no_hit (hx : ¬ ∃ u, ξ.partition.r (f u) x) :
    isolatedBoundaryComponentLabel f ξ A x =
      Sum.inr ⟨Quotient.mk ξ.partition x, by
        intro u heq
        apply hx
        exact ⟨u, Quotient.exact heq⟩⟩ := by
  simp [dite_eq_right hx, isolatedBoundaryComponentLabel]

end

section
variable {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) (ξ : BoundaryCondition W)
    (A : Configuration G) (x y : W)
include f A

private theorem actualConnected_isolatedExtension_iff_explicit :
    ActualConnected (isolatedExtensionConfigurationEquiv G f A) x y ↔
      x = y ∨ ∃ u v, ActualConnected A u v ∧ f u = x ∧ f v = y := by
  simpa only [ActualConnected, openGraph_isolatedExtension] using
    (reachable_isolatedExtension _ f x y)

private theorem isolatedBoundaryInnerRel_maps {u v : V}
    (h : (componentSetoid (isolatedExtensionPullbackBoundary f ξ) A).r u v) :
    (componentSetoid ξ (isolatedExtensionConfigurationEquiv G f A)).r (f u) (f v) := by
  rw [componentSetoid_rel_iff] at h ⊢
  induction h with
  | rel u v huv =>
      rcases huv with hconn | hξ
      · exact Relation.EqvGen.rel _ _ (Or.inl
          ((actualConnected_isolatedExtension G f A u v).mpr hconn))
      · exact Relation.EqvGen.rel _ _ (Or.inr
          (by assumption))
  | refl u => exact Relation.EqvGen.refl _
  | symm u v huv ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v z huv hvz ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

include ξ x y in
def isolatedBoundaryComponentRelation : Prop :=
  ξ.partition.r x y ∨ ∃ u v,
    ξ.partition.r x (f u) ∧
    (componentSetoid (isolatedExtensionPullbackBoundary f ξ) A).r u v ∧
    ξ.partition.r (f v) y

 theorem componentSetoid_isolatedExtension_iff_boundaryRelation :
    (componentSetoid ξ (isolatedExtensionConfigurationEquiv G f A)).r x y ↔
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
              actualConnected_component _ huv,
              Setoid.refl' ξ.partition _⟩
        · exact Or.inl hξ
    | refl x => exact Or.inl (Setoid.refl' ξ.partition _)
    | symm x y hxy ih =>
        rcases ih with hξ | ⟨u, v, hxu, huv, hvy⟩
        · exact Or.inl (Setoid.symm' ξ.partition hξ)
        · exact Or.inr ⟨v, u, Setoid.symm' ξ.partition hvy, Setoid.symm' _ huv, Setoid.symm' ξ.partition hxu⟩
    | trans x y z hxy hyz ih₁ ih₂ =>
        rcases ih₁ with hxy | ⟨u, v, hxu, huv, hvy⟩
        · rcases ih₂ with hyz | ⟨u', v', hyu', hu'v', hv'z⟩
          · exact Or.inl (Setoid.trans' ξ.partition hxy hyz)
          · exact Or.inr ⟨u', v', Setoid.trans' ξ.partition hxy hyu', hu'v', hv'z⟩
        · rcases ih₂ with hyz | ⟨u', v', hyu', hu'v', hv'z⟩
          · exact Or.inr ⟨u, v, hxu, huv, Setoid.trans' ξ.partition hvy hyz⟩
          · have hcomp :=
              boundary_component G (isolatedExtensionPullbackBoundary f ξ) A ((Setoid.comap_rel f ξ.partition v u').mpr (Setoid.trans' ξ.partition hvy hyu'))
            exact Or.inr ⟨u, v', hxu, Setoid.trans' _ huv (Setoid.trans' _ hcomp hu'v'), hv'z⟩
  · intro h
    rcases h with hξ | ⟨u, v, hxu, huv, hvy⟩
    · solve_by_elim [boundary_component]
    · exact (componentSetoid ξ
        (isolatedExtensionConfigurationEquiv G f A)).trans
          (boundary_component _ ξ
            _ hxu)
          (Setoid.trans' _
          (isolatedBoundaryInnerRel_maps G f ξ A huv)
            (boundary_component _ ξ
              _ hvy))

 theorem isolatedBoundaryRelation_iff_label_eq :
    isolatedBoundaryComponentRelation G f ξ A x y ↔
      isolatedBoundaryComponentLabel f ξ A x =
        isolatedBoundaryComponentLabel f ξ A y := by
  classical
  constructor
  · intro h
    rcases h with hξ | ⟨u, v, hxu, huv, hvy⟩
    · by_cases hx : ∃ z, ξ.partition.r (f z) x
      · rw [isolatedBoundaryLabel_of_hit A
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_hit A
              (Setoid.trans' ξ.partition (Classical.choose_spec hx) hξ)]
      · rw [isolatedBoundaryLabel_of_no_hit A hx,
            isolatedBoundaryLabel_of_no_hit A (by
              intro hy
              rcases hy with ⟨z, hzy⟩
              exact hx ⟨z, Setoid.trans' ξ.partition hzy (Setoid.symm' ξ.partition hξ)⟩)]
        congr 1
        apply Subtype.ext
        exact Quotient.sound hξ
    · rw [isolatedBoundaryLabel_of_hit A (Setoid.symm' ξ.partition hxu),
        isolatedBoundaryLabel_of_hit A hvy]
      exact congrArg Sum.inl (Quotient.sound huv)
  · intro h
    by_cases hx : ∃ u, ξ.partition.r (f u) x
    · by_cases hy : ∃ v, ξ.partition.r (f v) y
      · rw [isolatedBoundaryLabel_of_hit A
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_hit A
              (Classical.choose_spec hy)] at h
        exact Or.inr ⟨Classical.choose hx, Classical.choose hy,
          Setoid.symm' ξ.partition (Classical.choose_spec hx), (Quotient.exact (Sum.inl.inj h)),
          Classical.choose_spec hy⟩
      · rw [isolatedBoundaryLabel_of_hit A
              (Classical.choose_spec hx),
            isolatedBoundaryLabel_of_no_hit A hy] at h
        grind
    · by_cases hy : ∃ v, ξ.partition.r (f v) y
      · rw [isolatedBoundaryLabel_of_no_hit A hx,
            isolatedBoundaryLabel_of_hit A
              (Classical.choose_spec hy)] at h
        grind
      · rw [isolatedBoundaryLabel_of_no_hit A hx,
            isolatedBoundaryLabel_of_no_hit A hy] at h
        exact Or.inl (Quotient.exact (congrArg Subtype.val (Sum.inr.inj h)))

 theorem isolatedBoundaryComponentLabel_surjective :
    Function.Surjective (isolatedBoundaryComponentLabel f ξ A) := by
  classical
  intro z
  rcases z with q | c
  · obtain ⟨u, rfl⟩ := Quotient.mk_surjective q
    exact ⟨f u, isolatedBoundaryLabel_of_hit A
      (Setoid.refl' ξ.partition _)⟩
  · obtain ⟨x, hx⟩ := Quotient.mk_surjective c.1
    refine ⟨x, ?_⟩
    rw [isolatedBoundaryLabel_of_no_hit A (by
      rintro ⟨u, hrel⟩
      apply c.2 u
      exact (Quotient.sound hrel).trans hx)]
    congr 1
    exact Subtype.ext hx

/-- The component classes of an isolated vertex extension split into the
components represented by the original vertices and the exterior boundary
classes disjoint from the embedded vertex range. -/
noncomputable def isolatedExtensionComponentQuotientEquiv :
    Quotient (componentSetoid ξ (isolatedExtensionConfigurationEquiv G f A)) ≃
      Sum (Quotient (componentSetoid (isolatedExtensionPullbackBoundary f ξ) A))
        (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  let F := isolatedBoundaryComponentLabel f ξ A
  have hrel : componentSetoid ξ
      (isolatedExtensionConfigurationEquiv G f A) = Setoid.ker F := Setoid.ext fun x y => Iff.trans (componentSetoid_isolatedExtension_iff_boundaryRelation G f ξ A x y) (isolatedBoundaryRelation_iff_label_eq G f ξ A x y)
  exact (Quotient.congrRight (fun x y => hrel ▸ Iff.rfl)).trans
    (Setoid.quotientKerEquivOfSurjective F
      (isolatedBoundaryComponentLabel_surjective G f ξ A))

end

/-- The exact component count is the pullback-boundary component count plus
all boundary classes wholly outside the embedded vertex range. -/
theorem componentCount_isolatedExtension_boundary_pullback {V W : Type*}
    [Finite V] [Finite W] (G : SimpleGraph V) (f : V ↪ W)
    (ξ : BoundaryCondition W) (A : Configuration G) :
    componentCount ξ (isolatedExtensionConfigurationEquiv G f A) =
      componentCount (isolatedExtensionPullbackBoundary f ξ) A +
        Nat.card (isolatedExtensionExteriorBoundaryClasses f ξ) := by
  let : Finite (isolatedExtensionExteriorBoundaryClasses f ξ) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  rw [componentCount, componentCount, ← Nat.card_sum]
  exact Nat.card_congr (isolatedExtensionComponentQuotientEquiv G f ξ A)

end
end PottsDiscontinuity.FK
