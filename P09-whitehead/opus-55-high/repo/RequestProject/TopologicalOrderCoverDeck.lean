import RequestProject.Statement
import RequestProject.HomeomorphContinuousMap
import RequestProject.TopologicalOrderCover
import RequestProject.StrictPosetCovering
import RequestProject.Tac


/-! Genuine topological deck transformations act on the reconstructed
ordered cover and its strict cells. Compatibility holds on vertices,
edges and faces, not only on vertices. Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
open scoped unitInterval
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def deckSubgroup : Subgroup (Equiv.Perm E) where
  carrier := {g | Continuous g ∧ Continuous g.symm ∧ ∀ x, p (g x) = p x}
  one_mem' := ⟨continuous_id, continuous_id, fun _ => rfl⟩
  mul_mem' {g h} hg hh := by
    refine ⟨hg.1.comp hh.1, hh.2.1.comp hg.2.1, ?_⟩
    simp_all
  inv_mem' {g} hg := by
    refine ⟨hg.2.1, hg.1, ?_⟩
    intro x
    have hh := hg.2.2 (g.symm x)
    simp_all

def deckHomeomorph (g : deckSubgroup p) : E ≃ₜ E where
  toEquiv := g.val
  continuous_toFun := g.property.1
  continuous_invFun := g.property.2.1

def deckFibre (g : deckSubgroup p) x :
    (p ⁻¹' {x}) ≃ (p ⁻¹' {x}) where
  toFun e := ⟨g.val e.val, (g.property.2.2 e.val).trans e.property⟩
  invFun e := ⟨g.val.symm e.val, by
    have hh := g.property.2.2 (g.val.symm e.val)
    grind⟩
  left_inv e := Subtype.ext (g.val.symm_apply_apply e.val)
  right_inv e := Subtype.ext (g.val.apply_symm_apply e.val)

theorem monodromy_deck g
    {x y} γ e :
    hp.monodromy γ (deckFibre p g x e) = deckFibre p g y (hp.monodromy γ e) := by
  obtain ⟨γ⟩ := γ
  have h₀ : γ 0 = p e.val := γ.source.trans e.property.symm
  have h₁ : γ 0 = p (g.val e.val) := h₀.trans (g.property.2.2 e.val).symm
  let L := hp.liftPath γ e.val h₀
  let M := (deckHomeomorph p g).toContinuousMap.comp L
  have hM : M = hp.liftPath γ _ h₁ := by
    apply (hp.eq_liftPath_iff' h₁).mpr
    constructor
    · funext t
      change p (g.val (L t)) = γ t
      rw [g.property.2.2]
      exact congrFun (hp.liftPath_lifts γ e.val h₀) t
    · change g.val (hp.liftPath γ e.val h₀ 0) = g.val e.val
      rw [hp.liftPath_zero]
  apply Subtype.ext
  exact (congrArg (· 1) hM).symm

def deck (g : deckSubgroup p) : Cover p hp ≃o Cover p hp where
  toFun v := ⟨v.1, deckFibre p g (orderNerveRealizationVertex v.1) v.2⟩
  invFun v := ⟨v.1, (deckFibre p g (orderNerveRealizationVertex v.1)).symm v.2⟩
  left_inv v := by
    simp
  right_inv v := by
    simp
  map_rel_iff' := by
    intro v w
    constructor
    · rintro ⟨hvw, hval⟩
      refine ⟨hvw, ?_⟩
      apply (deckFibre p g (orderNerveRealizationVertex w.1)).injective
      exact (monodromy_deck p hp g
        (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath hvw)) v.2).symm.trans hval
    · rintro ⟨hvw, hval⟩
      refine ⟨hvw, ?_⟩
      exact (monodromy_deck p hp g
        (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath hvw)) v.2).trans
        (congrArg (deckFibre p g (orderNerveRealizationVertex w.1)) hval)

theorem deck_one v : deck p hp 1 v = v := by
  rfl

theorem deck_mul g h v :
    deck p hp (g * h) v = deck p hp g (deck p hp h v) := by
  rfl

def strictDeckAction : DeckAction (strictOrderCx (Cover p hp)) (deckSubgroup p) where
  smulV := fun g => deck p hp g
  smulE g e := ⟨(deck p hp g e.val.1, deck p hp g e.val.2), (deck p hp g).strictMono e.property⟩
  smulF g t := ⟨(deck p hp g t.val.1, deck p hp g t.val.2.1, deck p hp g t.val.2.2),
    (deck p hp g).strictMono t.property.1, (deck p hp g).strictMono t.property.2⟩
  one_smulV := deck_one p hp
  mul_smulV := deck_mul p hp
  one_smulE _ := Subtype.ext (Prod.ext (deck_one p hp _) (deck_one p hp _))
  mul_smulE g h _ := Subtype.ext (Prod.ext (deck_mul p hp g h _) (deck_mul p hp g h _))
  one_smulF _ := Subtype.ext (Prod.ext (deck_one p hp _) (Prod.ext (deck_one p hp _) (deck_one p hp _)))
  mul_smulF g h _ := Subtype.ext (Prod.ext (deck_mul p hp g h _)
    (Prod.ext (deck_mul p hp g h _) (deck_mul p hp g h _)))
  src_smul _ _ := rfl
  tgt_smul _ _ := rfl
  base_smul _ _ := rfl
  att_smul _ _ := rfl

def strictProjection (hs : Function.Surjective p) := (projection_isPosetCover p hp hs).strictMap

theorem strictProjection_isCovering hs :
    IsCovering (strictProjection p hp hs) := (projection_isPosetCover p hp hs).strictMap_isCovering

theorem strictDeck_edges hs g
    e :
    (strictProjection p hp hs).onE ((strictDeckAction p hp).smulE g e) =
      (strictProjection p hp hs).onE e := rfl

theorem strictDeck_faces hs g
    t :
    (strictProjection p hp hs).onF ((strictDeckAction p hp).smulF g t) =
      (strictProjection p hp hs).onF t := rfl

theorem strictProjection_isRegular [ConnectedSpace E] hs
    (hr : Whitehead.Regular p) : IsRegular (strictProjection p hp hs) (strictDeckAction p hp) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro v w hvw
  have hproj :=
    (point_projection p hp v).trans
      ((congrArg _ hvw).trans (point_projection p hp w).symm)
  obtain ⟨e, he, hev⟩ := hr _ _ hproj
  let g : deckSubgroup p := ⟨e.toEquiv, e.continuous, e.symm.continuous, he⟩
  have hgv : (strictDeckAction p hp).smulV g v = w := by
    cases' v with v x
    cases' w with w y
    change v = w at hvw
    subst w
    refine Sigma.ext rfl ?_
    exact heq_of_eq (Subtype.ext hev)
  refine ⟨g, hgv, ?_⟩
  intro h hh
  have hpoint : h.val (point p hp v) = g.val (point p hp v) :=
    (congrArg (point p hp) hh).trans (by aesop)
  apply Subtype.ext
  apply Equiv.ext
  exact congrFun (hp.eq_of_comp_eq h.property.1 g.property.1
    (funext (fun x => (h.property.2.2 x).trans (g.property.2.2 x).symm))
    _ hpoint)
