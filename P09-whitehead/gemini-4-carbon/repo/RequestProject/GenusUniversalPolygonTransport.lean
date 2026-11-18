module

public import RequestProject.OrderNerveCommonSimplex
public import RequestProject.CylinderPi1Surjective
public import Mathlib.Topology.Homotopy.Equiv
public import RequestProject.CombPi1
public import RequestProject.GenusQuotientRelativeSupport
public import Mathlib.Order.Hom.WithTopBot
public import RequestProject.GenusCollapseIteration
public import RequestProject.GenusLoops
public import RequestProject.OrderNerveOneDecoding
public import RequestProject.PresPosetReading

@[expose] public section
noncomputable section
namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
variable (f : P → Q) (hf : Monotone f) (g : P → Q) (hg : Monotone g)
variable (hc : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ g q ∨ g q ≤ f p)
include hc

/-- Cross-comparability gives a common target simplex for both actual maps
on each source simplex. This is stronger than pointwise comparison. -/
theorem orderNerveSimplex_common_maps {n : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) :
    ∃ (m : SimplexCategory) (u : (nerve Q).obj (Opposite.op m))
      (a b : n ⟶ m),
      (∀ z, orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map a z) =
        orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z)) ∧
      (∀ z, orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map b z) =
        orderNerveRealizationMap g hg (orderNerveRealizationSimplex P s z)) := by
  have hcross : ∀ i j, f (s.obj i) ≤ g (s.obj j) ∨ g (s.obj j) ≤ f (s.obj i) := by
    intro i j
    apply hc
    rcases le_total i j with h | h
    · exact Or.inl (leOfHom (s.map (homOfLE h)))
    · exact Or.inr (leOfHom (s.map (homOfLE h)))
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common
    ((nerveMap hf.functor).app _ s) ((nerveMap hg.functor).app _ s) hcross
  refine ⟨m, u, a, b, ?_, ?_⟩
  · intro z
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator Q a u)
    rw [ha] at h
    have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s)
    exact h.trans hn.symm
  · intro z
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator Q b u)
    rw [hb] at h
    have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural g hg s)
    exact h.trans hn.symm

theorem orderNerveRealization_blend_exists (t : I) (x : orderNerveRealization P) :
    ∃ y : orderNerveRealization Q, ∀ q,
      orderNerveRealizationCoordinates Q y q =
        (1 - (t : ℝ)) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q +
        (t : ℝ) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap g hg x) q := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common_maps f hf g hg hc s
  refine ⟨orderNerveRealizationSimplex Q u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) (SimplexCategory.toTop.map b z)),
    fun q => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, ha, hb]

/-- The unique affine interpolation, defined in global barycentric coordinates. -/
def orderNerveRealizationBlend (t : I) (x : orderNerveRealization P) :
    orderNerveRealization Q := (orderNerveRealization_blend_exists f hf g hg hc t x).choose

theorem orderNerveRealizationBlend_coordinates (t : I) (x : orderNerveRealization P) (q : Q) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationBlend f hf g hg hc t x) q =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q +
      (t : ℝ) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap g hg x) q :=
  (orderNerveRealization_blend_exists f hf g hg hc t x).choose_spec q

/-- Joint continuity holds in the actual weak CW topology, including infinite posets. -/

@[simp] theorem orderNerveRealizationBlend_zero (x : orderNerveRealization P) :
    orderNerveRealizationBlend f hf g hg hc 0 x = orderNerveRealizationMap f hf x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [orderNerveRealizationBlend_coordinates]

@[simp] theorem orderNerveRealizationBlend_one (x : orderNerveRealization P) :
    orderNerveRealizationBlend f hf g hg hc 1 x = orderNerveRealizationMap g hg x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [orderNerveRealizationBlend_coordinates]

/-- A concrete topological homotopy between maps with cross-comparable images. -/
def orderNerveRealizationContiguousHomotopy :
    ContinuousMap.Homotopy
      (⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ :
        C(orderNerveRealization P, orderNerveRealization Q))
      ⟨orderNerveRealizationMap g hg, (orderNerveRealizationMap g hg).hom.continuous⟩ where
  toFun tx := orderNerveRealizationBlend f hf g hg hc tx.1 tx.2
  continuous_toFun := (by
    apply (orderNerveRealization_continuous_prod_iff P _).mpr
    intro n s
    obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common_maps f hf g hg hc s
    have he : (fun tx : I × SimplexCategory.toTop.obj n =>
        orderNerveRealizationBlend f hf g hg hc tx.1 (orderNerveRealizationSimplex P s tx.2)) =
        (fun tx => orderNerveRealizationSimplex Q u
          (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2)
            (SimplexCategory.toTop.map b tx.2))) := by
      funext tx
      apply orderNerveRealizationCoordinates_injective Q
      funext q
      rw [orderNerveRealizationBlend_coordinates, orderNerveRealizationCoordinates_blend, ha, hb]
    rw [he]
    exact (orderNerveRealizationSimplex Q u).hom.continuous.comp
      (topologicalSimplexBlend_continuous.comp
        (continuous_fst.prodMk
          (((SimplexCategory.toTop.map a).hom.continuous.comp continuous_snd).prodMk
            ((SimplexCategory.toTop.map b).hom.continuous.comp continuous_snd)))))
  map_zero_left := orderNerveRealizationBlend_zero f hf g hg hc
  map_one_left := orderNerveRealizationBlend_one f hf g hg hc

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory
open scoped unitInterval Topology Classical

theorem orderNerveRealizationMap_congr {P Q : Type} [PartialOrder P] [PartialOrder Q]
    {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (he : f = g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf x = orderNerveRealizationMap g hg x := by simp_all

variable {X S : Type} [PartialOrder X] [PartialOrder S]
  (a : S →o X) (d : S → ℕ) (hd : StrictMono d) (hd₁ : ∀ s, d s ≤ 1)

include hd hd₁ in
theorem rankOne_maximal {s t : S} (hs : d s = 1) (h : s ≤ t) : s = t := by
  by_contra hne
  have hh := hd (lt_of_le_of_ne h hne)
  grind

include hd in
theorem rankOne_minimal {s t : S} (ht : d t = 0) (h : s ≤ t) : s = t := by
  by_contra hne
  have hh := hd (lt_of_le_of_ne h hne)
  omega

def cylinderHalfCollapse : CylP a → CylP a
  | .inl x => .inl x
  | .inr s => if d s = 1 then .inl (a s) else .inr s

include hd hd₁ in
theorem cylinderHalfCollapse_monotone : Monotone (cylinderHalfCollapse a d) := by
  intro p q hpq
  rcases p with x | s <;> rcases q with y | t
  · exact hpq
  · exact hpq.elim
  · change a s ≤ y at hpq
    change CylP.le a (cylinderHalfCollapse a d (Sum.inr s)) (cylinderHalfCollapse a d (Sum.inl y))
    by_cases hs : d s = 1 <;> simpa only [cylinderHalfCollapse, hs, ↓reduceIte, CylP.le] using hpq
  · change s ≤ t at hpq
    by_cases hs : d s = 1
    · have he := rankOne_maximal d hd hd₁ hs hpq
      subst t
      exact le_rfl
    · by_cases ht : d t = 1
      · change ((if d s = 1 then Sum.inl (a s) else Sum.inr s) : CylP a) ≤
          (if d t = 1 then Sum.inl (a t) else Sum.inr t)
        rw [if_neg hs, if_pos ht]
        exact a.monotone hpq
      · change CylP.le a (cylinderHalfCollapse a d (Sum.inr s)) (cylinderHalfCollapse a d (Sum.inr t))
        simpa only [cylinderHalfCollapse, if_neg hs, if_neg ht, CylP.le] using hpq



def cylinderRealizationInclusion :
    C(orderNerveRealization X, orderNerveRealization (CylP a)) :=
  ⟨orderNerveRealizationMap (cylIn a) (cylIn_monotone a),
    (orderNerveRealizationMap (cylIn a) (cylIn_monotone a)).hom.continuous⟩

def cylinderRealizationRetraction :
    C(orderNerveRealization (CylP a), orderNerveRealization X) :=
  ⟨orderNerveRealizationMap (cylRetr a) (cylRetr_monotone a),
    (orderNerveRealizationMap (cylRetr a) (cylRetr_monotone a)).hom.continuous⟩

theorem cylinderRealization_section :
    (cylinderRealizationRetraction a).comp (cylinderRealizationInclusion a) =
      ContinuousMap.id (orderNerveRealization X) := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (cylRetr a) (cylRetr_monotone a)
    (orderNerveRealizationMap (cylIn a) (cylIn_monotone a) x) = x
  rw [orderNerveRealizationMap_comp]
  have he : cylRetr a ∘ cylIn a = id := rfl
  exact (orderNerveRealizationMap_congr _ monotone_id he x).trans
    (orderNerveRealizationMap_id _ _)


def rankOneCylinderRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (CylP a)) (orderNerveRealization X) where
  toFun := cylinderRealizationRetraction a
  invFun := cylinderRealizationInclusion a
  left_inv := ⟨(show ContinuousMap.Homotopy
    (ContinuousMap.id (orderNerveRealization (CylP a)))
    ((cylinderRealizationInclusion a).comp (cylinderRealizationRetraction a)) by
    let H₀ := orderNerveRealizationContiguousHomotopy id monotone_id
      (cylinderHalfCollapse a d) (cylinderHalfCollapse_monotone a d hd hd₁)
      (show ∀ p q : CylP a, p ≤ q ∨ q ≤ p →
      p ≤ cylinderHalfCollapse a d q ∨ cylinderHalfCollapse a d q ≤ p by
        intro p q hpq
        rcases p with x | s <;> rcases q with y | t
        · exact hpq
        · by_cases ht : d t = 1
          · rw [cylinderHalfCollapse, if_pos ht]
            rcases hpq with h | h
            · exact h.elim
            · exact Or.inr h
          · simpa only [cylinderHalfCollapse, CylP.le, if_neg ht] using hpq
        · exact hpq
        · by_cases ht : d t = 1
          · rw [cylinderHalfCollapse, if_pos ht]
            rcases hpq with h | h
            · exact Or.inl (a.monotone h)
            · have he := rankOne_maximal d hd hd₁ ht h
              subst s
              exact Or.inl (le_refl (a t))
          · simpa only [cylinderHalfCollapse, CylP.le, if_neg ht] using hpq)
    let H₁ := orderNerveRealizationContiguousHomotopy
      (cylinderHalfCollapse a d) (cylinderHalfCollapse_monotone a d hd hd₁)
      (cylCollapse a) (cylCollapse_monotone a) (by
        intro p q hpq
        rcases p with x | s <;> rcases q with y | t
        · exact hpq
        · rcases hpq with h | h
          · exact h.elim
          · exact Or.inr h
        · rcases hpq with h | h
          · by_cases hs : d s = 1
            · change CylP.le a (cylinderHalfCollapse a d (Sum.inr s)) (cylCollapse a (Sum.inl y)) ∨
                CylP.le a (cylCollapse a (Sum.inl y)) (cylinderHalfCollapse a d (Sum.inr s))
              simpa only [cylinderHalfCollapse, if_pos hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq, CylP.le] using
                (Or.inl h : a s ≤ y ∨ y ≤ a s)
            · apply Or.inl
              simpa only [cylinderHalfCollapse, CylP.le, if_neg hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq] using h
          · exact h.elim
        · by_cases hs : d s = 1
          · simp only [cylinderHalfCollapse, CylP.le, if_pos hs, cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq]
            exact hpq.elim (fun h => Or.inl (a.monotone h)) (fun h => Or.inr (a.monotone h))
          · have hs₀ : d s = 0 := by have := hd₁ s; omega
            apply Or.inl
            change ((if d s = 1 then Sum.inl (a s) else Sum.inr s) : CylP a) ≤ Sum.inl (a t)
            rw [if_neg hs]
            rcases hpq with h | h
            · exact a.monotone h
            · have he := rankOne_minimal d hd hs₀ h
              subst t
              exact le_rfl)
    have hzero :
        (⟨orderNerveRealizationMap id monotone_id,
          (orderNerveRealizationMap id monotone_id).hom.continuous⟩ :
            C(orderNerveRealization (CylP a), orderNerveRealization (CylP a))) =
          ContinuousMap.id _ := by
      apply ContinuousMap.ext
      exact orderNerveRealizationMap_id (CylP a)
    have hone :
        (⟨orderNerveRealizationMap (cylCollapse a) (cylCollapse_monotone a),
          (orderNerveRealizationMap (cylCollapse a) (cylCollapse_monotone a)).hom.continuous⟩ :
            C(orderNerveRealization (CylP a), orderNerveRealization (CylP a))) =
        (cylinderRealizationInclusion a).comp (cylinderRealizationRetraction a) := by
      apply ContinuousMap.ext
      intro x
      exact (orderNerveRealizationMap_comp (cylRetr a) (cylRetr_monotone a)
        (cylIn a) (cylIn_monotone a) x).symm
    exact (hzero ▸ hone ▸ H₀.trans H₁)).symm⟩
  right_inv := by rw [cylinderRealization_section]

end FiniteChains.Comb
end

namespace FiniteChains.PresModel
open Comb CategoryTheory
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool))

def presCylinderRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (CylBase w))
      (orderNerveRealization (Rose A)) :=
  rankOneCylinderRealizationHomotopyEquiv (aHom w) (circleDimension w)
    (circleDimension_strictMono w) (circleDimension_le_one w)

end FiniteChains.PresModel

namespace FiniteChains.RelativeAttachment
open Topology

universe u
variable {A B D Y : Type u} [TopologicalSpace B] [TopologicalSpace D]
  [TopologicalSpace Y] (r : A → B) (i : A → D)
  (f : C(B, Y)) (g : C(D, Y))
  (hbd : ∀ a, f (r a) = g (i a))
  (hf : Function.Injective f)
  (hsep : ∀ d, g d ∈ Set.range f ↔ d ∈ Set.range i)
  (hnew : ∀ d e, d ∉ Set.range i → e ∉ Set.range i → g d = g e → d = e)
  (hq : IsQuotientMap (Sum.elim f g))

def attachmentQuotientHomeomorph : Space r i ≃ₜ Y := by
  let F := desc r i f g hbd
  have hcomp : F ∘ quotientMap r i = Sum.elim f g := by
    funext z
    rcases z with b | d
    · exact desc_old r i f g hbd b
    · exact desc_cell r i f g hbd d
  have hFq : IsQuotientMap F := IsQuotientMap.of_comp
    (quotientMap_continuous r i) F.continuous (hcomp.symm ▸ hq)
  have hFi : Function.Injective F := by
    rintro (b | d) (c | e) he
    · exact congrArg Sum.inl (hf he)
    · have hd : g e.val ∈ Set.range f := ⟨b, he⟩
      exact (e.property ((hsep e.val).mp hd)).elim
    · have hd : g d.val ∈ Set.range f := ⟨c, he.symm⟩
      exact (d.property ((hsep d.val).mp hd)).elim
    · exact congrArg Sum.inr (Subtype.ext (hnew d.val e.val d.property e.property he))
  let E := Equiv.ofBijective F ⟨hFi, hFq.surjective⟩
  refine { E with continuous_toFun := F.continuous, continuous_invFun := ?_ }
  apply hFq.continuous_iff.mpr
  change Continuous (E.symm ∘ F)
  have he : E.symm ∘ F = id := funext E.symm_apply_apply
  rw [he]
  exact continuous_id

@[simp] theorem attachmentQuotientHomeomorph_old (b : B) :
    attachmentQuotientHomeomorph r i f g hbd hf hsep hnew hq (old r i b) = f b :=
  desc_old r i f g hbd b

@[simp] theorem attachmentQuotientHomeomorph_cell (d : D) :
    attachmentQuotientHomeomorph r i f g hbd hf hsep hnew hq (cell r i d) = g d :=
  desc_cell r i f g hbd d

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped Topology

universe u
variable {A A' P P' D D' : Type u}
  [TopologicalSpace P] [TopologicalSpace P']
  [TopologicalSpace D] [TopologicalSpace D']
  (r : A → P) (i : A → D) (r' : A' → P') (i' : A' → D')
  (eA : A ≃ A') (eP : P ≃ₜ P') (eD : D ≃ₜ D')
  (hr : ∀ a, eP (r a) = r' (eA a))
  (hi : ∀ a, eD (i a) = i' (eA a))
  (hi' : Function.Injective i')

def attachmentDiagramMap : C(Space r i, Space r' i') :=
  desc r i
    ((⟨old r' i', old_continuous r' i'⟩ : C(P', Space r' i')).comp eP.toContinuousMap)
    ((⟨cell r' i', cell_continuous r' i'⟩ : C(D', Space r' i')).comp eD.toContinuousMap)
    (fun a => by
      change old r' i' (eP (r a)) = cell r' i' (eD (i a))
      rw [hr a, hi a, cell_boundary r' i' hi'])

@[simp] theorem attachmentDiagramMap_old (p : P) :
    attachmentDiagramMap r i r' i' eA eP eD hr hi hi' (old r i p) =
      old r' i' (eP p) := rfl

@[simp] theorem attachmentDiagramMap_cell (d : D) :
    attachmentDiagramMap r i r' i' eA eP eD hr hi hi' (cell r i d) =
      cell r' i' (eD d) := desc_cell ..

include hr in
theorem attachmentDiagram_inverse_old (a' : A') :
    eP.symm (r' a') = r (eA.symm a') := by
  apply eP.injective
  simp_all

include hi in
theorem attachmentDiagram_inverse_boundary (a' : A') :
    eD.symm (i' a') = i (eA.symm a') := by
  apply eD.injective
  simp_all

def attachmentDiagramHomeomorph (hi₀ : Function.Injective i) : Space r i ≃ₜ Space r' i' where
  toFun := attachmentDiagramMap r i r' i' eA eP eD hr hi hi'
  invFun := attachmentDiagramMap r' i' r i eA.symm eP.symm eD.symm
    (attachmentDiagram_inverse_old r r' eA eP hr)
    (attachmentDiagram_inverse_boundary i i' eA eD hi) hi₀
  left_inv z := by
    obtain ⟨z, rfl⟩ := quotientMap_surjective r i z
    cases z with
    | inl p =>
        change attachmentDiagramMap _ _ _ _ _ _ _ _ _ _
          (attachmentDiagramMap _ _ _ _ _ _ _ _ _ _ (old r i p)) = old r i p
        simp only [attachmentDiagramMap_old, Homeomorph.symm_apply_apply]
    | inr d =>
        change attachmentDiagramMap _ _ _ _ _ _ _ _ _ _
          (attachmentDiagramMap _ _ _ _ _ _ _ _ _ _ (cell r i d)) = cell r i d
        simp only [attachmentDiagramMap_cell, Homeomorph.symm_apply_apply]
  right_inv z := by
    obtain ⟨z, rfl⟩ := quotientMap_surjective r' i' z
    cases z with
    | inl p =>
        change attachmentDiagramMap _ _ _ _ _ _ _ _ _ _
          (attachmentDiagramMap _ _ _ _ _ _ _ _ _ _ (old r' i' p)) = old r' i' p
        simp only [attachmentDiagramMap_old, Homeomorph.apply_symm_apply]
    | inr d =>
        change attachmentDiagramMap _ _ _ _ _ _ _ _ _ _
          (attachmentDiagramMap _ _ _ _ _ _ _ _ _ _ (cell r' i' d)) = cell r' i' d
        simp only [attachmentDiagramMap_cell, Homeomorph.apply_symm_apply]
  continuous_toFun := (attachmentDiagramMap r i r' i' eA eP eD hr hi hi').continuous
  continuous_invFun := (attachmentDiagramMap r' i' r i eA.symm eP.symm eD.symm
    (attachmentDiagram_inverse_old r r' eA eP hr)
    (attachmentDiagram_inverse_boundary i i' eA eD hi) hi₀).continuous

@[simp] theorem attachmentDiagramHomeomorph_old (hi₀ : Function.Injective i) (p : P) :
    attachmentDiagramHomeomorph r i r' i' eA eP eD hr hi hi' hi₀ (old r i p) =
      old r' i' (eP p) := rfl

@[simp] theorem attachmentDiagramHomeomorph_cell (hi₀ : Function.Injective i) (d : D) :
    attachmentDiagramHomeomorph r i r' i' eA eP eD hr hi hi' hi₀ (cell r i d) =
      cell r' i' (eD d) := attachmentDiagramMap_cell r i r' i' eA eP eD hr hi hi' d

/-- Change each member of a topological sum by a specified homeomorphism. -/
def sigmaFiberHomeomorph {J : Type u} {X Y : J → Type u}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (e : ∀ j, X j ≃ₜ Y j) : (Σ j, X j) ≃ₜ (Σ j, Y j) where
  toFun z := ⟨z.1, e z.1 z.2⟩
  invFun z := ⟨z.1, (e z.1).symm z.2⟩
  left_inv := by rintro ⟨j, x⟩; simp only [Homeomorph.symm_apply_apply]
  right_inv := by rintro ⟨j, x⟩; simp only [Homeomorph.apply_symm_apply]
  continuous_toFun := continuous_sigma (fun j => continuous_sigmaMk.comp (e j).continuous)
  continuous_invFun := continuous_sigma (fun j => continuous_sigmaMk.comp (e j).symm.continuous)

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {P : Type} [PartialOrder P] {J : Type} (A : J → Set P)

def orderNervePieceMap (j : J) : C(orderNerveRealization (A j), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap (Subtype.val : A j → P) (fun _ _ h => h),
    (orderNerveRealizationMap (Subtype.val : A j → P) (fun _ _ h => h)).hom.continuous⟩

def orderNervePieceQuotient : C((Σ j, orderNerveRealization (A j)), orderNerveRealization P) :=
  ⟨fun x => orderNervePieceMap A x.1 x.2,
    continuous_sigma (fun j => (orderNervePieceMap A j).continuous)⟩

variable (hc : ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
  ∃ j, ∀ i, s.obj i ∈ A j)

include hc in
theorem orderNervePieceQuotient_surjective : Function.Surjective (orderNervePieceQuotient A) := by
  intro x
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨j, hj⟩ := hc n s
  exact ⟨⟨j, orderNerveRealizationSimplex (A j) (orderNerveSimplexSubtype (A j) s hj) z⟩,
    orderNerveRealizationSimplex_subtype (A j) s hj z⟩

include hc in
theorem orderNervePieceQuotient_isQuotientMap : IsQuotientMap (orderNervePieceQuotient A) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨orderNervePieceQuotient_surjective A hc, ?_⟩
  intro T
  constructor
  · exact fun hT => hT.preimage (orderNervePieceQuotient A).continuous
  · intro hT
    apply (orderNerveRealization_isClosed_iff P T).mpr
    intro n s
    obtain ⟨j, hj⟩ := hc n s
    have hjT := (isClosed_sigma_iff.mp hT) j
    have hz := hjT.preimage
      (orderNerveRealizationSimplex (A j) (orderNerveSimplexSubtype (A j) s hj)).hom.continuous
    convert hz using 1
    ext z
    exact iff_of_eq (congrArg (fun x => x ∈ T)
      (orderNerveRealizationSimplex_subtype (A j) s hj z).symm)

theorem orderNerveRealizationSupported_inter (B C : Set P) :
    orderNerveRealizationSupported P (B ∩ C) =
      orderNerveRealizationSupported P B ∩ orderNerveRealizationSupported P C := by
  ext x
  constructor
  · intro h
    exact ⟨fun p hp => h p (fun hpc => hp hpc.1),
      fun p hp => h p (fun hpc => hp hpc.2)⟩
  · rintro ⟨hB, hC⟩ p hp
    by_cases hb : p ∈ B
    · exact hC p (fun hc => hp ⟨hb, hc⟩)
    · exact hB p hb

theorem orderNerveRealizationSubtype_preimage_supported (B C : Set P) :
    (orderNerveRealizationMap (Subtype.val : B → P) (fun _ _ h => h)) ⁻¹'
        orderNerveRealizationSupported P C =
      orderNerveRealizationSupported B {b | b.val ∈ C} := by
  ext x
  constructor
  · intro hx b hb
    have h := hx b.val hb
    simpa only [orderNerveRealizationCoordinates_map_injective
      (Subtype.val : B → P) (fun _ _ h => h) Subtype.val_injective] using h
  · intro hx p hp
    by_cases hb : p ∈ B
    · have h := hx ⟨p, hb⟩ hp
      exact (orderNerveRealizationCoordinates_map_injective
        Subtype.val (fun _ _ h => h) Subtype.val_injective x ⟨p, hb⟩).trans h
    · exact orderNerveRealizationCoordinates_map_outside
        Subtype.val (fun _ _ h => h) x p (by
          simpa using hb)

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)

abbrev ConeAdjBase := coneAdjBaseSet (S := S)
abbrev ConeAdjDisk (j : J) := Set.Iic (ConeAdj.apex (S := S) j)
abbrev ConeAdjBoundary (j : J) :=
  setOf (fun x : ConeAdjDisk S j => x.val ∈ ConeAdjBase S)

/-- The old boundary of a cone is exactly its strict lower interval. -/
def coneAdjBoundaryOrderIso (j : J) : ConeAdjBoundary S j ≃o StrictBelow (ConeAdj.apex (S := S) j) where
  toFun x := ⟨x.val.val, lt_of_le_of_ne x.val.property (by
    intro h
    obtain ⟨p, hp⟩ := x.property
    exact Sum.inl_ne_inr (hp.trans h))⟩
  invFun x := ⟨⟨x.val, x.property.le⟩, by
    rcases x with ⟨q, hq⟩
    cases q with
    | inl p => exact ⟨p, rfl⟩
    | inr k =>
        have hk : k = j := hq.le
        subst k
        exact (lt_irrefl _ hq).elim⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := Iff.rfl

def coneAdjRealizationOld :
    C(orderNerveRealization (ConeAdjBase S), orderNerveRealization (ConeAdj S)) :=
  ⟨orderNerveRealizationMap Subtype.val (fun _ _ h => h),
    (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom.continuous⟩

def coneAdjRealizationCell :
    C((Σ j, orderNerveRealization (ConeAdjDisk S j)),
      orderNerveRealization (ConeAdj S)) :=
  ⟨fun z => orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2,
    continuous_sigma (fun _ =>
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom.continuous)⟩

def coneAdjRealizationBoundary :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      (Σ j, orderNerveRealization (ConeAdjDisk S j))) :=
  ⟨fun z => ⟨z.1, orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2⟩,
    continuous_sigma (fun j => (continuous_sigmaMk
      (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)).comp
      (orderNerveRealizationMap (Subtype.val : ConeAdjBoundary S j → ConeAdjDisk S j)
        (fun _ _ h => h)).hom.continuous)⟩

def coneAdjBoundaryToBase (j : J) : ConeAdjBoundary S j → ConeAdjBase S :=
  fun x => ⟨x.val.val, x.property⟩

theorem coneAdjBoundaryToBase_monotone (j : J) : Monotone (coneAdjBoundaryToBase S j) :=
  fun _ _ h => h

def coneAdjRealizationAttaching :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      orderNerveRealization (ConeAdjBase S)) :=
  ⟨fun z => orderNerveRealizationMap (coneAdjBoundaryToBase S z.1)
      (coneAdjBoundaryToBase_monotone S z.1) z.2,
    continuous_sigma (fun j =>
      (orderNerveRealizationMap (coneAdjBoundaryToBase S j)
        (coneAdjBoundaryToBase_monotone S j)).hom.continuous)⟩

theorem coneAdjRealization_boundary_commutes
    (z : Σ j, orderNerveRealization (ConeAdjBoundary S j)) :
    coneAdjRealizationOld S (coneAdjRealizationAttaching S z) =
      coneAdjRealizationCell S (coneAdjRealizationBoundary S z) := by
  change orderNerveRealizationMap Subtype.val (fun _ _ h => h)
      (orderNerveRealizationMap (coneAdjBoundaryToBase S z.1)
        (coneAdjBoundaryToBase_monotone S z.1) z.2) =
    orderNerveRealizationMap Subtype.val (fun _ _ h => h)
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2)
  rw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem coneAdjRealizationOld_range :
    Set.range (coneAdjRealizationOld S) =
      orderNerveRealizationSupported (ConeAdj S) (ConeAdjBase S) :=
  orderNerveRealizationSubtype_range (ConeAdjBase S)


theorem coneAdjRealizationCell_boundary_iff
    (z : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationCell S z ∈ Set.range (coneAdjRealizationOld S) ↔
      z ∈ Set.range (coneAdjRealizationBoundary S) := by
  rcases z with ⟨j, x⟩
  rw [coneAdjRealizationOld_range, (show ⟨j, x⟩ ∈
        Set.range (coneAdjRealizationBoundary S) ↔
      x ∈ orderNerveRealizationSupported (ConeAdjDisk S j) (ConeAdjBoundary S j) by
    change _ ↔ x ∈ (orderNerveRealizationSubcomplex (ConeAdjDisk S j)
      (ConeAdjBoundary S j) : Set (orderNerveRealization (ConeAdjDisk S j)))
    rw [← orderNerveRealizationSubtype_range (ConeAdjBoundary S j)]
    constructor
    · rintro ⟨⟨k, z⟩, h⟩
      have hk : k = j := congrArg Sigma.fst h
      subst k
      exact ⟨z, eq_of_heq (Sigma.mk.inj h).2⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨j, z⟩, rfl⟩)]
  exact Set.ext_iff.mp
    (orderNerveRealizationSubtype_preimage_supported (ConeAdjDisk S j) (ConeAdjBase S)) x

theorem coneAdj_disks_inter_subset_base {j k : J} (hjk : j ≠ k) :
    ConeAdjDisk S j ∩ ConeAdjDisk S k ⊆ ConeAdjBase S := by
  rintro (p | l) ⟨hj, hk⟩
  · exact ⟨p, rfl⟩
  · exact (hjk ((show l = j from hj).symm.trans (show l = k from hk))).elim


theorem coneAdjRealizationCell_injective_off_boundary
    (z t : Σ j, orderNerveRealization (ConeAdjDisk S j))
    (hz : z ∉ Set.range (coneAdjRealizationBoundary S))
    (_ht : t ∉ Set.range (coneAdjRealizationBoundary S))
    (he : coneAdjRealizationCell S z = coneAdjRealizationCell S t) : z = t := by
  rcases z with ⟨j, x⟩
  rcases t with ⟨k, y⟩
  by_cases hjk : j = k
  · subst k
    exact congrArg (Sigma.mk j) (orderNerveRealizationMap_injective
      Subtype.val (fun _ _ h => h)
      Subtype.val_injective he)
  · exact (hz ((coneAdjRealizationCell_boundary_iff S ⟨j, x⟩).mp
      (by
        rw [coneAdjRealizationOld_range]
        have hx : coneAdjRealizationCell S ⟨j, x⟩ ∈
            orderNerveRealizationSupported (ConeAdj S) (ConeAdjDisk S j) := by
          change _ ∈ (orderNerveRealizationSubcomplex (ConeAdj S) (ConeAdjDisk S j) :
            Set (orderNerveRealization (ConeAdj S)))
          rw [← orderNerveRealizationSubtype_range (ConeAdjDisk S j)]
          exact ⟨x, rfl⟩
        have hy : coneAdjRealizationCell S ⟨j, x⟩ ∈
            orderNerveRealizationSupported (ConeAdj S) (ConeAdjDisk S k) := by
          change _ ∈ (orderNerveRealizationSubcomplex (ConeAdj S) (ConeAdjDisk S k) :
            Set (orderNerveRealization (ConeAdj S)))
          rw [he, ← orderNerveRealizationSubtype_range (ConeAdjDisk S k)]
          exact ⟨y, rfl⟩
        intro p hp
        by_cases hpj : p ∈ ConeAdjDisk S j
        · apply hy p
          intro hpk
          exact hp (coneAdj_disks_inter_subset_base S hjk ⟨hpj, hpk⟩)
        · exact hx p hpj))).elim

/-- Every simplex is entirely old or is contained in one cone lower ideal. -/
theorem coneAdj_simplex_in_piece (n : SimplexCategory)
    (s : (nerve (ConeAdj S)).obj (Opposite.op n)) :
    (∀ i, s.obj i ∈ ConeAdjBase S) ∨
      ∃ j, ∀ i, s.obj i ∈ ConeAdjDisk S j := by
  have hlast (i : Fin (n.len + 1)) : s.obj i ≤ s.obj (Fin.last n.len) :=
    leOfHom (s.map (homOfLE (Fin.le_last i)))
  cases he : s.obj (Fin.last n.len) with
  | inl p =>
      exact Or.inl (fun i => coneAdjBaseSet_down_closed
        (show s.obj (Fin.last n.len) ∈ ConeAdjBase S by rw [he]; exact ⟨p, rfl⟩)
        (hlast i))
  | inr j =>
      exact Or.inr ⟨j, fun i => by
        change s.obj i ≤ ConeAdj.apex j
        simpa only [he, ConeAdj.apex] using hlast i⟩

theorem coneAdjRealization_piece_isQuotientMap :
    IsQuotientMap (Sum.elim (coneAdjRealizationOld S) (coneAdjRealizationCell S)) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective (ConeAdj S) x
    rcases coneAdj_simplex_in_piece S n s with h | ⟨j, h⟩
    · exact ⟨Sum.inl (orderNerveRealizationSimplex (ConeAdjBase S)
        (orderNerveSimplexSubtype (ConeAdjBase S) s h) z),
        orderNerveRealizationSimplex_subtype (ConeAdjBase S) s h z⟩
    · exact ⟨Sum.inr ⟨j, orderNerveRealizationSimplex (ConeAdjDisk S j)
        (orderNerveSimplexSubtype (ConeAdjDisk S j) s h) z⟩,
        orderNerveRealizationSimplex_subtype (ConeAdjDisk S j) s h z⟩
  · intro T
    constructor
    · intro hT
      exact hT.preimage ((coneAdjRealizationOld S).continuous.sumElim
        (coneAdjRealizationCell S).continuous)
    · intro hT
      apply (orderNerveRealization_isClosed_iff (ConeAdj S) T).mpr
      intro n s
      rcases coneAdj_simplex_in_piece S n s with h | ⟨j, h⟩
      · have hb := hT.preimage continuous_inl
        have ht := hb.preimage
          (orderNerveRealizationSimplex (ConeAdjBase S)
            (orderNerveSimplexSubtype (ConeAdjBase S) s h)).hom.continuous
        convert ht using 1
        ext z
        exact iff_of_eq (congrArg (fun y => y ∈ T)
          (orderNerveRealizationSimplex_subtype (ConeAdjBase S) s h z).symm)
      · have hc := hT.preimage (continuous_inr.comp
          (continuous_sigmaMk (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)))
        have ht := hc.preimage
          (orderNerveRealizationSimplex (ConeAdjDisk S j)
            (orderNerveSimplexSubtype (ConeAdjDisk S j) s h)).hom.continuous
        convert ht using 1
        ext z
        exact iff_of_eq (congrArg (fun y => y ∈ T)
          (orderNerveRealizationSimplex_subtype (ConeAdjDisk S j) s h z).symm)

/-- The topological attachment is the actual nerve realization, with
the actual old inclusion and the actual cone inclusions. -/
def coneAdjRealizationAttachmentHomeomorph :
    RelativeAttachment.Space (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
      ≃ₜ orderNerveRealization (ConeAdj S) :=
  RelativeAttachment.attachmentQuotientHomeomorph
    (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
    (coneAdjRealizationOld S) (coneAdjRealizationCell S)
    (coneAdjRealization_boundary_commutes S)
    (orderNerveRealizationMap_injective Subtype.val (fun _ _ h => h) Subtype.val_injective)
    (coneAdjRealizationCell_boundary_iff S)
    (coneAdjRealizationCell_injective_off_boundary S)
    (coneAdjRealization_piece_isQuotientMap S)

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_old
    (x : orderNerveRealization (ConeAdjBase S)) :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.old (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationOld S x :=
  RelativeAttachment.attachmentQuotientHomeomorph_old _ _ _ _ _ _ _ _ _ x

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_cell
    (x : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.cell (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationCell S x :=
  RelativeAttachment.attachmentQuotientHomeomorph_cell _ _ _ _ _ _ _ _ _ x

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open scoped Topology
open RelativeAttachment

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)
  (C : J → Type) [∀ j, PartialOrder (C j)] [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)]
  (e : ∀ j, C j ≃o StrictBelow (ConeAdj.apex (S := S) j))
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (b : ∀ j, orderNerveRealization (C j) ≃ₜ UnitBoundary E)

def coneAdjLinkOrderIso (j : J) : C j ≃o ConeAdjBoundary S j :=
  (e j).trans (coneAdjBoundaryOrderIso S j).symm

def coneAdjLinkRealizationHomeomorph (j : J) :
    orderNerveRealization (C j) ≃ₜ orderNerveRealization (ConeAdjBoundary S j) :=
  orderNerveRealizationOrderIso (coneAdjLinkOrderIso S C e j)

def coneAdjSphereHomeomorph (j : J) :
    orderNerveRealization (ConeAdjBoundary S j) ≃ₜ UnitBoundary E :=
  (coneAdjLinkRealizationHomeomorph S C e j).symm.trans (b j)

def coneAdjBallHomeomorph (j : J) :
    orderNerveRealization (ConeAdjDisk S j) ≃ₜ ClosedUnitBall E :=
  lowerConeBallHomeomorph (ConeAdj.apex j) (e j) (b j)

omit [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)] in
theorem coneAdjLinkRealization_boundary (j : J) (x : orderNerveRealization (C j)) :
    orderNerveRealizationMap (Subtype.val : ConeAdjBoundary S j → ConeAdjDisk S j)
        (fun _ _ h => h) (coneAdjLinkRealizationHomeomorph S C e j x) =
      orderNerveRealizationMap (lowerConeBoundary (ConeAdj.apex j) (e j))
        (lowerConeBoundary (ConeAdj.apex j) (e j)).monotone x := by
  erw [orderNerveRealizationMap_comp]
  rfl


def coneAdjSphereFamilyHomeomorph :
    (Σ j, orderNerveRealization (ConeAdjBoundary S j)) ≃ₜ BoundaryFamily J E :=
  sigmaFiberHomeomorph (coneAdjSphereHomeomorph S C e b)

def coneAdjBallFamilyHomeomorph :
    (Σ j, orderNerveRealization (ConeAdjDisk S j)) ≃ₜ DiskFamily J E :=
  sigmaFiberHomeomorph (coneAdjBallHomeomorph S C e b)

def coneAdjDiskAttaching : C(BoundaryFamily J E, orderNerveRealization (ConeAdjBase S)) :=
  (coneAdjRealizationAttaching S).comp (coneAdjSphereFamilyHomeomorph S C e b).symm.toContinuousMap

omit [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)] [NormedSpace ℝ E] [ProperSpace E] in
theorem coneAdjDiskAttaching_link (j : J) (x : orderNerveRealization (C j)) :
    coneAdjDiskAttaching S C e b ⟨j, b j x⟩ =
      coneAdjRealizationAttaching S ⟨j, coneAdjLinkRealizationHomeomorph S C e j x⟩ := by
  have hs : coneAdjSphereFamilyHomeomorph S C e b
      ⟨j, coneAdjLinkRealizationHomeomorph S C e j x⟩ = ⟨j, b j x⟩ := by
    change (⟨j, b j ((coneAdjLinkRealizationHomeomorph S C e j).symm
      (coneAdjLinkRealizationHomeomorph S C e j x))⟩ : BoundaryFamily J E) = _
    erw [Homeomorph.symm_apply_apply]
  change coneAdjRealizationAttaching S
    ((coneAdjSphereFamilyHomeomorph S C e b).symm ⟨j, b j x⟩) = _
  erw [← hs, Homeomorph.symm_apply_apply]

theorem coneAdjRealizationBoundary_injective : Function.Injective (coneAdjRealizationBoundary S) := by
  rintro ⟨j, x⟩ ⟨k, y⟩ h
  have hk : j = k := congrArg Sigma.fst h
  subst k
  exact congrArg (Sigma.mk j) (orderNerveRealizationMap_injective
    Subtype.val (fun _ _ h => h)
    Subtype.val_injective (eq_of_heq (Sigma.mk.inj h).2))

def coneAdjAttachmentDiskHomeomorph :
    RelativeAttachment.Space (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
      ≃ₜ DiskAttachment (coneAdjDiskAttaching S C e b) :=
  attachmentDiagramHomeomorph
    (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
    (coneAdjDiskAttaching S C e b) (boundaryFamilyInclusion J E)
    (coneAdjSphereFamilyHomeomorph S C e b).toEquiv (Homeomorph.refl _)
    (coneAdjBallFamilyHomeomorph S C e b)
    (fun a => by
      change coneAdjRealizationAttaching S a = coneAdjRealizationAttaching S
        ((coneAdjSphereFamilyHomeomorph S C e b).symm
          (coneAdjSphereFamilyHomeomorph S C e b a))
      rw (config := { transparency := .default }) [Homeomorph.symm_apply_apply])
    (fun a => by
      rcases a with ⟨j, x⟩
      exact congrArg (Sigma.mk j) (by
        have h := lowerConeBallHomeomorph_boundary (ConeAdj.apex (S := S) j) (e j) (b j)
          ((coneAdjLinkRealizationHomeomorph S C e j).symm x)
        erw [← coneAdjLinkRealization_boundary S C e j, Homeomorph.apply_symm_apply] at h
        exact h))
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (coneAdjRealizationBoundary_injective S)

/-- The realization is a genuine family of disks attached to its old part. -/
def coneAdjRealizationDiskHomeomorph :
    orderNerveRealization (ConeAdj S) ≃ₜ DiskAttachment (coneAdjDiskAttaching S C e b) :=
  (coneAdjRealizationAttachmentHomeomorph S).symm.trans
    (coneAdjAttachmentDiskHomeomorph S C e b)

@[simp] theorem coneAdjRealizationDiskHomeomorph_old
    (x : orderNerveRealization (ConeAdjBase S)) :
    coneAdjRealizationDiskHomeomorph S C e b (coneAdjRealizationOld S x) =
      old (coneAdjDiskAttaching S C e b) (boundaryFamilyInclusion J E) x := by
  erw [← coneAdjRealizationAttachmentHomeomorph_old]
  change coneAdjAttachmentDiskHomeomorph S C e b
    ((coneAdjRealizationAttachmentHomeomorph S).symm
      (coneAdjRealizationAttachmentHomeomorph S _)) = _
  erw [Homeomorph.symm_apply_apply]
  exact attachmentDiagramHomeomorph_old ..

@[simp] theorem coneAdjRealizationDiskHomeomorph_cell
    (z : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationDiskHomeomorph S C e b (coneAdjRealizationCell S z) =
      cell (coneAdjDiskAttaching S C e b) (boundaryFamilyInclusion J E)
        (coneAdjBallFamilyHomeomorph S C e b z) := by
  erw [← coneAdjRealizationAttachmentHomeomorph_cell]
  change coneAdjAttachmentDiskHomeomorph S C e b
    ((coneAdjRealizationAttachmentHomeomorph S).symm
      (coneAdjRealizationAttachmentHomeomorph S _)) = _
  erw [Homeomorph.symm_apply_apply]
  exact attachmentDiagramHomeomorph_cell ..

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

local instance relatorCircleFintype (j : J) : Fintype (RelatorCircle w j) := Fintype.ofFinite _


def presOldRoseHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (ConeAdjBase (circSet w)))
      (orderNerveRealization (Rose A)) :=
  (orderNerveRealizationOrderIso (coneAdjBaseOrderIso (S := circSet w))).toHomotopyEquiv.trans (presCylinderRealizationHomotopyEquiv w)

def presCircleWordMap (j : J) :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (Rose A)) :=
  ⟨orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h),
    (orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h)).hom.continuous⟩


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (b : ∀ j, orderNerveRealization (RelatorCircle w j) ≃ₜ UnitBoundary E)

def presCylinderDiskAttaching :
    C(BoundaryFamily J E, orderNerveRealization (ConeAdjBase (circSet w))) :=
  coneAdjDiskAttaching (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) b

def presRoseDiskAttaching : C(BoundaryFamily J E, orderNerveRealization (Rose A)) :=
  (presOldRoseHomotopyEquiv w).toFun.comp (presCylinderDiskAttaching w b)

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    presRoseDiskAttaching w b ⟨j, b j x⟩ = presCircleWordMap w j x := by
  change presOldRoseHomotopyEquiv w
    (coneAdjDiskAttaching (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) b ⟨j, b j x⟩) = _
  erw [coneAdjDiskAttaching_link]
  exact (by
    have hp c :
        coneAdjBaseOrderIso (coneAdjBoundaryToBase (circSet w) j
          (coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j c)) =
        cylOuter (aHom w) c.val := by
      apply ConeAdj.inc_injective
      exact Classical.choose_spec
        (coneAdjBoundaryToBase (circSet w) j
          (coneAdjLinkOrderIso (circSet w) (RelatorCircle w)
            (relatorCircleOrderIso w) j c)).property
    erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp,
      orderNerveRealizationMap_comp]
    have hf : (cylRetr (aHom w) ∘ coneAdjBaseOrderIso ∘ coneAdjBoundaryToBase (circSet w) j ∘
        coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j) =
          (fun c : RelatorCircle w j => aFun w c.val) := by
      funext c
      simp only [Function.comp_apply, hp]
      rfl
    exact orderNerveRealizationMap_congr _ _ hf x)

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_apply (z : BoundaryFamily J E) :
    presRoseDiskAttaching w b z = presCircleWordMap w z.1 ((b z.1).symm z.2) := by
  rcases z with ⟨j, y⟩
  simpa using
    presRoseDiskAttaching_link w b j ((b j).symm y)

/-- Both the cone attachment and the mapping-cylinder collapse are actual
maps; this equivalence has no unproved CW-model comparison as an input. -/
def presRealizationRoseDiskHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w))
      (DiskAttachment (presRoseDiskAttaching w b)) := by
  letI : ∀ j, Nonempty (RelatorCircle w j) := fun j => relatorCircle_nonempty w j (hw j)
  exact (coneAdjRealizationDiskHomeomorph (circSet w) (RelatorCircle w)
    (relatorCircleOrderIso w) b).toHomotopyEquiv.trans
      (diskAttachmentBaseChangeHomotopyEquiv (presCylinderDiskAttaching w b)
        (presOldRoseHomotopyEquiv w))

@[simp] theorem presRealizationRoseDiskHomotopyEquiv_old
    (x : orderNerveRealization (ConeAdjBase (circSet w))) :
    presRealizationRoseDiskHomotopyEquiv w hw b (coneAdjRealizationOld (circSet w) x) =
      old (presRoseDiskAttaching w b) (boundaryFamilyInclusion J E)
        (presOldRoseHomotopyEquiv w x) := by
  letI : ∀ j, Nonempty (RelatorCircle w j) := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ (coneAdjRealizationOld _ x)) = _
  erw [coneAdjRealizationDiskHomeomorph_old, diskAttachmentBaseChangeHomotopyEquiv_old]
  rfl

end FiniteChains.PresModel

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

def relatorCircleMap (j : J) : RelatorCircle w j ↪o RelatorCircle v (h.cell j) where
  toFun x := ⟨h.circleFun x.val, by
    constructor
    · exact congrArg h.cell x.property.1
    · change x.val.2.1 < (v (h.cell j)).length
      rw (config := { transparency := .default }) [h.word_length]
      exact x.property.2⟩
  inj' := fun _ _ he => Subtype.ext (h.circleFun_injective (congrArg Subtype.val he))
  map_rel_iff' := h.circleFun_le_iff _ _

@[simp] theorem relatorCircleMap_val (j : J) (x : RelatorCircle w j) :
    (h.relatorCircleMap j x).val = h.circleFun x.val := rfl

@[simp] theorem relatorCircleMap_position (j : J) (x : RelatorCircle w j) :
    (h.relatorCircleMap j x).val.2 = x.val.2 := rfl

@[simp] theorem relatorCircleMap_index (j : J) (x : RelatorCircle w j) :
    (relatorCircleIndexEquiv v (h.cell j) (h.relatorCircleMap j x)).val =
      (relatorCircleIndexEquiv w j x).val := rfl

theorem relatorCircleMap_surjective (j : J) : Function.Surjective (h.relatorCircleMap j) := by
  intro y
  let k : Fin (w j).length := ⟨y.val.2.1, by
    erw [← h.word_length j]
    exact y.property.2⟩
  refine ⟨relatorCirclePoint w j k y.val.2.2, ?_⟩
  apply Subtype.ext
  exact Prod.ext y.property.1.symm rfl

def relatorCircleOrderIso (j : J) : RelatorCircle w j ≃o RelatorCircle v (h.cell j) where
  toEquiv := Equiv.ofBijective (h.relatorCircleMap j)
    ⟨(h.relatorCircleMap j).injective, h.relatorCircleMap_surjective j⟩
  map_rel_iff' := (h.relatorCircleMap j).le_iff_le

def relatorCircleRealizationMap (j : J) :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (RelatorCircle v (h.cell j))) :=
  ⟨orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone,
    (orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone).hom.continuous⟩

theorem presCircleWordMap_natural (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (presCircleWordMap w j x) =
      presCircleWordMap v (h.cell j) (h.relatorCircleRealizationMap j x) := by
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf : (h.roseMap ∘ (fun c : RelatorCircle w j => aFun w c.val)) =
      ((fun c : RelatorCircle v (h.cell j) => aFun v c.val) ∘ h.relatorCircleMap j) := by
    funext c
    exact (h.attaching_map c.val).symm
  exact orderNerveRealizationMap_congr _ _ hf x

end FiniteChains.PresModel.PresWordEmbedding

section
open scoped Classical unitInterval
open Set Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment

theorem arcConcat_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (n : ℕ) (v : Fin (n + 2) → X) (w : Fin (n + 2) → Y)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ))
    (G : ∀ i : Fin (n + 1), Path (w i.castSucc) (w i.succ))
    (h : ∀ i t, f (F i t) = G i t) (t : I) :
    f (arcConcat n v F t) = arcConcat n w G t := by
  induction n generalizing t with
  | zero => exact h 0 t
  | succ n ih =>
    simp only [arcConcat, Path.trans_apply]
    split_ifs
    · exact ih (v ∘ Fin.castSucc) (w ∘ Fin.castSucc)
        (fun i => F i.castSucc) (fun i => G i.castSucc)
        (fun i s => h i.castSucc s) _
    · exact h (Fin.last (n + 1)) _

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open RelativeAttachment

theorem orderNerveComparablePath_natural_bijective {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hb : Function.Bijective f) {a b : P} (h : a ≤ b ∨ b ≤ a)
    (h' : f a ≤ f b ∨ f b ≤ f a) (t : I) :
    orderNerveRealizationMap f hf (orderNerveComparablePath h t) =
      orderNerveComparablePath h' t := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  obtain ⟨p, rfl⟩ := hb.2 q
  rw [orderNerveRealizationCoordinates_map_injective f hf hb.1]
  simp only [orderNerveComparablePath_coordinates, hb.1.eq_iff]

namespace FinitePosetCycle

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {n : ℕ}
  (C : FinitePosetCycle P n) (D : FinitePosetCycle Q n)
  (f : P → Q) (hf : Monotone f) (hv : ∀ i, f (C.vertex i) = D.vertex i)

include hv in
theorem vertex_map_bijective : Function.Bijective f := by
  constructor
  · intro a b hab
    obtain ⟨i, rfl⟩ := C.vertex.surjective a
    obtain ⟨j, rfl⟩ := C.vertex.surjective b
    rw [hv, hv] at hab
    exact congrArg C.vertex (D.vertex.injective hab)
  · intro q
    obtain ⟨i, rfl⟩ := D.vertex.surjective q
    exact ⟨C.vertex i, hv i⟩

include hv in
theorem edge_natural (i : Fin (n + 1)) (t : I) :
    orderNerveRealizationMap f hf (C.edge i t) = D.edge i t := by
  have h'  :=
    (C.consecutive i).imp (fun h => hf h) (fun h => hf h)
  have h := orderNerveComparablePath_natural_bijective f hf
    (C.vertex_map_bijective D f hv) (C.consecutive i) h' t
  apply h.trans
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp only [edge, orderNerveComparablePath_coordinates, hv]

include hv in
theorem lastEdge_natural (t : I) :
    orderNerveRealizationMap f hf (C.lastEdge t) = D.lastEdge t := by
  have h'  :=
    C.closing.imp (fun h => hf h) (fun h => hf h)
  have h := orderNerveComparablePath_natural_bijective f hf
    (C.vertex_map_bijective D f hv) C.closing h' t
  apply h.trans
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp only [lastEdge, orderNerveComparablePath_coordinates, hv]

include hv in
theorem traversal_natural (t : I) :
    orderNerveRealizationMap f hf (C.traversal t) = D.traversal t := by
  have hp := arcConcat_natural (orderNerveRealizationMap f hf) n
    (orderNerveRealizationVertex ∘ C.vertex) (orderNerveRealizationVertex ∘ D.vertex)
    C.edge D.edge (C.edge_natural D f hf hv)
  simp only [traversal, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact C.lastEdge_natural D f hf hv _

theorem boundaryHomeomorph_traversal (t : I) :
    C.boundaryHomeomorph (C.traversal t) =
      unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t) := by
  apply C.boundaryHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  change C.traversal t = simpleLoopBoundaryHomeomorph C.traversal
    C.traversal_surjective C.traversal_fiber
      (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t))
  simp only [simpleLoopBoundaryHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, simpleLoopSquareHomeomorph_traversal]

include hv in
theorem boundaryHomeomorph_natural (x : orderNerveRealization P) :
    D.boundaryHomeomorph (orderNerveRealizationMap f hf x) = C.boundaryHomeomorph x := by
  obtain ⟨t, rfl⟩ := C.traversal_surjective x
  rw [C.traversal_natural D f hf hv, D.boundaryHomeomorph_traversal,
    C.boundaryHomeomorph_traversal]

theorem boundaryHomeomorph_natural_cast {m : ℕ} (D' : FinitePosetCycle Q m)
    (hnm : n = m) (f' : P → Q) (hf' : Monotone f')
    (hv' : ∀ i, f' (C.vertex i) = D'.vertex (Fin.cast (congrArg (fun k => k + 2) hnm) i))
    (x : orderNerveRealization P) :
    D'.boundaryHomeomorph (orderNerveRealizationMap f' hf' x) = C.boundaryHomeomorph x := by
  subst m
  exact C.boundaryHomeomorph_natural D' f' hf' hv' x

end FinitePosetCycle
end FiniteChains.Comb
end

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

theorem relatorCircleSize_eq (j : J) :
    relatorCircleSize w j = relatorCircleSize v (h.cell j) := by
  simp only [relatorCircleSize, h.word_length]

theorem relatorCircleEnumeration_natural (j : J)
    (hw : 0 < (w j).length) (hv : 0 < (v (h.cell j)).length)
    (i : Fin (relatorCircleSize w j + 2)) :
    h.relatorCircleMap j (relatorCircleEnumeration w j hw i) =
      relatorCircleEnumeration v (h.cell j) hv
        (Fin.cast (congrArg (fun n => n + 2) (h.relatorCircleSize_eq j)) i) := rfl

/-- The actual boundary coordinates of every retained cell commute with
the literal presentation inclusion. -/
theorem relatorCircleBoundaryHomeomorph_natural (j : J)
    (hw : 0 < (w j).length) (hv : 0 < (v (h.cell j)).length)
    (x : orderNerveRealization (RelatorCircle w j)) :
    relatorCircleBoundaryHomeomorph v (h.cell j) hv
      (h.relatorCircleRealizationMap j x) =
        relatorCircleBoundaryHomeomorph w j hw x := by
  exact (relatorCircleCycle w j hw).boundaryHomeomorph_natural_cast
    (relatorCircleCycle v (h.cell j) hv) (h.relatorCircleSize_eq j)
    (h.relatorCircleMap j) (h.relatorCircleMap j).monotone
    (h.relatorCircleEnumeration_natural j hw hv) x

theorem relatorCircleBoundaryHomeomorph_symm_natural (j : J)
    (hw : 0 < (w j).length) (hv : 0 < (v (h.cell j)).length)
    (z : FiniteChains.RelativeAttachment.UnitBoundary (Fin 2 → ℝ)) :
    h.relatorCircleRealizationMap j ((relatorCircleBoundaryHomeomorph w j hw).symm z) =
      (relatorCircleBoundaryHomeomorph v (h.cell j) hv).symm z := by
  apply (relatorCircleBoundaryHomeomorph v (h.cell j) hv).injective
  rw [h.relatorCircleBoundaryHomeomorph_natural j hw hv, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.Comb
open RelativeAttachment
open scoped Classical unitInterval

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q)

theorem orderNerveRadialCone_natural (r : I) (x : orderNerveRealization P) :
    orderNerveRealizationOrderIso e.withTopCongr (orderNerveRadialCone P (r, x)) =
      orderNerveRadialCone Q (r, orderNerveRealizationOrderIso e x) := by
  apply orderNerveRealizationCoordinates_injective (WithTop Q)
  funext q
  obtain ⟨p, rfl⟩ := e.withTopCongr.surjective q
  change orderNerveRealizationCoordinates (WithTop Q)
      (orderNerveRealizationMap e.withTopCongr e.withTopCongr.monotone
        (orderNerveRadialCone P (r, x))) (e.withTopCongr p) = _
  rw [orderNerveRealizationCoordinates_map_injective _ _ e.withTopCongr.injective]
  induction p using WithTop.recTopCoe with
  | top => simp
  | coe p =>
      change orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) p =
        orderNerveRealizationCoordinates (WithTop Q)
          (orderNerveRadialCone Q (r, orderNerveRealizationOrderIso e x)) (e p)
      rw [orderNerveRadialCone_coordinate, orderNerveRadialCone_coordinate]
      exact congrArg ((r : ℝ) * ·)
        (orderNerveRealizationCoordinates_map_injective e e.monotone e.injective x p).symm

variable [Fintype P] [Nonempty P] [Fintype Q] [Nonempty Q]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (bP : orderNerveRealization P ≃ₜ UnitBoundary E)
  (bQ : orderNerveRealization Q ≃ₜ UnitBoundary E)
  (hb : ∀ x, bQ (orderNerveRealizationOrderIso e x) = bP x)

include hb in
theorem orderNerveWithTopBallHomeomorph_natural (x : orderNerveRealization (WithTop P)) :
    orderNerveWithTopBallHomeomorph bQ (orderNerveRealizationOrderIso e.withTopCongr x) =
      orderNerveWithTopBallHomeomorph bP x := by
  obtain ⟨⟨r, y⟩, rfl⟩ := orderNerveRadialCone_surjective P x
  rw [orderNerveRadialCone_natural, orderNerveWithTopBallHomeomorph_radial,
    orderNerveWithTopBallHomeomorph_radial, hb]

end FiniteChains.Comb

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb RelativeAttachment
open scoped Classical

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v) (j : J)

def coneLowerMap : Set.Iic (apexOf w j) ↪o Set.Iic (apexOf v (h.cell j)) where
  toFun x := ⟨h.posMap x.val, h.posMap.monotone x.property⟩
  inj' := fun _ _ he => Subtype.ext (h.posMap.injective (congrArg Subtype.val he))
  map_rel_iff' := h.posMap.le_iff_le

theorem coneLowerMap_withTop (p : WithTop (RelatorCircle w j)) :
    h.coneLowerMap j (lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j) p) =
      lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j))
        ((h.relatorCircleOrderIso j).withTopCongr p) := by
  induction p using WithTop.recTopCoe with
  | top => rfl
  | coe p => rfl

theorem coneLowerMap_realization_withTop (x : orderNerveRealization (WithTop (RelatorCircle w j))) :
    orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone
      (orderNerveRealizationOrderIso
        (lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j)) x) =
      orderNerveRealizationOrderIso
        (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)))
        (orderNerveRealizationOrderIso (h.relatorCircleOrderIso j).withTopCongr x) := by
  change orderNerveRealizationMap _ _ (orderNerveRealizationMap _ _ x) =
    orderNerveRealizationMap _ _ (orderNerveRealizationMap _ _ x)
  rw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf  :=
    funext (h.coneLowerMap_withTop j)
  exact orderNerveRealizationMap_congr _ _ hf x

variable (hn : 0 < (w j).length) (hn' : 0 < (v (h.cell j)).length)

local instance sourceCircleFintype : Fintype (RelatorCircle w j) := Fintype.ofFinite _
local instance targetCircleFintype : Fintype (RelatorCircle v (h.cell j)) := Fintype.ofFinite _

theorem presConeBallHomeomorph_natural_of_boundary
    (hb : ∀ x, relatorCircleBoundaryHomeomorph v (h.cell j) hn'
      (h.relatorCircleRealizationMap j x) = relatorCircleBoundaryHomeomorph w j hn x)
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    presConeBallHomeomorph v (h.cell j) hn'
      (orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone x) =
      presConeBallHomeomorph w j hn x := by
  letI := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  letI :=
    relatorCircle_nonempty v (h.cell j) (List.ne_nil_of_length_pos hn')
  let e₀ := orderNerveRealizationOrderIso
    (lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j))
  obtain ⟨y, rfl⟩ := e₀.surjective x
  rw [coneLowerMap_realization_withTop]
  change orderNerveWithTopBallHomeomorph (relatorCircleBoundaryHomeomorph v (h.cell j) hn')
      ((orderNerveRealizationOrderIso
        (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)))).symm
        (orderNerveRealizationOrderIso
          (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)))
          (orderNerveRealizationOrderIso (h.relatorCircleOrderIso j).withTopCongr y))) =
    orderNerveWithTopBallHomeomorph (relatorCircleBoundaryHomeomorph w j hn) (e₀.symm (e₀ y))
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  exact orderNerveWithTopBallHomeomorph_natural (h.relatorCircleOrderIso j)
    (relatorCircleBoundaryHomeomorph w j hn) (relatorCircleBoundaryHomeomorph v (h.cell j) hn') hb y

theorem presConeBallHomeomorph_natural
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    presConeBallHomeomorph v (h.cell j) hn'
      (orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone x) =
      presConeBallHomeomorph w j hn x :=
  h.presConeBallHomeomorph_natural_of_boundary j hn hn'
    (h.relatorCircleBoundaryHomeomorph_natural j hn hn') x

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

def presCircleBoundaryHomeomorph (j : J) :
    orderNerveRealization (RelatorCircle w j) ≃ₜ UnitBoundary (Fin 2 → ℝ) :=
  relatorCircleBoundaryHomeomorph w j (List.length_pos_of_ne_nil (hw j))

def actualPresWordAttaching :
    C(BoundaryFamily J (Fin 2 → ℝ), orderNerveRealization (Rose A)) :=
  presRoseDiskAttaching w (presCircleBoundaryHomeomorph w hw)

abbrev ActualPresWordDisks := DiskAttachment (actualPresWordAttaching w hw)

def actualPresWordDiskComparison :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w)) (ActualPresWordDisks w hw) :=
  presRealizationRoseDiskHomotopyEquiv w hw (presCircleBoundaryHomeomorph w hw)

theorem actualPresWordAttaching_apply (z : BoundaryFamily J (Fin 2 → ℝ)) :
    actualPresWordAttaching w hw z =
      presCircleWordMap w z.1 ((presCircleBoundaryHomeomorph w hw z.1).symm z.2) :=
  presRoseDiskAttaching_apply w (presCircleBoundaryHomeomorph w hw) z

theorem actualPresWordAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    actualPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩ =
      presCircleWordMap w j x :=
  presRoseDiskAttaching_link w (presCircleBoundaryHomeomorph w hw) j x

@[simp] theorem actualPresWordDiskComparison_old
    (x : orderNerveRealization (ConeAdjBase (circSet w))) :
    actualPresWordDiskComparison w hw (coneAdjRealizationOld (circSet w) x) =
      old (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
        (presOldRoseHomotopyEquiv w x) :=
  presRealizationRoseDiskHomotopyEquiv_old w hw (presCircleBoundaryHomeomorph w hw) x

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

def classicalPresWordAttaching :
    C(BoundaryFamily J (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (orderRoseRealizationHomeomorph A).toContinuousMap.comp (actualPresWordAttaching w hw)

abbrev ClassicalPresWordDisks := DiskAttachment (classicalPresWordAttaching w hw)

def presClassicalDiskComparison :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w)) (ClassicalPresWordDisks w hw) :=
  (actualPresWordDiskComparison w hw).trans
    (diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching w hw)
      (orderRoseRealizationHomeomorph A).toHomotopyEquiv)

theorem classicalPresWordAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    classicalPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩ =
      orderRoseRealizationHomeomorph A (presCircleWordMap w j x) := by simp_all [actualPresWordAttaching_link, classicalPresWordAttaching]


end FiniteChains.PresModel

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb RelativeAttachment ClassicalGraphModel
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

theorem actualPresWordAttaching_natural (z : BoundaryFamily J (Fin 2 → ℝ)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (actualPresWordAttaching w hw z) =
      actualPresWordAttaching v hv ⟨h.cell z.1, z.2⟩ := by
  rcases z with ⟨j, a⟩
  rw [actualPresWordAttaching_apply, actualPresWordAttaching_apply]
  have hs := h.relatorCircleBoundaryHomeomorph_symm_natural j
    (List.length_pos_of_ne_nil (hw j)) (List.length_pos_of_ne_nil (hv (h.cell j))) a
  change h.relatorCircleRealizationMap j ((presCircleBoundaryHomeomorph w hw j).symm a) =
    (presCircleBoundaryHomeomorph v hv (h.cell j)).symm a at hs
  rw [← hs]
  exact h.presCircleWordMap_natural j _

theorem classicalPresWordAttaching_natural (z : BoundaryFamily J (Fin 2 → ℝ)) :
    diskRoseMap h.gen (classicalPresWordAttaching w hw z) =
      classicalPresWordAttaching v hv ⟨h.cell z.1, z.2⟩ := by
  change diskRoseMap h.gen (orderRoseRealizationHomeomorph A (actualPresWordAttaching w hw z)) =
    orderRoseRealizationHomeomorph B (actualPresWordAttaching v hv ⟨h.cell z.1, z.2⟩)
  rw [← orderRoseRealizationHomeomorph_natural h, h.actualPresWordAttaching_natural hw hv z]

def orderRoseMapContinuous : C(orderNerveRealization (PresModel.Rose A),
    orderNerveRealization (PresModel.Rose B)) :=
  (orderNerveRealizationMap h.roseMap h.roseMap.monotone).hom

def wordDiskCellMap : C(DiskFamily J (Fin 2 → ℝ), ActualPresWordDisks v hv) :=
  (⟨RelativeAttachment.cell (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
    cell_continuous _ _⟩ : C(DiskFamily K (Fin 2 → ℝ), _)).comp
      ⟨fun d => ⟨h.cell d.1, d.2⟩, continuous_sigma (fun j => continuous_sigmaMk
          (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := h.cell j))⟩

def wordDiskMap : C(ActualPresWordDisks w hw, ActualPresWordDisks v hv) :=
  desc (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
    ((⟨old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      old_continuous _ _⟩ : C(orderNerveRealization (PresModel.Rose B), _)).comp
        h.orderRoseMapContinuous)
    (h.wordDiskCellMap hv)
    (fun a => by
      change old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone
        (actualPresWordAttaching w hw a)) =
          RelativeAttachment.cell _ _ (boundaryFamilyInclusion K (Fin 2 → ℝ) ⟨h.cell a.1, a.2⟩)
      rw [cell_boundary _ _ (boundaryFamilyInclusion_isClosedEmbedding K (Fin 2 → ℝ)).injective,
        h.actualPresWordAttaching_natural hw hv])

@[simp] theorem wordDiskMap_old (x : orderNerveRealization (PresModel.Rose A)) :
    h.wordDiskMap hw hv (old (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) x) =
      old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone x) := rfl

@[simp] theorem wordDiskMap_cell (d : DiskFamily J (Fin 2 → ℝ)) :
    h.wordDiskMap hw hv (RelativeAttachment.cell (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) d) =
      RelativeAttachment.cell (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        ⟨h.cell d.1, d.2⟩ := desc_cell ..

def classicalWordDiskMap : C(ClassicalPresWordDisks w hw, ClassicalPresWordDisks v hv) :=
  desc (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
    ((⟨old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      old_continuous _ _⟩ : C(ClassicalGraphModel.Rose B, _)).comp (diskRoseMap h.gen))
    ((⟨RelativeAttachment.cell (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      cell_continuous _ _⟩ : C(DiskFamily K (Fin 2 → ℝ), _)).comp
        ⟨fun d => ⟨h.cell d.1, d.2⟩, continuous_sigma (fun j => continuous_sigmaMk
          (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := h.cell j))⟩)
    (fun a => by
      change old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (diskRoseMap h.gen (classicalPresWordAttaching w hw a)) =
        RelativeAttachment.cell _ _ (boundaryFamilyInclusion K (Fin 2 → ℝ) ⟨h.cell a.1, a.2⟩)
      rw [cell_boundary _ _ (boundaryFamilyInclusion_isClosedEmbedding K (Fin 2 → ℝ)).injective,
        h.classicalPresWordAttaching_natural hw hv])

@[simp] theorem classicalWordDiskMap_old (x : ClassicalGraphModel.Rose A) :
    h.classicalWordDiskMap hw hv
      (old (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) x) =
      old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (diskRoseMap h.gen x) := rfl

@[simp] theorem classicalWordDiskMap_cell (d : DiskFamily J (Fin 2 → ℝ)) :
    h.classicalWordDiskMap hw hv
      (RelativeAttachment.cell (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) d) =
      RelativeAttachment.cell (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        ⟨h.cell d.1, d.2⟩ := desc_cell ..

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}

theorem actualPresWordDiskComparison_cone (hw : ∀ j, w j ≠ []) (j : J)
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    actualPresWordDiskComparison w hw (coneAdjRealizationCell (circSet w) ⟨j, x⟩) =
      RelativeAttachment.cell (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
        ⟨j, presConeBallHomeomorph w j (List.length_pos_of_ne_nil (hw j)) x⟩ := by
  letI := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ (coneAdjRealizationCell _ ⟨j, x⟩)) = _
  erw [coneAdjRealizationDiskHomeomorph_cell, diskAttachmentBaseChangeHomotopyEquiv_cell]
  rfl

namespace PresWordEmbedding
variable (h : PresWordEmbedding w v)

def cylinderMap : CylBase w →o CylBase v where
  toFun
    | .inl r => .inl (h.roseMap r)
    | .inr c => .inr (h.circleMap c)
  monotone' := by
    intro p q hpq
    have H := h.posMap.monotone (show (ConeAdj.inc p : PresPos w) ≤ ConeAdj.inc q from hpq)
    cases p <;> cases q <;> exact H

theorem cylinderMap_inc (p : CylBase w) :
    ConeAdj.inc (h.cylinderMap p) = h.posMap (ConeAdj.inc p) := by
  cases p <;> rfl

theorem cylinderRetr_natural (p : CylBase w) :
    cylRetr (aHom v) (h.cylinderMap p) = h.roseMap (cylRetr (aHom w) p) := by
  cases p with
  | inl r => rfl
  | inr c => exact h.attaching_map c

def oldPartMap : ConeAdjBase (circSet w) →o ConeAdjBase (circSet v) where
  toFun x := ⟨h.posMap x.val, by
    obtain ⟨p, hp⟩ := x.property
    rw (config := { transparency := .default }) [← hp]
    exact ⟨h.cylinderMap p, h.cylinderMap_inc p⟩⟩
  monotone' := fun _ _ hxy => h.posMap.monotone hxy

theorem oldPartMap_baseOrderIso (x : ConeAdjBase (circSet w)) :
    coneAdjBaseOrderIso (h.oldPartMap x) = h.cylinderMap (coneAdjBaseOrderIso x) := by
  apply ConeAdj.inc_injective
  erw [h.cylinderMap_inc]
  exact (Classical.choose_spec (h.oldPartMap x).property).trans
    (congrArg h.posMap (Classical.choose_spec x.property)).symm




variable (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

theorem actualPresWordDiskComparison_natural (x : orderNerveRealization (PresPos w)) :
    actualPresWordDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x) =
      h.wordDiskMap hw hv (actualPresWordDiskComparison w hw x) := by
  obtain ⟨z, rfl⟩ := (coneAdjRealization_piece_isQuotientMap (circSet w)).surjective x
  cases z with
  | inl x =>
      erw [(show orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationOld (circSet w) x) =
      coneAdjRealizationOld (circSet v)
        (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x) by
        erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
        rfl), actualPresWordDiskComparison_old,
        actualPresWordDiskComparison_old, h.wordDiskMap_old, (show presOldRoseHomotopyEquiv v (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x) =
      orderNerveRealizationMap h.roseMap h.roseMap.monotone (presOldRoseHomotopyEquiv w x) by
          change orderNerveRealizationMap (cylRetr (aHom v)) (cylRetr_monotone (aHom v))
              (orderNerveRealizationMap (coneAdjBaseOrderIso)
                (coneAdjBaseOrderIso (S := circSet v)).monotone
                (orderNerveRealizationMap h.oldPartMap h.oldPartMap.monotone x)) =
            orderNerveRealizationMap h.roseMap h.roseMap.monotone
              (orderNerveRealizationMap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))
                (orderNerveRealizationMap (coneAdjBaseOrderIso)
                  (coneAdjBaseOrderIso (S := circSet w)).monotone x))
          simp only [orderNerveRealizationMap_comp]
          have hf : (cylRetr (aHom v) ∘ coneAdjBaseOrderIso ∘ h.oldPartMap) =
              (h.roseMap ∘ cylRetr (aHom w) ∘ coneAdjBaseOrderIso) := by
            funext p
            change cylRetr (aHom v) (coneAdjBaseOrderIso (h.oldPartMap p)) = _
            erw [h.oldPartMap_baseOrderIso, h.cylinderRetr_natural]
            rfl
          exact orderNerveRealizationMap_congr _ _ hf x)]
  | inr z =>
      rcases z with ⟨j, x⟩
      erw [(show orderNerveRealizationMap h.posMap h.posMap.monotone (coneAdjRealizationCell (circSet w) ⟨j, x⟩) =
      coneAdjRealizationCell (circSet v)
        ⟨h.cell j, orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone x⟩ by
        erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
        rfl), actualPresWordDiskComparison_cone,
        actualPresWordDiskComparison_cone, h.wordDiskMap_cell, h.presConeBallHomeomorph_natural]

theorem diskRoseBaseChange_natural (x : ActualPresWordDisks w hw) :
    diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching v hv)
        (orderRoseRealizationHomeomorph B).toHomotopyEquiv (h.wordDiskMap hw hv x) =
      h.classicalWordDiskMap hw hv
        (diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching w hw)
          (orderRoseRealizationHomeomorph A).toHomotopyEquiv x) := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (actualPresWordAttaching w hw)
    (boundaryFamilyInclusion J (Fin 2 → ℝ)) x
  cases z with
  | inl x =>
      erw [h.wordDiskMap_old, diskAttachmentBaseChangeHomotopyEquiv_old,
        diskAttachmentBaseChangeHomotopyEquiv_old]
      exact (congrArg
        (old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)))
        (orderRoseRealizationHomeomorph_natural h x)).trans
          (h.classicalWordDiskMap_old hw hv (orderRoseRealizationHomeomorph A x)).symm
  | inr d =>
      erw [h.wordDiskMap_cell, diskAttachmentBaseChangeHomotopyEquiv_cell,
        diskAttachmentBaseChangeHomotopyEquiv_cell]
      exact (h.classicalWordDiskMap_cell hw hv d).symm

theorem presClassicalDiskComparison_natural (x : orderNerveRealization (PresPos w)) :
    presClassicalDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x) =
      h.classicalWordDiskMap hw hv (presClassicalDiskComparison w hw x) := by
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (actualPresWordDiskComparison v hv (orderNerveRealizationMap h.posMap h.posMap.monotone x)) = _
  erw [h.actualPresWordDiskComparison_natural hw hv, h.diskRoseBaseChange_natural hw hv]
  rfl

theorem classicalWordDiskMap_killsPi2_iff :
    Whitehead.KillsPi2 (h.classicalWordDiskMap hw hv) ↔
      Whitehead.KillsPi2 (orderNerveRealizationMap h.posMap h.posMap.monotone).hom := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (presClassicalDiskComparison w hw) (presClassicalDiskComparison v hv)
  have hs : (h.classicalWordDiskMap hw hv).comp (presClassicalDiskComparison w hw).toFun =
      (presClassicalDiskComparison v hv).toFun.comp
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom := by
    apply ContinuousMap.ext
    exact fun x => (h.presClassicalDiskComparison_natural hw hv x).symm
  erw [hs]

end PresWordEmbedding
end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

def puncturedLowerOrderIso (v : P) (a : Q) :
    {p : P // p < v ∧ f p ≠ a} ≃o {q : Q // q < f v ∧ q ≠ a} where
  toFun p := ⟨f p.1, hf.strictMono p.2.1, p.2.2⟩
  invFun q := ⟨(hf.lowerIntervalLift v ⟨q.1, q.2.1⟩).1,
    (hf.lowerIntervalLift v ⟨q.1, q.2.1⟩).2, by
      rw [hf.lowerIntervalLift_projection]
      exact q.2.2⟩
  left_inv p := Subtype.ext (hf.down_inj
    (hf.lowerIntervalLift v ⟨f p.1, hf.strictMono p.2.1⟩).2.le p.2.1.le
    (hf.lowerIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.lowerIntervalLift_projection v _)
  map_rel_iff' {a b} :=
    ⟨fun h => hf.le_of_le_below a.2.1.le b.2.1.le h, fun h => hf.mono h⟩

/-- Unlike the full inverse image, this interval cover is one fixed sheet. -/
theorem puncturedLower_isPosetCover (v : P) (a : Q) :
    IsPosetCover (fun p : {p : P // p < v ∧ f p ≠ a} =>
      (⟨f p.1, hf.strictMono p.2.1, p.2.2⟩ : {q : Q // q < f v ∧ q ≠ a})) := by
  let hi : IsPosetCover (id : {p : P // p < v ∧ f p ≠ a} → _) :=
    ⟨monotone_id, Function.surjective_id,
      fun x y h => ⟨y, ⟨h, rfl⟩, fun z hz => hz.2⟩,
      fun x y h => ⟨y, ⟨h, rfl⟩, fun z hz => hz.2⟩⟩
  exact hi.postcompose_orderIso (hf.puncturedLowerOrderIso v a)

end FiniteChains.Comb.IsPosetCover

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

theorem exists_cover_zigzag_contraction (hf : IsPosetCover f)
    (l r : Q → Q) (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b) :
    ∃ L R E : P → P, Monotone L ∧ Monotone R ∧ Monotone E ∧
      (∀ x, x ≤ R x) ∧ (∀ x, L x ≤ R x) ∧ (∀ x, L x ≤ E x) ∧
      (∀ {x y}, x ≤ y → E x = E y) := by
  let R := hf.upTransform r hir
  have hR  := hf.upTransform_monotone r hr hir
  have hlR : ∀ x, l (f x) ≤ f (R x) := by
    intro x
    rw [(hf.upTransform_spec r hir x).2]
    exact hlr (f x)
  let L := hf.lowerMapLift R (l ∘ f) hlR
  have hL  := hf.lowerMapLift_monotone R (l ∘ f) hR (hl.comp hf.mono) hlR
  have hLb : ∀ x, f (L x) ≤ b := by
    intro x
    rw [(hf.lowerMapLift_spec R (l ∘ f) hlR x).2]
    exact hlb (f x)
  let E := hf.upperMapLift L (fun _ => b) hLb
  refine ⟨L, R, E, hL, hR,
    hf.upperMapLift_monotone L (fun _ => b) hL (fun _ _ _ => le_refl _) hLb,
    hf.le_upTransform r hir, ?_, ?_, ?_⟩
  · intro x
    exact (hf.lowerMapLift_spec R (l ∘ f) hlR x).1
  · intro x
    exact (hf.upperMapLift_spec L (fun _ => b) hLb x).1
  · intro x y hxy
    exact hf.upperMapLift_constant_comparable L hL b hLb hxy

theorem strict_oneCycle_cover_zigzag (hf : IsPosetCover f)
    (l r : Q → Q) (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) d = c := by
  obtain ⟨L, R, E, hL, hR, hE, hiR, hLR, hLE, hconst⟩ :=
    exists_cover_zigzag_contraction hf l r hl hr hir hlr b hlb
  obtain ⟨y, hy⟩ := strict_oneCycle_comparable_boundary id R monotone_id hR hiR c hc
  obtain ⟨z, hz⟩ := strict_oneCycle_comparable_boundary L R hL hR hLR c hc
  obtain ⟨w, hw⟩ := strict_oneCycle_comparable_boundary L E hL hE hLE c hc
  refine ⟨z - y - w, ?_⟩
  rw [map_sub, map_sub, hz, hy, hw, normalizedStrictChain1_id,
    normalizedStrictChain1_zero_of_comparable_equal E hE hconst]
  abel_nf
  simp

theorem strict_twoCycle_cover_zigzag (hf : IsPosetCover f)
    (l r : Q → Q) (hl : Monotone l) (hr : Monotone r)
    (hir : ∀ x, x ≤ r x) (hlr : ∀ x, l x ≤ r x) (b : Q) (hlb : ∀ x, l x ≤ b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c := by
  obtain ⟨L, R, E, hL, hR, hE, hiR, hLR, hLE, hconst⟩ :=
    exists_cover_zigzag_contraction hf l r hl hr hir hlr b hlb
  obtain ⟨y, hy⟩ := strict_cycle_comparable_boundary id R monotone_id hR hiR c hc
  obtain ⟨z, hz⟩ := strict_cycle_comparable_boundary L R hL hR hLR c hc
  obtain ⟨w, hw⟩ := strict_cycle_comparable_boundary L E hL hE hLE c hc
  refine ⟨z - y - w, ?_⟩
  rw [map_sub, map_sub, hz, hy, hw, normalizedStrictChain2_id,
    normalizedStrictChain2_zero_of_comparable_equal E hE hconst]
  abel

end FiniteChains.Comb
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V P : Type} [DecidableEq V] [PartialOrder P]

theorem puncturedCubeBoundary_cover_fillings (t : Cube V) (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    (ht : t j = CubeCoord.free) {f : P → PuncturedCubeFace t j b} (hf : IsPosetCover f) :
    (∀ c : StrictOrdEdge P →₀ ℤ, Comb.bdry1 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) d = c) ∧
    (∀ c : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c) := by
  have hupper : ∀ c : PuncturedCubeFace t j b,
      c ≤ punctureOpen t j b z hb hz hbz ht c :=
    fun c => coordinate_face_open j z c.1
  have hmiddle : ∀ c : PuncturedCubeFace t j b,
      punctureProject t j b z hz hbz ht c ≤ punctureOpen t j b z hb hz hbz ht c :=
    fun c => coordinate_fix_face_open j z c.1
  have hend : ∀ c : PuncturedCubeFace t j b,
      punctureProject t j b z hz hbz ht c ≤ punctureOpposite t j b z hz hbz ht :=
    fun c => coordinateFix_face_opposite_facet j z c.2.1
  exact ⟨strict_oneCycle_cover_zigzag hf _ _
    (punctureProject_monotone t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht) hupper hmiddle _ hend,
    strict_twoCycle_cover_zigzag hf _ _
    (punctureProject_monotone t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht) hupper hmiddle _ hend⟩

/-- A genuine facet puncture supplies its own contraction, with no filling input. -/
theorem ordinary_puncturedCubeBoundary_cover_fillings (t : Cube V) (j : V) (b : CubeCoord)
    (hb : b ≠ CubeCoord.free) (ht : t j = CubeCoord.free)
    {f : P → PuncturedCubeFace t j b} (hf : IsPosetCover f) :
    (∀ c : StrictOrdEdge P →₀ ℤ, Comb.bdry1 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) d = c) ∧
    (∀ c : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c) := by
  cases b with
  | free => simp_all
  | pos =>
      exact puncturedCubeBoundary_cover_fillings t j .pos .neg hb
        (by decide) (by decide) ht hf
  | neg =>
      exact puncturedCubeBoundary_cover_fillings t j .neg .pos hb
        (by decide) (by decide) ht hf

variable [Fintype V] {A : CommRel V}

/-- The actual ordinary truncated-cell boundary has the same covered fillings. -/
theorem ordinaryTruncatedBoundary_cover_fillings {L : ASC V} {s t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate s.1)))
    {f : P → OldPuncturedBoundary s t} (hf : IsPosetCover f) :
    (∀ c : StrictOrdEdge P →₀ ℤ, Comb.bdry1 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) d = c) ∧
    (∀ c : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) c = 0 →
      ∃ d : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 d = c) := by
  obtain ⟨j, b, hb, htj, hs⟩ := exists_facet_coordinates_of_inc s t hi
  exact ordinary_puncturedCubeBoundary_cover_fillings _ j b hb htj
    (hf.postcomp_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hs))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- Both required lower-link fillings in the actual sheet of a lifted top cube.
Earlier collapse stages do not remove any other boundary cells. -/
theorem genus_ordinary_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s t : QOld (cmpRel (GenusVertex q)))
    (hs : s.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right))
    (v : P) (hv : f v = Sum.inl t) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 2 ∧
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 3 := by
  let pair : GenusCollapsePair q :=
    (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inl (qCubeToCoordinate s.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inl (qCubeToCoordinate s.1)) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hcert.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inl s} ≃o
      OldPuncturedBoundary s t := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intros; rfl }
  have hcover := (hf.puncturedLower_isPosetCover v (Sum.inl s)).postcompose_orderIso e
  have hfill := ordinaryTruncatedBoundary_cover_fillings hordinary hi hcover
  have hne : ∃ p : P, p < v ∧ f p ≠ Sum.inl s := by
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q (Sum.inl s) hs t ht
    obtain ⟨p, hp⟩ := hcover.surj ⟨x, hxt, hxs⟩
    exact ⟨p.1, p.2⟩
  have he p : (p < v ∧ f p ≠ Sum.inl s) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨genusCollapseStage_boundary_mem q left (pair :: right) hsplit t htail
        (f p) ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    · simp_all
  constructor
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_oneCycle_filling_of_strict hfill.1
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_twoCycle_filling_of_strict hfill.2

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- Delete every lift of both cells of an actual recorded ordinary pair.
This is a genuine comparison between consecutive chosen collapse stages;
neither finite sheet number nor relative homology vanishing is an input. -/
theorem genus_ordinary_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))]) (f p)) 3 := by
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))
  have hp : pair ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hs : s.1.spx.card = 2 := genus_removedFace_dimension q (Sum.inl s)
    (List.mem_map.mpr ⟨pair, hp, rfl⟩)
  have ht : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨pair, hp, rfl⟩)
  have hordinary : t.1.sgn ≠ 0 := by
    intro he
    apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1)
      (qCubeToCoordinate s.1) hp
    simpa using qCubeToCoordinate_sgn_zero t.1 he
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (pair :: right) hsplit
      (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s
  let T := fun p => f p = Sum.inl t
  have hTC : ∀ p, T p → C p := by
    intro p hpT
    refine ⟨hpT ▸ htC, ?_⟩
    rw [hpT]
    intro he
    have hdim := congrArg (fun c : QOld (cmpRel (GenusVertex q)) => c.1.spx.card)
      (Sum.inl.inj he)
    omega
  have hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p := by
    intro p hp x _ hpx
    have hx  := genus_top_cell_maximal q t ht (f x)
      (by rw [← hp]; exact hf.mono hpx)
    exact (hf.up_inj (le_refl p) hpx (hp.trans hx.symm)).symm
  have hlink₁ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 2 := by
    intro v hv
    exact (genus_ordinary_lifted_link_fillings q hf left right s t hs ht hordinary hsplit v hv).1
  have hlink₂ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 3 := by
    intro v hv
    exact (genus_ordinary_lifted_link_fillings q hf left right s t hs ht hordinary hsplit v hv).2
  have htop := maximalFamily_homology hTC hmax hlink₁ hlink₂
  have hface := genus_recorded_free_face_cover_homology q hf left right (Sum.inl s) t hsplit
  have he : (fun p => genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))]) (f p)) =
      (fun p => C p ∧ ¬ T p) := by
    funext p
    exact propext (genusCollapseStage_ordinary_step_iff q left s t (f p))
  rw [he]
  exact ⟨generatesDegreeIn_trans (fun _ h => h.1)
      (generatesDegreeIn_of_acyclicRelIn hface.1) htop.1,
    reflectsBoundsIn_trans (fun _ h => h.1) (hface.2 3) htop.2⟩

end FiniteChains.Davis.Genus

namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- A filling of the projected cycle pulls back along the section; the prism
corrects it to a filling of the original cycle. -/
theorem boundary_reflection_of_upper_section (r : P → Q) (s : Q → P)
    (hr : Monotone r) (hs : Monotone s) (hle : ∀ p, p ≤ s (r p))
    (c : Ch P) (hc : c ∈ Inc P) (hcyc : bdry c = 0)
    (hbound : ∃ y ∈ Inc Q, bdry y = cmap r c) :
    ∃ y ∈ Inc P, bdry y = c := by
  obtain ⟨y, hy, hdy⟩ := hbound
  have hp := bdry_prism_add_prism_bdry id (s ∘ r) c
  rw [hcyc, map_zero, add_zero, cmap_id] at hp
  refine ⟨cmap s y - prism id (s ∘ r) c,
    AddSubgroup.sub_mem _ (cmap_mem_inc_of_monotone hs hy)
      (prism_mem_inc monotone_id (hs.comp hr) hle hc), ?_⟩
  rw [map_sub, ← cmap_bdry, hdy, cmap_comp, hp]
  abel

end FiniteChains.Nerve

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V P : Type} [DecidableEq V] [PartialOrder P] {A : CommRel V}
  (f : P → QOld A)

abbrev TruncatedCover := PosetCoverPullback f (truncatedCellRetraction (A := A))

abbrev truncatedCoverProjection : TruncatedCover f → TruncatedCell A :=
  posetPullbackProjection f truncatedCellRetraction

abbrev truncatedCoverRetraction : TruncatedCover f → P :=
  posetPullbackOriginal f truncatedCellRetraction

theorem truncatedCoverProjection_isPosetCover (hf : IsPosetCover f) :
    IsPosetCover (truncatedCoverProjection f) :=
  hf.pullback truncatedCellRetraction truncatedCellRetraction_monotone

def truncatedCoverSection (p : P) : TruncatedCover f :=
  ⟨(p, oldCellIncl (f p)), rfl⟩

theorem truncatedCoverSection_monotone (hf : Monotone f) :
    Monotone (truncatedCoverSection f) := fun _ _ h => ⟨h, oldCellIncl_monotone (hf h)⟩

omit [DecidableEq V] [PartialOrder P] in
@[simp] theorem truncatedCoverRetraction_section (p : P) :
    truncatedCoverRetraction f (truncatedCoverSection f p) = p := rfl

theorem truncatedCover_le_section_retraction (p : TruncatedCover f) :
    p ≤ truncatedCoverSection f (truncatedCoverRetraction f p) := by
  refine ⟨le_refl _, ?_⟩
  change p.1.2 ≤ oldCellIncl (f p.1.1)
  rw [p.2]
  exact truncatedCell_le_retraction p.1.2

/-- Actual filling reflection in every old-cell covering, without a homology hypothesis. -/
theorem truncatedCoverRetraction_reflects_boundaries (hf : Monotone f)
    (c : Ch (TruncatedCover f)) (hc : c ∈ Inc (TruncatedCover f))
    (hcyc : Nerve.bdry c = 0)
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y = cmap (truncatedCoverRetraction f) c) :
    ∃ y ∈ Inc (TruncatedCover f), Nerve.bdry y = c :=
  boundary_reflection_of_upper_section (truncatedCoverRetraction f) (truncatedCoverSection f)
    (posetPullbackOriginal_monotone f _) (truncatedCoverSection_monotone f hf)
    (truncatedCover_le_section_retraction f) c hc hcyc hbound

end FiniteChains.Davis

namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem exists_bdry_eq_of_cycle_threeLeg (r g : P → P) (d : P)
    (hr : Monotone r) (hg : Monotone g) (hri : ∀ p, r p ≤ p)
    (hrg : ∀ p, r p ≤ g p) (hdg : ∀ p, d ≤ g p)
    (c : Ch P) (hc : c ∈ Inc P) (hcyc : bdry c = 0) :
    ∃ y ∈ Inc P, bdry y = c := by
  have h₁ := bdry_prism_add_prism_bdry r id c
  have h₂ := bdry_prism_add_prism_bdry r g c
  have h₃ := bdry_prism_add_prism_bdry (fun _ => d) g c
  rw [hcyc, map_zero, add_zero, cmap_id] at h₁
  rw [hcyc, map_zero, add_zero] at h₂ h₃
  have h₄ : bdry (consMap d (cmap (fun _ => d) c)) = cmap (fun _ => d) c := by
    have he : bdry (consMap d (cmap (fun _ => d) c)) +
        consMap d (cmap (fun _ => d) (bdry c)) = cmap (fun _ => d) c := by
      rw [bdry_consMap, cmap_bdry]
      abel
    simpa only [hcyc, map_zero, add_zero] using he
  refine ⟨prism r id c - prism r g c + prism (fun _ => d) g c +
    consMap d (cmap (fun _ => d) c), ?_, ?_⟩
  · exact AddSubgroup.add_mem _
      (AddSubgroup.add_mem _
        (AddSubgroup.sub_mem _ (prism_mem_inc hr monotone_id hri hc)
          (prism_mem_inc hr hg hrg hc))
        (prism_mem_inc monotone_const hg hdg hc)) (cone_const_mem_inc d c)
  · simp_all

end FiniteChains.Nerve

namespace FiniteChains.Davis
open Comb Nerve

abbrev VertexIntersection :=
  {c : VertexPuncturedCube // vertexPunctureLeft c ∧ vertexPunctureRight c}

def vertexIntersectionPoint (i : Fin 7) : VertexIntersection :=
  ⟨vertexIntersectionCell i, vertexIntersectionCell_mem i⟩

theorem vertexIntersectionPoint_injective : Function.Injective vertexIntersectionPoint := by
  have hi : Function.Injective vertexIntersectionCoordinates := by decide
  intro i j h
  exact hi (congrArg (fun c : VertexIntersection => c.1.1) h)

theorem vertexIntersectionPoint_surjective : Function.Surjective vertexIntersectionPoint := by
  intro c
  obtain ⟨i, hi⟩ := vertexIntersection_classify c.1 c.2
  exact ⟨i, Subtype.ext hi.symm⟩

def vertexIntersectionIndex (c : VertexIntersection) : Fin 7 :=
  Classical.choose (vertexIntersectionPoint_surjective c)


@[simp] theorem vertexIntersectionIndex_point (i : Fin 7) :
    vertexIntersectionIndex (vertexIntersectionPoint i) = i :=
  vertexIntersectionPoint_injective (Classical.choose_spec (vertexIntersectionPoint_surjective (vertexIntersectionPoint i)))

def vertexIntersectionLowerIndex : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 3, 2]
def vertexIntersectionUpperIndex : Fin 7 → Fin 7 := ![0, 1, 1, 4, 4, 4, 1]

def vertexIntersectionLower (c : VertexIntersection) : VertexIntersection :=
  vertexIntersectionPoint (vertexIntersectionLowerIndex (vertexIntersectionIndex c))

def vertexIntersectionUpper (c : VertexIntersection) : VertexIntersection :=
  vertexIntersectionPoint (vertexIntersectionUpperIndex (vertexIntersectionIndex c))

@[simp] theorem vertexIntersectionLower_point (i : Fin 7) :
    vertexIntersectionLower (vertexIntersectionPoint i) =
      vertexIntersectionPoint (vertexIntersectionLowerIndex i) := by
  simp [vertexIntersectionLower]

@[simp] theorem vertexIntersectionUpper_point (i : Fin 7) :
    vertexIntersectionUpper (vertexIntersectionPoint i) =
      vertexIntersectionPoint (vertexIntersectionUpperIndex i) := by
  simp [vertexIntersectionUpper]

theorem vertexIntersectionLower_monotone : Monotone vertexIntersectionLower := by
  have h : ∀ i j : Fin 7,
      CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
      CoordinateFace (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
        (vertexIntersectionCoordinates (vertexIntersectionLowerIndex j)) := by unfold CoordinateFace; decide
  intro c d hcd
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  obtain ⟨j, rfl⟩ := vertexIntersectionPoint_surjective d
  rw [vertexIntersectionLower_point, vertexIntersectionLower_point]
  exact h i j hcd


theorem vertexIntersectionLower_le (c : VertexIntersection) : vertexIntersectionLower c ≤ c := by
  have h : ∀ i : Fin 7, CoordinateFace
      (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
      (vertexIntersectionCoordinates i) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  rw [vertexIntersectionLower_point]
  exact h i

theorem vertexIntersectionLower_le_upper (c : VertexIntersection) :
    vertexIntersectionLower c ≤ vertexIntersectionUpper c := by
  have h : ∀ i : Fin 7, CoordinateFace
      (vertexIntersectionCoordinates (vertexIntersectionLowerIndex i))
      (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i)) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  rw [vertexIntersectionLower_point, vertexIntersectionUpper_point]
  exact h i

theorem vertexIntersectionPoint_zero_le_upper (c : VertexIntersection) :
    vertexIntersectionPoint 0 ≤ vertexIntersectionUpper c := by
  have h : ∀ i : Fin 7, CoordinateFace (vertexIntersectionCoordinates 0)
      (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i)) := by unfold CoordinateFace; decide
  obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
  rw [vertexIntersectionUpper_point]
  exact h i

/-- The actual intersection is acyclic in all augmented nerve degrees. -/
theorem vertexPuncture_intersection_acyclic :
    AcyclicIn (fun c : VertexPuncturedCube => vertexPunctureLeft c ∧ vertexPunctureRight c) := by
  apply acyclicIn_of_subtype _ ⟨vertexIntersectionCell 0, vertexIntersectionCell_mem 0⟩
  intro c hc hcyc
  exact exists_bdry_eq_of_cycle_threeLeg vertexIntersectionLower vertexIntersectionUpper
    (vertexIntersectionPoint 0) vertexIntersectionLower_monotone (by
      have h : ∀ i j : Fin 7,
          CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) →
          CoordinateFace (vertexIntersectionCoordinates (vertexIntersectionUpperIndex i))
            (vertexIntersectionCoordinates (vertexIntersectionUpperIndex j)) := by unfold CoordinateFace; decide
      intro c d hcd
      obtain ⟨i, rfl⟩ := vertexIntersectionPoint_surjective c
      obtain ⟨j, rfl⟩ := vertexIntersectionPoint_surjective d
      rw [vertexIntersectionUpper_point, vertexIntersectionUpper_point]
      exact h i j hcd)
    vertexIntersectionLower_le vertexIntersectionLower_le_upper
    vertexIntersectionPoint_zero_le_upper c hc hcyc

end FiniteChains.Davis

namespace FiniteChains.Davis
open Comb Nerve

theorem vertexPuncture_left_acyclic : AcyclicIn vertexPunctureLeft := by
  apply acyclicIn_of_subtype _ ⟨vertexPunctureLeftPole.1, vertexPunctureLeftPole.2⟩
  intro c hc hcyc
  exact exists_bdry_eq_of_cycle vertexPunctureLeftProjection vertexPunctureLeftPole
    vertexPunctureLeftProjection_monotone vertexPunctureLeftProjection_le
    vertexPunctureLeftProjection_le_pole hc hcyc


/-- The two actual coordinate pieces glue along the seven-cell path. -/
theorem vertexPuncturedCube_acyclic :
    ∀ c ∈ Inc VertexPuncturedCube, Nerve.bdry c = 0 →
      ∃ y ∈ Inc VertexPuncturedCube, Nerve.bdry y = c := by
  have h  :=
    acyclicIn_union_of_unmixed (fun c => ⟨fun _ => vertexPuncture_cover c, fun _ => trivial⟩)
      (fun c d h _ _ => vertexPuncture_unmixed c d h)
      vertexPuncture_left_acyclic (by
        apply acyclicIn_of_subtype _ ⟨vertexPunctureRightPole.1, vertexPunctureRightPole.2⟩
        intro c hc hcyc
        exact exists_bdry_eq_of_cycle vertexPunctureRightProjection vertexPunctureRightPole
          vertexPunctureRightProjection_monotone vertexPunctureRightProjection_le
          vertexPunctureRightProjection_le_pole hc hcyc)
      vertexPuncture_intersection_acyclic
  intro c hc hcyc
  have hc' : c ∈ IncOn (fun _ : VertexPuncturedCube => True) := by
    simpa using
      cmap_mem_incOn_of_maps monotone_id (fun _ => True.intro) hc
  obtain ⟨y, hy, hdy⟩ := h c hc' hcyc
  exact ⟨y, incOn_le_inc _ hy, hdy⟩

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

theorem positiveRetainedBoundary_acyclic (t : QOld A)
    (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ∀ c ∈ Inc (RetainedProperBoundary t), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (RetainedProperBoundary t), Nerve.bdry y = c :=
  exists_bdry_eq_of_cycle_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_acyclic

/-- The order homotopy to the retained proper faces supplies the missing prism. -/
theorem positiveCutPuncturedBoundary_acyclic (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ∀ c ∈ Inc (CutPuncturedBoundary t hne), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (CutPuncturedBoundary t hne), Nerve.bdry y = c := by
  let r := cutBoundaryRetraction t hne
  let s := cutBoundarySection t hne
  have hr := cutBoundaryRetraction_monotone t hne
  have hs := cutBoundarySection_monotone t hne
  intro c hc hcyc
  obtain ⟨y, hy, hdy⟩ := positiveRetainedBoundary_acyclic t ht hcard
    (cmap r c) (cmap_mem_inc_of_monotone hr hc)
    (by rw [← cmap_bdry, hcyc, map_zero])
  have hp := bdry_prism_add_prism_bdry id (s ∘ r) c
  rw [hcyc, map_zero, add_zero, cmap_id] at hp
  refine ⟨cmap s y - prism id (s ∘ r) c,
    AddSubgroup.sub_mem _ (cmap_mem_inc_of_monotone hs hy)
      (prism_mem_inc monotone_id (hs.comp hr)
        (cutBoundary_le_section_retraction t hne) hc), ?_⟩
  rw [map_sub, ← cmap_bdry, hdy, cmap_comp, hp]
  abel

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_cut_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hne : t.1.spx.Nonempty)
    (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right))
    (v : P) (hv : f v = Sum.inl t) (n : ℕ) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)) ∧ p < v) n := by
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inr (fullCutCell t hne)} ≃o
      CutPuncturedBoundary t hne := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intros; rfl }
  let E := (hf.puncturedLowerOrderIso v (Sum.inr (fullCutCell t hne))).trans e
  have hfill := exists_bdry_eq_of_cycle_of_orderIso E
    (positiveCutPuncturedBoundary_acyclic t hne hpositive ht)
  have hnonempty : ∃ p : P, p < v ∧ f p ≠ Sum.inr (fullCutCell t hne) := by
    have hdim : truncatedCellDimension (Sum.inr (fullCutCell t hne)) = 2 := by
      change t.1.spx.card - 1 = 2
      omega
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q (Sum.inr (fullCutCell t hne))
      hdim t ht
    exact ⟨(E.symm ⟨x, hxt, hxs⟩).1, (E.symm ⟨x, hxt, hxs⟩).2⟩
  have he p : (p < v ∧ f p ≠ Sum.inr (fullCutCell t hne)) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨genusCollapseStage_boundary_mem q left (pair :: right) hsplit t htail
        (f p) ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    · simp_all
  apply fillsDegreeIn_congr he
  apply fillsDegreeIn_of_subtype hnonempty
  exact fun c hc _ hcyc => hfill c hc hcyc

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_cut_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hne : t.1.spx.Nonempty)
    (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) (f p)) 3 := by
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (pair :: right) hsplit
      (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)
  let T := fun p => f p = Sum.inl t
  have hTC : ∀ p, T p → C p := by
    intro p hp
    exact ⟨hp ▸ htC, by rw [hp]; exact Sum.inl_ne_inr⟩
  have hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p := by
    intro p hp x _ hpx
    have hx  := genus_top_cell_maximal q t ht (f x)
      (by rw [← hp]; exact hf.mono hpx)
    exact (hf.up_inj (le_refl p) hpx (hp.trans hx.symm)).symm
  have hlink₁ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 2 := by
    intro v hv
    exact genus_cut_lifted_link_fillings q hf left right t hne ht hpositive hsplit v hv 2
  have hlink₂ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 3 := by
    intro v hv
    exact genus_cut_lifted_link_fillings q hf left right t hne ht hpositive hsplit v hv 3
  have htop := maximalFamily_homology hTC hmax hlink₁ hlink₂
  have hface := genus_recorded_free_face_cover_homology q hf left right
    (Sum.inr (fullCutCell t hne)) t hsplit
  have he : (fun p => genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) (f p)) =
      (fun p => C p ∧ ¬ T p) := by
    funext p
    exact propext (genusCollapseStage_cut_step_iff q left t hne (f p))
  rw [he]
  exact ⟨generatesDegreeIn_trans (fun _ h => h.1)
      (generatesDegreeIn_of_acyclicRelIn hface.1) htop.1,
    reflectsBoundsIn_trans (fun _ h => h.1) (hface.2 3) htop.2⟩

/-- Positivity and dimensions follow from the chosen collapse certificate. -/
theorem genus_recorded_cut_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) (f p)) 3 := by
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ht  := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inr σ.1), hp, rfl⟩)
  have hc := genusCollapseStage_suffix_certificate q left
    ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr σ.1) := by
    have hm : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
        (Sum.inr σ.1) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hc.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    simp only [spineInc] at hi
    split at hi
    · simp_all
    · simp at hi
  have hs : t.1.spx = σ.1 := by
    have hh := congrArg freeSet he
    simpa using hh
  have hpositive : t.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1
    · simpa [posCube, hv] using hh.symm
    · simpa [posCube, hv] using hh.symm
  have hne  := hs.symm ▸ σ.2.1
  have hstep := genus_cut_pair_cover_homology q hf left right t hne ht hpositive
    (by simpa only [hs] using hsplit)
  simpa only [hs] using hstep

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}


/-- All intermediate comparisons use chains on the actual surviving cells. -/
theorem genus_collapse_suffix_cover_homology (hf : IsPosetCover f)
    (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ right) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ right) (f p)) 3 := by
  induction right generalizing left with
  | nil =>
    simp
    constructor
    · intro z hz _ hcyc
      exact ⟨z, hz, 0, AddSubgroup.zero_mem _, hcyc, by simp⟩
    · intro c _ _ hbound
      exact hbound
  | cons pair right ih =>
    have hfirst := (show GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [pair]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [pair]) (f p)) 3 by
      have hp : pair ∈ genusChainCollapse q := by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      obtain ⟨t, s, ht, hs⟩ := genus_pair_cells q pair hp
      have he : pair = (qCubeToCoordinate t.1, truncatedFaceIndex s) :=
        Prod.ext ht.symm hs.symm
      rw [he] at hsplit ⊢
      cases s with
      | inl s => exact genus_ordinary_pair_cover_homology q hf left right s t hsplit
      | inr σ => exact genus_recorded_cut_pair_cover_homology q hf left right σ t hsplit)
    have htail := ih (left ++ [pair]) (by simpa using hsplit)
    have hgen := generatesDegreeIn_trans
      (fun p hp => genusCollapseStage_append_subset q left [pair] (f p) hp)
      hfirst.1 htail.1
    have href := reflectsBoundsIn_trans
      (fun p hp => genusCollapseStage_append_subset q (left ++ [pair]) right (f p) hp)
      hfirst.2 htail.2
    simpa using And.intro hgen href

/-- The actual surviving spine and the whole truncated block have the same H2
in every poset cover, including infinitely many sheets. This asserts both chain
generation and reflection of boundaries, with no homology premise. -/
theorem genusSpine_cover_homology (hf : IsPosetCover f) :
    GeneratesDegreeIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 ∧
    ReflectsBoundsIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 := by
  have h := genus_collapse_suffix_cover_homology q hf (genusChainCollapse q) [] (by simp)
  have hstart : (fun p => genusCollapseStage q [] (f p)) = (fun _ : P => True) := by
    funext p
    exact propext ⟨fun _ => trivial, fun _ => genusCollapseStage_nil q (f p)⟩
  have hfinish : (fun p => genusCollapseStage q ([] ++ genusChainCollapse q) (f p)) =
      (fun p => f p ∈ genusSpineCellSet q) := by
    funext p
    exact propext (by simpa using genusCollapseStage_final_iff q (f p))
  simp_all

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}


/-- A filling in the entire covering block is reflected to its actual spine;
normalization then makes it zero because that spine has no three-flags.
The input is an actual boundary, with no asphericity or relative-homology premise. -/
theorem genus_covered_spine_chain_zero_of_boundary (hf : IsPosetCover f)
    (c : StrictOrdTri {p : P // f p ∈ genusSpineCellSet q} →₀ ℤ)
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y =
      cmap (Subtype.val : {p : P // f p ∈ genusSpineCellSet q} → P)
        (ordNerveChain2 (ordStrictInclusion2 c))) : c = 0 := by
  let B := fun p => f p ∈ genusSpineCellSet q
  let z := ordNerveChain2 (ordStrictInclusion2 c)
  have hz : z ∈ Inc {p : P // B p} := ordNerveChain2_mem_inc _
  have hd : lengthProjection 3 (cmap Subtype.val z) =
      cmap Subtype.val z := by
    rw [lengthProjection_cmap, ordNerveChain2_lengthProjection]
  have hbound' : ∃ y ∈ IncOn (fun _ : P => True), Nerve.bdry y = cmap Subtype.val z := by
    obtain ⟨y, hy, hdy⟩ := hbound
    refine ⟨y, ?_, hdy⟩
    simpa using
      cmap_mem_incOn_of_maps (f := id) monotone_id (fun _ => True.intro) hy
  obtain ⟨y, hy, hdy⟩ := (genusSpine_cover_homology q hf).2
    _ (cmap_val_mem_incOn B hz) hd hbound'
  have hne : ∃ p : P, B p := by
    obtain ⟨p, hp⟩ := hf.surj (spineBase q).1
    refine ⟨p, ?_⟩
    change f p ∈ genusSpineCellSet q
    rw [hp]
    exact (spineBase q).2
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn B hy
  have hdb : Nerve.bdry b = z := by
    apply cmap_val_injective B hne
    rw [cmap_bdry, hby]
    exact hdy
  have he : ordBoundary3 (decodeOrdNerve3 b) = ordStrictInclusion2 c := by
    apply ordNerveChain2_injective
    rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hb,
      ← lengthProjection_bdry, hdb, ordNerveChain2_lengthProjection]
  haveI := (show IsEmpty (StrictOrdTet {p : P // f p ∈ genusSpineCellSet q}) by
    refine ⟨fun t => ?_⟩
    have h01 := truncatedCellDimension_strictMono (hf.strictMono t.2.1)
    have h12 := truncatedCellDimension_strictMono (hf.strictMono t.2.2.1)
    have h23 := truncatedCellDimension_strictMono (hf.strictMono t.2.2.2)
    have hmax := genusSpineCell_dimension_le_two q ⟨f t.1.2.2.2.1, t.1.2.2.2.2⟩
    change truncatedCellDimension (f t.1.2.2.2.1) ≤ 2 at hmax
    omega)
  have hzero : normalizeOrdChain3 (decodeOrdNerve3 b) = 0 := by
    ext t
    exact isEmptyElim t
  have hn := congrArg normalizeOrdChain2 he
  rw [normalizeOrdChain2_ordBoundary3, hzero, map_zero] at hn
  have hi  := normalizeOrdChain2_inclusion c
  exact (hn.trans hi).symm

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

abbrev OldCoveredSpine :=
  {p : TruncatedCover f // truncatedCoverProjection f p ∈ genusSpineCellSet q}

def oldCoveredSpineToOld (p : OldCoveredSpine q f) : P := truncatedCoverRetraction f p.1

theorem oldCoveredSpineToOld_monotone : Monotone (oldCoveredSpineToOld q f) :=
  fun _ _ h => h.1

/-- The comparison is constructed in the pullback of the actual covering.
It detects a boundary after projecting to old cells, without assuming an
isomorphism of covered chain complexes. -/
theorem genus_old_cover_spine_chain_zero_of_boundary (hf : IsPosetCover f)
    (c : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) c = 0)
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y =
      cmap (oldCoveredSpineToOld q f) (ordNerveChain2 (ordStrictInclusion2 c))) : c = 0 := by
  have hp := truncatedCoverProjection_isPosetCover f hf
  apply genus_covered_spine_chain_zero_of_boundary q hp c
  let z := cmap Subtype.val
    (ordNerveChain2 (ordStrictInclusion2 c))
  have hz : z ∈ Inc (TruncatedCover f) :=
    cmap_mem_inc_of_monotone monotone_subtypeVal (ordNerveChain2_mem_inc _)
  have hweak : Comb.bdry2 (orderCx (OldCoveredSpine q f)) (ordStrictInclusion2 c) = 0 := by
    change Comb.bdry2 _ (chain2 (strictOrderIncl _) c) = 0
    rw [bdry2_chain2, hc, map_zero]
  have hcyc : Nerve.bdry z = 0 := by
    rw [← cmap_bdry, (ordNerveChain2_cycle_iff _).mpr hweak, map_zero]
  apply truncatedCoverRetraction_reflects_boundaries f hf.mono z hz hcyc
  change ∃ y ∈ Inc P, Nerve.bdry y =
    cmap (fun x : OldCoveredSpine q f => truncatedCoverRetraction f x.val)
      (ordNerveChain2 (ordStrictInclusion2 c)) at hbound
  simpa only [z, cmap_comp, oldCoveredSpineToOld, Function.comp_def] using hbound

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f g : P → Q) (hf : Monotone f) (hg : Monotone g) (hfg : ∀ x, f x ≤ g x)

def ordMapPrismEdge (e : OrdEdge P) : OrdTri Q →₀ ℤ :=
  Finsupp.single ⟨(f e.1.1, g e.1.1, g e.1.2), hfg _, hg e.2⟩ 1 -
  Finsupp.single ⟨(f e.1.1, f e.1.2, g e.1.2), hf e.2, hfg _⟩ 1

def ordMapPrismTriangle (t : OrdTri P) : OrdTet Q →₀ ℤ :=
  Finsupp.single ⟨(f t.1.1, g t.1.1, g t.1.2.1, g t.1.2.2),
    hfg _, hg t.2.1, hg t.2.2⟩ 1 -
  Finsupp.single ⟨(f t.1.1, f t.1.2.1, g t.1.2.1, g t.1.2.2),
    hf t.2.1, hfg _, hg t.2.2⟩ 1 +
  Finsupp.single ⟨(f t.1.1, f t.1.2.1, f t.1.2.2, g t.1.2.2),
    hf t.2.1, hf t.2.2, hfg _⟩ 1

def ordMapPrism1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] (OrdTri Q →₀ ℤ) :=
  Finsupp.linearCombination ℤ (ordMapPrismEdge f g hf hg hfg)

def ordMapPrism2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTet Q →₀ ℤ) :=
  Finsupp.linearCombination ℤ (ordMapPrismTriangle f g hf hg hfg)


theorem ordMapPrism_identity (c : OrdTri P →₀ ℤ) :
    ordBoundary3 (ordMapPrism2 f g hf hg hfg c) +
      ordMapPrism1 f g hf hg hfg (Comb.bdry2 (orderCx P) c) =
    chain2 (orderCxMap g hg) c - chain2 (orderCxMap f hf) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add]
    rw [add_add_add_comm, hc, hd]
    abel
  | single t n =>
    have h := congrArg (fun z : OrdTri Q →₀ ℤ => n • z)
      (show ordBoundary3 (ordMapPrismTriangle f g hf hg hfg t) +
      ordMapPrism1 f g hf hg hfg (Comb.bdry2 (orderCx P) (Finsupp.single t 1)) =
    chain2 (orderCxMap g hg) (Finsupp.single t 1) -
      chain2 (orderCxMap f hf) (Finsupp.single t 1) by
        simp [ordMapPrismTriangle, ordMapPrism1, ordMapPrismEdge, ordBoundary3,
          ordTetBoundary, Comb.bdry2, orderCx, pathChain, chain2, orderCxMap]
        abel)
    simpa [ordMapPrism2, Comb.bdry2, smul_add, smul_sub, Finsupp.smul_single] using h

/-- Actual finite tetrahedra comparing the images of a cellular cycle. -/
theorem ordMapPrism_cycle (c : OrdTri P →₀ ℤ) (hc : Comb.bdry2 (orderCx P) c = 0) :
    ordBoundary3 (ordMapPrism2 f g hf hg hfg c) =
      chain2 (orderCxMap g hg) c - chain2 (orderCxMap f hf) c := by
  have h := ordMapPrism_identity f g hf hg hfg c
  simp_all

end FiniteChains.Comb
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Image of a finite nonempty chain under a monotone map. Repeated images
are removed from the simplex, without discarding their chain coefficients. -/
def barycentricMap (f : P → Q) (hf : Monotone f) (σ : NeSpx (cmpRel P)) :
    NeSpx (cmpRel Q) :=
  ⟨σ.1.image f, σ.2.1.image f, by
    apply isSimplex_cmpRel_iff.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact ((isSimplex_cmpRel_iff.mp σ.2.2) x hx y hy).imp (fun h => hf h) (fun h => hf h)⟩

theorem barycentricMap_monotone (f : P → Q) (hf : Monotone f) :
    Monotone (barycentricMap f hf) := fun _ _ h => Finset.image_mono f h

@[simp] theorem barycentricMap_spx1 (f : P → Q) (hf : Monotone f) (a : P) :
    barycentricMap f hf (spx1 a) = spx1 (f a) := rfl

@[simp] theorem barycentricMap_spx2 (f : P → Q) (hf : Monotone f)
    {a b : P} (hab : a ≤ b) :
    barycentricMap f hf (spx2 hab) = spx2 (hf hab) := by
  ext
  simp [barycentricMap, spx2]

@[simp] theorem chainMax_barycentricMap (f : P → Q) (hf : Monotone f)
    (σ : NeSpx (cmpRel P)) :
    chainMax (barycentricMap f hf σ) = f (chainMax σ) := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (chainMax_mem (barycentricMap f hf σ))
    rw [← he]
    exact hf (le_chainMax σ hx)
  · exact le_chainMax (barycentricMap f hf σ)
      (Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩)

def spx3 {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) : NeSpx (cmpRel P) :=
  ⟨{a, b, c}, by simp, by
    apply isSimplex_cmpRel_iff.mpr
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    exacts [Or.inl le_rfl, Or.inl hab, Or.inl (hab.trans hbc),
      Or.inr hab, Or.inl le_rfl, Or.inl hbc,
      Or.inr (hab.trans hbc), Or.inr hbc, Or.inl le_rfl]⟩

theorem spx2_le_spx3_left {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 hab ≤ spx3 hab hbc := by
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> simp [spx3]

theorem spx2_le_spx3_outer {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 (hab.trans hbc) ≤ spx3 hab hbc := by
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> simp [spx3]

theorem spx2_le_spx3_right {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 hbc ≤ spx3 hab hbc := by
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> simp [spx3]

@[simp] theorem chainMax_spx3 {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    chainMax (spx3 hab hbc) = c := by
  apply le_antisymm
  · have h := chainMax_mem (spx3 hab hbc)
    simp only [spx3, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact (le_of_eq h).trans (hab.trans hbc)
    · exact (le_of_eq h).trans hbc
    · exact le_of_eq h
  · exact le_chainMax (spx3 hab hbc) (by simp [spx3])

@[simp] theorem barycentricMap_spx3 (f : P → Q) (hf : Monotone f)
    {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    barycentricMap f hf (spx3 hab hbc) = spx3 (hf hab) (hf hbc) := by
  ext
  simp [barycentricMap, spx3]

def barycentricFlag (x : P) (e t : NeSpx (cmpRel P))
    (hxe : spx1 x ≤ e) (het : e ≤ t) : OrdTri (NeSpx (cmpRel P)) :=
  ⟨(spx1 x, e, t), hxe, het⟩

def barycentricEdge (e : OrdEdge P) : OrdEdge (NeSpx (cmpRel P)) →₀ ℤ :=
  Finsupp.single ⟨(spx1 e.1.1, spx2 e.2), spx1_le_spx2_left e.2⟩ 1 -
    Finsupp.single ⟨(spx1 e.1.2, spx2 e.2), spx1_le_spx2_right e.2⟩ 1

def barycentricTriangle (t : OrdTri P) : OrdTri (NeSpx (cmpRel P)) →₀ ℤ :=
  Finsupp.single (barycentricFlag t.1.2.1 (spx2 t.2.2) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_left t.2.2) (spx2_le_spx3_right t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.2.2 (spx2 t.2.2) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_right t.2.2) (spx2_le_spx3_right t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.1 (spx2 (t.2.1.trans t.2.2)) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_left _) (spx2_le_spx3_outer t.2.1 t.2.2)) 1 +
  Finsupp.single (barycentricFlag t.1.2.2 (spx2 (t.2.1.trans t.2.2)) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_right _) (spx2_le_spx3_outer t.2.1 t.2.2)) 1 +
  Finsupp.single (barycentricFlag t.1.1 (spx2 t.2.1) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_left _) (spx2_le_spx3_left t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.2.1 (spx2 t.2.1) (spx3 t.2.1 t.2.2)
    (spx1_le_spx2_right _) (spx2_le_spx3_left t.2.1 t.2.2)) 1

def barycentricChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] (OrdEdge (NeSpx (cmpRel P)) →₀ ℤ) :=
  Finsupp.linearCombination ℤ barycentricEdge

def barycentricChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTri (NeSpx (cmpRel P)) →₀ ℤ) :=
  Finsupp.linearCombination ℤ barycentricTriangle


theorem barycentricChain2_boundary (c : OrdTri P →₀ ℤ) :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricChain2 c) =
      barycentricChain1 (Comb.bdry2 (orderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rw [← Finsupp.smul_single_one t n, map_smul, map_smul, map_smul, map_smul]
    congr 1
    simpa only [barycentricChain2, Finsupp.linearCombination_single, one_smul] using
      (show Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricTriangle t) =
      barycentricChain1 (Comb.bdry2 (orderCx P) (Finsupp.single t 1)) by
        simp only [barycentricTriangle, map_add, map_sub, map_smul, Comb.bdry2_single, one_smul]
        simp only [pathChain, orderCx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        simp
        simp [barycentricTriangle, barycentricFlag, barycentricChain1,
          barycentricEdge, Comb.bdry2, orderCx, pathChain]
        abel)

theorem barycentric_mapDomain_sub {I J : Type u} (f : I → J) (x y : I →₀ ℤ) :
    Finsupp.mapDomain f (x - y) = Finsupp.mapDomain f x - Finsupp.mapDomain f y :=
  (Finsupp.mapDomain.addMonoidHom f).map_sub x y

theorem barycentricChain2_natural (f : P → Q) (hf : Monotone f) (c : OrdTri P →₀ ℤ) :
    chain2 (orderCxMap (barycentricMap f hf) (barycentricMap_monotone f hf))
      (barycentricChain2 c) = barycentricChain2 (chain2 (orderCxMap f hf) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [barycentricChain2, barycentricTriangle, barycentricFlag, chain2,
      orderCxMap, barycentric_mapDomain_sub, Finsupp.mapDomain_add,
      barycentricMap_spx1, barycentricMap_spx2, barycentricMap_spx3]

/-- Degenerate weak triangles have zero subdivision, so no artificial
diagonal cell survives the reverse map. -/
theorem barycentricTriangle_degenerate (t : OrdTri P)
    (ht : t.1.1 = t.1.2.1 ∨ t.1.2.1 = t.1.2.2) : barycentricTriangle t = 0 := by
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  rcases ht with h | h
  · change a = b at h
    subst b
    simp [barycentricTriangle, barycentricFlag, spx1, spx2, spx3]
  · change b = c at h
    subst c
    simp [barycentricTriangle, barycentricFlag, spx1, spx2, spx3]

theorem barycentricChain2_normalization (c : OrdTri P →₀ ℤ) :
    barycentricChain2 c = barycentricChain2 (ordStrictInclusion2 (normalizeOrdChain2 c)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    by_cases hab : t.1.1 = t.1.2.1
    · simp [barycentricChain2, barycentricTriangle_degenerate t (Or.inl hab),
        normalizeOrdChain2_single, normalizeOrdTriangle, hab]
    · by_cases hbc : t.1.2.1 = t.1.2.2
      · simp [barycentricChain2, barycentricTriangle_degenerate t (Or.inr hbc),
          normalizeOrdChain2_single, normalizeOrdTriangle, hbc]
      · have h1 := lt_of_le_of_ne t.2.1 hab
        have h2 := lt_of_le_of_ne t.2.2 hbc
        simp [normalizeOrdChain2_single, normalizeOrdTriangle, h1, h2,
          ordStrictInclusion2, strictOrderIncl]

/-- The last-vertex map recovers the original strict triangle with coefficient
one; the other five flags collapse and have zero normalized coefficient. -/
theorem barycentricChain2_lastVertex (c : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap (chainMax (P := P)) chainMax_monotone)
      (barycentricChain2 c)) = normalizeOrdChain2 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [barycentricChain2, barycentricTriangle, barycentricFlag, chain2,
      orderCxMap, barycentric_mapDomain_sub, Finsupp.mapDomain_add,
      normalizeOrdChain2, normalizeOrdTriangle]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P X : Type u} [PartialOrder P] [DecidableEq P]
  [PartialOrder X] (g : P →o X)
  (a : Qpos (cmpRel P) X (nerveAtt g))
  (hc : IsConnected (orderCx (Qpos (cmpRel P) X (nerveAtt g))))

/-- Lift an actual simplex in the surface cover to its barycentric pullback.
The top vertex fixes the sheet and all other vertices remain in that sheet. -/
def surfaceBarycentricToSubdivision
    (σ : NeSpx (cmpRel (AttachingSurfaceCover g a))) : AttachingSurfaceSubdivision g a :=
  ⟨((chainMax σ).1.1,
      barycentricMap (attachingSurfaceProjection g a) (posetPullbackProjection_monotone _ _) σ), by
    change uOrderEnd (chainMax σ).1.1 =
      qNew (att := nerveAtt g) (g (chainMax
        (barycentricMap (attachingSurfaceProjection g a)
          (posetPullbackProjection_monotone _ _) σ)))
    erw [chainMax_barycentricMap]
    exact (chainMax σ).2⟩


def surfaceBarycentricReverse : NeSpx (cmpRel (AttachingSurfaceCover g a)) →
    QLiftedAttaching a :=
  (surfaceSubdivisionToAttaching g a hc) ∘ (surfaceBarycentricToSubdivision g a)


/-- The reverse subdivision of the last-vertex image is carried by the
original top simplex, inside the OLD attaching cover itself. -/
theorem surfaceBarycentricReverse_le_lastVertex
    (σ : NeSpx (cmpRel (QLiftedAttaching a))) :
    surfaceBarycentricReverse g a hc
      (barycentricMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc) σ) ≤ chainMax σ := by
  let F := attachingToSurfaceCover g a hc
  let hF := attachingToSurfaceCover_monotone g a hc
  let s := surfaceBarycentricToSubdivision g a (barycentricMap F hF σ)
  have hb : s.1.1 = attachingSurfaceLowerLift g a hc (chainMax σ) := by
    change (chainMax (barycentricMap F hF σ)).1.1 = _
    erw [chainMax_barycentricMap]
    rfl
  have hs : s.1.2 ≤ qAttachingCoverEnd a (chainMax σ) := by
    intro p hp
    obtain ⟨d, hd, he⟩ := (@Finset.mem_image _ P (Classical.decEq P) _ _ _).mp hp
    obtain ⟨e, heσ, hed⟩ := Finset.mem_image.mp hd
    subst d
    erw [← he]
    exact (qAttachingCoverEnd_monotone g a (le_chainMax σ heσ))
      (chainMax_mem (qAttachingCoverEnd a e))
  have hsold : qOldIncl (posQCube s.1.2) ≤
      uOrderEnd (chainMax σ).1 := by
    erw [← qAttachingCoverEnd_oldPoint g a (chainMax σ)]
    exact qOldIncl_monotone ⟨hs, fun _ _ => rfl⟩
  have hlo : s.1.1 ≤ (chainMax σ).1 := by
    erw [hb]
    exact (attachingSurfaceLowerLift_spec g a hc (chainMax σ)).1
  obtain ⟨v, hvlo, hvhi, hvend⟩ := (uOrderEnd_isPosetCover hc).exists_interval_lift hlo
    (qOldIncl (posQCube s.1.2))
    (surfaceSubdivision_upper_comparison g a s) hsold
  have hu := surfaceSubdivisionUpperLift_spec g a hc s
  have heq : v = surfaceSubdivisionUpperLift g a hc s :=
    (uOrderEnd_isPosetCover hc).up_inj hvlo hu.1 (hvend.trans hu.2.symm)
  change surfaceSubdivisionUpperLift g a hc s ≤ (chainMax σ).1
  exact heq ▸ hvhi

/-- The only kernel of the normalized forward map on actual two-cycles is
made of actual old three-boundaries. All witnesses are finite cellular chains. -/
theorem attachingSurface_normalized_cycle_reflection
    (c : OrdTri (QLiftedAttaching a) →₀ ℤ)
    (hcycle : Comb.bdry2 (orderCx (QLiftedAttaching a)) c = 0)
    (hzero : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) c) = 0) :
    ∃ b : OrdTet (QLiftedAttaching a) →₀ ℤ, ordBoundary3 b = c := by
  let F := attachingToSurfaceCover g a hc
  let hF := attachingToSurfaceCover_monotone g a hc
  let R := surfaceBarycentricReverse g a hc
  let hR := ((surfaceSubdivisionToAttaching_monotone g a hc).comp
    (show Monotone (surfaceBarycentricToSubdivision g a) by
      intro σ τ h
      exact ⟨(chainMax_monotone h).1,
        barycentricMap_monotone _ (posetPullbackProjection_monotone _ _) h⟩))
  let H := R ∘ barycentricMap F hF
  have hH  := hR.comp (barycentricMap_monotone F hF)
  have hle  := surfaceBarycentricReverse_le_lastVertex g a hc
  let s := barycentricChain2 c
  have hsc : Comb.bdry2 (orderCx (NeSpx (cmpRel (QLiftedAttaching a)))) s = 0 := by
    erw [barycentricChain2_boundary, hcycle, map_zero]
  have hnatural : chain2 (orderCxMap H hH) s =
      chain2 (orderCxMap R hR) (barycentricChain2 (chain2 (orderCxMap F hF) c)) := by
    change Finsupp.mapDomain
      ((orderCxMap R hR).onF ∘
        (orderCxMap (barycentricMap F hF) (barycentricMap_monotone F hF)).onF) s = _
    erw [Finsupp.mapDomain_comp]
    erw [show Finsupp.mapDomain
        (orderCxMap (barycentricMap F hF) (barycentricMap_monotone F hF)).onF s =
      barycentricChain2 (chain2 (orderCxMap F hF) c) from
        barycentricChain2_natural F hF c]
    rfl
  have hz : barycentricChain2 (chain2 (orderCxMap F hF) c) = 0 := by
    rw (config := { transparency := .default }) [barycentricChain2_normalization, hzero, map_zero]
  have hHz : chain2 (orderCxMap H hH) s = 0 := by rw (config := { transparency := .default }) [hnatural, hz, map_zero]
  let l := chain2 (orderCxMap (chainMax) chainMax_monotone) s
  let p := ordMapPrism2 H chainMax hH chainMax_monotone hle s
  have hp : ordBoundary3 p = l := by
    have h := ordMapPrism_cycle H chainMax hH chainMax_monotone hle s hsc
    simpa only [hHz, sub_zero] using h
  have hlc : Comb.bdry2 (orderCx (QLiftedAttaching a)) l = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hsc, map_zero]
  have hln : normalizeOrdChain2 l = normalizeOrdChain2 c := barycentricChain2_lastVertex c
  refine ⟨ordNormalizationHomotopy2 c - ordNormalizationHomotopy2 l + p, ?_⟩
  rw (config := { transparency := .default }) [map_add, map_sub, ← ordNormalization_cycle_boundary c hcycle,
    ← ordNormalization_cycle_boundary l hlc, hp, hln]
  rw (config := { transparency := .default }) [sub_sub_sub_cancel_right, sub_add_cancel]

/-- The reflection in exactly the homogeneous full-nerve interface used by
the old/star gluing theorem. -/

theorem attachingSurface_nerve_cycle_reflection_homogeneous
    (c : Nerve.Ch (QLiftedAttaching a)) (hinc : c ∈ Nerve.Inc (QLiftedAttaching a))
    (hdegree : Nerve.lengthProjection 3 c = c) (hcycle : Nerve.bdry c = 0)
    (hzero : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 c)) = 0) :
    ∃ b ∈ Nerve.Inc (QLiftedAttaching a),
      Nerve.lengthProjection 4 b = b ∧ Nerve.bdry b = c := by
  obtain ⟨b, hb, hdb⟩ := (show ∃ b ∈ Nerve.Inc (QLiftedAttaching a), Nerve.bdry b = c by
    have he  :=
      (ordNerveChain2_decode hinc).trans hdegree
    have hcell := (ordNerveChain2_cycle_iff (decodeOrdNerve2 c)).mp (by erw [he, hcycle])
    obtain ⟨b, hb⟩ := attachingSurface_normalized_cycle_reflection g a hc
      (decodeOrdNerve2 c) hcell hzero
    refine ⟨ordNerveChain3 b, ordNerveChain3_mem_inc b, ?_⟩
    erw [← ordNerveChain2_ordBoundary3, hb, he])
  refine ⟨Nerve.lengthProjection 4 b, Nerve.lengthProjection_mem_inc _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  erw [← Nerve.lengthProjection_bdry 3, hdb, hdegree]

/-- Exact homogeneous relative-chain comparison; the boundary itself is
retained, not merely its augmentation or its homology class. -/
theorem attachingSurface_nerve_relative_comparison
    (c d : Nerve.Ch (QLiftedAttaching a))
    (hcinc : c ∈ Nerve.Inc (QLiftedAttaching a))
    (hdinc : d ∈ Nerve.Inc (QLiftedAttaching a))
    (hcdegree : Nerve.lengthProjection 3 c = c)
    (hddegree : Nerve.lengthProjection 3 d = d)
    (hboundary : Nerve.bdry c = Nerve.bdry d)
    (himage : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 c)) =
      normalizeOrdChain2 (chain2
        (orderCxMap (attachingToSurfaceCover g a hc)
          (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 d))) :
    ∃ b ∈ Nerve.Inc (QLiftedAttaching a),
      Nerve.lengthProjection 4 b = b ∧ c - d = Nerve.bdry b := by
  obtain ⟨b, hb, hdeg, he⟩ := attachingSurface_nerve_cycle_reflection_homogeneous g a hc
    (c - d) (AddSubgroup.sub_mem _ hcinc hdinc)
    (by erw [map_sub, hcdegree, hddegree])
    (by erw [map_sub, hboundary, sub_self])
    (by erw [map_sub, map_sub, map_sub, himage, sub_self])
  grind

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

end FiniteChains.Davis.Genus
end

section
open scoped Classical
namespace FiniteChains.Comb
universe u

theorem pathChain_apply_zero_of_edge_absent {E : Type u} (p : List (E × Bool))
    (e : E) (hp : ∀ b ∈ p, b.1 ≠ e) : pathChain p e = 0 := by
  induction p with
  | nil => simp
  | cons b p ih =>
      have hb  := hp b (List.mem_cons_self ..)
      have ht  := fun c hc => hp c (List.mem_cons_of_mem b hc)
      rw [pathChain_cons, Finsupp.add_apply, ih ht]
      cases b.2 <;> simp [hb]

variable {X : Complex2.{u}} {a : X.V}

theorem liftedPathChain_apply_zero_of_edge_absent
    (v : UV X a) {p : List (X.E × Bool)} {b : X.V}
    (hp : IsPath X.src X.tgt p (endV v) b) (e : UE X a)
    (he : ∀ c ∈ p, c.1 ≠ e.1.2) : pathChain (uLiftPath p v) e = 0 := by
  apply pathChain_apply_zero_of_edge_absent
  intro c hc hce
  have hm : (c.1.1.2, c.2) ∈ p := by
    rw [← map_uLiftPath p v b hp]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  grind

section Markings
variable {I J : Type u} (b : X.V) (edge : I → X.E)
  (tail : I → List (X.E × Bool))
  (hp : ∀ i, IsPath X.src X.tgt ((edge i, true) :: tail i) b b)
  (v : J → UV X a) (hv : ∀ j, endV (v j) = b)

include hp in
theorem markedFirstEdge_src (i : I) : X.src (edge i) = b := (hp i).1.symm

def liftedMarkedFirstEdge (j : J) (i : I) : UE X a :=
  ⟨(v j, edge i), (hv j).trans (markedFirstEdge_src b edge tail hp i).symm⟩


/-- No occurrence later in any marking contributes to the distinguished
lifted first-edge coefficient, regardless of its sheet. -/
theorem liftedMarking_first_coefficient
    (he : Function.Injective edge) (hv' : Function.Injective v)
    (ht : ∀ i k c, c ∈ tail k → c.1 ≠ edge i) (j k : J) (i l : I) :
    pathChain (uLiftPath ((edge l, true) :: tail l) (v k))
      (liftedMarkedFirstEdge b edge tail hp v hv j i) =
        if (k, l) = (j, i) then 1 else 0 := by
  have hstart : endV (v k) = germSrc X.src X.tgt (edge l, true) :=
    (hv k).trans (markedFirstEdge_src b edge tail hp l).symm
  have hrest : IsPath X.src X.tgt (tail l) (endV (extend (edge l, true) (v k))) b := by
    rw [endV_extend hstart]
    exact (hp l).2
  have hzero := liftedPathChain_apply_zero_of_edge_absent (extend (edge l, true) (v k))
    hrest (liftedMarkedFirstEdge b edge tail hp v hv j i) (ht i l)
  rw [uLiftPath_cons hstart, liftGerm_true, pathChain_cons]
  simp only [↓reduceIte, Finsupp.add_apply, hzero, add_zero]
  have hinj := (show Function.Injective (fun x : J × I => liftedMarkedFirstEdge b edge tail hp v hv x.1 x.2) by
    intro x y hxy
    exact Prod.ext (hv' (congrArg (fun e : UE X a => e.1.1) hxy))
      (he (congrArg (fun e : UE X a => e.1.2) hxy)))
  change Finsupp.single (liftedMarkedFirstEdge b edge tail hp v hv k l) 1
    (liftedMarkedFirstEdge b edge tail hp v hv j i) = _
  have hsame :
      liftedMarkedFirstEdge b edge tail hp v hv k l =
        liftedMarkedFirstEdge b edge tail hp v hv j i ↔ (k, l) = (j, i) :=
    ⟨@hinj (k, l) (j, i),
      fun h => congrArg (fun x : J × I => liftedMarkedFirstEdge b edge tail hp v hv x.1 x.2) h⟩
  simp only [Finsupp.single_apply, hsame]

def liftedMarkingChainMap : ((J × I) →₀ ℤ) →ₗ[ℤ] (UE X a →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun x => pathChain (uLiftPath ((edge x.2, true) :: tail x.2) (v x.1)))

/-- This recovers the original finite coefficient function, with no
augmentation or sum over sheets. -/
theorem liftedMarkingChainMap_coefficient
    (he : Function.Injective edge) (hv' : Function.Injective v)
    (ht : ∀ i k c, c ∈ tail k → c.1 ≠ edge i)
    (c : (J × I) →₀ ℤ) (j : J) (i : I) :
    liftedMarkingChainMap edge tail v c (liftedMarkedFirstEdge b edge tail hp v hv j i) =
      c (j, i) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      rw [liftedMarkingChainMap, Finsupp.linearCombination_single, Finsupp.smul_apply,
        liftedMarking_first_coefficient b edge tail hp v hv he hv' ht]
      by_cases h : x = (j, i) <;> simp [h]

include hp hv in
theorem liftedMarkingChainMap_injective
    (he : Function.Injective edge) (hv' : Function.Injective v)
    (ht : ∀ i k c, c ∈ tail k → c.1 ≠ edge i) :
    Function.Injective (liftedMarkingChainMap edge tail v) := by
  intro c d hcd
  ext x
  have h := congrArg (fun z : UE X a →₀ ℤ =>
    z (liftedMarkedFirstEdge b edge tail hp v hv x.1 x.2)) hcd
  simpa only [liftedMarkingChainMap_coefficient b edge tail hp v hv he hv' ht] using h

end Markings
end FiniteChains.Comb
end

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def qOldPartOrderIso : {p : Qpos A X att // InQOld p} ≃o QOld A where
  toFun p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl c => exact c
    | inr x => exact False.elim hp
  invFun c := ⟨Sum.inl c, trivial⟩
  left_inv p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl c => rfl
    | inr x => exact False.elim hp
  right_inv c := rfl
  map_rel_iff' := by
    rintro ⟨p, hp⟩ ⟨r, hr⟩
    cases p with
    | inr x => exact False.elim hp
    | inl c =>
      cases r with
      | inr x => exact False.elim hr
      | inl d => rfl

abbrev QLiftedOld (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQOld (uOrderEnd p)}

def qOldCoverEnd (a : Qpos A X att) (p : QLiftedOld a) : QOld A :=
  qOldPartOrderIso ⟨uOrderEnd p.1, p.2⟩

theorem qOldCoverEnd_spec (a : Qpos A X att) (p : QLiftedOld a) :
    (Sum.inl (qOldCoverEnd a p) : Qpos A X att) = uOrderEnd p.1 :=
  congrArg Subtype.val (qOldPartOrderIso.symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

variable [Fintype V]

theorem qOldCoverEnd_isPosetCover (x : X) (hx : IsConnected (orderCx X)) :
    IsPosetCover (qOldCoverEnd (qNew (A := A) (att := att) x)) := by
  letI : Nonempty X := ⟨x⟩
  have hc : IsConnected (orderCx (Qpos A X att)) :=
    qpos_isConnected_of_zpos (zpos_isConnected hx)
  have hf := IsPosetCover.restriction
    (uOrderEnd (a := qNew x)) {p | InQOld p}
    (uOrderEnd_isPosetCover hc)
  exact hf.postcompose_orderIso qOldPartOrderIso

end FiniteChains.Davis

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem Hom.comp_left_cancel_of_injective (f : Hom Y Z)
    (hv : Function.Injective f.onV) (he : Function.Injective f.onE)
    (hf : Function.Injective f.onF) (r s : Hom K Y)
    (h : f.comp r = f.comp s) : r = s := by
  apply Hom.ext'
  · funext a
    exact hv (congrArg (fun k : Hom K Z => k.onV a) h)
  · funext e
    exact he (congrArg (fun k : Hom K Z => k.onE e) h)
  · funext t
    exact hf (congrArg (fun k : Hom K Z => k.onF t) h)

theorem uOrderHomInv_projection_square {P : Type} [PartialOrder P] (a : P) :
    (orderCxMap uOrderEnd (uOrderEnd_monotone (P := P) (a := a))).comp uOrderHomInv =
      univProj (orderCx P) a := by
  apply Hom.ext'
  · funext x
    change uOrderEnd (uOrderHomInv.onV x) = endV x
    erw [uOrderHomInv_vertex]
    rfl
  · funext e
    exact uOrderHomInv_edge_projection e
  · funext t
    exact uOrderHomInv_face_projection t

theorem deckV_injective_in_group {X : Complex2} (a : X.V) (v : UV X a) :
    Function.Injective (fun g : Pi1 X a => deckV g v) := by
  intro g h he
  obtain ⟨d, _, hu⟩ := (isRegular_univProj (X := X) (x₀ := a)).simply_transitive
    v (deckV g v) (endV_deckV g v).symm
  exact (hu g rfl).trans (hu h he.symm).symm

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}
  {X : Type} [PartialOrder X] {att : NeSpx A →o X}

theorem qOldCover_projection_square (a : Qpos A X att)
    (hf : Monotone (qOldCoverEnd a)) :
    (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone).comp
      (orderCxMap (qOldCoverEnd a) hf) =
      (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (orderCxMap (Subtype.val : QLiftedOld a → UOrder (Qpos A X att) a)
          (fun _ _ h => h)) := by
  apply Hom.ext'
  · funext p
    exact qOldCoverEnd_spec a p
  · funext e
    apply Subtype.ext
    exact Prod.ext (qOldCoverEnd_spec a e.1.1) (qOldCoverEnd_spec a e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (qOldCoverEnd_spec a t.1.1)
      (Prod.ext (qOldCoverEnd_spec a t.1.2.1) (qOldCoverEnd_spec a t.1.2.2))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedOldCover := QLiftedOld (namedQuotientBase ρ q u)

def namedOldCoverProjection :
    namedOldCover q ρ u → QOld (cmpRel (GenusVertex q)) :=
  qOldCoverEnd (namedQuotientBase ρ q u)

theorem namedOldCoverProjection_isPosetCover : IsPosetCover (namedOldCoverProjection q ρ u) :=
  qOldCoverEnd_isPosetCover (namedAtt ρ q u (gBase q)) (namedBasePos_isConnected ρ q u)

variable {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

/-- The fibre product over the surviving spine is precisely the old-cover
spine used by the proved chain-faithfulness theorem. -/
def spinePullbackOldCoverOrderIso :
    PosetCoverPullback f (genusSpineCellToOld q) ≃o OldCoveredSpine q f where
  toFun x := ⟨⟨(x.1.1, x.1.2.1), x.2⟩, x.1.2.2⟩
  invFun x := ⟨(x.1.1.1, ⟨x.1.1.2, x.2⟩), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def coveredSpineToStrictSpine :
    Hom (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u)))
      (strictOrderCx (GenusSpineCell q)) :=
  (strictPullbackProjection (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm
        (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm.strictMono)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

abbrev MarkingSurfaceCell := SCell (gvc q) (gec q) (gc q)
abbrev MarkingSurfaceEdge := (orderCx (NeSpx (cmpRel (MarkingSurfaceCell q)))).E

def markingBaseCell : MarkingSurfaceCell q := .vtx none
def markingMidCell (i : Fin q × Bool) : MarkingSurfaceCell q := .vtx (some i)
def markingBedCell (i : Fin q × Bool) (b : Bool) : MarkingSurfaceCell q :=
  .bed (i.1, i.2, b)

theorem markingBaseLe (i : Fin q × Bool) (b : Bool) :
    markingBaseCell q ≤ markingBedCell q i b := by
  cases b with
  | false =>
    simpa only [cV, cE, gvc_markedBoundaryPos_false, gec_markedBoundaryPos,
      markingBaseCell, markingBedCell, toS] using
      cV_le_cE (gc q) (markedBoundaryPos q i false)
  | true =>
    simpa only [cV, cE, gvc_markedBoundaryPos_end, gec_markedBoundaryPos,
      markingBaseCell, markingBedCell, toS] using
      cV1_le_cE (gc q) (markedBoundaryPos q i true)

theorem markingMidLe (i : Fin q × Bool) (b : Bool) :
    markingMidCell q i ≤ markingBedCell q i b := by
  cases b with
  | false =>
    simpa only [markedBoundaryPos_succ, cV, cE, gvc_markedBoundaryPos_true,
      gec_markedBoundaryPos, markingMidCell, markingBedCell, toS] using
      cV1_le_cE (gc q) (markedBoundaryPos q i false)
  | true =>
    simpa only [cV, cE, gvc_markedBoundaryPos_true, gec_markedBoundaryPos,
      markingMidCell, markingBedCell, toS] using
      cV_le_cE (gc q) (markedBoundaryPos q i true)

def markingBaseFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBaseCell q), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_left (markingBaseLe q i b)⟩

def markingBedBaseFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_right (markingBaseLe q i b)⟩

def markingMidFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingMidCell q i), spx2 (markingMidLe q i b)),
    spx1_le_spx2_left (markingMidLe q i b)⟩

def markingBedMidFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingMidLe q i b)),
    spx1_le_spx2_right (markingMidLe q i b)⟩

/-- The edge detecting the marking `i`, traversed positively at its start. -/
def markingFirstEdge (i : Fin q × Bool) : MarkingSurfaceEdge q := markingBaseFlag q i false

def markingTail (i : Fin q × Bool) : List (MarkingSurfaceEdge q × Bool) :=
  [(markingBedBaseFlag q i false, false),
    (markingBedMidFlag q i false, true),
    (markingMidFlag q i false, false),
    (markingMidFlag q i true, true),
    (markingBedMidFlag q i true, false),
    (markingBedBaseFlag q i true, true),
    (markingBaseFlag q i true, false)]

/-- This is an equality of the original geometric paths, before passing to
path chains or projecting any cover sheets. -/
theorem gSig_first_edge (i : Fin q × Bool) :
    gSig q (i.1.val, i.2) = (markingFirstEdge q i, true) :: markingTail q i := by
  rw [gSig_boundary_path]
  simp only [bdEdge, edgeHop, edgeHopRev, hop, List.cons_append, List.nil_append,
    ordPos, ordNeg, markedBoundaryPos_succ, cV, cE,
    gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true,
    gvc_markedBoundaryPos_end, gec_markedBoundaryPos]
  rfl

theorem markingBaseFlag_eq_iff (i j : Fin q × Bool) (b c : Bool) :
    markingBaseFlag q i b = markingBaseFlag q j c ↔ i = j ∧ b = c := by
  constructor
  · intro h
    have ht := congrArg (fun e : MarkingSurfaceEdge q => e.1.2.1) h
    change ({markingBaseCell q, markingBedCell q i b}) =
      {markingBaseCell q, markingBedCell q j c} at ht
    have hm : markingBedCell q i b ∈
        ({markingBaseCell q, markingBedCell q j c} : Finset (MarkingSurfaceCell q)) := by
      rw [← ht]
      simp
    simp at hm
    rcases hm with hm | hm
    · cases hm
    · have he  := Cell.bed.inj hm
      exact ⟨congrArg (fun x : Fin q × Bool × Bool => (x.1, x.2.1)) he,
        congrArg (fun x : Fin q × Bool × Bool => x.2.2) he⟩
  · simp_all

theorem markingFirstEdge_injective : Function.Injective (markingFirstEdge q) := by
  intro i j h
  exact ((markingBaseFlag_eq_iff q i j false false).mp h).1


theorem markingFirstEdge_ne_mid (i j : Fin q × Bool) (b : Bool) :
    markingFirstEdge q i ≠ markingMidFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_base (i j : Fin q × Bool) (b : Bool) :
    markingFirstEdge q i ≠ markingBedBaseFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_mid (i j : Fin q × Bool) (b : Bool) :
    markingFirstEdge q i ≠ markingBedMidFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  have he := Finset.singleton_inj.mp hs
  cases he

/-- No marking's tail uses any distinguished edge, in either orientation. -/
theorem markingTail_avoids_firstEdge (i j : Fin q × Bool)
    (a : MarkingSurfaceEdge q × Bool) (ha : a ∈ markingTail q j) :
    a.1 ≠ markingFirstEdge q i := by
  simp only [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (markingFirstEdge_ne_bed_base q i j false).symm
  · exact (markingFirstEdge_ne_bed_mid q i j false).symm
  · exact (markingFirstEdge_ne_mid q i j false).symm
  · exact (markingFirstEdge_ne_mid q i j true).symm
  · exact (markingFirstEdge_ne_bed_mid q i j true).symm
  · exact (markingFirstEdge_ne_bed_base q i j true).symm
  · exact (show markingFirstEdge q i ≠ markingBaseFlag q j true by
    intro h
    have hf := ((markingBaseFlag_eq_iff q i j false true).mp h).2
    cases hf).symm

end FiniteChains.Davis.Genus

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.ReceivedTree
variable {G H I : Type} [Group G] [Group H]

def translateCellChain (g : G) (c : (G × I) →₀ ℤ) : (G × I) →₀ ℤ :=
  Finsupp.mapDomain (fun x : G × I => (g * x.1, x.2)) c

def multiplyCellChain (c : (G × I) →₀ ℤ) :
    MonoidAlgebra ℤ G →ₗ[ℤ] ((G × I) →₀ ℤ) :=
  (Finsupp.linearCombination ℤ (fun g => translateCellChain g c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap


theorem cellCoefficient_multiply (w : MonoidAlgebra ℤ G)
    (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (multiplyCellChain c w) = w * cellCoefficient i c := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, hw, hz, add_mul]
  | single g n =>
      erw [multiplyCellChain]
      erw [Finsupp.linearCombination_single]
      erw [map_smul, (show cellCoefficient i (translateCellChain g c) =
      MonoidAlgebra.single g 1 * cellCoefficient i c by
        induction c using Finsupp.induction_linear with
        | zero => simp [translateCellChain]
        | add c d hc hd =>
            simp only [translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
            erw [hc, hd, mul_add]
        | single x n =>
            erw [translateCellChain, Finsupp.mapDomain_single, cellCoefficient_single,
              cellCoefficient_single]
            by_cases h : x.2 = i
            · simp
            · simp)]
      erw [← smul_mul_assoc]
      congr 1
      simp [MonoidAlgebra.smul_single]

theorem cellCoefficient_map_group (f : G →* H) (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (Finsupp.mapDomain (fun x : G × I => (f x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ f (cellCoefficient i c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single x n =>
      erw [Finsupp.mapDomain_single, cellCoefficient_single, cellCoefficient_single]
      by_cases h : x.2 = i <;> simp [h, MonoidAlgebra.mapDomainRingHom]

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem namedSurfaceIntoQuotient_onV_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onV := by
  intro σ τ h
  have ho  := Sum.inl.inj h
  exact Subtype.ext (congrArg (fun c : QOld (cmpRel (GenusVertex q)) => c.1.spx) ho)

theorem namedSurfaceIntoQuotient_onE_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onE := by
  intro e f h
  apply Subtype.ext
  exact Prod.ext
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (fun e => e.1.1) h))
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (fun e => e.1.2) h))

def quotientMarkingFirstEdge (i : Fin q × Bool) : (orderCx (namedQuotientPos ρ q u)).E :=
  (namedSurfaceIntoQuotient q ρ u).onE (markingFirstEdge q i)

def quotientMarkingTail (i : Fin q × Bool) : List ((orderCx (namedQuotientPos ρ q u)).E × Bool) :=
  mapPath (namedSurfaceIntoQuotient q ρ u) (markingTail q i)

theorem quotientSurfaceMarking_first_edge (i : Fin q × Bool) :
    mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) =
      (quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i := by
  exact (mapPath_comp (oldIntoNamedQuotient q ρ u) (surfCx _) _).trans (by
    simpa only [namedSurfaceIntoQuotient, quotientMarkingFirstEdge, quotientMarkingTail, mapPath, List.map_cons]
      using congrArg (mapPath (namedSurfaceIntoQuotient q ρ u)) (gSig_first_edge q i))


theorem quotientMarkingTail_avoids (i j : Fin q × Bool)
    (c : (orderCx (namedQuotientPos ρ q u)).E × Bool)
    (hc : c ∈ quotientMarkingTail q ρ u j) : c.1 ≠ quotientMarkingFirstEdge q ρ u i := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  intro h
  exact markingTail_avoids_firstEdge q i j d hd
    (namedSurfaceIntoQuotient_onE_injective q ρ u h)

def allQuotientMarkingVertex
    (g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  deckV g (quotientCylinderVertex q ρ u)

theorem allQuotientMarkingVertex_end (g) :
    endV (allQuotientMarkingVertex q ρ u g) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) := by
  erw [allQuotientMarkingVertex, endV_deckV, quotientCylinderVertex_end]

theorem quotientSurfaceMarking_isPath (i : Fin q × Bool) :
    IsPath (orderCx (namedQuotientPos ρ q u)).src (orderCx (namedQuotientPos ρ q u)).tgt
      ((quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i)
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
  erw [← quotientSurfaceMarking_first_edge]
  exact isPath_mapPath _ (surfaceOldMarking_isPath q i)

def allQuotientSurfaceMarkingChains :
    ((Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  liftedMarkingChainMap (quotientMarkingFirstEdge q ρ u) (quotientMarkingTail q ρ u)
    (allQuotientMarkingVertex q ρ u)

/-- Every individual sheet coefficient is retained by the actual geometric
marking chains. -/
theorem allQuotientSurfaceMarkingChains_injective :
    Function.Injective (allQuotientSurfaceMarkingChains q ρ u) := by
  exact liftedMarkingChainMap_injective _ _ _ (quotientSurfaceMarking_isPath q ρ u)
    _ (allQuotientMarkingVertex_end q ρ u) ((namedSurfaceIntoQuotient_onE_injective q ρ u).comp (markingFirstEdge_injective q))
    (deckV_injective_in_group _ (quotientCylinderVertex q ρ u))
    (quotientMarkingTail_avoids q ρ u)

theorem quotientSurfaceMarkingChains_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    quotientSurfaceMarkingChains q ρ u hrho c =
      allQuotientSurfaceMarkingChains q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      simp only [Finsupp.mapDomain_single, quotientSurfaceMarkingChains,
        allQuotientSurfaceMarkingChains, liftedMarkingChainMap,
        Finsupp.linearCombination_single, quotientSurfaceMarking_first_edge,
        allQuotientMarkingVertex]
      erw [Finsupp.linearCombination_single]

theorem allQuotientSurfaceMarkingChains_translate
    (g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.translateCellChain g c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c) := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd =>
      simp only [ReceivedTree.translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
      erw [hc, hd]
  | single x n =>
      erw [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
      simp only [allQuotientSurfaceMarkingChains, liftedMarkingChainMap]
      erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg (fun z => n • z)
      have hp := quotientSurfaceMarking_isPath q ρ u x.2
      erw [← allQuotientMarkingVertex_end q ρ u x.1] at hp
      rw (config := { transparency := .default }) [univDeck_pathChain _ _ _ hp]
      simp only [allQuotientMarkingVertex, deckV_mul]

theorem allQuotientSurfaceMarkingChains_multiply
    (w : MonoidAlgebra ℤ (Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
          (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      erw [map_smul,
        allQuotientSurfaceMarkingChains_translate]

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)

abbrev QuotientMarkingGroup :=
  Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)

def allQuotientMarkingCorrection (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

def allQuotientMarkingCorrections :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => allQuotientMarkingCorrection q ρ u x.1 x.2)


theorem allQuotientMarkingCorrections_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allQuotientMarkingCorrections q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (allQuotientMarkingCorrections q ρ u c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      erw [map_smul,
        (show allQuotientMarkingCorrections q ρ u (ReceivedTree.translateCellChain g c) =
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
        (allQuotientMarkingCorrections q ρ u c) by
          induction c using Finsupp.induction_linear with
          | zero => rfl
          | add c d hc hd =>
              simp only [ReceivedTree.translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
              erw [hc, hd]
          | single x n =>
              erw [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
              simp only [allQuotientMarkingCorrections, Finsupp.linearCombination_single,
                map_smul, allQuotientMarkingCorrection, DeckAction.faceChains_mul])]

/-- The marked boundary detects the exact correction chain even when the
scalar has support outside the substituted subgroup. -/
theorem allQuotientMarkingCorrections_eq_of_boundary_multiple
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c d : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (h : allQuotientSurfaceMarkingChains q ρ u c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u d)) w.coeff) :
    allQuotientMarkingCorrections q ρ u c =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (allQuotientMarkingCorrections q ρ u d)) w.coeff := by
  erw [← allQuotientSurfaceMarkingChains_multiply] at h
  erw [allQuotientSurfaceMarkingChains_injective q ρ u h,
    allQuotientMarkingCorrections_multiply]

/-- Consequently the correction cancels from the relative difference as an
equality of actual two-chains, before applying old-cover faithfulness. -/
theorem allQuotientCorrection_cancel_difference
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c d : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (x y : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ)
    (h : allQuotientSurfaceMarkingChains q ρ u c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u d)) w.coeff) :
    (x - allQuotientMarkingCorrections q ρ u c) -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (y - allQuotientMarkingCorrections q ρ u d)) w.coeff =
    x - Finsupp.linearCombination ℤ (fun g =>
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g y) w.coeff := by
  have hs : Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (y - allQuotientMarkingCorrections q ρ u d)) w.coeff =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g y) w.coeff -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (allQuotientMarkingCorrections q ρ u d)) w.coeff := by
    clear h
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add w z hw hz => erw [MonoidAlgebra.coeff_add, map_add, map_add, map_add, hw, hz]; abel
    | single g n => simp only [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_sub, smul_sub]
  erw [hs, ← allQuotientMarkingCorrections_eq_of_boundary_multiple q ρ u w c d h]
  abel

variable (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem quotientMarkingCorrections_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    quotientMarkingCorrections q ρ u hrho c =
      allQuotientMarkingCorrections q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      simp only [Finsupp.mapDomain_single, quotientMarkingCorrections,
        allQuotientMarkingCorrections, Finsupp.linearCombination_single,
        quotientMarkingCorrection, allQuotientMarkingCorrection]

/-- Reflect the same polygon scalar on both parts of the named relation
vector at once. This avoids choosing unrelated scalars for faces and markings. -/
theorem quotientNamedCoefficients_reflect_multiple
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (hf : Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
        ((ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => β (Sum.inl j))) =
      ReceivedTree.multiplyCellChain
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
          ((ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => γ (Sum.inl j)))) w)
    (hm : Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      ReceivedTree.multiplyCellChain
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))) w) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  apply finiteSpineCoefficientMap_reflect_multiple ρ q u hrho β γ w
  intro m
  cases m with
  | inl j =>
      have h := congrArg (ReceivedTree.cellCoefficient j) hf
      simpa only [ReceivedTree.cellCoefficient_map_group,
        ReceivedTree.cellCoefficient_multiply, ReceivedTree.cellCoefficient_coordinates_symm,
        finiteSpineCoefficientMap] using h
  | inr i =>
      have h := congrArg (ReceivedTree.cellCoefficient i) hm
      simpa only [ReceivedTree.cellCoefficient_map_group,
        ReceivedTree.cellCoefficient_multiply, ReceivedTree.cellCoefficient_coordinates_symm,
        finiteSpineCoefficientMap] using h

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb.ReceivedTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  {G H : Type u} [Group G] [Group H]
  (φ : PresGroup (SpanningTree.treeRel T) →* G) (η : G →* H)

/-- Changing the sheet group commutes with every lifted attaching path. -/
theorem liftPath_map_group (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun eb => ((η eb.1.1, eb.1.2), eb.2)) =
      liftPath T (η.comp φ) p (η g) := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih =>
      rw (config := { transparency := .default }) [liftPath_cons, List.map_cons, liftPath_cons]
      have he : ((η (liftGerm T φ g e).1.1, (liftGerm T φ g e).1.2),
          (liftGerm T φ g e).2) = liftGerm T (η.comp φ) (η g) e := by
        obtain ⟨e, b⟩ := e
        cases b <;> simp [liftGerm, germValue, map_mul]
      erw [he, ih]
      apply congrArg (List.cons (liftGerm T (η.comp φ) (η g) e))
      apply congrArg (liftPath T (η.comp φ) p)
      exact map_mul η g (germValue T φ e)

/-- An actual cellular map, retaining the original cell in each dimension. -/
def changeGroup : Hom (cover T φ) (cover T (η.comp φ)) where
  onV x := (η x.1, x.2)
  onE x := (η x.1, x.2)
  onF x := (η x.1, x.2)
  src_onE _ := rfl
  tgt_onE x := by
    change (η x.1 * η (germValue T φ (x.2, true)), _) =
      (η (x.1 * germValue T φ (x.2, true)), _)
    rw (config := { transparency := .default }) [map_mul]
    rfl
  base_onF _ := rfl
  att_onF x := (liftPath_map_group T φ η (K.att x.2) x.1).symm

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def allQuotientSpineReceiver : PresGroup (spinePresentation q) →*
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (finiteSpineToQuotient ρ q u hrho).comp
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)

abbrev allQuotientReceivedSpineCover : Complex2 :=
  ReceivedTree.cover (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def allQuotientReceivedSpineProjection :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (markedSpineCx q) :=
  ReceivedTree.projection (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def receivedSpineChangeToAllQuotient :
    Hom (singleReceivedSpineCover q ρ u) (allQuotientReceivedSpineCover q ρ u hrho) :=
  ReceivedTree.changeGroup (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineToQuotient ρ q u hrho)

def allQuotientSpineOldRootReceiver :
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →*
      Pi1 (orderCx (namedQuotientPos ρ q u))
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) :=
  pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))



def allQuotientReceivedSpineToQuotient :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (allQuotientSpineReceiver q ρ u hrho) (allQuotientSpineOldRootReceiver q ρ u)
    (by
      exact finiteSpineOldRootReceiver_compatible q ρ u hrho))

theorem allQuotientReceivedSpineToQuotient_projects :
    (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
      (allQuotientReceivedSpineToQuotient q ρ u hrho) =
      (markedSpineToNamedQuotient q ρ u).comp
        (allQuotientReceivedSpineProjection q ρ u hrho) := by
  apply Hom.ext'
  · funext x
    change endV (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (allQuotientSpineOldRootReceiver q ρ u) x.1 x.2)) = _
    erw [endV_pathTransportV, ReceivedTree.receiverVertex_end]
    rfl
  · rfl
  · rfl

theorem allQuotientReceivedSpineToQuotient_changeGroup :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).comp
      (receivedSpineChangeToAllQuotient q ρ u hrho) =
      receivedSpineToQuotient q ρ u hrho := rfl

theorem allQuotientReceivedSpineToQuotient_chain2_changeGroup
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x =>
        (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) =
      chain2 (receivedSpineToQuotient q ρ u hrho) c := by
  change chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
    (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) c) = _
  erw [← chain2_comp_apply, allQuotientReceivedSpineToQuotient_changeGroup]

theorem allQuotientReceivedSpineToQuotient_deckV
    (g h : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
    (a : (markedSpineCx q).V) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onV (g * h, a) =
      deckV g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV (h, a)) := by
  have hs : ReceivedTree.receiverVertex (markedSpineTree q)
      (markedSpineToNamedQuotient q ρ u) (allQuotientSpineOldRootReceiver q ρ u) (g * h) a =
      deckV (allQuotientSpineOldRootReceiver q ρ u g)
        (ReceivedTree.receiverVertex (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (allQuotientSpineOldRootReceiver q ρ u) h a) := by
    simp only [ReceivedTree.receiverVertex, map_mul, deckV_mul]
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
      (allQuotientSpineOldRootReceiver q ρ u) (g * h) a) = _
  erw [hs, uCoverPathTransport_deckV]
  erw [pi1Conj_cancel_reverse]
  rfl

theorem allQuotientReceivedSpineToQuotient_deckF
    (g h : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
    (f : (markedSpineCx q).F) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onF (g * h, f) =
      deckF g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onF (h, f)) := by
  apply Subtype.ext
  exact Prod.ext (allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g h _) rfl

def allQuotientReceivedSpineOrderMap :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (orderCx (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :=
  uOrderHomInv.comp (allQuotientReceivedSpineToQuotient q ρ u hrho)

theorem allQuotientReceivedSpineOrderMap_old (a : (allQuotientReceivedSpineCover q ρ u hrho).V) :
    InQOld (uOrderEnd ((allQuotientReceivedSpineOrderMap q ρ u hrho).onV a)) := by
  change InQOld (endV (uOrderHomInv.onV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a)))
  erw [uOrderHomInv_vertex]
  have h := congrArg
    (fun k : Hom (allQuotientReceivedSpineCover q ρ u hrho) (orderCx (namedQuotientPos ρ q u)) => k.onV a)
    (allQuotientReceivedSpineToQuotient_projects q ρ u hrho)
  change endV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a) =
    (markedSpineToNamedQuotient q ρ u).onV a.2 at h
  erw [h]
  trivial

def allQuotientReceivedSpineToOldCover :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (orderCx (namedOldCover q ρ u)) :=
  orderCxRestrict (allQuotientReceivedSpineOrderMap q ρ u hrho)
    (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho)

def allQuotientReceivedSpineToStrictSpine :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (strictOrderCx (GenusSpineCell q)) :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (allQuotientReceivedSpineProjection q ρ u hrho)



def allQuotientReceivedSpineToCoveredSpine :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u))) :=
  (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u))
    (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).strictMono).comp
      (strictOrderPullbackHom (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q) (allQuotientReceivedSpineToOldCover q ρ u hrho)
    (allQuotientReceivedSpineToStrictSpine q ρ u hrho) (by
      let j := orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone
      have hv : Function.Injective j.onV := fun _ _ h => Sum.inl.inj h
      have he : Function.Injective j.onE := by
        intro e f h
        apply Subtype.ext
        exact Prod.ext (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.1) h))
          (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.2) h))
      have ht : Function.Injective j.onF := by
        intro e f h
        apply Subtype.ext
        exact Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.1) h))
          (Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.1) h))
            (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.2) h)))
      apply Hom.comp_left_cancel_of_injective j hv he ht
      calc
        _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
            ((orderCxMap Subtype.val (fun _ _ h => h)).comp
              (allQuotientReceivedSpineToOldCover q ρ u hrho)) := by
          change (j.comp (orderCxMap (namedOldCoverProjection q ρ u)
            (namedOldCoverProjection_isPosetCover q ρ u).mono)).comp _ = _
          dsimp only [j, namedOldCoverProjection]
          erw [qOldCover_projection_square]
          rfl
        _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
            (allQuotientReceivedSpineOrderMap q ρ u hrho) := by
          erw [allQuotientReceivedSpineToOldCover, orderCxRestrict_projects]
        _ = (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
            (allQuotientReceivedSpineToQuotient q ρ u hrho) := by
          change ((orderCxMap uOrderEnd uOrderEnd_monotone).comp uOrderHomInv).comp _ = _
          rw (config := { transparency := .default }) [uOrderHomInv_projection_square]
        _ = _ := allQuotientReceivedSpineToQuotient_projects q ρ u hrho))

theorem allQuotientReceivedSpineToCoveredSpine_first :
    (orderCxMap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
      (oldCoveredSpineToOld_monotone q (namedOldCoverProjection q ρ u))).comp
      ((strictOrderIncl _).comp (allQuotientReceivedSpineToCoveredSpine q ρ u hrho)) =
      allQuotientReceivedSpineToOldCover q ρ u hrho := rfl

theorem allQuotientReceivedSpineToCoveredSpine_vertex_old (a : (allQuotientReceivedSpineCover q ρ u hrho).V) :
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u)
      ((allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV a)).1 =
      (allQuotientReceivedSpineToQuotient q ρ u hrho).onV a := by
  change uOrderHomInv.onV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a) = _
  exact uOrderHomInv_vertex _

/-- Faithfulness of the group receiver preserves the individual sheets over
every spine vertex, including vertices away from the chosen root. -/
theorem allQuotientReceivedSpineToQuotient_sheet_injective (a : (markedSpineCx q).V) :
    Function.Injective (fun g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) =>
      (allQuotientReceivedSpineToQuotient q ρ u hrho).onV (g, a)) := by
  intro g h hgh
  apply deckV_injective_in_group (X := orderCx (namedQuotientPos ρ q u))
    (namedQuotientBase ρ q u)
    ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV (1, a))
  have hg := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g 1 a
  have hh := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho h 1 a
  simp_all

/-- The actual map into the pullback spine is injective on faces: its
spine projection retains the original face, and its old-cover projection
retains the sheet through the proved faithful receiver. -/
theorem allQuotientReceivedSpineToCoveredSpine_onF_injective :
    Function.Injective (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onF := by
  rintro ⟨g, t⟩ ⟨h, s⟩ he
  have hs := congrArg (coveredSpineToStrictSpine q ρ u).onF he
  have hts : t = s := Subtype.ext hs
  subst s
  have hv : (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV
      ((allQuotientReceivedSpineCover q ρ u hrho).base (g, t)) =
      (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV
        ((allQuotientReceivedSpineCover q ρ u hrho).base (h, t)) := by
    erw [← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF,
      ← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF, he]
  have hv' := congrArg (fun a =>
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u) a).1) hv
  erw [allQuotientReceivedSpineToCoveredSpine_vertex_old, allQuotientReceivedSpineToCoveredSpine_vertex_old] at hv'
  have hg  := allQuotientReceivedSpineToQuotient_sheet_injective q ρ u hrho
    ((markedSpineCx q).base t) hv'
  exact Prod.ext hg rfl


/-- A received spine cycle which bounds in the actual old cover is zero
already in the original group-indexed face chain. No abstract identification
of covered chains or extra injectivity hypothesis is used. -/
theorem allQuotientReceivedSpine_cycle_zero_of_old_boundary
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ)
    (hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = 0)
    (hbound : ∃ y ∈ Inc (namedOldCover q ρ u), Nerve.bdry y =
      cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c)))) : c = 0 := by
  have hz : chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c = 0 := by
    apply genus_old_cover_spine_chain_zero_of_boundary q (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u) _ _ hbound
    rw (config := { transparency := .default }) [bdry2_chain2, hc, map_zero]
  apply (Finsupp.mapDomain_injective (allQuotientReceivedSpineToCoveredSpine_onF_injective q ρ u hrho))
  simpa using hz


/-- This is the precise reflection needed after the old/star relative
filling: a three-boundary supported on actual old cells forces the original
received two-cycle, with its individual sheet coefficients, to vanish. -/
theorem allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ)
    (hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = 0)
    (hbound : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2 (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) :
    c = 0 := by
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hy
  apply allQuotientReceivedSpine_cycle_zero_of_old_boundary q ρ u hrho c hc
  refine ⟨b, hb, ?_⟩
  have hne : ∃ p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u),
      InQOld (uOrderEnd p) :=
    ⟨(allQuotientReceivedSpineOrderMap q ρ u hrho).onV (1, (markedSpineTree q).root),
      allQuotientReceivedSpineOrderMap_old q ρ u hrho _⟩
  apply cmap_val_injective _ hne
  rw (config := { transparency := .default }) [cmap_bdry, hby, hdy]
  exact (show cmap Subtype.val
      (cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c)))) =
      universalNerveChain2 (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c) by
    erw [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q
      (namedOldCoverProjection q ρ u))]
    erw [← ordNerveChain2_chain2
      Subtype.val
      (fun _ _ h => h)]
    apply congrArg ordNerveChain2
    have hfirst := congrArg (fun k => chain2 k c)
      (allQuotientReceivedSpineToCoveredSpine_first q ρ u hrho)
    simp only [chain2_comp_apply] at hfirst
    erw [hfirst]
    have hrestrict := congrArg (fun k => chain2 k c)
      (orderCxRestrict_projects (allQuotientReceivedSpineOrderMap q ρ u hrho)
        (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho))
    simp only [allQuotientReceivedSpineOrderMap, chain2_comp_apply] at hrestrict
    exact hrestrict).symm

end FiniteChains.Davis.Genus
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
variable {K : Complex2} (T : SpanningTree K) {G H I : Type} [Group G] [Group H]
  (φ : PresGroup (treeRel T) →* G)

theorem bdry2_translateCellChain (g : G) (c : (G × K.F) →₀ ℤ) :
    Comb.bdry2 (cover T φ) (translateCellChain g c) =
      translateCellChain g (Comb.bdry2 (cover T φ) c) :=
  DeckAction.faceChains_boundary (deck T φ) g c

theorem bdry2_multiplyCellChain (w : MonoidAlgebra ℤ G) (c : (G × K.F) →₀ ℤ) :
    Comb.bdry2 (cover T φ) (multiplyCellChain c w) =
      multiplyCellChain (Comb.bdry2 (cover T φ) c) w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      erw [multiplyCellChain]
      erw [Finsupp.linearCombination_single]
      erw [map_smul, bdry2_translateCellChain, multiplyCellChain]
      erw [Finsupp.linearCombination_single]


theorem markedChainMap_multiply (p : I → List (K.E × Bool))
    (w : MonoidAlgebra ℤ G) (c : (G × I) →₀ ℤ) :
    markedChainMap T φ p (multiplyCellChain c w) =
      multiplyCellChain (markedChainMap T φ p c) w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      erw [multiplyCellChain]
      erw [Finsupp.linearCombination_single]
      erw [map_smul, (show markedChainMap T φ p (translateCellChain g c) =
      translateCellChain g (markedChainMap T φ p c) by
        change markedChainMap T φ p (translateCellChain g c) =
          chain1 ((deck T φ).cellHom g) (markedChainMap T φ p c)
        induction c using Finsupp.induction_linear with
        | zero => rfl
        | add c d hc hd =>
            simp only [translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
            erw [hc, hd]
        | single x n =>
            erw [translateCellChain, Finsupp.mapDomain_single, markedChainMap_single,
              markedChainMap_single, map_smul]
            congr 1
            erw [liftPath_translate]
            exact pathChain_map ((deck T φ).cellHom g) (liftPath T φ (p x.2) x.1)), multiplyCellChain]
      erw [Finsupp.linearCombination_single]

theorem markedChainMap_changeGroup (η : G →* H) (p : I → List (K.E × Bool))
    (c : (G × I) →₀ ℤ) :
    chain1 (changeGroup T φ η) (markedChainMap T φ p c) =
      markedChainMap T (η.comp φ) p
        (Finsupp.mapDomain (fun x : G × I => (η x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      erw [Finsupp.mapDomain_single, markedChainMap_single, markedChainMap_single, map_smul]
      congr 1
      change Finsupp.mapDomain (changeGroup T φ η).onE (pathChain _) = _
      erw [← pathChain_map]
      exact congrArg pathChain (liftPath_map_group T φ η (p x.2) x.1)

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem receivedSpineFaceChain_marked_boundary
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 (singleReceivedSpineCover q ρ u)
      (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β) =
      ReceivedTree.markedChainMap (markedSpineTree q)
        (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
        (fun i => (treeMarkedSpineLoop q i).1)
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
    (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (treeMarkedSpineLoop q) (fun i => β (Sum.inr i))
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β)
  intro z
  let βF : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ
        (familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u)))) := β
  have hz0 := receivedSpineFaceChain_relative_boundary ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit βF
  have hwords : familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u) =
      finiteSpineWordBlock q u := by
    funext s
    cases s
    rfl
  have hz := hz0 (by
    intro t
    with_reducible
      convert hβ t using 1
      apply Finset.sum_congr rfl
      intro m hm
      congr 2
      all_goals first
        | exact Subsingleton.elim _ _
        | rfl
        | exact congrArg (substPresF ρ) hwords) z
  refine hz.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun a => βF (Sum.inr i) * a)
  exact (receivedSpineWordReceiver_coeff ρ (fun _ : PUnit.{1} => q)
    (fun _ => u) PUnit.unit (fox z (spinePresentationMarkedWord q i))).symm


theorem allQuotientReceivedSpineToQuotient_chain2_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      erw [map_smul,
        (show chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (ReceivedTree.translateCellChain g c) =
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
        (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c) by
          change Finsupp.mapDomain _ (Finsupp.mapDomain _ c) =
            Finsupp.mapDomain _ (Finsupp.mapDomain _ c)
          erw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
          apply congrArg (fun f => Finsupp.mapDomain f c)
          funext x
          exact allQuotientReceivedSpineToQuotient_deckF q ρ u hrho g x.1 x.2)]

/-- Once polygon reconstruction identifies the genuine relative geometric
class, all named coefficients are a single multiple of the reference vector.
The only remaining inputs are explicit geometric equalities of actual chains. -/
theorem finiteSpine_relative_class_principal
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (hmark : quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i))))) w.coeff)
    (hrel : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2
        (quotientCorrectedRelativeChain q ρ u hrho β -
          Finsupp.linearCombination ℤ (fun g =>
            (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
              (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff)) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  let F  := finiteSpineToQuotient ρ q u hrho
  let cβ : (singleReceivedSpineCover q ρ u).F →₀ ℤ :=
    receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β
  let cγ : (singleReceivedSpineCover q ρ u).F →₀ ℤ :=
    receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit γ
  let c  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2)) cβ
  let d  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2)) cγ
  let m  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2))
    ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))
  let n  :=
    Finsupp.mapDomain (fun x => (F x.1, x.2))
    ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))
  have hm : allQuotientSurfaceMarkingChains q ρ u m =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u n)) w.coeff := by
    simpa only [quotientSurfaceMarkingChains_factor] using hmark
  have hmn : m = ReceivedTree.multiplyCellChain n w := by
    rw (config := { transparency := .default }) [← allQuotientSurfaceMarkingChains_multiply] at hm
    exact allQuotientSurfaceMarkingChains_injective q ρ u hm
  let M := ReceivedTree.markedChainMap (markedSpineTree q)
    (allQuotientSpineReceiver q ρ u hrho) (fun i => (treeMarkedSpineLoop q i).1)
  have hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = M m := by
    change Comb.bdry2 _ (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) cβ) = _
    rw (config := { transparency := .default }) [bdry2_chain2, receivedSpineFaceChain_marked_boundary q ρ u β hβ]
    exact ReceivedTree.markedChainMap_changeGroup _ _ F _ _
  have hd : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) d = M n := by
    change Comb.bdry2 _ (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) cγ) = _
    rw (config := { transparency := .default }) [bdry2_chain2, receivedSpineFaceChain_marked_boundary q ρ u γ hγ]
    exact ReceivedTree.markedChainMap_changeGroup _ _ F _ _
  have hcycle : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho)
      (c - ReceivedTree.multiplyCellChain d w) = 0 := by
    rw (config := { transparency := .default }) [map_sub, hc, ReceivedTree.bdry2_multiplyCellChain, hd, hmn]
    change M (ReceivedTree.multiplyCellChain n w) - ReceivedTree.multiplyCellChain (M n) w = 0
    rw (config := { transparency := .default }) [ReceivedTree.markedChainMap_multiply, sub_self]
  have hcmap : chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c =
      chain2 (receivedSpineToQuotient q ρ u hrho) cβ :=
    allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cβ
  have hdmap : chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) d =
      chain2 (receivedSpineToQuotient q ρ u hrho) cγ :=
    allQuotientReceivedSpineToQuotient_chain2_changeGroup q ρ u hrho cγ
  have hcorr : quotientCorrectedRelativeChain q ρ u hrho β -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (quotientCorrectedRelativeChain q ρ u hrho γ)) w.coeff =
      chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
        (c - ReceivedTree.multiplyCellChain d w) := by
    rw (config := { transparency := .default }) [map_sub, allQuotientReceivedSpineToQuotient_chain2_multiply, hcmap, hdmap]
    simp only [quotientCorrectedRelativeChain, quotientMarkingCorrections_factor]
    exact allQuotientCorrection_cancel_difference q ρ u w m n
      (chain2 (receivedSpineToQuotient q ρ u hrho) cβ)
      (chain2 (receivedSpineToQuotient q ρ u hrho) cγ) hm
  have hcd : c = ReceivedTree.multiplyCellChain d w := by
    apply sub_eq_zero.mp
    apply allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary q ρ u hrho _ hcycle
    simpa only [hcorr] using hrel
  apply quotientNamedCoefficients_reflect_multiple q ρ u hrho β γ w
  · convert hcd using 1 <;> rfl
  · omega

end FiniteChains.Davis.Genus
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open Nerve
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem decodeOrdNerve2_cmap_homogeneous (f : P → Q) (hf : Monotone f)
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection 3 c = c) :
    decodeOrdNerve2 (cmap f c) = chain2 (orderCxMap f hf) (decodeOrdNerve2 c) := by
  have he  := (ordNerveChain2_decode hc).trans hd
  calc
    _ = decodeOrdNerve2 (cmap f (ordNerveChain2 (decodeOrdNerve2 c))) := by rw [he]
    _ = _ := by rw [← ordNerveChain2_chain2 f hf, decodeOrdNerve2_encode]

variable {a : P}

theorem uOrderEdge_deck (g : Pi1 (orderCx P) a) (e : OrdEdge (UOrder P a)) :
    uOrderEdge ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onE e) =
      deckE g (uOrderEdge e) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (endV (deckV g e.1.1), endV (deckV g e.1.2)) = (endV e.1.1, endV e.1.2)
    simp



theorem universalNerveChain1_deck (g : Pi1 (orderCx P) a)
    (c : UE (orderCx P) a →₀ ℤ) :
    universalNerveChain1 (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      cmap (uOrderDeck g) (universalNerveChain1 c) := by
  have he : chain1 uOrderHomInv (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      chain1 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (chain1 uOrderHomInv c) := by
    change Finsupp.mapDomain uOrderHomInv.onE (Finsupp.mapDomain (deckE g) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain uOrderHomInv.onE c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext e
    exact (show uOrderHomInv.onE (deckE g e) =
      (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onE
        (uOrderHomInv.onE e) by
      have hinv (e : UE (orderCx P) a) : uOrderEdge (uOrderHomInv.onE e) = e :=
        homInv_onE_apply uOrderHom Function.bijective_id
          ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
          ⟨uOrderFace_injective, uOrderFace_surjective⟩ e
      apply uOrderEdge_injective
      rw [hinv, uOrderEdge_deck, hinv])
  change ordNerveChain1 (chain1 uOrderHomInv
    (chain1 ((univDeck (orderCx P) a).cellHom g) c)) = _
  rw [he, ordNerveChain1_chain1]
  rfl

theorem universalNerveChain2_deck (g : Pi1 (orderCx P) a)
    (c : UF (orderCx P) a →₀ ℤ) :
    universalNerveChain2 ((univDeck (orderCx P) a).faceChains g c) =
      cmap (uOrderDeck g) (universalNerveChain2 c) := by
  have he : chain2 uOrderHomInv ((univDeck (orderCx P) a).faceChains g c) =
      chain2 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (chain2 uOrderHomInv c) := by
    change Finsupp.mapDomain uOrderHomInv.onF (Finsupp.mapDomain (deckF g) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain uOrderHomInv.onF c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext t
    exact (show uOrderHomInv.onF (deckF g t) =
      (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF
        (uOrderHomInv.onF t) by
      have hinv (t : UF (orderCx P) a) : uOrderFace (uOrderHomInv.onF t) = t :=
        homInv_onF_apply uOrderHom Function.bijective_id
          ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
          ⟨uOrderFace_injective, uOrderFace_surjective⟩ t
      apply uOrderFace_injective
      rw [hinv, uOrderFace_deck, hinv])
  change ordNerveChain2 (chain2 uOrderHomInv
    ((univDeck (orderCx P) a).faceChains g c)) = _
  rw [he, ordNerveChain2_chain2]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedAttachingDeck (g : NamedPolygonDeckGroup ρ q u) :
    namedAttachingCover q ρ u ≃o namedAttachingCover q ρ u where
  toFun p := ⟨uOrderDeck g p.1, by rw [uOrderDeck_end]; exact p.2⟩
  invFun p := ⟨uOrderDeck g⁻¹ p.1, by rw [uOrderDeck_end]; exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    change deckV g⁻¹ (deckV g p.1) = p.1
    rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv p := by
    apply Subtype.ext
    change deckV g (deckV g⁻¹ p.1) = p.1
    rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' := (uOrderDeckOrderIso g).map_rel_iff


theorem namedAttachingIntoUniversal_chain1_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u)
      (chain1 (orderCxMap (namedAttachingDeck ρ q u g)
        (namedAttachingDeck ρ q u g).monotone) c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g)
          (chain1 (namedAttachingIntoUniversal q ρ u) c) := by
  rw [← chain1_comp_apply, (show (namedAttachingIntoUniversal q ρ u).comp
      (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
      ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g).comp (namedAttachingIntoUniversal q ρ u) by
    apply Hom.ext'
    · rfl
    · funext e
      exact uOrderEdge_deck g ((orderCxMap Subtype.val
        (fun _ _ h => h)).onE e)
    · funext t
      exact uOrderFace_deck g ((orderCxMap Subtype.val
        (fun _ _ h => h)).onF t)), chain1_comp_apply]

theorem namedAttachingDeck_projection (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    qAttachingCoverEnd (namedQuotientBase ρ q u) (namedAttachingDeck ρ q u g p) =
      qAttachingCoverEnd (namedQuotientBase ρ q u) p := by
  change qPositiveOldOrderIso ⟨uOrderEnd (uOrderDeck g p.1), _⟩ =
    qPositiveOldOrderIso ⟨uOrderEnd p.1, _⟩
  congr 1
  exact Subtype.ext (uOrderDeck_end g p.1)


theorem namedAttachingToSurface_deck (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (namedAttachingDeck ρ q u g p) =
      namedSurfaceDeck ρ q u g
        (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
          (namedQuotientPos_isConnected ρ q u) p) := by
  apply Subtype.ext
  exact Prod.ext (by
    have h₁ := attachingSurfaceLowerLift_spec (namedSurfaceLabel ρ q u)
      (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
      (namedAttachingDeck ρ q u g p)
    have h₂ := attachingSurfaceLowerLift_spec (namedSurfaceLabel ρ q u)
      (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p
    apply (uOrderEnd_isPosetCover (namedQuotientPos_isConnected ρ q u)).down_inj
      h₁.1 ((uOrderDeckOrderIso g).monotone h₂.1)
    change uOrderEnd (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
      (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
      (namedAttachingDeck ρ q u g p)) =
      uOrderEnd (uOrderDeck g (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
        (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p))
    rw [h₁.2, uOrderDeck_end, h₂.2, namedAttachingDeck_projection])
    (congrArg chainMax (namedAttachingDeck_projection ρ q u g p))

def namedAttachingNerveSurfaceChain :
    Ch (namedAttachingCover q ρ u) →+
      (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  normalizeOrdChain2.toAddMonoidHom.comp
    ((chain2 (orderCxMap
      (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
        (namedQuotientPos_isConnected ρ q u))
      (attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
        (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)))).toAddMonoidHom.comp
      decodeOrdNerve2)


def namedAttachingNerveMultiple (c : Ch (namedAttachingCover q ρ u)) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      Ch (namedAttachingCover q ρ u) :=
  (Finsupp.linearCombination ℤ (fun g => cmap (namedAttachingDeck ρ q u g) c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

def namedQuotientNerveMultiple
    (c : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) :=
  (Finsupp.linearCombination ℤ (fun g => cmap (uOrderDeck g) c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem namedAttachingNerveMultiple_single (c : Ch (namedAttachingCover q ρ u))
    (g : NamedPolygonDeckGroup ρ q u) (n : ℤ) :
    namedAttachingNerveMultiple ρ q u c (MonoidAlgebra.single g n) =
      n • cmap (namedAttachingDeck ρ q u g) c := by
  unfold namedAttachingNerveMultiple
  simp

@[simp] theorem namedQuotientNerveMultiple_single
    (c : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (g : NamedPolygonDeckGroup ρ q u) (n : ℤ) :
    namedQuotientNerveMultiple ρ q u c (MonoidAlgebra.single g n) =
      n • cmap (uOrderDeck g) c := by
  unfold namedQuotientNerveMultiple
  simp

theorem namedAttachingNerveMultiple_mem_inc (c : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveMultiple ρ q u c w ∈ Inc _ := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simpa using AddSubgroup.add_mem _ hw hz
  | single g n =>
      rw [namedAttachingNerveMultiple_single]
      exact AddSubgroup.zsmul_mem _
        (cmap_mem_inc_of_monotone (namedAttachingDeck ρ q u g).monotone hc) n

theorem namedAttachingNerveMultiple_degree (c : Ch (namedAttachingCover q ρ u))
    (k : ℕ) (hc : lengthProjection k c = c)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    lengthProjection k (namedAttachingNerveMultiple ρ q u c w) =
      namedAttachingNerveMultiple ρ q u c w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp only [namedAttachingNerveMultiple_single,
        map_zsmul, lengthProjection_cmap, hc]

theorem namedAttachingNerveSurfaceChain_multiple
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c) (v : NamedPolygonPole ρ q u)
    (hv : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonFillingAt ρ q u v)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveSurfaceChain ρ q u (namedAttachingNerveMultiple ρ q u c w) =
      namedPolygonMultipleAt ρ q u v w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      rw [namedAttachingNerveMultiple_single, map_zsmul,
        (show namedAttachingNerveSurfaceChain ρ q u (cmap (namedAttachingDeck ρ q u g) c) =
      chain2 (strictOrderCxMap (namedSurfaceDeck ρ q u g)
        (namedSurfaceDeck ρ q u g).strictMono) (namedAttachingNerveSurfaceChain ρ q u c) by
          let F : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
            attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
            (namedQuotientPos_isConnected ρ q u)
          have hF  := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
            (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
          have hs : (orderCxMap F hF).comp
              (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
              (orderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).monotone).comp
                (orderCxMap F hF) := by
            apply Hom.ext'
            · funext p; exact namedAttachingToSurface_deck ρ q u g p
            · funext e
              apply Subtype.ext
              exact Prod.ext (namedAttachingToSurface_deck ρ q u g _)
                (namedAttachingToSurface_deck ρ q u g _)
            · funext t
              apply Subtype.ext
              exact Prod.ext (namedAttachingToSurface_deck ρ q u g _)
                (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
                  (namedAttachingToSurface_deck ρ q u g _))
          change normalizeOrdChain2 (chain2 (orderCxMap F hF)
            (decodeOrdNerve2 (cmap (namedAttachingDeck ρ q u g) c))) = _
          rw [decodeOrdNerve2_cmap_homogeneous _ (namedAttachingDeck ρ q u g).monotone c hc hd,
            ← chain2_comp_apply, hs, chain2_comp_apply, normalizeOrdChain2_strict_map]
          rfl), hv,
        namedPolygonMultipleAt]
      let f := fun g => chain2
        (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (namedPolygonFillingAt ρ q u v)
      change n • f g = Finsupp.linearCombination ℤ f (Finsupp.single g n)
      exact (Finsupp.linearCombination_single ℤ n g).symm


theorem namedQuotientNerveMultiple_add (c d)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (c + d) w =
      namedQuotientNerveMultiple ρ q u c w + namedQuotientNerveMultiple ρ q u d w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => grind
  | single g n => simp

theorem namedQuotientNerveMultiple_bdry (c)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (Nerve.bdry c) w =
      Nerve.bdry (namedQuotientNerveMultiple ρ q u c w) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp only [namedQuotientNerveMultiple_single,
        map_zsmul, cmap_bdry]

theorem namedQuotientNerveMultiple_attaching (c : Ch (namedAttachingCover q ρ u))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (cmap Subtype.val c) w =
      cmap Subtype.val (namedAttachingNerveMultiple ρ q u c w) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => rfl
  | add w z hw hz => grind
  | single g n =>
      simp only [namedQuotientNerveMultiple_single, namedAttachingNerveMultiple_single,
        map_zsmul, cmap_comp]
      rfl

theorem namedQuotientNerveMultiple_old (c)
    (hc : c ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u c w ∈ IncOn (fun p => InQOld (uOrderEnd p)) := by
  obtain ⟨d, hd, hdc⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hc
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simpa using AddSubgroup.add_mem _ hw hz
  | single g n =>
      rw [namedQuotientNerveMultiple_single]
      apply AddSubgroup.zsmul_mem
      rw [← hdc, cmap_comp]
      exact cmap_mem_incOn_of_maps
        (f := fun p : {p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) //
          InQOld (uOrderEnd p)} => uOrderDeck g p.1)
        ((uOrderDeckOrderIso g).monotone.comp (fun _ _ h => h))
        (fun p => by change InQOld (uOrderEnd (uOrderDeck g p.1)); rw [uOrderDeck_end]; exact p.2)
        hd

theorem namedQuotientNerveMultiple_universal1
    (c : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (universalNerveChain1 c) w =
      universalNerveChain1 (Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
          c) w.coeff) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      rw [namedQuotientNerveMultiple_single,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_smul, universalNerveChain1_deck]

theorem namedQuotientNerveMultiple_universal2
    (c : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (universalNerveChain2 c) w =
      universalNerveChain2 (Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          c) w.coeff) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      rw [namedQuotientNerveMultiple_single,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_smul, universalNerveChain2_deck]

/-- The reverse subdivision comparison supplies the missing old three-chain.
The reference is required to be the actual degree-one polygon filling. -/
theorem namedAttaching_polygon_multiple_old_boundary
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (C D : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : C = cmap Subtype.val c + Nerve.bdry yC)
    (hD : D = cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u))
    (hpolygon : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonMultipleAt ρ q u v w)
    (hboundary : Nerve.bdry C = namedQuotientNerveMultiple ρ q u (Nerve.bdry D) w) :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      Nerve.bdry y = C - namedQuotientNerveMultiple ρ q u D w := by
  let dw := namedAttachingNerveMultiple ρ q u d w
  have hdw  := namedAttachingNerveMultiple_mem_inc ρ q u d hd w
  have hdwdegree  :=
    namedAttachingNerveMultiple_degree ρ q u d 3 hddegree w
  have hD' : namedQuotientNerveMultiple ρ q u D w =
      cmap Subtype.val dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) := by
    rw [hD, namedQuotientNerveMultiple_add, namedQuotientNerveMultiple_attaching,
      namedQuotientNerveMultiple_bdry]
  have hb : Nerve.bdry c = Nerve.bdry dw := by
    apply cmap_val_injective _
      ⟨(namedAttachingReference q ρ u hrho 1).1, (namedAttachingReference q ρ u hrho 1).2⟩
    have h := hboundary
    rw [namedQuotientNerveMultiple_bdry, hC, hD', map_add, map_add,
      Nerve.bdry_bdry, Nerve.bdry_bdry, add_zero, add_zero, ← cmap_bdry, ← cmap_bdry] at h
    exact h
  have himage : namedAttachingNerveSurfaceChain ρ q u c =
      namedAttachingNerveSurfaceChain ρ q u dw := by
    rw [hpolygon, namedAttachingNerveSurfaceChain_multiple ρ q u d hd hddegree v hreference w]
  obtain ⟨b, hbi, _, hbcd⟩ := attachingSurface_nerve_relative_comparison
    (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u) c dw hc hdw hcdegree hdwdegree hb himage
  have hbOld : cmap Subtype.val b ∈
      IncOn (fun p => InQOld (uOrderEnd p)) :=
    cmap_mem_incOn_of_maps
      (f := Subtype.val)
      (fun _ _ h => h) (fun p => p.2.1) hbi
  refine ⟨(cmap Subtype.val b :
      Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) +
      yC - namedQuotientNerveMultiple ρ q u yD w,
    AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ hbOld hyC)
      (namedQuotientNerveMultiple_old ρ q u yD hyD w), ?_⟩
  rw [map_sub, map_add, ← cmap_bdry, ← hbcd, map_sub, hC, hD']
  let inc : namedAttachingCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) := Subtype.val
  change (cmap inc c - cmap inc dw) + Nerve.bdry yC -
      Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) =
    (cmap inc c + Nerve.bdry yC) -
      (cmap inc dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w))
  abel

/-- The geometric comparison feeds the full coefficient-rigidity theorem.
Its scalar is the actual polygon coefficient at the specified reference pole. -/
theorem finiteSpine_polygon_reference_principal
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry yC)
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c))
    (hmark : quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hpolygon  :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hboundary : Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      namedQuotientNerveMultiple ρ q u
        (Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho γ)) w := by
    rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
      quotientCorrectedRelativeNerveChain_boundary q ρ u hrho γ hγ,
      namedQuotientNerveMultiple_universal1, hmark]
  obtain ⟨y, hy, hdy⟩ := namedAttaching_polygon_multiple_old_boundary ρ q u hrho
    (quotientCorrectedRelativeNerveChain q ρ u hrho β)
    (quotientCorrectedRelativeNerveChain q ρ u hrho γ)
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference w hpolygon hboundary
  apply finiteSpine_relative_class_principal q ρ u hrho β γ hβ hγ w hmark
  refine ⟨y, hy, ?_⟩
  rw [hdy, quotientCorrectedRelativeNerveChain, quotientCorrectedRelativeNerveChain,
    namedQuotientNerveMultiple_universal2, map_sub]

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def oldToFullCube :
    Hom (orderCx (QOld (cmpRel (GenusVertex q))))
      (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  orderCxMap Subtype.val (fun _ _ h => h)

def markedSpineToFullCube :
    Hom (markedSpineCx q) (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  Hom.comp (oldToFullCube q)
    (Hom.comp (genusSpineToOld q) (componentIncl (genusSpineCx q) (spineBase q)))

/-- The constructed map sends each actual capping loop to a null-homotopic loop. -/
theorem markedSpineToFullCube_mark_null (x : Fin q × Bool) :
    Htpy (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) [] := by
  have h := mapPath_htpy (oldToFullCube q) (spineMarkedLoop_toOld_htpy q x)
  have hf := surfaceFullCube_loop_null (cmpRel (GenusVertex q))
    (isPath_gSig q (x.1.val, x.2))
  have he : mapPath (oldToFullCube q)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) =
      mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)) := by
    simp only [mapPath, List.map_map]
    rfl
  erw [he] at h
  have hh := h.trans hf
  unfold markedSpineToFullCube
  erw [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]
  exact hh

def spineFreeToFullCube :
    FreeGroup (SpinePresentationGen q) →*
      Pi1 (orderCx (QCube (cmpRel (GenusVertex q))))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  (pi1Map (markedSpineToFullCube q) (markedSpineTree q).root).comp
    (SpanningTree.freeToPi1 (markedSpineTree q))

/-- All actual capped presentation relators die in the full cube quotient. -/
theorem spineFreeToFullCube_capped_rel
    (m : SpinePresentationRel q ⊕ (Fin q × Bool)) :
    spineFreeToFullCube q (cappedSpinePresentation q m) = 1 := by
  cases m with
  | inl f =>
      change pi1Map (markedSpineToFullCube q) _
        (SpanningTree.freeToPi1 (markedSpineTree q)
          (SpanningTree.treeRel (markedSpineTree q) f)) = 1
      erw [SpanningTree.freeToPi1_treeRel, map_one]
  | inr x =>
      change pi1Map (markedSpineToFullCube q) _
        (SpanningTree.freeToPi1 (markedSpineTree q)
          (SpanningTree.pathWord (markedSpineTree q) (markedSpineLoop q x).1)) = 1
      erw [SpanningTree.freeToPi1_pathWord _ (markedSpineLoop q x).2]
      change pi1Map (markedSpineToFullCube q) _
        (pi1Conj ((markedSpineTree q).treePath_isPath (markedSpineBase q))
          (Pi1.mk (markedSpineLoop q x))) = 1
      rw (config := { transparency := .default }) [pi1Map_pi1Conj]
      have hz : pi1Map (markedSpineToFullCube q) (markedSpineBase q)
          (Pi1.mk (markedSpineLoop q x)) = 1 :=
        Quotient.sound (markedSpineToFullCube_mark_null q x)
      rw (config := { transparency := .default }) [hz, map_one]

/-- The genuine capped presentation maps to the full-cube fundamental group. -/
def cappedPresentationToFullCube :
    PresGroup (cappedSpinePresentation q) →*
      Pi1 (orderCx (QCube (cmpRel (GenusVertex q))))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  QuotientGroup.lift _ (spineFreeToFullCube q) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact spineFreeToFullCube_capped_rel q m)

@[simp] theorem cappedPresentationToFullCube_mk (w : FreeGroup (SpinePresentationGen q)) :
    cappedPresentationToFullCube q (QuotientGroup.mk w) = spineFreeToFullCube q w := rfl

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {a : X.V}

/-- A null-homotopic loop has a finite chain filling after lifting at any cover vertex. -/
theorem exists_lifted_boundary_of_null {v : UV X a}
    {p : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p (endV v) (endV v))
    (hn : Htpy X (endV v) (endV v) p []) :
    ∃ c : (uCover X a).F →₀ ℤ,
      bdry2 (uCover X a) c = pathChain (uLiftPath p v) := by
  have he : extendList p v = v := by
    simpa using extendList_htpy hp hn
  have hl : IsPath (uCover X a).src (uCover X a).tgt (uLiftPath p v) v v := by
    have h := isPath_uLiftPath p v (endV v) hp
    rwa [he] at h
  simpa using (simplyConnected_univCover v _ hl).exists_boundary

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Every exact marked cap loop has a filling at every vertex over its base point. -/
theorem fullCubeCover_cap_filling {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    ∃ c : (uCover (orderCx (QCube (cmpRel (GenusVertex q)))) a).F →₀ ℤ,
      Comb.bdry2 _ c = pathChain
        (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) v) := by
  apply exists_lifted_boundary_of_null
  · rw [hv]
    exact isPath_mapPath (markedSpineToFullCube q) (markedSpineLoop q x).2
  · rw [hv]
    exact markedSpineToFullCube_mark_null q x

/-- A chosen filling uses actual universal-cover faces and their actual cellular boundary. -/
def fullCubeCoverCapChain {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    (uCover (orderCx (QCube (cmpRel (GenusVertex q)))) a).F →₀ ℤ :=
  Classical.choose (fullCubeCover_cap_filling q x v hv)

theorem fullCubeCoverCapChain_boundary {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    Comb.bdry2 _ (fullCubeCoverCapChain q x v hv) = pathChain
      (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) v) :=
  Classical.choose_spec (fullCubeCover_cap_filling q x v hv)

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def rootedCappedFullVertex (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    UV (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  deckV (cappedPresentationToFullCube q g)
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q) a)

theorem rootedCappedFullVertex_end (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    endV (rootedCappedFullVertex q g a) = (markedSpineToFullCube q).onV a := by
  rw [rootedCappedFullVertex, endV_deckV, SpanningTree.mappedTreeReference_end]

/-- Traversing any genuine spine path updates the comparison vertex by its capped-group word. -/
theorem rootedCappedFullVertex_path (g : PresGroup (cappedSpinePresentation q))
    {a b : (markedSpineCx q).V} {p : List ((markedSpineCx q).E × Bool)}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    extendList (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) =
      rootedCappedFullVertex q
        (g * QuotientGroup.mk (SpanningTree.pathWord (markedSpineTree q) p)) b := by
  unfold rootedCappedFullVertex
  rw [extendList_deckV, SpanningTree.mappedTreeReference_path _ _ hp,
    map_mul, cappedPresentationToFullCube_mk, deckV_mul]
  rfl

/-- Comparison edges are actual edges in the full path-class universal cover. -/
def rootedCappedFullEdge (g : PresGroup (cappedSpinePresentation q))
    (e : (markedSpineCx q).E) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).src e),
    (markedSpineToFullCube q).onE e), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).src_onE]⟩

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def rootedCappedEdgeGerm
    (z : (PresGroup (cappedSpinePresentation q) × (markedSpineCx q).E) × Bool) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) × Bool :=
  (rootedCappedFullEdge q z.1.1 z.1.2, z.2)

/-- Comparison of an oriented lifted edge, including reverse traversal. -/
theorem rootedCapped_liftGerm (g : PresGroup (cappedSpinePresentation q))
    (eb : (markedSpineCx q).E × Bool) :
    rootedCappedEdgeGerm q
      (SpanningTree.liftGerm (cappedSpineTree q) (relSub (cappedSpinePresentation q)) g eb) =
      Comb.liftGerm (rootedCappedFullVertex q g
        (germSrc (markedSpineCx q).src (markedSpineCx q).tgt eb))
        ((markedSpineToFullCube q).onE eb.1, eb.2)
        (by rw [rootedCappedFullVertex_end, germSrc_onE]) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      have h := rootedCappedFullVertex_path q g
        (isPath_single (X := markedSpineCx q) (e, false))
      have he : extend ((markedSpineToFullCube q).onE e, false)
          (rootedCappedFullVertex q g ((markedSpineCx q).tgt e)) =
          rootedCappedFullVertex q
            (g * QuotientGroup.mk (SpanningTree.germWord (markedSpineTree q) (e, false)))
            ((markedSpineCx q).src e) := by
        simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
          SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, ite_false, Bool.false_eq_true] using h
      apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext
        · exact he.symm
        · rfl
      · rfl

/-- The comparison sends the entire genuine tree-cover lift to the actual path-class lift. -/
theorem rootedCapped_liftPath (g : PresGroup (cappedSpinePresentation q))
    {a b : (markedSpineCx q).V} {p : List ((markedSpineCx q).E × Bool)}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    (SpanningTree.liftK (cappedSpineTree q) (relSub (cappedSpinePresentation q)) p g).map
      (rootedCappedEdgeGerm q) =
      uLiftPath (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) := by
  induction p generalizing a g with
  | nil => rfl
  | cons eb p ih =>
      obtain ⟨ha, hp⟩ := hp
      subst a
      have hs : endV (rootedCappedFullVertex q g
          (germSrc (markedSpineCx q).src (markedSpineCx q).tgt eb)) =
          germSrc (orderCx (QCube (cmpRel (GenusVertex q)))).src
            (orderCx (QCube (cmpRel (GenusVertex q)))).tgt
            ((markedSpineToFullCube q).onE eb.1, eb.2) := by
        rw [rootedCappedFullVertex_end, germSrc_onE]
      have he : extend ((markedSpineToFullCube q).onE eb.1, eb.2)
          (rootedCappedFullVertex q g
            (germSrc (markedSpineCx q).src (markedSpineCx q).tgt eb)) =
          rootedCappedFullVertex q
            (g * QuotientGroup.mk (SpanningTree.germWord (markedSpineTree q) eb))
            (germTgt (markedSpineCx q).src (markedSpineCx q).tgt eb) := by
        have h := rootedCappedFullVertex_path q g (isPath_single (X := markedSpineCx q) eb)
        simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
          SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, ite_false, Bool.false_eq_true] using h
      rw [SpanningTree.liftK_cons, List.map_cons]
      change rootedCappedEdgeGerm q (SpanningTree.liftGerm _ _ g eb) :: _ =
        uLiftPath (((markedSpineToFullCube q).onE eb.1, eb.2) ::
          mapPath (markedSpineToFullCube q) p) _
      rw [uLiftPath_cons hs, he]
      apply congrArg₂ List.cons
      · exact rootedCapped_liftGerm q g eb
      · exact ih _ hp

end FiniteChains.Davis.Genus
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}
theorem pathChain_map_edges (f : X.E → Y.E) (p : List (X.E × Bool)) :
    pathChain (p.map (fun eb => (f eb.1, eb.2))) = Finsupp.mapDomain f (pathChain p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
      rw [List.map_cons, pathChain_cons, pathChain_cons, ih, Finsupp.mapDomain_add]
      congr 1
      by_cases hb : e.2
      · simp_all
      · have hn : Finsupp.mapDomain f (-Finsupp.single e.1 1) =
            -Finsupp.mapDomain f (Finsupp.single e.1 (1 : ℤ)) := by
          simpa using (Finsupp.lmapDomain ℤ ℤ f).map_neg (Finsupp.single e.1 1)
        simp [hb, hn]
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

abbrev rootedFullCover := uCover (orderCx (QCube (cmpRel (GenusVertex q))))
  ((markedSpineToFullCube q).onV (markedSpineTree q).root)
abbrev cappedTreeCover := SpanningTree.treeCover (cappedSpineTree q)
  (relSub (cappedSpinePresentation q)) (by
    intro f
    rw [cappedSpineTree_rel]
    exact rel_mem_relSub (cappedSpinePresentation q) f)

def rootedOldFace (g : PresGroup (cappedSpinePresentation q))
    (f : (markedSpineCx q).F) : (rootedFullCover q).F :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).base f),
    (markedSpineToFullCube q).onF f), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).base_onF]⟩

def rootedCoverChain1 :
    ((cappedTreeCover q).E →₀ ℤ) →ₗ[ℤ] ((rootedFullCover q).E →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun ge => rootedCappedFullEdge q ge.1 ge.2)


def rootedBaseCapFilling (x : Fin q × Bool) : (rootedFullCover q).F →₀ ℤ :=
  fullCubeCoverCapChain q x
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q))
    (SpanningTree.mappedTreeReference_end _ _ _)

def rootedCapFilling (g : PresGroup (cappedSpinePresentation q))
    (x : Fin q × Bool) : (rootedFullCover q).F →₀ ℤ :=
  (univDeck _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)).faceChains
    (cappedPresentationToFullCube q g) (rootedBaseCapFilling q x)


def rootedFaceComparison (gf : (cappedTreeCover q).F) :
    (rootedFullCover q).F →₀ ℤ :=
  match gf.2 with
  | .inl f => Finsupp.single (rootedOldFace q gf.1 f) 1
  | .inr x => rootedCapFilling q gf.1 x

def rootedCoverChain2 :
    ((cappedTreeCover q).F →₀ ℤ) →ₗ[ℤ] ((rootedFullCover q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (rootedFaceComparison q)

/-- The constructed comparison commutes with the boundary on every actual cover two-chain. -/
theorem rootedCoverChain2_boundary (c : (cappedTreeCover q).F →₀ ℤ) :
    Comb.bdry2 _ (rootedCoverChain2 q c) = rootedCoverChain1 q (Comb.bdry2 _ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single gf n =>
      have hb : Comb.bdry2 _ (rootedFaceComparison q gf) =
          rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single gf 1)) := by
        obtain ⟨g, f | x⟩ := gf
        · exact (show Comb.bdry2 _ (Finsupp.single (rootedOldFace q g f) 1) =
      rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single (g, Sum.inl f) 1)) by
          rw [bdry2_single, one_smul, bdry2_single, one_smul]
          change pathChain (uLiftPath ((orderCx (QCube (cmpRel (GenusVertex q)))).att
            ((markedSpineToFullCube q).onF f))
            (rootedCappedFullVertex q g ((markedSpineCx q).base f))) =
              Finsupp.mapDomain (fun ge => rootedCappedFullEdge q ge.1 ge.2)
                (pathChain (SpanningTree.liftK (cappedSpineTree q)
                  (relSub (cappedSpinePresentation q)) ((markedSpineCx q).att f) g))
          rw [(markedSpineToFullCube q).att_onF]
          have hp := rootedCapped_liftPath q g ((markedSpineCx q).att_isLoop f)
          simp only [mapPath] at hp
          rw [← hp]
          exact pathChain_map_edges (X := cappedTreeCover q) (Y := rootedFullCover q)
            (fun ge => rootedCappedFullEdge q ge.1 ge.2) _)
        · exact (show Comb.bdry2 _ (rootedCapFilling q g x) =
      rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single (g, Sum.inr x) 1)) by
          have hb := fullCubeCoverCapChain_boundary q x
            (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
              (markedSpineBase q)) (SpanningTree.mappedTreeReference_end _ _ _)
          have ht := (univDeck _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)).transport_filling
            (cappedPresentationToFullCube q g) (rootedBaseCapFilling q x) _ hb
          have he := uLiftPath_deckV (cappedPresentationToFullCube q g)
            (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
            (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
              (markedSpineBase q)) ((markedSpineToFullCube q).onV (markedSpineBase q))
            (by rw [SpanningTree.mappedTreeReference_end]
                exact isPath_mapPath _ (markedSpineLoop q x).2)
          change Comb.bdry2 _ (rootedCapFilling q g x) = pathChain
            ((uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
              (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
                (markedSpineBase q))).map
              (fun Eb => (deckE (cappedPresentationToFullCube q g) Eb.1, Eb.2))) at ht
          rw [← he] at ht
          rw [ht, bdry2_single, one_smul]
          change pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
            (rootedCappedFullVertex q g (markedSpineBase q))) =
              Finsupp.mapDomain (fun ge => rootedCappedFullEdge q ge.1 ge.2)
                (pathChain (SpanningTree.liftK (cappedSpineTree q)
                  (relSub (cappedSpinePresentation q)) (markedSpineLoop q x).1 g))
          rw [← rootedCapped_liftPath q g (markedSpineLoop q x).2]
          exact pathChain_map_edges (X := cappedTreeCover q) (Y := rootedFullCover q)
            (fun ge => rootedCappedFullEdge q ge.1 ge.2) _)
      rw [rootedCoverChain2, Finsupp.linearCombination_single, map_smul, hb]
      rw [bdry2_single, map_smul, bdry2_single, one_smul, map_smul]

/-- Every genuine capped-cover cycle has a degree-three filling after this comparison. -/
theorem rootedCoverCycle_fullCube_filling (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : UOrdTet (QCube (cmpRel (GenusVertex q)))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) →₀ ℤ,
      uOrdBoundary3 y = rootedCoverChain2 q c := by
  apply exists_universal_bdry3_of_cycle_qCube
  rw [rootedCoverChain2_boundary, hc, map_zero]

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

def rootedAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x)

def rootedAugmentedChain2 :
    ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (rootedAugmentedFace q)

/-- The constructed full comparison commutes with forgetting the actual deck coordinate. -/
theorem rootedCoverChain2_hurewicz (c : (cappedTreeCover q).F →₀ ℤ) :
    hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedCoverChain2 q c) = rootedAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      erw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single gf n =>
      erw [rootedCoverChain2, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, rootedAugmentedChain2, Finsupp.linearCombination_single]
      congr 1
      obtain ⟨g, f | x⟩ := gf
      · change Finsupp.mapDomain (univProj _ _).onF
          (Finsupp.single (rootedOldFace q g f) 1) =
          Finsupp.single ((markedSpineToFullCube q).onF f) 1
        erw [Finsupp.mapDomain_single]
        rfl
      · exact hurewicz_deck_faceChains _ _ _

/-- The augmented comparison of a genuine capped-cover cycle is an actual three-boundary. -/
theorem rootedAugmentedCycle_boundary3 (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨z, hz⟩ := rootedCoverCycle_fullCube_filling q c hc
  refine ⟨Finsupp.mapDomain (fun t => t.1.2) z, ?_⟩
  erw [← hurewicz_uOrdBoundary3, hz, rootedCoverChain2_hurewicz]

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev fullCubeMarkBase := (markedSpineToFullCube q).onV (markedSpineBase q)
abbrev fullCubeMarkCover := uCover (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)

def fullCubeBaseCapChain (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  fullCubeCoverCapChain q x (UV.base _ (fullCubeMarkBase q)) rfl

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev markingOldCover :=
  uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q))

/-- The marking correction is supported on actual old-block cover faces. -/
theorem exists_lifted_marking_correction (x : Fin q × Bool) :
    ∃ d : (markingOldCover q).F →₀ ℤ,
      Comb.bdry2 (fullCubeMarkCover q)
        (chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) d) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) -
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  have hp := (spineMarkedLoop_toOld_htpy q x).symm.isPath
    (isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2)))
  obtain ⟨d, hd⟩ := @exists_mapped_lifted_homotopy_chain
    (orderCx (QOld (cmpRel (GenusVertex q)))) (orderCx (QCube (cmpRel (GenusVertex q))))
    (posQCube (gBase q)) (oldToFullCube q)
    (UV.base (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)))
    (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1)
    (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)))
    (posQCube (gBase q)) hp (spineMarkedLoop_toOld_htpy q x)
  refine ⟨d, ?_⟩
  have he1 : mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1) =
      mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1 := by
    convert congrArg (fun p => mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) p)) (markedSpineLoop_inclusion q x).symm using 1 <;>
      simp only [markedSpineToFullCube, mapPath, Hom.comp, List.map_map, Function.comp_def] <;> rfl
  have he2 : mapPath (oldToFullCube q)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) =
      mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)) := by
    simp only [mapPath, List.map_map]
    rfl
  erw [he1, he2] at hd
  exact hd

def liftedMarkingCorrection (x : Fin q × Bool) :
    (markingOldCover q).F →₀ ℤ :=
  Classical.choose (exists_lifted_marking_correction q x)

theorem liftedMarkingCorrection_boundary (x : Fin q × Bool) :
    Comb.bdry2 (fullCubeMarkCover q)
      (chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q)))
        (liftedMarkingCorrection q x)) =
    pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
      (UV.base _ (fullCubeMarkBase q))) -
    pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
      (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
      (UV.base _ (fullCubeMarkBase q))) :=
  Classical.choose_spec (exists_lifted_marking_correction q x)

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)
  {o : Q} (k : UV (orderCx Q) o) (hk : endV k = c)

def coneCoverReference (a : P) : UV (orderCx Q) o :=
  extend (coneRadial f c hc a, true) k

include hk
omit [Preorder P] in
theorem coneCoverReference_end (a : P) :
    endV (coneCoverReference f c hc k a) = f a :=
  endV_extend hk

/-- The actual surface edge connects the reference vertices in the lifted cone fan. -/
theorem coneCoverReference_edge (e : (orderCx P).E) :
    extend ((orderCxMap f hf).onE e, true) (coneCoverReference f c hc k e.1.1) =
      coneCoverReference f c hc k e.1.2 := by
  let t := coneEdgeTriangle f hf c hc e
  have ht  := hk
  have hloop := extendList_att (f := t) ht
  change extend (coneRadial f c hc e.1.2, false)
    (extend ((orderCxMap f hf).onE e, true)
      (coneCoverReference f c hc k e.1.1)) = k at hloop
  have hsrc : endV (coneCoverReference f c hc k e.1.1) =
      germSrc (orderCx Q).src (orderCx Q).tgt ((orderCxMap f hf).onE e, true) := by
    rw [coneCoverReference_end f c hc k hk]
    rfl
  have hend  :=
    endV_extend hsrc
  have h := congrArg (extend (coneRadial f c hc e.1.2, true)) hloop
  have hcancel := extend_revGerm (eb := (coneRadial f c hc e.1.2, false)) hend
  change extend (coneRadial f c hc e.1.2, true)
    (extend (coneRadial f c hc e.1.2, false) _) = _ at hcancel
  rw [hcancel] at h
  exact h

def coneCoverRadialEdge (a : P) : (uCover (orderCx Q) o).E :=
  ⟨(k, coneRadial f c hc a), hk⟩

def coneCoverSurfaceEdge (e : (orderCx P).E) : (uCover (orderCx Q) o).E :=
  ⟨(coneCoverReference f c hc k e.1.1, (orderCxMap f hf).onE e), by
    rw [coneCoverReference_end f c hc k hk]
    rfl⟩

def coneCoverFace (e : (orderCx P).E) : (uCover (orderCx Q) o).F :=
  ⟨(k, coneEdgeTriangle f hf c hc e), hk⟩

/-- The lifted cone triangle has the two radial edges and the actual surface edge as boundary. -/
theorem coneCoverFace_att (e : (orderCx P).E) :
    uAtt (coneCoverFace f hf c hc k hk e) =
      [(coneCoverRadialEdge f c hc k hk e.1.1, true),
       (coneCoverSurfaceEdge f hf c hc k hk e, true),
       (coneCoverRadialEdge f c hc k hk e.1.2, false)] := by
  have hs : endV (coneCoverReference f c hc k e.1.1) =
      germSrc (orderCx Q).src (orderCx Q).tgt ((orderCxMap f hf).onE e, true) := by
    rw [coneCoverReference_end f c hc k hk]
    rfl
  have hb : endV (coneCoverReference f c hc k e.1.2) =
      germSrc (orderCx Q).src (orderCx Q).tgt (coneRadial f c hc e.1.2, false) :=
    coneCoverReference_end f c hc k hk _
  have he := coneCoverReference_edge f hf c hc k hk e
  have hcancel := extend_revGerm (eb := (coneRadial f c hc e.1.2, true)) hk
  change extend (coneRadial f c hc e.1.2, false)
    (coneCoverReference f c hc k e.1.2) = k at hcancel
  change uLiftPath [(coneRadial f c hc e.1.1, true),
    ((orderCxMap f hf).onE e, true), (coneRadial f c hc e.1.2, false)] k = _
  rw [uLiftPath_cons hk]
  change (Comb.liftGerm k (coneRadial f c hc e.1.1, true) hk) ::
    uLiftPath [((orderCxMap f hf).onE e, true), (coneRadial f c hc e.1.2, false)]
      (coneCoverReference f c hc k e.1.1) = _
  rw [uLiftPath_cons hs, he, uLiftPath_cons hb, uLiftPath_nil]
  simp only [Comb.liftGerm, hcancel]
  rfl

/-- Exact cellular boundary of the actual lifted cone triangle. -/
theorem coneCoverFace_boundary (e : (orderCx P).E) :
    bdry2 (uCover (orderCx Q) o) (Finsupp.single (coneCoverFace f hf c hc k hk e) (1 : ℤ)) =
      Finsupp.single (coneCoverSurfaceEdge f hf c hc k hk e) (1 : ℤ) +
      Finsupp.single (coneCoverRadialEdge f c hc k hk e.1.1) (1 : ℤ) -
      Finsupp.single (coneCoverRadialEdge f c hc k hk e.1.2) (1 : ℤ) := by
  rw [bdry2_single, one_smul]
  change pathChain (uAtt (coneCoverFace f hf c hc k hk e)) = _
  rw [coneCoverFace_att]
  simp [pathChain_cons]
  abel

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)
  {o : Q} (k : UV (orderCx Q) o) (hk : endV k = c)

def coneCoverFan :
    ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((uCover (orderCx Q) o).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneCoverFace f hf c hc k hk e) 1)

def coneCoverPath (p : List ((orderCx P).E × Bool)) :
    List ((uCover (orderCx Q) o).E × Bool) :=
  p.map (fun eb => (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2))

/-- A lifted fan has the surface path boundary plus the initial radial edge minus the final one. -/
theorem coneCoverFan_path_boundary {a b : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (coneCoverPath f hf c hc k hk p) +
      Finsupp.single (coneCoverRadialEdge f c hc k hk a : (uCover (orderCx Q) o).E) (1 : ℤ) -
      Finsupp.single (coneCoverRadialEdge f c hc k hk b : (uCover (orderCx Q) o).E) (1 : ℤ) := by
  induction p generalizing a with
  | nil => subst b; simp [coneCoverPath]
  | cons eb p ih =>
      obtain ⟨ha, hp⟩ := hp
      subst a
      rw [pathChain_cons, map_add, map_add, ih hp]
      obtain ⟨e, d⟩ := eb
      cases d
      · have he := coneCoverFace_boundary f hf c hc k hk e
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [map_neg, map_neg]
        rw [coneCoverFan, Finsupp.linearCombination_single, one_smul, he]
        simp [coneCoverPath, pathChain_cons, germSrc, germTgt, orderCx]
        abel
      · have he := coneCoverFace_boundary f hf c hc k hk e
        simp
        rw [coneCoverFan, Finsupp.linearCombination_single, one_smul, he]
        simp [coneCoverPath, pathChain_cons, germSrc, germTgt, orderCx]
        abel

/-- The radial terms cancel for a loop, giving a concrete finite universal-cover filling. -/
theorem coneCoverFan_loop_boundary {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (coneCoverPath f hf c hc k hk p) := by
  rw [coneCoverFan_path_boundary f hf c hc k hk hp]
  abel



/-- The fan's surface path is an actual path between the lifted reference vertices. -/
theorem coneCoverPath_isPath {a b : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    IsPath (uCover (orderCx Q) o).src (uCover (orderCx Q) o).tgt
      (coneCoverPath f hf c hc k hk p)
      (coneCoverReference f c hc k a) (coneCoverReference f c hc k b) := by
  induction p generalizing a with
  | nil => subst b; rfl
  | cons eb p ih =>
      obtain ⟨ha, hp⟩ := hp
      subst a
      constructor
      · exact (show germSrc (uCover (orderCx Q) o).src (uCover (orderCx Q) o).tgt
      (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2) =
      coneCoverReference f c hc k (germSrc (orderCx P).src (orderCx P).tgt eb) by
        obtain ⟨e, d⟩ := eb
        cases d
        · exact coneCoverReference_edge f hf c hc k hk e
        · rfl).symm
      · rw [(show germTgt (uCover (orderCx Q) o).src (uCover (orderCx Q) o).tgt
      (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2) =
      coneCoverReference f c hc k (germTgt (orderCx P).src (orderCx P).tgt eb) by
        obtain ⟨e, d⟩ := eb
        cases d
        · rfl
        · exact coneCoverReference_edge f hf c hc k hk e)]
        exact ih hp

/-- The fan follows the canonical actual lift of the included surface path. -/
theorem coneCoverPath_eq_lift {a b : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    coneCoverPath f hf c hc k hk p =
      uLiftPath (mapPath (orderCxMap f hf) p) (coneCoverReference f c hc k a) := by
  have h := eq_uLiftPath_of_isPath _ _ _ (coneCoverPath_isPath f hf c hc k hk hp)
  have he : mapPath (univProj (orderCx Q) o) (coneCoverPath f hf c hc k hk p) =
      mapPath (orderCxMap f hf) p := by
    simp only [mapPath, coneCoverPath, List.map_map]
    rfl
  rw [he] at h
  exact h

/-- The explicit lifted fan fills the canonical universal-cover lift of any surface loop. -/
theorem coneCoverFan_loop_lift_boundary {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (uLiftPath (mapPath (orderCxMap f hf) p) (coneCoverReference f c hc k a)) := by
  rw [coneCoverFan_loop_boundary f hf c hc k hk hp, coneCoverPath_eq_lift f hf c hc k hk hp]

/-- Forgetting the deck coordinate gives exactly the explicit ordinary cone fan. -/
theorem coneCoverFan_hurewicz (z : (orderCx P).E →₀ ℤ) :
    hurewicz (orderCx Q) o (coneCoverFan f hf c hc k hk z) = coneEdgeChain f hf c hc z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single e n =>
      rw [coneCoverFan, coneEdgeChain, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, map_smul]
      congr 1
      change Finsupp.mapDomain (univProj (orderCx Q) o).onF
        (Finsupp.single (coneCoverFace f hf c hc k hk e) 1) =
          Finsupp.single (coneEdgeTriangle f hf c hc e) 1
      rw [Finsupp.mapDomain_single]
      rfl

end FiniteChains.Comb
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def markingCornerLift :
    UV (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q) :=
  extend (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
    (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)
    (UV.base _ (fullCubeMarkBase q))

theorem markingCornerLift_end : endV (markingCornerLift q) =
    positiveCorner (cmpRel (GenusVertex q)) :=
  endV_extend (by rfl)

theorem markingCornerLift_reference_base :
    coneCoverReference (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q) (gBase q) =
      UV.base _ (fullCubeMarkBase q) := by
  have h := extend_revGerm
    (c := UV.base _ (fullCubeMarkBase q))
    (eb := (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)) (by rfl)
  exact h

def markingCoverConeFan (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  coneCoverFan (surfaceFullCube (cmpRel (GenusVertex q))) (surfaceFullCube_monotone _)
    (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q)
    (markingCornerLift_end q) (pathChain (gSig q (x.1.val, x.2)))


def markingOldImage (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) (liftedMarkingCorrection q x)

def controlledCoverCap (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  markingOldImage q x + markingCoverConeFan q x

/-- The old-cover correction and the controlled cone fan fill the exact lifted cap loop. -/
theorem controlledCoverCap_boundary (x : Fin q × Bool) :
    Comb.bdry2 (fullCubeMarkCover q) (controlledCoverCap q x) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) := by
  erw [controlledCoverCap, map_add, markingOldImage, liftedMarkingCorrection_boundary, (show Comb.bdry2 (fullCubeMarkCover q) (markingCoverConeFan q x) =
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) by
    erw [markingCoverConeFan, coneCoverFan_loop_lift_boundary _ _ _ _ _ _
      (isPath_gSig q (x.1.val, x.2)), markingCornerLift_reference_base])]
  abel

/-- Its projection splits into old-block faces and the explicit positive-corner cone fan. -/
theorem controlledCoverCap_hurewicz (x : Fin q × Bool) :
    hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) =
      chain2 (oldToFullCube q) (hurewicz _ (posQCube (gBase q)) (liftedMarkingCorrection q x)) +
        surfaceCornerFan (cmpRel (GenusVertex q)) (pathChain (gSig q (x.1.val, x.2))) := by
  erw [controlledCoverCap, map_add]
  apply congrArg₂ (· + ·)
  · exact hurewicz_univLift_chain2 (posQCube (gBase q)) (oldToFullCube q)
      (liftedMarkingCorrection q x)
  · erw [markingCoverConeFan, coneCoverFan_hurewicz]
    rfl

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Two fillings of the same cover chain differ by an actual lifted three-boundary. -/
theorem fillings_difference_boundary3 (A : CommRel V) (b : QCube A)
    (c d : (uCover (orderCx (QCube A)) b).F →₀ ℤ)
    (h : Comb.bdry2 (uCover (orderCx (QCube A)) b) c =
      Comb.bdry2 (uCover (orderCx (QCube A)) b) d) :
    ∃ y : UOrdTet (QCube A) b →₀ ℤ, uOrdBoundary3 y = c - d := by
  apply exists_universal_bdry3_of_cycle_qCube A b
  simp_all

/-- Projected fillings of the same lifted boundary differ by an ordinary three-boundary. -/
theorem projected_fillings_difference_boundary3 (A : CommRel V) (b : QCube A)
    (c d : (uCover (orderCx (QCube A)) b).F →₀ ℤ)
    (h : Comb.bdry2 (uCover (orderCx (QCube A)) b) c =
      Comb.bdry2 (uCover (orderCx (QCube A)) b) d) :
    ∃ y : OrdTet (QCube A) →₀ ℤ,
      ordBoundary3 y = hurewicz (orderCx (QCube A)) b c -
        hurewicz (orderCx (QCube A)) b d := by
  obtain ⟨y, hy⟩ := fillings_difference_boundary3 A b c d h
  refine ⟨Finsupp.mapDomain (fun t : UOrdTet (QCube A) b => t.1.2) y, ?_⟩
  rw [← hurewicz_uOrdBoundary3, hy, map_sub]

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]




def controlledAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)

def controlledAugmentedChain2 :
    ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (controlledAugmentedFace q)

/-- Replacing all chosen cap fillings by controlled fillings changes the comparison
only by an ordinary three-boundary. -/
theorem augmentedComparison_difference_boundary3 (c : (cappedSpineCx q).F →₀ ℤ) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedChain2 q c - controlledAugmentedChain2 q c := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add c d hc hd =>
      obtain ⟨y, hy⟩ := hc
      obtain ⟨z, hz⟩ := hd
      refine ⟨y + z, ?_⟩
      erw [map_add, hy, hz, map_add, map_add]
      abel
  | single f n =>
      obtain f | x := f
      · refine ⟨0, ?_⟩
        simp [rootedAugmentedChain2, controlledAugmentedChain2,
          rootedAugmentedFace, controlledAugmentedFace]
      · obtain ⟨y, hy⟩ := (show ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedFace q (.inr x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) by
        change ∃ y, ordBoundary3 y =
          hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
            (rootedBaseCapFilling q x) - _
        erw [(show hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x) =
    hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) by
          have haux a
              ha :
              hurewicz _ a (fullCubeCoverCapChain q x (UV.base (orderCx (QCube (cmpRel (GenusVertex q)))) a) ha) =
                hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) := by
            have he : a = fullCubeMarkBase q := ha
            subst a
            rfl
          unfold rootedBaseCapFilling SpanningTree.mappedTreeReference
          simp only [← markedSpineTree_root q, SpanningTree.treePath_root, mapPath,
            List.map_nil, extendList_nil]
          exact haux _ _)]
        exact (by
          apply projected_fillings_difference_boundary3
          erw [fullCubeBaseCapChain, fullCubeCoverCapChain_boundary, controlledCoverCap_boundary]))
        refine ⟨n • y, ?_⟩
        erw [map_smul, hy, rootedAugmentedChain2, controlledAugmentedChain2,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
        rfl

/-- The controlled comparison of every actual capped-cover cycle is a three-boundary. -/
theorem controlledAugmentedCycle_boundary3 (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = controlledAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨y, hy⟩ := rootedAugmentedCycle_boundary3 q c hc
  obtain ⟨z, hz⟩ := augmentedComparison_difference_boundary3 q
    (Finsupp.mapDomain Prod.snd c)
  refine ⟨y - z, ?_⟩
  simp_all

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

/-- Every homogeneous old-cover two-cycle is represented by an actual cycle on
the actual covered spine, modulo an actual increasing three-boundary. -/
theorem genus_old_cover_spine_nerve_generation (hf : IsPosetCover f)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hcyc : Nerve.bdry z = 0) :
    ∃ c ∈ Inc (OldCoveredSpine q f), lengthProjection 3 c = c ∧
      Nerve.bdry c = 0 ∧ ∃ y ∈ Inc P,
        z = cmap (oldCoveredSpineToOld q f) c + Nerve.bdry y := by
  let B := fun p => truncatedCoverProjection f p ∈ genusSpineCellSet q
  let s := truncatedCoverSection f
  let r := truncatedCoverRetraction f
  let z' := cmap s z
  have hs := truncatedCoverSection_monotone f hf.mono
  have hr := posetPullbackOriginal_monotone f truncatedCellRetraction
  have hz' : z' ∈ IncOn (fun _ : TruncatedCover f => True) :=
    cmap_mem_incOn_of_maps hs (fun _ => True.intro) hz
  have hd' : lengthProjection 3 z' = z' := by
    erw [lengthProjection_cmap, hd]
  have hcyc' : Nerve.bdry z' = 0 := by
    erw [← cmap_bdry, hcyc, map_zero]
  obtain ⟨c₀, hc₀, y₀, hy₀, hcc₀, he₀⟩ :=
    (genusSpine_cover_homology q (truncatedCoverProjection_isPosetCover f hf)).1
      z' hz' hd' hcyc'
  let b := lengthProjection 3 c₀
  let y := lengthProjection 4 y₀
  have hb : b ∈ IncOn B := lengthProjection_mem_incOn _ hc₀
  have hy : y ∈ Inc (TruncatedCover f) :=
    lengthProjection_mem_inc _ (incOn_le_inc _ hy₀)
  have hbd : lengthProjection 3 b = b := lengthProjection_idempotent _ _
  have hbc : Nerve.bdry b = 0 := by
    rw (config := { transparency := .default }) [← lengthProjection_bdry, hcc₀, map_zero]
  have he : z' = b + Nerve.bdry y := by
    rw (config := { transparency := .default }) [← hd', he₀, map_add, lengthProjection_bdry]
  have hne : ∃ p : TruncatedCover f, B p := by
    obtain ⟨p, hp⟩ := (truncatedCoverProjection_isPosetCover f hf).surj (spineBase q).1
    refine ⟨p, ?_⟩
    change truncatedCoverProjection f p ∈ genusSpineCellSet q
    rw (config := { transparency := .default }) [hp]
    exact (spineBase q).2
  obtain ⟨c, hc, hcb⟩ := exists_preimage_of_mem_incOn B hb
  have hcd : lengthProjection 3 c = c := by
    apply cmap_val_injective B hne
    rw (config := { transparency := .default }) [← lengthProjection_cmap, hcb, hbd]
  have hcc : Nerve.bdry c = 0 := by
    apply cmap_val_injective B hne
    rw (config := { transparency := .default }) [cmap_bdry, hcb, hbc, map_zero]
  refine ⟨c, hc, hcd, hcc, cmap r y, cmap_mem_inc_of_monotone hr hy, ?_⟩
  have hp := congrArg (cmap r) he
  have hreturn : cmap r z' = z := by
    rw (config := { transparency := .default }) [cmap_comp]
    change cmap id z = z
    exact cmap_id z
  rw (config := { transparency := .default }) [hreturn, map_add, cmap_bdry, ← hcb, cmap_comp] at hp
  exact hp

/-- The preceding geometric representative can be made strictly cellular.
Degenerate flags are removed with the explicit normalization three-chain. -/
theorem genus_old_cover_spine_cycle_generation (hf : IsPosetCover f)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hcyc : Nerve.bdry z = 0) :
    ∃ c : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) c = 0 ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 c)) + Nerve.bdry y := by
  obtain ⟨b, hb, hbd, hbc, y, hy, he⟩ :=
    genus_old_cover_spine_nerve_generation q f hf z hz hd hcyc
  let a := decodeOrdNerve2 b
  have ha : ordNerveChain2 a = b := by
    erw [ordNerveChain2_decode hb, hbd]
  have hac  :=
    (ordNerveChain2_cycle_iff a).mp (by erw [ha]; exact hbc)
  let w := ordNerveChain3 (ordNormalizationHomotopy2 a)
  have hw : w ∈ Inc (OldCoveredSpine q f) := ordNerveChain3_mem_inc _
  have hwb : b - ordNerveChain2 (ordStrictInclusion2 (normalizeOrdChain2 a)) =
      Nerve.bdry w := by
    erw [← ha]
    exact ordNerve_normalization_cycle a hac
  let g := oldCoveredSpineToOld q f
  have hg := oldCoveredSpineToOld_monotone q f
  refine ⟨normalizeOrdChain2 a, normalizeOrdChain2_cycle a hac,
    cmap g w + y, (Inc _).add_mem (cmap_mem_inc_of_monotone hg hw) hy, ?_⟩
  erw [map_add, ← cmap_bdry, ← hwb, map_sub, he]
  abel

/-- Any spine filling can be adjusted by an actual spine cycle so that its
old-cover realization represents a prescribed geometric filling of the same
boundary. This is the normalization needed when choosing the marked reference
filling before arbitrary substitutions. -/
theorem genus_old_cover_spine_adjust_filling (hf : IsPosetCover f)
    (d : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry (cmap (oldCoveredSpineToOld q f)
      (ordNerveChain2 (ordStrictInclusion2 d)))) :
    ∃ d' : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d' =
        Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 d')) + Nerve.bdry y := by
  let g := oldCoveredSpineToOld q f
  let b := cmap g (ordNerveChain2 (ordStrictInclusion2 d))
  have hbi : b ∈ Inc P := cmap_mem_inc_of_monotone
    (oldCoveredSpineToOld_monotone q f) (ordNerveChain2_mem_inc _)
  have hbd : lengthProjection 3 b = b := by
    erw [lengthProjection_cmap, ordNerveChain2_lengthProjection]
  have hzd : lengthProjection 3 (z - b) = z - b := by
    erw [map_sub, hd, hbd]
  have hzc : Nerve.bdry (z - b) = 0 := by
    erw [map_sub, hb, sub_self]
  obtain ⟨c, hc, y, hy, he⟩ := genus_old_cover_spine_cycle_generation q f hf
    (z - b) ((Inc _).sub_mem hz hbi) hzd hzc
  refine ⟨d + c, ?_, y, hy, ?_⟩
  · erw [map_add, hc, add_zero]
  · grind

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

def spineSignVertex (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0) : GenusSpineCell q :=
  ⟨Sum.inl (vtxCube ξ hξ), genusSpineCellSet_of_dimension_lt_two q _ (by
    simp [truncatedCellDimension, vtxCube])⟩

def spineSignEdge (v : GenusVertex q) (ξ : GenusVertex q → ZMod 2) : GenusSpineCell q :=
  ⟨Sum.inl (oneCube v ξ), genusSpineCellSet_of_dimension_lt_two q _ (by
    simp [truncatedCellDimension, oneCube])⟩

theorem spineReach_refl (a : GenusSpineCell q) :
    Reach (orderCx (GenusSpineCell q)) a a := reach_self _ _

theorem spineReach_trans {a b c : GenusSpineCell q}
    (h : Reach (orderCx (GenusSpineCell q)) a b)
    (h' : Reach (orderCx (GenusSpineCell q)) b c) :
    Reach (orderCx (GenusSpineCell q)) a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨r, hr⟩ := h'
  exact ⟨p ++ r, hp.append hr⟩

theorem spineReach_le {a b : GenusSpineCell q} (h : a ≤ b) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordPos h], isPath_ordPos h⟩

theorem spineReach_ge {a b : GenusSpineCell q} (h : b ≤ a) :
    Reach (orderCx (GenusSpineCell q)) a b := ⟨[ordNeg h], isPath_ordNeg h⟩

theorem spineSignVertex_flip (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0)
    (v : GenusVertex q) (b : ZMod 2) (h' : Function.update ξ v b ≠ 0) :
    Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
      (spineSignVertex q (Function.update ξ v b) h') :=
  spineReach_trans q
    (spineReach_le q (b := spineSignEdge q v ξ) (vtxCube_le_oneCube hξ v))
    (spineReach_ge q (vtxCube_update_le_oneCube (ξ := ξ) v b h'))

/-- Sign changes stay inside the actual surviving one-skeleton. -/
theorem spineSignVertex_to_unit (v₀ : GenusVertex q) :
    ∀ (n : ℕ) (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0),
      ξ v₀ = 1 → (sgnSupport ξ).card = n →
      Reach (orderCx (GenusSpineCell q)) (spineSignVertex q ξ hξ)
        (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ξ hξ hv₀ hcard
    by_cases hsupp : ∀ w, ξ w ≠ 0 → w = v₀
    · have hxi : ξ = unitSgn v₀ := by
        funext w
        by_cases hw : w = v₀
        · subst w
          simp [unitSgn, hv₀]
        · have hz : ξ w = 0 := by
            by_contra hne
            exact hw (hsupp w hne)
          simp [unitSgn, hw, hz]
      subst ξ
      exact spineReach_refl q _
    · push_neg at hsupp
      obtain ⟨w, hw, hwv⟩ := hsupp
      let ξ' := Function.update ξ w 0
      have hξ'v₀ : ξ' v₀ = 1 := by
        simp only [ξ', Function.update_apply, if_neg (Ne.symm hwv), hv₀]
      have hξ'ne : ξ' ≠ 0 := by
        intro h
        simpa [hξ'v₀] using congrFun h v₀
      have hsub : sgnSupport ξ' ⊂ sgnSupport ξ := by
        constructor
        · intro x hx
          rw [mem_sgnSupport] at hx ⊢
          by_cases hxw : x = w
          · subst x
            simp [ξ'] at hx
          · simpa only [ξ', Function.update_apply, if_neg hxw] using hx
        · intro hle
          have hh  := hle (mem_sgnSupport.2 hw)
          rw [mem_sgnSupport] at hh
          simp [ξ'] at hh
      have hlt : (sgnSupport ξ').card < n := by
        rw [← hcard]
        exact Finset.card_lt_card hsub
      exact spineReach_trans q (spineSignVertex_flip q ξ hξ w 0 hξ'ne)
        (ih _ hlt ξ' hξ'ne hξ'v₀ rfl)


/-- Every surviving cell reaches a retained sign vertex by genuine comparabilities. -/


theorem genusSpineCx_isConnected : IsConnected (genusSpineCx q) :=
  strictOrderCx_isConnected (by
    let v₀ := cV (gc q) (cyc (8 * q) 0)
    have hbase (c : GenusSpineCell q) : Reach (orderCx (GenusSpineCell q)) c
        (spineSignVertex q (unitSgn v₀) (unitSgn_ne_zero v₀)) := by
      obtain ⟨ξ, hξ, hc⟩ := (show ∃ (ξ : GenusVertex q → ZMod 2) (hξ : ξ ≠ 0),
      Reach (orderCx (GenusSpineCell q)) c (spineSignVertex q ξ hξ) by
        obtain ⟨c, hc⟩ := c
        cases c with
        | inl c =>
            by_cases hs : c.1.spx = ∅
            · have hne  := fun h => c.2 ⟨hs, h⟩
              refine ⟨c.1.sgn, hne, ?_⟩
              have he : c = vtxCube c.1.sgn hne := by
                apply Subtype.ext
                exact QCube.ext' hs (fun _ _ => rfl)
              have hv : (⟨Sum.inl c, hc⟩ : GenusSpineCell q) = spineSignVertex q c.1.sgn hne :=
                Subtype.ext (congrArg Sum.inl he)
              rw [hv]
              exact spineReach_refl q _
            · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
              have hne : Function.update c.1.sgn v 1 ≠ 0 := by
                intro h
                simpa using congrFun h v
              refine ⟨Function.update c.1.sgn v 1, hne, spineReach_ge q ?_⟩
              refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
              have hwv : w ≠ v := fun h => hw (h ▸ hv)
              simp [vtxCube, hwv]
        | inr σ =>
            obtain ⟨v, hv⟩ := σ.2.1
            let s := spineCutSingleton q v
            let e := spineSignEdge q v 0
            have hsc : s ≤ (⟨Sum.inr σ, hc⟩ : GenusSpineCell q) := by
              change ({v} : Finset (GenusVertex q)) ⊆ σ.1
              exact Finset.singleton_subset_iff.mpr hv
            have hse : s ≤ e := by
              change ({v} : Finset (GenusVertex q)) ⊆ {v} ∧
                Function.update (0 : GenusVertex q → ZMod 2) v 0 = 0
              exact ⟨Finset.Subset.refl _, by funext w; simp⟩
            have hve : spineSignVertex q (unitSgn v) (unitSgn_ne_zero v) ≤ e := by
              change (vtxCube (unitSgn v) (unitSgn_ne_zero v)).1 ≤ (oneCube v 0).1
              refine ⟨Finset.empty_subset _, fun w hw => ?_⟩
              have hwv : w ≠ v := fun h => hw (by rw [h]; exact Finset.mem_singleton_self v)
              simp [vtxCube, oneCube, unitSgn, hwv]
            exact ⟨unitSgn v, unitSgn_ne_zero v,
              spineReach_trans q (spineReach_ge q hsc)
                (spineReach_trans q (spineReach_le q hse) (spineReach_ge q hve))⟩)
      exact spineReach_trans q hc (by
        let ξ' := Function.update ξ v₀ 1
        have hv₀ : ξ' v₀ = 1 := by simp [ξ']
        have hξ' : ξ' ≠ 0 := by
          intro h
          simpa [hv₀] using congrFun h v₀
        exact spineReach_trans q (spineSignVertex_flip q ξ hξ v₀ 1 hξ')
          (spineSignVertex_to_unit q v₀ _ ξ' hξ' hv₀ rfl))
    intro a b
    obtain ⟨p, hp⟩ := hbase a
    obtain ⟨r, hr⟩ := hbase b
    exact ⟨p ++ revPath r, hp.append (isPath_revPath hr)⟩)

theorem markedSpine_component_onF_surjective :
    Function.Surjective (componentIncl (genusSpineCx q) (spineBase q)).onF := by
  intro t
  exact ⟨⟨t, genusSpineCx_isConnected q (spineBase q) ((genusSpineCx q).base t)⟩, rfl⟩

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.Comb
universe u
variable {K Y Z : Complex2.{u}}


theorem universal_chain2_comp (f : Hom K Y) (g : Hom Y Z) (c : K.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  change Finsupp.mapDomain (g.onF ∘ f.onF) c =
    Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
  erw [Finsupp.mapDomain_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

def universalSpineToOld :
    Hom (markedSpineCx q) (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

abbrev universalSpineOldBase :=
  (universalSpineToOld q).onV (markedSpineTree q).root


/-- The receiver is the actual geometric fundamental-group equivalence,
with named generators folded back to the tree presentation. -/
def universalSpineOldReceiver :
    PresGroup (namedSpinePresentation q) →*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q) :=
  (ReceivedTree.canonicalReceiver (markedSpineTree q) (universalSpineToOld q)).comp
    (namedSpineGroupEquiv q).symm.toMonoidHom

theorem universalSpineOldReceiver_bijective :
    Function.Bijective (universalSpineOldReceiver q) :=
  (show Function.Bijective (pi1Map (universalSpineToOld q) (markedSpineTree q).root) by
    erw [markedSpineTree_root]
    have he : pi1Map (universalSpineToOld q) (markedSpineBase q) =
        (genusSpineToOldPi1Equiv q).toMonoidHom.comp (markedSpinePi1Equiv q).toMonoidHom := by
      apply MonoidHom.ext
      intro z
      exact (show pi1Map ((genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))) (markedSpineBase q) z = pi1Map (genusSpineToOld q) ((componentIncl (genusSpineCx q) (spineBase q)).onV (markedSpineBase q)) (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q) z) by
        refine Quotient.inductionOn z ?_
        intro p
        apply congrArg Pi1.mk
        apply Subtype.ext
        simp only [mapPath, Hom.comp, List.map_map, Function.comp_def])
    erw [he]
    exact (genusSpineToOldPi1Equiv q).bijective.comp (markedSpinePi1Equiv q).bijective).comp
    ((spinePresentationPi1Equiv q).symm.bijective.comp (namedSpineGroupEquiv q).symm.bijective)

def universalSpineWordReceiver :
    PresGroup (spinePresentation q) →* PresGroup (namedSpinePresentation q) :=
  (namedSpineGroupEquiv q).toMonoidHom

theorem universalSpineOldReceiver_compatible :
    (universalSpineOldReceiver q).comp (universalSpineWordReceiver q) =
      (pi1Map (universalSpineToOld q) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) := by
  apply MonoidHom.ext
  intro z
  change (ReceivedTree.canonicalReceiver (markedSpineTree q) (universalSpineToOld q))
    ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
  erw [MulEquiv.symm_apply_apply]
  rfl

abbrev universalNamedSpineCover :=
  ReceivedTree.cover (markedSpineTree q) (universalSpineWordReceiver q)

def universalNamedSpineComparison :
    Hom (universalNamedSpineCover q)
      (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)) :=
  ReceivedTree.comparison (markedSpineTree q) (universalSpineToOld q)
    (universalSpineWordReceiver q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_compatible q)

abbrev universalOldOrder :=
  UOrder (QOld (cmpRel (GenusVertex q))) (universalSpineOldBase q)

theorem universalOldEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
      (a := universalSpineOldBase q)) := by
  letI : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩
  exact uOrderEnd_isPosetCover isConnected_orderCx_qOld

def universalReceivedOrderMap :
    Hom (universalNamedSpineCover q) (orderCx (universalOldOrder q)) :=
  uOrderHomInv.comp (universalNamedSpineComparison q)

def universalReceivedStrictSpine :
    Hom (universalNamedSpineCover q) (strictOrderCx (GenusSpineCell q)) :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (ReceivedTree.projection (markedSpineTree q) (universalSpineWordReceiver q))


abbrev universalSpinePullback :=
  PosetCoverPullback (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
    (a := universalSpineOldBase q)) (genusSpineCellToOld q)

def universalReceivedToPullback :
    Hom (universalNamedSpineCover q) (strictOrderCx (universalSpinePullback q)) :=
  strictOrderPullbackHom uOrderEnd (universalOldEnd_isPosetCover q)
    (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
    (universalReceivedOrderMap q) (universalReceivedStrictSpine q)
    (by
      apply Hom.ext'
      · funext a
        change uOrderEnd (uOrderHomInv.onV
          (ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
            (universalSpineOldReceiver q) a.1 a.2)) = _
        erw [uOrderHomInv_vertex]
        exact ReceivedTree.receiverVertex_end _ _ _ _ _
      · funext e
        exact uOrderHomInv_edge_projection
          (ReceivedTree.receiverEdge (markedSpineTree q) (universalSpineToOld q)
            (universalSpineOldReceiver q) e.1 e.2)
      · funext t
        exact uOrderHomInv_face_projection
          (ReceivedTree.receiverFace (markedSpineTree q) (universalSpineToOld q)
            (universalSpineOldReceiver q) t.1 t.2))

theorem universalPullbackFace_ext
    (t s : StrictOrdTri (universalSpinePullback q))
    (hp : (strictPullbackOriginal uOrderEnd (genusSpineCellToOld q)).onF t =
      (strictPullbackOriginal uOrderEnd (genusSpineCellToOld q)).onF s)
    (hs : (strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
        (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).onF t =
      (strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
        (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).onF s) : t = s := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun t => t.1.1) hp) (congrArg (fun t => t.1.1) hs)
  · apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun t => t.1.2.1) hp) (congrArg (fun t => t.1.2.1) hs)
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun t => t.1.2.2) hp) (congrArg (fun t => t.1.2.2) hs)

/-- Every actual pulled-back spine face has named tree-cover coordinates.
The two ingredients are full-spine connectivity and the pre-substitution
geometric receiver equivalence. -/
theorem universalReceivedToPullback_onF_surjective :
    Function.Surjective (universalReceivedToPullback q).onF := by
  intro t
  let original := strictPullbackOriginal
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))
    (genusSpineCellToOld q)
  let projection := strictPullbackProjection
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))
    (universalOldEnd_isPosetCover q) (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
  obtain ⟨s, hs⟩ := markedSpine_component_onF_surjective q (projection.onF t)
  have ht : (uOrderFace (original.onF t)).1.2 =
      (universalSpineToOld q).onF s := by
    have hpair : (uOrderFace (original.onF t)).1.2 =
        (genusSpineToOld q).onF (projection.onF t) := by
      apply Subtype.ext
      exact Prod.ext t.1.1.2 (Prod.ext t.1.2.1.2 t.1.2.2.2)
    exact hpair.trans (congrArg (genusSpineToOld q).onF hs).symm
  obtain ⟨g, hg⟩ := ReceivedTree.receiverFace_fiber_surjective
    (markedSpineTree q) (universalSpineToOld q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_bijective q).2 s (uOrderFace (original.onF t)) ht
  refine ⟨(g, s), universalPullbackFace_ext q _ t ?_ ?_⟩
  · change (universalReceivedOrderMap q).onF (g, s) = original.onF t
    apply uOrderFace_injective
    exact (homInv_onF_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ _).trans hg
  · exact hs

def universalSpinePullbackOldOrderIso :
    universalSpinePullback q ≃o OldCoveredSpine q
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)) where
  toFun x := ⟨⟨(x.1.1, x.1.2.1), x.2⟩, x.1.2.2⟩
  invFun x := ⟨(x.1.1.1, ⟨x.1.1.2, x.2⟩), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def universalReceivedToCoveredSpine :
    Hom (universalNamedSpineCover q)
      (strictOrderCx (OldCoveredSpine q
        (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)))) :=
  (strictOrderCxMap (universalSpinePullbackOldOrderIso q)
    (universalSpinePullbackOldOrderIso q).strictMono).comp (universalReceivedToPullback q)


/-- This is the concrete pre-substitution chain lift needed for the normalized
marked reference filling. It applies to every finite chain on the full geometric spine. -/
theorem universalReceivedToCoveredSpine_chain2_surjective :
    Function.Surjective (chain2 (universalReceivedToCoveredSpine q)) :=
  Finsupp.mapDomain_surjective (by
    intro t
    obtain ⟨c, hc⟩ := universalReceivedToPullback_onF_surjective q
      ((strictOrderCxMap (universalSpinePullbackOldOrderIso q).symm
        (universalSpinePullbackOldOrderIso q).symm.strictMono).onF t)
    refine ⟨c, ?_⟩
    change (strictOrderCxMap (universalSpinePullbackOldOrderIso q)
      (universalSpinePullbackOldOrderIso q).strictMono).onF
        ((universalReceivedToPullback q).onF c) = t
    erw [hc]
    apply Subtype.ext
    simp only [strictOrderCxMap, OrderIso.apply_symm_apply])

/-- Keeping the underlying spine edge and its actual initial lift retains
both coordinates of a received edge. -/

theorem universalReceivedToCoveredSpine_vertex_old
    (a : (universalNamedSpineCover q).V) :
    oldCoveredSpineToOld q uOrderEnd ((universalReceivedToCoveredSpine q).onV a) =
      (universalNamedSpineComparison q).onV a := by
  exact uOrderHomInv_vertex _


theorem universalReceivedToCoveredSpine_chain1_injective :
    Function.Injective (chain1 (universalReceivedToCoveredSpine q)) :=
  Finsupp.mapDomain_injective (by
    rintro ⟨g, e⟩ ⟨h, d⟩ he
    have hed : e = d := Subtype.ext
      (congrArg ((strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
    (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (universalSpinePullbackOldOrderIso q).symm
        (universalSpinePullbackOldOrderIso q).symm.strictMono)).onE he)
    subst d
    have hv : (universalReceivedToCoveredSpine q).onV
        ((universalNamedSpineCover q).src (g, e)) =
        (universalReceivedToCoveredSpine q).onV
          ((universalNamedSpineCover q).src (h, e)) := by
      erw [← (universalReceivedToCoveredSpine q).src_onE,
        ← (universalReceivedToCoveredSpine q).src_onE, he]
    have hv' := congrArg (oldCoveredSpineToOld q uOrderEnd) hv
    erw [universalReceivedToCoveredSpine_vertex_old,
      universalReceivedToCoveredSpine_vertex_old] at hv'
    have hg  := ReceivedTree.receiverVertex_fiber_injective
      (markedSpineTree q) (universalSpineToOld q) (universalSpineOldReceiver q)
      (universalSpineOldReceiver_bijective q).1 ((markedSpineCx q).src e) hv'
    exact Prod.ext hg rfl)

theorem universalReceivedCoveredChain_nerve_image
    (d : (universalNamedSpineCover q).F →₀ ℤ) :
    Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
      (ordNerveChain2 (ordStrictInclusion2
        (chain2 (universalReceivedToCoveredSpine q) d))) =
      universalNerveChain2 (chain2 (universalNamedSpineComparison q) d) := by
  have hfirst :
      (orderCxMap (oldCoveredSpineToOld q uOrderEnd)
        (oldCoveredSpineToOld_monotone q uOrderEnd)).comp
        ((strictOrderIncl _).comp (universalReceivedToCoveredSpine q)) =
        universalReceivedOrderMap q := by
    apply Hom.ext' <;> rfl
  change Nerve.cmap _ (ordNerveChain2 (chain2 (strictOrderIncl _)
    (chain2 (universalReceivedToCoveredSpine q) d))) =
    ordNerveChain2 (chain2 uOrderHomInv (chain2 (universalNamedSpineComparison q) d))
  erw [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q uOrderEnd)]
  apply congrArg ordNerveChain2
  have he := congrArg (fun k => chain2 k d) hfirst
  simpa only [universal_chain2_comp, universalReceivedOrderMap] using he

/-- The geometric adjustment lifts back to genuine pre-substitution tree
coordinates with its exact boundary preserved. The prescribed geometric
class is an explicit input here, rather than a claimed canonical choice. -/
theorem universalSpine_adjust_filling
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (z : Nerve.Ch (universalOldOrder q))
    (hz : z ∈ Nerve.Inc (universalOldOrder q))
    (hd : Nerve.lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry
      (Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (universalReceivedToCoveredSpine q) d))))) :
    ∃ d' : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d' = Comb.bdry2 (universalNamedSpineCover q) d ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        z = Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
          (ordNerveChain2 (ordStrictInclusion2
            (chain2 (universalReceivedToCoveredSpine q) d'))) + Nerve.bdry y := by
  obtain ⟨c, hcb, y, hy, hzy⟩ := genus_old_cover_spine_adjust_filling q
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
      (a := universalSpineOldBase q)) (universalOldEnd_isPosetCover q)
    (chain2 (universalReceivedToCoveredSpine q) d) z hz hd hb
  obtain ⟨d', hd'⟩ := universalReceivedToCoveredSpine_chain2_surjective q c
  refine ⟨d', ?_, y, hy, ?_⟩
  · apply universalReceivedToCoveredSpine_chain1_injective q
    erw [← bdry2_chain2, ← bdry2_chain2, hd']
    exact hcb
  · simp_all

/-- Cellular form of the actual geometric adjustment: equality of the
specified old-cover boundaries is sufficient, with no support premise added. -/
theorem universalSpine_adjust_to_chain
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (z : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ)
    (hz : Comb.bdry2 _ z = chain1 (universalNamedSpineComparison q)
      (Comb.bdry2 (universalNamedSpineCover q) d)) :
    ∃ d' : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d' = Comb.bdry2 (universalNamedSpineCover q) d ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        universalNerveChain2 z = universalNerveChain2
          (chain2 (universalNamedSpineComparison q) d') + Nerve.bdry y := by
  obtain ⟨d', hbd, y, hy, hzy⟩ := universalSpine_adjust_filling q d
    (universalNerveChain2 z) (universalNerveChain2_mem_inc z)
    (universalNerveChain2_lengthProjection z) (by
      erw [universalReceivedCoveredChain_nerve_image, universalNerveChain2_bdry,
        universalNerveChain2_bdry, bdry2_chain2, hz])
  refine ⟨d', hbd, y, hy, ?_⟩
  rwa [universalReceivedCoveredChain_nerve_image] at hzy

end FiniteChains.Davis.Genus
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.CoveredPolygon
open RACG Mirror Comb Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)
  {v : PolygonCoverPole hc f} (D : CoveredPolygon hc f v)

def subdivisionBoundaryEdge (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  edgeHop (D.ve p) ++ revPath (edgeHop (D.v1e p))

theorem subdivisionBoundaryEdge_isPath (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt
      (D.subdivisionBoundaryEdge hc f p) (spx1 (D.V p)) (spx1 (D.V (p + 1))) :=
  (isPath_edgeHop (D.ve p)).append (isPath_revPath (isPath_edgeHop (D.v1e p)))

def subdivisionBoundaryPath : ℕ → List ((orderCx (NeSpx (cmpRel P))).E × Bool)
  | 0 => []
  | n + 1 => subdivisionBoundaryPath n ++ D.subdivisionBoundaryEdge hc f (cyc M n)

theorem subdivisionBoundaryPath_isPath (n : ℕ) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt
      (D.subdivisionBoundaryPath hc f n) (spx1 (D.V (cyc M 0))) (spx1 (D.V (cyc M n))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih.append (D.subdivisionBoundaryEdge_isPath hc f (cyc M n))
    rw [← cyc_succ] at h
    exact h


theorem subdivisionBoundaryEdge_projection (p : Fin M) :
    mapPath (orderCxMap (barycentricMap f hf.mono) (barycentricMap_monotone f hf.mono))
      (D.subdivisionBoundaryEdge hc f p) = bdEdge hc p := by
  simp only [subdivisionBoundaryEdge, edgeHop, edgeHopRev, hop, bdEdge, revPath, revGerm,
    mapPath, List.map_append, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append]
  simp only [ordPos, ordNeg, Bool.not_false, Bool.not_true, orderCxMap,
    barycentricMap_spx1, barycentricMap_spx2, D.projV, D.projE]
  grind

theorem subdivisionBoundaryPath_projection (n : ℕ) :
    mapPath (orderCxMap (barycentricMap f hf.mono) (barycentricMap_monotone f hf.mono))
      (D.subdivisionBoundaryPath hc f n) = bdPath hc n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [subdivisionBoundaryPath, mapPath_append, ih,
      D.subdivisionBoundaryEdge_projection hc f hf, bdPath]

theorem subdivisionFundamental_boundary :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricChain2 (decodeOrdNerve2 D.fundamental)) =
      pathChain (D.subdivisionBoundaryPath hc f M) := by
  rw [barycentricChain2_boundary, D.decodedFundamental_boundary,
    (show barycentricChain1 D.boundaryEdges =
      pathChain (D.subdivisionBoundaryPath hc f M) by
      have hstep p :
          pathChain (D.subdivisionBoundaryEdge hc f p) =
            barycentricChain1 (Finsupp.single ⟨(D.V p, D.E p), D.ve p⟩ 1 -
              Finsupp.single ⟨(D.V (p + 1), D.E p), D.v1e p⟩ 1) := by
        rw [subdivisionBoundaryEdge, pathChain_append, pathChain_revPath, map_sub]
        simp [edgeHop, hop, pathChain, ordPos, ordNeg, barycentricChain1,
          barycentricEdge, sub_eq_add_neg]
      have hpath n : pathChain (D.subdivisionBoundaryPath hc f n) =
          ∑ k ∈ Finset.range n, pathChain (D.subdivisionBoundaryEdge hc f (cyc M k)) := by
        induction n with
        | zero => rfl
        | succ n ih => rw [subdivisionBoundaryPath, pathChain_append, ih, Finset.sum_range_succ]
      have hcyc i : cyc M i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [hpath]
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [hcyc]
      rw [boundaryEdges, map_sum]
      exact Finset.sum_congr rfl (fun p _ => (hstep p).symm))]

end FiniteChains.Davis.CoveredPolygon
end

namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- The sheet is multiplied on the right when a comparability is traversed. -/
structure Cover (c : OrdCocycle P G) where
  point : P
  sheet : G

instance coverPartialOrder : PartialOrder c.Cover where
  le a b := a.point ≤ b.point ∧ a.sheet * c.val a.point b.point = b.sheet
  le_refl a := ⟨le_rfl, by rw [c.val_refl, mul_one]⟩
  le_trans a b d hab hbd := ⟨hab.1.trans hbd.1, by
    rw [← c.comp hab.1 hbd.1, ← mul_assoc, hab.2, hbd.2]⟩
  le_antisymm a b hab hba := by
    have hp : a.point = b.point := le_antisymm hab.1 hba.1
    have hs : a.sheet = b.sheet := by
      simpa only [hp, c.val_refl, mul_one] using hab.2
    cases a with
    | mk ap ag =>
      cases b with
      | mk bp bg =>
        dsimp only at hp hs
        cases hp
        cases hs
        rfl

theorem coverProjection_isPosetCover : IsPosetCover (Cover.point (c := c)) := by
  refine ⟨fun _ _ h => h.1, fun p => ⟨⟨p, 1⟩, rfl⟩, ?_, ?_⟩
  · intro a p hp
    refine ⟨⟨p, a.sheet * c.val a.point p⟩, ⟨⟨hp, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨b, g⟩ ⟨h, hb⟩
    change b = p at hb
    subst b
    have hg : a.sheet * c.val a.point p = g := h.2
    cases hg
    rfl

  · intro a p hp
    refine ⟨⟨p, a.sheet * (c.val p a.point)⁻¹⟩,
      ⟨⟨hp, by simp⟩, rfl⟩, ?_⟩
    rintro ⟨b, g⟩ ⟨h, hb⟩
    change b = p at hb
    subst b
    have hg : g = a.sheet * (c.val p a.point)⁻¹ := by
      rw [← h.2]
      group
    cases hg
    rfl

/-- Left translation changes the sheet and preserves every incidence. -/
def coverDeck (g : G) : c.Cover ≃o c.Cover where
  toFun x := ⟨x.point, g * x.sheet⟩
  invFun x := ⟨x.point, g⁻¹ * x.sheet⟩
  left_inv x := by cases x; simp only [← mul_assoc, inv_mul_cancel, one_mul]
  right_inv x := by cases x; simp only [← mul_assoc, mul_inv_cancel, one_mul]
  map_rel_iff' := by
    intro x y
    change (x.point ≤ y.point ∧ (g * x.sheet) * c.val x.point y.point = g * y.sheet) ↔
      (x.point ≤ y.point ∧ x.sheet * c.val x.point y.point = y.sheet)
    simp only [mul_assoc, mul_left_cancel_iff]

variable (a : P) (hc : IsConnected (orderCx P))
  (hm : Function.Bijective (c.monodromy a))

include hc hm in
theorem exists_point_reading (p : P) (g : G) :
    ∃ v : UOrder P a, uOrderEnd v = p ∧ c.readVertex a v = g := by
  obtain ⟨v, hv⟩ := (uOrderEnd_isPosetCover hc).surj p
  obtain ⟨w, hw, hread⟩ := c.readVertex_fibre_surjective a hm.2 v g
  exact ⟨w, hw.trans hv, hread⟩

/-- Actual path class with the specified endpoint and full group reading. -/
def pointReading (p : P) (g : G) : UOrder P a :=
  Classical.choose (c.exists_point_reading a hc hm p g)

theorem pointReading_end (p : P) (g : G) :
    uOrderEnd (c.pointReading a hc hm p g) = p :=
  (Classical.choose_spec (c.exists_point_reading a hc hm p g)).1

theorem pointReading_read (p : P) (g : G) :
    c.readVertex a (c.pointReading a hc hm p g) = g :=
  (Classical.choose_spec (c.exists_point_reading a hc hm p g)).2

/-- Comparable endpoint/read pairs lift to actual comparable vertices. -/
theorem pointReading_le {p r : P} {g h : G} (hpr : p ≤ r)
    (hgh : g * c.val p r = h) :
    c.pointReading a hc hm p g ≤ c.pointReading a hc hm r h := by
  let v := c.pointReading a hc hm p g
  have hv  := c.pointReading_end a hc hm p g
  have hvp : uOrderEnd v ≤ r := by rw [hv]; exact hpr
  let w := uOrderStep v r hvp
  have hw : uOrderEnd w = r := uOrderStep_end v r _
  have hr : c.readVertex a w = h := by
    change c.readVertex a (extend (ordPos hvp) v) = h
    rw [c.readVertex_extend a _ v rfl, c.pointReading_read,
      readGerm_ordPos, hv, hgh]
  have he  :=
    c.readVertex_fibre_injective a hm.1 w _
      (hw.trans (c.pointReading_end a hc hm r h).symm)
      (hr.trans (c.pointReading_read a hc hm r h).symm)
  rw [← he]
  exact uOrderStep_le v r _

end FiniteChains.Comb.OrdCocycle

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P Q G : Type u} [PartialOrder P] [PartialOrder Q] [Group G]
  (f : NeSpx (cmpRel P) → Q) (hf : Monotone f)
  (c : OrdCocycle Q G) (a : Q) (hc : IsConnected (orderCx Q))
  (hm : Function.Bijective (c.monodromy a))

def descendedSurfaceCocycle : OrdCocycle P G :=
  barycentricCocycle (c.comap f hf)

abbrev DescendedSurfaceCover := (descendedSurfaceCocycle f hf c).Cover

def descendedSurfaceProjection : DescendedSurfaceCover f hf c → P :=
  OrdCocycle.Cover.point

theorem descendedSurfaceProjection_isPosetCover :
    IsPosetCover (descendedSurfaceProjection f hf c) :=
  (descendedSurfaceCocycle f hf c).coverProjection_isPosetCover

def descendedSurfaceSimplex
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : NeSpx (cmpRel P) :=
  barycentricMap (descendedSurfaceProjection f hf c)
    (descendedSurfaceProjection_isPosetCover f hf c).mono σ

theorem descendedSurfaceSimplex_monotone : Monotone (descendedSurfaceSimplex f hf c) :=
  barycentricMap_monotone _ (descendedSurfaceProjection_isPosetCover f hf c).mono

theorem descendedSurfaceSimplex_top
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    (chainMax σ).point ∈ (descendedSurfaceSimplex f hf c σ).1 :=
  Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩

def barycentricCoverReading
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : G :=
  (chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
    (f (descendedSurfaceSimplex f hf c σ))

/-- The top of each lifted simplex fixes the sheet of the whole flag. -/
def barycentricCoverRealization
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) : UOrder Q a :=
  c.pointReading a hc hm (f (descendedSurfaceSimplex f hf c σ))
    (barycentricCoverReading f hf c σ)

theorem barycentricCoverRealization_end
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    uOrderEnd (barycentricCoverRealization f hf c a hc hm σ) =
      f (descendedSurfaceSimplex f hf c σ) :=
  c.pointReading_end a hc hm _ _

theorem barycentricCoverRealization_read
    (σ : NeSpx (cmpRel (DescendedSurfaceCover f hf c))) :
    c.readVertex a (barycentricCoverRealization f hf c a hc hm σ) =
      barycentricCoverReading f hf c σ :=
  c.pointReading_read a hc hm _ _

theorem barycentricCoverRealization_monotone :
    Monotone (barycentricCoverRealization f hf c a hc hm) := by
  intro σ τ hστ
  have htop := chainMax_monotone hστ
  have hσ : spx1 (chainMax σ).point ≤ descendedSurfaceSimplex f hf c σ := by
    intro p hp
    simp at hp
    subst p
    exact descendedSurfaceSimplex_top f hf c σ
  have hτ :=
    descendedSurfaceSimplex_monotone f hf c hστ
  have hmσ :=
    hτ (descendedSurfaceSimplex_top f hf c σ)
  have hread := edgeHop_read_via (c.comap f hf) htop.1
    (descendedSurfaceSimplex f hf c τ) hmσ (descendedSurfaceSimplex_top f hf c τ)
  have hval : (descendedSurfaceCocycle f hf c).val (chainMax σ).point (chainMax τ).point =
      c.val (f (spx1 (chainMax σ).point)) (f (descendedSurfaceSimplex f hf c τ)) *
        (c.val (f (spx1 (chainMax τ).point)) (f (descendedSurfaceSimplex f hf c τ)))⁻¹ := by
    exact (barycentricCocycle_val (c.comap f hf) htop.1).trans hread
  apply c.pointReading_le a hc hm (hf hτ)
  change ((chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
      (f (descendedSurfaceSimplex f hf c σ))) *
      c.val (f (descendedSurfaceSimplex f hf c σ)) (f (descendedSurfaceSimplex f hf c τ)) =
    (chainMax τ).sheet * c.val (f (spx1 (chainMax τ).point))
      (f (descendedSurfaceSimplex f hf c τ))
  calc
    _ = (chainMax σ).sheet * c.val (f (spx1 (chainMax σ).point))
        (f (descendedSurfaceSimplex f hf c τ)) := by rw [mul_assoc, c.comp (hf hσ) (hf hτ)]
    _ = ((chainMax σ).sheet *
        (descendedSurfaceCocycle f hf c).val (chainMax σ).point (chainMax τ).point) *
        c.val (f (spx1 (chainMax τ).point)) (f (descendedSurfaceSimplex f hf c τ)) := by
      rw [hval]
      group
    _ = _ := by rw [htop.2]

end FiniteChains.Davis
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

local instance : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩

def universalSpineOldReceiverEquiv :
    PresGroup (namedSpinePresentation q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q) :=
  MulEquiv.ofBijective (universalSpineOldReceiver q) (universalSpineOldReceiver_bijective q)

theorem universalSpineOldBase_eq : universalSpineOldBase q = posQCube (gBase q) := by
  change (genusSpineToOld q).onV ((markedSpineTree q).root).1 = _
  erw [markedSpineTree_root]
  rfl

theorem exists_universalOldCocycle :
    ∃ c : OrdCocycle (QOld (cmpRel (GenusVertex q))) (PresGroup (namedSpinePresentation q)),
      ∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q),
        c.readPath p.1 = (universalSpineOldReceiverEquiv q).symm (Pi1.mk p) :=
  OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld (universalSpineOldBase q)
    (universalSpineOldReceiverEquiv q).symm.toMonoidHom

def universalOldCocycle := Classical.choose (exists_universalOldCocycle q)

theorem universalOldCocycle_monodromy :
    (universalOldCocycle q).monodromy (universalSpineOldBase q) =
      (universalSpineOldReceiverEquiv q).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro z
  induction z using Quotient.inductionOn with
  | h p => exact Classical.choose_spec (exists_universalOldCocycle q) p

theorem universalOldCocycle_monodromy_bijective :
    Function.Bijective ((universalOldCocycle q).monodromy (universalSpineOldBase q)) := by
  erw [universalOldCocycle_monodromy]
  exact (universalSpineOldReceiverEquiv q).symm.bijective

abbrev UniversalPolygonCover :=
  DescendedSurfaceCover (posQCube (A := cmpRel (GenusVertex q)))
    posQCube_monotone (universalOldCocycle q)

def universalPolygonProjection : UniversalPolygonCover q → GenusVertex q :=
  descendedSurfaceProjection posQCube posQCube_monotone (universalOldCocycle q)

theorem universalPolygonProjection_isPosetCover : IsPosetCover (universalPolygonProjection q) :=
  descendedSurfaceProjection_isPosetCover posQCube posQCube_monotone (universalOldCocycle q)

def universalPolygonRawPole : PolygonCoverPole (gc q) (universalPolygonProjection q) :=
  ⟨⟨cC (gc q), 1⟩, rfl⟩

def universalPolygonRaw := coveredPolygon (gc q) (universalPolygonProjection q)
  (universalPolygonProjection_isPosetCover q) (universalPolygonRawPole q)

def universalPolygonShift : UniversalPolygonCover q ≃o UniversalPolygonCover q :=
  (descendedSurfaceCocycle posQCube posQCube_monotone (universalOldCocycle q)).coverDeck
    ((universalPolygonRaw q).V (cyc (8 * q) 0)).sheet⁻¹

def universalPolygonPole : PolygonCoverPole (gc q) (universalPolygonProjection q) :=
  CoveredPolygon.mapPole (gc q) (universalPolygonProjection q) (universalPolygonProjection q)
    (universalPolygonShift q) (fun _ => rfl) (v := universalPolygonRawPole q)

/-- All polygon positions are translated together so the first boundary
vertex is in the identity sheet. The actual polygon orientation is retained. -/
def universalPolygon : CoveredPolygon (gc q) (universalPolygonProjection q)
    (universalPolygonPole q) :=
  (universalPolygonRaw q).map (gc q) (universalPolygonProjection q)
    (universalPolygonProjection q) (universalPolygonShift q)
    (universalPolygonShift q).monotone (fun _ => rfl)

theorem universalPolygon_initial_sheet :
    ((universalPolygon q).V (cyc (8 * q) 0)).sheet = 1 := inv_mul_cancel _

def universalPolygonRealization :
    NeSpx (cmpRel (UniversalPolygonCover q)) → universalOldOrder q :=
  barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q)

theorem universalPolygonRealization_monotone : Monotone (universalPolygonRealization q) :=
  barycentricCoverRealization_monotone posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q)

def universalPolygonLift :
    Hom (orderCx (NeSpx (cmpRel (UniversalPolygonCover q))))
      (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)) :=
  uOrderHom.comp (orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q))

theorem universalPolygonRealization_end (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    uOrderEnd (universalPolygonRealization q σ) =
      posQCube (barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ) :=
  barycentricCoverRealization_end posQCube posQCube_monotone (universalOldCocycle q)
    (universalSpineOldBase q) isConnected_orderCx_qOld
    (universalOldCocycle_monodromy_bijective q) σ

theorem universalPolygonLift_projects :
    (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)).comp
      (universalPolygonLift q) =
      (surfCx (cmpRel (GenusVertex q))).comp
        (orderCxMap (barycentricMap (universalPolygonProjection q)
          (universalPolygonProjection_isPosetCover q).mono)
          (barycentricMap_monotone _ (universalPolygonProjection_isPosetCover q).mono)) := by
  apply Hom.ext'
  · funext σ
    exact universalPolygonRealization_end q σ
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalPolygonRealization_end q e.1.1)
      (universalPolygonRealization_end q e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalPolygonRealization_end q t.1.1)
      (Prod.ext (universalPolygonRealization_end q t.1.2.1)
        (universalPolygonRealization_end q t.1.2.2))

theorem universalPolygonLift_initial :
    (universalPolygonLift q).onV (spx1 ((universalPolygon q).V (cyc (8 * q) 0))) =
      UV.base _ (universalSpineOldBase q) := by
  apply (universalOldCocycle q).readVertex_fibre_injective (universalSpineOldBase q)
    (universalOldCocycle_monodromy_bijective q).1
  · change uOrderEnd (universalPolygonRealization q _) = _
    erw [universalPolygonRealization_end, barycentricMap_spx1,
      (universalPolygon q).projV, endV_base, universalSpineOldBase_eq]
    rfl
  · change (universalOldCocycle q).readVertex (universalSpineOldBase q)
      (barycentricCoverRealization posQCube posQCube_monotone (universalOldCocycle q)
        (universalSpineOldBase q) isConnected_orderCx_qOld
        (universalOldCocycle_monodromy_bijective q) _) = _
    erw [barycentricCoverRealization_read]
    simp only [barycentricCoverReading, chainMax_spx1, descendedSurfaceSimplex,
      barycentricMap_spx1, descendedSurfaceProjection, OrdCocycle.val_refl, mul_one,
      universalPolygon_initial_sheet, OrdCocycle.readVertex_base]

/-- The subdivided source polygon, now in actual old universal-cover cells. -/
def universalOldPolygonChain :
    (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)).F →₀ ℤ :=
  chain2 (universalPolygonLift q)
    (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental))

theorem universalOldPolygonChain_boundary :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      pathChain (uLiftPath (mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)))
        (UV.base _ (universalSpineOldBase q))) := by
  erw [universalOldPolygonChain, bdry2_chain2,
    (universalPolygon q).subdivisionFundamental_boundary (gc q) (universalPolygonProjection q)]
  change Finsupp.mapDomain (universalPolygonLift q).onE (pathChain _) = _
  erw [← pathChain_map]
  apply congrArg pathChain
  have hp := isPath_mapPath (universalPolygonLift q)
    ((universalPolygon q).subdivisionBoundaryPath_isPath (gc q) (universalPolygonProjection q) (8 * q))
  erw [universalPolygonLift_initial] at hp
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath (univProj (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (mapPath (universalPolygonLift q)
        ((universalPolygon q).subdivisionBoundaryPath (gc q) (universalPolygonProjection q) (8 * q))) =
      mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
    erw [mapPath_comp, universalPolygonLift_projects, ← mapPath_comp,
      (universalPolygon q).subdivisionBoundaryPath_projection (gc q)
        (universalPolygonProjection q) (universalPolygonProjection_isPosetCover q)]
    congr 2 <;> exact Subsingleton.elim _ _
  erw [hproj] at he
  exact he

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem cellularOrderHom_vertex_monotone (f : Hom (orderCx P) (orderCx Q)) :
    Monotone (show P → Q from f.onV) := by
  intro a b hab
  let e : OrdEdge P := ⟨(a, b), hab⟩
  have h := (f.onE e).2
  have hs : (f.onE e).1.1 = f.onV a := f.src_onE e
  have ht : (f.onE e).1.2 = f.onV b := f.tgt_onE e
  simpa only [hs, ht] using h

variable {a : P}

theorem universalNerveChain2_uOrderHom (c : OrdTri (UOrder P a) →₀ ℤ) :
    universalNerveChain2 (chain2 uOrderHom c) = ordNerveChain2 c := by
  change ordNerveChain2
    (Finsupp.mapDomain uOrderHomInv.onF (Finsupp.mapDomain uOrderHom.onF c)) = _
  rw [← Finsupp.mapDomain_comp]
  have h : (uOrderHomInv (a := a)).onF ∘ uOrderHom.onF = id := by
    funext t
    exact homInv_onF_comp uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ t
  rw [h, Finsupp.mapDomain_id]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve Cell
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- The source old-cover base is the actual spanning-tree root. The same
cylinder path used by the received comparison transports it to the quotient base. -/
def universalOldToNamedQuotient :
    Hom (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (univLift (orderCx (QOld (cmpRel (GenusVertex q))))
      (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q))

def universalOldToNamedOrder (p : universalOldOrder q) :
    UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) :=
  (universalOldToNamedQuotient ρ q u).onV p

theorem universalOldToNamedOrder_monotone : Monotone (universalOldToNamedOrder ρ q u) := by
  have hm := cellularOrderHom_vertex_monotone
    (uOrderHomInv.comp ((universalOldToNamedQuotient ρ q u).comp uOrderHom))
  intro p r hpr
  have h := hm hpr
  change @LE.le (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) inferInstance
    (uOrderHomInv.onV (universalOldToNamedOrder ρ q u p))
    (uOrderHomInv.onV (universalOldToNamedOrder ρ q u r)) at h
  simpa only [uOrderHomInv_vertex] using h

theorem universalOldToNamedOrder_end (p : universalOldOrder q) :
    uOrderEnd (universalOldToNamedOrder ρ q u p) =
      qOldIncl (att := namedAtt ρ q u) (uOrderEnd p) := by
  change endV (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)
    (univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u) p)) = _
  rw [endV_pathTransportV, endV_univLiftV]
  rfl

theorem universalOldToNamedOrder_edge (e : OrdEdge (universalOldOrder q)) :
    uOrderEdge ((orderCxMap (universalOldToNamedOrder ρ q u)
      (universalOldToNamedOrder_monotone ρ q u)).onE e) =
      (universalOldToNamedQuotient ρ q u).onE (uOrderEdge e) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact Prod.ext (universalOldToNamedOrder_end ρ q u e.1.1)
      (universalOldToNamedOrder_end ρ q u e.1.2)

theorem universalOldToNamedOrder_face (t : OrdTri (universalOldOrder q)) :
    uOrderFace ((orderCxMap (universalOldToNamedOrder ρ q u)
      (universalOldToNamedOrder_monotone ρ q u)).onF t) =
      (universalOldToNamedQuotient ρ q u).onF (uOrderFace t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact Prod.ext (universalOldToNamedOrder_end ρ q u t.1.1)
      (Prod.ext (universalOldToNamedOrder_end ρ q u t.1.2.1)
        (universalOldToNamedOrder_end ρ q u t.1.2.2))

theorem universalOldToNamedOrder_square :
    uOrderHom.comp (orderCxMap (universalOldToNamedOrder ρ q u)
      (universalOldToNamedOrder_monotone ρ q u)) =
      (universalOldToNamedQuotient ρ q u).comp uOrderHom := by
  apply Hom.ext'
  · rfl
  · funext e; exact universalOldToNamedOrder_edge ρ q u e
  · funext t; exact universalOldToNamedOrder_face ρ q u t

theorem universalOldToNamedQuotient_nerve_chain2
    (c : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ) :
    universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u) c) =
      cmap (universalOldToNamedOrder ρ q u) (universalNerveChain2 c) := by
  have hsource : chain2 uOrderHom (chain2 uOrderHomInv c) = c := by
    change Finsupp.mapDomain uOrderHom.onF (Finsupp.mapDomain uOrderHomInv.onF c) = c
    rw [← Finsupp.mapDomain_comp]
    have hi : uOrderHom.onF ∘ (uOrderHomInv
        (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)).onF = id := by
      funext t
      exact homInv_onF_apply uOrderHom Function.bijective_id
        ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
        ⟨uOrderFace_injective, uOrderFace_surjective⟩ t
    rw [hi, Finsupp.mapDomain_id]
  calc
    _ = universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 uOrderHom (chain2 uOrderHomInv c))) := by rw [hsource]
    _ = universalNerveChain2 (chain2 uOrderHom
        (chain2 (orderCxMap (universalOldToNamedOrder ρ q u)
          (universalOldToNamedOrder_monotone ρ q u)) (chain2 uOrderHomInv c))) := by
      rw [← chain2_comp_apply, ← universalOldToNamedOrder_square, chain2_comp_apply]
    _ = _ := by
      rw [universalNerveChain2_uOrderHom, ordNerveChain2_chain2]
      rfl


/-- The entire barycentric source cover maps into the genuine attaching
intersection, before applying the last-vertex projection. -/
def universalPolygonAttachingRealization
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) : namedAttachingCover q ρ u :=
  ⟨universalOldToNamedOrder ρ q u (universalPolygonRealization q σ), by
    rw [universalOldToNamedOrder_end, universalPolygonRealization_end]
    exact ⟨trivial, rfl⟩⟩

theorem universalPolygonAttachingRealization_monotone :
    Monotone (universalPolygonAttachingRealization ρ q u) :=
  (universalOldToNamedOrder_monotone ρ q u).comp (universalPolygonRealization_monotone q)

theorem universalPolygonAttachingRealization_projection
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ) =
      barycentricMap (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q).mono σ := by
  have h := qAttachingCoverEnd_spec (namedQuotientBase ρ q u)
    (universalPolygonAttachingRealization ρ q u σ)
  change qOldIncl
    (posQCube (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ))) =
    uOrderEnd (universalOldToNamedOrder ρ q u (universalPolygonRealization q σ)) at h
  rw [universalOldToNamedOrder_end, universalPolygonRealization_end] at h
  exact Subtype.ext (congrArg (fun t : QOld (cmpRel (GenusVertex q)) => t.1.spx)
    (Sum.inl.inj h))

def universalPolygonToNamedSurface (p : UniversalPolygonCover q) : NamedSurfaceCover ρ q u :=
  attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)
      (universalPolygonAttachingRealization ρ q u (spx1 p))

theorem universalPolygonToNamedSurface_projection (p : UniversalPolygonCover q) :
    namedSurfaceProjection ρ q u (universalPolygonToNamedSurface ρ q u p) =
      universalPolygonProjection q p := by simp_all [universalPolygonAttachingRealization_projection, barycentricMap_spx1, chainMax_spx1, universalPolygonToNamedSurface]

theorem universalPolygonToNamedSurface_monotone :
    Monotone (universalPolygonToNamedSurface ρ q u) := by
  intro p r hpr
  let T := attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)
  have hT := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
  let s := universalPolygonAttachingRealization ρ q u (spx2 hpr)
  have hp  :=
    hT (universalPolygonAttachingRealization_monotone ρ q u (spx1_le_spx2_left hpr))
  have hr : universalPolygonToNamedSurface ρ q u r ≤ T s :=
    hT (universalPolygonAttachingRealization_monotone ρ q u (spx1_le_spx2_right hpr))
  have he : universalPolygonToNamedSurface ρ q u r = T s := by
    apply (namedSurfaceProjection_isPosetCover ρ q u).down_inj hr le_rfl
    rw [universalPolygonToNamedSurface_projection]
    change universalPolygonProjection q r =
      chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
        (universalPolygonAttachingRealization ρ q u (spx2 hpr)))
    rw [universalPolygonAttachingRealization_projection,
      barycentricMap_spx2]
    letI : DecidableEq (GenusVertex q) := Classical.decEq _
    exact (chainMax_spx2 ((universalPolygonProjection_isPosetCover q).mono hpr)).symm
  exact he.symm ▸ hp

theorem universalPolygonToNamedSurface_strictMono :
    StrictMono (universalPolygonToNamedSurface ρ q u) := by
  intro p r hpr
  apply lt_of_le_of_ne (universalPolygonToNamedSurface_monotone ρ q u hpr.le)
  intro he
  have hp := congrArg (namedSurfaceProjection ρ q u) he
  rw [universalPolygonToNamedSurface_projection, universalPolygonToNamedSurface_projection] at hp
  exact hpr.ne ((universalPolygonProjection_isPosetCover q).up_inj le_rfl hpr.le hp)

/-- Singleton lifts and general simplex lifts give the same surface sheet
at the maximal original cell. This is stronger than equality after projection. -/
theorem universalPolygonAttachingRealization_lastVertex
    (σ : NeSpx (cmpRel (UniversalPolygonCover q))) :
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (universalPolygonAttachingRealization ρ q u σ) =
      universalPolygonToNamedSurface ρ q u (chainMax σ) := by
  have hs : spx1 (chainMax σ) ≤ σ := by
    intro p hp
    have he : p = chainMax σ := by simpa using hp
    rw [he]
    exact chainMax_mem σ
  have hm := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
      (universalPolygonAttachingRealization_monotone ρ q u hs)
  apply Eq.symm
  apply (namedSurfaceProjection_isPosetCover ρ q u).down_inj hm le_rfl
  change namedSurfaceProjection ρ q u
    (universalPolygonToNamedSurface ρ q u (chainMax σ)) = _
  rw [universalPolygonToNamedSurface_projection]
  change universalPolygonProjection q (chainMax σ) =
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (universalPolygonAttachingRealization ρ q u σ))
  rw [universalPolygonAttachingRealization_projection]
  erw [chainMax_barycentricMap]

def transportedUniversalPolygonPole : NamedPolygonPole ρ q u :=
  ⟨universalPolygonToNamedSurface ρ q u (universalPolygonPole q).1,
    (universalPolygonToNamedSurface_projection ρ q u _).trans (universalPolygonPole q).2⟩


def transportedUniversalPolygonAttachingChain : Ch (namedAttachingCover q ρ u) :=
  ordNerveChain2 (chain2 (orderCxMap (universalPolygonAttachingRealization ρ q u)
    (universalPolygonAttachingRealization_monotone ρ q u))
      (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental)))

theorem transportedUniversalPolygonAttachingChain_mem_inc :
    transportedUniversalPolygonAttachingChain ρ q u ∈ Inc _ := ordNerveChain2_mem_inc _

theorem transportedUniversalPolygonAttachingChain_degree :
    lengthProjection 3 (transportedUniversalPolygonAttachingChain ρ q u) =
      transportedUniversalPolygonAttachingChain ρ q u := ordNerveChain2_lengthProjection _

/-- Exact normalization to the actual lifted degree-one filling, at its
transported pole. No arbitrary nullhomotopy enters this identity. -/
theorem transportedUniversalPolygonAttachingChain_normalized :
    namedAttachingNerveSurfaceChain ρ q u (transportedUniversalPolygonAttachingChain ρ q u) =
      namedPolygonFillingAt ρ q u (transportedUniversalPolygonPole ρ q u) := by
  let F : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)
  have hF  := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
  have hs : (orderCxMap F hF).comp
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u)) =
      (orderCxMap (universalPolygonToNamedSurface ρ q u)
        (universalPolygonToNamedSurface_monotone ρ q u)).comp
          (orderCxMap (chainMax) chainMax_monotone) := by
    apply Hom.ext'
    · funext σ; exact universalPolygonAttachingRealization_lastVertex ρ q u σ
    · funext e
      apply Subtype.ext
      exact Prod.ext (universalPolygonAttachingRealization_lastVertex ρ q u _)
        (universalPolygonAttachingRealization_lastVertex ρ q u _)
    · funext t
      apply Subtype.ext
      exact Prod.ext (universalPolygonAttachingRealization_lastVertex ρ q u _)
        (Prod.ext (universalPolygonAttachingRealization_lastVertex ρ q u _)
          (universalPolygonAttachingRealization_lastVertex ρ q u _))
  change normalizeOrdChain2 (chain2 (orderCxMap F hF)
    (decodeOrdNerve2 (ordNerveChain2 (chain2
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u))
      (barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental)))))) = _
  rw [decodeOrdNerve2_encode]
  rw [← chain2_comp_apply, hs, chain2_comp_apply,
    normalizeOrdChain2_strict_map _ (universalPolygonToNamedSurface_strictMono ρ q u),
    barycentricChain2_lastVertex]
  exact (show chain2 (strictOrderCxMap (universalPolygonToNamedSurface ρ q u)
      (universalPolygonToNamedSurface_strictMono ρ q u)) (universalPolygon q).cellularFundamental =
      namedPolygonFillingAt ρ q u (transportedUniversalPolygonPole ρ q u) by
    have hsource : (universalPolygon q).cellularFundamental =
        polygonCoverFilling (gc q) (universalPolygonProjection q)
          (universalPolygonProjection_isPosetCover q) (universalPolygonPole q) :=
      CoveredPolygon.cellularFundamental_unique (gc q) (universalPolygonProjection q)
        (universalPolygonProjection_isPosetCover q) (universalPolygon q) _
    rw [hsource]
    exact polygonCoverFilling_map (gc q) (universalPolygonProjection q)
      (universalPolygonProjection_isPosetCover q) (namedSurfaceProjection ρ q u)
      (namedSurfaceProjection_isPosetCover ρ q u) (universalPolygonToNamedSurface ρ q u)
      (universalPolygonToNamedSurface_strictMono ρ q u)
      (universalPolygonToNamedSurface_projection ρ q u) (universalPolygonPole q))

theorem universalPolygonAttachingRealization_square :
    (namedAttachingIntoUniversal q ρ u).comp
      (orderCxMap (universalPolygonAttachingRealization ρ q u)
        (universalPolygonAttachingRealization_monotone ρ q u)) =
      (universalOldToNamedQuotient ρ q u).comp (universalPolygonLift q) := by
  apply Hom.ext'
  · rfl
  · funext e
    exact universalOldToNamedOrder_edge ρ q u
      ((orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q)).onE e)
  · funext t
    exact universalOldToNamedOrder_face ρ q u
      ((orderCxMap (universalPolygonRealization q) (universalPolygonRealization_monotone q)).onF t)

/-- The reference in the attaching intersection is the exact image of the
source old-cover polygon, with every sheet and face coefficient unchanged. -/
theorem transportedUniversalPolygonAttachingChain_image :
    cmap (Subtype.val : namedAttachingCover q ρ u → _)
      (transportedUniversalPolygonAttachingChain ρ q u) =
      universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u)
        (universalOldPolygonChain q)) := by
  let b := barycentricChain2 (decodeOrdNerve2 (universalPolygon q).fundamental)
  have he (c : OrdTri (namedAttachingCover q ρ u) →₀ ℤ) :
      universalNerveChain2 (chain2 (namedAttachingIntoUniversal q ρ u) c) =
        cmap Subtype.val (ordNerveChain2 c) := by
    rw [namedAttachingIntoUniversal, chain2_comp_apply,
      universalNerveChain2_uOrderHom, ordNerveChain2_chain2]
  change cmap Subtype.val (ordNerveChain2 (chain2
    (orderCxMap (universalPolygonAttachingRealization ρ q u)
      (universalPolygonAttachingRealization_monotone ρ q u)) b)) = _
  rw [← he, ← chain2_comp_apply, universalPolygonAttachingRealization_square,
    chain2_comp_apply]
  rfl

/-- Any source old-cover chain in the selected polygon class is transported
to the explicit degree-one attaching reference, with an actual old correction. -/
theorem universalOldToNamedQuotient_polygon_reference
    (c : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ)
    (hgeometry : ∃ y ∈ Inc (universalOldOrder q),
      universalNerveChain2 c = universalNerveChain2 (universalOldPolygonChain q) + Nerve.bdry y) :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      universalNerveChain2 (chain2 (universalOldToNamedQuotient ρ q u) c) =
        cmap Subtype.val (transportedUniversalPolygonAttachingChain ρ q u) + Nerve.bdry y := by
  obtain ⟨y, hy, hcy⟩ := hgeometry
  refine ⟨cmap (universalOldToNamedOrder ρ q u) y,
    (by
      apply cmap_mem_incOn_of_maps (universalOldToNamedOrder_monotone ρ q u) _ hy
      intro p
      rw [universalOldToNamedOrder_end]
      trivial), ?_⟩
  rw [universalOldToNamedQuotient_nerve_chain2, hcy, map_add, cmap_bdry,
    ← universalOldToNamedQuotient_nerve_chain2, ← transportedUniversalPolygonAttachingChain_image]

end FiniteChains.Davis.Genus
end
