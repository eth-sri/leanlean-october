module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

noncomputable section
open scoped Classical
open Set Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.RelativeAttachment

universe u
variable {A X D : Type u}

def Space (_r : A → X) (i : A → D) : Type u :=
  X ⊕ {d : D // d ∉ Set.range i}

def old (r : A → X) (i : A → D) : X → Space r i := Sum.inl

def cell (r : A → X) (i : A → D) (d : D) : Space r i :=
  if h : d ∈ Set.range i then Sum.inl (r (Classical.choose h))
  else Sum.inr ⟨d, h⟩

def quotientMap (r : A → X) (i : A → D) : X ⊕ D → Space r i :=
  Sum.elim (old r i) (cell r i)

def fresh (r : A → X) (i : A → D) : {d : D // d ∉ Set.range i} → Space r i :=
  Sum.inr

theorem old_injective (r : A → X) (i : A → D) : Function.Injective (old r i) :=
  Sum.inl_injective

@[simp] theorem cell_of_not_mem (r : A → X) (i : A → D) (d : D)
    (hd : d ∉ Set.range i) : cell r i d = Sum.inr ⟨d, hd⟩ := dif_neg hd

theorem cell_boundary (r : A → X) (i : A → D) (hi : Function.Injective i) (a : A) :
    cell r i (i a) = old r i (r a) := by
  have h : i a ∈ Set.range i := ⟨a, rfl⟩
  simp only [cell, old, dif_pos h]
  exact congrArg Sum.inl (congrArg r (hi (Classical.choose_spec h)))

theorem quotientMap_surjective (r : A → X) (i : A → D) :
    Function.Surjective (quotientMap r i)
  | Sum.inl x => ⟨Sum.inl x, rfl⟩
  | Sum.inr d => ⟨Sum.inr d.val, cell_of_not_mem r i d.val d.property⟩

variable [TopologicalSpace X] [TopologicalSpace D]

instance topology (r : A → X) (i : A → D) : TopologicalSpace (Space r i) :=
  TopologicalSpace.coinduced (quotientMap r i) inferInstance

theorem quotientMap_continuous (r : A → X) (i : A → D) :
    Continuous (quotientMap r i) := continuous_coinduced_rng

theorem old_continuous (r : A → X) (i : A → D) : Continuous (old r i) :=
  (quotientMap_continuous r i).comp continuous_inl

theorem cell_continuous (r : A → X) (i : A → D) : Continuous (cell r i) :=
  (quotientMap_continuous r i).comp continuous_inr

theorem fresh_isOpenEmbedding (r : A → X) (i : A → D)
    (hi : IsClosed (Set.range i)) : IsOpenEmbedding (fresh r i) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (by rw [show fresh r i = cell r i ∘ Subtype.val from funext fun d => (cell_of_not_mem r i d.val d.property).symm]
        exact (cell_continuous r i).comp continuous_subtype_val)
    Sum.inr_injective fun S hS => isOpen_coinduced.mpr (isOpen_sum_iff.mpr ⟨?_, ?_⟩)
  · change IsOpen ((old r i) ⁻¹' ((fresh r i) '' S))
    rw [show (old r i) ⁻¹' ((fresh r i) '' S) = ∅ from
      Set.ext fun _ => ⟨fun ⟨_, _, he⟩ => Sum.inr_ne_inl he, False.elim⟩]
    exact isOpen_empty
  · change IsOpen ((cell r i) ⁻¹' ((fresh r i) '' S))
    rw [show (cell r i) ⁻¹' ((fresh r i) '' S) = Subtype.val '' S from Set.ext fun d =>
      ⟨fun ⟨v, hv, he⟩ => by
        by_cases hd : d ∈ Set.range i
        · simp only [fresh, cell, dif_pos hd] at he; exact (Sum.inr_ne_inl he).elim
        · simp only [fresh, cell, dif_neg hd] at he
          exact ⟨v, hv, congrArg Subtype.val (Sum.inr_injective he)⟩,
       by rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, (cell_of_not_mem r i v.val v.property).symm⟩⟩]
    exact hi.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hS

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem old_fresh_disjoint (r : A → X) (i : A → D) :
    Disjoint (Set.range (old r i)) (Set.range (fresh r i)) :=
  Set.disjoint_left.mpr fun _ ⟨_, hx⟩ ⟨_, hd⟩ => Sum.inr_ne_inl (hd.trans hx.symm)

variable {Z : Type u} [TopologicalSpace Z]

def desc (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) : C(Space r i, Z) where
  toFun := Sum.elim f (fun d => g d.val)
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    rw [show Sum.elim f (fun d => g d.val) ∘ quotientMap r i = Sum.elim f g by
      ext (x | d)
      · rfl
      · simp only [Function.comp_apply, quotientMap, Sum.elim_inr, cell]
        split_ifs with hd
        · simp only [Sum.elim_inl]; rw [h, Classical.choose_spec hd]
        · rfl]
    exact f.continuous.sumElim g.continuous

@[simp] theorem desc_old (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (x : X) : desc r i f g h (old r i x) = f x := rfl

@[simp] theorem desc_cell (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (d : D) : desc r i f g h (cell r i d) = g d := by
  show Sum.elim f (fun d => g d.val) (cell r i d) = g d
  simp only [cell]
  split_ifs with hd
  · simp only [Sum.elim_inl]; rw [h, Classical.choose_spec hd]
  · rfl

theorem hom_ext (r : A → X) (i : A → D) {f g : C(Space r i, Z)}
    (hOld : ∀ x, f (old r i x) = g (old r i x))
    (hCell : ∀ d, f (cell r i d) = g (cell r i d)) : f = g :=
  ContinuousMap.ext fun z => by
    obtain ⟨x | d, rfl⟩ := quotientMap_surjective r i z
    exacts [hOld x, hCell d]

variable [TopologicalSpace A]

omit [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D] in
theorem cell_preimage_old_image (r : A → X) (i : A → D)
    (hi : Function.Injective i) (S : Set X) :
    (cell r i) ⁻¹' ((old r i) '' S) = i '' (r ⁻¹' S) :=
  Set.ext fun d => ⟨fun ⟨x, hx, he⟩ => by
    by_cases hd : d ∈ Set.range i
    · simp only [old, cell, dif_pos hd] at he
      exact ⟨Classical.choose hd, by simpa [Sum.inl_injective he] using hx, Classical.choose_spec hd⟩
    · rw [cell_of_not_mem r i d hd] at he; exact (Sum.inl_ne_inr he).elim,
   by rintro ⟨a, ha, rfl⟩; exact ⟨r a, ha, (cell_boundary r i hi a).symm⟩⟩

theorem old_isClosedEmbedding (r : A → X) (i : A → D)
    (hr : Continuous r) (hi : IsClosedEmbedding i) : IsClosedEmbedding (old r i) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (old_continuous r i) (old_injective r i) fun S hS =>
    isClosed_coinduced.mpr (isClosed_sum_iff.mpr
      ⟨by change IsClosed ((old r i) ⁻¹' ((old r i) '' S))
          rwa [Set.preimage_image_eq S (old_injective r i)],
       by change IsClosed ((cell r i) ⁻¹' ((old r i) '' S))
          rw [cell_preimage_old_image r i hi.injective]
          exact hi.isClosedMap _ (hS.preimage hr)⟩)
