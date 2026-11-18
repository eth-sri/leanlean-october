module

public import RequestProject.TreePi2Reflection
public import RequestProject.RegularCoverChainDescent
public import RequestProject.OrderNerveOneDecoding
public import RequestProject.GenusQuotientRelativeSupport
public import RequestProject.GenusCollapseIteration
public import RequestProject.OrderNerveCommonSimplex
public import RequestProject.CylinderPi1Surjective
public import RequestProject.CombPi1
public import RequestProject.GenusUniversalPolygonTransport
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import RequestProject.TopologicalOrderCoverDeck
public import RequestProject.PresWordEmbeddingCombPi2
public import Mathlib.Order.Fin.Basic
public import RequestProject.PresPosetReading
public import Mathlib.Analysis.Convex.StdSimplex
public import RequestProject.QCubeThreeFaceIndex

@[expose] public section
noncomputable section
section
open scoped Classical
namespace FiniteChains.RelativeNormalForm.AmbientChain
open Comb

variable {A C : Type} {core : C → FreeGroup A} {n : ℕ}
  (c : AmbientChain core n)

def cellComplex (i : ℕ) : Complex2 := presComplex (c.chainRel i)

def cellInclusion (i : ℕ) : Hom (c.cellComplex i) (c.cellComplex (i + 1)) :=
  presInclHom (c.chainGenIncl i) (c.chainGenIncl_injective i)
    (c.chainRel i) (c.chainRel (i + 1)) (c.chainCellIncl i) (c.chainRel_incl i)

theorem cellInclusion_zero (hinj : Function.Injective (expMatrix core))
    (i : ℕ) (hi : i < n + 1) : ZeroPi2 (c.cellInclusion i) := by
  apply (zeroPi2_presInclHom_iff (ρ := c.chainRel i)
    (c.chainGenIncl i) (c.chainGenIncl_injective i)
    (c.chainCellIncl i) (c.chainRel_incl i)).mpr
  exact (c.toPresChainFS hinj).zero_pi2 i hi

theorem first_cellInclusion_pi1Trivial : Pi1Trivial (c.cellInclusion 0) := by
  apply (pi1Trivial_presInclHom_iff (ρ := c.chainRel 0)
    (c.chainGenIncl 0) (c.chainGenIncl_injective 0)
    (c.chainCellIncl 0) (c.chainRel_incl 0)).mpr
  intro w
  induction w using QuotientGroup.induction_on with
  | H w =>
      let f  :=
        (QuotientGroup.mk' (relSub (c.chainRel 1))).comp (FreeGroup.map Sum.inl)
      have hf : f = 1 := by
        apply FreeGroup.ext_hom
        intro a
        exact c.core_trivial 0 a
      exact DFunLike.congr_fun hf w

end FiniteChains.RelativeNormalForm.AmbientChain

namespace FiniteChains.RelativeNormalForm
open Comb
variable {A C : Type} (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))

end FiniteChains.RelativeNormalForm

namespace FiniteChains.Comb.RelativeTreeAmbientChain
open SpanningTree RelativeNormalForm RelativeTreeExtension

variable {D : Complex2} (T : SpanningTree D) {n : ℕ}
  (c : AmbientChain (treeRel T) n)

def stageEdges : ℕ → Type
  | 0 => D.E
  | _ + 1 => D.E ⊕ c.extraGen

def stageSource : ∀ i, stageEdges T c i → D.V
  | 0 => D.src
  | _ + 1 => source T

def stageTarget : ∀ i, stageEdges T c i → D.V
  | 0 => D.tgt
  | _ + 1 => target T

def stageBase : ∀ i, c.chainCell i → D.V
  | 0 => D.base
  | _ + 1 => Sum.elim D.base (fun _ => T.root)

def stageAttaching : ∀ i, c.chainCell i → List (stageEdges T c i × Bool)
  | 0 => D.att
  | i + 1 => Sum.elim (fun f => oldPath (D.att f))
      (fun s => readWord T (restrictedExtra c.rel (c.stage i) s).toWord)

/-- Keep the face family definitionally equal to the ambient chain's
family also at a variable index; this avoids transporting face labels. -/
def stages (i : ℕ) : Complex2 where
  V := D.V
  E := stageEdges T c i
  F := c.chainCell i
  src := stageSource T c i
  tgt := stageTarget T c i
  base := stageBase T c i
  att := stageAttaching T c i
  att_isLoop := by
    cases i with
    | zero => exact D.att_isLoop
    | succ i => exact (complex T (restrictedExtra c.rel (c.stage i))).att_isLoop

def trees : ∀ i, SpanningTree (stages T c i)
  | 0 => T
  | i + 1 => tree T (restrictedExtra c.rel (c.stage i))

def inclusions : ∀ i, Hom (stages T c i) (stages T c (i + 1))
  | 0 => oldInclusion T (restrictedExtra c.rel (c.stage 0))
  | i + 1 => inclusion T (restrictedExtra c.rel (c.stage i))
      (restrictedExtra c.rel (c.stage (i + 1))) (labelIncl (c.mono i)) (fun _ => rfl)

theorem inclusions_V (i : ℕ) : Function.Injective (inclusions T c i).onV := by
  cases i <;> exact Function.injective_id

theorem inclusions_E (i : ℕ) : Function.Injective (inclusions T c i).onE := by
  cases i
  · exact Sum.inl_injective
  · exact Function.injective_id

theorem inclusions_F (i : ℕ) : Function.Injective (inclusions T c i).onF := by
  cases i with
  | zero => exact Sum.inl_injective
  | succ i =>
      exact c.chainCellIncl_injective (i + 1)

theorem trees_inclusions (i : ℕ) (e : (stages T c i).E) :
    (trees T c (i + 1)).isTree ((inclusions T c i).onE e) ↔
      (trees T c i).isTree e := by
  cases i <;> exact Iff.rfl

def generatorCoordinates : ∀ i, NonTree (trees T c i) ≃ c.chainGen i
  | 0 => Equiv.refl _
  | i + 1 => generatorEquiv T (restrictedExtra c.rel (c.stage i))

theorem relatorCoordinates (i : ℕ) (f : (stages T c i).F) :
    c.chainRel i f = FreeGroup.map (generatorCoordinates T c i)
      (treeRel (trees T c i) f) := by
  cases i with
  | zero => exact (FreeGroup.map.id (treeRel T f)).symm
  | succ i =>
      exact (treeRel_equation T (restrictedExtra c.rel (c.stage i)) f).symm

def presentationCoordinates (i : ℕ) :
    Hom (presComplex (treeRel (trees T c i))) (c.cellComplex i) :=
  PresGeneratorRelabel.forward (generatorCoordinates T c i) _ _ (relatorCoordinates T c i)

def inversePresentationCoordinates (i : ℕ) :
    Hom (c.cellComplex i) (presComplex (treeRel (trees T c i))) :=
  PresGeneratorRelabel.backward (generatorCoordinates T c i) _ _ (relatorCoordinates T c i)

def collapsedInclusion (i : ℕ) :
    Hom (presComplex (treeRel (trees T c i)))
      (presComplex (treeRel (trees T c (i + 1)))) :=
  presInclHom (nonTreeIncl (trees_inclusions T c i))
    (nonTreeIncl_injective (trees_inclusions T c i) (inclusions_E T c i))
    _ _ (inclusions T c i).onF (treeRel_onF (trees_inclusions T c i))

theorem generatorCoordinates_natural (i : ℕ) (a : NonTree (trees T c i)) :
    generatorCoordinates T c (i + 1) (nonTreeIncl (trees_inclusions T c i) a) =
      c.chainGenIncl i (generatorCoordinates T c i a) := by
  cases i with
  | zero => rfl
  | succ i => rcases a with ⟨a | z, ha⟩ <;> rfl

theorem presentationCoordinates_square (i : ℕ) :
    (presentationCoordinates T c (i + 1)).comp (collapsedInclusion T c i) =
      (c.cellInclusion i).comp (presentationCoordinates T c i) := by
  apply Hom.ext'
  · rfl
  · exact funext (generatorCoordinates_natural T c i)
  · cases i <;> rfl

theorem zeroPi2_inclusions (hinj : Function.Injective (expMatrix (treeRel T)))
    (i : ℕ) (hi : i < n + 1) : ZeroPi2 (inclusions T c i) := by
  apply zeroPi2_of_zeroPi2_presInclHom (trees_inclusions T c i) (inclusions_E T c i)
  exact zeroPi2_of_retraction_square (collapsedInclusion T c i) (c.cellInclusion i)
    (presentationCoordinates T c i) (presentationCoordinates T c (i + 1))
    (inversePresentationCoordinates T c (i + 1))
    (PresGeneratorRelabel.backward_forward_V _ _ _ _)
    (PresGeneratorRelabel.backward_forward_E _ _ _ _)
    (PresGeneratorRelabel.backward_forward_F _ _ _ _)
    (presentationCoordinates_square T c i) (c.cellInclusion_zero hinj i hi)

theorem first_inclusion_pi1Trivial : Pi1Trivial (inclusions T c 0) := by
  apply pi1Trivial_of_pi1Trivial_presInclHom (trees_inclusions T c 0) (inclusions_E T c 0)
  exact pi1Trivial_of_retraction_square (collapsedInclusion T c 0) (c.cellInclusion 0)
    (presentationCoordinates T c 0) (presentationCoordinates T c 1)
    (inversePresentationCoordinates T c 1)
    (PresGeneratorRelabel.backward_forward_V _ _ _ _)
    (PresGeneratorRelabel.backward_forward_E _ _ _ _)
    (PresGeneratorRelabel.backward_forward_F _ _ _ _)
    (presentationCoordinates_square T c 0) c.first_cellInclusion_pi1Trivial

theorem inclFrom_pi1Trivial : ∀ i, 1 ≤ i →
    Pi1Trivial (inclFrom (stages T c) (inclusions T c) i)
  | 0, hi => by omega
  | 1, _ => fun a p hp => first_inclusion_pi1Trivial T c a p hp
  | i + 2, _ => Pi1Trivial.comp_left (inclusions T c (i + 1))
      (inclFrom_pi1Trivial (i + 1) (by omega))

theorem proper (i : ℕ) (hi : i < n + 1) :
    (¬ Function.Surjective (inclusions T c i).onE) ∨
      (¬ Function.Surjective (inclusions T c i).onF) := by
  cases i with
  | zero =>
      left
      intro hs
      obtain ⟨e, he⟩ := hs (Sum.inr c.fresh)
      exact Sum.inl_ne_inr he
  | succ i =>
      rcases c.chain_proper (i + 1) hi with ⟨a, ha⟩ | ⟨f, hf⟩
      · exact False.elim (ha ⟨a, rfl⟩)
      · right
        intro hs
        exact hf (hs f)

def relativeChain (hinj : Function.Injective (expMatrix (treeRel T))) :
    RelativeCellChain (stages T c) (n + 1) where
  inc := inclusions T c
  incV := inclusions_V T c
  incE := inclusions_E T c
  incF := inclusions_F T c
  conn := by
    intro i
    cases i with
    | zero =>
        intro a b
        exact ⟨revPath (T.treePath a) ++ T.treePath b,
          (isPath_revPath (T.treePath_isPath a)).append (T.treePath_isPath b)⟩
    | succ i => exact connected T (restrictedExtra c.rel (c.stage i))
  zero := zeroPi2_inclusions T c hinj
  pi1 := fun i hi _ => inclFrom_pi1Trivial T c i hi
  proper := proper T c

/-- An explicit relative chain over D itself, from the bijective
exponent boundary of its tree presentation. No cells of D are collapsed
in the resulting chain. -/
def actualRelativeChain (h : Function.Bijective (expMatrix (treeRel T))) (n : ℕ) :
    RelativeCellChain (stages T (actualAmbientChain (treeRel T) h n)) (n + 1) :=
  relativeChain T (actualAmbientChain (treeRel T) h n) h.1

end FiniteChains.Comb.RelativeTreeAmbientChain

namespace FiniteChains.Comb
open SpanningTree RelativeNormalForm RelativeTreeAmbientChain

variable {D : Complex2.{0}} (T : SpanningTree D) (hD : IsAcyclic D)

def acyclicRelativeStages (n : ℕ) : ℕ → Complex2 :=
  stages T (actualAmbientChain (treeRel T) (expMatrix_bijective_of_acyclic T hD) n)

def acyclicRelativeCellChain (n : ℕ) :
    RelativeCellChain (acyclicRelativeStages T hD n) (n + 1) :=
  actualRelativeChain T (expMatrix_bijective_of_acyclic T hD) n

@[simp] theorem acyclicRelativeStages_zero (n : ℕ) :
    acyclicRelativeStages T hD n 0 = D := rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
universe v
variable {D K : Complex2} (T : SpanningTree D) (hD : IsAcyclic D)
  (p : Hom D K)

def regularCoverChainStages (n : ℕ) : ℕ → Complex2 :=
  (acyclicRelativeCellChain T hD n).desc p

def regularCoverChainInclusion (n i : ℕ) :
    Hom (regularCoverChainStages T hD p n i) (regularCoverChainStages T hD p n (i + 1)) :=
  (acyclicRelativeCellChain T hD n).descInc p i

@[simp] theorem regularCoverChainStages_zero (n : ℕ) :
    regularCoverChainStages T hD p n 0 = K := rfl

theorem regularCoverChainInclusion_V (n i : ℕ) :
    Function.Injective (regularCoverChainInclusion T hD p n i).onV :=
  (acyclicRelativeCellChain T hD n).descInc_injective_V p i

theorem regularCoverChainInclusion_E (n i : ℕ) :
    Function.Injective (regularCoverChainInclusion T hD p n i).onE :=
  (acyclicRelativeCellChain T hD n).descInc_injective_E p i

theorem regularCoverChainInclusion_F (n i : ℕ) :
    Function.Injective (regularCoverChainInclusion T hD p n i).onF :=
  (acyclicRelativeCellChain T hD n).descInc_injective_F p i

theorem regularCoverChain_connected (hp : IsCovering p) (n i : ℕ) :
    IsConnected (regularCoverChainStages T hD p n i) :=
  (acyclicRelativeCellChain T hD n).desc_connected p hp T.root i

variable (hp : IsCovering p) {Q : Type v} [Group Q]
  (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)

include hp hr he hf in
theorem regularCoverChain_zeroPi2 (n i : ℕ) (hi : i < n + 1) :
    ZeroPi2 (regularCoverChainInclusion T hD p n i) :=
  (acyclicRelativeCellChain T hD n).descInc_zeroPi2 p hp a hr he hf hD T.root i hi

/-- The actual descended inclusions form an arbitrary-length cellular
chain beginning literally at K. Strictness is regularCoverChain_proper. -/
def regularCoverTopChain (n : ℕ) : TopChainFS K (n + 1) where
  X := regularCoverChainStages T hD p n
  inc := regularCoverChainInclusion T hD p n
  incV := regularCoverChainInclusion_V T hD p n
  incE := regularCoverChainInclusion_E T hD p n
  incF := regularCoverChainInclusion_F T hD p n
  conn := regularCoverChain_connected T hD p hp n
  base := Hom.id K
  baseV := Function.injective_id
  baseE := Function.injective_id
  baseF := Function.injective_id
  zero_pi2 := regularCoverChain_zeroPi2 T hD p hp a hr he hf n

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u

variable {X Y : Complex2.{u}}

def FreshLoopOrFace (h : Hom X Y) : Prop :=
  (∃ e : Y.E, Y.src e = Y.tgt e ∧ e ∉ Set.range h.onE) ∨
    ∃ f : Y.F, f ∉ Set.range h.onF

namespace SpanningTree

theorem height_step_of_isTree (T : SpanningTree X) {e : X.E} (he : T.isTree e) :
    T.ht (X.src e) + 1 = T.ht (X.tgt e) ∨
      T.ht (X.tgt e) + 1 = T.ht (X.src e) := by
  obtain ⟨a, ha, hea⟩ := (T.isTree_iff e).mp he
  have hs := T.up_src a ha
  have hh := T.up_ht a ha
  cases hb : (T.up a ha).2 with
  | false =>
      left
      have hsrc : X.tgt e = a := by
        simpa [germSrc, hb, hea] using hs
      have hheight : T.ht (X.src e) + 1 = T.ht a := by
        simpa [germTgt, hb, hea] using hh
      exact hheight.trans (congrArg T.ht hsrc).symm
  | true =>
      right
      have hsrc : X.src e = a := by
        simpa [germSrc, hb, hea] using hs
      have hheight : T.ht (X.tgt e) + 1 = T.ht a := by
        simpa [germTgt, hb, hea] using hh
      exact hheight.trans (congrArg T.ht hsrc).symm

theorem not_isTree_of_loop (T : SpanningTree X) {e : X.E}
    (he : X.src e = X.tgt e) : ¬T.isTree e := by
  intro ht
  have hs := T.height_step_of_isTree ht
  rw [he] at hs
  omega

theorem nonTree_or_face_fresh {h : Hom X Y} {T : SpanningTree X}
    {U : SpanningTree Y} (ht : ∀ e, U.isTree (h.onE e) ↔ T.isTree e)
    (hp : FreshLoopOrFace h) :
    (∃ a : NonTree U, a ∉ Set.range (nonTreeIncl ht)) ∨
      ∃ f : Y.F, f ∉ Set.range h.onF := by
  rcases hp with ⟨e, hloop, he⟩ | hf
  · left
    refine ⟨⟨e, U.not_isTree_of_loop hloop⟩, ?_⟩
    rintro ⟨a, ha⟩
    exact he ⟨a.val, congrArg Subtype.val ha⟩
  · simp_all

end SpanningTree
end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory
universe u
variable (P : Type u) [PartialOrder P]

def vertexNerveEquiv : P ≃ (nerve P).nonDegenerate 0 where
  toFun p := ⟨ComposableArrows.mk₀ p,
    (PartialOrder.mem_nerve_nonDegenerate_iff_injective _).mpr
      (fun i j _ => @Subsingleton.elim (Fin 1) inferInstance i j)⟩
  invFun s := s.val.obj 0
  left_inv _ := rfl
  right_inv s := by
    apply Subtype.ext
    exact ComposableArrows.ext₀ rfl

def strictEdgeNerveEquiv : StrictOrdEdge P ≃ (nerve P).nonDegenerate 1 where
  toFun e := ⟨ordEdgeNerveEquiv P ⟨e.val, e.property.le⟩, by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    exact e.property⟩
  invFun s := ⟨(s.val.obj 0, s.val.obj 1),
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mp s.property) (by decide)⟩
  left_inv e := Subtype.ext rfl
  right_inv s := by
    apply Subtype.ext
    change ordEdgeNerveEquiv P ((ordEdgeNerveEquiv P).symm s.val) = s.val
    exact (ordEdgeNerveEquiv P).apply_symm_apply s.val

def strictTriNerveEquiv : StrictOrdTri P ≃ (nerve P).nonDegenerate 2 where
  toFun t := ⟨ordTriNerveEquiv P ⟨t.val, t.property.1.le, t.property.2.le⟩, by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    all_goals first | exact t.property.1 | exact t.property.2 |
      exact t.property.1.trans t.property.2⟩
  invFun s := ⟨(s.val.obj 0, s.val.obj 1, s.val.obj 2),
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mp s.property) (by decide),
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mp s.property) (by decide)⟩
  left_inv t := Subtype.ext rfl
  right_inv s := by
    apply Subtype.ext
    change ordTriNerveEquiv P ((ordTriNerveEquiv P).symm s.val) = s.val
    exact (ordTriNerveEquiv P).apply_symm_apply s.val

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.StrictNormalized
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The normalized strict edge-chain map of an arbitrary monotone map. -/
def mapOne (f : P → Q) (hf : Monotone f) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

theorem mapOne_single (f : P → Q) (hf : Monotone f) (e : StrictOrdEdge P) (n : ℤ) :
    mapOne f hf (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(f e.1.1, f e.1.2), hf e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
  rfl

theorem mapOne_strict (f : P → Q) (hf : StrictMono f) (c : StrictOrdEdge P →₀ ℤ) :
    mapOne f hf.monotone c = chain1 (strictOrderCxMap f hf) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [mapOne_single]
    simp [normalizeOrdEdge, (hf e.2).ne, chain1, strictOrderCxMap]

theorem mapOne_id (c : StrictOrdEdge P →₀ ℤ) : mapOne id monotone_id c = c :=
  normalizedStrictChain1_id c

theorem mapOne_comp (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (c : StrictOrdEdge P →₀ ℤ) :
    mapOne g hg (mapOne f hf c) = mapOne (g ∘ f) (hg.comp hf) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [mapOne_single, map_smul]
    by_cases h : f e.1.1 = f e.1.2
    · simp [normalizeOrdEdge, h, mapOne_single, Function.comp_def]
    · rw [show normalizeOrdEdge ⟨(f e.1.1, f e.1.2), hf e.2.le⟩ =
        Finsupp.single ⟨(f e.1.1, f e.1.2), lt_of_le_of_ne (hf e.2.le) h⟩ 1 by
          simp [normalizeOrdEdge, h]]
      rw [mapOne_single, one_smul, mapOne_single]
      rfl

/-- Exact naturality of normalization under a strict change of coordinates. -/
theorem mapOne_semiconj (e : P → Q) (he : StrictMono e)
    (g : P → P) (hg : Monotone g) (h : Q → Q) (hh : Monotone h)
    (hs : ∀ x, e (g x) = h (e x)) (c : StrictOrdEdge P →₀ ℤ) :
    chain1 (strictOrderCxMap e he) (normalizedStrictChain1 g hg c) =
      normalizedStrictChain1 h hh (chain1 (strictOrderCxMap e he) c) := by
  change chain1 (strictOrderCxMap e he) (mapOne g hg c) =
    mapOne h hh (chain1 (strictOrderCxMap e he) c)
  rw [← mapOne_strict e he, ← mapOne_strict e he, mapOne_comp, mapOne_comp]
  have heq : e ∘ g = h ∘ e := funext hs
  simp_all

end FiniteChains.Comb.StrictNormalized
end

namespace FiniteChains.PresModel.IdentityChains
open Comb Comb.StrictNormalized
universe u
variable {α J : Type u} (w : J → List (α × Bool))

def cover : IsPosetCover (id : PresPos w → PresPos w) :=
  ⟨monotone_id, Function.surjective_id,
    fun _ b h => ⟨b, ⟨h, rfl⟩, fun _ hz => hz.2⟩,
    fun _ b h => ⟨b, ⟨h, rfl⟩, fun _ hz => hz.2⟩⟩

/-- In the identity cover the actual lifted-apex labels are exactly the original labels. -/
def relatorEquiv : J ≃ PresCoverRelator w id where
  toFun j := ⟨(apexOf w j, j), rfl⟩
  invFun p := p.1.2
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext p.2.symm rfl)

abbrev Base := {p : PresPos w // p ∈ coneAdjBaseSet (S := circSet w)}

def baseIso : Base w ≃o CylBase w := coneAdjBaseOrderIso

def baseProjection :
    (StrictOrdEdge (Base w) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (CylBase w) →₀ ℤ) :=
  chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)

theorem baseProjection_injective : Function.Injective (baseProjection w) :=
  Finsupp.mapDomain_injective
    (strictOrderCxMap_onE_injective (baseIso w) (baseIso w).strictMono (baseIso w).injective)

theorem baseIso_collapse (p : Base w) :
    baseIso w (presCoverCylinderCollapse w id (cover w) p) =
      cylCollapse (aHom w) (baseIso w p) :=
  cylinderCoverCollapse_projection w (coneAdjCoverBaseEnd_isPosetCover id (cover w)) p


def circleIntoCylinder (j : J) : RelatorCircle w j → CylBase w :=
  fun x => cylOuter (aHom w) x.val


def cylinderBoundary (j : J) : StrictOrdEdge (CylBase w) →₀ ℤ :=
  mapOne (circleIntoCylinder w j) (show StrictMono (circleIntoCylinder w j) by
    intro a b h
    exact lt_of_le_of_ne h.le (fun he => h.ne (Subtype.ext (Sum.inr.inj he)))).monotone
    (relatorCircleFundamentalChain w j)

theorem baseIso_circle (p : PresCoverRelator w id) (x : RelatorCircle w p.1.2) :
    baseIso w (presCoverCircleCylinderInclusion w id (cover w) p x) =
      circleIntoCylinder w p.1.2 x := by
  apply (Sum.inl_injective : Function.Injective (Sum.inl : CylBase w → PresPos w))
  exact (coneAdjCoverBaseEnd_spec id
    (presCoverCircleCylinderInclusion w id (cover w) p x)).trans
      (presCoverConeCircleOrderIso_symm_projection w id (cover w) p.1.1 p.1.2 p.2 x)

theorem baseProjection_relatorBoundary (p : PresCoverRelator w id) :
    baseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      cylinderBoundary w p.1.2 := by
  change chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)
    (chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w id (cover w) p)
      (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)) _) = _
  erw [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict _ (presCoverCircleCylinderInclusion_strictMono w id (cover w) p)]
  erw [mapOne_comp (presCoverCircleCylinderInclusion w id (cover w) p)
    (presCoverCircleCylinderInclusion_strictMono w id (cover w) p).monotone
    (baseIso w) (baseIso w).monotone (relatorCircleFundamentalChain w p.1.2)]
  have he : baseIso w ∘ presCoverCircleCylinderInclusion w id (cover w) p =
      circleIntoCylinder w p.1.2 := funext (baseIso_circle w p)
  simp only [he]
  rfl

/-- The actual cylinder retraction, in literal rose-edge coordinates. -/
def roseProjection :
    (StrictOrdEdge (Base w) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Rose α) →₀ ℤ) :=
  (mapOne (cylRetr (aHom w)) (cylRetr_monotone (aHom w))).comp (baseProjection w)

theorem baseProjection_collapse_eq (c : StrictOrdEdge (Base w) →₀ ℤ) :
    baseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) =
      mapOne (cylIn (aHom w)) (cylIn_monotone (aHom w)) (roseProjection w c) := by
  erw [(mapOne_semiconj (baseIso w) (baseIso w).strictMono _ _ _ _ (baseIso_collapse w) c)]
  change mapOne (cylCollapse (aHom w)) _ (baseProjection w c) =
    mapOne (cylIn (aHom w)) _ (mapOne (cylRetr (aHom w)) _ (baseProjection w c))
  rw [mapOne_comp]; rfl

theorem collapsed_eq_zero_of_roseProjection_eq_zero
    (c : StrictOrdEdge (Base w) →₀ ℤ) (hc : roseProjection w c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c = 0 := by
  apply baseProjection_injective w
  erw [baseProjection_collapse_eq, hc, map_zero]

theorem roseProjection_collapse (c : StrictOrdEdge (Base w) →₀ ℤ) :
    roseProjection w (normalizedStrictChain1 (presCoverCylinderCollapse w id (cover w))
      (presCoverCylinderCollapse_monotone w id (cover w)) c) = roseProjection w c := by
  change mapOne (cylRetr (aHom w)) _ (baseProjection w _) = _
  erw [baseProjection_collapse_eq, mapOne_comp]
  exact mapOne_id _

def roseIntoBase (x : Rose α) : Base w :=
  ⟨ConeAdj.inc (cylIn (aHom w) x), ⟨cylIn (aHom w) x, rfl⟩⟩

theorem roseIntoBase_strictMono : StrictMono (roseIntoBase w) := by
  intro a b h
  exact lt_of_le_of_ne h.le (fun he => h.ne (Sum.inl.inj (Sum.inl.inj (congrArg Subtype.val he))))


def roseInclusion :
    (StrictOrdEdge (Rose α) →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Base w) →₀ ℤ) :=
  chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w))

theorem roseProjection_inclusion (c : StrictOrdEdge (Rose α) →₀ ℤ) :
    roseProjection w (roseInclusion w c) = c := by
  change mapOne (cylRetr (aHom w)) _
    (chain1 (strictOrderCxMap (baseIso w) (baseIso w).strictMono)
      (chain1 (strictOrderCxMap (roseIntoBase w) (roseIntoBase_strictMono w)) c)) = c
  erw [← mapOne_strict (baseIso w) (baseIso w).strictMono,
    ← mapOne_strict (roseIntoBase w) (roseIntoBase_strictMono w), mapOne_comp, mapOne_comp]
  have he : (cylRetr (aHom w) ∘ baseIso w) ∘ roseIntoBase w = id := by
    funext x
    exact congrArg (cylRetr (aHom w)) ((baseIso w).apply_symm_apply (cylIn (aHom w) x))
  simpa only [he] using (mapOne_id c)

end FiniteChains.PresModel.IdentityChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment
open Topology
open scoped Classical unitInterval Topology

universe u
variable {A X D : Type u} [TopologicalSpace X] [TopologicalSpace D]

theorem attachmentQuotientMap_isQuotientMap (r : A → X) (i : A → D) :
    IsQuotientMap (quotientMap r i) :=
  ⟨⟨rfl⟩, quotientMap_surjective r i⟩

omit [TopologicalSpace X] [TopologicalSpace D] in
/-- Injectivity of the attaching map keeps the entire disk embedded,
including its boundary. -/
theorem attachmentCell_injective (r : A → X) (i : A → D) (hr : Function.Injective r) :
    Function.Injective (cell r i) := by
  intro d e h
  by_cases hd : d ∈ Set.range i
  · by_cases he : e ∈ Set.range i
    · simp only [cell, dif_pos hd, dif_pos he] at h
      have ha := hr (Sum.inl.inj h)
      exact (Classical.choose_spec hd).symm.trans ((congrArg i ha).trans (Classical.choose_spec he))
    · simp only [cell, dif_pos hd, dif_neg he] at h
      exact (Sum.inl_ne_inr h).elim
  · by_cases he : e ∈ Set.range i
    · simp only [cell, dif_neg hd, dif_pos he] at h
      exact (Sum.inr_ne_inl h).elim
    · simp only [cell, dif_neg hd, dif_neg he] at h
      exact congrArg Subtype.val (Sum.inr.inj h)

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem attachmentCell_mem_old_iff (r : A → X) (i : A → D) (d : D) :
    cell r i d ∈ Set.range (old r i) ↔ d ∈ Set.range i := by
  by_cases hd : d ∈ Set.range i
  · simp only [cell, dif_pos hd]
    exact iff_of_true ⟨r (Classical.choose hd), rfl⟩ hd
  · constructor
    · rintro ⟨x, hx⟩
      rw [cell_of_not_mem r i d hd] at hx
      exact (Sum.inl_ne_inr hx).elim
    · exact fun h => (hd h).elim

abbrev PointAttachment (x : X) (d : D) :=
  Space (fun _ : PUnit => x) (fun _ : PUnit => d)

def pointOld (x : X) (d : D) : C(X, PointAttachment x d) :=
  ⟨old (fun _ : PUnit => x) (fun _ : PUnit => d), old_continuous _ _⟩

def pointCell (x : X) (d : D) : C(D, PointAttachment x d) :=
  ⟨cell (fun _ : PUnit => x) (fun _ : PUnit => d), cell_continuous _ _⟩

theorem pointCell_injective (x : X) (d : D) : Function.Injective (pointCell x d) :=
  attachmentCell_injective (fun _ : PUnit => x) (fun _ : PUnit => d)
    (fun _ _ _ => Subsingleton.elim _ _)

@[simp] theorem pointCell_mark (x : X) (d : D) : pointCell x d d = pointOld x d x :=
  cell_boundary (fun _ : PUnit => x) (fun _ : PUnit => d)
    (fun _ _ _ => Subsingleton.elim _ _) PUnit.unit

theorem pointCell_mem_old_iff (x : X) (d c : D) :
    pointCell x d c ∈ Set.range (pointOld x d) ↔ c = d := by
  change cell (fun _ : PUnit => x) (fun _ : PUnit => d) c ∈
    Set.range (old (fun _ : PUnit => x) (fun _ : PUnit => d)) ↔ c = d
  rw [attachmentCell_mem_old_iff]
  simp

def pointProjection (x : X) (d : D) : C(PointAttachment x d, X) :=
  desc (fun _ : PUnit => x) (fun _ : PUnit => d)
    (ContinuousMap.id X) (ContinuousMap.const D x) (fun _ => rfl)

@[simp] theorem pointProjection_old (x : X) (d : D) (y : X) :
    pointProjection x d (pointOld x d y) = y := rfl

@[simp] theorem pointProjection_cell (x : X) (d c : D) :
    pointProjection x d (pointCell x d c) = x := desc_cell ..


def pointAttachmentOldHomotopyEquiv (x : X) (d : D)
    (H : (ContinuousMap.const D d).Homotopy (ContinuousMap.id D))
    (hfix : ∀ t, H (t, d) = d) : ContinuousMap.HomotopyEquiv X (PointAttachment x d) where
  toFun := pointOld x d
  invFun := pointProjection x d
  left_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩
  right_inv := ⟨(by
    let F : C(I × X, PointAttachment x d) := (pointOld x d).comp ⟨Prod.snd, continuous_snd⟩
    let G : C(I × D, PointAttachment x d) := (pointCell x d).comp H.toContinuousMap
    have hbd : ∀ t (a : PUnit), F (t, x) = G (t, d) := by
      intro t _a
      change pointOld x d x = pointCell x d (H (t, d))
      rw [hfix, pointCell_mark]
    let L := attachmentHomotopyPasting (fun _ : PUnit => x) (fun _ : PUnit => d) F G hbd
    refine { toContinuousMap := L, map_zero_left := ?_, map_one_left := ?_ }
    · intro z
      obtain ⟨z, rfl⟩ := quotientMap_surjective (fun _ : PUnit => x) (fun _ : PUnit => d) z
      cases z with
      | inl y => rfl
      | inr c =>
          change attachmentHomotopyPasting _ _ F G hbd (0, cell _ _ c) =
            pointOld x d (pointProjection x d (pointCell x d c))
          rw [attachmentHomotopyPasting_cell, pointProjection_cell]
          change pointCell x d (H (0, c)) = pointOld x d x
          exact (congrArg (pointCell x d) (H.apply_zero c)).trans (pointCell_mark x d)
    · intro z
      obtain ⟨z, rfl⟩ := quotientMap_surjective (fun _ : PUnit => x) (fun _ : PUnit => d) z
      cases z with
      | inl y => rfl
      | inr c =>
          change attachmentHomotopyPasting _ _ F G hbd (1, cell _ _ c) = pointCell x d c
          rw [attachmentHomotopyPasting_cell]
          change pointCell x d (H (1, c)) = pointCell x d c
          exact congrArg (pointCell x d) (H.apply_one c))⟩

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def closedBallFromPointHomotopy (d : ClosedUnitBall E) :
    (ContinuousMap.const (ClosedUnitBall E) d).Homotopy (ContinuousMap.id (ClosedUnitBall E)) where
  toFun tx := ⟨(1 - (tx.1 : ℝ)) • d.val + (tx.1 : ℝ) • tx.2.val, by
    calc
      ‖(1 - (tx.1 : ℝ)) • d.val + (tx.1 : ℝ) • tx.2.val‖ ≤
          ‖(1 - (tx.1 : ℝ)) • d.val‖ + ‖(tx.1 : ℝ) • tx.2.val‖ := norm_add_le _ _
      _ = (1 - (tx.1 : ℝ)) * ‖d.val‖ + (tx.1 : ℝ) * ‖tx.2.val‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr tx.1.property.2),
          Real.norm_of_nonneg tx.1.property.1]
      _ ≤ (1 - (tx.1 : ℝ)) * 1 + (tx.1 : ℝ) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left d.property (sub_nonneg.mpr tx.1.property.2))
          (mul_le_mul_of_nonneg_left tx.2.property tx.1.property.1)
      _ = 1 := by ring⟩
  continuous_toFun := by fun_prop
  map_zero_left x := Subtype.ext (by simp)
  map_one_left x := Subtype.ext (by simp)

theorem closedBallFromPointHomotopy_fixed (d : ClosedUnitBall E) (t : I) :
    closedBallFromPointHomotopy d (t, d) = d := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • d.val + (t : ℝ) • d.val = d.val
  rw [← add_smul, sub_add_cancel, one_smul]

def pointBallAttachmentHomotopyEquiv (x : X) (d : ClosedUnitBall E) :
    ContinuousMap.HomotopyEquiv X (PointAttachment x d) :=
  pointAttachmentOldHomotopyEquiv x d (closedBallFromPointHomotopy d)
    (closedBallFromPointHomotopy_fixed d)

end FiniteChains.RelativeAttachment
end

namespace FiniteChains.RelativeAttachment
open Topology
open scoped Topology

universe u
variable {X C S D : Type u} [TopologicalSpace X] [TopologicalSpace C]
  [TopologicalSpace S] [TopologicalSpace D]
  (x : X) (c : C) (b : S ≃ₜ C) (i : C(S, D)) (hi : Function.Injective i)

def pointFillAttaching : C(S, PointAttachment x c) := (pointCell x c).comp b.toContinuousMap

abbrev FilledPointAttachment := Space (pointFillAttaching x c b) i

def pointFillBase : C(X, FilledPointAttachment x c b i) :=
  (⟨old (pointFillAttaching x c b) i, old_continuous _ _⟩ :
    C(PointAttachment x c, _)).comp (pointOld x c)

def pointFillDisk : C(D, FilledPointAttachment x c b i) :=
  ⟨cell (pointFillAttaching x c b) i, cell_continuous _ _⟩

include hi in
theorem pointFillDisk_boundary (a : S) :
    pointFillDisk x c b i (i a) = old (pointFillAttaching x c b) i (pointCell x c (b a)) :=
  cell_boundary _ _ hi a

include hi in
theorem pointFillDisk_circle (y : C) :
    pointFillDisk x c b i (i (b.symm y)) = old (pointFillAttaching x c b) i (pointCell x c y) := by
  rw [pointFillDisk_boundary x c b i hi, Homeomorph.apply_symm_apply]



theorem pointFillDisk_injective : Function.Injective (pointFillDisk x c b i) :=
  attachmentCell_injective _ _ ((pointCell_injective x c).comp b.injective)



/-- The two-stage pointed-boundary filling is literally a disk attached
at one point, with exact base and disk formulas. -/
def pointAttachmentFillingHomeomorph :
    PointAttachment x (i (b.symm c)) ≃ₜ FilledPointAttachment x c b i :=
  attachmentQuotientHomeomorph (fun _ : PUnit => x) (fun _ : PUnit => i (b.symm c))
    (pointFillBase x c b i) (pointFillDisk x c b i)
    (fun _ => (show pointFillDisk x c b i (i (b.symm c)) = pointFillBase x c b i x by
      rw [pointFillDisk_circle x c b i hi, pointCell_mark]
      rfl).symm)
    ((old_injective _ _).comp (old_injective _ _))
    (fun d => by
      rw [(show pointFillDisk x c b i d ∈ Set.range (pointFillBase x c b i) ↔ d = i (b.symm c) by
        have hrange : Set.range (pointFillBase x c b i) =
            old (pointFillAttaching x c b) i '' Set.range (pointOld x c) := by
          ext z
          constructor
          · rintro ⟨y, rfl⟩
            exact ⟨pointOld x c y, ⟨y, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
            exact ⟨t, rfl⟩
        rw [hrange]
        change d ∈ cell (pointFillAttaching x c b) i ⁻¹'
          (old (pointFillAttaching x c b) i '' Set.range (pointOld x c)) ↔ _
        rw [cell_preimage_old_image _ _ hi]
        constructor
        · rintro ⟨a, ha, had⟩
          have hac  := (pointCell_mem_old_iff x c (b a)).mp ha
          have he  := b.injective (hac.trans (b.apply_symm_apply c).symm)
          exact had.symm.trans (congrArg i he)
        · intro hd
          refine ⟨b.symm c, ?_, hd.symm⟩
          apply (pointCell_mem_old_iff x c (b (b.symm c))).mpr
          exact b.apply_symm_apply c)]
      constructor
      · exact fun hd => ⟨PUnit.unit, hd.symm⟩
      · rintro ⟨a, ha⟩
        exact ha.symm)
    (fun _ _ _ _ h => pointFillDisk_injective x c b i h)
    (by
      apply isQuotientMap_iff_isClosed.mpr
      constructor
      · intro z
        obtain ⟨z, rfl⟩ := quotientMap_surjective (pointFillAttaching x c b) i z
        cases z with
        | inl y =>
            obtain ⟨y, rfl⟩ := quotientMap_surjective (fun _ : PUnit => x) (fun _ : PUnit => c) y
            cases y with
            | inl t => exact ⟨Sum.inl t, rfl⟩
            | inr a => exact ⟨Sum.inr (i (b.symm a)), pointFillDisk_circle x c b i hi a⟩
        | inr d => exact ⟨Sum.inr d, rfl⟩
      · intro T
        constructor
        · exact fun hT => hT.preimage ((pointFillBase x c b i).continuous.sumElim
            (pointFillDisk x c b i).continuous)
        · intro hT
          have hX := hT.preimage (continuous_inl : Continuous (Sum.inl : X → X ⊕ D))
          have hD := hT.preimage (continuous_inr : Continuous (Sum.inr : D → X ⊕ D))
          apply isClosed_coinduced.mpr
          apply isClosed_sum_iff.mpr
          constructor
          · change IsClosed ((old (pointFillAttaching x c b) i) ⁻¹' T)
            apply isClosed_coinduced.mpr
            apply isClosed_sum_iff.mpr
            constructor
            · exact hX
            · have hc := hD.preimage (i.continuous.comp b.symm.continuous)
              convert hc using 1
              ext y
              exact iff_of_eq (congrArg (fun z => z ∈ T) (pointFillDisk_circle x c b i hi y).symm)
          · exact hD)



variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pointBoundaryFillingHomotopyEquiv (b : UnitBoundary E ≃ₜ C) :
    ContinuousMap.HomotopyEquiv X
      (FilledPointAttachment x c b (unitBoundaryInclusion E)) :=
  (pointBallAttachmentHomotopyEquiv x (unitBoundaryInclusion E (b.symm c))).trans
    (pointAttachmentFillingHomeomorph x c b (unitBoundaryInclusion E)
      (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall E => z.val) h))).toHomotopyEquiv


end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open Topology
open scoped Topology

universe u
variable {A D P K X : Type u}
  [TopologicalSpace D] [TopologicalSpace P] [TopologicalSpace K] [TopologicalSpace X]

theorem attachmentBaseMap_injective (r : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (he : Function.Injective e) :
    Function.Injective (attachmentBaseMap r i hi e) := by
  rintro (p | d) (q | u) h
  · exact congrArg Sum.inl (he (Sum.inl.inj h))
  · change Sum.inl (e p) = cell (e ∘ r) i u.val at h
    rw [cell_of_not_mem _ _ _ u.property] at h
    exact (Sum.inl_ne_inr h).elim
  · change cell (e ∘ r) i d.val = Sum.inl (e q) at h
    rw [cell_of_not_mem _ _ _ d.property] at h
    exact (Sum.inr_ne_inl h).elim
  · change cell (e ∘ r) i d.val = cell (e ∘ r) i u.val at h
    rw [cell_of_not_mem _ _ _ d.property, cell_of_not_mem _ _ _ u.property] at h
    exact congrArg Sum.inr (Sum.inr.inj h)

abbrev SingletonAttachment (i : A → D) := Space (fun _ : A => (PUnit.unit : PUnit)) i

def singletonAttachmentPoint (i : A → D) : SingletonAttachment i :=
  old (fun _ : A => (PUnit.unit : PUnit)) i PUnit.unit

def singletonAttachmentInto (x : X) (i : A → D) (hi : Function.Injective i) :
    C(SingletonAttachment i, Space (fun _ : A => x) i) :=
  attachmentBaseMap (fun _ : A => (PUnit.unit : PUnit)) i hi (ContinuousMap.const PUnit x)

theorem singletonAttachmentInto_injective (x : X) (i : A → D) (hi : Function.Injective i) :
    Function.Injective (singletonAttachmentInto x i hi) :=
  attachmentBaseMap_injective _ _ hi _ (fun _ _ _ => Subsingleton.elim _ _)

@[simp] theorem singletonAttachmentInto_point (x : X) (i : A → D) (hi : Function.Injective i) :
    singletonAttachmentInto x i hi (singletonAttachmentPoint i) = old (fun _ : A => x) i x := rfl

@[simp] theorem singletonAttachmentInto_cell (x : X) (i : A → D) (hi : Function.Injective i) (d : D) :
    singletonAttachmentInto x i hi (cell (fun _ : A => (PUnit.unit : PUnit)) i d) =
      cell (fun _ : A => x) i d := attachmentBaseMap_cell ..


theorem singletonAttachment_piece_isQuotientMap (x : X) (i : A → D) (hi : Function.Injective i) :
    IsQuotientMap (Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi)) := by
  let F : C(X ⊕ D, X ⊕ SingletonAttachment i) :=
    ⟨Sum.elim Sum.inl (fun d => Sum.inr (cell (fun _ : A => PUnit.unit) i d)),
      continuous_inl.sumElim (continuous_inr.comp (cell_continuous _ _))⟩
  let Q : C(X ⊕ SingletonAttachment i, Space (fun _ : A => x) i) :=
    ⟨Sum.elim (old (fun _ : A => x) i) (singletonAttachmentInto x i hi),
      (old_continuous _ _).sumElim (singletonAttachmentInto x i hi).continuous⟩
  have hf : Q ∘ F = quotientMap (fun _ : A => x) i := by
    funext z
    cases z with
    | inl y => rfl
    | inr d => exact singletonAttachmentInto_cell x i hi d
  apply IsQuotientMap.of_comp F.continuous Q.continuous
  rw [hf]
  exact attachmentQuotientMap_isQuotientMap _ _

def pointAttachmentBaseChangeHomeomorph (x : X) (i : A → D) (hi : Function.Injective i) :
    PointAttachment x (singletonAttachmentPoint i) ≃ₜ Space (fun _ : A => x) i :=
  attachmentQuotientHomeomorph (fun _ : PUnit => x) (fun _ : PUnit => singletonAttachmentPoint i)
    ⟨old (fun _ : A => x) i, old_continuous _ _⟩ (singletonAttachmentInto x i hi)
    (fun _ => rfl) (old_injective _ _)
    (fun z => by
      change singletonAttachmentInto x i hi z ∈ Set.range (old (fun _ : A => x) i) ↔
        z ∈ Set.range (fun _ : PUnit.{u + 1} => singletonAttachmentPoint i)
      rw [(show singletonAttachmentInto x i hi z ∈ Set.range (old (fun _ : A => x) i) ↔
      z = singletonAttachmentPoint i by
        rcases z with p | d
        · have hp : p = PUnit.unit := Subsingleton.elim _ _
          subst p
          exact iff_of_true ⟨x, rfl⟩ rfl
        · constructor
          · rintro ⟨y, hy⟩
            change Sum.inl y = cell (fun _ : A => x) i d.val at hy
            rw [cell_of_not_mem _ _ _ d.property] at hy
            exact (Sum.inl_ne_inr hy).elim
          · intro hz
            exact (Sum.inr_ne_inl hz).elim)]
      constructor
      · exact fun hz => ⟨PUnit.unit, hz.symm⟩
      · rintro ⟨a, ha⟩
        exact ha.symm)
    (fun _ _ _ _ h => singletonAttachmentInto_injective x i hi h)
    (singletonAttachment_piece_isQuotientMap x i hi)


@[simp] theorem pointAttachmentBaseChangeHomeomorph_cell
    (x : X) (i : A → D) (hi : Function.Injective i) (y : SingletonAttachment i) :
    pointAttachmentBaseChangeHomeomorph x i hi (pointCell x (singletonAttachmentPoint i) y) =
      singletonAttachmentInto x i hi y := attachmentQuotientHomeomorph_cell ..

def sigmaSingletonHomeomorph (Y : Type u) [TopologicalSpace Y] :
    (Σ _ : PUnit.{u + 1}, Y) ≃ₜ Y where
  toFun z := z.2
  invFun y := ⟨PUnit.unit, y⟩
  left_inv := by rintro ⟨u, y⟩; cases u; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_sigma (fun _ => continuous_id)
  continuous_invFun := continuous_sigmaMk (σ := fun _ : PUnit.{u + 1} => Y) (i := PUnit.unit)

variable {E : Type u} [NormedAddCommGroup E]

def singletonDiskAttaching (r : C(UnitBoundary E, X)) : C(BoundaryFamily PUnit E, X) :=
  r.comp (sigmaSingletonHomeomorph (UnitBoundary E)).toContinuousMap

def singletonDiskAttachmentHomeomorph (r : C(UnitBoundary E, X)) :
    DiskAttachment (singletonDiskAttaching r) ≃ₜ Space r (unitBoundaryInclusion E) :=
  attachmentDiagramHomeomorph (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E)
    r (unitBoundaryInclusion E) (sigmaSingletonHomeomorph (UnitBoundary E)).toEquiv
    (Homeomorph.refl X) (sigmaSingletonHomeomorph (ClosedUnitBall E))
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall E => z.val) h))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit E).injective

@[simp] theorem singletonDiskAttachmentHomeomorph_old (r : C(UnitBoundary E, X)) (x : X) :
    singletonDiskAttachmentHomeomorph r (old (singletonDiskAttaching r) (boundaryFamilyInclusion PUnit E) x) =
      old r (unitBoundaryInclusion E) x := rfl


end FiniteChains.RelativeAttachment

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Topology

/-- An actual parametrized circle, including the direction of its
once-around traversal. It is not a chosen homotopy-type comparison. -/
def dummyCircleBoundaryHomeomorph : UnitBoundary (Fin 2 → ℝ) ≃ₜ Rose PUnit :=
  PresModel.roseFourCycle.boundaryHomeomorph.symm.trans
    (PresModel.orderRoseRealizationHomeomorph PUnit)

variable {X : Type} [TopologicalSpace X] (x : X)

def dummyOneAttaching : C(BoundaryFamily PUnit (Fin 1 → ℝ), X) :=
  ContinuousMap.const _ x

def dummyLoopMap : C(Rose PUnit, DiskAttachment (dummyOneAttaching x)) :=
  singletonAttachmentInto x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective

def dummyFillingBoundary : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (dummyOneAttaching x)) :=
  (dummyLoopMap x).comp dummyCircleBoundaryHomeomorph.toContinuousMap

def dummyTwoAttaching :
    C(BoundaryFamily PUnit (Fin 2 → ℝ), DiskAttachment (dummyOneAttaching x)) :=
  singletonDiskAttaching (dummyFillingBoundary x)

abbrev DummyLoopFilled := DiskAttachment (dummyTwoAttaching x)

def dummyLoopPointHomeomorph :
    PointAttachment x (roseVertex PUnit) ≃ₜ DiskAttachment (dummyOneAttaching x) :=
  pointAttachmentBaseChangeHomeomorph x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective


@[simp] theorem dummyLoopPointHomeomorph_cell (y : Rose PUnit) :
    dummyLoopPointHomeomorph x (pointCell x (roseVertex PUnit) y) = dummyLoopMap x y :=
  pointAttachmentBaseChangeHomeomorph_cell ..


def dummyLoopFillingHomotopyEquiv : ContinuousMap.HomotopyEquiv X (DummyLoopFilled x) :=
  ((pointBoundaryFillingHomotopyEquiv x (roseVertex PUnit) dummyCircleBoundaryHomeomorph).trans
    (attachmentDiagramHomeomorph
    (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
    (unitBoundaryInclusion (Fin 2 → ℝ))
    (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ))
    (Equiv.refl _) (dummyLoopPointHomeomorph x) (Homeomorph.refl _)
    (fun a => dummyLoopPointHomeomorph_cell x (dummyCircleBoundaryHomeomorph a))
    (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))).toHomotopyEquiv).trans
      (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).symm.toHomotopyEquiv



end FiniteChains.ClassicalGraphModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalGraphModel.BoundaryWords
open RelativeAttachment ContinuousEdgeWords
open scoped Classical unitInterval

variable {V J : Type} [TopologicalSpace V]
    {r : BoundaryFamily J (Fin 1 → ℝ) → V} (W : BoundaryWords r)

theorem corner01Eq : squareSideMap (0, false) 1 = squareSideMap (1, true) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner11Eq : squareSideMap (1, true) 1 = squareSideMap (0, true) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner10Eq : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner00Eq : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem realize_cast_eq {V E X : Type} [TopologicalSpace X]
    (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))
    (l : List (E × Bool)) {a b a' b' : V}
    (hl : Comb.IsPath src tgt l a b) (hl' : Comb.IsPath src tgt l a' b')
    (ha : a' = a) (hb : b' = b) :
    (realize src tgt v edge l hl).cast (congrArg v ha) (congrArg v hb) =
      realize src tgt v edge l hl' := by
  cases ha
  cases hb
  rfl

def loopRealization :
    Path (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00))
      (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00)) :=
  realize (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J _))
    (graphEdgePath r) W.loopWord W.loopWord_isPath

theorem corner_value (s : SquareSide) (t : I) (ht : t = 0 ∨ t = 1) :
    W.squareMap (squareSideMap s t) =
      old r (boundaryFamilyInclusion J _) (W.vertex (squareSideMap s t)) :=
  (W.squareMap_side s t).trans (W.sidePath_endpoint s t ht)

def baseEquality : old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00) =
    W.squareMap squareCorner00 := (corner_value W (0, false) 0 (Or.inl rfl)).symm

def basedTraversal :
    Path (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00))
      (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00)) :=
  (squareBoundaryTraversal.map W.squareMap.continuous).cast W.baseEquality W.baseEquality



def loopBoundaryMap : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r) :=
  (squareLoopDesc W.loopRealization).comp unitBoundarySquareHomeomorph.toContinuousMap


theorem boundaryMap_homotopic_word : W.boundaryMap.Homotopic
    ((squareLoopDesc (realize (graphSrc r) (graphTgt r)
      (old r (boundaryFamilyInclusion J _)) (graphEdgePath r)
      W.loopWord W.loopWord_isPath)).comp unitBoundarySquareHomeomorph.toContinuousMap) :=
  (by
    have H := squareLoopDesc_homotopic (show W.basedTraversal.Homotopic W.loopRealization by
      let vG := old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      let a₀ := W.vertex squareCorner00
      let a₁ := W.vertex squareCorner01
      let a₂ := W.vertex squareCorner11
      let a₃ := W.vertex squareCorner10
      have e₀ : vG a₀ = W.squareMap squareCorner00 := W.baseEquality
      have e₁ : vG a₁ = W.squareMap squareCorner01 :=
        (corner_value W (0, false) 1 (Or.inr rfl)).symm
      have e₂ : vG a₂ = W.squareMap squareCorner11 :=
        (corner_value W (0, true) 1 (Or.inr rfl)).symm
      have e₃ : vG a₃ = W.squareMap squareCorner10 :=
        (corner_value W (0, true) 0 (Or.inl rfl)).symm
      let D₀ := (squareTraversalLeft.map W.squareMap.continuous).cast e₀ e₁
      let D₁ := (squareTraversalTop.map W.squareMap.continuous).cast e₁ e₂
      let D₂ := (squareTraversalRight.map W.squareMap.continuous).cast e₂ e₃
      let D₃ := (squareTraversalBottom.map W.squareMap.continuous).cast e₃ e₀
      have ht : W.basedTraversal = (D₀.trans D₁).trans (D₂.trans D₃) := by
        unfold basedTraversal squareBoundaryTraversal
        rw [Path.map_trans, Path.map_trans, Path.map_trans]
        rfl
      let l₀ := W.word (0, false)
      let l₁ := W.word (1, true)
      let l₂ := Comb.revPath (X := graphCx r) (W.word (0, true))
      let l₃ := Comb.revPath (X := graphCx r) (W.word (1, false))
      have hw₀ : Comb.IsPath (graphSrc r) (graphTgt r) l₀ a₀ a₁ := W.isPath (0, false)
      have hw₁ : Comb.IsPath (graphSrc r) (graphTgt r) l₁ a₁ a₂ := by
        have hh := W.isPath (1, true)
        rw [← corner01Eq, corner11Eq] at hh
        exact hh
      have hw₂ : Comb.IsPath (graphSrc r) (graphTgt r) l₂ a₂ a₃ :=
        Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
      have hw₃ : Comb.IsPath (graphSrc r) (graphTgt r) l₃ a₃ a₀ := by
        have hh := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
        rw [← corner10Eq, corner00Eq] at hh
        exact hh
      let R₀ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₀ hw₀
      let R₁ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₁ hw₁
      let R₂ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₂ hw₂
      let R₃ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃ hw₃
      have H₀ : D₀.Homotopic R₀ := by
        have he : D₀ = R₀ := by
          apply Path.ext
          funext t
          exact W.squareMap_side (0, false) t
        simpa only [he] using Path.Homotopic.refl R₀
      have H₁ : D₁.Homotopic R₁ := by
        have ha  := congrArg W.vertex corner01Eq
        have hb  := congrArg W.vertex corner11Eq.symm
        have hd : D₁ = (W.sidePath (1, true)).cast (congrArg vG ha) (congrArg vG hb) := by
          apply Path.ext
          funext t
          exact W.squareMap_side (1, true) t
        have he : D₁ = R₁ := hd.trans (realize_cast_eq (graphSrc r) (graphTgt r) vG
          (graphEdgePath r) l₁ (W.isPath (1, true)) hw₁ ha hb)
        simpa only [he] using Path.Homotopic.refl R₁
      have H₂ : D₂.Homotopic R₂ := by
        have hd : D₂ = (W.sidePath (0, true)).symm := by
          apply Path.ext
          funext t
          exact W.squareMap_side (0, true) (unitInterval.symm t)
        rw [hd]
        exact realize_revPath (K := graphCx r) vG (graphEdgePath r)
          (W.word (0, true)) (W.isPath (0, true))
      have H₃ : D₃.Homotopic R₃ := by
        have ha : a₃ = W.vertex (squareSideMap (1, false) 1) := congrArg W.vertex corner10Eq
        have hb : a₀ = W.vertex (squareSideMap (1, false) 0) := congrArg W.vertex corner00Eq.symm
        have hd : (W.sidePath (1, false)).symm.cast (congrArg vG ha) (congrArg vG hb) = D₃ := by
          apply Path.ext
          funext t
          exact (W.squareMap_side (1, false) (unitInterval.symm t)).symm
        have HH := (realize_revPath (K := graphCx r) vG (graphEdgePath r)
          (W.word (1, false)) (W.isPath (1, false))).pathCast (congrArg vG ha) (congrArg vG hb)
        have hr : (realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃
            (Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false)))).cast
              (congrArg vG ha) (congrArg vG hb) = R₃ :=
          realize_cast_eq (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃ _ hw₃ ha hb
        change ((W.sidePath (1, false)).symm.cast (congrArg vG ha) (congrArg vG hb)).Homotopic
          ((realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃
            (Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false)))).cast
              (congrArg vG ha) (congrArg vG hb)) at HH
        rw [hd, hr] at HH
        exact HH
      have Hs : W.basedTraversal.Homotopic ((R₀.trans R₁).trans (R₂.trans R₃)) := by
        rw [ht]
        exact (H₀.hcomp H₁).hcomp (H₂.hcomp H₃)
      have Hleft := realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₀ l₁ hw₀ hw₁
      have Hright := realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₂ l₃ hw₂ hw₃
      have Happend := realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r)
        (l₀ ++ l₁) (l₂ ++ l₃) (hw₀.append hw₁) (hw₂.append hw₃)
      have Hall := Hs.trans ((Hleft.hcomp Hright).trans Happend)
      simpa only [loopRealization, loopWord, l₀, l₁, l₂, l₃, List.append_eq, List.append_assoc] using Hall)
    rw [(show squareLoopDesc W.basedTraversal = W.squareMap by
      have hc : squareLoopDesc W.basedTraversal =
          squareLoopDesc (squareBoundaryTraversal.map W.squareMap.continuous) := by
        apply ContinuousMap.ext
        intro z
        rfl
      exact hc.trans (squareLoopDesc_map W.squareMap))] at H
    exact H.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap))

end FiniteChains.ClassicalGraphModel.BoundaryWords
end

section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel ContinuousEdgeWords

variable {A B : Type}

theorem classicalRoseRead_map (f : A → B) (l : List (A × Bool)) (t : I) :
    diskRoseMap f (classicalRoseRead l t) =
      classicalRoseRead (l.map (fun p => (f p.1, p.2))) t := by
  induction l generalizing t with
  | nil => exact diskRoseMap_vertex f
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [List.map_cons, classicalRoseRead, Path.trans_apply, dif_pos ht, if_pos ht]
      cases b <;> simp
      all_goals exact diskRoseMap_cell f _
    · simp only [List.map_cons, classicalRoseRead, Path.trans_apply, dif_neg ht, if_neg ht]
      exact ih _

theorem classicalRoseWordBoundary_map (f : A → B) (l : List (A × Bool)) :
    (diskRoseMap f).comp (classicalRoseWordBoundary l) =
      classicalRoseWordBoundary (l.map (fun p => (f p.1, p.2))) := by
  apply ContinuousMap.ext
  intro z
  exact classicalRoseRead_map f l _

theorem classicalRoseRead_eq_realize_apply (l : List (A × Bool))
    {a b : PUnit}
    (hl : IsPath (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A)) l a b) (t : I) :
    classicalRoseRead l t = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl t := by
  cases a
  cases b
  exact congrArg (fun p => p t) (classicalRoseRead_eq_realize l hl)

theorem boundaryWords_homotopic_classicalWord (W : BoundaryWords (roseAttaching A)) :
    W.boundaryMap.Homotopic (classicalRoseWordBoundary W.loopWord) := by
  have H := W.boundaryMap_homotopic_word
  have he : ((squareLoopDesc (realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) W.loopWord W.loopWord_isPath)).comp
        unitBoundarySquareHomeomorph.toContinuousMap) = classicalRoseWordBoundary W.loopWord := by
    apply ContinuousMap.ext
    intro z
    exact (classicalRoseRead_eq_realize_apply W.loopWord W.loopWord_isPath _).symm
  rwa [he] at H

theorem roseCopyRealization_unit (x : orderNerveRealization (Rose PUnit)) :
    roseCopyRealization PUnit.unit x = x := by
  change orderNerveRealizationMap (roseCopy PUnit.unit) (roseCopy PUnit.unit).monotone x = x
  have hf : (roseCopy PUnit.unit : Rose PUnit → Rose PUnit) = id := by
    funext p
    cases p with
    | base => rfl
    | mid u => rfl
    | edg u b => rfl
  have mapEq g hg (he : g = id) :
      orderNerveRealizationMap g hg x = x := by
    subst g
    exact orderNerveRealizationMap_id _ _
  grind


theorem dummyCircleBoundaryHomeomorph_eq :
    dummyCircleBoundaryHomeomorph.toContinuousMap =
      (squareLoopDesc (graphEdgePath (roseAttaching PUnit) PUnit.unit)).comp
        unitBoundarySquareHomeomorph.toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht⟩ := squareBoundaryTraversal_surjective (unitBoundarySquareHomeomorph z)
  have hz : unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t) = z := by
    rw [ht, Homeomorph.symm_apply_apply]
  rw [← hz]
  change dummyCircleBoundaryHomeomorph
    (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)) =
      squareLoopDesc (graphEdgePath (roseAttaching PUnit) PUnit.unit)
    (unitBoundarySquareHomeomorph (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)))
  rw [Homeomorph.apply_symm_apply, squareLoopDesc_traversal]
  exact (by
    change orderRoseRealizationHomeomorph PUnit
      (roseFourCycle.boundaryHomeomorph.symm
        (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t))) = _
    rw [← roseFourCycle.boundaryHomeomorph_traversal, Homeomorph.symm_apply_apply]
    change orderRoseRealizationHomeomorph PUnit (orderRoseTraversal t) = _
    rw [← roseCopyRealization_unit (orderRoseTraversal t), orderRoseRealizationHomeomorph_interval]
    rfl)

theorem dummyCircleBoundaryHomeomorph_homotopic_word :
    dummyCircleBoundaryHomeomorph.toContinuousMap.Homotopic
      (classicalRoseWordBoundary [(PUnit.unit, true)]) := by
  have H := (squareLoopDesc_homotopic
    (Path.Homotopic.trans_refl (graphEdgePath (roseAttaching PUnit) PUnit.unit)).symm).comp
      (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  rw [← dummyCircleBoundaryHomeomorph_eq] at H
  exact H

end FiniteChains.PresModel
end

section
open scoped Classical
open Set Topology
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment ClassicalGraphModel ContinuousEdgeWords

variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]

theorem isClosed_of_closedCell_constant (S : Set X)
    (hS : ∀ n (j : RelCWComplex.cell (Set.univ : Set X) n),
      CWComplex.closedCell n j ⊆ S ∨ Disjoint (CWComplex.closedCell n j) S) : IsClosed S := by
  apply (CWComplex.closed Set.univ S (Set.subset_univ _)).mpr
  intro n j
  rcases hS n j with h | h
  · rw [Set.inter_eq_right.mpr h]
    exact CWComplex.isClosed_closedCell
  · rw [Set.disjoint_iff_inter_eq_empty.mp h.symm]
    exact isClosed_empty


/-- Connected classical CW complexes are actually path connected. -/
theorem cw_pathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X where
  nonempty := inferInstance
  joined x y := by
    have h := (show IsClopen (pathComponent x) by
      have hcell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
          CWComplex.closedCell n j ⊆ pathComponent x ∨
            Disjoint (CWComplex.closedCell n j) (pathComponent x) := by
        by_cases h : (CWComplex.closedCell n j ∩ pathComponent x).Nonempty
        · obtain ⟨y, hy, hxy⟩ := h
          left
          intro z hz
          exact hxy.trans ((closedCell_joined n j hy hz).joined)
        · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h))
      refine ⟨isClosed_of_closedCell_constant (pathComponent x) hcell, ?_⟩
      apply isClosed_compl_iff.mp
      apply isClosed_of_closedCell_constant
      grind).eq_univ (pathComponent.nonempty x)
    exact (show y ∈ pathComponent x from by rw [h]; trivial)

theorem zeroSkeleton_cellSeparated :
    CellSeparated (CWComplex.skeletonLT (Set.univ : Set X) (1 : ℕ∞) : Set X) := by
  intro n j
  by_cases hn : n = 0
  · subst n
    exact (Set.subsingleton_singleton).anti (by
      intro x hx
      simpa only [CWComplex.openCell_zero_eq_singleton] using hx.2)
  · intro x hx y hy
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)) hx.1 hx.2)

theorem zeroSkeleton_discrete :
    DiscreteTopology (SkeletonCarrier (Set.univ : Set X) 1) :=
  (zeroSkeleton_cellSeparated (X := X)).isDiscrete.to_subtype

def zeroCellPoint (j : RelCWComplex.cell (Set.univ : Set X) 0) :
    SkeletonCarrier (Set.univ : Set X) 1 :=
  ⟨vertexPoint j, CWComplex.closedCell_subset_skeletonLT 0 j
    (by rw [CWComplex.closedCell_zero_eq_singleton]; rfl)⟩


/-- The literal original zero-cells label the vertices bijectively. -/
def zeroCellEquiv : RelCWComplex.cell (Set.univ : Set X) 0 ≃
    SkeletonCarrier (Set.univ : Set X) 1 :=
  Equiv.ofBijective zeroCellPoint (by
    constructor
    · intro i j h
      have hi : vertexPoint i ∈ CWComplex.openCell 0 i := by
        rw [CWComplex.openCell_zero_eq_singleton]
        rfl
      have hj : vertexPoint i ∈ CWComplex.openCell 0 j := by
        have hv : vertexPoint i = vertexPoint j := congrArg Subtype.val h
        rw [hv, CWComplex.openCell_zero_eq_singleton]
        rfl
      have hlabel := RelCWComplex.eq_of_not_disjoint_openCell
        (fun hd => Set.disjoint_left.mp hd hi hj)
      exact eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
    · intro x
      have hx := x.property
      change x.val ∈ (CWComplex.skeletonLT (Set.univ : Set X) (1 : ℕ∞) : Set X) at hx
      rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx
      obtain ⟨n, hn, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
      have hn' : n < 1 := by exact_mod_cast hn
      have hn0 : n = 0 := by omega
      subst n
      refine ⟨j, Subtype.ext ?_⟩
      exact (show x.val = vertexPoint j from by
        simpa only [CWComplex.openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint] using hj).symm)

variable (K : Whitehead.TwoComplex)


theorem oneSkeleton_pathConnectedSpace : PathConnectedSpace (OneSkeleton K) where
  nonempty := (by
    let x : K := Classical.choice inferInstance
    let j := pointVertex x
    exact ⟨skeletonInclusion (Set.univ : Set K) 1 (zeroCellPoint j)⟩)
  joined x y := by
    letI := cw_pathConnectedSpace (X := K)
    obtain ⟨p⟩ := PathConnectedSpace.joined x.val y.val
    obtain ⟨q, _⟩ := path_into_oneSkeleton K x y p
    exact ⟨q⟩

abbrev originalGraphAttaching := skeletonAttachingMap (Set.univ : Set K) 1

def originalGraph : Comb.Complex2 := graphCx (originalGraphAttaching K)


/-- The original graph admits a spanning tree, including for arbitrary
infinite cell families. Its existence uses actual continuous connectedness. -/
theorem originalGraph_exists_spanningTree (v : SkeletonCarrier (Set.univ : Set K) 1) :
    ∃ T : Comb.SpanningTree (originalGraph K), T.root = v :=
  Comb.SpanningTree.exists_of_isConnected (by
    letI := zeroSkeleton_discrete (X := K)
    letI : PathConnectedSpace (SkeletonCarrier (Set.univ : Set K) 2) :=
      oneSkeleton_pathConnectedSpace K
    let e := skeletonAsDiskAttachment (Set.univ : Set K) 1
    letI : PathConnectedSpace (DiskAttachment (originalGraphAttaching K)) :=
      e.surjective.pathConnectedSpace e.continuous
    exact graphCx_isConnected (originalGraphAttaching K) (originalGraphAttaching K).continuous) v

end FiniteChains.ClassicalCW
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical unitInterval

variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {C D E : CWComplex.Subcomplex (Set.univ : Set X)}

theorem subcomplex_cell_mono (h : (C : Set X) ⊆ D) (n : ℕ) : C.I n ⊆ D.I n := by
  intro j hj
  have hx := CWComplex.map_zero_mem_openCell n j
  have hxD := h (C.openCell_subset_of_mem hj hx)
  by_contra hn
  exact Set.disjoint_left.mp (D.disjoint_openCell_subcomplex_of_not_mem hn) hx hxD

def subcomplexCellInclusion (h : (C : Set X) ⊆ D) (n : ℕ) :
    RelCWComplex.cell (C : Set X) n ↪ RelCWComplex.cell (D : Set X) n :=
  ⟨fun j => ⟨j.val, subcomplex_cell_mono h n j.property⟩,
    fun _ _ he => Subtype.ext (congrArg (fun z : RelCWComplex.cell (D : Set X) n => z.val) he)⟩

theorem subcomplex_skeleton_mono (h : (C : Set X) ⊆ D) (n : ℕ) :
    (CWComplex.skeletonLT (C : Set X) (n : ℕ∞) : Set X) ⊆
      CWComplex.skeletonLT (D : Set X) (n : ℕ∞) := by
  intro x hx
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
  obtain ⟨m, hm, j, hxj⟩ := by simpa only [Set.mem_iUnion] using hx
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm,
    Set.mem_iUnion.mpr ⟨subcomplexCellInclusion h m j, hxj⟩⟩⟩

def subcomplexSkeletonInclusion (h : (C : Set X) ⊆ D) (n : ℕ) :
    C(SkeletonCarrier (C : Set X) n, SkeletonCarrier (D : Set X) n) :=
  ⟨fun x => ⟨x.val, subcomplex_skeleton_mono h n x.property⟩,
    continuous_subtype_val.subtype_mk _⟩


def subcomplexGraph (C : CWComplex.Subcomplex (Set.univ : Set X)) : Comb.Complex2 :=
  graphCx (skeletonAttachingMap (C : Set X) 1)

def subcomplexGraphInclusion (h : (C : Set X) ⊆ D) :
    Comb.Hom (subcomplexGraph C) (subcomplexGraph D) where
  onV := subcomplexSkeletonInclusion h 1
  onE := subcomplexCellInclusion h 1
  onF := Empty.elim
  src_onE _ := Subtype.ext rfl
  tgt_onE _ := Subtype.ext rfl
  base_onF f := Empty.elim f
  att_onF f := Empty.elim f

theorem subcomplexGraphInclusion_injective_V (h : (C : Set X) ⊆ D) :
    Function.Injective (subcomplexGraphInclusion h).onV :=
  (fun _ _ he => Subtype.ext (congrArg (fun z : SkeletonCarrier (D : Set X) 1 => z.val) he))

theorem subcomplexGraphInclusion_injective_E (h : (C : Set X) ⊆ D) :
    Function.Injective (subcomplexGraphInclusion h).onE :=
  (subcomplexCellInclusion h 1).injective

theorem subcomplexGraphInclusion_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) :
    (subcomplexGraphInclusion k).comp (subcomplexGraphInclusion h) =
      subcomplexGraphInclusion (h.trans k) := by
  refine Comb.Hom.ext' ?_ ?_ ?_
  · rfl
  · rfl
  · funext f
    exact Empty.elim f

theorem subcomplexZeroSkeleton_discrete (C : CWComplex.Subcomplex (Set.univ : Set X)) :
    DiscreteTopology (SkeletonCarrier (C : Set X) 1) := by
  have hs : (CWComplex.skeletonLT (C : Set X) 1 : Set X) ⊆
      (CWComplex.skeletonLT (Set.univ : Set X) 1) := by
    intro x hx
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
    obtain ⟨n, hn, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn,
      Set.mem_iUnion.mpr ⟨j.val, hj⟩⟩⟩
  exact ((zeroSkeleton_cellSeparated).mono hs).isDiscrete.to_subtype

def subcomplexDiskMap (h : (C : Set X) ⊆ D) (n : ℕ) :
    C(DiskAttachment (skeletonAttachingMap (C : Set X) n),
      DiskAttachment (skeletonAttachingMap (D : Set X) n)) :=
  (⟨_, (skeletonAsDiskAttachment (D : Set X) n).continuous⟩ :
      C(SkeletonCarrier (D : Set X) (n + 1), _)).comp
    ((subcomplexSkeletonInclusion h (n + 1)).comp
      ⟨_, (skeletonAttachmentHomeomorph (C : Set X) n).continuous⟩)

theorem subcomplexDiskMap_skeleton (h : (C : Set X) ⊆ D) (n : ℕ)
    (z : DiskAttachment (skeletonAttachingMap (C : Set X) n)) :
    skeletonAttachmentHomeomorph (D : Set X) n (subcomplexDiskMap h n z) =
      subcomplexSkeletonInclusion h (n + 1) (skeletonAttachmentHomeomorph (C : Set X) n z) :=
  (skeletonAttachmentHomeomorph (D : Set X) n).apply_symm_apply _

theorem subcomplexDiskMap_old (h : (C : Set X) ⊆ D) (n : ℕ)
    (x : SkeletonCarrier (C : Set X) n) :
    subcomplexDiskMap h n (old (skeletonAttachingMap (C : Set X) n) _ x) =
      old (skeletonAttachingMap (D : Set X) n) _ (subcomplexSkeletonInclusion h n x) := by
  apply (skeletonAttachmentHomeomorph (D : Set X) n).injective
  rw [subcomplexDiskMap_skeleton]
  ext
  rfl

theorem subcomplexDiskMap_cell (h : (C : Set X) ⊆ D) (n : ℕ)
    (j : RelCWComplex.cell (C : Set X) n) (x : ClosedUnitBall (Fin n → ℝ)) :
    subcomplexDiskMap h n (cell (skeletonAttachingMap (C : Set X) n) _ ⟨j, x⟩) =
      cell (skeletonAttachingMap (D : Set X) n) _ ⟨subcomplexCellInclusion h n j, x⟩ := by
  apply (skeletonAttachmentHomeomorph (D : Set X) n).injective
  rw [subcomplexDiskMap_skeleton]
  ext
  change (skeletonAttachmentHomeomorph (C : Set X) n (cell _ _ ⟨j, x⟩)).val = _
  rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]
  rfl

def subcomplexGraphDiskMap (h : (C : Set X) ⊆ D) :
    C(DiskAttachment (skeletonAttachingMap (C : Set X) 1),
      DiskAttachment (skeletonAttachingMap (D : Set X) 1)) := subcomplexDiskMap h 1

theorem subcomplexGraphDiskMap_skeleton (h : (C : Set X) ⊆ D)
    (z : DiskAttachment (skeletonAttachingMap (C : Set X) 1)) :
    skeletonAttachmentHomeomorph (D : Set X) 1 (subcomplexGraphDiskMap h z) =
      subcomplexSkeletonInclusion h 2 (skeletonAttachmentHomeomorph (C : Set X) 1 z) :=
  (skeletonAttachmentHomeomorph (D : Set X) 1).apply_symm_apply _

theorem subcomplexGraphDiskMap_old (h : (C : Set X) ⊆ D)
    (v : (subcomplexGraph C).V) :
    subcomplexGraphDiskMap h
      (old (skeletonAttachingMap (C : Set X) 1) _ v) =
      old (skeletonAttachingMap (D : Set X) 1) _ ((subcomplexGraphInclusion h).onV v) := by
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  rw [subcomplexGraphDiskMap_skeleton]
  ext
  rfl

theorem subcomplexGraphDiskMap_edge (h : (C : Set X) ⊆ D)
    (j : (subcomplexGraph C).E) (t : I) :
    subcomplexGraphDiskMap h (graphEdgePath (skeletonAttachingMap (C : Set X) 1) j t) =
      graphEdgePath (skeletonAttachingMap (D : Set X) 1)
        ((subcomplexGraphInclusion h).onE j) t := by
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  rw [subcomplexGraphDiskMap_skeleton]
  ext
  change (skeletonAttachmentHomeomorph C 1
    (cell _ _ ⟨j, graphDiskHomeomorph t⟩)).val =
    (skeletonAttachmentHomeomorph (D : Set X) 1
      (cell _ _ ⟨subcomplexCellInclusion h 1 j, graphDiskHomeomorph t⟩)).val
  rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]
  rfl

theorem subcomplexGraphDiskMap_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) :
    (subcomplexGraphDiskMap k).comp (subcomplexGraphDiskMap h) =
      subcomplexGraphDiskMap (h.trans k) := by
  ext z
  apply (skeletonAttachmentHomeomorph (E : Set X) 1).injective
  change skeletonAttachmentHomeomorph (E : Set X) 1
    (subcomplexGraphDiskMap k (subcomplexGraphDiskMap h z)) =
    skeletonAttachmentHomeomorph (E : Set X) 1 (subcomplexGraphDiskMap (h.trans k) z)
  rw [subcomplexGraphDiskMap_skeleton, subcomplexGraphDiskMap_skeleton,
    subcomplexGraphDiskMap_skeleton]
  rfl

end FiniteChains.ClassicalCW
end

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {C D : CWComplex.Subcomplex (Set.univ : Set X)}

def subcomplexCellBoundary (C : CWComplex.Subcomplex (Set.univ : Set X))
    (j : RelCWComplex.cell (C : Set X) 2) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (skeletonAttachingMap (C : Set X) 1)) := by
  let a : C(UnitBoundary (Fin 2 → ℝ),
      BoundaryFamily (RelCWComplex.cell (C : Set X) 2) (Fin 2 → ℝ)) :=
    ⟨fun x => ⟨j, x⟩, continuous_sigmaMk
      (σ := fun _ : RelCWComplex.cell (C : Set X) 2 => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩
  exact (skeletonAsDiskAttachment (C : Set X) 1).toContinuousMap.comp
    ((skeletonAttachingMap (C : Set X) 2).comp a)

theorem subcomplexCellBoundary_natural (h : (C : Set X) ⊆ D)
    (j : RelCWComplex.cell (C : Set X) 2) :
    (subcomplexGraphDiskMap h).comp (subcomplexCellBoundary C j) =
      subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) := by
  ext a
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  change skeletonAttachmentHomeomorph (D : Set X) 1
    (subcomplexGraphDiskMap h (subcomplexCellBoundary C j a)) =
    skeletonAttachmentHomeomorph (D : Set X) 1
      (subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) a)
  rw [subcomplexGraphDiskMap_skeleton]
  change subcomplexSkeletonInclusion h 2
      ((skeletonAttachmentHomeomorph (C : Set X) 1)
        ((skeletonAttachmentHomeomorph (C : Set X) 1).symm _)) =
    (skeletonAttachmentHomeomorph (D : Set X) 1)
      ((skeletonAttachmentHomeomorph (D : Set X) 1).symm _)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rfl

theorem subcomplexCellBoundary_word_exists
    (C : CWComplex.Subcomplex (Set.univ : Set X))
    (j : RelCWComplex.cell (C : Set X) 2) :
    ∃ W : BoundaryWords (skeletonAttachingMap (C : Set X) 1),
      (subcomplexCellBoundary C j).Homotopic W.boundaryMap := by
  letI := subcomplexZeroSkeleton_discrete C
  exact boundaryMap_homotopic_boundaryWords (skeletonAttachingMap (C : Set X) 1)
    (skeletonAttachingMap (C : Set X) 1).continuous (subcomplexCellBoundary C j)

theorem subcomplexBoundaryWord_map (h : (C : Set X) ⊆ D)
    (W : BoundaryWords (skeletonAttachingMap (C : Set X) 1)) :
    (subcomplexGraphDiskMap h).comp W.boundaryMap =
      (W.map (subcomplexGraphInclusion h)).boundaryMap :=
  W.boundaryMap_map (subcomplexGraphInclusion h) (subcomplexGraphDiskMap h)
    (subcomplexGraphDiskMap_old h) (subcomplexGraphDiskMap_edge h)

end FiniteChains.ClassicalCW

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set X))
  (hC : Monotone C)

/-- Actual circle words and their homotopies. A seeded relative construction
may prescribe these on C0; the default is supplied by graph cellularization. -/
class Choices where
  cellWord : ∀ (i : Fin (n + 1)) (_j : RelCWComplex.cell (C i : Set X) 2),
    BoundaryWords (skeletonAttachingMap (C i : Set X) 1)
  cellWord_spec : ∀ i j,
    (subcomplexCellBoundary (C i) j).Homotopic (cellWord i j).boundaryMap


abbrev TopCell := RelCWComplex.cell (C (Fin.last n) : Set X) 2

def topCell (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) : TopCell C :=
  subcomplexCellInclusion (hC (Fin.le_last i)) 2 j

def birthSet (j : TopCell C) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => j.val ∈ (C i).I 2)

theorem birthSet_nonempty (j : TopCell C) : (birthSet C j).Nonempty :=
  ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩⟩

def birth (j : TopCell C) : Fin (n + 1) := (birthSet C j).min' (birthSet_nonempty C j)

theorem birth_mem (j : TopCell C) : j.val ∈ (C (birth C j)).I 2 :=
  (Finset.mem_filter.mp (Finset.min'_mem (birthSet C j) (birthSet_nonempty C j))).2

theorem birth_le (j : TopCell C) (i : Fin (n + 1)) (hj : j.val ∈ (C i).I 2) :
    birth C j ≤ i :=
  Finset.min'_le (birthSet C j) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

def birthCell (j : TopCell C) : RelCWComplex.cell (C (birth C j) : Set X) 2 :=
  ⟨j.val, birth_mem C j⟩

variable [Choices C]

def birthWord (j : TopCell C) : BoundaryWords (skeletonAttachingMap (C (birth C j) : Set X) 1) :=
  Choices.cellWord (birth C j) (birthCell C j)

theorem birthWord_spec (j : TopCell C) :
    (subcomplexCellBoundary (C (birth C j)) (birthCell C j)).Homotopic
      (birthWord C j).boundaryMap :=
  Choices.cellWord_spec (birth C j) (birthCell C j)

def word (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) :
    BoundaryWords (skeletonAttachingMap (C i : Set X) 1) :=
  (birthWord C (topCell C hC i j)).map
    (subcomplexGraphInclusion (hC (birth_le C (topCell C hC i j) i j.property)))

theorem word_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) :
    word C hC k (subcomplexCellInclusion (hC hik) 2 j) =
      (word C hC i j).map (subcomplexGraphInclusion (hC hik)) := by
  unfold word
  rw [BoundaryWords.map_comp, subcomplexGraphInclusion_comp]
  rfl




end FiniteChains.ClassicalCW.ChainWords
end

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set X))
  (hC : Monotone C)
  [Choices C]

def birthHomotopy (j : TopCell C) :
    (subcomplexCellBoundary (C (birth C j)) (birthCell C j)).Homotopy
      (birthWord C j).boundaryMap := Classical.choice (birthWord_spec C j)

def wordHomotopy (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) :
    (subcomplexCellBoundary (C i) j).Homotopy (word C hC i j).boundaryMap where
  toContinuousMap := (subcomplexGraphDiskMap
    (hC (birth_le C (topCell C hC i j) i j.property))).comp
      (birthHomotopy C (topCell C hC i j)).toContinuousMap
  map_zero_left a := by
    change subcomplexGraphDiskMap _ (birthHomotopy C _ (0, a)) = _
    rw [(birthHomotopy C _).apply_zero]
    exact congrArg (fun f => f a) (subcomplexCellBoundary_natural
      (hC (birth_le C (topCell C hC i j) i j.property))
      (birthCell C (topCell C hC i j)))
  map_one_left a := by
    change subcomplexGraphDiskMap _ (birthHomotopy C _ (1, a)) = _
    rw [(birthHomotopy C _).apply_one]
    exact congrArg (fun f => f a) (subcomplexBoundaryWord_map
      (hC (birth_le C (topCell C hC i j) i j.property))
      (birthWord C (topCell C hC i j)))


def rawAttaching (i : Fin (n + 1)) :
    C(BoundaryFamily (RelCWComplex.cell (C i : Set X) 2) (Fin 2 → ℝ),
      DiskAttachment (skeletonAttachingMap (C i : Set X) 1)) :=
  ⟨fun a => subcomplexCellBoundary (C i) a.1 a.2,
    continuous_sigma (fun j => (subcomplexCellBoundary (C i) j).continuous)⟩

def wordAttaching (i : Fin (n + 1)) :
    C(BoundaryFamily (RelCWComplex.cell (C i : Set X) 2) (Fin 2 → ℝ),
      DiskAttachment (skeletonAttachingMap (C i : Set X) 1)) :=
  ⟨fun a => (word C hC i a.1).boundaryMap a.2,
    continuous_sigma (fun j => (word C hC i j).boundaryMap.continuous)⟩

def attachingHomotopy (i : Fin (n + 1)) : (rawAttaching C i).Homotopy (wordAttaching C hC i) := by
  let H j := wordHomotopy C hC i j
  let F : C(BoundaryFamily (RelCWComplex.cell (C i : Set X) 2) (Fin 2 → ℝ),
      C(I, DiskAttachment (skeletonAttachingMap (C i : Set X) 1))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }

theorem attachingHomotopy_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) (t : I) (a : UnitBoundary (Fin 2 → ℝ)) :
    attachingHomotopy C hC k (t, ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩) =
      subcomplexGraphDiskMap (hC hik) (attachingHomotopy C hC i (t, ⟨j, a⟩)) :=
  (by
    exact (congrArg (fun f => f (birthHomotopy C (topCell C hC i j) (t, a)))
      (subcomplexGraphDiskMap_comp
        (hC (birth_le C (topCell C hC i j) i j.property)) (hC hik))).symm)

def wordDiskChange (i : Fin (n + 1)) :
    DiskAttachment (rawAttaching C i) ≃ₕ DiskAttachment (wordAttaching C hC i) :=
  naturalDiskAttachingEquiv (rawAttaching C i) (wordAttaching C hC i)
    (attachingHomotopy C hC i)

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical ContinuousMap

variable (K : Whitehead.TwoComplex)


def subcomplexTopSkeletonHomeomorph (C : CWComplex.Subcomplex (Set.univ : Set K)) :
    (C : Set K) ≃ₜ SkeletonCarrier (C : Set K) 3 where
  toFun x := ⟨x.val, (show x.val ∈ CWComplex.skeletonLT (C : Set K) (3 : ℕ∞) by
    have hx := x.property
    have hx' := (CWComplex.iUnion_openCell_eq_complex (C := (C : Set K))).symm
    have hmem := congrArg (fun S : Set K => x.val ∈ S) hx'
    have hx := Eq.mp hmem hx
    obtain ⟨n, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    have hn : n < 3 := by
      by_contra h
      have hn2 : 2 < n := by omega
      letI := K.dimension n hn2
      exact isEmptyElim j.val
    change x.val ∈ (CWComplex.skeletonLT (C : Set K) (3 : ℕ∞) : Set K)
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT]
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨by exact_mod_cast hn,
      Set.mem_iUnion.mpr ⟨j, hj⟩⟩⟩)⟩
  invFun x := ⟨x.val, (CWComplex.skeletonLT (C : Set K) (3 : ℕ∞)).subset_complex x.property⟩
  left_inv _x := Subtype.ext rfl
  right_inv _x := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def subcomplexAsDiskAttachment (C : CWComplex.Subcomplex (Set.univ : Set K)) :
    (C : Set K) ≃ₜ DiskAttachment (skeletonAttachingMap (C : Set K) 2) :=
  (subcomplexTopSkeletonHomeomorph K C).trans (skeletonAsDiskAttachment (C : Set K) 2)

namespace ChainWords
variable {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)
  [Choices C]

def rawDiskEquiv (i : Fin (n + 1)) : (C i : Set K) ≃ₕ DiskAttachment (rawAttaching C i) :=
  (subcomplexAsDiskAttachment K (C i)).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
      (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv)

def wordDiskEquiv (i : Fin (n + 1)) :
    (C i : Set K) ≃ₕ DiskAttachment (wordAttaching C hC i) :=
  (rawDiskEquiv K C i).trans (wordDiskChange C hC i)

end ChainWords
end FiniteChains.ClassicalCW

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex)

theorem subcomplexAsDiskAttachment_natural
    {C D : CWComplex.Subcomplex (Set.univ : Set K)} (h : (C : Set K) ⊆ D)
    (x : (C : Set K)) :
    subcomplexAsDiskAttachment K D (Set.inclusion h x) =
      subcomplexDiskMap h 2 (subcomplexAsDiskAttachment K C x) := by
  apply (skeletonAttachmentHomeomorph (D : Set K) 2).injective
  rw [subcomplexDiskMap_skeleton]
  change (skeletonAttachmentHomeomorph (D : Set K) 2)
      ((skeletonAttachmentHomeomorph (D : Set K) 2).symm _) =
    subcomplexSkeletonInclusion h 3
      ((skeletonAttachmentHomeomorph (C : Set K) 2)
        ((skeletonAttachmentHomeomorph (C : Set K) 2).symm _))
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  rfl

namespace ChainWords
variable {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)
  [Choices C]

omit [Choices C] in
theorem rawAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    subcomplexGraphDiskMap (hC hik) (rawAttaching C i ⟨j, a⟩) =
      rawAttaching C k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ :=
  congrArg (fun f => f a) (subcomplexCellBoundary_natural (hC hik) j)

theorem wordAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩) =
      wordAttaching C hC k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  change subcomplexGraphDiskMap _ ((word C hC i j).boundaryMap a) =
    (word C hC k _).boundaryMap a
  rw [word_natural C hC hik]
  exact congrArg (fun f => f a) (subcomplexBoundaryWord_map (hC hik) (word C hC i j))

def rawDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    C(DiskAttachment (rawAttaching C i), DiskAttachment (rawAttaching C k)) :=
  diskFamilyMap (rawAttaching C i) (rawAttaching C k) (subcomplexGraphDiskMap (hC hik))
    (subcomplexCellInclusion (hC hik) 2) (rawAttaching_natural K C hC hik)

def wordDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    C(DiskAttachment (wordAttaching C hC i), DiskAttachment (wordAttaching C hC k)) :=
  diskFamilyMap (wordAttaching C hC i) (wordAttaching C hC k)
    (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
    (wordAttaching_natural K C hC hik)


def rawBaseChange (i : Fin (n + 1)) :=
  diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
    (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv




theorem wordDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (wordDiskInclusion K C hC hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (wordDiskEquiv K C hC i) (wordDiskEquiv K C hC k)
  rw [(show (wordDiskInclusion K C hC hik).comp (wordDiskEquiv K C hC i).toFun =
      (wordDiskEquiv K C hC k).toFun.comp
        ⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ by
    ext x
    change wordDiskInclusion K C hC hik (wordDiskChange C hC i (rawDiskEquiv K C i x)) = _
    have h := congrArg (fun f => f (rawDiskEquiv K C i x)) (naturalDiskAttachingEquiv_natural _ _ (attachingHomotopy C hC i)
    _ _ (attachingHomotopy C hC k) (subcomplexGraphDiskMap (hC hik))
    (subcomplexCellInclusion (hC hik) 2) (rawAttaching_natural K C hC hik)
    (wordAttaching_natural K C hC hik)
    (fun t j a => (attachingHomotopy_natural C hC hik j t a).symm))
    change wordDiskInclusion K C hC hik (wordDiskChange C hC i (rawDiskEquiv K C i x)) =
      wordDiskChange C hC k (rawDiskInclusion K C hC hik (rawDiskEquiv K C i x)) at h
    rw [h, (show rawDiskInclusion K C hC hik (rawDiskEquiv K C i x) =
      rawDiskEquiv K C k (Set.inclusion (hC hik) x) by
      change rawDiskInclusion K C hC hik
          (rawBaseChange K C i (subcomplexAsDiskAttachment K (C i) x)) =
        rawBaseChange K C k (subcomplexAsDiskAttachment K (C k) (Set.inclusion (hC hik) x))
      rw [subcomplexAsDiskAttachment_natural K (hC hik) x]
      exact congrArg (fun f => f (subcomplexAsDiskAttachment K (C i) x))
        (show (rawDiskInclusion K C hC hik).comp (rawBaseChange K C i).toFun =
      (rawBaseChange K C k).toFun.comp (subcomplexDiskMap (hC hik) 2) by
          apply hom_ext (skeletonAttachingMap (C i : Set K) 2)
            (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
          · intro x
            change rawDiskInclusion K C hC hik
              (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
                (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv
                (old (skeletonAttachingMap (C i : Set K) 2)
                  (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ)) x)) = _
            rw [diskAttachmentBaseChangeHomotopyEquiv_old]
            change diskFamilyMap _ _ _ _ _ (old _ _ _) =
              diskAttachmentBaseChangeHomotopyEquiv _ _ (subcomplexDiskMap _ 2 (old _ _ x))
            rw [diskFamilyMap_old, subcomplexDiskMap_old, diskAttachmentBaseChangeHomotopyEquiv_old]
            congr 1
            change (skeletonAttachmentHomeomorph (C k : Set K) 1).symm
              (subcomplexSkeletonInclusion (hC hik) 2
                ((skeletonAttachmentHomeomorph (C i : Set K) 1)
                  ((skeletonAttachmentHomeomorph (C i : Set K) 1).symm x))) = _
            rw [Homeomorph.apply_symm_apply]
            rfl
          · rintro ⟨j, x⟩
            change rawDiskInclusion K C hC hik (diskAttachmentBaseChangeHomotopyEquiv _ _ (cell _ _ ⟨j, x⟩)) = _
            rw [diskAttachmentBaseChangeHomotopyEquiv_cell]
            change diskFamilyMap _ _ _ _ _ (cell _ _ _) =
              diskAttachmentBaseChangeHomotopyEquiv _ _ (subcomplexDiskMap _ 2 (cell _ _ ⟨j, x⟩))
            rw [diskFamilyMap_cell, subcomplexDiskMap_cell, diskAttachmentBaseChangeHomotopyEquiv_cell]
            rfl))]
    rfl)]

end ChainWords
end FiniteChains.ClassicalCW
end

namespace FiniteChains.RelativeAttachment
open scoped Topology

universe u
variable {J K X E : Type u} [TopologicalSpace X]
  [NormedAddCommGroup E]

def sigmaLabelHomeomorph {Y : Type u} [TopologicalSpace Y] (e : J ≃ K) :
    (Σ _ : J, Y) ≃ₜ (Σ _ : K, Y) where
  toFun z := ⟨e z.1, z.2⟩
  invFun z := ⟨e.symm z.1, z.2⟩
  left_inv := by rintro ⟨j, x⟩; simp only [Equiv.symm_apply_apply]
  right_inv := by rintro ⟨j, x⟩; simp only [Equiv.apply_symm_apply]
  continuous_toFun := continuous_sigma (fun j =>
    continuous_sigmaMk (σ := fun _ : K => Y) (i := e j))
  continuous_invFun := continuous_sigma (fun k =>
    continuous_sigmaMk (σ := fun _ : J => Y) (i := e.symm k))

def reindexedDiskAttaching (r : C(BoundaryFamily J E, X)) (e : J ≃ K) :
    C(BoundaryFamily K E, X) := r.comp (sigmaLabelHomeomorph e).symm.toContinuousMap

def diskAttachmentReindexHomeomorph (r : C(BoundaryFamily J E, X)) (e : J ≃ K) :
    DiskAttachment r ≃ₜ DiskAttachment (reindexedDiskAttaching r e) :=
  attachmentDiagramHomeomorph r (boundaryFamilyInclusion J E)
    (reindexedDiskAttaching r e) (boundaryFamilyInclusion K E)
    (sigmaLabelHomeomorph (Y := UnitBoundary E) e).toEquiv
    (Homeomorph.refl X) (sigmaLabelHomeomorph (Y := ClosedUnitBall E) e)
    (fun a => by
      change r a = r ((sigmaLabelHomeomorph e).symm (sigmaLabelHomeomorph e a))
      rw [Homeomorph.symm_apply_apply])
    (fun _ => rfl)
    (boundaryFamilyInclusion_isClosedEmbedding K E).injective
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective

@[simp] theorem diskAttachmentReindexHomeomorph_old
    (r : C(BoundaryFamily J E, X)) (e : J ≃ K) (x : X) :
    diskAttachmentReindexHomeomorph r e (old r (boundaryFamilyInclusion J E) x) =
      old (reindexedDiskAttaching r e) (boundaryFamilyInclusion K E) x := rfl

@[simp] theorem diskAttachmentReindexHomeomorph_cell
    (r : C(BoundaryFamily J E, X)) (e : J ≃ K) (d : DiskFamily J E) :
    diskAttachmentReindexHomeomorph r e (cell r (boundaryFamilyInclusion J E) d) =
      cell (reindexedDiskAttaching r e) (boundaryFamilyInclusion K E) ⟨e d.1, d.2⟩ :=
  attachmentDiagramHomeomorph_cell ..

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment.StabilizedDiskPresentation
open ClassicalGraphModel DiskPresentationExtension
open scoped Classical Topology

variable {A J : Type}

def oldGenerator : A ↪ A ⊕ PUnit := ⟨Sum.inl, Sum.inl_injective⟩
def oldRelator : J ↪ J ⊕ PUnit := ⟨Sum.inl, Sum.inl_injective⟩

def freshLabelEquiv (A : Type) : {a : A ⊕ PUnit // a ∉ Set.range (Sum.inl : A → A ⊕ PUnit)} ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨Sum.inr PUnit.unit, by rintro ⟨a, ha⟩; exact Sum.inl_ne_inr ha⟩
  left_inv a := by grind
  right_inv _ := Subsingleton.elim _ _

variable (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))

def attaching : C(BoundaryFamily (J ⊕ PUnit) (Fin 2 → ℝ), Rose (A ⊕ PUnit)) where
  toFun z := match z.1 with
    | Sum.inl j => diskRoseMap Sum.inl (r ⟨j, z.2⟩)
    | Sum.inr _ => diskRoseMap Sum.inr (dummyCircleBoundaryHomeomorph z.2)
  continuous_toFun := by
    apply continuous_sigma
    intro j
    cases j with
    | inl j => exact (diskRoseMap Sum.inl).continuous.comp (r.continuous.comp
        (continuous_sigmaMk (σ := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)))
    | inr u => exact (diskRoseMap Sum.inr).continuous.comp dummyCircleBoundaryHomeomorph.continuous

abbrev Model := DiskAttachment (attaching r)

theorem attaching_old (z : BoundaryFamily J (Fin 2 → ℝ)) :
    diskRoseMap (oldGenerator (A := A)) (r z) = attaching r ⟨oldRelator z.1, z.2⟩ := rfl

def extension := DiskPresentationExtension.extensionModel oldGenerator oldRelator r (attaching r)
  (attaching_old r)

def basepoint : DiskAttachment r := old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) (roseVertex A)

def oneHomeomorph :
    DiskAttachment (extension r).oneAttaching ≃ₜ DiskAttachment (dummyOneAttaching (basepoint r)) :=
  diskAttachmentReindexHomeomorph
    (DiskPresentationExtension.oneAttaching oldGenerator r) (freshLabelEquiv A)


@[simp] theorem oneHomeomorph_cell (d : DiskFamily (extension r).oneCells (Fin 1 → ℝ)) :
    oneHomeomorph r
      (cell (extension r).oneAttaching (boundaryFamilyInclusion (extension r).oneCells (Fin 1 → ℝ)) d) =
        cell (dummyOneAttaching (basepoint r)) (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
          ⟨PUnit.unit, d.2⟩ := diskAttachmentReindexHomeomorph_cell ..

theorem oneHomeomorph_dummyCircle (y : Rose PUnit) :
    oneHomeomorph r
      (DiskPresentationExtension.roseIntoOne oldGenerator r (diskRoseMap Sum.inr y)) =
        dummyLoopMap (basepoint r) y := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (roseAttaching PUnit)
    (boundaryFamilyInclusion PUnit (Fin 1 → ℝ)) y
  cases z with
  | inl u => rfl
  | inr d =>
      rcases d with ⟨u, d⟩
      cases u
      change oneHomeomorph r (DiskPresentationExtension.roseIntoOne oldGenerator r
        (diskRoseMap Sum.inr (cell (roseAttaching PUnit) (boundaryFamilyInclusion PUnit _) ⟨PUnit.unit, d⟩))) = _
      rw [diskRoseMap_cell]
      let a : NewGenerators (oldGenerator (A := A)) :=
        ⟨Sum.inr PUnit.unit, by rintro ⟨a, ha⟩; exact Sum.inl_ne_inr ha⟩
      rw [DiskPresentationExtension.roseIntoOne_cell_new oldGenerator r a d]
      exact (oneHomeomorph_cell r ⟨a, d⟩).trans (singletonAttachmentInto_cell (basepoint r)
        (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
        (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective
        ⟨PUnit.unit, d⟩).symm

theorem twoAttaching_reindexed (z : BoundaryFamily (extension r).twoCells (Fin 2 → ℝ)) :
    oneHomeomorph r ((extension r).twoAttaching z) =
      dummyTwoAttaching (basepoint r) ⟨PUnit.unit, z.2⟩ := by
  rcases z with ⟨⟨j | u, hj⟩, z⟩
  · exact (hj ⟨j, rfl⟩).elim
  · cases u
    exact oneHomeomorph_dummyCircle r (dummyCircleBoundaryHomeomorph z)



def homotopyEquiv : ContinuousMap.HomotopyEquiv (DiskAttachment r) (Model r) :=
  ((dummyLoopFillingHomotopyEquiv (basepoint r)).trans (attachmentDiagramHomeomorph (extension r).twoAttaching
    (boundaryFamilyInclusion (extension r).twoCells (Fin 2 → ℝ))
    (dummyTwoAttaching (basepoint r)) (boundaryFamilyInclusion PUnit (Fin 2 → ℝ))
    (sigmaLabelHomeomorph (Y := UnitBoundary (Fin 2 → ℝ)) (freshLabelEquiv J)).toEquiv
    (oneHomeomorph r)
    (sigmaLabelHomeomorph (Y := ClosedUnitBall (Fin 2 → ℝ)) (freshLabelEquiv J))
    (twoAttaching_reindexed r) (fun _ => rfl)
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 2 → ℝ)).injective
    (boundaryFamilyInclusion_isClosedEmbedding (extension r).twoCells (Fin 2 → ℝ)).injective).symm.toHomotopyEquiv).trans
    (DiskPresentationExtension.extensionHomeomorph oldGenerator oldRelator r (attaching r)
      (attaching_old r)).toHomotopyEquiv

theorem homotopyEquiv_toFun :
    (homotopyEquiv r).toFun =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator r (attaching r) (attaching_old r) := rfl

end FiniteChains.RelativeAttachment.StabilizedDiskPresentation

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
variable {A B D : Type}

theorem diskRoseMap_comp (f : A → B) (g : B → D) :
    (diskRoseMap g).comp (diskRoseMap f) = diskRoseMap (g ∘ f) := by
  apply hom_ext (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ))
  · intro u
    cases u
    rfl
  · simp

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.RelativeAttachment.StabilizedDiskPresentation
open ClassicalGraphModel
variable {A B J K : Type}

def withDummy (f : A ↪ B) : A ⊕ PUnit ↪ B ⊕ PUnit where
  toFun := Sum.map f id
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f.injective.eq_iff]

variable (f : A ↪ B) (c : J ↪ K)
  (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
  (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
  (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

include h in
theorem attaching_natural (z : BoundaryFamily (J ⊕ PUnit) (Fin 2 → ℝ)) :
    diskRoseMap (withDummy f) (attaching r z) =
      attaching s ⟨withDummy c z.1, z.2⟩ := by
  rcases z with ⟨j | u, a⟩
  · change diskRoseMap (withDummy f) (diskRoseMap Sum.inl (r ⟨j, a⟩)) =
      diskRoseMap Sum.inl (s ⟨c j, a⟩)
    rw [← h ⟨j, a⟩]
    exact congrArg (fun m => m (r ⟨j, a⟩))
      ((diskRoseMap_comp Sum.inl (withDummy f)).trans
        (diskRoseMap_comp f Sum.inl).symm)
  · change diskRoseMap (withDummy f) (diskRoseMap Sum.inr (dummyCircleBoundaryHomeomorph a)) =
      diskRoseMap Sum.inr (dummyCircleBoundaryHomeomorph a)
    exact congrArg (fun m => m (dummyCircleBoundaryHomeomorph a))
      (diskRoseMap_comp Sum.inr (withDummy f))

def map : C(Model r, Model s) :=
  diskFamilyMap (attaching r) (attaching s) (diskRoseMap (withDummy f))
    (withDummy c) (fun j a => attaching_natural f c r s h ⟨j, a⟩)

theorem homotopyEquiv_natural :
    (map f c r s h).comp (homotopyEquiv r).toFun =
      (homotopyEquiv s).toFun.comp
        (DiskPresentationExtension.sourceMap f c r s h) := by
  rw [homotopyEquiv_toFun, homotopyEquiv_toFun]
  apply hom_ext r (boundaryFamilyInclusion J (Fin 2 → ℝ))
  · intro x
    change map f c r s h (DiskPresentationExtension.sourceMap oldGenerator oldRelator
      r (attaching r) (attaching_old r) (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x)) =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator s (attaching s) (attaching_old s)
        (DiskPresentationExtension.sourceMap f c r s h (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x))
    rw [DiskPresentationExtension.sourceMap_old]
    change diskFamilyMap (attaching r) (attaching s) (diskRoseMap (withDummy f))
      (withDummy c) (fun j a => attaching_natural f c r s h ⟨j, a⟩)
        (old (attaching r) (boundaryFamilyInclusion (J ⊕ PUnit) (Fin 2 → ℝ))
          (diskRoseMap oldGenerator x)) = _
    rw [diskFamilyMap_old, DiskPresentationExtension.sourceMap_old,
      DiskPresentationExtension.sourceMap_old]
    exact congrArg (old (attaching s) (boundaryFamilyInclusion (K ⊕ PUnit) (Fin 2 → ℝ)))
      (congrArg (fun m => m x)
      ((diskRoseMap_comp Sum.inl (withDummy f)).trans
        (diskRoseMap_comp f Sum.inl).symm))
  · rintro ⟨j, x⟩
    change map f c r s h (DiskPresentationExtension.sourceMap oldGenerator oldRelator
      r (attaching r) (attaching_old r) (cell r (boundaryFamilyInclusion J (Fin 2 → ℝ)) ⟨j, x⟩)) =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator s (attaching s) (attaching_old s)
        (DiskPresentationExtension.sourceMap f c r s h
          (cell r (boundaryFamilyInclusion J (Fin 2 → ℝ)) ⟨j, x⟩))
    rw [DiskPresentationExtension.sourceMap_cell]
    change diskFamilyMap (attaching r) (attaching s) (diskRoseMap (withDummy f))
      (withDummy c) (fun j a => attaching_natural f c r s h ⟨j, a⟩)
        (cell (attaching r) (boundaryFamilyInclusion (J ⊕ PUnit) (Fin 2 → ℝ))
          ⟨oldRelator j, x⟩) = _
    rw [diskFamilyMap_cell, DiskPresentationExtension.sourceMap_cell,
      DiskPresentationExtension.sourceMap_cell]
    rfl

theorem map_killsPi2_iff : Whitehead.KillsPi2 (map f c r s h) ↔
    Whitehead.KillsPi2 (DiskPresentationExtension.sourceMap f c r s h) := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff (homotopyEquiv r) (homotopyEquiv s)
  rw [homotopyEquiv_natural]

end FiniteChains.RelativeAttachment.StabilizedDiskPresentation

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval Topology
variable {V J M : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphComponentSetoid : Setoid V where
  r := Comb.Reach (graphCx r)
  iseqv := {
    refl := Comb.reach_self (graphCx r)
    symm := by
      rintro a b ⟨l, hl⟩
      exact ⟨Comb.revPath l, Comb.isPath_revPath hl⟩
    trans := by
      rintro a b c ⟨l, hl⟩ ⟨m, hm⟩
      exact ⟨l ++ m, hl.append hm⟩ }

abbrev GraphComponents := Quotient (graphComponentSetoid r)
local instance : TopologicalSpace (GraphComponents r) := ⊥
local instance : DiscreteTopology (GraphComponents r) := ⟨rfl⟩

def graphComponentMap : C(DiskAttachment r, GraphComponents r) :=
  desc r (boundaryFamilyInclusion J (Fin 1 → ℝ))
    ⟨Quotient.mk _, continuous_of_discreteTopology⟩
    ⟨fun d => Quotient.mk _ (graphSrc r d.1),
      continuous_sigma (fun j =>
        (continuous_const : Continuous (fun _ : ClosedUnitBall (Fin 1 → ℝ) =>
          Quotient.mk (graphComponentSetoid r) (graphSrc r j))))⟩
    (fun a => by
      rcases a with ⟨j, a⟩
      rcases graphBoundary_cases a with rfl | rfl
      · rfl
      · apply Eq.symm
        exact Quotient.sound (show Comb.Reach (graphCx r) (graphSrc r j) (graphTgt r j)
          from ⟨[(j, true)], rfl, rfl⟩))

theorem graphComponentMap_path {x y : V}
    (p : Path (old r (boundaryFamilyInclusion J _) x)
      (old r (boundaryFamilyInclusion J _) y)) (t : I) :
    graphComponentMap r (p t) = Quotient.mk (graphComponentSetoid r) x := by
  have h := TotallyDisconnectedSpace.eq_of_continuous
    (fun t => graphComponentMap r (p t)) ((graphComponentMap r).continuous.comp p.continuous) t 0
  simpa [p.source, graphComponentMap] using h

theorem graphComponentMap_boundaryWord (W : BoundaryWords r)
    (a : UnitBoundary (Fin 2 → ℝ)) :
    graphComponentMap r (W.boundaryMap a) =
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap (0, false) 0)) := by
  have hedge s :
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 0)) =
        Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 1)) := by
    exact Quotient.sound ⟨W.word s, W.isPath s⟩
  have hcorner s :
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 0)) =
        Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap (0, false) 0)) := by
    rcases s with ⟨i, b⟩
    fin_cases i <;> cases b
    · rfl
    · have h₁ : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      have h₀ : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      exact (congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₁).trans
        ((hedge (1, false)).symm.trans
          (congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₀))
    · have h₀ : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      exact congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₀
    · have h₀ : squareSideMap (1, true) 0 = squareSideMap (0, false) 1 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      exact (congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₀).trans
        (hedge (0, false)).symm
  obtain ⟨⟨s, t⟩, hs⟩ := squareSideQuotient_surjective (unitBoundarySquareHomeomorph a)
  change squareSideMap s t = unitBoundarySquareHomeomorph a at hs
  change graphComponentMap r (W.squareMap (unitBoundarySquareHomeomorph a)) = _
  rw [← hs, W.squareMap_side, graphComponentMap_path]
  exact hcorner s

variable (W : M → BoundaryWords r)

def boundaryWordsAttaching : C(BoundaryFamily M (Fin 2 → ℝ), DiskAttachment r) :=
  ⟨fun a => (W a.1).boundaryMap a.2, continuous_sigma (fun m => (W m).boundaryMap.continuous)⟩

def wordDiskComponentMap : C(DiskAttachment (boundaryWordsAttaching r W), GraphComponents r) :=
  desc (boundaryWordsAttaching r W) (boundaryFamilyInclusion M (Fin 2 → ℝ))
    (graphComponentMap r)
    ⟨fun d => Quotient.mk _ ((W d.1).vertex (squareSideMap (0, false) 0)),
      continuous_sigma (fun j =>
        (continuous_const : Continuous (fun _ : ClosedUnitBall (Fin 2 → ℝ) =>
          Quotient.mk (graphComponentSetoid r) ((W j).vertex (squareSideMap (0, false) 0)))))⟩
    (fun a => graphComponentMap_boundaryWord r (W a.1) a.2)

theorem graphCx_isConnected_of_wordDisks
    [PreconnectedSpace (DiskAttachment (boundaryWordsAttaching r W))] :
    Comb.IsConnected (graphCx r) := by
  intro a b
  apply Quotient.exact (s := graphComponentSetoid r)
  exact TotallyDisconnectedSpace.eq_of_continuous (wordDiskComponentMap r W)
    (wordDiskComponentMap r W).continuous
    (old _ _ (old r _ a)) (old _ _ (old r _ b))

omit [DiscreteTopology V] in
theorem graph_vertices_nonempty_of_wordDisks
    [Nonempty (DiskAttachment (boundaryWordsAttaching r W))] : Nonempty V := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (DiskAttachment (boundaryWordsAttaching r W)))
  obtain ⟨z, rfl⟩ := quotientMap_surjective (boundaryWordsAttaching r W)
    (boundaryFamilyInclusion M (Fin 2 → ℝ)) x
  cases z with
  | inr d => exact ⟨(W d.1).vertex (squareSideMap (0, false) 0)⟩
  | inl x =>
    obtain ⟨z, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J (Fin 1 → ℝ)) x
    cases z with
    | inl v => exact ⟨v⟩
    | inr d => exact ⟨graphSrc r d.1⟩

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]

/-- A relative construction can fix the tree on its original graph.
The unseeded construction obtains one from connectedness. -/
class TreeChoice where
  initial : Option (Comb.SpanningTree (subcomplexGraph (C 0)))


variable [TreeChoice K C]

omit [TreeChoice K C] in
include hconn in
theorem wordDisk_connected (i : Fin (n + 1)) :
    ConnectedSpace (DiskAttachment (wordAttaching C hC i)) := by
  letI := hconn i
  exact Whitehead.connectedSpace_of_homotopyEquiv (wordDiskEquiv K C hC i).symm

omit [TreeChoice K C] in
include hC hconn in
theorem graph_connected (i : Fin (n + 1)) : Comb.IsConnected (subcomplexGraph (C i)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI : ConnectedSpace (DiskAttachment
      (boundaryWordsAttaching (skeletonAttachingMap (C i : Set K) 1) (word C hC i))) :=
    wordDisk_connected K C hC hconn i
  exact graphCx_isConnected_of_wordDisks (skeletonAttachingMap (C i : Set K) 1) (word C hC i)


def boundedStage (n r : ℕ) : Fin (n + 1) :=
  ⟨min r n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem boundedStage_monotone (n : ℕ) : Monotone (boundedStage n) :=
  fun _ _ h => min_le_min h le_rfl

def boundedGraph (r : ℕ) := subcomplexGraph (C (boundedStage n r))

def boundedGraphInclusion (r : ℕ) :
    Comb.Hom (boundedGraph K C r) (boundedGraph K C (r + 1)) :=
  subcomplexGraphInclusion (hC (boundedStage_monotone n (Nat.le_succ r)))

include hconn in
theorem boundedGraphs_have_compatible_trees :
    ∃ T : ∀ r, Comb.SpanningTree (boundedGraph K C r),
      (∀ S, TreeChoice.initial (K := K) (C := C) = some S → T 0 = S) ∧
      ∀ r e, (T (r + 1)).isTree ((boundedGraphInclusion K C hC r).onE e) ↔ (T r).isTree e := by
  letI : Nonempty (boundedGraph K C 0).V := (by
    letI := subcomplexZeroSkeleton_discrete (C (boundedStage n 0))
    letI : ConnectedSpace (DiskAttachment
        (boundaryWordsAttaching (skeletonAttachingMap (C (boundedStage n 0) : Set K) 1) (word C hC (boundedStage n 0)))) :=
      wordDisk_connected K C hC hconn (boundedStage n 0)
    exact graph_vertices_nonempty_of_wordDisks (V := SkeletonCarrier (C (boundedStage n 0) : Set K) 1)
      (skeletonAttachingMap (C (boundedStage n 0) : Set K) 1) (word C hC (boundedStage n 0)))
  let v : (boundedGraph K C 0).V := Classical.choice inferInstance
  obtain ⟨R₀, hroot⟩ := Comb.SpanningTree.exists_of_isConnected
    (graph_connected K C hC hconn (boundedStage n 0)) v
  let T₀ : Comb.SpanningTree (boundedGraph K C 0) :=
    (TreeChoice.initial (K := K) (C := C)).getD R₀
  have hseed : ∀ S, TreeChoice.initial (K := K) (C := C) = some S → T₀ = S := by
    intro S hS
    dsimp only [T₀]
    rw [hS]
    rfl
  obtain ⟨T, hT₀, hT⟩ := Comb.SpanningTree.exists_compatible_trees
    (boundedGraph K C) (boundedGraphInclusion K C hC)
    (fun r => graph_connected K C hC hconn (boundedStage n r))
    (fun r => subcomplexGraphInclusion_injective_V _)
    (fun r => subcomplexGraphInclusion_injective_E _) T₀
  exact ⟨T, fun S hS => hT₀.trans (hseed S hS), hT⟩

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical ContinuousMap
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

omit [Choices C] [TreeChoice K C] in
theorem boundedTrees_compatible
    (T : ∀ r, Comb.SpanningTree (boundedGraph K C r))
    (hT : ∀ r e, (T (r + 1)).isTree ((boundedGraphInclusion K C hC r).onE e) ↔
      (T r).isTree e) {r s : ℕ} (hrs : r ≤ s)
    (e : (boundedGraph K C r).E) :
    (T s).isTree ((subcomplexGraphInclusion (hC (boundedStage_monotone n hrs))).onE e) ↔
      (T r).isTree e := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
      exact (hT s ((subcomplexGraphInclusion
        (hC (boundedStage_monotone n hrs))).onE e)).trans ih

include hconn in
theorem finiteGraphs_have_compatible_trees :
    ∃ T : ∀ i, Comb.SpanningTree (subcomplexGraph (C i)),
      (∀ S, TreeChoice.initial (K := K) (C := C) = some S → T 0 = S) ∧
      ∀ {i k : Fin (n + 1)} (hik : i ≤ k) e,
        (T k).isTree ((subcomplexGraphInclusion (hC hik)).onE e) ↔ (T i).isTree e := by
  obtain ⟨T, hT₀, hT⟩ := boundedGraphs_have_compatible_trees K C hC hconn
  have hs i : boundedStage n i.val = i := by
    ext
    exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)
  let U i : Comb.SpanningTree (subcomplexGraph (C i)) := (hs i) ▸ T i.val
  have transport (a b) (hab : a ≤ b) (i k)
      (ha : boundedStage n a = i) (hb : boundedStage n b = k) hik :
      ∀ e : (subcomplexGraph (C i)).E,
        (show Comb.SpanningTree (subcomplexGraph (C k)) from hb ▸ T b).isTree
            ((subcomplexGraphInclusion (hC hik)).onE e) ↔
          (show Comb.SpanningTree (subcomplexGraph (C i)) from ha ▸ T a).isTree e := by
    subst i
    subst k
    exact boundedTrees_compatible K C hC T hT hab
  refine ⟨U, ?_, ?_⟩
  · grind
  · grind

def chainTree (i : Fin (n + 1)) : Comb.SpanningTree (subcomplexGraph (C i)) :=
  Classical.choose (finiteGraphs_have_compatible_trees K C hC hconn) i

theorem chainTree_zero (S : Comb.SpanningTree (subcomplexGraph (C 0)))
    (hS : TreeChoice.initial (K := K) (C := C) = some S) :
    chainTree K C hC hconn 0 = S :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).1 S hS

theorem chainTree_compatible {i k : Fin (n + 1)} (hik : i ≤ k)
    (e : (subcomplexGraph (C i)).E) :
    (chainTree K C hC hconn k).isTree ((subcomplexGraphInclusion (hC hik)).onE e) ↔
      (chainTree K C hC hconn i).isTree e :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).2 hik e

abbrev RoseGen (i : Fin (n + 1)) :=
  {e : (subcomplexGraph (C i)).E // ¬(chainTree K C hC hconn i).isTree e}

def roseGenInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    RoseGen K C hC hconn i ↪ RoseGen K C hC hconn k where
  toFun e := ⟨(subcomplexGraphInclusion (hC hik)).onE e.val,
    fun ht => e.property ((chainTree_compatible K C hC hconn hik e.val).mp ht)⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact subcomplexGraphInclusion_injective_E (hC hik) (congrArg Subtype.val hef)

def graphCollapse (i : Fin (n + 1)) :
    DiskAttachment (skeletonAttachingMap (C i : Set K) 1) ≃ₕ
      ClassicalGraphModel.Rose (RoseGen K C hC hconn i) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  exact graphRoseHomotopyEquiv (skeletonAttachingMap (C i : Set K) 1)
    (skeletonAttachingMap (C i : Set K) 1).continuous (chainTree K C hC hconn i)

theorem graphCollapse_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (diskRoseMap (roseGenInclusion K C hC hconn hik)).comp
        (graphCollapse K C hC hconn i).toFun =
      (graphCollapse K C hC hconn k).toFun.comp (subcomplexGraphDiskMap (hC hik)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI := subcomplexZeroSkeleton_discrete (C k)
  have H := graphRoseHomotopyEquiv_natural
    (skeletonAttachingMap (C i : Set K) 1) (skeletonAttachingMap (C i : Set K) 1).continuous
    (skeletonAttachingMap (C k : Set K) 1) (skeletonAttachingMap (C k : Set K) 1).continuous
    (chainTree K C hC hconn i) (chainTree K C hC hconn k)
    (subcomplexGraphInclusion (hC hik)) (chainTree_compatible K C hC hconn hik)
    (subcomplexGraphDiskMap (hC hik)) (subcomplexGraphDiskMap_old (hC hik))
    (fun j x => subcomplexDiskMap_cell (hC hik) 1 j x)
  have he : graphRoseMap _ _ (chainTree K C hC hconn i) (chainTree K C hC hconn k)
      (subcomplexGraphInclusion (hC hik)) (chainTree_compatible K C hC hconn hik) =
      diskRoseMap (roseGenInclusion K C hC hconn hik) := by
    apply hom_ext (roseAttaching _) (boundaryFamilyInclusion _ (Fin 1 → ℝ))
    · intro u
      cases u
      rfl
    · rintro ⟨e, x⟩
      erw [graphRoseMap, diskFamilyMap_cell]
  rwa [he] at H

def collapsedAttaching (i : Fin (n + 1)) :
    C(BoundaryFamily (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ),
      ClassicalGraphModel.Rose (RoseGen K C hC hconn i)) :=
  (graphCollapse K C hC hconn i).toFun.comp (wordAttaching C hC i)

theorem collapsedAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    diskRoseMap (roseGenInclusion K C hC hconn hik) (collapsedAttaching K C hC hconn i ⟨j, a⟩) =
      collapsedAttaching K C hC hconn k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  have H := congrArg (fun f => f (wordAttaching C hC i ⟨j, a⟩))
    (graphCollapse_natural K C hC hconn hik)
  change _ = graphCollapse K C hC hconn k
    (subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩)) at H
  erw [wordAttaching_natural] at H
  exact H

def collapsedDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  diskFamilyMap (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
    (diskRoseMap (roseGenInclusion K C hC hconn hik))
    (subcomplexCellInclusion (hC hik) 2) (collapsedAttaching_natural K C hC hconn hik)

def collapsedDiskChange (i : Fin (n + 1)) :=
  diskAttachmentBaseChangeHomotopyEquiv (wordAttaching C hC i) (graphCollapse K C hC hconn i)


theorem collapsedDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (collapsedDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  erw [← wordDiskInclusion_killsPi2_iff K C hC hik]
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (collapsedDiskChange K C hC hconn i) (collapsedDiskChange K C hC hconn k)
  erw [(show (collapsedDiskInclusion K C hC hconn hik).comp (collapsedDiskChange K C hC hconn i).toFun =
      (collapsedDiskChange K C hC hconn k).toFun.comp (wordDiskInclusion K C hC hik) by
    apply hom_ext (wordAttaching C hC i)
      (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
    · intro x
      have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
        (diskAttachmentBaseChangeHomotopyEquiv_old (wordAttaching C hC i)
          (graphCollapse K C hC hconn i) x)).trans
        (diskFamilyMap_old (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
          (diskRoseMap (roseGenInclusion K C hC hconn hik)) (subcomplexCellInclusion (hC hik) 2)
          (collapsedAttaching_natural K C hC hconn hik) (graphCollapse K C hC hconn i x))
      have hright := (congrArg (collapsedDiskChange K C hC hconn k)
        (diskFamilyMap_old (wordAttaching C hC i) (wordAttaching C hC k)
          (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
          (wordAttaching_natural K C hC hik) x)).trans
        (diskAttachmentBaseChangeHomotopyEquiv_old (wordAttaching C hC k)
          (graphCollapse K C hC hconn k) (subcomplexGraphDiskMap (hC hik) x))
      have hmid := congrArg (old (collapsedAttaching K C hC hconn k)
        (boundaryFamilyInclusion (RelCWComplex.cell (C k : Set K) 2) (Fin 2 → ℝ)))
        (congrArg (fun f => f x) (graphCollapse_natural K C hC hconn hik))
      exact hleft.trans (hmid.trans hright.symm)
    · rintro ⟨j, x⟩
      have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
        (diskAttachmentBaseChangeHomotopyEquiv_cell (wordAttaching C hC i)
          (graphCollapse K C hC hconn i) ⟨j, x⟩)).trans
        (diskFamilyMap_cell (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
          (diskRoseMap (roseGenInclusion K C hC hconn hik)) (subcomplexCellInclusion (hC hik) 2)
          (collapsedAttaching_natural K C hC hconn hik) j x)
      have hright := (congrArg (collapsedDiskChange K C hC hconn k)
        (diskFamilyMap_cell (wordAttaching C hC i) (wordAttaching C hC k)
          (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
          (wordAttaching_natural K C hC hik) j x)).trans
        (diskAttachmentBaseChangeHomotopyEquiv_cell (wordAttaching C hC k)
          (graphCollapse K C hC hconn k) ⟨subcomplexCellInclusion (hC hik) 2 j, x⟩)
      exact hleft.trans hright.symm)]

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

def roseWord (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set K) 2) :
    BoundaryWords (roseAttaching (RoseGen K C hC hconn i)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  exact (word C hC i j).eraseTree (skeletonAttachingMap (C i : Set K) 1)
    (chainTree K C hC hconn i)

theorem roseWord_loop_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) :
    (roseWord K C hC hconn k (subcomplexCellInclusion (hC hik) 2 j)).loopWord =
      ((roseWord K C hC hconn i j).loopWord).map
        (fun p => (roseGenInclusion K C hC hconn hik p.1, p.2)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI := subcomplexZeroSkeleton_discrete (C k)
  unfold roseWord
  erw [word_natural C hC hik j]
  exact BoundaryWords.eraseTree_loop_natural _ _ _ _
    (subcomplexGraphInclusion (hC hik)) (chainTree_compatible K C hC hconn hik) _

abbrev CanonicalGen (i : Fin (n + 1)) := RoseGen K C hC hconn i ⊕ PUnit.{1}
abbrev CanonicalRel (i : Fin (n + 1)) := RelCWComplex.cell (C i : Set K) 2 ⊕ PUnit.{1}

def canonicalGenInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    CanonicalGen K C hC hconn i ↪ CanonicalGen K C hC hconn k :=
  StabilizedDiskPresentation.withDummy (roseGenInclusion K C hC hconn hik)

def canonicalCellInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    CanonicalRel K C i ↪ CanonicalRel K C k :=
  StabilizedDiskPresentation.withDummy (subcomplexCellInclusion (hC hik) 2)

theorem canonicalGenInclusion_comp {i k l : Fin (n + 1)} (hik : i ≤ k) (hkl : k ≤ l)
    (a : CanonicalGen K C hC hconn i) :
    canonicalGenInclusion K C hC hconn hkl (canonicalGenInclusion K C hC hconn hik a) =
      canonicalGenInclusion K C hC hconn (hik.trans hkl) a := by
  cases a <;> rfl

def canonicalRelators (i : Fin (n + 1)) :
    CanonicalRel K C i → FreeGroup (CanonicalGen K C hC hconn i)
  | .inl j => FreeGroup.map Sum.inl (FreeGroup.mk (roseWord K C hC hconn i j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)

theorem canonicalRelators_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    canonicalRelators K C hC hconn k (canonicalCellInclusion K C hC hik j) =
      FreeGroup.map (canonicalGenInclusion K C hC hconn hik) (canonicalRelators K C hC hconn i j) := by
  cases j with
  | inl j =>
      simp only [canonicalRelators, canonicalCellInclusion, StabilizedDiskPresentation.withDummy,
        Function.Embedding.coeFn_mk, Sum.map_inl]
      erw [roseWord_loop_natural K C hC hconn hik j]
      simp
      rfl
  | inr u => rfl

def canonicalWords (i : Fin (n + 1)) :
    CanonicalRel K C i → List (CanonicalGen K C hC hconn i × Bool) :=
  presCanonicalWords (canonicalRelators K C hC hconn i) (Sum.inr PUnit.unit)

theorem canonicalWords_ne_nil (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    canonicalWords K C hC hconn i j ≠ [] := presCanonicalWords_ne_nil _ _ _

theorem canonicalWords_mk (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    FreeGroup.mk (canonicalWords K C hC hconn i j) = canonicalRelators K C hC hconn i j :=
  mk_presCanonicalWords _ _ _

def canonicalWordEmbedding {i k : Fin (n + 1)} (hik : i ≤ k) :
    PresWordEmbedding (canonicalWords K C hC hconn i) (canonicalWords K C hC hconn k) :=
  canonicalPresWordEmbedding _ _ (canonicalGenInclusion K C hC hconn hik)
    (canonicalCellInclusion K C hC hik) (canonicalRelators_natural K C hC hconn hik)
    (Sum.inr PUnit.unit)

def stabilizedAttaching (i : Fin (n + 1)) :=
  StabilizedDiskPresentation.attaching (collapsedAttaching K C hC hconn i)

def stabilizedCellBoundary (i : Fin (n + 1)) (j : CanonicalRel K C i) :=
  (stabilizedAttaching K C hC hconn i).comp
    (⟨fun a => ⟨j, a⟩, by
        exact continuous_sigmaMk (σ := fun _ : CanonicalRel K C i => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ : C(UnitBoundary (Fin 2 → ℝ),
      BoundaryFamily (CanonicalRel K C i) (Fin 2 → ℝ)))

theorem stabilizedCellBoundary_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (stabilizedCellBoundary K C hC hconn i j) =
      stabilizedCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  ext a
  exact StabilizedDiskPresentation.attaching_natural
    (roseGenInclusion K C hC hconn hik) (subcomplexCellInclusion (hC hik) 2)
    (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
    (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2) ⟨j, a⟩

theorem stabilizedCellBoundary_homotopic (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    (stabilizedCellBoundary K C hC hconn i j).Homotopic
      (classicalPresCellBoundary (canonicalWords K C hC hconn i) j
        (canonicalWords_ne_nil K C hC hconn i)) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C i)
      have H₀ := (word C hC i j).collapse_homotopic_eraseTree
        (skeletonAttachingMap (C i : Set K) 1) (skeletonAttachingMap (C i : Set K) 1).continuous
        (chainTree K C hC hconn i)
      have H₁ := H₀.trans (boundaryWords_homotopic_classicalWord (roseWord K C hC hconn i j))
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inl : RoseGen K C hC hconn i → CanonicalGen K C hC hconn i))).comp H₁
      erw [classicalRoseWordBoundary_map] at H
      have he : FreeGroup.mk (((roseWord K C hC hconn i j).loopWord).map
          (fun p => (Sum.inl p.1, p.2))) =
          FreeGroup.mk (canonicalWords K C hC hconn i (Sum.inl j)) := by
        erw [canonicalWords_mk]
        rfl
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (canonicalWords K C hC hconn i)
          (Sum.inl j) (canonicalWords_ne_nil K C hC hconn i)).symm)
  | inr u =>
      cases u
      have H := (ContinuousMap.Homotopic.refl (diskRoseMap
        (Sum.inr : PUnit → CanonicalGen K C hC hconn i))).comp
          dummyCircleBoundaryHomeomorph_homotopic_word
      erw [classicalRoseWordBoundary_map] at H
      have he  :=
        (canonicalWords_mk K C hC hconn i (Sum.inr PUnit.unit)).symm
      exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (canonicalWords K C hC hconn i)
          (Sum.inr PUnit.unit) (canonicalWords_ne_nil K C hC hconn i)).symm)

end FiniteChains.ClassicalCW.ChainWords

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

def canonicalCellBoundary (i : Fin (n + 1)) (j : CanonicalRel K C i) :=
  classicalPresCellBoundary (canonicalWords K C hC hconn i) j
    (canonicalWords_ne_nil K C hC hconn i)

theorem canonicalCellBoundary_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : CanonicalRel K C i) :
    (diskRoseMap (canonicalGenInclusion K C hC hconn hik)).comp
        (canonicalCellBoundary K C hC hconn i j) =
      canonicalCellBoundary K C hC hconn k (canonicalCellInclusion K C hC hik j) := by
  ext a
  exact (canonicalWordEmbedding K C hC hconn hik).classicalPresWordAttaching_natural
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k) ⟨j, a⟩

abbrev CanonicalTopCell := TopCell C ⊕ PUnit.{1}

def canonicalTopCell (i : Fin (n + 1)) : CanonicalRel K C i → CanonicalTopCell K C
  | .inl j => .inl (topCell C hC i j)
  | .inr u => .inr u

def canonicalBirth : CanonicalTopCell K C → Fin (n + 1)
  | .inl j => birth C j
  | .inr _ => 0

def canonicalBirthCell (j : CanonicalTopCell K C) : CanonicalRel K C (canonicalBirth K C j) :=
  match j with
  | .inl j => .inl (birthCell C j)
  | .inr u => .inr u

omit [Choices C] [TreeChoice K C] in
theorem canonicalBirth_le (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    canonicalBirth K C (canonicalTopCell K C hC i j) ≤ i := by
  cases j with
  | inl j => exact birth_le C (topCell C hC i j) i j.property
  | inr u => exact Fin.zero_le _

omit [Choices C] [TreeChoice K C] in
theorem canonicalBirthCell_image (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    canonicalCellInclusion K C hC (canonicalBirth_le K C hC i j)
      (canonicalBirthCell K C (canonicalTopCell K C hC i j)) = j := by
  cases j <;> rfl

def canonicalBirthHomotopy (j : CanonicalTopCell K C) :
    (stabilizedCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)).Homotopy
      (canonicalCellBoundary K C hC hconn (canonicalBirth K C j) (canonicalBirthCell K C j)) :=
  Classical.choice (stabilizedCellBoundary_homotopic K C hC hconn
    (canonicalBirth K C j) (canonicalBirthCell K C j))

def canonicalCellHomotopy (i : Fin (n + 1)) (j : CanonicalRel K C i) :
    (stabilizedCellBoundary K C hC hconn i j).Homotopy
      (canonicalCellBoundary K C hC hconn i j) where
  toContinuousMap := (diskRoseMap
    (canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j))).comp
      (canonicalBirthHomotopy K C hC hconn (canonicalTopCell K C hC i j)).toContinuousMap
  map_zero_left a := by
    change diskRoseMap _ (canonicalBirthHomotopy K C hC hconn _ (0, a)) = _
    rw (config := { transparency := .default }) [(canonicalBirthHomotopy K C hC hconn _).apply_zero]
    have H := congrArg (fun f => f a) (stabilizedCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    rwa [canonicalBirthCell_image] at H
  map_one_left a := by
    change diskRoseMap _ (canonicalBirthHomotopy K C hC hconn _ (1, a)) = _
    rw (config := { transparency := .default }) [(canonicalBirthHomotopy K C hC hconn _).apply_one]
    have H := congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn
      (canonicalBirth_le K C hC i j) (canonicalBirthCell K C (canonicalTopCell K C hC i j)))
    rwa [canonicalBirthCell_image] at H


def canonicalAttaching (i : Fin (n + 1)) :=
  classicalPresWordAttaching (canonicalWords K C hC hconn i) (canonicalWords_ne_nil K C hC hconn i)

def canonicalAttachingHomotopy (i : Fin (n + 1)) :
    (stabilizedAttaching K C hC hconn i).Homotopy (canonicalAttaching K C hC hconn i) := by
  let H j := canonicalCellHomotopy K C hC hconn i j
  let F : C(BoundaryFamily (CanonicalRel K C i) (Fin 2 → ℝ),
      C(I, ClassicalGraphModel.Rose (CanonicalGen K C hC hconn i))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }

def canonicalDiskChange (i : Fin (n + 1)) :
    DiskAttachment (stabilizedAttaching K C hC hconn i) ≃ₕ
      ClassicalPresWordDisks (canonicalWords K C hC hconn i) (canonicalWords_ne_nil K C hC hconn i) :=
  naturalDiskAttachingEquiv _ _ (canonicalAttachingHomotopy K C hC hconn i)

def stabilizedDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  StabilizedDiskPresentation.map (roseGenInclusion K C hC hconn hik)
    (subcomplexCellInclusion (hC hik) 2)
    (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
    (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2)

def canonicalDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  (canonicalWordEmbedding K C hC hconn hik).classicalWordDiskMap
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)


theorem canonicalDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  have h₁ : Whitehead.KillsPi2 (canonicalDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (stabilizedDiskInclusion K C hC hconn hik) := by
    apply Whitehead.killsPi2_homotopyEquiv_square_iff
      (canonicalDiskChange K C hC hconn i) (canonicalDiskChange K C hC hconn k)
    erw [(show (canonicalDiskInclusion K C hC hconn hik).comp (canonicalDiskChange K C hC hconn i).toFun =
      (canonicalDiskChange K C hC hconn k).toFun.comp (stabilizedDiskInclusion K C hC hconn hik) by
      have H := naturalDiskAttachingEquiv_natural
        (stabilizedAttaching K C hC hconn i) (canonicalAttaching K C hC hconn i)
        (canonicalAttachingHomotopy K C hC hconn i)
        (stabilizedAttaching K C hC hconn k) (canonicalAttaching K C hC hconn k)
        (canonicalAttachingHomotopy K C hC hconn k)
        (diskRoseMap (canonicalGenInclusion K C hC hconn hik))
        (canonicalCellInclusion K C hC hik)
        (fun j a => congrArg (fun f => f a) (stabilizedCellBoundary_natural K C hC hconn hik j))
        (fun j a => congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn hik j))
        (fun t j a => (by
          have he : (canonicalGenInclusion K C hC hconn hik ∘
              canonicalGenInclusion K C hC hconn (canonicalBirth_le K C hC i j)) =
              canonicalGenInclusion K C hC hconn ((canonicalBirth_le K C hC i j).trans hik) := by
            funext b
            exact canonicalGenInclusion_comp K C hC hconn _ _ b
          have H := congrArg (fun f => f (canonicalBirthHomotopy K C hC hconn
            (canonicalTopCell K C hC i j) (t, a)))
              ((diskRoseMap_comp _ _).trans (congrArg diskRoseMap he))
          cases j with
          | inl j => exact H
          | inr u => exact H))
      have he : diskFamilyMap (canonicalAttaching K C hC hconn i) (canonicalAttaching K C hC hconn k)
          (diskRoseMap (canonicalGenInclusion K C hC hconn hik)) (canonicalCellInclusion K C hC hik)
          (fun j a => congrArg (fun f => f a) (canonicalCellBoundary_natural K C hC hconn hik j)) =
          canonicalDiskInclusion K C hC hconn hik := by
        apply hom_ext _ (boundaryFamilyInclusion (CanonicalRel K C i) (Fin 2 → ℝ))
        · intro x
          rfl
        · intro d
          erw [diskFamilyMap_cell]
      erw [he] at H
      exact H)]
  have he : DiskPresentationExtension.sourceMap (roseGenInclusion K C hC hconn hik)
      (subcomplexCellInclusion (hC hik) 2) (collapsedAttaching K C hC hconn i)
      (collapsedAttaching K C hC hconn k)
      (fun z => collapsedAttaching_natural K C hC hconn hik z.1 z.2) =
      collapsedDiskInclusion K C hC hconn hik := by
    apply hom_ext _ (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
    · intro x
      rfl
    · intro d
      erw [DiskPresentationExtension.sourceMap_cell]
  exact h₁.trans ((StabilizedDiskPresentation.map_killsPi2_iff _ _ _ _ _).trans
    (he ▸ collapsedDiskInclusion_killsPi2_iff K C hC hconn hik))

end FiniteChains.ClassicalCW.ChainWords
end

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

theorem canonicalInclusion_zeroPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Comb.ZeroPi2 (Comb.presInclHom (canonicalGenInclusion K C hC hconn hik)
      (canonicalGenInclusion K C hC hconn hik).injective
      (canonicalRelators K C hC hconn i) (canonicalRelators K C hC hconn k)
      (canonicalCellInclusion K C hC hik) (canonicalRelators_natural K C hC hconn hik)) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  let e := canonicalWordEmbedding K C hC hconn hik
  have h₁ := e.killsPi2_iff_combPi2
    (fun j => List.length_pos_of_ne_nil (canonicalWords_ne_nil K C hC hconn i j))
    (fun j => List.length_pos_of_ne_nil (canonicalWords_ne_nil K C hC hconn k j))
    (canonicalRelators K C hC hconn i) (canonicalRelators K C hC hconn k)
    (canonicalWords_mk K C hC hconn i) (canonicalWords_mk K C hC hconn k)
  have h₂ := e.classicalWordDiskMap_killsPi2_iff
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)
  exact h₁.symm.trans (h₂.symm.trans (canonicalDiskInclusion_killsPi2_iff K C hC hconn hik))

def canonicalPresChainTopFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainTopFS (canonicalRelators K C hC hconn 0) n where
  gen r := CanonicalGen K C hC hconn (boundedStage n r)
  cell r := CanonicalRel K C (boundedStage n r)
  decGen _ := inferInstance
  rel r := canonicalRelators K C hC hconn (boundedStage n r)
  genIncl r := canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  genIncl_injective r := (canonicalGenInclusion K C hC hconn
    (boundedStage_monotone n (Nat.le_succ r))).injective
  cellIncl r := canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))
  cellIncl_injective r := (canonicalCellInclusion K C hC
    (boundedStage_monotone n (Nat.le_succ r))).injective
  rel_incl r := canonicalRelators_natural K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base j := (FreeGroup.map.id _).symm
  zero_pi2 := by
    intro r hr
    let i : Fin n := ⟨r, hr⟩
    have H := (canonicalInclusion_zeroPi2_iff K C hC hconn
      (show i.castSucc ≤ i.succ from Nat.le_succ r)).mpr (hkill i)
    have hleft : boundedStage n r = i.castSucc := Fin.ext (Nat.min_eq_left (Nat.le_of_lt hr))
    have hright : boundedStage n (r + 1) = i.succ := Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt hr))
    change Comb.ZeroPi2 (Comb.presInclHom
      (canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))) _
      (canonicalRelators K C hC hconn (boundedStage n r))
      (canonicalRelators K C hC hconn (boundedStage n (r + 1)))
      (canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))) _)
    have hh (a b : Fin (n + 1)) (hab : a ≤ b)
        (ha : a = i.castSucc) (hb : b = i.succ) :
        Comb.ZeroPi2 (Comb.presInclHom (canonicalGenInclusion K C hC hconn hab)
          (canonicalGenInclusion K C hC hconn hab).injective
          (canonicalRelators K C hC hconn a) (canonicalRelators K C hC hconn b)
          (canonicalCellInclusion K C hC hab) (canonicalRelators_natural K C hC hconn hab)) := by
      subst a
      subst b
      exact H
    exact hh _ _ _ hleft hright

end FiniteChains.ClassicalCW.ChainWords

section
open scoped Classical unitInterval ContinuousMap
open Set Topology
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment ClassicalGraphModel

variable (K : Whitehead.TwoComplex)


def originalGraphTree : Comb.SpanningTree (originalGraph K) :=
  Classical.choose (originalGraph_exists_spanningTree K (zeroCellPoint (pointVertex (Classical.choice (inferInstance : Nonempty K)))))




def originalTopSkeletonHomeomorph : K ≃ₜ SkeletonCarrier (Set.univ : Set K) 3 where
  toFun x := ⟨x, twoComplex_mem_skeleton_three K x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- Literal original characteristic disks, prior to any graph collapse. -/
def originalAsDiskAttachment :
    K ≃ₜ DiskAttachment (skeletonAttachingMap (Set.univ : Set K) 2) :=
  (originalTopSkeletonHomeomorph K).trans
    (skeletonAsDiskAttachment (Set.univ : Set K) 2)












theorem originalRoseGen_finite (hK : Whitehead.FiniteCells K) : Finite ({j : RelCWComplex.cell (Set.univ : Set K) 1 // ¬(originalGraphTree K).isTree j}) := by
  letI : Finite (Σ n, RelCWComplex.cell Set.univ n) := hK
  letI : Finite (RelCWComplex.cell (Set.univ : Set K) 1) :=
    Finite.of_injective (Sigma.mk 1) (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  infer_instance

theorem originalRoseRel_finite (hK : Whitehead.FiniteCells K) : Finite (RelCWComplex.cell (Set.univ : Set K) 2) := by
  letI : Finite (Σ n, RelCWComplex.cell Set.univ n) := hK
  exact Finite.of_injective (Sigma.mk 2) (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)

end FiniteChains.ClassicalCW
end

section
open scoped Classical
open Set Topology Metric
namespace Whitehead.CWCellEmbedding
open FiniteChains
variable {K L : TwoComplex} (e : CWCellEmbedding K L)

def recharacterizationMap (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    PartialEquiv (Fin n → ℝ) L :=
  if hj : j ∈ Set.range (e.cellIndex n) then
    ClosedEmbeddingCW.imageCharacteristic e.map e.closedEmbedding n (Classical.choose hj)
  else RelCWComplex.map (C := (Set.univ : Set L)) n j

theorem recharacterizationMap_old (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set K) n) :
    recharacterizationMap e n (e.cellIndex n j) =
      ClosedEmbeddingCW.imageCharacteristic e.map e.closedEmbedding n j := by
  have hj : e.cellIndex n j ∈ Set.range (e.cellIndex n) := ⟨j, rfl⟩
  have he  := (e.cellIndex n).injective (Classical.choose_spec hj)
  simp only [recharacterizationMap, dif_pos hj, he]

theorem recharacterizationMap_open (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    recharacterizationMap e n j '' ball 0 1 = CWComplex.openCell (C := (Set.univ : Set L)) n j := by
  by_cases hj : j ∈ Set.range (e.cellIndex n)
  · rw [recharacterizationMap, dif_pos hj, ClosedEmbeddingCW.imageCharacteristic_image]
    change e.map '' CWComplex.openCell n (Classical.choose hj) = _
    rw [e.openCell_image, Classical.choose_spec hj]
  · rw [recharacterizationMap, dif_neg hj]
    rfl

theorem image_closedCell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set K) n) :
    e.map '' CWComplex.closedCell (C := (Set.univ : Set K)) n j =
      CWComplex.closedCell (C := (Set.univ : Set L)) n (e.cellIndex n j) := by
  rw [← CWComplex.closure_openCell_eq_closedCell,
    ← CWComplex.closure_openCell_eq_closedCell, ← e.openCell_image,
    e.closedEmbedding.closure_image_eq]

theorem recharacterizationMap_closed (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    recharacterizationMap e n j '' closedBall 0 1 =
      CWComplex.closedCell (C := (Set.univ : Set L)) n j := by
  by_cases hj : j ∈ Set.range (e.cellIndex n)
  · rw [recharacterizationMap, dif_pos hj, ClosedEmbeddingCW.imageCharacteristic_image]
    change e.map '' CWComplex.closedCell n (Classical.choose hj) = _
    rw [image_closedCell, Classical.choose_spec hj]
  · rw [recharacterizationMap, dif_neg hj]
    rfl

def recharacterizedCW : CWComplex (Set.univ : Set L) where
  cell n := RelCWComplex.cell (Set.univ : Set L) n
  map := recharacterizationMap e
  source_eq := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · rw [recharacterizationMap, dif_pos hj]
      exact ClosedEmbeddingCW.imageCharacteristic_source _ _ _ _
    · rw [recharacterizationMap, dif_neg hj]
      exact RelCWComplex.source_eq n j
  continuousOn := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · rw [recharacterizationMap, dif_pos hj]
      exact ClosedEmbeddingCW.imageCharacteristic_continuousOn _ _ _ _
    · rw [recharacterizationMap, dif_neg hj]
      exact RelCWComplex.continuousOn n j
  continuousOn_symm := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · rw [recharacterizationMap, dif_pos hj]
      exact ClosedEmbeddingCW.imageCharacteristic_continuousOn_symm _ _ _ _
    · rw [recharacterizationMap, dif_neg hj]
      exact RelCWComplex.continuousOn_symm n j
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (recharacterizationMap e a.1 a.2 '' ball 0 1)
      (recharacterizationMap e b.1 b.2 '' ball 0 1)
    rw [recharacterizationMap_open, recharacterizationMap_open]
    exact RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set L)) hab
  mapsTo' := by
    intro n j
    by_cases hj : j ∈ Set.range (e.cellIndex n)
    · let k := Classical.choose hj
      obtain ⟨I, hI⟩ := CWComplex.mapsTo' (C := (Set.univ : Set K)) n k
      refine ⟨fun m => (I m).map (e.cellIndex m), ?_⟩
      intro x hx
      obtain ⟨m, hm, a, ha, hy⟩ := by simpa only [Set.mem_iUnion] using hI hx
      simp only [Set.mem_iUnion]
      refine ⟨m, hm, e.cellIndex m a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      rw [recharacterizationMap_closed, ← image_closedCell]
      refine ⟨RelCWComplex.map (C := (Set.univ : Set K)) n k x, hy, ?_⟩
      rw [recharacterizationMap, dif_pos hj]
      rfl
    · obtain ⟨I, hI⟩ := CWComplex.mapsTo' (C := (Set.univ : Set L)) n j
      refine ⟨I, ?_⟩
      intro x hx
      change recharacterizationMap e n j x ∈
        ⋃ m, ⋃ (_ : m < n), ⋃ k ∈ I m, recharacterizationMap e m k '' closedBall 0 1
      simp only [recharacterizationMap_closed]
      rw [recharacterizationMap, dif_neg hj]
      exact hI hx
  closed' := by
    intro A hA hclosed
    apply (CWComplex.closed (Set.univ : Set L) A hA).mpr
    intro n j
    simpa only [recharacterizationMap_closed] using hclosed n j
  union' := by
    simp only [recharacterizationMap_closed]
    exact CWComplex.union

def recharacterizedComplex : TwoComplex where
  space := L
  topology := L.topology
  hausdorff := L.hausdorff
  cw := recharacterizedCW e
  connected := L.connected
  dimension := L.dimension

theorem recharacterized_openCell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set L) n) :
    @RelCWComplex.openCell L L.topology Set.univ ∅
      (@CWComplex.instRelCWComplex L L.topology Set.univ (recharacterizedCW e)) n j =
      CWComplex.openCell (C := (Set.univ : Set L)) n j :=
  recharacterizationMap_open e n j

def recharacterizedSubcomplex (D : CWComplex.Subcomplex (Set.univ : Set L)) :
    CWComplex.Subcomplex (Set.univ : Set (recharacterizedComplex e)) where
  carrier := D.carrier
  I := D.I
  closed' := D.closed
  union' := by
    change ∅ ∪ (⋃ m, ⋃ j : {j // j ∈ D.I m},
      recharacterizationMap e m j.val '' ball 0 1) = D.carrier
    simp only [recharacterizationMap_open]
    exact D.union

def recharacterizedEmbedding : CWCellEmbedding K (recharacterizedComplex e) where
  map := e.map
  closedEmbedding := e.closedEmbedding
  cellIndex := e.cellIndex
  openCell_image n j := (e.openCell_image n j).trans (recharacterized_openCell e n _).symm

theorem recharacterizedEmbedding_characteristic (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set K) n) (x : Fin n → ℝ) :
    @CWComplex.map L L.topology Set.univ (recharacterizedCW e) n (e.cellIndex n j) x =
      e.map (RelCWComplex.map (C := (Set.univ : Set K)) n j x) := by
  change recharacterizationMap e n (e.cellIndex n j) x = _
  rw [recharacterizationMap_old]
  rfl

end Whitehead.CWCellEmbedding

namespace Whitehead
variable {K L : TwoComplex} (C : CWComplex.Subcomplex (Set.univ : Set L))
  (e : K ≃ₜ (C : Set L)) (he : InitialIdentification C e)

def initialCellEmbedding : CWCellEmbedding K L where
  map := ⟨fun x => (e x).val, continuous_subtype_val.comp e.continuous⟩
  closedEmbedding := C.closed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
  cellIndex n := {
    toFun := fun j => (Classical.choose (he n) j).val
    inj' := fun _ _ hjk => (Classical.choose (he n)).injective (Subtype.ext hjk) }
  openCell_image n j := Classical.choose_spec (he n) j

theorem initialCellEmbedding_range : Set.range (initialCellEmbedding C e he).map = C := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (e x).property
  · intro hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

end Whitehead
end

section
open scoped Classical
open Set Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Whitehead.CWCellEmbedding
open FiniteChains FiniteChains.ClassicalCW FiniteChains.ClassicalGraphModel
open FiniteChains.ClassicalSkeletonAttachment FiniteChains.RelativeAttachment
variable {K L : TwoComplex} (e : CWCellEmbedding K L)

theorem skeleton_image (n : ℕ) :
    e.map '' (CWComplex.skeletonLT (Set.univ : Set K) (n : ℕ∞) : Set K) =
      (CWComplex.skeletonLT (e.imageSubcomplex : Set L) (n : ℕ∞) : Set L) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
    obtain ⟨m, hm, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    apply Set.mem_iUnion.mpr
    refine ⟨m, Set.mem_iUnion.mpr ⟨hm, Set.mem_iUnion.mpr ⟨e.imageCellEquiv m j, ?_⟩⟩⟩
    change e.map x ∈ CWComplex.openCell m (e.cellIndex m j)
    rw [← e.openCell_image]
    exact ⟨x, hj, rfl⟩
  · intro hy
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hy
    obtain ⟨m, hm, j, hj⟩ := by simpa only [Set.mem_iUnion] using hy
    obtain ⟨a, ha⟩ := j.property
    change y ∈ CWComplex.openCell m j.val at hj
    rw [← ha, ← e.openCell_image] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    refine ⟨x, ?_, rfl⟩
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT]
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, Set.mem_iUnion.mpr ⟨a, hx⟩⟩⟩


def skeletonMap (n : ℕ) :
    C(SkeletonCarrier (Set.univ : Set K) n, SkeletonCarrier (e.imageSubcomplex : Set L) n) where
  toFun x := ⟨e.map x.val, ((skeleton_image e n).subset ⟨x.val, x.property, rfl⟩)⟩
  continuous_toFun := (e.map.continuous.comp continuous_subtype_val).subtype_mk _

theorem skeletonMap_isEmbedding (n : ℕ) : IsEmbedding (skeletonMap e n) := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  exact e.closedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal


def skeletonHomeomorph (n : ℕ) :
    SkeletonCarrier (Set.univ : Set K) n ≃ₜ SkeletonCarrier (e.imageSubcomplex : Set L) n :=
  (skeletonMap_isEmbedding e n).toHomeomorphOfSurjective (by
    intro y
    have hy : y.val ∈ (CWComplex.skeletonLT (e.imageSubcomplex : Set L) (n : ℕ∞) : Set L) := y.property
    rw [← skeleton_image] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

variable (hchart : ∀ n (j : RelCWComplex.cell (Set.univ : Set K) n) (x : Fin n → ℝ),
  RelCWComplex.map (C := (Set.univ : Set L)) n (e.cellIndex n j) x =
    e.map (RelCWComplex.map (C := (Set.univ : Set K)) n j x))

def graphHom : Comb.Hom (originalGraph K) (subcomplexGraph e.imageSubcomplex) where
  onV := skeletonMap e 1
  onE := e.imageCellEquiv 1
  onF := Empty.elim
  src_onE j := Subtype.ext (hchart 1 j _)
  tgt_onE j := Subtype.ext (hchart 1 j _)
  base_onF f := nomatch f
  att_onF f := nomatch f

theorem graphHom_injective_V : Function.Injective (graphHom e hchart).onV :=
  (skeletonMap_isEmbedding e 1).injective

theorem graphHom_injective_E : Function.Injective (graphHom e hchart).onE :=
  (e.imageCellEquiv 1).injective

def graphDiskHomeomorph : DiskAttachment (originalGraphAttaching K) ≃ₜ
    DiskAttachment (skeletonAttachingMap (e.imageSubcomplex : Set L) 1) :=
  ((skeletonAttachmentHomeomorph (Set.univ : Set K) 1).trans (skeletonHomeomorph e 2)).trans
    (skeletonAsDiskAttachment (e.imageSubcomplex : Set L) 1)

theorem graphDiskHomeomorph_skeleton (x : DiskAttachment (originalGraphAttaching K)) :
    skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1 (graphDiskHomeomorph e x) =
      skeletonMap e 2 (skeletonAttachmentHomeomorph (Set.univ : Set K) 1 x) :=
  (skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1).apply_symm_apply _

theorem graphDiskHomeomorph_old (v : (originalGraph K).V) :
    graphDiskHomeomorph e (old (originalGraphAttaching K) _ v) =
      old (skeletonAttachingMap (e.imageSubcomplex : Set L) 1) _ ((graphHom e hchart).onV v) := by
  apply (skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1).injective
  rw [graphDiskHomeomorph_skeleton]
  ext
  rfl


theorem graphDiskHomeomorph_edge (j : (originalGraph K).E) (t : unitInterval) :
    graphDiskHomeomorph e (graphEdgePath (originalGraphAttaching K) j t) =
      graphEdgePath (skeletonAttachingMap (e.imageSubcomplex : Set L) 1)
        ((graphHom e hchart).onE j) t :=
  (by
    apply (skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1).injective
    rw [graphDiskHomeomorph_skeleton]
    apply Subtype.ext
    change e.map ((skeletonAttachmentHomeomorph (Set.univ : Set K) 1 (cell _ _ ⟨j, (ClassicalGraphModel.graphDiskHomeomorph t)⟩)).val) =
      (skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1 (cell _ _ ⟨e.imageCellEquiv 1 j, (ClassicalGraphModel.graphDiskHomeomorph t)⟩)).val
    rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]
    exact (hchart 1 j (ClassicalGraphModel.graphDiskHomeomorph t).val).symm)

end Whitehead.CWCellEmbedding

namespace FiniteChains.ClassicalCW
open ClassicalGraphModel ClassicalSkeletonAttachment RelativeAttachment

def originalGraphCellBoundary (K : Whitehead.TwoComplex)
    (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (originalGraphAttaching K)) :=
  (skeletonAsDiskAttachment (Set.univ : Set K) 1).toContinuousMap.comp
    ((skeletonAttachingMap (Set.univ : Set K) 2).comp ⟨fun a => ⟨j, a⟩, by
      exact continuous_sigmaMk (σ := fun _ : RelCWComplex.cell (Set.univ : Set K) 2 => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩)

theorem originalGraphCellBoundary_word_exists (K : Whitehead.TwoComplex)
    (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    ∃ W : BoundaryWords (originalGraphAttaching K),
      (originalGraphCellBoundary K j).Homotopic W.boundaryMap := by
  letI := zeroSkeleton_discrete (X := K)
  exact boundaryMap_homotopic_boundaryWords (originalGraphAttaching K)
    (originalGraphAttaching K).continuous (originalGraphCellBoundary K j)

def fixedGraphWord (K : Whitehead.TwoComplex) (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    BoundaryWords (originalGraphAttaching K) :=
  Classical.choose (originalGraphCellBoundary_word_exists K j)

theorem fixedGraphWord_spec (K : Whitehead.TwoComplex)
    (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    (originalGraphCellBoundary K j).Homotopic (fixedGraphWord K j).boundaryMap :=
  Classical.choose_spec (originalGraphCellBoundary_word_exists K j)

end FiniteChains.ClassicalCW

namespace Whitehead.CWCellEmbedding
open FiniteChains FiniteChains.ClassicalCW FiniteChains.ClassicalGraphModel
open FiniteChains.ClassicalSkeletonAttachment FiniteChains.RelativeAttachment
variable {K L : TwoComplex} (e : CWCellEmbedding K L)
  (hchart : ∀ n (j : RelCWComplex.cell (Set.univ : Set K) n) (x : Fin n → ℝ),
    RelCWComplex.map (C := (Set.univ : Set L)) n (e.cellIndex n j) x =
      e.map (RelCWComplex.map (C := (Set.univ : Set K)) n j x))


theorem fixedGraphWord_transport (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    (subcomplexCellBoundary e.imageSubcomplex (e.imageCellEquiv 2 j)).Homotopic
      ((fixedGraphWord K j).map (graphHom e hchart)).boundaryMap := by
  letI := zeroSkeleton_discrete (X := K)
  letI := subcomplexZeroSkeleton_discrete e.imageSubcomplex
  have H := (ContinuousMap.Homotopic.refl (graphDiskHomeomorph e).toContinuousMap).comp
    (fixedGraphWord_spec K j)
  rw [(show (graphDiskHomeomorph e).toContinuousMap.comp (originalGraphCellBoundary K j) =
      subcomplexCellBoundary e.imageSubcomplex (e.imageCellEquiv 2 j) by
    ext a
    apply (skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1).injective
    change skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1
      (graphDiskHomeomorph e (originalGraphCellBoundary K j a)) = _
    rw [graphDiskHomeomorph_skeleton]
    change skeletonMap e 2
        (skeletonAttachmentHomeomorph Set.univ 1
          ((skeletonAttachmentHomeomorph Set.univ 1).symm _)) =
      skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1
        ((skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1).symm _)
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    apply Subtype.ext
    exact (hchart 2 j a.val).symm)] at H
  have he := BoundaryWords.boundaryMap_map (graphHom e hchart)
    (graphDiskHomeomorph e).toContinuousMap (graphDiskHomeomorph_old e hchart)
    (graphDiskHomeomorph_edge e hchart) (fixedGraphWord K j)
  rwa [he] at H

end Whitehead.CWCellEmbedding
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)

def seededChoices
    (W : ∀ _j : RelCWComplex.cell (C 0 : Set K) 2,
      BoundaryWords (skeletonAttachingMap (C 0 : Set K) 1))
    (hW : ∀ j, (subcomplexCellBoundary (C 0) j).Homotopic (W j).boundaryMap) : Choices C where
  cellWord i j := if hi : i = 0 then by subst i; exact W j
    else Classical.choose (subcomplexCellBoundary_word_exists (C i) j)
  cellWord_spec i j := by
    split_ifs with hi
    · subst i
      exact hW j
    · grind

theorem seededChoices_zero
    (W : ∀ _j : RelCWComplex.cell (C 0 : Set K) 2,
      BoundaryWords (skeletonAttachingMap (C 0 : Set K) 1))
    (hW : ∀ j, (subcomplexCellBoundary (C 0) j).Homotopic (W j).boundaryMap)
    (j : RelCWComplex.cell (C 0 : Set K) 2) :
    Choices.cellWord (self := seededChoices K C W hW) 0 j = W j := by
  rfl

theorem word_zero [Choices C] (j : RelCWComplex.cell (C 0 : Set K) 2) :
    word C hC 0 j = Choices.cellWord 0 j := by
  have hh a ha hj :
      (Choices.cellWord a ⟨j.val, hj⟩).map (subcomplexGraphInclusion (hC ha)) =
        Choices.cellWord 0 j := by
    have hz  := le_antisymm ha (Fin.zero_le _)
    subst a
    have he : subcomplexGraphInclusion (hC ha) = Comb.Hom.id (subcomplexGraph (C 0)) := by
      apply Comb.Hom.ext'
      · rfl
      · rfl
      · funext f
        exact Empty.elim f
    rw [he]
    cases Choices.cellWord 0 j
    simp [BoundaryWords.map, Comb.Hom.id, Comb.mapPath]
  exact hh (birth C (topCell C hC 0 j))
    (birth_le C (topCell C hC 0 j) 0 j.property) (birth_mem C (topCell C hC 0 j))

def seededTreeChoice (T : Comb.SpanningTree (subcomplexGraph (C 0))) : TreeChoice K C := ⟨some T⟩

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW
open ClassicalGraphModel Comb Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) (T : SpanningTree (originalGraph K))

abbrev FixedGen := SpanningTree.NonTree T ⊕ PUnit.{1}
abbrev FixedRel := RelCWComplex.cell (Set.univ : Set K) 2 ⊕ PUnit.{1}

def fixedRelators : FixedRel K → FreeGroup (FixedGen K T)
  | .inl j => FreeGroup.map Sum.inl (SpanningTree.pathWord T (fixedGraphWord K j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)

end FiniteChains.ClassicalCW
end

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel Comb
open Set Topology
open scoped Classical
variable (D K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C] [TreeChoice K C]
  (T : SpanningTree (originalGraph D))
  (g : Hom (originalGraph D) (subcomplexGraph (C 0)))
  (hg : Function.Injective g.onE)
  (c : RelCWComplex.cell (Set.univ : Set D) 2 ↪ RelCWComplex.cell (C 0 : Set K) 2)
  (hw : ∀ j, Choices.cellWord 0 (c j) = (fixedGraphWord D j).map g)
  (ht : ∀ a, (chainTree K C hC hconn 0).isTree (g.onE a) ↔ T.isTree a)

def fixedBaseGen : FixedGen D T ↪ CanonicalGen K C hC hconn 0 :=
  StabilizedDiskPresentation.withDummy
    ⟨SpanningTree.nonTreeIncl ht, SpanningTree.nonTreeIncl_injective ht hg⟩

def fixedBaseCell : FixedRel D ↪ CanonicalRel K C 0 :=
  StabilizedDiskPresentation.withDummy c

include hw in
theorem fixedBase_relators (j : FixedRel D) :
    canonicalRelators K C hC hconn 0 (fixedBaseCell D K C c j) =
      FreeGroup.map (fixedBaseGen D K C hC hconn T g hg ht) (fixedRelators D T j) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C 0)
      change FreeGroup.map Sum.inl (FreeGroup.mk
        (((word C hC 0 (c j)).eraseTree (skeletonAttachingMap (C 0 : Set K) 1)
          (chainTree K C hC hconn 0)).loopWord)) = _
      erw [BoundaryWords.eraseTree_mk, word_zero, hw, BoundaryWords.loopWord_map,
        SpanningTree.pathWord_mapPath ht]
      erw [FreeGroup.map.comp, FreeGroup.map.comp]
      rfl
  | inr u =>
      cases u
      rfl

def fixedPresChainTopFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainTopFS (fixedRelators D T) n where
  gen r := CanonicalGen K C hC hconn (boundedStage n r)
  cell r := CanonicalRel K C (boundedStage n r)
  decGen _ := inferInstance
  rel r := canonicalRelators K C hC hconn (boundedStage n r)
  genIncl r := canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  genIncl_injective r := (canonicalGenInclusion K C hC hconn
    (boundedStage_monotone n (Nat.le_succ r))).injective
  cellIncl r := canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))
  cellIncl_injective r := (canonicalCellInclusion K C hC
    (boundedStage_monotone n (Nat.le_succ r))).injective
  rel_incl r := canonicalRelators_natural K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  baseGen := fixedBaseGen D K C hC hconn T g hg ht
  baseGen_injective := (fixedBaseGen D K C hC hconn T g hg ht).injective
  baseCell := fixedBaseCell D K C c
  baseCell_injective := (fixedBaseCell D K C c).injective
  rel_base := fixedBase_relators D K C hC hconn T g hg c hw ht
  zero_pi2 := (canonicalPresChainTopFS K C hC hconn hkill).zero_pi2

def fixedPresChainFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainFS (fixedRelators D T) n :=
  (fixedPresChainTopFS D K C hC hconn T g hg c hw ht hkill).toPresChainFS

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel Comb
open Set Topology
open scoped Classical
variable (D K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  (T : SpanningTree (originalGraph D))
  (e : Whitehead.CWCellEmbedding D K)
  (hchart : ∀ m (j : RelCWComplex.cell (Set.univ : Set D) m) (x : Fin m → ℝ),
    RelCWComplex.map (C := (Set.univ : Set K)) m (e.cellIndex m j) x =
      e.map (RelCWComplex.map (C := (Set.univ : Set D)) m j x))
  (h₀ : C 0 = e.imageSubcomplex)

def chartedGraphAt (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) : Hom (originalGraph D) (subcomplexGraph S) :=
  hS.symm ▸ e.graphHom hchart

def chartedCellsAt (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set D) m ≃ RelCWComplex.cell (S : Set K) m :=
  hS.symm ▸ e.imageCellEquiv m

theorem chartedGraphAt_injective_V (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) : Function.Injective (chartedGraphAt D K e hchart S hS).onV := by
  subst S
  exact e.graphHom_injective_V hchart

theorem chartedGraphAt_injective_E (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) : Function.Injective (chartedGraphAt D K e hchart S hS).onE := by
  subst S
  exact e.graphHom_injective_E hchart

theorem chartedWordAt_spec (S : CWComplex.Subcomplex (Set.univ : Set K))
    (hS : S = e.imageSubcomplex) (j : RelCWComplex.cell (Set.univ : Set D) 2) :
    (subcomplexCellBoundary S (chartedCellsAt D K e S hS 2 j)).Homotopic
      ((fixedGraphWord D j).map (chartedGraphAt D K e hchart S hS)).boundaryMap := by
  subst S
  exact e.fixedGraphWord_transport hchart j

def chartedInitialGraph : Hom (originalGraph D) (subcomplexGraph (C 0)) :=
  chartedGraphAt D K e hchart (C 0) h₀

def chartedInitialCells (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set D) m ≃ RelCWComplex.cell (C 0 : Set K) m :=
  chartedCellsAt D K e (C 0) h₀ m


theorem chartedInitialGraph_injective_E : Function.Injective (chartedInitialGraph D K C e hchart h₀).onE :=
  chartedGraphAt_injective_E D K e hchart (C 0) h₀

theorem chartedInitialWord_spec (j : RelCWComplex.cell (Set.univ : Set D) 2) :
    (subcomplexCellBoundary (C 0) (chartedInitialCells D K C e h₀ 2 j)).Homotopic
      ((fixedGraphWord D j).map (chartedInitialGraph D K C e hchart h₀)).boundaryMap :=
  chartedWordAt_spec D K e hchart (C 0) h₀ j

def chartedInitialChoices : Choices C :=
  seededChoices K C
    (fun j => (fixedGraphWord D ((chartedInitialCells D K C e h₀ 2).symm j)).map
      (chartedInitialGraph D K C e hchart h₀))
    (fun j => by simpa only [Equiv.apply_symm_apply] using
      chartedInitialWord_spec D K C e hchart h₀ ((chartedInitialCells D K C e h₀ 2).symm j))

theorem chartedInitialChoices_old (j : RelCWComplex.cell (Set.univ : Set D) 2) :
    (chartedInitialChoices D K C e hchart h₀).cellWord 0 (chartedInitialCells D K C e h₀ 2 j) =
      (fixedGraphWord D j).map (chartedInitialGraph D K C e hchart h₀) := by
  rw [chartedInitialChoices, seededChoices_zero, Equiv.symm_apply_apply]

def chartedFixedPresChainFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainFS (fixedRelators D T) n := by
  letI : Choices C := chartedInitialChoices D K C e hchart h₀
  let g := chartedInitialGraph D K C e hchart h₀
  let htree := SpanningTree.exists_extension g
    (graph_connected K C hC hconn 0) T.root T
    (chartedGraphAt_injective_V D K e hchart (C 0) h₀)
    (chartedInitialGraph_injective_E D K C e hchart h₀)
  let U := Classical.choose htree
  have hU := (Classical.choose_spec htree).2
  letI : TreeChoice K C := seededTreeChoice K C U
  have ht : ∀ a, (chainTree K C hC hconn 0).isTree (g.onE a) ↔ T.isTree a := by
    rw [chainTree_zero K C hC hconn U rfl]
    exact hU
  exact fixedPresChainFS D K C hC hconn T g
    (chartedInitialGraph_injective_E D K C e hchart h₀)
    (chartedInitialCells D K C e h₀ 2).toEmbedding
    (chartedInitialChoices_old D K C e hchart h₀) ht hkill

end FiniteChains.ClassicalCW.ChainWords

namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.ClassicalCW.ChainWords
open Set Topology
open scoped Classical
variable (K : TwoComplex) (T : Comb.SpanningTree (originalGraph K))

theorem fixedPresChainFS_of_hasChain {n : ℕ} {finite : Bool} (h : HasChain K n finite) :
    Nonempty (PresChainFS (fixedRelators K T) n) := by
  obtain ⟨L, C, e, he, _hfin, hconn, hstep⟩ := h
  have hC : Monotone C := Fin.monotone_iff_le_succ.mpr (fun i => (hstep i).choose)
  let f := initialCellEmbedding (C 0) e he
  let L' := f.recharacterizedComplex
  let C' i : CWComplex.Subcomplex Set.univ := f.recharacterizedSubcomplex (C i)
  have hC'  := hC
  have hconn'  := hconn
  let f'  := f.recharacterizedEmbedding
  have h₀ : C' 0 = f'.imageSubcomplex := by
    apply SetLike.coe_injective
    exact (initialCellEmbedding_range (C 0) e he).symm
  have hchart  :=
    f.recharacterizedEmbedding_characteristic
  have hz : ∀ i : Fin n, KillsPi2
      (⟨Set.inclusion (hC' (Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C' i.castSucc), (C' i.succ))) := by
    intro i
    exact (hstep i).choose_spec.2
  exact ⟨chartedFixedPresChainFS K L' C' hC' hconn' T f' hchart h₀ hz⟩

/-- The base is fixed before any ambient chain is chosen. -/
theorem fixedPresChainsFS_of_original_chains
    (h : ∀ n : ℕ, 1 ≤ n → HasChain K n false) :
    ∀ n : ℕ, Nonempty (PresChainFS (fixedRelators K T) n) := by
  intro n
  cases n with
  | zero =>
      obtain ⟨L, C, e, he, hf, hc, _hs⟩ := h 1 le_rfl
      apply fixedPresChainFS_of_hasChain K T
      refine ⟨L, (fun _ : Fin 1 => C 0), e, he, hf, (fun _ => hc 0), ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n => exact fixedPresChainFS_of_hasChain K T (h (n + 1) (Nat.succ_pos n))

end Whitehead

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical unitInterval ContinuousMap
variable (K : Whitehead.TwoComplex) (T : Comb.SpanningTree (originalGraph K))

def fixedGraphAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  (skeletonAsDiskAttachment (Set.univ : Set K) 1).toContinuousMap.comp
    (skeletonAttachingMap (Set.univ : Set K) 2)

def fixedGraphWordAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      DiskAttachment (originalGraphAttaching K)) :=
  ⟨fun a => (fixedGraphWord K a.1).boundaryMap a.2,
    continuous_sigma (fun j => (fixedGraphWord K j).boundaryMap.continuous)⟩

def fixedGraphAttachingHomotopy : (fixedGraphAttaching K).Homotopy (fixedGraphWordAttaching K) := by
  let H j := Classical.choice (fixedGraphWord_spec K j)
  let F : C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      C(I, DiskAttachment (originalGraphAttaching K))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }


def fixedGraphCollapse : DiskAttachment (originalGraphAttaching K) ≃ₕ
    ClassicalGraphModel.Rose (Comb.SpanningTree.NonTree T) := by
  letI := zeroSkeleton_discrete (X := K)
  exact graphRoseHomotopyEquiv (originalGraphAttaching K) (originalGraphAttaching K).continuous T

def fixedRoseAttaching :
    C(BoundaryFamily (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ),
      ClassicalGraphModel.Rose (Comb.SpanningTree.NonTree T)) :=
  (fixedGraphCollapse K T).toFun.comp (fixedGraphWordAttaching K)


def fixedCanonicalWords : FixedRel K → List (FixedGen K T × Bool) :=
  presCanonicalWords (fixedRelators K T) (Sum.inr PUnit.unit)

theorem fixedCanonicalWords_ne_nil (j : FixedRel K) : fixedCanonicalWords K T j ≠ [] :=
  presCanonicalWords_ne_nil _ _ _

theorem fixedCanonicalWords_mk (j : FixedRel K) :
    FreeGroup.mk (fixedCanonicalWords K T j) = fixedRelators K T j := mk_presCanonicalWords _ _ _

def fixedStabilizedBoundary (j : FixedRel K) :
    C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose (FixedGen K T)) :=
  (StabilizedDiskPresentation.attaching (fixedRoseAttaching K T)).comp
    (⟨fun a => ⟨j, a⟩, by
      exact continuous_sigmaMk («σ» := fun _ : FixedRel K => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ :
        C(UnitBoundary (Fin 2 → ℝ), BoundaryFamily (FixedRel K) (Fin 2 → ℝ)))



def fixedClassicalPresWordDiskEquiv : K ≃ₕ
    ClassicalPresWordDisks (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T) :=
  ((((((originalAsDiskAttachment K).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (Set.univ : Set K) 2)
      (skeletonAsDiskAttachment (Set.univ : Set K) 1).toHomotopyEquiv)).trans
        (diskAttachingHomotopyEquiv _ _ (fixedGraphAttachingHomotopy K)))).trans
    (diskAttachmentBaseChangeHomotopyEquiv (fixedGraphWordAttaching K) (fixedGraphCollapse K T))).trans (StabilizedDiskPresentation.homotopyEquiv (fixedRoseAttaching K T))).trans
    (diskAttachingHomotopyEquiv _ _ (by
      let H j := Classical.choice (show (fixedStabilizedBoundary K T j).Homotopic
      (classicalPresCellBoundary (fixedCanonicalWords K T) j (fixedCanonicalWords_ne_nil K T)) by
        cases j with
        | inl j =>
            letI := zeroSkeleton_discrete (X := K)
            let W := (fixedGraphWord K j).eraseTree (originalGraphAttaching K) T
            have H₀ := (fixedGraphWord K j).collapse_homotopic_eraseTree
              (originalGraphAttaching K) (originalGraphAttaching K).continuous T
            have H₁ := H₀.trans (boundaryWords_homotopic_classicalWord W)
            have H := (ContinuousMap.Homotopic.refl (diskRoseMap
              (Sum.inl : Comb.SpanningTree.NonTree T → FixedGen K T))).comp H₁
            erw [classicalRoseWordBoundary_map] at H
            have he : FreeGroup.mk (W.loopWord.map (fun p => ((Sum.inl p.1 : FixedGen K T), p.2))) =
                FreeGroup.mk (fixedCanonicalWords K T (Sum.inl j)) := by
              erw [fixedCanonicalWords_mk]
              change FreeGroup.map Sum.inl (FreeGroup.mk W.loopWord) = _
              erw [BoundaryWords.eraseTree_mk]
              rfl
            exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
              (classicalPresWordAttaching_homotopic_read (fixedCanonicalWords K T) (Sum.inl j)
                (fixedCanonicalWords_ne_nil K T)).symm)
        | inr u =>
            cases u
            have H := (ContinuousMap.Homotopic.refl (diskRoseMap
              (Sum.inr : PUnit → FixedGen K T))).comp dummyCircleBoundaryHomeomorph_homotopic_word
            erw [classicalRoseWordBoundary_map] at H
            have he  :=
              (fixedCanonicalWords_mk K T (Sum.inr PUnit.unit)).symm
            exact H.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
              (classicalPresWordAttaching_homotopic_read (fixedCanonicalWords K T) (Sum.inr PUnit.unit)
                (fixedCanonicalWords_ne_nil K T)).symm))
      let F : C(BoundaryFamily (FixedRel K) (Fin 2 → ℝ), C(I, ClassicalGraphModel.Rose (FixedGen K T))) :=
        ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
          continuous_sigma (fun j =>
            ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
      exact {
        toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
        map_zero_left := fun a => (H a.1).apply_zero a.2
        map_one_left := fun a => (H a.1).apply_one a.2 }))

def fixedCanonicalRealizationEquiv : K ≃ₕ Comb.orderNerveRealization (PresPos (fixedCanonicalWords K T)) :=
  (fixedClassicalPresWordDiskEquiv K T).trans
    (presClassicalDiskComparison (fixedCanonicalWords K T) (fixedCanonicalWords_ne_nil K T)).symm

end FiniteChains.ClassicalCW

section
open scoped Classical
namespace FiniteChains.ClassicalCW
open PresModel

variable (K : Whitehead.TwoComplex)

abbrev CanonicalGen := FixedGen K (originalGraphTree K)
abbrev CanonicalRel := FixedRel K

def canonicalDummy : CanonicalGen K := Sum.inr PUnit.unit

def canonicalRelators : CanonicalRel K → FreeGroup (CanonicalGen K) :=
  fixedRelators K (originalGraphTree K)

def canonicalWords : CanonicalRel K → List (CanonicalGen K × Bool) :=
  fixedCanonicalWords K (originalGraphTree K)

theorem canonicalWords_ne_nil (j : CanonicalRel K) : canonicalWords K j ≠ [] :=
  fixedCanonicalWords_ne_nil K (originalGraphTree K) j

def originalClassicalPresWordDiskEquiv :
    ContinuousMap.HomotopyEquiv K
      (ClassicalPresWordDisks (presCanonicalWords (canonicalRelators K) (canonicalDummy K))
        (presCanonicalWords_ne_nil (canonicalRelators K) (canonicalDummy K))) :=
  fixedClassicalPresWordDiskEquiv K (originalGraphTree K)

def originalCanonicalRealizationEquiv :
    ContinuousMap.HomotopyEquiv K (Comb.orderNerveRealization (PresPos (canonicalWords K))) :=
  fixedCanonicalRealizationEquiv K (originalGraphTree K)

theorem canonicalGen_finite (hK : Whitehead.FiniteCells K) : Finite (CanonicalGen K) := by
  haveI : Finite (Comb.SpanningTree.NonTree (originalGraphTree K)) := originalRoseGen_finite K hK
  infer_instance

theorem canonicalRel_finite (hK : Whitehead.FiniteCells K) : Finite (CanonicalRel K) := by
  letI := originalRoseRel_finite K hK
  infer_instance

end FiniteChains.ClassicalCW

namespace FiniteChains.ClassicalCW
open Comb PresModel CategoryTheory

abbrev CanonicalPos (K : Whitehead.TwoComplex) := PresPos (canonicalWords K)

instance canonicalPos_nonempty (K : Whitehead.TwoComplex) : Nonempty (CanonicalPos K) :=
  ⟨Sum.inl (Sum.inl Rose.base)⟩

instance canonicalPos_dimension (K : Whitehead.TwoComplex) :
    (nerve (CanonicalPos K)).HasDimensionLE 2 :=
  orderNerve_hasDimensionLE (presPosDimension (canonicalWords K))
    (presPosDimension_strictMono (canonicalWords K)) 2
    (presPosDimension_le_two (canonicalWords K))

def canonicalTwoComplex (K : Whitehead.TwoComplex) : Whitehead.TwoComplex :=
  orderNerveTwoComplex (CanonicalPos K) (presPos_isConnected _ (canonicalWords_ne_nil K))

def originalCanonicalTwoComplexEquiv (K : Whitehead.TwoComplex) :
    ContinuousMap.HomotopyEquiv K (canonicalTwoComplex K) :=
  originalCanonicalRealizationEquiv K

theorem canonicalTwoComplex_hasCover (K : Whitehead.TwoComplex)
    (h : Whitehead.HasAcyclicRegularCover K) :
    Whitehead.HasAcyclicRegularCover (canonicalTwoComplex K) :=
  Whitehead.hasAcyclicRegularCover_of_homotopyEquiv (canonicalTwoComplex K) K
    (originalCanonicalTwoComplexEquiv K).symm h

end FiniteChains.ClassicalCW

namespace FiniteChains.Comb.SpanningTree
universe u
variable {P : Type u} [PartialOrder P]

theorem nonempty_nonTree_of_strictTriangle (T : SpanningTree (strictOrderCx P))
    (t : StrictOrdTri P) : Nonempty (NonTree T) := by
  let e₀₁ : StrictOrdEdge P := ⟨(t.val.1, t.val.2.1), t.property.1⟩
  let e₁₂ : StrictOrdEdge P := ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
  let e₀₂ : StrictOrdEdge P := ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩
  by_cases h₀₁ : T.isTree e₀₁
  · by_cases h₁₂ : T.isTree e₁₂
    · by_cases h₀₂ : T.isTree e₀₂
      · have h₁ := T.height_step_of_isTree h₀₁
        have h₂ := T.height_step_of_isTree h₁₂
        have h₃ := T.height_step_of_isTree h₀₂
        change (T.ht t.val.1 + 1 = T.ht t.val.2.1 ∨
          T.ht t.val.2.1 + 1 = T.ht t.val.1) at h₁
        change (T.ht t.val.2.1 + 1 = T.ht t.val.2.2 ∨
          T.ht t.val.2.2 + 1 = T.ht t.val.2.1) at h₂
        change (T.ht t.val.1 + 1 = T.ht t.val.2.2 ∨
          T.ht t.val.2.2 + 1 = T.ht t.val.1) at h₃
        omega
      · exact ⟨⟨e₀₂, h₀₂⟩⟩
    · exact ⟨⟨e₁₂, h₁₂⟩⟩
  · exact ⟨⟨e₀₁, h₀₁⟩⟩

end FiniteChains.Comb.SpanningTree

namespace FiniteChains.ClassicalCW
open Comb PresModel


def canonicalTreeGenerator (K : Whitehead.TwoComplex)
    (T : SpanningTree (strictOrderCx (CanonicalPos K))) : SpanningTree.NonTree T :=
  Classical.choice (T.nonempty_nonTree_of_strictTriangle (presCoverRelatorTriangle (canonicalWords K) id (IdentityChains.cover (canonicalWords K))
    (presCanonicalWords_positive (canonicalRelators K) (canonicalDummy K))
    ⟨(apexOf (canonicalWords K) (Sum.inr PUnit.unit), Sum.inr PUnit.unit), rfl⟩))

end FiniteChains.ClassicalCW
end

namespace FiniteChains.Comb
universe u
variable (X : Complex2.{u})

/-- Edge chains modulo actual finite face boundaries. -/
abbrev EdgeBoundaryQuotient := (X.E →₀ ℤ) ⧸ LinearMap.range (bdry2 X)

/-- The chain of a based loop, in the actual cellular boundary quotient. -/
def loopBoundaryClass (a : X.V) :
    Pi1 X a →* Multiplicative (EdgeBoundaryQuotient X) where
  toFun := Quotient.lift (fun p : Loop X a =>
    Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain p.val))) (by
      intro p q h
      apply congrArg Multiplicative.ofAdd
      apply (Submodule.Quotient.eq _).mpr
      exact h.exists_boundary)
  map_one' := rfl
  map_mul' g h := by
    induction g using Quotient.inductionOn with
    | h p =>
      induction h using Quotient.inductionOn with
      | h q =>
        change Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain (p.val ++ q.val))) = _
        rw [pathChain_append, Submodule.Quotient.mk_add]
        rfl

/-- A commutator loop has a genuine finite integral face filling. -/
theorem loop_bounds_of_mem_commutator (a : X.V) (p : Loop X a)
    (hp : Pi1.mk p ∈ commutator (Pi1 X a)) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain p.val := by
  have hz := Abelianization.commutator_subset_ker (loopBoundaryClass X a) hp
  change Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain p.val)) = 1 at hz
  simp_all

/-- Actual loop fillings give actual finite one-cycle fillings in a connected complex. -/
theorem oneCycle_filling_of_loop_fillings (a : X.V) (hX : IsConnected X)
    (hloop : ∀ p : Loop X a, ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain p.val)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = c := by
  choose p hp using hX a
  have hface e : ∃ y : X.F →₀ ℤ,
      bdry2 X y = Finsupp.single e 1 + pathChain (p (X.src e)) -
        pathChain (p (X.tgt e)) := by
    let l := p (X.src e) ++ [(e, true)] ++ revPath (p (X.tgt e))
    have hl  :=
      ((hp _).append (show IsPath X.src X.tgt [(e, true)] (X.src e) (X.tgt e)
        from ⟨rfl, rfl⟩)).append (isPath_revPath (hp _))
    obtain ⟨y, hy⟩ := hloop ⟨l, hl⟩
    refine ⟨y, ?_⟩
    simpa [l, pathChain_append, pathChain_cons, pathChain_revPath,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy
  choose f hf using hface
  let s  :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  let t  := Finsupp.linearCombination ℤ f
  have hs v : s (Finsupp.single v 1) = pathChain (p v) := by simp [s]
  have ht z : bdry2 X (t z) = z - s (bdry1 X z) := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]; abel
    | single e n =>
      rw [Finsupp.linearCombination_single, map_smul, hf, bdry1_single,
        map_smul, map_sub, hs, hs, smul_sub, smul_add, smul_sub]
      simp
      abel
  exact ⟨t c, by rw [ht, hc, map_zero, sub_zero]⟩

/-- Perfect fundamental group kills every actual finite one-cycle. -/
theorem oneCycle_filling_of_perfect_pi1 (a : X.V) (hX : IsConnected X)
    (hperfect : commutator (Pi1 X a) = ⊤)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = c := by
  apply oneCycle_filling_of_loop_fillings X a hX _ c hc
  intro p
  exact loop_bounds_of_mem_commutator X a p (by rw [hperfect]; trivial)

end FiniteChains.Comb

namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- Sheet coordinates on an actual fibre of the cocycle covering. -/
def coverFibreEquiv (p : P) : {x : c.Cover // x.point = p} ≃ G where
  toFun x := x.val.sheet
  invFun g := ⟨⟨p, g⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    cases x with
    | mk x hx => cases x; cases hx; rfl
  right_inv _ := rfl

/-- The genuine universal-cover path class maps to its endpoint and reading. -/
def universalReading (a : P) (v : UOrder P a) : c.Cover :=
  ⟨uOrderEnd v, c.readVertex a v⟩

theorem universalReading_monotone (a : P) : Monotone (c.universalReading a) := by
  intro v w h
  obtain ⟨h, hw⟩ := h
  refine ⟨h, ?_⟩
  have he := c.readVertex_extend a (ordPos h) v rfl
  change c.readVertex a (uOrderStep v (uOrderEnd w) h) =
    c.readVertex a v * c.val (uOrderEnd v) (uOrderEnd w) at he
  rw [hw] at he
  exact he.symm

theorem universalReading_surjective (a : P) (hP : IsConnected (orderCx P))
    (hm : Function.Surjective (c.monodromy a)) :
    Function.Surjective (c.universalReading a) := by
  rintro ⟨p, g⟩
  obtain ⟨v, hv⟩ := (uOrderEnd_isPosetCover hP).surj p
  obtain ⟨z, hz, hg⟩ := c.readVertex_fibre_surjective a hm v g
  refine ⟨z, ?_⟩
  change Cover.mk (uOrderEnd z) (c.readVertex a z) = Cover.mk p g
  rw [hg, show uOrderEnd z = p from hz.trans hv]

/-- Surjective monodromy, rather than faithful monodromy, gives a connected cover. -/
theorem cover_isConnected (a : P) (hP : IsConnected (orderCx P))
    (hm : Function.Surjective (c.monodromy a)) : IsConnected (orderCx c.Cover) := by
  intro v w
  obtain ⟨v', rfl⟩ := c.universalReading_surjective a hP hm v
  obtain ⟨w', rfl⟩ := c.universalReading_surjective a hP hm w
  obtain ⟨p, hp⟩ := uOrder_complex_isConnected v' w'
  exact ⟨mapPath (orderCxMap (c.universalReading a) (c.universalReading_monotone a)) p,
    isPath_mapPath _ hp⟩

theorem cover_deck_transitive (v w : c.Cover) (h : v.point = w.point) :
    ∃ e : c.Cover ≃o c.Cover,
      (∀ p, (e p).point = p.point) ∧ e v = w := by
  refine ⟨c.coverDeck (w.sheet * v.sheet⁻¹), fun _ => rfl, ?_⟩
  cases v with
  | mk vp vg =>
    cases w with
    | mk wp wg =>
      dsimp only at h
      subst wp
      simp [coverDeck, mul_assoc]

end FiniteChains.Comb.OrdCocycle

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

def coverBase (a : P) : c.Cover := ⟨a, 1⟩
def coverHom : Hom (orderCx c.Cover) (orderCx P) :=
  orderCxMap Cover.point c.coverProjection_isPosetCover.mono


theorem coverPath_sheet {a b : c.Cover} {p : List ((orderCx c.Cover).E × Bool)}
    (hp : IsPath (orderCx c.Cover).src (orderCx c.Cover).tgt p a b) :
    a.sheet * c.readPath (mapPath c.coverHom p) = b.sheet := by
  induction p generalizing a with
  | nil => simp_all
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    change a.sheet * c.readPath (((c.coverHom).onE e.1, e.2) :: mapPath c.coverHom p) = _
    rw [readPath_cons, ← mul_assoc, ha, (show (germSrc (orderCx c.Cover).src (orderCx c.Cover).tgt e).sheet *
        c.readGerm ((c.coverHom).onE e.1, e.2) =
      (germTgt (orderCx c.Cover).src (orderCx c.Cover).tgt e).sheet by
      obtain ⟨e, b⟩ := e
      cases b with
      | true => exact e.property.2
      | false =>
        change e.val.2.sheet * (c.val e.val.1.point e.val.2.point)⁻¹ = e.val.1.sheet
        rw [← e.property.2]
        simp)]
    exact ih hp

theorem coverPi1_reading (a : P) (g : Pi1 (orderCx c.Cover) (c.coverBase a)) :
    c.monodromy a (pi1Map c.coverHom (c.coverBase a) g) = 1 := by
  induction g using Quotient.inductionOn with
  | h p =>
    have h := c.coverPath_sheet p.property
    change c.readPath (mapPath c.coverHom p.val) = 1
    simpa using h

/-- The fundamental group of the honest cocycle cover maps to the monodromy kernel. -/
def coverPi1KernelHom (a : P) :
    Pi1 (orderCx c.Cover) (c.coverBase a) →* (c.monodromy a).ker :=
  (pi1Map c.coverHom (c.coverBase a)).codRestrict _ (c.coverPi1_reading a)

theorem coverPi1KernelHom_injective (a : P) :
    Function.Injective (c.coverPi1KernelHom a) := by
  intro g h he
  exact pi1Map_injective_of_isCovering
    (isCovering_orderCxMap c.coverProjection_isPosetCover) (c.coverBase a)
      (congrArg Subtype.val he)

/-- Every kernel class lifts to an actual closed path, since its sheet reading is one. -/
theorem coverPi1KernelHom_surjective (a : P) :
    Function.Surjective (c.coverPi1KernelHom a) := by
  intro g
  obtain ⟨p, hp⟩ := Quotient.exists_rep g.val
  change Pi1.mk p = g.val at hp
  have hread : c.readPath p.val = 1 := by
    change c.monodromy a (Pi1.mk p) = 1
    rw [hp]
    exact g.property
  obtain ⟨m, b, hm, he⟩ := exists_liftPathAt
    (isCovering_orderCxMap c.coverProjection_isPosetCover)
    p.val (c.coverBase a) a p.property
  change mapPath c.coverHom m = p.val at he
  have hbpoint  :=
    isPath_endpoint_eq (isPath_mapPath c.coverHom hm) (he.symm ▸ p.property)
  have hbsheet : b.sheet = 1 := by
    have h := c.coverPath_sheet hm
    rw [he, hread] at h
    simpa only [coverBase, one_mul] using h.symm
  have hb : b = c.coverBase a := by
    cases b with
    | mk bp bg => dsimp only at hbpoint hbsheet; cases hbpoint; cases hbsheet; rfl
  refine ⟨Pi1.mk ⟨m, hb ▸ hm⟩, ?_⟩
  ext
  change Pi1.mk ⟨mapPath c.coverHom m, _⟩ = g.val
  rw [← hp]
  apply congrArg Pi1.mk
  exact Subtype.ext he

def coverPi1KernelEquiv (a : P) :
    Pi1 (orderCx c.Cover) (c.coverBase a) ≃* (c.monodromy a).ker :=
  MulEquiv.ofBijective (c.coverPi1KernelHom a)
    ⟨c.coverPi1KernelHom_injective a, c.coverPi1KernelHom_surjective a⟩

end FiniteChains.Comb.OrdCocycle
end

namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J G : Type u} [Group G] (w : J → List (α × Bool))
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

abbrev Coc := presCoc w gen hrel
abbrev Space := (Coc w gen hrel).Cover
abbrev projection : Space w gen hrel → PresPos w := OrdCocycle.Cover.point
abbrev covering : IsPosetCover (projection w gen hrel) :=
  (Coc w gen hrel).coverProjection_isPosetCover
abbrev cylinderProjection := coneAdjCoverBaseEnd (projection w gen hrel)
abbrev cylinderCovering := coneAdjCoverBaseEnd_isPosetCover
  (projection w gen hrel) (covering w gen hrel)
abbrev RoseSpace := cylinderCoverRoseSet w (cylinderProjection w gen hrel)
abbrev roseProjection := cylinderCoverRoseEnd w (cylinderProjection w gen hrel)
abbrev roseCovering := cylinderCoverRoseEnd_isPosetCover w
  (cylinderProjection w gen hrel) (cylinderCovering w gen hrel)

/-- An actual lifted relator is exactly an apex sheet together with a relator label. -/
def relatorEquiv : PresCoverRelator w (projection w gen hrel) ≃ G × J where
  toFun p := (p.val.1.sheet, p.val.2)
  invFun p := ⟨(⟨apexOf w p.2, p.1⟩, p.2), rfl⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    cases p with
    | mk p hp => cases p with
      | mk v j => cases v with
        | mk x g => dsimp only at hp; cases hp; rfl
  right_inv _ := rfl

def roseFibreEquiv (x : Rose α) :
    {p : RoseSpace w gen hrel // roseProjection w gen hrel p = x} ≃ G :=
  (presCoverRoseFibreEquiv w (projection w gen hrel) x).trans
    ((Coc w gen hrel).coverFibreEquiv (iRose w x))

/-- The sheet of an actual lifted midpoint is the initial sheet of its positive generator. -/
def midpointEquiv : roseCoverMidpoints (roseProjection w gen hrel) ≃ G × α where
  toFun p := (roseFibreEquiv w gen hrel (Rose.mid p.val.2) ⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨(((roseFibreEquiv w gen hrel (Rose.mid p.2)).symm p.1).val, p.2),
    ((roseFibreEquiv w gen hrel (Rose.mid p.2)).symm p.1).property⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    exact congrArg Subtype.val ((roseFibreEquiv w gen hrel (Rose.mid p.val.2)).symm_apply_apply
      ⟨p.val.1, p.property⟩)
  right_inv p := rfl

def generatorEquiv :
    roseCoverGeneratorEdges (roseProjection w gen hrel) (roseCovering w gen hrel) ≃ G × α :=
  (roseCoverMidpointEdgeEquiv (roseProjection w gen hrel)
    (roseCovering w gen hrel)).symm.trans (midpointEquiv w gen hrel)

theorem generatorEquiv_midpoint (p : roseCoverMidpoints (roseProjection w gen hrel)) :
    generatorEquiv w gen hrel
      (roseCoverMidpointEdge (roseProjection w gen hrel) (roseCovering w gen hrel) p) =
        (p.val.1.val.val.sheet, p.val.2) := by
  change midpointEquiv w gen hrel
    ((roseCoverMidpointEdgeEquiv _ _).symm ((roseCoverMidpointEdgeEquiv _ _) p)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The genuine lifted cylinder collapse preserves the cocycle sheet. -/
theorem cylinderCollapse_sheet (p : ({p : Space w gen hrel //
  projection w gen hrel p ∈ coneAdjBaseSet (S := circSet w)})) :
    (cylinderCoverCollapse w (cylinderCovering w gen hrel) p).val.sheet = p.val.sheet := by
  let r := cylinderCoverCollapse w (cylinderCovering w gen hrel) p
  have hle  := (cylinderCovering w gen hrel).le_upTransform
    (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w)) p
  have he := hle.2
  have hp := coneAdjCoverBaseEnd_spec (projection w gen hrel) p
  have hr := coneAdjCoverBaseEnd_spec (projection w gen hrel) r
  change p.val.sheet * (Coc w gen hrel).val p.val.point r.val.point = r.val.sheet at he
  change ConeAdj.inc (cylinderProjection w gen hrel p) = p.val.point at hp
  change ConeAdj.inc (cylinderProjection w gen hrel r) = r.val.point at hr
  have hr2 : cylinderProjection w gen hrel r =
      cylCollapse (aHom w) (cylinderProjection w gen hrel p) :=
    cylinderCoverCollapse_projection w (cylinderCovering w gen hrel) p
  rw [← hp, ← hr, hr2] at he
  change p.val.sheet * roseVal gen
    (cylRetr (aHom w) (cylinderProjection w gen hrel p))
    (cylRetr (aHom w) (cylCollapse (aHom w) (cylinderProjection w gen hrel p))) =
      r.val.sheet at he
  simpa only [cylCollapse, cylRetr, cylIn, Sum.elim_inl, id_eq, roseVal_self, mul_one] using he.symm

/-- The actual cone trivialisation determines every lifted circle sheet. -/
theorem circleInclusion_sheet (p : PresCoverRelator w (projection w gen hrel))
    (x : RelatorCircle w p.val.2) :
    (presCoverCircleInclusion w (projection w gen hrel) (covering w gen hrel) p x).sheet =
      p.val.1.sheet * (trivFun w gen p.val.2 (cylOuter (aHom w) x.val))⁻¹ := by
  have hle := (presCoverCircleInclusion_lt_apex w (projection w gen hrel)
    (covering w gen hrel) p x).le
  have he := hle.2
  have hx := presCoverConeCircleOrderIso_symm_projection w (projection w gen hrel)
    (covering w gen hrel) p.val.1 p.val.2 p.property x
  change (presCoverCircleInclusion w (projection w gen hrel) (covering w gen hrel) p x).point =
    iCirc w x.val at hx
  have hp : p.val.1.point = apexOf w p.val.2 := p.property
  rw [hx, hp] at he
  change _ * trivFun w gen p.val.2 (cylOuter (aHom w) x.val) = p.val.1.sheet at he
  rw [← he]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Actual midpoint sheet equals the signed-letter Fox prefix, including inverse letters. -/
theorem relatorLetterMidpoint_sheet (p : PresCoverRelator w (projection w gen hrel))
    (k : Fin (w p.val.2).length) :
    generatorEquiv w gen hrel
      (roseCoverMidpointEdge (roseProjection w gen hrel) (roseCovering w gen hrel)
        (presCoverRelatorLetterMidpoint w (projection w gen hrel) (covering w gen hrel) p k)) =
      (p.val.1.sheet * prefixVal w gen p.val.2 k.val *
        (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹),
        ((w p.val.2)[k.val]).1) := by
  rw [generatorEquiv_midpoint]
  refine Prod.ext ?_ rfl
  change (cylinderCoverCollapse w (cylinderCovering w gen hrel)
    (presCoverCircleCylinderInclusion w (projection w gen hrel) (covering w gen hrel) p
      (relatorCirclePoint w p.val.2 k CPos.cmid))).val.sheet = _
  rw [cylinderCollapse_sheet]
  change (presCoverCircleInclusion w (projection w gen hrel) (covering w gen hrel) p
    (relatorCirclePoint w p.val.2 k CPos.cmid)).sheet = _
  rw [circleInclusion_sheet]
  have ha := aFun_pt_cedgL_of_get w (List.getElem?_eq_getElem k.isLt)
  change p.val.1.sheet *
    ((roseVal gen Rose.base (aFun w (TCirc.pt w p.val.2 k.val CPos.cedgL)))⁻¹ *
      (prefixVal w gen p.val.2 k.val)⁻¹)⁻¹ = _
  rw [ha]
  cases hb : ((w p.val.2)[k.val]).2 <;>
    simp [roseVal, mul_inv_rev, mul_assoc]

/-- All coordinate changes are linear equivalences of finitely supported chains. -/
def relatorCoordinates :
    (PresCoverRelator w (projection w gen hrel) →₀ ℤ) ≃ₗ[ℤ] ((G × J) →₀ ℤ) :=
  Finsupp.domLCongr (relatorEquiv w gen hrel)

def generatorCoordinates :
    (roseCoverGeneratorEdges (roseProjection w gen hrel) (roseCovering w gen hrel) →₀ ℤ)
      ≃ₗ[ℤ] ((G × α) →₀ ℤ) := Finsupp.domLCongr (generatorEquiv w gen hrel)

theorem relatorCoordinates_single (p : PresCoverRelator w (projection w gen hrel)) (n : ℤ) :
    relatorCoordinates w gen hrel (Finsupp.single p n) =
      Finsupp.single (p.val.1.sheet, p.val.2) n :=
  Finsupp.domLCongr_single _ _ _

theorem generatorCoordinates_single
    (p : roseCoverGeneratorEdges (roseProjection w gen hrel) (roseCovering w gen hrel)) (n : ℤ) :
    generatorCoordinates w gen hrel (Finsupp.single p n) =
      Finsupp.single (generatorEquiv w gen hrel p) n :=
  Finsupp.domLCongr_single _ _ _

end FiniteChains.PresModel.PresCocycleCover

namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J : Type u} [DecidableEq α] (w : J → List (α × Bool))
  (N : Subgroup (FreeGroup α)) [N.Normal]

omit [DecidableEq α] in
theorem quotient_wordVal (l : List (α × Bool)) :
    wordVal (qof N) l = (QuotientGroup.mk (FreeGroup.mk l) : FreeGroup α ⧸ N) := by
  have h : FreeGroup.lift (qof N) = QuotientGroup.mk' N := by
    apply FreeGroup.ext_hom
    intro i
    simp [qof]
  exact DFunLike.congr_fun h (FreeGroup.mk l)

variable (hword : ∀ j, FreeGroup.mk (w j) ∈ N)

include hword in
omit [DecidableEq α] in
theorem quotient_relators_close (j : J) : wordVal (qof N) (w j) = 1 := by
  rw [quotient_wordVal]
  simp_all

abbrev QuotientCover := Space w (qof N) (quotient_relators_close w N hword)
abbrev quotientProjection := projection w (qof N) (quotient_relators_close w N hword)
abbrev quotientCovering := covering w (qof N) (quotient_relators_close w N hword)

/-- The actual geometric attaching boundary is exactly the finitely supported Fox boundary. -/
theorem quotient_relator_boundary_coordinates
    (c : PresCoverRelator w (quotientProjection w N hword) →₀ ℤ) :
    fsCoords N α
      (generatorCoordinates w (qof N) (quotient_relators_close w N hword)
        (presCoverRelatorGeneratorBoundary w (quotientProjection w N hword)
          (quotientCovering w N hword) c)) =
      coverSecondBoundary N (fun j => FreeGroup.mk (w j))
        (fsCoords N J (relatorCoordinates w (qof N)
          (quotient_relators_close w N hword) c)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n =>
    have hone : fsCoords N α
        (generatorCoordinates w (qof N) (quotient_relators_close w N hword)
          (presCoverRelatorGeneratorBoundary w (quotientProjection w N hword)
            (quotientCovering w N hword) (Finsupp.single p 1))) =
        coverSecondBoundary N (fun j => FreeGroup.mk (w j))
          (fsCoords N J (relatorCoordinates w (qof N)
            (quotient_relators_close w N hword) (Finsupp.single p 1))) := by
      rw [presCoverRelatorGeneratorBoundary_single]
      simp only [map_sum, map_smul, generatorCoordinates_single, relatorCoordinates_single,
        relatorLetterMidpoint_sheet, fsCoords_single]
      rw [coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply,
        coe_coverFoxGradient, foxVec, smul_eq_mul]
      rw [coverFox_mk_prefix_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hp : prefixVal w (qof N) p.val.2 k.val =
          (QuotientGroup.mk (FreeGroup.mk ((w p.val.2).take k.val))) :=
        quotient_wordVal N _
      rw [hp]
      by_cases hi : i = ((w p.val.2)[k.val]).1
      · cases hb : ((w p.val.2)[k.val]).2 <;>
          simp [hi, qof, MonoidAlgebra.single_mul_single, ← mul_assoc]
      · simp_all
    have hs : Finsupp.single p n = n • Finsupp.single p 1 := by simp
    rw [hs]
    simpa only [map_smul, map_zsmul] using congrArg (fun z => n • z) hone

/-- Injectivity of the actual Fox boundary annihilates actual strict cover two-cycles. -/
theorem quotient_two_cycle_zero (hpos : ∀ j, 0 < (w j).length)
    (hinj : Function.Injective (coverSecondBoundary N (fun j => FreeGroup.mk (w j))))
    (c : StrictOrdTri (QuotientCover w N hword) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx (QuotientCover w N hword)) c = 0) : c = 0 := by
  let r := presCoverRelatorChain w (quotientProjection w N hword)
    (quotientCovering w N hword) hpos c
  have hr  :=
    (presCoverCollapsedRelatorBoundary_eq_zero_iff_generator w
      (quotientProjection w N hword) (quotientCovering w N hword) r).mp
      (presCover_cycle_collapsed_relator_boundary_zero w (quotientProjection w N hword)
        (quotientCovering w N hword) hpos c hc)
  have hz : fsCoords N J (relatorCoordinates w (qof N)
      (quotient_relators_close w N hword) r) = 0 := by
    apply hinj
    rw [← quotient_relator_boundary_coordinates, hr, map_zero, map_zero, map_zero]
  have hr0 : r = 0 := by
    apply (relatorCoordinates w (qof N) (quotient_relators_close w N hword)).injective
    apply (fsCoords N J).injective
    rw [map_zero, map_zero]
    exact hz
  exact presCoverRelatorChain_cycle_injective w (quotientProjection w N hword)
    (quotientCovering w N hword) hpos c 0 hc (map_zero _) (by
      rw [map_zero]
      exact hr0)

end FiniteChains.PresModel.PresCocycleCover

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (N : Subgroup (FreeGroup α)) [N.Normal] (hword : ∀ j, FreeGroup.mk (w j) ∈ N)

theorem quotient_monodromy_alphaFree :
    ((Coc w (qof N) (quotient_relators_close w N hword)).monodromy (ptBase w)).comp
      (alphaFree w) = QuotientGroup.mk' N := by
  apply FreeGroup.ext_hom
  intro i
  erw [MonoidHom.comp_apply, alphaFree_of]


theorem quotient_isConnected (hpos : ∀ j, 0 < (w j).length) :
    IsConnected (orderCx (QuotientCover w N hword)) :=
  (Coc w (qof N) (quotient_relators_close w N hword)).cover_isConnected (ptBase w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
    (by
      intro g
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N g
      exact ⟨alphaFree w x, (DFunLike.congr_fun
        (quotient_monodromy_alphaFree w N hword) x).trans hx⟩)

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
  (hpos : ∀ j, 0 < (w j).length) (H : Subgroup (PresGroup ρ)) [H.Normal]

abbrev subgroupPreimage : Subgroup (FreeGroup α) := H.comap (QuotientGroup.mk' (relSub ρ))

include hw in
omit [H.Normal] in
theorem subgroupPreimage_contains_relators (j : J) :
    FreeGroup.mk (w j) ∈ subgroupPreimage ρ H := by
  change (QuotientGroup.mk (FreeGroup.mk (w j))) ∈ H
  erw [hw j, (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Set.mem_range_self j))]
  exact H.one_mem

abbrev SubgroupCover := QuotientCover w (subgroupPreimage ρ H)
  (subgroupPreimage_contains_relators w ρ hw H)
abbrev subgroupCoc := Coc w (qof (subgroupPreimage ρ H))
  (quotient_relators_close w (subgroupPreimage ρ H)
    (subgroupPreimage_contains_relators w ρ hw H))

include hpos in
/-- Reading identifies the actual monodromy kernel with the specified original subgroup. -/
theorem subgroup_monodromy_kernel_iff (z : Pi1 (orderCx (PresPos w)) (ptBase w)) :
    (subgroupCoc w ρ hw H).monodromy (ptBase w) z = 1 ↔ readingPresW ρ w hw z ∈ H := by
  obtain ⟨g, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  induction g using QuotientGroup.induction_on with
  | _ x =>
    rw [readingPresW_alphaHomW]
    change (subgroupCoc w ρ hw H).monodromy (ptBase w) (alphaFree w x) = 1 ↔ _
    rw [show (subgroupCoc w ρ hw H).monodromy (ptBase w) (alphaFree w x) =
        QuotientGroup.mk x from DFunLike.congr_fun (quotient_monodromy_alphaFree w
          (subgroupPreimage ρ H) (subgroupPreimage_contains_relators w ρ hw H)) x]
    exact QuotientGroup.eq_one_iff x

def subgroupKernelHom : ((subgroupCoc w ρ hw H).monodromy (ptBase w)).ker →* H :=
  ((readingPresW ρ w hw).comp
    ((subgroupCoc w ρ hw H).monodromy (ptBase w)).ker.subtype).codRestrict H (by
      intro z
      exact (subgroup_monodromy_kernel_iff w ρ hw hpos H z.val).mp z.property)


/-- Fundamental group of the genuine covering, with its original subgroup marking. -/
def subgroupCoverPi1Equiv :
    Pi1 (orderCx (SubgroupCover w ρ hw H)) ((subgroupCoc w ρ hw H).coverBase (ptBase w)) ≃* H :=
  ((subgroupCoc w ρ hw H).coverPi1KernelEquiv (ptBase w)).trans
    (MulEquiv.ofBijective (subgroupKernelHom w ρ hw hpos H)
      (by
        constructor
        · intro z t he
          apply Subtype.ext
          exact readingPresW_injective w ρ hw hpos (congrArg Subtype.val he)
        · intro g
          let z := alphaHomW ρ w hw g.val
          have hz  :=
            (subgroup_monodromy_kernel_iff w ρ hw hpos H z).mpr (by
              rw [show readingPresW ρ w hw z = g.val from readingPresW_alphaHomW ρ w hw g.val]
              exact g.property)
          refine ⟨⟨z, hz⟩, ?_⟩
          apply Subtype.ext
          exact readingPresW_alphaHomW ρ w hw g.val))


include hpos in
/-- Perfectness supplies genuine strict one-cycle fillings, with no finite-cell restriction. -/
theorem subgroupCover_one_cycle_filling (hperf : ⁅H, H⁆ = H)
    (c : StrictOrdEdge (SubgroupCover w ρ hw H) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (SubgroupCover w ρ hw H)) c = 0) :
    ∃ d : StrictOrdTri (SubgroupCover w ρ hw H) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (SubgroupCover w ρ hw H)) d = c := by
  let C := SubgroupCover w ρ hw H
  have hweak : Comb.bdry1 (orderCx C) (chain1 (strictOrderIncl C) c) = 0 := by
    erw [bdry1_chain1, hc, map_zero]
  obtain ⟨d, hd⟩ := oneCycle_filling_of_perfect_pi1 (orderCx C)
    ((subgroupCoc w ρ hw H).coverBase (ptBase w))
    (quotient_isConnected w (subgroupPreimage ρ H)
      (subgroupPreimage_contains_relators w ρ hw H) hpos)
    (by
      have hH : commutator H = ⊤ := by
        apply top_unique
        intro g _
        have hg : g.val ∈ (commutator H).map H.subtype := by
          erw [H.map_subtype_commutator, hperf]
          exact g.property
        obtain ⟨x, hx, he⟩ := hg
        exact (Subtype.ext he) ▸ hx
      let e := (subgroupCoverPi1Equiv w ρ hw hpos H).symm
      have hr : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
      have he := map_commutator_eq H e.toMonoidHom
      erw [hH, Subgroup.map_top_of_surjective _ e.surjective, hr, ← commutator_def] at he
      exact he.symm) _ hweak
  exact ⟨normalizeOrdChain2 d, by
    erw [bdry2_normalizeOrdChain2, hd]
    exact normalizeOrdChain1_inclusion c⟩

variable [DecidableEq α]

include hpos in
/-- The specified perfect subgroup and finite-support Fox tests give a genuinely acyclic poset cover. -/
theorem subgroupCover_isAcyclic
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v H)
    (hperf : ⁅H, H⁆ = H) : IsAcyclic (strictOrderCx (SubgroupCover w ρ hw H)) := by
  let N := subgroupPreimage ρ H
  have hR : relSub ρ ≤ N := by
    intro r hr
    change (QuotientGroup.mk r) ∈ H
    erw [(QuotientGroup.eq_one_iff r).mpr hr]
    exact H.one_mem
  have hNeq : presSub ρ N = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hinj : Function.Injective (coverSecondBoundary N ρ) := by
    apply fs_injective_boundary_of_foxSat ρ N hR
    intro v
    erw [hNeq]
    exact hsat v
  have hwfun  := funext hw
  have hi : Function.Injective (coverSecondBoundary N (fun j => FreeGroup.mk (w j))) := by
    erw [hwfun]
    exact hinj
  refine ⟨?_, subgroupCover_one_cycle_filling w ρ hw hpos H hperf, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    exact quotient_two_cycle_zero w N (subgroupPreimage_contains_relators w ρ hw H) hpos hi
  · exact strict_order_zeroCycle_filling_of_connected (P := SubgroupCover w ρ hw H)
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))
      (quotient_isConnected w N (subgroupPreimage_contains_relators w ρ hw H) hpos)

end FiniteChains.PresModel.PresCocycleCover
end

namespace FiniteChains.PresModel
open Comb PresCocycleCover CategoryTheory
variable {α J : Type} [DecidableEq α] (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

def coveredPresentationTwoComplex : Whitehead.TwoComplex := by
  letI : Nonempty (PresPos w) := ⟨ptBase w⟩
  letI : (nerve (PresPos w)).HasDimensionLE 2 :=
    orderNerve_hasDimensionLE (presPosDimension w) (presPosDimension_strictMono w) 2
      (presPosDimension_le_two w)
  exact orderNerveTwoComplex (PresPos w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))


/-- The compactness necessity argument produces an actual connected regular
topological cover with vanishing genuine singular homology. -/

theorem coveredPresentation_hasAcyclicRegularCover_of_presChains
    (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (hchains : ∀ n, Nonempty (PresChainFS ρ n)) :
    Whitehead.HasAcyclicRegularCover (coveredPresentationTwoComplex w hpos) :=
  (by
    obtain ⟨H, hn, _, hs, hp⟩ := fs_exists_perfect_normal_of_cellChains ρ (hasCellChainsLift_of_presChainsFS ρ hchains)
    letI := hn
    exact (by
      letI : Nonempty (PresPos w) := ⟨ptBase w⟩
      letI : (nerve (PresPos w)).HasDimensionLE 2 :=
        orderNerve_hasDimensionLE (presPosDimension w) (presPosDimension_strictMono w) 2
          (presPosDimension_le_two w)
      let N := subgroupPreimage ρ H
      let hr := subgroupPreimage_contains_relators w ρ hw H
      exact (quotientCovering w N hr).hasAcyclicRegularCover
        (quotient_isConnected w N hr hpos)
        (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
        ((subgroupCoc w ρ hw H).cover_deck_transitive)
        (subgroupCover_isAcyclic w ρ hw hpos H hs hp)))

end FiniteChains.PresModel

section
open scoped Classical
namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.PresModel

theorem hasAcyclicRegularCover_of_chains (K : TwoComplex)
    (h : ∀ n : ℕ, 1 ≤ n → HasChain K n false) : HasAcyclicRegularCover K := by
  let T := originalGraphTree K
  let w := fixedCanonicalWords K T
  let hpos  :=
    fun j => List.length_pos_iff.mpr (fixedCanonicalWords_ne_nil K T j)
  let L := coveredPresentationTwoComplex w hpos
  have hL  :=
    coveredPresentation_hasAcyclicRegularCover_of_presChains w hpos
      (fixedRelators K T) (fixedCanonicalWords_mk K T)
      (fixedPresChainsFS_of_original_chains K T h)
  let e  := fixedCanonicalRealizationEquiv K T
  exact hasAcyclicRegularCover_of_homotopyEquiv K L e hL

end Whitehead

namespace FiniteChains.RelativeAttachment
open Topology

variable {J K X E : Type} [TopologicalSpace X]
  [NormedAddCommGroup E]
  (r : BoundaryFamily K E → X) (e : J ≃ K)
  (q : ∀ _ : J, C(ClosedUnitBall E, ClosedUnitBall E))
  (b : ∀ _ : J, C(UnitBoundary E, UnitBoundary E))
  (hb : ∀ j z, q j (unitBoundaryInclusion E z) = unitBoundaryInclusion E (b j z))
  (hq : ∀ j, IsQuotientMap (q j))
  (hint : ∀ j x, ‖(q j x).val‖ < 1 ↔ ‖x.val‖ < 1)
  (hinj : ∀ j, Set.InjOn (q j) {x | ‖x.val‖ < 1})

def reparametrizedAttaching (a : BoundaryFamily J E) : X :=
  r ⟨e a.1, b a.1 a.2⟩

def reparametrizedDiskFamily : C(DiskFamily J E, DiskFamily K E) where
  toFun d := ⟨e d.1, q d.1 d.2⟩
  continuous_toFun := continuous_sigma (fun j =>
    (show Continuous (Sigma.mk (β := fun _ : K => ClosedUnitBall E) (e j)) from
      continuous_sigmaMk).comp (q j).continuous)

include hint in
theorem reparametrizedDiskFamily_boundary_iff (d : DiskFamily J E) :
    reparametrizedDiskFamily e q d ∈ Set.range (boundaryFamilyInclusion K E) ↔
      d ∈ Set.range (boundaryFamilyInclusion J E) := by
  rw [boundaryFamilyInclusion_range, boundaryFamilyInclusion_range]
  change ‖(q d.1 d.2).val‖ = 1 ↔ ‖d.2.val‖ = 1
  grind



def reparametrizedOldAndDisks : X ⊕ DiskFamily J E → X ⊕ DiskFamily K E :=
  Sum.map id (reparametrizedDiskFamily e q)

include hq in
theorem reparametrizedOldAndDisks_isQuotientMap :
    IsQuotientMap (reparametrizedOldAndDisks (X := X) e q) := by
  have hQ := (show IsQuotientMap (reparametrizedDiskFamily e q) by
    apply isQuotientMap_iff_isClosed.mpr
    constructor
    · rintro ⟨k, y⟩
      obtain ⟨j, rfl⟩ := e.surjective k
      obtain ⟨x, rfl⟩ := (hq j).surjective y
      exact ⟨⟨j, x⟩, rfl⟩
    · intro S
      constructor
      · intro hS
        exact hS.preimage (reparametrizedDiskFamily e q).continuous
      · intro hS
        apply isClosed_sigma_iff.mpr
        intro k
        obtain ⟨j, rfl⟩ := e.surjective k
        apply (hq j).isClosed_preimage.mp
        exact (isClosed_sigma_iff.mp hS) j)
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · rintro (x | d)
    · exact ⟨Sum.inl x, rfl⟩
    · obtain ⟨d', rfl⟩ := hQ.surjective d
      exact ⟨Sum.inr d', rfl⟩
  · intro S
    rw [isClosed_sum_iff, isClosed_sum_iff]
    exact and_congr Iff.rfl hQ.isClosed_preimage.symm

def reparametrizedDiskEvaluation : C(DiskFamily J E, DiskAttachment r) :=
  (⟨cell r (boundaryFamilyInclusion K E), cell_continuous r _⟩ :
    C(DiskFamily K E, DiskAttachment r)).comp
    (reparametrizedDiskFamily e q)

include hint in
theorem reparametrizedDiskEvaluation_separation (d : DiskFamily J E) :
    reparametrizedDiskEvaluation r e q d ∈ Set.range (old r (boundaryFamilyInclusion K E)) ↔
      d ∈ Set.range (boundaryFamilyInclusion J E) := by
  rw [← reparametrizedDiskFamily_boundary_iff e q hint d]
  let d' := reparametrizedDiskFamily e q d
  change cell r (boundaryFamilyInclusion K E) d' ∈ Set.range (old r _) ↔
    d' ∈ Set.range (boundaryFamilyInclusion K E)
  constructor
  · rintro ⟨x, hx⟩
    by_contra hd
    rw [cell_of_not_mem r _ d' hd] at hx
    exact Sum.inl_ne_inr hx
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact ⟨r a, (cell_boundary r _
      (boundaryFamilyInclusion_isClosedEmbedding K E).injective a).symm⟩

def diskAttachmentQuotientReparametrization :
    DiskAttachment (reparametrizedAttaching r e b) ≃ₜ DiskAttachment r := by
  let f : C(X, DiskAttachment r) := ⟨old r (boundaryFamilyInclusion K E), old_continuous r _⟩
  let g := reparametrizedDiskEvaluation r e q
  have hbd : ∀ a, f (reparametrizedAttaching r e b a) =
      g (boundaryFamilyInclusion J E a) := by
    rintro ⟨j, z⟩
    change old r (boundaryFamilyInclusion K E) (r ⟨e j, b j z⟩) =
      cell r (boundaryFamilyInclusion K E) ⟨e j, q j (unitBoundaryInclusion E z)⟩
    rw [hb]
    exact (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding K E).injective
      ⟨e j, b j z⟩).symm
  have hnew : ∀ d d', d ∉ Set.range (boundaryFamilyInclusion J E) →
      d' ∉ Set.range (boundaryFamilyInclusion J E) → g d = g d' → d = d' := by
    intro d d' hd hd' he
    have hdq : reparametrizedDiskFamily e q d ∉ Set.range (boundaryFamilyInclusion K E) :=
      fun h => hd ((reparametrizedDiskFamily_boundary_iff e q hint d).mp h)
    have hdq' : reparametrizedDiskFamily e q d' ∉ Set.range (boundaryFamilyInclusion K E) :=
      fun h => hd' ((reparametrizedDiskFamily_boundary_iff e q hint d').mp h)
    change cell r _ (reparametrizedDiskFamily e q d) =
      cell r _ (reparametrizedDiskFamily e q d') at he
    rw [cell_of_not_mem r _ _ hdq, cell_of_not_mem r _ _ hdq'] at he
    exact (by
      rcases d with ⟨j, x⟩
      rcases d' with ⟨k, y⟩
      have hjk : j = k := e.injective (congrArg Sigma.fst (congrArg Subtype.val (Sum.inr.inj he)))
      subst k
      have hxy  := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val (Sum.inr.inj he))).2
      have hx  := lt_of_le_of_ne x.property
        (fun h => hd ((boundaryFamilyInclusion_range J E _).mpr h))
      have hy  := lt_of_le_of_ne y.property
        (fun h => hd' ((boundaryFamilyInclusion_range J E _).mpr h))
      exact congrArg (Sigma.mk (β := fun _ : J => ClosedUnitBall E) j) (hinj j hx hy hxy))
  have hq₀ : IsQuotientMap (quotientMap r (boundaryFamilyInclusion K E)) :=
    ⟨⟨rfl⟩, quotientMap_surjective r _⟩
  have hcomp : quotientMap r (boundaryFamilyInclusion K E) ∘
      reparametrizedOldAndDisks (X := X) e q = Sum.elim f g := by
    funext x
    cases x <;> rfl
  have hq' : IsQuotientMap (Sum.elim f g) := by
    rw [← hcomp]
    exact hq₀.comp (reparametrizedOldAndDisks_isQuotientMap (X := X) e q hq)
  exact attachmentQuotientHomeomorph (reparametrizedAttaching r e b)
    (boundaryFamilyInclusion J E) f g hbd (old_injective r _)
    (reparametrizedDiskEvaluation_separation r e q hint) hnew hq'

@[simp] theorem diskAttachmentQuotientReparametrization_old (x : X) :
    diskAttachmentQuotientReparametrization r e q b hb hq hint hinj
      (old (reparametrizedAttaching r e b) (boundaryFamilyInclusion J E) x) =
        old r (boundaryFamilyInclusion K E) x := rfl

@[simp] theorem diskAttachmentQuotientReparametrization_cell (d : DiskFamily J E) :
    diskAttachmentQuotientReparametrization r e q b hb hq hint hinj
      (cell (reparametrizedAttaching r e b) (boundaryFamilyInclusion J E) d) =
        cell r (boundaryFamilyInclusion K E) (reparametrizedDiskFamily e q d) := by
  unfold diskAttachmentQuotientReparametrization
  exact attachmentQuotientHomeomorph_cell ..

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
namespace FiniteChains.Comb
universe u

namespace RelativeCellChain
variable {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelativeCellChain c n)
  {K : Complex2.{u}} (p : Hom (c 0) K)

theorem descInc_freshLoopOrFace (i : ℕ) (h : FreshLoopOrFace (R.inc i)) :
    FreshLoopOrFace (R.descInc p i) := by
  rcases h with ⟨e, hloop, he⟩ | ⟨f, hf⟩
  · left
    cases i with
    | zero =>
        have hoff : ∀ d, (inclFrom c R.inc 1).onE d ≠ e := by
          intro d hd
          exact he ⟨d, hd⟩
        let w : OffE (inclFrom c R.inc 1) := ⟨e, hoff⟩
        refine ⟨Sum.inr w, ?_, ?_⟩
        · change pushV p (inclFrom c R.inc 1) ((c 1).src e) =
            pushV p (inclFrom c R.inc 1) ((c 1).tgt e)
          exact congrArg (pushV p (inclFrom c R.inc 1)) hloop
        · rintro ⟨d, hd⟩
          exact Sum.inl_ne_inr hd
    | succ i =>
        have hoff : ∀ d, (inclFrom c R.inc (i + 2)).onE d ≠ e := by
          intro d hd
          exact he ⟨(inclFrom c R.inc (i + 1)).onE d, hd⟩
        let w : OffE (inclFrom c R.inc (i + 2)) := ⟨e, hoff⟩
        refine ⟨Sum.inr w, ?_, ?_⟩
        · change pushV p (inclFrom c R.inc (i + 2)) ((c (i + 2)).src e) =
            pushV p (inclFrom c R.inc (i + 2)) ((c (i + 2)).tgt e)
          exact congrArg (pushV p (inclFrom c R.inc (i + 2))) hloop
        · rintro ⟨d, hd⟩
          cases d with
          | inl d => exact Sum.inl_ne_inr hd
          | inr d =>
              exact he ⟨d.val, pushE_eq_inr_imp p _ (R.inclE (i + 2))
                ((R.inc (i + 1)).onE d.val) w hd⟩
  · right
    cases i with
    | zero =>
        have hoff : ∀ d, (inclFrom c R.inc 1).onF d ≠ f := by
          intro d hd
          exact hf ⟨d, hd⟩
        refine ⟨Sum.inr ⟨f, hoff⟩, ?_⟩
        rintro ⟨d, hd⟩
        exact Sum.inl_ne_inr hd
    | succ i =>
        have hoff : ∀ d, (inclFrom c R.inc (i + 2)).onF d ≠ f := by
          intro d hd
          exact hf ⟨(inclFrom c R.inc (i + 1)).onF d, hd⟩
        let w : OffF (inclFrom c R.inc (i + 2)) := ⟨f, hoff⟩
        refine ⟨Sum.inr w, ?_⟩
        rintro ⟨d, hd⟩
        cases d with
        | inl d => exact Sum.inl_ne_inr hd
        | inr d =>
            exact hf ⟨d.val, pushF_eq_inr_imp p _ (R.inclF (i + 2))
              ((R.inc (i + 1)).onF d.val) w hd⟩

end RelativeCellChain

namespace RelativeTreeAmbientChain
open SpanningTree RelativeNormalForm
variable {D : Complex2} (T : SpanningTree D) {n : ℕ}
  (c : AmbientChain (treeRel T) n)


end RelativeTreeAmbientChain

theorem regularCoverChain_freshLoopOrFace {D K : Complex2}
    (T : SpanningTree D) (hD : IsAcyclic D) (p : Hom D K)
    (n i : ℕ) (hi : i < n + 1) :
    FreshLoopOrFace (regularCoverChainInclusion T hD p n i) :=
  (acyclicRelativeCellChain T hD n).descInc_freshLoopOrFace p i
    (by
      cases i with
      | zero =>
          left
          refine ⟨Sum.inr (RelativeNormalForm.actualAmbientChain (SpanningTree.treeRel T)
        (SpanningTree.expMatrix_bijective_of_acyclic T hD) n).fresh, rfl, ?_⟩
          rintro ⟨d, hd⟩
          exact Sum.inl_ne_inr hd
      | succ i =>
          rcases (RelativeNormalForm.actualAmbientChain (SpanningTree.treeRel T)
        (SpanningTree.expMatrix_bijective_of_acyclic T hD) n).chain_proper (i + 1) hi with ⟨a, ha⟩ | ⟨f, hf⟩
          · exact False.elim (ha ⟨a, rfl⟩)
          · exact Or.inr ⟨f, hf⟩)

end FiniteChains.Comb
end

namespace FiniteChains.PresModel.PresWordEmbedding
open RelativeAttachment ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
    (h : PresWordEmbedding w v) (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

def classicalDiskExtension :
    Whitehead.DiskExtensionModel (ClassicalPresWordDisks w hw) (ClassicalPresWordDisks v hv) :=
  DiskPresentationExtension.extensionModel h.gen h.cell
    (classicalPresWordAttaching w hw) (classicalPresWordAttaching v hv)
    (h.classicalPresWordAttaching_natural hw hv)

theorem classicalDiskExtension_map : (h.classicalDiskExtension hw hv).map =
    h.classicalWordDiskMap hw hv := rfl

theorem classicalDiskExtension_nonempty_of_generator (b : B) (hb : b ∉ Set.range h.gen) :
    Nonempty (h.classicalDiskExtension hw hv).oneCells := ⟨⟨b, hb⟩⟩

theorem classicalDiskExtension_nonempty_of_relator (k : K) (hk : k ∉ Set.range h.cell) :
    Nonempty (h.classicalDiskExtension hw hv).twoCells := ⟨⟨k, hk⟩⟩

theorem classicalDiskExtension_finite [Finite B] [Finite K] :
    Finite (h.classicalDiskExtension hw hv).oneCells ∧
      Finite (h.classicalDiskExtension hw hv).twoCells :=
  ⟨inferInstanceAs (Finite {b : B // b ∉ Set.range h.gen}),
    inferInstanceAs (Finite {k : K // k ∉ Set.range h.cell})⟩

end FiniteChains.PresModel.PresWordEmbedding

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Classical

variable {α J : ℕ → Type}

def successiveEmbedding (f : ∀ i, α i ↪ α (i + 1)) (i j : ℕ) (hij : i ≤ j) : α i ↪ α j :=
  Nat.leRecOn (C := fun k => α i ↪ α k) hij
    (fun {k} e => e.trans (f k)) (Function.Embedding.refl _)

variable [∀ i, DecidableEq (α i)]
  (w : ∀ i, J i → List (α i × Bool))
  (e : ∀ i, PresWordEmbedding (w i) (w (i + 1)))
  (ρ : ∀ i, J i → FreeGroup (α i))
  (hw : ∀ i j, FreeGroup.mk (w i j) = ρ i j)
  (hpos : ∀ i j, 0 < (w i j).length)

/-- This produces the challenge's original-cell-preserving HasChain on
the supplied K, including a genuinely finite ambient complex when asked. -/
theorem original_hasChain_of_word_embeddings (K : Whitehead.TwoComplex)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (w 0) (fun j => List.length_pos_iff.mp (hpos 0 j))) K)
    (n : ℕ)
    (hp : ∀ i, i < n → (∃ a : α (i + 1), a ∉ Set.range (e i).gen) ∨
      ∃ j : J (i + 1), j ∉ Set.range (e i).cell)
    (hz : ∀ i, i < n → ∀ c : PresGroup (ρ i) × J i →₀ ℤ,
      Comb.bdry2 (univCover (ρ i)) c = 0 →
      Finsupp.mapDomain (Prod.map ((e i).groupHom (ρ i) (ρ (i + 1)) (hw i) (hw (i + 1)))
        (e i).cell) c = 0)
    (finite : Bool)
    (hfin : finite = true → Whitehead.FiniteCells K ∧ Finite (α n) ∧ Finite (J n)) :
    Whitehead.HasChain K n finite := by
  let hne i j := List.length_pos_iff.mp (hpos i j)
  let M i := (e i).classicalDiskExtension (hne i) (hne (i + 1))
  apply Whitehead.hasChain_of_diskExtensionModels M K e₀ n ?_ ?_ finite ?_
  · intro i hi
    rcases hp i hi with ⟨a, ha⟩ | ⟨j, hj⟩
    · exact Or.inl ((e i).classicalDiskExtension_nonempty_of_generator
        (hne i) (hne (i + 1)) a ha)
    · exact Or.inr ((e i).classicalDiskExtension_nonempty_of_relator
        (hne i) (hne (i + 1)) j hj)
  · intro i hi
    rw [(e i).classicalDiskExtension_map]
    apply ((e i).classicalWordDiskMap_killsPi2_iff (hne i) (hne (i + 1))).mpr
    exact ((e i).killsPi2_iff_univCover (hpos i) (hpos (i + 1))
      (ρ i) (ρ (i + 1)) (hw i) (hw (i + 1))).mpr (hz i hi)
  · intro hf
    obtain ⟨hK, hA, hJ⟩ := hfin hf
    refine ⟨hK, ?_⟩
    intro i hi
    letI := hA
    letI := hJ
    letI := Finite.of_injective
      (successiveEmbedding (fun i => (e i).gen) (i + 1) n hi)
      (successiveEmbedding (fun i => (e i).gen) (i + 1) n hi).injective
    letI := Finite.of_injective
      (successiveEmbedding (fun i => (e i).cell) (i + 1) n hi)
      (successiveEmbedding (fun i => (e i).cell) (i + 1) n hi).injective
    exact (e i).classicalDiskExtension_finite (hne i) (hne (i + 1))

end FiniteChains.PresModel

namespace FiniteChains.PresChainFS
open PresModel
open scoped Classical

variable {A C : Type} {core : C → FreeGroup A} {n : ℕ} (c : PresChainFS core n)

def stageWordDisks (i : ℕ) (a : c.gen i) : Type :=
  letI := c.decGen i
  ClassicalPresWordDisks (presCanonicalWords (c.rel i) a) (presCanonicalWords_ne_nil (c.rel i) a)

instance stageWordDisks_topology (i : ℕ) (a : c.gen i) : TopologicalSpace (c.stageWordDisks i a) := by
  unfold stageWordDisks
  infer_instance

theorem hasOriginalTopologicalChain (K : Whitehead.TwoComplex) (a : c.gen 0)
    (e₀ : ContinuousMap.HomotopyEquiv (c.stageWordDisks 0 a) K)
    (hp : ∀ i, i < n → (∃ b : c.gen (i + 1), b ∉ Set.range (c.genIncl i)) ∨
      ∃ j : c.cell (i + 1), j ∉ Set.range (c.cellIncl i))
    (finite : Bool)
    (hfin : finite = true → Whitehead.FiniteCells K ∧ Finite (c.gen n) ∧ Finite (c.cell n)) :
    Whitehead.HasChain K n finite := by
  letI := c.decGen
  let f i : c.gen i ↪ c.gen (i + 1) := ⟨c.genIncl i, c.genIncl_injective i⟩
  let g i : c.cell i ↪ c.cell (i + 1) := ⟨c.cellIncl i, c.cellIncl_injective i⟩
  exact original_hasChain_of_word_embeddings
    (fun i => presCanonicalWords (c.rel i) (presentationMarkedGenerator f a i))
    (canonicalPresentationStep c.rel f g c.rel_incl a) c.rel
    (fun i => mk_presCanonicalWords (c.rel i) (presentationMarkedGenerator f a i))
    (fun i => presCanonicalWords_positive (c.rel i) (presentationMarkedGenerator f a i))
    K e₀ n hp c.zero_pi2 finite hfin

end FiniteChains.PresChainFS

section
open scoped Classical
namespace FiniteChains.Comb.TopChainFS
open SpanningTree
variable {K : Complex2} {n : ℕ} (c : TopChainFS K n)
  (T₀ : SpanningTree (c.X 0))

def stageTree (i : ℕ) : SpanningTree (c.X i) :=
  Nat.rec T₀ (fun i U =>
    (exists_extension (c.inc i) (c.conn (i + 1)) U.root U
      (c.incV i) (c.incE i)).choose) i

theorem stageTree_compatible (i : ℕ) (e : (c.X i).E) :
    (c.stageTree T₀ (i + 1)).isTree ((c.inc i).onE e) ↔
      (c.stageTree T₀ i).isTree e :=
  (exists_extension (c.inc i) (c.conn (i + 1)) (c.stageTree T₀ i).root
    (c.stageTree T₀ i) (c.incV i) (c.incE i)).choose_spec.2 e

def treePresentationTopChain : PresChainTopFS (treeRel T₀) n where
  gen i := NonTree (c.stageTree T₀ i)
  cell i := (c.X i).F
  decGen _ := inferInstance
  rel i := treeRel (c.stageTree T₀ i)
  genIncl i := nonTreeIncl (c.stageTree_compatible T₀ i)
  genIncl_injective i := nonTreeIncl_injective (c.stageTree_compatible T₀ i) (c.incE i)
  cellIncl i := (c.inc i).onF
  cellIncl_injective := c.incF
  rel_incl i := treeRel_onF (c.stageTree_compatible T₀ i)
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base j := by
    change treeRel T₀ j = FreeGroup.map id (treeRel T₀ j)
    rw [FreeGroup.map.id]
  zero_pi2 i hi := zeroPi2_presInclHom_of_zeroPi2
    (c.stageTree_compatible T₀ i) (c.incE i) (c.zero_pi2 i hi)

def treePresentationChain : PresChainFS (treeRel T₀) n :=
  (c.treePresentationTopChain T₀).toPresChainFS

theorem treePresentationChain_proper
    (hp : ∀ i, i < n → FreshLoopOrFace (c.inc i)) (i : ℕ) (hi : i < n) :
    (∃ a : (c.treePresentationChain T₀).gen (i + 1),
      a ∉ Set.range ((c.treePresentationChain T₀).genIncl i)) ∨
    ∃ f : (c.treePresentationChain T₀).cell (i + 1),
      f ∉ Set.range ((c.treePresentationChain T₀).cellIncl i) :=
  nonTree_or_face_fresh (c.stageTree_compatible T₀ i) (hp i hi)

/-- All stages and their vanishing maps are now actual relative word-disk
extensions. Only the initial topological comparison remains to instantiate. -/
theorem hasOriginalChain_of_initial_tree_comparison (X : Whitehead.TwoComplex)
    (a : NonTree T₀)
    (e₀ : ContinuousMap.HomotopyEquiv
      (PresModel.ClassicalPresWordDisks (PresModel.presCanonicalWords (treeRel T₀) a)
        (PresModel.presCanonicalWords_ne_nil (treeRel T₀) a)) X)
    (hp : ∀ i, i < n → FreshLoopOrFace (c.inc i)) :
    Whitehead.HasChain X n false :=
  (c.treePresentationChain T₀).hasOriginalTopologicalChain X a e₀
    (c.treePresentationChain_proper T₀ hp) false (by simp)

end FiniteChains.Comb.TopChainFS

namespace FiniteChains.Comb
open CategoryTheory PresModel SpanningTree
variable (P : Type) [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]
  (hP : IsConnected (orderCx P))


end FiniteChains.Comb

namespace FiniteChains.ClassicalCW
open Comb PresModel SpanningTree

/-- Reduction of the original sufficiency direction to one actual
homotopy equivalence for the initial strict order-complex tree model. -/
theorem hasChain_of_original_cover_tree_comparison (K : Whitehead.TwoComplex)
    (T₀ : SpanningTree (strictOrderCx (CanonicalPos K)))
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords (treeRel T₀) (canonicalTreeGenerator K T₀))
        (presCanonicalWords_ne_nil (treeRel T₀) (canonicalTreeGenerator K T₀)))
      (orderNerveRealization (CanonicalPos K)))
    (h : Whitehead.HasAcyclicRegularCover K) (n : ℕ) :
    Whitehead.HasChain K (n + 1) false :=
  (by
    obtain ⟨E, tE, p, hp, hs, hconn, hr, hac⟩ := (canonicalTwoComplex_hasCover K h)
    letI := tE
    letI := hconn
    obtain ⟨hcover, hregular, hconnected, hacyclic, hedge, hface⟩ :=
      TopologicalOrderCover.reconstructed_cover_conclusions p hp hs hr hac
    let proj := TopologicalOrderCover.strictProjection p hp hs
    let action := TopologicalOrderCover.strictDeckAction p hp
    obtain ⟨d, -⟩ := hcover.surjV (Classical.choice (inferInstance : Nonempty (CanonicalPos K)))
    obtain ⟨T, -⟩ := SpanningTree.exists_of_isConnected hconnected d
    let c := regularCoverTopChain T hacyclic proj hcover action hregular hedge hface n
    exact c.hasOriginalChain_of_initial_tree_comparison T₀ K (canonicalTreeGenerator K T₀) (e₀.trans (originalCanonicalTwoComplexEquiv K).symm)
      (fun i hi => regularCoverChain_freshLoopOrFace T hacyclic proj n i hi))

end FiniteChains.ClassicalCW
end

section
open scoped Classical unitInterval Topology
namespace FiniteChains.OrderTriangleDisk
open RelativeAttachment Topology

abbrev Triangle := stdSimplex ℝ (Fin 3)
abbrev Square := Fin 2 → I

def parametrization : C(Square, Triangle) where
  toFun z := ⟨![1 - (z 1 : ℝ), (z 1 : ℝ) * (1 - (z 0 : ℝ)),
      (z 1 : ℝ) * (z 0 : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (z 1).property.2
      · exact mul_nonneg (z 1).property.1 (sub_nonneg.mpr (z 0).property.2)
      · exact mul_nonneg (z 1).property.1 (z 0).property.1
    · rw [Fin.sum_univ_three]
      dsimp
      ring⟩
  continuous_toFun := by fun_prop

theorem coordinate_sum (z : Triangle) : z.val 0 + z.val 1 + z.val 2 = 1 :=
  (Fin.sum_univ_three z.val).symm.trans z.property.2

theorem remaining_nonneg (z : Triangle) : 0 ≤ 1 - z.val 0 := by
  have hs := coordinate_sum z
  linarith [z.property.1 1, z.property.1 2]

theorem remaining_zero (z : Triangle) (h : 1 - z.val 0 = 0) :
    z.val 1 = 0 ∧ z.val 2 = 0 := by
  have hs := coordinate_sum z
  constructor <;> linarith [z.property.1 1, z.property.1 2]

def sectionPoint (z : Triangle) : Square :=
  ![⟨z.val 2 / (1 - z.val 0), by
      constructor
      · exact div_nonneg (z.property.1 2) (remaining_nonneg z)
      · by_cases h : 1 - z.val 0 = 0
        · simp [h]
        · apply (div_le_one (lt_of_le_of_ne (remaining_nonneg z) (Ne.symm h))).mpr
          have hs := coordinate_sum z
          linarith [z.property.1 1]⟩,
    ⟨1 - z.val 0, remaining_nonneg z, by linarith [z.property.1 0]⟩]



theorem parametrization_isQuotientMap : IsQuotientMap parametrization :=
  parametrization.continuous.isClosedMap.isQuotientMap
    parametrization.continuous (fun z => ⟨sectionPoint z, (by
      apply Subtype.ext
      funext i
      have hs := coordinate_sum z
      by_cases h : 1 - z.val 0 = 0
      · obtain ⟨h₁, h₂⟩ := remaining_zero z h
        fin_cases i <;> simp [parametrization, sectionPoint, h, h₁, h₂]
        linarith
      · fin_cases i
        · change 1 - (1 - z.val 0) = z.val 0
          ring
        · change (1 - z.val 0) * (1 - z.val 2 / (1 - z.val 0)) = z.val 1
          rw [mul_sub, mul_one, mul_div_cancel₀ _ h]
          linarith
        · change (1 - z.val 0) * (z.val 2 / (1 - z.val 0)) = z.val 2
          exact mul_div_cancel₀ _ h)⟩)

def SquareInterior (z : Square) : Prop := ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1

theorem parametrization_positive_iff (z : Square) :
    (∀ i, 0 < (parametrization z).val i) ↔ SquareInterior z := by
  constructor
  · intro h
    have h₀ : 0 < 1 - (z 1 : ℝ) := h 0
    have h₁ : 0 < (z 1) * (1 - (z 0 : ℝ)) := h 1
    have h₂ : 0 < (z 1) * (z 0) := h 2
    have hxy  :=
      (mul_pos_iff.mp h₂).resolve_right
        (fun hneg => (not_lt_of_ge (z 1).property.1) hneg.1)
    have hy := hxy.1
    have hx := hxy.2
    have hx'  := (mul_pos_iff_of_pos_left hy).mp h₁
    intro i
    fin_cases i <;> dsimp <;> constructor <;> linarith
  · intro h i
    fin_cases i
    · exact sub_pos.mpr (h 1).2
    · exact mul_pos (h 1).1 (sub_pos.mpr (h 0).2)
    · exact mul_pos (h 1).1 (h 0).1

theorem parametrization_injective_off_collapsed_side {z w : Square}
    (hz : (z 1 : ℝ) ≠ 0) (h : parametrization z = parametrization w) : z = w := by
  have hy : (z 1) = (w 1 : ℝ) := by
    have he := congrArg (fun t : Triangle => t.val 0) h
    change 1 - (z 1) = 1 - (w 1 : ℝ) at he
    linarith
  have hx : (z 0) = (w 0 : ℝ) := by
    have he := congrArg (fun t : Triangle => t.val 2) h
    change (z 1 : ℝ) * (z 0 : ℝ) = (w 1 : ℝ) * (w 0 : ℝ) at he
    rw [← hy] at he
    exact (mul_left_cancel₀ hz) he
  funext i
  apply Subtype.ext
  fin_cases i
  · exact hx
  · exact hy

def squareBallHomeomorph : ClosedUnitBall (Fin 2 → ℝ) ≃ₜ Square where
  toFun x i := ⟨(x.val i + 1) / 2, by
    have hi : |x.val i| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.val i).trans x.property
    obtain ⟨hl, hu⟩ := abs_le.mp hi
    constructor <;> linarith⟩
  invFun z := ⟨fun i => 2 * (z i : ℝ) - 1, by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hi := (z i).property
    constructor <;> linarith [hi.1, hi.2]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp
    ring
  right_inv z := by simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by fun_prop

theorem squareBallHomeomorph_interior (x : ClosedUnitBall (Fin 2 → ℝ)) :
    SquareInterior (squareBallHomeomorph x) ↔ ‖x.val‖ < 1 := by
  rw [pi_norm_lt_iff zero_lt_one]
  constructor
  · intro h i
    have hi := h i
    rw [Real.norm_eq_abs]
    apply abs_lt.mpr
    change 0 < (x.val i + 1) / 2 ∧ (x.val i + 1) / 2 < 1 at hi
    constructor <;> linarith [hi.1, hi.2]
  · intro h i
    have hi := abs_lt.mp (by simpa using h i)
    change 0 < (x.val i + 1) / 2 ∧ (x.val i + 1) / 2 < 1
    constructor <;> linarith [hi.1, hi.2]

theorem squareBallHomeomorph_boundary (z : UnitBoundary (Fin 2 → ℝ)) :
    squareBallHomeomorph (unitBoundaryInclusion _ z) =
      (unitBoundarySquareHomeomorph z).val := rfl

def disk : C(ClosedUnitBall (Fin 2 → ℝ), Triangle) :=
  parametrization.comp squareBallHomeomorph.toContinuousMap

theorem disk_positive_iff (x : ClosedUnitBall (Fin 2 → ℝ)) :
    (∀ i, 0 < (disk x).val i) ↔ ‖x.val‖ < 1 :=
  (parametrization_positive_iff _).trans (squareBallHomeomorph_interior x)

theorem disk_isQuotientMap : IsQuotientMap disk :=
  parametrization_isQuotientMap.comp squareBallHomeomorph.isQuotientMap

theorem disk_injOn_interior : Set.InjOn disk {x | ‖x.val‖ < 1} := by
  intro x hx y _ h
  apply squareBallHomeomorph.injective
  exact parametrization_injective_off_collapsed_side
    (ne_of_gt (((squareBallHomeomorph_interior x).mpr hx) 1).1) h

end FiniteChains.OrderTriangleDisk
end

section
open scoped Classical Topology
namespace FiniteChains.Comb.OrderTriangleAttachment
open RelativeAttachment ClassicalSkeletonAttachment CategoryTheory Topology

def metricBallNormBallHomeomorph (n : ℕ) :
    (Metric.closedBall 0 1 : Set (Fin n → ℝ)) ≃ₜ ClosedUnitBall (Fin n → ℝ) where
  toFun x := ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
  invFun x := ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def simplexNormDiskHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ ClosedUnitBall (Fin n → ℝ) :=
  (standardSimplexClosedBallHomeomorph n).trans (metricBallNormBallHomeomorph n)

theorem simplexNormDiskHomeomorph_positive_iff (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (∀ i, 0 < z.val i) ↔ ‖(simplexNormDiskHomeomorph n z).val‖ < 1 := by
  change (∀ i, 0 < z.val i) ↔ ‖(standardSimplexClosedBallHomeomorph n z).val‖ < 1
  simpa using
    standardSimplexClosedBallHomeomorph_positive_iff n z

def diskReparametrization : C(ClosedUnitBall (Fin 2 → ℝ), ClosedUnitBall (Fin 2 → ℝ)) :=
  (simplexNormDiskHomeomorph 2).toContinuousMap.comp OrderTriangleDisk.disk

theorem diskReparametrization_interior (x : ClosedUnitBall (Fin 2 → ℝ)) :
    ‖(diskReparametrization x).val‖ < 1 ↔ ‖x.val‖ < 1 :=
  (simplexNormDiskHomeomorph_positive_iff 2 (OrderTriangleDisk.disk x)).symm.trans
    (OrderTriangleDisk.disk_positive_iff x)



def boundaryReparametrization : C(UnitBoundary (Fin 2 → ℝ), UnitBoundary (Fin 2 → ℝ)) where
  toFun z := ⟨(diskReparametrization (unitBoundaryInclusion _ z)).val, by
    apply le_antisymm (diskReparametrization (unitBoundaryInclusion _ z)).property
    apply le_of_not_gt
    intro h
    have h' := (diskReparametrization_interior (unitBoundaryInclusion _ z)).mp h
    change ‖z.val‖ < 1 at h'
    rw [z.property] at h'
    exact (lt_irrefl _ h')⟩
  continuous_toFun := by fun_prop

theorem diskReparametrization_boundary (z : UnitBoundary (Fin 2 → ℝ)) :
    diskReparametrization (unitBoundaryInclusion _ z) =
      unitBoundaryInclusion _ (boundaryReparametrization z) := rfl

variable (P : Type) [PartialOrder P]

abbrev OneSkeleton := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 2
abbrev TwoSkeleton := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 3

def triangleDiskMap (t : StrictOrdTri P) :
    C(ClosedUnitBall (Fin 2 → ℝ), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P (strictTriNerveEquiv P t).val
    (ULift.up ((TopologicalSingular.simplexCoordinates 2).symm (OrderTriangleDisk.disk x)))
  continuous_toFun := (orderNerveRealizationSimplex P (strictTriNerveEquiv P t).val).hom.continuous.comp
    (continuous_uliftUp.comp
      ((TopologicalSingular.simplexCoordinates 2).symm.continuous.comp OrderTriangleDisk.disk.continuous))

theorem characteristicDisk_simplex (n : ℕ) (s : (nerve P).nonDegenerate n)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) n s
      (simplexNormDiskHomeomorph n z).val =
        orderNerveRealizationSimplex P s.val (ULift.up ((TopologicalSingular.simplexCoordinates n).symm z)) := by
  rw [show Topology.CWComplex.map (C := Set.univ) n s
      (simplexNormDiskHomeomorph n z).val =
        orderNerveClosedBallChart s (standardSimplexClosedBallHomeomorph n z) from
    orderNerveCharacteristicFunction_closedBall s (standardSimplexClosedBallHomeomorph n z)]
  change orderNerveRealizationSimplex P s.val
    (ULift.up ((TopologicalSingular.simplexCoordinates n).symm
      ((standardSimplexClosedBallHomeomorph n).symm
      (standardSimplexClosedBallHomeomorph n z)))) = _
  rw [Homeomorph.symm_apply_apply]


def triangleAttaching : C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ), OneSkeleton P) where
  toFun := reparametrizedAttaching
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2)
    (strictTriNerveEquiv P) (fun _ => boundaryReparametrization)
  continuous_toFun := by
    apply continuous_sigma
    intro t
    have hs : Continuous (Sigma.mk
        (β := fun _ : (nerve P).nonDegenerate 2 => UnitBoundary (Fin 2 → ℝ))
        (strictTriNerveEquiv P t)) := continuous_sigmaMk
    exact (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2).continuous.comp
      (hs.comp boundaryReparametrization.continuous)

theorem triangleAttaching_val (t : StrictOrdTri P) (z : UnitBoundary (Fin 2 → ℝ)) :
    (triangleAttaching P ⟨t, z⟩).val = triangleDiskMap P t (unitBoundaryInclusion _ z) :=
  (characteristicDisk_simplex P 2 (strictTriNerveEquiv P t) (OrderTriangleDisk.disk (unitBoundaryInclusion _ z)))


def triangleAttachmentHomeomorph : DiskAttachment (triangleAttaching P) ≃ₜ TwoSkeleton P :=
  (diskAttachmentQuotientReparametrization
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2)
    (strictTriNerveEquiv P) (fun _ => diskReparametrization)
    (fun _ => boundaryReparametrization) (fun _ => diskReparametrization_boundary)
    (fun _ => ((simplexNormDiskHomeomorph 2).isQuotientMap.comp OrderTriangleDisk.disk_isQuotientMap))
    (fun _ => diskReparametrization_interior)
    (fun _ => (by
      intro x hx y hy h
      exact OrderTriangleDisk.disk_injOn_interior hx hy ((simplexNormDiskHomeomorph 2).injective h)))).trans
    (skeletonAttachmentHomeomorph (Set.univ : Set (orderNerveRealization P)) 2)

@[simp] theorem triangleAttachmentHomeomorph_old (x : OneSkeleton P) :
    (triangleAttachmentHomeomorph P
      (old (triangleAttaching P) (boundaryFamilyInclusion (StrictOrdTri P) _) x)).val = x.val := rfl


/-- When the nerve is two-dimensional, these are all the cells of the
actual realization, not just an auxiliary finite or truncated space. -/
def triangleAttachmentRealizationHomeomorph [Nonempty P]
    [(nerve P).HasDimensionLE 2] (hP : IsConnected (orderCx P)) :
    DiskAttachment (triangleAttaching P) ≃ₜ orderNerveRealization P :=
  (triangleAttachmentHomeomorph P).trans
    (ClassicalCW.originalTopSkeletonHomeomorph (orderNerveTwoComplex P hP)).symm

end FiniteChains.Comb.OrderTriangleAttachment
end

section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.OrderEdgeAttachment
open RelativeAttachment ClassicalSkeletonAttachment ClassicalGraphModel
open OrderTriangleAttachment CategoryTheory Topology

def intervalSimplexHomeomorph : I ≃ₜ stdSimplex ℝ (Fin 2) where
  toFun t := ⟨![1 - (t : ℝ), (t : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr t.property.2
      · exact t.property.1
    · simp [Fin.sum_univ_two]⟩
  invFun z := ⟨z.val 1, z.property.1 1, by
    have hs : z.val 0 + z.val 1 = 1 := (Fin.sum_univ_two z.val).symm.trans z.property.2
    linarith [z.property.1 0]⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    funext i
    have hs : z.val 0 + z.val 1 = 1 := (Fin.sum_univ_two z.val).symm.trans z.property.2
    fin_cases i
    · change 1 - z.val 1 = z.val 0
      linarith
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val

def edgeDiskSimplexHomeomorph : ClosedUnitBall (Fin 1 → ℝ) ≃ₜ stdSimplex ℝ (Fin 2) :=
  oneBallIntervalHomeomorph.trans intervalSimplexHomeomorph


def edgeDiskReparametrization : ClosedUnitBall (Fin 1 → ℝ) ≃ₜ ClosedUnitBall (Fin 1 → ℝ) :=
  edgeDiskSimplexHomeomorph.trans (simplexNormDiskHomeomorph 1)

theorem edgeDiskReparametrization_interior (x : ClosedUnitBall (Fin 1 → ℝ)) :
    ‖(edgeDiskReparametrization x).val‖ < 1 ↔ ‖x.val‖ < 1 :=
  (simplexNormDiskHomeomorph_positive_iff 1 (edgeDiskSimplexHomeomorph x)).symm.trans
    (by
      rw [finOne_norm, abs_lt]
      constructor
      · intro h
        have h₀ : 0 < 1 - (x.val 0 + 1) / 2 := h 0
        have h₁ : 0 < (x.val 0 + 1) / 2 := h 1
        constructor <;> linarith
      · rintro ⟨hl, hu⟩ i
        fin_cases i
        · change 0 < 1 - (x.val 0 + 1) / 2
          linarith
        · change 0 < (x.val 0 + 1) / 2
          linarith)

def edgeBoundaryReparametrization : C(UnitBoundary (Fin 1 → ℝ), UnitBoundary (Fin 1 → ℝ)) where
  toFun z := ⟨(edgeDiskReparametrization (unitBoundaryInclusion _ z)).val, by
    apply le_antisymm (edgeDiskReparametrization (unitBoundaryInclusion _ z)).property
    apply le_of_not_gt
    intro h
    have h' := (edgeDiskReparametrization_interior (unitBoundaryInclusion _ z)).mp h
    change ‖z.val‖ < 1 at h'
    rw [z.property] at h'
    exact (lt_irrefl _ h')⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp edgeDiskReparametrization.continuous).comp
      (unitBoundaryInclusion (Fin 1 → ℝ)).continuous

variable (P : Type) [PartialOrder P]

abbrev Vertices := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 1

def vertexEquiv : P ≃ Vertices P :=
  (vertexNerveEquiv P).trans (ClassicalCW.zeroCellEquiv (X := orderNerveRealization P))

theorem vertexEquiv_val (p : P) : (vertexEquiv P p).val = orderNerveRealizationVertex p := by
  change Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) 0
    (vertexNerveEquiv P p) ![] = _
  have he : (simplexNormDiskHomeomorph 0 (default : stdSimplex ℝ (Fin 1))).val = ![] :=
    Subsingleton.elim _ _
  rw [← he, characteristicDisk_simplex]
  apply congrArg (orderNerveRealizationSimplex P (vertexNerveEquiv P p).val)
  exact Subsingleton.elim _ _

def edgeDiskMap (e : StrictOrdEdge P) :
    C(ClosedUnitBall (Fin 1 → ℝ), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val
    (ULift.up ((TopologicalSingular.simplexCoordinates 1).symm (edgeDiskSimplexHomeomorph x)))
  continuous_toFun := (orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val).hom.continuous.comp
    (continuous_uliftUp.comp
      ((TopologicalSingular.simplexCoordinates 1).symm.continuous.comp edgeDiskSimplexHomeomorph.continuous))

theorem edgeDiskMap_characteristic (e : StrictOrdEdge P) (x : ClosedUnitBall (Fin 1 → ℝ)) :
    Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) 1
      (strictEdgeNerveEquiv P e) (edgeDiskReparametrization x).val = edgeDiskMap P e x :=
  characteristicDisk_simplex P 1 (strictEdgeNerveEquiv P e) (edgeDiskSimplexHomeomorph x)

theorem edgeDiskMap_coordinates (e : StrictOrdEdge P) (x : ClosedUnitBall (Fin 1 → ℝ)) (p : P) :
    orderNerveRealizationCoordinates P (edgeDiskMap P e x) p =
      (1 - (oneBallIntervalHomeomorph x : ℝ)) * (if e.val.1 = p then 1 else 0) +
      (oneBallIntervalHomeomorph x : ℝ) * (if e.val.2 = p then 1 else 0) := by
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val
      (ULift.up ((TopologicalSingular.simplexCoordinates 1).symm (edgeDiskSimplexHomeomorph x)))) p = _
  rw [orderNerveRealizationCoordinates_simplex]
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk,
    TopologicalSingular.simplexCoordinates_symm_weights_apply]
  rw [Fin.sum_univ_two]
  rfl

theorem edgeDiskMap_edgePath (e : StrictOrdEdge P) (t : I) :
    edgeDiskMap P e (graphDiskHomeomorph t) = orderNerveAffineEdgePath e.property.le t := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [edgeDiskMap_coordinates, orderNerveAffineEdgePath_coordinates]
  have he : oneBallIntervalHomeomorph (graphDiskHomeomorph t) = t := by
    ext
    dsimp [oneBallIntervalHomeomorph, graphDiskHomeomorph]
    ring
  rw [he]

def graphAttaching : C(BoundaryFamily (StrictOrdEdge P) (Fin 1 → ℝ), Vertices P) where
  toFun := reparametrizedAttaching
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1)
    (strictEdgeNerveEquiv P) (fun _ => edgeBoundaryReparametrization)
  continuous_toFun := by
    apply continuous_sigma
    intro e
    have hs : Continuous (Sigma.mk
        (β := fun _ : (nerve P).nonDegenerate 1 => UnitBoundary (Fin 1 → ℝ))
        (strictEdgeNerveEquiv P e)) := continuous_sigmaMk
    exact (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1).continuous.comp
      (hs.comp edgeBoundaryReparametrization.continuous)

theorem graphAttaching_val (e : StrictOrdEdge P) (z : UnitBoundary (Fin 1 → ℝ)) :
    (graphAttaching P ⟨e, z⟩).val = edgeDiskMap P e (unitBoundaryInclusion _ z) :=
  edgeDiskMap_characteristic P e (unitBoundaryInclusion _ z)

theorem graphAttaching_source (e : StrictOrdEdge P) :
    graphSrc (graphAttaching P) e = vertexEquiv P e.val.1 := by
  ext
  rw [graphSrc, graphAttaching_val, vertexEquiv_val, ← graphDiskHomeomorph_zero,
    edgeDiskMap_edgePath]
  simp

theorem graphAttaching_target (e : StrictOrdEdge P) :
    graphTgt (graphAttaching P) e = vertexEquiv P e.val.2 := by
  ext
  rw [graphTgt, graphAttaching_val, vertexEquiv_val, ← graphDiskHomeomorph_one,
    edgeDiskMap_edgePath]
  simp

def edgeReparametrizationHomeomorph :
    DiskAttachment (graphAttaching P) ≃ₜ
      DiskAttachment (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1) :=
  diskAttachmentQuotientReparametrization
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1)
    (strictEdgeNerveEquiv P) (fun _ => edgeDiskReparametrization.toContinuousMap)
    (fun _ => edgeBoundaryReparametrization) (fun _ _ => rfl)
    (fun _ => edgeDiskReparametrization.isQuotientMap)
    (fun _ => edgeDiskReparametrization_interior)
    (fun _ _ _ _ _ h => edgeDiskReparametrization.injective h)

def graphHomeomorph : DiskAttachment (graphAttaching P) ≃ₜ OrderTriangleAttachment.OneSkeleton P :=
  (edgeReparametrizationHomeomorph P).trans
    (skeletonAttachmentHomeomorph (Set.univ : Set (orderNerveRealization P)) 1)

@[simp] theorem graphHomeomorph_old (v : Vertices P) :
    (graphHomeomorph P (old (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) v)).val =
      v.val := rfl

@[simp] theorem graphHomeomorph_cell (e : StrictOrdEdge P) (x : ClosedUnitBall (Fin 1 → ℝ)) :
    (graphHomeomorph P (cell (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) ⟨e, x⟩)).val =
      edgeDiskMap P e x := by
  change (skeletonAttachmentHomeomorph Set.univ 1
    (edgeReparametrizationHomeomorph P (cell _ _ ⟨e, x⟩))).val = _
  rw [edgeReparametrizationHomeomorph]
  erw [diskAttachmentQuotientReparametrization_cell]
  rw [skeletonAttachmentHomeomorph_cell]
  exact edgeDiskMap_characteristic P e x

theorem graphHomeomorph_edgePath (e : StrictOrdEdge P) (t : I) :
    (graphHomeomorph P (graphEdgePath (graphAttaching P) e t)).val =
      orderNerveAffineEdgePath e.property.le t :=
  (graphHomeomorph_cell P e (graphDiskHomeomorph t)).trans (edgeDiskMap_edgePath P e t)

end FiniteChains.Comb.OrderEdgeAttachment

namespace FiniteChains.Comb.OrderTriangleWords
open RelativeAttachment ClassicalGraphModel ContinuousEdgeWords
open OrderTriangleAttachment OrderEdgeAttachment CategoryTheory

variable (P : Type) [PartialOrder P]

def edge01 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.val.1, t.val.2.1), t.property.1⟩
def edge12 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
def edge02 (t : StrictOrdTri P) : StrictOrdEdge P :=
  ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩

def corner (t : StrictOrdTri P) (z : SquareBoundary) : Vertices P :=
  vertexEquiv P (if z.val 1 = 0 then t.val.1 else
    if z.val 0 = 0 then t.val.2.1 else t.val.2.2)

def sideWord (t : StrictOrdTri P) (s : SquareSide) : List (StrictOrdEdge P × Bool) :=
  if s.1 = 0 then
    if s.2 then [(edge02 P t, true)] else [(edge01 P t, true)]
  else if s.2 then [(edge12 P t, true)] else []

def words (t : StrictOrdTri P) : BoundaryWords (graphAttaching P) where
  vertex := corner P t
  word := sideWord P t
  isPath := by
    rintro ⟨i, b⟩
    fin_cases i <;> cases b <;>
      simp [sideWord, corner, squareSideMap, Whitehead.squareEdge, boolEndpoint,
        IsPath, germSrc, germTgt, graphAttaching_source, graphAttaching_target,
        edge01, edge12, edge02]

theorem words_loopWord (t : StrictOrdTri P) :
    (words P t).loopWord = (strictOrderCx P).att t := rfl


def graphBoundary (t : StrictOrdTri P) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (graphAttaching P)) :=
  ((graphHomeomorph P).symm.toContinuousMap.comp (triangleAttaching P)).comp
    ⟨Sigma.mk (β := fun _ : StrictOrdTri P => UnitBoundary (Fin 2 → ℝ)) t,
      by exact continuous_sigmaMk⟩

def graphSquare (t : StrictOrdTri P) : C(SquareBoundary, DiskAttachment (graphAttaching P)) :=
  (graphBoundary P t).comp unitBoundarySquareHomeomorph.symm.toContinuousMap

theorem graphSquare_coordinates (t : StrictOrdTri P) (z : SquareBoundary) (p : P) :
    orderNerveRealizationCoordinates P ((graphHomeomorph P (graphSquare P t z)).val) p =
      (1 - (z.val 1 : ℝ)) * (if t.val.1 = p then 1 else 0) +
      ((z.val 1 : ℝ) * (1 - (z.val 0 : ℝ))) * (if t.val.2.1 = p then 1 else 0) +
      ((z.val 1 : ℝ) * (z.val 0 : ℝ)) * (if t.val.2.2 = p then 1 else 0) := by
  have he : graphHomeomorph P (graphSquare P t z) =
      triangleAttaching P ⟨t, unitBoundarySquareHomeomorph.symm z⟩ :=
    (graphHomeomorph P).apply_symm_apply _
  rw [he, triangleAttaching_val]
  have hd : OrderTriangleDisk.disk
      (unitBoundaryInclusion _ (unitBoundarySquareHomeomorph.symm z)) =
        OrderTriangleDisk.parametrization z.val := by
    change OrderTriangleDisk.parametrization
      (OrderTriangleDisk.squareBallHomeomorph
        (unitBoundaryInclusion _ (unitBoundarySquareHomeomorph.symm z))) = _
    rw [OrderTriangleDisk.squareBallHomeomorph_boundary, Homeomorph.apply_symm_apply]
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (strictTriNerveEquiv P t).val
      (ULift.up ((TopologicalSingular.simplexCoordinates 2).symm (OrderTriangleDisk.disk
        (unitBoundaryInclusion _ (unitBoundarySquareHomeomorph.symm z)))))) p = _
  rw [hd, orderNerveRealizationCoordinates_simplex]
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk,
    TopologicalSingular.simplexCoordinates_symm_weights_apply]
  change (∑ i : Fin 3, (OrderTriangleDisk.parametrization z.val).val i *
    (if (strictTriNerveEquiv P t).val.obj i = p then 1 else 0)) = _
  rw [Fin.sum_univ_three]
  rfl





def intervalPath : Path (0 : I) 1 where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl

def pausedIntervalPath : Path (0 : I) 1 := intervalPath.trans (Path.refl 1)

theorem single_word_paused {V E X : Type} [TopologicalSpace X]
    (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))
    (g : E × Bool) {a b : V} (h : IsPath src tgt [g] a b) (u : I) :
    realize src tgt v edge [g] h u = germPath src tgt v edge g (pausedIntervalPath u) := by
  by_cases hu : (u : ℝ) ≤ 2⁻¹
  · simp [realize, pausedIntervalPath, intervalPath, Path.trans_apply, hu]
  · simp [realize, pausedIntervalPath, intervalPath, Path.trans_apply, hu]


/-- All side homotopies use the same fixed-endpoint interval homotopy,
so they agree at corners throughout the deformation. -/

theorem graphBoundary_homotopic_words (t : StrictOrdTri P) :
    (graphBoundary P t).Homotopic (words P t).boundaryMap := by
  have H := (show (graphSquare P t).Homotopic (words P t).squareMap by
    let H := Classical.choice ((Path.Homotopic.trans_refl intervalPath).symm)
    let F s : C(I × I, DiskAttachment (graphAttaching P)) :=
      (graphSquare P t).comp ((squareSideMap s).comp H.toHomotopy.toContinuousMap)
    have hend : ∀ s τ u, u = 0 ∨ u = 1 → F s (τ, u) = graphSquare P t (squareSideMap s u) := by
      intro s τ u hu
      rcases hu with rfl | rfl
      · exact congrArg (fun u => graphSquare P t (squareSideMap s u)) (H.source τ)
      · exact congrArg (fun u => graphSquare P t (squareSideMap s u)) (H.target τ)
    let G := squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
    exact ⟨{
      toContinuousMap := G
      map_zero_left := by
        intro z
        obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
        change squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
          (0, squareSideMap s u) = graphSquare P t (squareSideMap s u)
        rw [squareBoundaryHomotopyPasting_side]
        change graphSquare P t (squareSideMap s (H (0, u))) = _
        rw [H.apply_zero]
        rfl
      map_one_left := by
        intro z
        obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
        change squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
          (1, squareSideMap s u) = (words P t).squareMap (squareSideMap s u)
        rw [squareBoundaryHomotopyPasting_side, BoundaryWords.squareMap_side]
        change graphSquare P t (squareSideMap s (H (1, u))) = _
        rw [H.apply_one]
        exact (show (words P t).sidePath s u = graphSquare P t (squareSideMap s (pausedIntervalPath u)) by
          rcases s with ⟨i, b⟩
          fin_cases i <;> cases b
          · erw [(show graphSquare P t (squareSideMap (0, false) (pausedIntervalPath u)) = graphEdgePath (graphAttaching P) (edge01 P t) (pausedIntervalPath u) by
            apply (graphHomeomorph P).injective
            ext
            apply orderNerveRealizationCoordinates_injective P
            funext p
            rw [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates]
            simp [squareSideMap, Whitehead.squareEdge, boolEndpoint, edge01])]
            exact single_word_paused _ _ _ _ _ ((words P t).isPath (0, false)) u
          · erw [(show graphSquare P t (squareSideMap (0, true) (pausedIntervalPath u)) = graphEdgePath (graphAttaching P) (edge02 P t) (pausedIntervalPath u) by
            apply (graphHomeomorph P).injective
            ext
            apply orderNerveRealizationCoordinates_injective P
            funext p
            rw [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates]
            simp [squareSideMap, Whitehead.squareEdge, boolEndpoint, edge02])]
            exact single_word_paused _ _ _ _ _ ((words P t).isPath (0, true)) u
          · erw [(show graphSquare P t (squareSideMap (1, false) (pausedIntervalPath u)) =
      old (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) (vertexEquiv P t.val.1) by
            apply (graphHomeomorph P).injective
            ext
            apply orderNerveRealizationCoordinates_injective P
            funext p
            rw [graphSquare_coordinates, graphHomeomorph_old, vertexEquiv_val,
              orderNerveRealizationCoordinates_vertex]
            simp [squareSideMap, Whitehead.squareEdge, boolEndpoint])]
            simp [BoundaryWords.sidePath, words, sideWord, realize, corner,
              squareSideMap, Whitehead.squareEdge, boolEndpoint]
          · erw [(show graphSquare P t (squareSideMap (1, true) (pausedIntervalPath u)) = graphEdgePath (graphAttaching P) (edge12 P t) (pausedIntervalPath u) by
            apply (graphHomeomorph P).injective
            ext
            apply orderNerveRealizationCoordinates_injective P
            funext p
            rw [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates]
            simp [squareSideMap, Whitehead.squareEdge, boolEndpoint, edge12])]
            exact single_word_paused _ _ _ _ _ ((words P t).isPath (1, true)) u).symm }⟩).comp
    (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  have he : (graphSquare P t).comp unitBoundarySquareHomeomorph.toContinuousMap =
      graphBoundary P t := by
    apply ContinuousMap.ext
    intro z
    exact congrArg (graphBoundary P t) (unitBoundarySquareHomeomorph.symm_apply_apply z)
  rwa [he] at H

end FiniteChains.Comb.OrderTriangleWords
end

section
open scoped Classical unitInterval Topology ContinuousMap
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.OrderTriangleWords
open RelativeAttachment ClassicalGraphModel PresModel SpanningTree
open OrderTriangleAttachment OrderEdgeAttachment CategoryTheory

variable (P : Type) [PartialOrder P]

local instance : DiscreteTopology (Vertices P) :=
  ClassicalCW.zeroSkeleton_discrete (X := orderNerveRealization P)

theorem graph_germSrc (g : StrictOrdEdge P × Bool) :
    germSrc (graphSrc (graphAttaching P)) (graphTgt (graphAttaching P)) g =
      vertexEquiv P (germSrc (strictOrderCx P).src (strictOrderCx P).tgt g) := by
  rcases g with ⟨e, b⟩
  cases b <;> simp only [germSrc, graphAttaching_source, graphAttaching_target] <;> rfl

theorem graph_germTgt (g : StrictOrdEdge P × Bool) :
    germTgt (graphSrc (graphAttaching P)) (graphTgt (graphAttaching P)) g =
      vertexEquiv P (germTgt (strictOrderCx P).src (strictOrderCx P).tgt g) := by
  rcases g with ⟨e, b⟩
  cases b <;> simp only [germTgt, graphAttaching_source, graphAttaching_target] <;> rfl

variable (T : SpanningTree (strictOrderCx P))

/-- Only the vertex names change. In particular the non-tree edge type
is definitionally the prescribed type `NonTree T`. -/
def graphTree : SpanningTree (graphCx (graphAttaching P)) where
  root := vertexEquiv P T.root
  ht v := T.ht ((vertexEquiv P).symm v)
  isTree := T.isTree
  up v hv := T.up ((vertexEquiv P).symm v) (by
    intro h
    apply hv
    simpa only [Equiv.apply_symm_apply] using congrArg (vertexEquiv P) h)
  ht_root := by simpa only [Equiv.symm_apply_apply] using T.ht_root
  ht_eq_zero := by
    intro v hv
    simpa only [Equiv.apply_symm_apply] using
      congrArg (vertexEquiv P) (T.ht_eq_zero _ hv)
  up_src := by
    intro v hv
    erw [graph_germSrc, T.up_src, Equiv.apply_symm_apply]
  up_ht := by
    intro v hv
    erw [graph_germTgt, Equiv.symm_apply_apply]
    exact T.up_ht _ _
  isTree_iff := by
    intro e
    constructor
    · intro he
      obtain ⟨v, hv, he⟩ := (T.isTree_iff e).mp he
      refine ⟨vertexEquiv P v, (fun h => hv ((vertexEquiv P).injective h)), ?_⟩
      simpa only [Equiv.symm_apply_apply] using he
    · rintro ⟨v, hv, he⟩
      refine (T.isTree_iff e).mpr ⟨(vertexEquiv P).symm v, ?_, he⟩
      intro h
      apply hv
      simpa only [Equiv.apply_symm_apply] using congrArg (vertexEquiv P) h

theorem graphTree_pathWord (l : List (StrictOrdEdge P × Bool)) :
    pathWord (graphTree P T) l = pathWord T l := rfl

def collapsedWords (t : StrictOrdTri P) : BoundaryWords (roseAttaching (NonTree T)) :=
  (words P t).eraseTree (graphAttaching P) (graphTree P T)


def oneSkeletonRoseEquiv : OneSkeleton P ≃ₕ ClassicalGraphModel.Rose (NonTree T) :=
  (graphHomeomorph P).symm.toHomotopyEquiv.trans
    (graphRoseHomotopyEquiv (graphAttaching P) (graphAttaching P).continuous (graphTree P T))

def collapsedAttaching :
    C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ), ClassicalGraphModel.Rose (NonTree T)) :=
  (oneSkeletonRoseEquiv P T).toFun.comp (triangleAttaching P)

def collapsedCellBoundary (t : StrictOrdTri P) :
    C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose (NonTree T)) :=
  (collapsedAttaching P T).comp
    ⟨Sigma.mk (β := fun _ : StrictOrdTri P => UnitBoundary (Fin 2 → ℝ)) t,
      by exact continuous_sigmaMk⟩


variable (a : NonTree T)



/-- The comparison uses the actual CW attaching maps of every triangle,
not a homology or fundamental-group surrogate for a homotopy equivalence. -/
def canonicalTreeDiskRealizationEquiv [Nonempty P] [(nerve P).HasDimensionLE 2]
    (hP : IsConnected (orderCx P)) :
    ClassicalPresWordDisks (presCanonicalWords (treeRel T) a)
      (presCanonicalWords_ne_nil (treeRel T) a) ≃ₕ orderNerveRealization P :=
  (((triangleAttachmentRealizationHomeomorph P hP).symm.toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (triangleAttaching P)
      (oneSkeletonRoseEquiv P T))).trans
    (diskAttachingHomotopyEquiv (collapsedAttaching P T)
      (classicalPresWordAttaching (presCanonicalWords (treeRel T) a)
        (presCanonicalWords_ne_nil (treeRel T) a))
      (by
        let H (t : StrictOrdTri P) := Classical.choice
          (show (collapsedCellBoundary P T t).Homotopic
      (classicalPresCellBoundary (presCanonicalWords (treeRel T) a) t
        (presCanonicalWords_ne_nil (treeRel T) a)) by
            have he  :=
              (show FreeGroup.mk (collapsedWords P T t).loopWord = treeRel T t by
                change FreeGroup.mk ((words P t).eraseTree (graphAttaching P) (graphTree P T)).loopWord = _
                rw [BoundaryWords.eraseTree_mk, graphTree_pathWord, words_loopWord]
                rfl).trans (mk_presCanonicalWords (treeRel T) a t).symm
            exact (show (collapsedCellBoundary P T t).Homotopic (collapsedWords P T t).boundaryMap by
              have H := (ContinuousMap.Homotopic.refl
                (graphRoseHomotopyEquiv (graphAttaching P) (graphAttaching P).continuous
                  (graphTree P T)).toFun).comp (graphBoundary_homotopic_words P t)
              exact H.trans ((words P t).collapse_homotopic_eraseTree
                (graphAttaching P) (graphAttaching P).continuous (graphTree P T))).trans
              ((boundaryWords_homotopic_classicalWord (collapsedWords P T t)).trans
                ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
                  (classicalPresWordAttaching_homotopic_read (presCanonicalWords (treeRel T) a) t
                    (presCanonicalWords_ne_nil (treeRel T) a)).symm)))
        let F : C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ),
            C(I, ClassicalGraphModel.Rose (NonTree T))) :=
          ⟨fun z => ((H z.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry z.2,
            continuous_sigma (fun t =>
              ((H t).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
        exact {
          toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
          map_zero_left := fun z => (H z.1).apply_zero z.2
          map_one_left := fun z => (H z.1).apply_one z.2 }))).symm

end FiniteChains.Comb.OrderTriangleWords
end

section
open scoped Classical
namespace Whitehead
open FiniteChains FiniteChains.Comb FiniteChains.ClassicalCW FiniteChains.PresModel

theorem hasChain_of_acyclicRegularCover (K : TwoComplex)
    (h : HasAcyclicRegularCover K) (n : ℕ) (hn : 1 ≤ n) : HasChain K n false := by
  let hP := presPos_isConnected (canonicalWords K) (canonicalWords_ne_nil K)
  obtain ⟨T, -⟩ := SpanningTree.exists_of_isConnected
    (strictOrderCx_isConnected hP)
    (Classical.choice (inferInstance : Nonempty (CanonicalPos K)))
  let e₀ := OrderTriangleWords.canonicalTreeDiskRealizationEquiv
    (CanonicalPos K) T (canonicalTreeGenerator K T) hP
  cases n with
  | zero => omega
  | succ n => exact hasChain_of_original_cover_tree_comparison K T e₀ h n

end Whitehead
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
open scoped Classical
universe u
variable {A J : Type u}

def roseIntegerBaseEdge (a : A) (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.base, Rose.edg a b), lt_of_le_of_ne (Rose.base_le_edg a b) (by simp)⟩

def roseIntegerMidEdge (a : A) (b : Bool) : StrictOrdEdge (Rose A) :=
  ⟨(Rose.mid a, Rose.edg a b), lt_of_le_of_ne (Rose.mid_le_edg a b) (by simp)⟩

def roseIntegerGeneratorChain (a : A) : StrictOrdEdge (Rose A) →₀ ℤ :=
  Finsupp.single (roseIntegerBaseEdge a false) 1 -
    Finsupp.single (roseIntegerMidEdge a false) 1 +
    Finsupp.single (roseIntegerMidEdge a true) 1 -
    Finsupp.single (roseIntegerBaseEdge a true) 1

def roseIntegerRealize : (A →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (Rose A) →₀ ℤ) :=
  Finsupp.linearCombination ℤ roseIntegerGeneratorChain

theorem roseIntegerGeneratorChain_selected (a b : A) :
    roseIntegerGeneratorChain a (roseIntegerMidEdge b true) = if a = b then 1 else 0 := by
  have hb s : roseIntegerBaseEdge a s ≠ roseIntegerMidEdge b true := by
    intro h
    have he := congrArg (fun e : StrictOrdEdge (Rose A) => e.val.1) h
    cases he
  have hm : roseIntegerMidEdge a false ≠ roseIntegerMidEdge b true := by
    intro h
    have he := congrArg (fun e : StrictOrdEdge (Rose A) => e.val.2) h
    cases he
  have he : roseIntegerMidEdge a true = roseIntegerMidEdge b true ↔ a = b := by
    constructor
    · intro h
      exact Rose.mid.inj (congrArg (fun e : StrictOrdEdge (Rose A) => e.val.1) h)
    · rintro rfl
      rfl
  simp [roseIntegerGeneratorChain, Finsupp.single_apply, hb, hm, he]

theorem roseIntegerRealize_selected (c : A →₀ ℤ) (a : A) :
    roseIntegerRealize c (roseIntegerMidEdge a true) = c a := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single b n =>
    simp only [roseIntegerRealize, Finsupp.linearCombination_single, Finsupp.smul_apply,
      roseIntegerGeneratorChain_selected, Finsupp.single_apply]
    split_ifs <;> simp_all

theorem roseIntegerRealize_injective : Function.Injective (roseIntegerRealize (A := A)) := by
  intro c d h
  apply Finsupp.ext
  intro a
  have he := congrArg (fun z => z (roseIntegerMidEdge a true)) h
  simpa only [roseIntegerRealize_selected] using he


theorem roseIntegerRealize_cycle (c : A →₀ ℤ) :
    Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerRealize c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single a n =>
    erw [roseIntegerRealize, Finsupp.linearCombination_single, map_smul,
      (show Comb.bdry1 (strictOrderCx (Rose A)) (roseIntegerGeneratorChain a) = 0 by
        simp only [roseIntegerGeneratorChain, map_sub, map_add, Comb.bdry1_single (X := strictOrderCx (Rose A)),
          Finsupp.linearCombination_single, one_smul]
        change (Finsupp.single (Rose.edg a false) 1 - Finsupp.single Rose.base 1) -
            (Finsupp.single (Rose.edg a false) 1 - Finsupp.single (Rose.mid a) 1) +
            (Finsupp.single (Rose.edg a true) 1 - Finsupp.single (Rose.mid a) 1) -
            (Finsupp.single (Rose.edg a true) 1 - Finsupp.single Rose.base 1) = 0
        abel), smul_zero]

theorem mapOne_single_of_endpoints {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (e : StrictOrdEdge P) (d : StrictOrdEdge Q)
    (he : (f e.val.1, f e.val.2) = d.val) :
    StrictNormalized.mapOne f hf (Finsupp.single e 1) = Finsupp.single d 1 := by
  erw [StrictNormalized.mapOne_single, one_smul]
  have hn : f e.val.1 ≠ f e.val.2 := by
    intro h
    exact d.property.ne ((congrArg Prod.fst he).symm.trans (h.trans (congrArg Prod.snd he)))
  unfold normalizeOrdEdge
  simp_all

variable (w : J → List (A × Bool)) (j : J)

theorem relatorCircleLetterChain_exponent (k : Fin (w j).length) :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleLetterChain w j k) =
        if (w j)[k.val].2 then roseIntegerGeneratorChain (w j)[k.val].1
          else -roseIntegerGeneratorChain (w j)[k.val].1 := by
  let f := fun x : RelatorCircle w j => aFun w x.val
  let hf : Monotone f := (aFun_monotone w).comp (fun _ _ h => h)
  have hp : (w j)[k.val]? = some (w j)[k.val] := List.getElem?_eq_getElem k.isLt
  have hmid  :=
    aFun_pt_cmid_of_get w hp
  have hL  :=
    aFun_pt_cedgL_of_get w hp
  have hR  :=
    aFun_pt_cedgR_of_get w hp
  have h₀ := mapOne_single_of_endpoints f hf (relatorCircleEdge0 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext rfl hL)
  have h₁ := mapOne_single_of_endpoints f hf (relatorCircleEdge1 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (!(w j)[k.val].2)) (Prod.ext hmid hL)
  have h₂ := mapOne_single_of_endpoints f hf (relatorCircleEdge2 w j k)
    (roseIntegerMidEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext hmid hR)
  have h₃ := mapOne_single_of_endpoints f hf (relatorCircleEdge3 w j k)
    (roseIntegerBaseEdge (w j)[k.val].1 (w j)[k.val].2) (Prod.ext rfl hR)
  erw [relatorCircleLetterChain, map_sub, map_add, map_sub, h₀, h₁, h₂, h₃]
  cases (w j)[k.val].2 <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, roseIntegerGeneratorChain]
  abel

theorem pathChain_eq_sum_get (l : List (A × Bool)) :
    pathChain l = ∑ k : Fin l.length,
      if l[k.val].2 then Finsupp.single l[k.val].1 (1 : ℤ) else -Finsupp.single l[k.val].1 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    erw [pathChain_cons]
    erw [Fin.sum_univ_succ]
    simpa using
      congrArg (fun z => (if p.2 then Finsupp.single p.1 (1 : ℤ) else -Finsupp.single p.1 1) + z) ih

theorem expVec_mk_eq_pathChain (l : List (A × Bool)) :
    FiniteChains.expVec (FreeGroup.mk l) = pathChain l := by
  exact congrArg Multiplicative.toAdd (Comb.expVec_pathChain l)

/-- Exact exponent-vector formula for the normalized image of the genuine
attaching-circle fundamental chain; valid also for the empty circle. -/
theorem relatorCircleFundamentalChain_exponent :
    StrictNormalized.mapOne (fun x : RelatorCircle w j => aFun w x.val)
      ((aFun_monotone w).comp (fun _ _ h => h)) (relatorCircleFundamentalChain w j) =
        roseIntegerRealize (FiniteChains.expVec (FreeGroup.mk (w j))) := by
  erw [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_exponent]
  erw [expVec_mk_eq_pathChain, pathChain_eq_sum_get, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases (w j)[k.val].2 <;>
    simp only [Bool.false_eq_true, if_false, if_true, map_neg,
      roseIntegerRealize, Finsupp.linearCombination_single, one_smul]

end FiniteChains.PresModel

namespace FiniteChains.PresModel.IdentityChains
open Comb Comb.StrictNormalized
universe u
variable {α J : Type u} (w : J → List (α × Bool))


/-- With the actual identity-cover labels, the actual attaching differential
is the original exponent matrix, realized by genuine rose cycles. -/
theorem roseProjection_relatorBoundaryChain (c : PresCoverRelator w id →₀ ℤ) :
    roseProjection w (presCoverCylinderRelatorBoundaryChain w id (cover w) c) =
      roseIntegerRealize (expMatrix (fun j => FreeGroup.mk (w j))
        (Finsupp.mapDomain (fun p : PresCoverRelator w id => p.1.2) c)) := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single p n =>
    erw [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single,
      map_smul, (show roseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      roseIntegerRealize (FiniteChains.expVec (FreeGroup.mk (w p.1.2))) by
        change mapOne (cylRetr (aHom w)) _ (baseProjection w _) = _
        erw [baseProjection_relatorBoundary]
        unfold cylinderBoundary
        erw [mapOne_comp]
        exact relatorCircleFundamentalChain_exponent w p.1.2), Finsupp.mapDomain_single,
      expMatrix, Finsupp.linearCombination_single, map_smul]


/-- Vanishing actual H₂ rules out every exponent-matrix kernel vector.
The proof realizes the vector by actual cone fans and an actual cylinder
prism before applying H₂. -/
theorem expMatrix_injective_of_strict_h2 (hpos : ∀ j, 0 < (w j).length)
    (h2 : Function.Injective (Comb.bdry2 (strictOrderCx (PresPos w)))) :
    Function.Injective (expMatrix (fun j => FreeGroup.mk (w j))) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  let d  := Finsupp.mapDomain (relatorEquiv w) c
  have hd : Finsupp.mapDomain (fun p : PresCoverRelator w id => p.1.2) d = c := by
    erw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  have hb : roseProjection w (presCoverCylinderRelatorBoundaryChain w id (cover w) d) = 0 := by
    erw [roseProjection_relatorBoundaryChain, hd, hc, map_zero]
  obtain ⟨z, hz, hcoord⟩ := exists_presCover_cycle_of_collapsed_relator_boundary
    w id (cover w) hpos d
    (collapsed_eq_zero_of_roseProjection_eq_zero w _ hb)
  have hz0  := h2 (hz.trans (map_zero _).symm)
  have hd0 : d = 0 := by simpa only [hz0, map_zero] using hcoord.symm
  erw [hd0, Finsupp.mapDomain_zero] at hd
  exact hd.symm

/-- Vanishing actual H₁ supplies every exponent vector: realize it on the
rose, fill it in the original strict complex, and extract the actual apex
coefficients of that filling. -/
theorem expMatrix_surjective_of_strict_h1 (hpos : ∀ j, 0 < (w j).length)
    (h1 : ∀ c : StrictOrdEdge (PresPos w) →₀ ℤ,
      Comb.bdry1 (strictOrderCx (PresPos w)) c = 0 →
        ∃ d : StrictOrdTri (PresPos w) →₀ ℤ,
          Comb.bdry2 (strictOrderCx (PresPos w)) d = c) :
    Function.Surjective (expMatrix (fun j => FreeGroup.mk (w j))) := by
  intro v
  let b := roseInclusion w (roseIntegerRealize v)
  let I := strictSubposetIncl (coneAdjBaseSet (S := circSet w))
  have hb : Comb.bdry1 (strictOrderCx (Base w)) b = 0 := by
    erw [bdry1_chain1, roseIntegerRealize_cycle, map_zero]
  have hz : Comb.bdry1 (strictOrderCx (PresPos w)) (chain1 I b) = 0 := by
    erw [bdry1_chain1 I b, hb, map_zero]
  obtain ⟨d, hd⟩ := h1 (chain1 I b) hz
  refine ⟨Finsupp.mapDomain (fun p : PresCoverRelator w id => p.1.2)
    (presCoverRelatorChain w id (cover w) hpos d), ?_⟩
  apply roseIntegerRealize_injective
  have h := (by
    have h := congrArg (roseProjection w)
      (presCover_relative_collapsed_boundary w id (cover w) hpos d b hd)
    rw [roseProjection_collapse, roseProjection_collapse,
      roseProjection_relatorBoundaryChain] at h
    exact h)
  erw [show b = roseInclusion w (roseIntegerRealize v) from rfl,
    roseProjection_inclusion] at h
  exact h.symm

end FiniteChains.PresModel.IdentityChains

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

/-- An acyclic actual strict presentation complex has a bijective exponent
matrix, without finiteness assumptions on either cell-index type. -/
theorem expMatrix_bijective_of_strict_pres_acyclic
    (ρ : J → FreeGroup α) (w : J → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)
    (h : IsAcyclic (strictOrderCx (PresPos w))) : Function.Bijective (expMatrix ρ) := by
  have he  := funext hw
  erw [← he]
  exact ⟨IdentityChains.expMatrix_injective_of_strict_h2 w hpos h.h2,
    IdentityChains.expMatrix_surjective_of_strict_h1 w hpos h.h1⟩

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb CategoryTheory
variable {α J : Type}

/-- The actual singular acyclicity hypothesis discharges the algebraic matrix
hypothesis used by the arbitrary-cell initial construction. -/
theorem expMatrix_bijective_of_presRealization_acyclic
    (ρ : J → FreeGroup α) (w : J → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)
    (h : Whitehead.Acyclic (orderNerveRealization (PresPos w))) :
    Function.Bijective (expMatrix ρ) := by
  letI : Nonempty (PresPos w) := ⟨ptBase w⟩
  letI : (nerve (PresPos w)).HasDimensionLE 2 :=
    orderNerve_hasDimensionLE (presPosDimension w) (presPosDimension_strictMono w) 2
      (presPosDimension_le_two w)
  exact expMatrix_bijective_of_strict_pres_acyclic ρ w hw hpos
    ((orderRealization_acyclic_iff_strict_isAcyclic (PresPos w)
      (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))).mp h)

end FiniteChains.PresModel
end

namespace FiniteChains.RelativeNormalForm
open PresModel
open scoped Classical

variable {A C : Type} [dA : DecidableEq A] (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))


/-- Transport the original singular acyclicity through the actual disk-model
comparison and extract the original presentation's exponent isomorphism. -/
theorem actual_expMatrix_bijective_of_acyclic
    (K : Whitehead.TwoComplex) (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K) :
    Function.Bijective (expMatrix core) := by
  let e := (presClassicalDiskComparison (presCanonicalWords core a)
    (presCanonicalWords_ne_nil core a)).trans e₀
  have hmodel  :=
    (Whitehead.acyclic_iff_of_homotopyEquiv e).mpr hK
  exact expMatrix_bijective_of_presRealization_acyclic core (presCanonicalWords core a)
    (mk_presCanonicalWords core a) (presCanonicalWords_positive core a) hmodel

/-- The finite original-cell version also derives its matrix premise from
actual singular acyclicity; finiteness is used only for the finite conclusion. -/
theorem actual_hasOriginalFiniteChain_of_acyclic [Finite A] [Finite C]
    (K : Whitehead.TwoComplex) (hfinite : Whitehead.FiniteCells K)
    (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ) : Whitehead.HasChain K (n + 1) true :=
  (by
    have hd : dA = Classical.decEq A := Subsingleton.elim _ _
    subst dA
    let c := actualAmbientChain core (actual_expMatrix_bijective_of_acyclic core K hK a e₀) n
    apply (c.toPresChainFS (actual_expMatrix_bijective_of_acyclic core K hK a e₀).1).hasOriginalTopologicalChain K a e₀ c.chain_proper true
    intro _
    have h := actualAmbientChain_finite core (actual_expMatrix_bijective_of_acyclic core K hK a e₀) n
    letI : Finite c.extraGen := h.1
    letI : Finite c.extraCell := h.2
    change Whitehead.FiniteCells K ∧ Finite (A ⊕ c.extraGen) ∧
      Finite (C ⊕ {s // c.stage n s})
    exact ⟨hfinite, inferInstance, inferInstance⟩)

end FiniteChains.RelativeNormalForm

section
open scoped Classical
namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.RelativeNormalForm

theorem hasFiniteChain_of_acyclic (K : TwoComplex) (hfinite : FiniteCells K)
    (hK : Acyclic K) (n : ℕ) (hn : 1 ≤ n) : HasChain K n true := by
  letI := canonicalGen_finite K hfinite
  letI := canonicalRel_finite K hfinite
  cases n with
  | zero => omega
  | succ n =>
      exact actual_hasOriginalFiniteChain_of_acyclic (canonicalRelators K) K hfinite hK
        (canonicalDummy K) (originalClassicalPresWordDiskEquiv K).symm n

end Whitehead
end
