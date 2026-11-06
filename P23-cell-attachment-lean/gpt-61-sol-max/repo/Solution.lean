/-
Attaching arbitrary families of two-cells, Hatcher Proposition 1.26.
Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.
First-party sources released under Apache-2.0.
Vendored sources preserve their original license and copyright notices below.
-/
/-
Vendored directed-topology helpers retain the following MIT notice.
Copyright 2023 Dominique Lawson
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/
module
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Groupoid.Basic
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} (f : ι → ContinuousMap Circle X) (x₀ : X)
  [Group G] [Groupoid U] [TopologicalSpace Y]
  (γ : ∀ i, Path x₀ (f i 1)) (i : ι)


/-- Changing the vertex of a groupoid by a chosen path is a group isomorphism. -/
abbrev transportEnd {a b : U} (p : a ⟶ b) :=
  ((Groupoid.isoEquivHom _ _).symm p).symm.conj
/-- A choice of paths from a vertex turns a homomorphism on its vertex group
into a functor on the whole connected groupoid. -/
def basedFunctor (p : ∀ x : U, b ⟶ x)
    (q : End b →* G) : U ⥤ SingleObj G where
  obj _ := .unit
  map {x y} f := q (p x ≫ f ≫ inv (p y))
  map_id x := by simpa using! q.map_one
  map_comp f g := by
    simp [SingleObj.comp_as_mul, ← q.map_mul]


/-- The closed two-dimensional unit disk in the complex plane. -/
abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
/-- The inclusion of the unit circle into the closed disk. -/
def boundaryInclusion : ContinuousMap Circle Disk where
  toFun z := ⟨z, le_of_eq (Circle.norm_coe z)⟩
/-- The actual topological disjoint union before attaching the disks. -/
abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)
/-- Only boundary points are identified with their prescribed attaching images. -/
inductive AttachingRel : Raw X ι → Raw X ι → Prop
  | boundary i z :
      AttachingRel (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
/-- The adjunction quotient, with its induced quotient topology. -/
def Space  := Quot (AttachingRel f)
instance : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))
/-- The quotient map from the unglued topological disjoint union. -/
def quotientMap : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩
/-- The actual continuous inclusion of the original space. -/
def inclusion  : ContinuousMap X (Space f) where
  toFun x := quotientMap f (.inl x)
  continuous_toFun := (quotientMap f).continuous.comp continuous_inl
def characteristic :=
  (quotientMap f).comp ⟨Sum.inr ∘ Sigma.mk i, continuous_inr.comp continuous_sigmaMk⟩
/-- The quotient map is a quotient map, not merely a continuous surjection. -/
theorem quotientMap_isQuotientMap  :
    Topology.IsQuotientMap (quotientMap f) := isQuotientMap_quot_mk
/-- The specified map on fundamental groups is induced by the actual inclusion. -/
def inclusionPi1 :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀

abbrev OpenDisk := Metric.ball (0 : ℂ) 1
/-- The representative of an interior disk point in the raw disjoint union. -/
def interiorRepresentative (z : OpenDisk) : Raw X ι :=
  .inr ⟨i, z, (mem_ball_zero_iff.mp z.property).le⟩
/-- The canonical continuous inclusion of the coproduct of open disks. -/
def interiorMap := ContinuousMap.sigma fun i =>
  ⟨quotientMap f ∘ interiorRepresentative i,
    (characteristic f i).continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Interior representatives have singleton quotient classes. -/
@[simp] theorem interiorRepresentative_quotient_eq_iff
    z a :
    quotientMap f (interiorRepresentative i z) = quotientMap f a ↔
      interiorRepresentative i z = a := by
  let r : Space f → Prop := Quot.lift (fun a => interiorRepresentative i z = a) (by
    rintro _ _ ⟨j,w⟩
    aesop (add simp [interiorRepresentative, boundaryInclusion, Subtype.ext_iff]))
  exact ⟨fun h => (congrArg r h).mp rfl, congrArg (quotientMap f)⟩
/-- The genuine quotient does not alter interiors or their topology. -/
theorem interiorMap_isOpenEmbedding : Topology.IsOpenEmbedding (interiorMap f) := by
  refine .of_continuous_injective_isOpenMap (interiorMap f).continuous ?_ ?_
  · intro a b h
    simpa [interiorRepresentative, Subtype.ext_iff, Sigma.ext_iff] using
      (interiorRepresentative_quotient_eq_iff f a.1 a.2 _).mp h
  · intro S hS
    rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
    convert ((isOpenMap_sigma (f := fun z => interiorRepresentative (X := X) z.1 z.2)).mpr fun i => isOpenMap_inr.comp (isOpenMap_sigmaMk.comp
      (Metric.isOpen_ball.isOpenMap_subtype_val.subtype_mk _))) S hS using 1
    ext a
    simp [interiorMap]

/-
Copyright (c) 2026 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen
This is a local backport from mathlib commit
389347a7c1cfa76f6bd5be2ca35d4cb621610ad3, file
Mathlib/Topology/Covering/FundamentalGroupCircle.lean (Apache 2.0):
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Topology/Covering/FundamentalGroupCircle.lean
The supporting lifting lemmas below are backported from the same commit's
Mathlib/Topology/Homotopy/Lifting.lean, copyright (c) 2025 Junyan Xu.
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Topology/Homotopy/Lifting.lean
The zmultiples equivalence is adapted, specialized to real numbers, from
Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean, copyright (c) 2020
Chris Hughes, authors Chris Hughes and Snir Broshi (Apache 2.0).
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean
-/


/-- The standard positively oriented circle loop, `t ↦ exp(2πt)`, based at `1`. -/
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp (t.1 * (2 * Real.pi))
  source' := by simp
  target' := by simp

/-- The contractible radius coordinate of the open annulus. -/
abbrev Radii := Set.Ioo (0 : ℝ) 1
abbrev PuncturedDisk := {z : Disk // z.1 ≠ 0}
/-- Normalize a nonzero disk point to the actual unit circle. -/
def polar : ContinuousMap PuncturedDisk Circle where
  toFun z := ⟨NormedSpace.normalize z.1.1,
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize z.2)⟩
  continuous_toFun := by unfold NormedSpace.normalize; fun_prop (disch := aesop)
def annulusPolarHomeomorph : {z : OpenDisk // z.1 ≠ 0} ≃ₜ Circle × Radii where
  toFun z := (polar ⟨⟨z.1.1,(mem_ball_zero_iff.mp z.1.2).le⟩,z.2⟩, ⟨dist z.1.1 0, dist_pos.mpr z.2, z.1.2⟩)
  invFun z := ⟨⟨z.2.1 • z.1.1, by
    simpa [abs_of_pos z.2.2.1] using z.2.2.2⟩,
    by aesop⟩
  left_inv z := by ext; simp [polar]
  right_inv z := by
    ext <;> simp [polar, NormedSpace.normalize, abs_of_pos z.2.2.1, z.2.2.1.ne']

instance : ContractibleSpace Radii :=
  (convex_Ioo 0 1).contractibleSpace (Set.nonempty_Ioo.mpr zero_lt_one)

def annulusHomotopyEquivCircle :=
    ((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr
      (ContractibleSpace.hequiv_unit Radii).some).trans
      (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv

/-- A homotopy equivalence induces the actual map on based fundamental groups
as a multiplicative equivalence. Its forward map is not an abstract choice. -/
def homotopyEquivFundamentalGroup (e : ContinuousMap.HomotopyEquiv X Y) x :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    ⟨x⟩

/-- A basepoint over `1` supplied by the homotopy inverse. -/
abbrev annulusBasepoint := annulusHomotopyEquivCircle.invFun 1
/-- Lift the once-around circle loop to the annulus at the chosen radius. -/
def annulusGenerator :=
  circleGenerator.map annulusHomotopyEquivCircle.invFun.continuous
/-- The open disk is contractible by convexity. -/
instance : ContractibleSpace OpenDisk :=
Metric.contractibleSpace_ball zero_lt_one

/-- The set of all attached disk interiors. -/
def interiors :=
  Set.range (interiorMap f)
/-- The set of attached disk centers, with no finiteness assumption. -/
def centers :=
  Set.range (fun i => interiorMap f ⟨i, ⟨0, by simp⟩⟩)
/-- The punctured neighborhood of the original space. -/
def puncturedNeighborhood := (centers f)ᶜ
theorem inclusion_not_mem_interiors x :
    inclusion f x ∉ interiors f := by
  simp [interiors, interiorMap, inclusion]
  simp [interiorRepresentative]
theorem quotient_inl_not_mem_centers x :
    quotientMap f (.inl x) ∉ centers f := fun ⟨_,h⟩ =>
  inclusion_not_mem_interiors f x ⟨_, h⟩
variable {f} in
theorem quotient_inr_mem_centers {i} {z} :
    quotientMap f (.inr ⟨i, z⟩) ∈ centers f ↔ z.1 = 0 := by
  change (∃ j, quotientMap f (interiorRepresentative j ⟨0, by simp⟩) = _) ↔ _
  simp only [interiorRepresentative_quotient_eq_iff]
  aesop (add simp [interiorRepresentative, Subtype.ext_iff])
/-- The punctured neighborhood is open, with no separation assumptions on the original space. -/
theorem neighborhood_isOpen : IsOpen (puncturedNeighborhood f) := by
  rw [puncturedNeighborhood, isOpen_compl_iff, ← (quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage]
  simp [quotient_inr_mem_centers, quotient_inl_not_mem_centers, isClosed_sum_iff, isClosed_sigma_iff, Set.preimage,
    isClosed_eq continuous_subtype_val continuous_const]
/-- The disjoint union of disk interiors is homeomorphic to the actual
interior subspace, with its induced quotient topology. -/
def interiorsHomeomorph :=
  (interiorMap_isOpenEmbedding f).isEmbedding.toHomeomorph

/-! Ordinary van Kampen descent, using finite chains of local path transports. -/
open Set

def line (x y : Icc (a : ℝ) b) : Path x y where
  toFun := Icc.convexComb x y
  source' := by simp
  target' := by simp

variable {s : Set X} {x y : X} (F : FundamentalGroupoid s ⥤ SingleObj G) (p : ContinuousMap unitInterval X)

def restrictPath (p : Path x y) (h : range p ⊆ s) :
    Path (⟨x, h p.source_mem_range⟩ : s) ⟨y, h p.target_mem_range⟩ where
  toFun t := ⟨p t, h (mem_range_self t)⟩
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target



abbrev subpath a b : Path (p a) (p b) := Path.subpath ⟨p,rfl,rfl⟩ a b

abbrev _root_.CategoryTheory.Functor.segment (hab : a ≤ b) (h : Icc a b ⊆ p ⁻¹' s) : G :=
  F.map (.mk (restrictPath (subpath p a b) (by
    rwa [Path.range_subpath, Set.uIcc_of_le hab, Set.image_subset_iff])))
lemma _root_.CategoryTheory.Functor.eval_subpath_trans
    (hab : a ≤ b) (hbc : b ≤ c) (h : Icc a c ⊆ p ⁻¹' s) :
    F.segment p (hab.trans hbc) h =
      F.segment p hbc (by grind) *
      F.segment p hab (by grind) := by
  let := (convex_Icc a.1 c).contractibleSpace ⟨b, hab, hbc⟩
  let L := FundamentalGroupoid.map {toFun t := (⟨p (ContinuousMap.inclusion (Icc_subset_Icc a.2.1 c.2.2) t), h t.2⟩ : s)} ⋙ F
  exact (L.congr_map (Subsingleton.elim
    (Path.Homotopic.Quotient.mk (line ⟨a,le_rfl,hab.trans hbc⟩ ⟨c,hab.trans hbc,le_rfl⟩)) _)).trans
    (L.map_comp (.mk (line _ ⟨b,hab,hbc⟩)) (.mk (line _ _)))



structure Cover (U : Bool → Set X) where
  patch : ∀ i, FundamentalGroupoid (U i) ⥤ SingleObj G
  isOpen : ∀ i, IsOpen (U i)
  covers : ∀ x, ∃ i, x ∈ U i
  agree : ∀ {x y} (p : Path x y) hi hj,
    (patch false).map (.mk (restrictPath p hi)) = (patch true).map (.mk (restrictPath p hj))

namespace Cover
variable {U : Bool → Set X} (T : Cover (G := G) U) {p : ContinuousMap unitInterval X}

inductive Chain (p : ContinuousMap unitInterval X) : unitInterval → unitInterval → G → Prop
  | step hab i (h : Icc a b ⊆ p ⁻¹' U i) :
      Chain p a b ((T.patch i).segment p hab h)
  | comp {f g} : Chain p a b f → Chain p b c g → Chain p a c (g * f)

variable {T} {f g : G}
lemma Chain.le (h : T.Chain p a b f) : a ≤ b := by
  induction h <;> order

lemma Chain.in_chart (hc : T.Chain p a b f)
    hab i (h : Icc a b ⊆ p ⁻¹' U i) :
    f = (T.patch i).segment p hab h := by
  induction hc <;> grind [T.agree, cases Bool, Functor.eval_subpath_trans, → Chain.le]

lemma Chain.split (hc : T.Chain p a b f)
    (hac : a ≤ c) (hcb : c ≤ b) :
    ∃ f₁ f₂, T.Chain p a c f₁ ∧ T.Chain p c b f₂ ∧ f = f₂ * f₁ := by
  induction hc with
  | step hab i h =>
    refine ⟨_, _, .step hac i ?_, .step hcb i ?_, ?_⟩ <;>
      grind [Functor.eval_subpath_trans]
  | comp => grind [→ Chain.comp, le_total]

lemma Chain.unique
    (hf : T.Chain p a b f) (hg : T.Chain p a b g) : f = g := by
  induction hf generalizing g <;> grind [Chain.in_chart, → Chain.split, → Chain.le]
variable (p T)

abbrev curveValue a b := Classical.epsilon (T.Chain p a b)

lemma curveValue_spec (hab : a ≤ b) :
    T.Chain p a b (T.curveValue p a b) := by
  apply Classical.epsilon_spec
  obtain ⟨t, ht, hm, ⟨n, hn⟩, hs⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun i => (T.isOpen i).preimage p.continuous) (fun x _ => mem_iUnion.mpr (T.covers (p x)))
  have H n : ∃ f, T.Chain p (t 0) (t n) f := by
    induction n with
    | zero =>
      obtain ⟨i, hi⟩ := T.covers (p (t 0))
      exact ⟨_, .step le_rfl i (by simpa using hi)⟩
    | succ n ih =>
      exact ⟨_, ih.choose_spec.comp (.step (hm (Nat.le_succ _)) _ (hs n).choose_spec)⟩
  specialize H n
  simp only [ht, hn n le_rfl] at H
  have : 0 ≤ a := bot_le
  grind [→ Chain.split, unitInterval.le_one']

def pathValue (p : Path x y) := T.curveValue p.toContinuousMap 0 1

lemma pathValue_local (p : Path x y) i h :
    T.pathValue p = (T.patch i).map (.mk (restrictPath p h)) := by
  rcases p with ⟨p,rfl,rfl⟩
  simpa [Functor.segment, restrictPath, subpath, pathValue] using (T.curveValue_spec p zero_le_one).in_chart zero_le_one i
    (fun t _ => h (mem_range_self t))

@[simp] lemma curveValue_const x : T.curveValue {toFun _ := x} 0 1 = 1 := by
  obtain ⟨i, hi⟩ := T.covers x
  rw [(T.curveValue_spec _ zero_le_one).in_chart zero_le_one i (by simpa using hi)]
  apply CategoryTheory.Functor.map_id

variable (H : ContinuousMap (unitInterval × unitInterval) X)

def Comm a b c d :=
  T.curveValue ((H.comp .prodSwap).curry d) a b * T.curveValue (H.curry a) c d =
    T.curveValue (H.curry b) c d * T.curveValue ((H.comp .prodSwap).curry c) a b

lemma Comm.local (hab : a ≤ b) (hcd : c ≤ d)
    i (h : Icc a b ×ˢ Icc c d ⊆ H ⁻¹' U i) : T.Comm H a b c d := by
  unfold Comm
  repeat rw [(T.curveValue_spec _ ‹_›).in_chart ‹_› i (fun t ht => h (by aesop))]
  have he := Path.Homotopic.map_trans_evalAt
    ((ContinuousMap.Homotopy.refl {toFun z := (⟨H (ContinuousMap.inclusion (Icc_subset_Icc a.2.1 b.2.2) z.1, ContinuousMap.inclusion (Icc_subset_Icc c.2.1 d.2.2) z.2), h ⟨z.1.2, z.2.2⟩⟩ : U i)}).comp
      ((line ⟨a,le_rfl,hab⟩ ⟨b,hab,le_rfl⟩).toHomotopyConst.prodMk (ContinuousMap.Homotopy.refl (.id _)))) (line ⟨c,le_rfl,hcd⟩ ⟨d,hcd,le_rfl⟩)
  simpa [Functor.segment, ← FundamentalGroupoid.comp_eq, SingleObj.comp_as_mul] using!
    (T.patch i).congr_map (Path.Homotopic.Quotient.eq.mpr he)
def classValue : Path.Homotopic.Quotient x y → G :=
  Quotient.lift T.pathValue (fun p q h => by
    let H := h.some.toContinuousMap
    obtain ⟨t, ht, hm, ⟨n, hn⟩, hs⟩ := exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => (T.isOpen i).preimage H.continuous) (fun x _ => mem_iUnion.mpr (T.covers (H x)))
    have hv i : T.Comm H (t 0) (t i) (t 0) (t n) := by
      induction i
      case' succ i ih =>
        have h₂ : T.Comm H (t i) (t (i + 1)) (t 0) (t n) := ?_
        swap
        clear hn ih
        induction n
        case' succ j ih =>
          obtain ⟨k, hk⟩ := hs i j
          have h₂ := Comm.local T H (hm (Nat.le_succ i)) (hm (Nat.le_succ j)) k hk
      all_goals grind [Comm, → Chain.unique, → Chain.comp, curveValue_spec, Monotone, mul_eq_left]
    unfold Comm ContinuousMap.curry Function.curry at hv
    simpa [ht, hn n le_rfl, H] using! hv n)

end Cover

/-- The actual intersection of the two quotient open sets. -/
def overlap :=
  puncturedNeighborhood f ∩ interiors f
/-- Jointly continuous radial expansion, staying within the punctured disk. -/
def radialDeformation : ContinuousMap (unitInterval × PuncturedDisk) PuncturedDisk where
  toFun p :=
    let r : Set.Ioc (0 : ℝ) 1 :=
      ⟨AffineMap.lineMap ‖p.2.1.1‖ 1 p.1.1,
        by apply (convex_Ioc 0 1).lineMap_mem <;> aesop⟩
    ⟨⟨r.1 • (polar p.2).1, by
        simpa [abs_of_pos r.2.1] using r.2.2⟩,
      by simp [r.2.1.ne']⟩
  continuous_toFun := by
    continuity

/-- The actual inclusion, codomain-restricted to the punctured neighborhood. -/
abbrev neighborhoodInclusion : ContinuousMap X (puncturedNeighborhood f) where
  toFun x := ⟨inclusion f x, quotient_inl_not_mem_centers f x⟩


/-- The retraction and radial paths descend together through the adjunction relation. -/
def quotientData :=
  let b x := (x, ContinuousMap.const unitInterval (neighborhoodInclusion f x))
  Quot.lift (r := AttachingRel f) (fun
    | .inl x => b x
    | .inr ⟨i,z⟩ => if h : z.1 ≠ 0 then
      (f i (polar ⟨z,h⟩),
        {toFun t := let r := radialDeformation (t, ⟨z,h⟩)
          ⟨characteristic f i r.1, quotient_inr_mem_centers.not.mpr r.property⟩})
      else b (f i 1)) (by
    rintro _ _ ⟨i,z⟩
    ext t <;> simp [b, polar, boundaryInclusion, NormedSpace.normalize,
      radialDeformation, characteristic, neighborhoodInclusion, inclusion, quotientMap]
    exact Quot.sound (AttachingRel.boundary (f := f) i z))

/-- Both descended constructions are jointly continuous away from the centers. -/
def neighborhoodData :=
  ContinuousMap.mk (fun y : puncturedNeighborhood f => quotientData f y.1) (by
    apply continuousOn_iff_continuous_domRestrict.mp
    have ho := neighborhood_isOpen f
    rw [(quotientMap_isQuotientMap f).continuousOn_isOpen_iff ho,
      (ho.preimage (quotientMap f).continuous).continuousOn_iff]
    rintro (x | ⟨i,z⟩) ha
    · apply Topology.IsOpenEmbedding.inl.continuousAt_iff.mp
      dsimp [quotientData, quotientMap]
      fun_prop
    · have hz := quotient_inr_mem_centers.not.mp ha
      apply Topology.IsOpenEmbedding.inr.continuousAt_iff.mp
      apply Topology.IsOpenEmbedding.sigmaMk.continuousAt_iff.mp
      apply ((isOpen_ne.preimage continuous_subtype_val).isOpenEmbedding_subtypeVal.continuousAt_iff
        (x := ⟨z,hz⟩)).mp
      apply Continuous.continuousAt
      simp [quotientMap, Function.comp_def, (fun z : PuncturedDisk => z.2)]
      constructor
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        dsimp
        fun_prop)
def neighborhoodRetraction := ContinuousMap.fst.comp (neighborhoodData f)
def overlapHomeomorph :=
  let h :=
    Sigma.map id (fun _ z => (annulusPolarHomeomorph.symm z).1)
  have he : Topology.IsEmbedding h :=
    (Topology.isEmbedding_sigmaMap Function.injective_id).mpr fun _ =>
      Topology.IsEmbedding.subtypeVal.comp annulusPolarHomeomorph.symm.isEmbedding
  ((interiorMap_isOpenEmbedding f).isEmbedding.comp he).codRestrict (overlap f)
    (fun z => ⟨quotient_inr_mem_centers.not.mpr (annulusPolarHomeomorph.symm z.2).2, h z,rfl⟩)
    |>.toHomeomorphOfSurjective (by
      rintro ⟨_,hy,⟨⟨i,z⟩,rfl⟩⟩
      refine ⟨⟨i,annulusPolarHomeomorph ⟨z,quotient_inr_mem_centers.not.mp hy⟩⟩, ?_⟩
      simp [h, Set.codRestrict, Sigma.map])

/-- The neighborhood retraction on the overlap is exactly the original attaching map
applied to the polar coordinate, not an abstract homotopic replacement. -/
lemma neighborhoodRetraction_overlap_coordinates
    z :
    neighborhoodRetraction f
      (ContinuousMap.inclusion (s := overlap f) Set.inter_subset_left (overlapHomeomorph f ⟨i, z⟩)) = f i z.1 :=
  (congrArg Prod.fst (dite_eq_left (annulusPolarHomeomorph.symm z).2)).trans
    (congrArg (f i ∘ Prod.fst) (annulusPolarHomeomorph.apply_symm_apply z))
/-- The cell index of an actual interior point. -/
def interiorIndex :=
  Sigma.fst ∘ (interiorsHomeomorph f).symm
/-- Every actual interior groupoid arrow lies within a single disk component. -/
lemma interiorIndex_arrow {a b}
    (γ : Path.Homotopic.Quotient a b) : interiorIndex f a = interiorIndex f b := by
  simpa using!
    (IsLocallyConstant.comp_continuous isOpen_sigma_fst_preimage
      ((interiorsHomeomorph f).symm.continuous.comp γ.out.continuous)).apply_eq_of_preconnectedSpace 0 1
variable {i} in
def coproductFundamentalGroupEquiv {A} [TopologicalSpace A] {a} :=
  (FundamentalGroup.map (ContinuousMap.sigmaMk (X := fun _ => A) i) a).toMulEquiv
    (FundamentalGroup.map (ContinuousMap.sigma fun _ => ContinuousMap.id A) ⟨i, a⟩)
    (by ext ⟨p⟩; rfl) (by
      ext ⟨p⟩
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      · simpa using
          (IsLocallyConstant.comp_continuous isOpen_sigma_fst_preimage
            p.continuous).apply_eq_of_preconnectedSpace 0 t
      · rfl)
/-- The radial deformation descends jointly continuously to the actual neighborhood. -/
def neighborhoodDeformation :
    ContinuousMap.Homotopy (ContinuousMap.id (puncturedNeighborhood f))
      ((neighborhoodInclusion f).comp (neighborhoodRetraction f)) := by
  refine {
    toFun p := (neighborhoodData f p.2).2 p.1
    map_zero_left := ?_
    map_one_left := ?_ }
  all_goals
    rintro ⟨⟨x | ⟨i,z⟩⟩,hy⟩ <;> apply Subtype.ext
    · rfl
    · have hz := quotient_inr_mem_centers.not.mp hy
      simp [neighborhoodInclusion, neighborhoodRetraction, neighborhoodData, quotientData, hz,
        characteristic, inclusion, quotientMap, radialDeformation, polar,
        -Complex.real_smul]
      all_goals exact (Quot.sound (AttachingRel.boundary (f := f) i (polar ⟨z,hz⟩)))
/-- The original space is genuinely homotopy equivalent to the punctured neighborhood. -/
def neighborhoodHomotopyEquiv :=
  ContinuousMap.HomotopyEquiv.mk (neighborhoodInclusion f) (neighborhoodRetraction f)
    (by rfl) ⟨(neighborhoodDeformation f).symm⟩

/-- The actual attaching loop in X, whiskered chronologically from the basepoint
along a chosen path, around the attaching circle once, and back. -/
def attachingLoop :=
  (γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)
/-- Its class in Mathlib's ordinary continuous-path fundamental group. -/
def attachingLoopClass : FundamentalGroup X x₀ :=
  .mk (attachingLoop f x₀ γ i)
/-- Precisely the normal subgroup generated by the chosen conjugated attaching loops. -/
def attachingNormalClosure :=
  Subgroup.normalClosure (Set.range (attachingLoopClass f x₀ γ))
instance attachingNormalClosure_normal : (attachingNormalClosure f x₀ γ).Normal := by
  unfold attachingNormalClosure
  infer_instance
/-- The full arbitrary-family two-cell attachment theorem, including compatibility
of the quotient equivalence with the actual inclusion-induced map. The index
universe and the space universe are independent. -/
def completeStatement :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {ι : Type v}
    (f : ι → ContinuousMap Circle X) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)),
    Function.Surjective (inclusionPi1 f x₀) ∧
    (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ ∧
    ∃ e : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀

theorem two_cell_attachment : completeStatement.{u,v} := by
  intro X _ _ ι f x₀ γ
  classical
  let B := puncturedNeighborhood f
  let C := interiors f
  let D := interiorsHomeomorph f
  let A := overlapHomeomorph f
  let i := FundamentalGroupoid.map (ContinuousMap.inclusion (s := overlap f) Set.inter_subset_left)
  let k := FundamentalGroupoid.map (ContinuousMap.inclusion (s := overlap f) Set.inter_subset_right)
  let j := FundamentalGroupoid.map (ContinuousMap.subtypeVal B)
  let l := FundamentalGroupoid.map (ContinuousMap.subtypeVal C)
  let x := FundamentalGroupoid.mk (neighborhoodInclusion f x₀)
  let J := j.mapEnd x
  let indexC := interiorIndex f ∘ FundamentalGroupoid.as
  let indexA := indexC ∘ k.obj
  let anchor n := FundamentalGroupoid.mk (A ⟨n, annulusBasepoint⟩)
  let qA : ∀ w, anchor (indexA w) ⟶ w := by
    rintro ⟨w⟩
    apply Path.Homotopic.Quotient.mk
    apply Classical.choice
    obtain ⟨⟨n,z⟩,rfl⟩ := A.surjective w
    refine ⟨((PathConnectedSpace.somePath annulusBasepoint z).map
      (A.continuous.comp continuous_sigmaMk)).cast ?_ rfl⟩
    exact congrArg (fun z => (anchor z.1).as)
      (D.symm_apply_apply ⟨n,(annulusPolarHomeomorph.symm z).1⟩)
  let R := (FundamentalGroupoidFunctor.equivOfHomotopyEquiv (neighborhoodHomotopyEquiv f)).symm
  let p' n : x ⟶ i.obj (anchor n) := R.fullyFaithfulFunctor.preimage
    (.mk ((γ n).cast rfl (neighborhoodRetraction_overlap_coordinates f n annulusBasepoint)))
  let s y : k.obj (anchor (indexC y)) ⟶ y := .mk
    (((PathConnectedSpace.somePath _ (D.symm y.as).2).map
      (D.continuous.comp continuous_sigmaMk)).cast
      rfl (D.apply_symm_apply y.as).symm)
  let : Quiver.IsThin (FundamentalGroupoid C) := (Groupoid.isThin_iff _).mpr (fun w =>
    ((homotopyEquivFundamentalGroup D.symm.toHomotopyEquiv w.as).trans
      coproductFundamentalGroupEquiv.symm).injective.subsingleton)
  let qB w := p' (indexA w) ≫ i.map (qA w)
  let pB : ∀ y, x ⟶ y := fun y =>
    if hy : y.as.val ∈ C then
      qB (.mk ⟨y.as.val,y.as.property,hy⟩)
    else if e : x = y then eqToHom e else R.fullyFaithfulFunctor.preimage
      (.mk (PathConnectedSpace.somePath _ _))
  have hpB : pB x = 𝟙 x := by
    simp [C, pB, x, inclusion_not_mem_interiors]
  have hpres w : pB (i.obj w) = p' (indexA w) ≫ i.map (qA w) := dite_eq_left w.as.property.2
  let a n : _ ⟶ l.obj (k.obj (anchor n)) := by
    simpa using! j.map (p' n)
  have coord {n m} (h : n = m) {y}
      (g : k.obj (anchor n) ⟶ y) g' :
      a n ≫ l.map g = a m ≫ l.map g' := by cases h; congr!
  let c y := a (indexC y) ≫ l.map (s y)
  let r n : End (anchor n) := .mk (annulusGenerator.map
    (A.toHomotopyEquiv.toFun.comp (ContinuousMap.sigmaMk n)).continuous)
  let rel n := transportEnd (p' n) (i.map (r n))
  let N := Subgroup.normalClosure (Set.range rel)
  have hN : N ≤ J.ker :=
    Subgroup.normalClosure_le_normal (by
      rintro _ ⟨n,rfl⟩
      simp [J, rel, Functor.map_conj, show j.map (i.map (r n)) = 𝟙 _ from by
        simpa using! l.congr_map (Subsingleton.elim (k.map (r n)) (𝟙 _))])
  let q := QuotientGroup.mk' N
  have hc y : y ∈ B ∪ C := by
    grind [puncturedNeighborhood, centers, interiors]
  let t : ∀ y, j.obj x ⟶ y := fun y =>
    if hy : y.as ∈ C then c (.mk ⟨y.as,hy⟩)
    else j.map (pB (.mk ⟨y.as, (hc y.as).resolve_right hy⟩))
  have htj y : t (j.obj y) = j.map (pB y) := by
    dsimp [t]
    split_ifs with h
    · symm
      erw [hpres (.mk ⟨_,y.as.property,h⟩), j.map_comp]
      exact coord rfl (k.map (qA _)) _
    · rfl
  have htl y : t (l.obj y) = c y := dite_eq_left y.as.property
  let e := QuotientGroup.lift _ J hN
  have hcomm {y z} g :
      q (pB (i.obj y) ≫ i.map g ≫ inv (pB (i.obj z))) = 1 := by
    rw [hpres y, hpres z]
    generalize qA z = az
    generalize hz : indexA z = m at az ⊢
    cases hz.symm.trans (interiorIndex_arrow f (k.map g)).symm
    let n := indexA y
    let e := q.comp ((transportEnd (p' n)).toMonoidHom.comp (i.mapEnd (anchor n)))
    let eA := coproductFundamentalGroupEquiv.trans
      (homotopyEquivFundamentalGroup A.toHomotopyEquiv ⟨n, annulusBasepoint⟩)
    let hp := Circle.isAddQuotientCoveringMap_exp
    let d := (homotopyEquivFundamentalGroup annulusHomotopyEquivCircle annulusBasepoint).trans
      (hp.fundamentalGroupEquiv ⟨0, Circle.exp_zero⟩)
    have hd : d (.mk annulusGenerator) = .op (.ofAdd ⟨2 * Real.pi, AddSubgroup.mem_zmultiples _⟩) := by
      apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
      change _ = hp.isCoveringMap.liftPath circleGenerator.toContinuousMap 0 _ 1
      rw [← (hp.isCoveringMap.eq_liftPath_iff' (Γ := {toFun t := t.1 * (2 * Real.pi)}) _).mpr ⟨rfl, by simp⟩]
      simp
    let b := eA.symm (qA y ≫ g ≫ inv az)
    obtain ⟨m, hm⟩ := (MulOpposite.unop (d b)).toAdd.property
    have hm : (.mk annulusGenerator) ^ m = b := by
      apply d.injective
      erw [map_zpow, hd]
      apply MulOpposite.unop_injective
      ext
      simpa using hm
    have he : e (eA (.mk annulusGenerator)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_range_self n))
    have H := congrArg e (congrArg eA hm)
    simp [he] at H
    simpa [b, e, MonoidHom.comp_apply, transportEnd, Iso.conj_apply] using! H.symm
  let T : Cover (Bool.rec B C) :=
    ⟨Bool.rec (basedFunctor pB q) ((Functor.const _).obj .unit), Bool.rec (neighborhood_isOpen f) (interiorMap_isOpenEmbedding f).isOpen_range,
      by simpa using hc, fun p hs ht =>
      hcomm (.mk (restrictPath p (subset_inter hs ht)))⟩
  let E := basedFunctor t (MonoidHom.id _)
  have cmp {y z} (p : Path y z) : e (T.pathValue p) = E.map (.mk p) := by
    rcases p with ⟨p,rfl,rfl⟩
    have hm {a b g} (hc : T.Chain p a b g) :
        E.map (Path.Homotopic.Quotient.mk (subpath p a b)) = e g := by
      induction hc with
      | step hab b hi =>
        let r := restrictPath (subpath p _ _) (by
          rwa [Path.range_subpath, Set.uIcc_of_le hab, Set.image_subset_iff])
        cases b
        · change E.map (j.map (.mk r)) = j.map (pB _ ≫ .mk r ≫ inv (pB _))
          simp [E, basedFunctor, htj]
        · change t (l.obj _) ≫ l.map (.mk r) ≫ inv (t (l.obj _)) = e 1
          have hn := coord (interiorIndex_arrow f (.mk r)) (s _ ≫ .mk r) (s _)
          simp [htl, c, indexC, ← Category.assoc] at hn ⊢
          simp [hn]
      | comp _ _ ihf ihg =>
        erw [← Path.Homotopic.mk_subpath_trans_mk_subpath ⟨p,rfl,rfl⟩ _ _ _,
          ← FundamentalGroupoid.comp_eq, E.map_comp, ihf, ihg, e.map_mul]
        rfl
    simpa only [subpath, Path.subpath_zero_one, Path.cast_rfl_rfl, Cover.pathValue] using
      (hm (T.curveValue_spec p zero_le_one)).symm
  have hs : Function.RightInverse T.classValue e := by
    rintro ⟨p⟩
    simpa [E, basedFunctor, htj, hpB] using! cmp p
  have hi : Function.LeftInverse T.classValue e := by
    rintro ⟨⟨p⟩⟩
    change T.pathValue _ = _
    rw [T.pathValue_local _ false (Set.range_subset_iff.mpr fun t => (p t).property)]
    change q (pB x ≫ .mk p ≫ inv (pB x)) = _
    rw [hpB, IsIso.inv_id, Category.comp_id, Category.id_comp]
    rfl
  have hk := ((QuotientGroup.injective_lift_iff N _ hN).mp hi.injective).symm
  have hs := hs.surjective.comp (QuotientGroup.mk'_surjective N)
  let e := R.symm.fullyFaithfulFunctor.mulEquivEnd ⟨x₀⟩
  have h n : e (attachingLoopClass f x₀ γ n) = rel n := by
    apply R.fullyFaithfulFunctor.map_injective
    simp [rel, p', transportEnd, Iso.conj_apply]
    rw [← Groupoid.inv_eq_inv]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    simp [A, attachingLoop, Path.trans_apply, annulusGenerator,
      neighborhoodRetraction_overlap_coordinates, neighborhoodHomotopyEquiv,
      -ContinuousMap.HomotopyEquiv.coe_invFun]
    rfl
  simp only [N, ← funext h] at hk
  have hk := congrArg (Subgroup.comap e.toMonoidHom) hk
  rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.comap_ker, ← Subgroup.comap_normalClosure _ e,
    Set.range_comp', Set.preimage_image_eq _ e.injective] at hk
  rw [← show J.comp e.toMonoidHom = inclusionPi1 f x₀ from by
    ext ⟨p⟩; rfl]
  have hs := hs.comp e.surjective
  exact ⟨hs,hk,QuotientGroup.liftEquiv _ hs hk.symm, rfl⟩
end CellAttachment
