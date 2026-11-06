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
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Constructions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Equiv
@[expose] public section
section CellAttachment_Geometry
noncomputable section
open scoped unitInterval ContinuousMap
open Topology unitInterval
namespace CellAttachment
universe u v
abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
def boundaryInclusion : C(Circle, Disk) := ⟨fun z => ⟨z, le_of_eq (Circle.norm_coe z)⟩, by fun_prop⟩
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop
def circleGeneratorClass : FundamentalGroup Circle 1 := .mk circleGenerator
abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
  (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1))
inductive AttachingRel : Raw X ι → Raw X ι → Prop
  | boundary (i : ι) (z : Circle) :
      AttachingRel (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
def Space := Quot (AttachingRel f)
instance : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))
def quotientMap : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩
def inclusion : C(X, Space f) :=
  ⟨fun x => quotientMap f (.inl x), (quotientMap f).continuous.comp continuous_inl⟩
def characteristic (i : ι) : C(Disk, Space f) :=
  ⟨fun z => quotientMap f (.inr ⟨i, z⟩),
   (quotientMap f).continuous.comp (continuous_inr.comp continuous_sigmaMk)⟩
@[simp] theorem characteristic_boundary (i : ι) (z : Circle) :
    characteristic f i (boundaryInclusion z) = inclusion f (f i z) :=
  Quot.sound (.boundary i z)
theorem quotientMap_isQuotientMap :
    IsQuotientMap (quotientMap f) := isQuotientMap_quot_mk
def inclusionPi1 :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀
def attachingLoop (i : ι) : Path x₀ x₀ :=
  (γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)
def attachingLoopClass : ι → FundamentalGroup X x₀ :=
  fun i => .mk (attachingLoop f x₀ γ i)
def attachingNormalClosure : Subgroup (FundamentalGroup X x₀) :=
  Subgroup.normalClosure (Set.range (attachingLoopClass f x₀ γ))
instance attachingNormalClosure_normal : (attachingNormalClosure f x₀ γ).Normal := by
  unfold attachingNormalClosure
  infer_instance
def completeStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {ι : Type v}
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)),
    Function.Surjective (inclusionPi1 f x₀) ∧
    (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ ∧
    ∃ e : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀

variable {f x₀ γ}

abbrev OpenDisk := {z : ℂ // ‖z‖ < 1}
def openDiskCenter : OpenDisk := ⟨0, by simp⟩
def rawInteriorMap : C((Σ _ : ι, OpenDisk), Raw X ι) :=
  ⟨fun z => .inr ⟨z.1, z.2.1, z.2.2.le⟩,
   continuous_sigma fun _ => continuous_inr.comp (continuous_sigmaMk.comp (continuous_subtype_val.subtype_mk _))⟩
def rawInteriorCoord : Raw X ι → Option (Σ _ : ι, OpenDisk)
  | .inl _ => none
  | .inr ⟨i, z⟩ => if h : ‖(z : ℂ)‖ < 1 then some ⟨i, ⟨z, h⟩⟩ else none
def interiorCoord : Space f → Option (Σ _ : ι, OpenDisk) :=
  Quot.lift rawInteriorCoord (by
    rintro _ _ ⟨i, z⟩
    change (if h : ‖(z : ℂ)‖ < 1 then _ else none) = none
    exact dite_eq_right (by rw [Circle.norm_coe]; exact lt_irrefl 1))
lemma eq_interiorRepresentative_of_rawInteriorCoord {a : Raw X ι} {w : Σ _ : ι, OpenDisk}
    (h : rawInteriorCoord a = some w) : a = rawInteriorMap w := by
  rcases a with x | ⟨i, z⟩
  · cases h
  · change (if hz : ‖(z : ℂ)‖ < 1 then some ⟨i, ⟨z, hz⟩⟩ else none) = some w at h
    split_ifs at h with hz
    cases h; rfl

theorem circleGenerator_generates (g : FundamentalGroup Circle 1) :
    ∃ n : ℤ, circleGeneratorClass ^ n = g := by
  let hp := Circle.isAddQuotientCoveringMap_exp
  let e : Circle.exp ⁻¹' {(1 : Circle)} := ⟨0, Circle.exp_zero⟩
  let φ := hp.fundamentalGroupToMulOpposite e
  have hgen : φ circleGeneratorClass =
      .op (.ofAdd ⟨2 * Real.pi, AddSubgroup.mem_zmultiples (2 * Real.pi)⟩) := by
    rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
    have hlift : (⟨fun t : I => (t : ℝ) * (2 * Real.pi), by fun_prop⟩ : C(I, ℝ)) =
        hp.isCoveringMap.liftPath circleGenerator e (by simp [e]) :=
      (hp.isCoveringMap.eq_liftPath_iff' _).mpr ⟨rfl, by simp [e]⟩
    change (2 * Real.pi : ℝ) + 0 =
      hp.isCoveringMap.liftPath circleGenerator e (by simp [e]) 1
    rw [← hlift]; simp
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (φ g).unop.toAdd.2
  refine ⟨n, hp.fundamentalGroupToMulOpposite_injective e ?_⟩
  rw [map_zpow, hgen]
  apply MulOpposite.unop_injective
  apply Multiplicative.toAdd.injective
  ext; simpa [zsmul_eq_mul] using hn

abbrev PuncturedDisk := {z : Disk // (z : ℂ) ≠ 0}
abbrev pCoord (z : PuncturedDisk) : ℂ := z.1
lemma punctured_norm_pos (z : PuncturedDisk) : 0 < ‖pCoord z‖ :=
  norm_pos_iff.mpr z.2
def polar : C(PuncturedDisk, Circle) :=
  ⟨fun z => ⟨(‖pCoord z‖⁻¹ : ℝ) • pCoord z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (punctured_norm_pos z).ne']⟩, by
    have : ∀ z : PuncturedDisk, ‖pCoord z‖ ≠ 0 := fun z => (punctured_norm_pos z).ne'
    refine Continuous.subtype_mk ?_ _; fun_prop (disch := assumption)⟩

abbrev Annulus := {z : OpenDisk // (z : ℂ) ≠ 0}
def annulusPolar : C(Annulus, Circle) :=
  polar.comp ⟨fun z => ⟨⟨z.1.1, z.1.2.le⟩, z.2⟩, by fun_prop⟩
def annulusBasepoint : Annulus := ⟨⟨1 / 2, by norm_num⟩, by norm_num⟩
@[simp] lemma annulusPolar_basepoint : annulusPolar annulusBasepoint = 1 := by
  ext; change (‖(1 / 2 : ℂ)‖⁻¹ : ℝ) • (1 / 2 : ℂ) = 1; norm_num
def annulusPath (z : Annulus) : Path annulusBasepoint z :=
  let p := PathConnectedSpace.somePath 1 (annulusPolar z)
  have hr0 (t : I) : 0 < (1 - (t : ℝ)) / 2 + (t : ℝ) * ‖(z.1 : ℂ)‖ := by
    nlinarith [t.2.1, t.2.2, z.1.2, norm_pos_iff.mpr z.2]
  ⟨⟨fun t => ⟨⟨((1 - (t : ℝ)) / 2 + (t : ℝ) * ‖(z.1 : ℂ)‖) • (p t : ℂ), by
      rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe, mul_one, abs_of_pos (hr0 t)]
      nlinarith [t.2.1, t.2.2, z.1.2, norm_pos_iff.mpr z.2]⟩,
    smul_ne_zero (hr0 t).ne' (Circle.coe_ne_zero _)⟩, by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _; fun_prop⟩,
   by ext; simp [p, annulusBasepoint],
   by apply Subtype.ext; apply Subtype.ext
      change ((1 - (1 : ℝ)) / 2 + (1 : ℝ) * ‖(z.1 : ℂ)‖) • (p 1 : ℂ) = z.1
      rw [p.target]; change _ • ((‖(z.1 : ℂ)‖⁻¹ : ℝ) • (z.1 : ℂ)) = _
      rw [smul_smul]; simp [mul_inv_cancel₀ (norm_pos_iff.mpr z.2).ne']⟩
instance : ContractibleSpace OpenDisk :=
  (by simpa [Metric.ball] using convex_ball (0 : ℂ) 1 :
    Convex ℝ {z : ℂ | ‖z‖ < 1}).contractibleSpace ⟨0, by simp⟩
instance : ContractibleSpace Disk :=
  (by simpa [Metric.closedBall] using convex_closedBall (0 : ℂ) 1 :
    Convex ℝ {z : ℂ | ‖z‖ ≤ 1}).contractibleSpace ⟨0, by simp⟩
instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, zero_mem⟩

variable (f) in
def interiorMap : C((Σ _ : ι, OpenDisk), Space f) :=
  (quotientMap f).comp rawInteriorMap
theorem interiorMap_isOpenEmbedding :
    IsOpenEmbedding (interiorMap f) := by
  refine .of_continuous_injective_isOpenMap (interiorMap f).continuous (fun a b h => ?_) (fun S hS => ?_)
  · exact Option.some.inj ((dite_eq_left a.2.2).symm.trans
      ((congrArg interiorCoord h).trans (dite_eq_left b.2.2)))
  · rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
    have hpre : (quotientMap f) ⁻¹' (interiorMap f '' S) = rawInteriorMap '' S := by
      ext a
      refine ⟨fun ⟨z, hz, heq⟩ => ⟨z, hz, (eq_interiorRepresentative_of_rawInteriorCoord
        ((congrArg interiorCoord heq.symm).trans (dite_eq_left z.2.2))).symm⟩,
        fun ⟨z, hz, h⟩ => ⟨z, hz, h ▸ rfl⟩⟩
    rw [hpre]
    have hopen := (isOpen_lt continuous_norm continuous_const).isOpenMap_subtype_val.subtype_mk
      (p := fun z : ℂ => ‖z‖ ≤ 1) fun z => z.2.le
    exact (isOpenMap_sigma.mpr fun _ => isOpenMap_inr.comp
      (isOpenMap_sigmaMk.comp hopen) : IsOpenMap rawInteriorMap) S hS

variable (f) in
def interiors : Set (Space f) := Set.range (interiorMap f)
def interiorsHomeomorph : (Σ _ : ι, OpenDisk) ≃ₜ interiors f :=
  interiorMap_isOpenEmbedding.isEmbedding.toHomeomorph
theorem interiors_isOpen : IsOpen (interiors f) :=
  interiorMap_isOpenEmbedding.isOpen_range
variable (f) in
def centers : Set (Space f) :=
  {y | ∃ i : ι, interiorCoord y = some ⟨i, openDiskCenter⟩}
variable (f) in
def puncturedNeighborhood : Set (Space f) := (centers f)ᶜ
@[simp] theorem inclusion_not_mem_interiors (x : X) :
    inclusion f x ∉ interiors f := by
  rintro ⟨z, h⟩
  cases (congrArg interiorCoord h).symm.trans (dite_eq_left z.2.2)
@[simp] theorem inclusion_not_mem_centers (x : X) :
    inclusion f x ∉ centers f := by rintro ⟨_, ⟨⟩⟩
@[simp] theorem quotient_inr_mem_centers (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ centers f ↔ (z : ℂ) = 0 := by
  change (∃ j, rawInteriorCoord (X := X) (.inr ⟨i, z⟩) = some ⟨j, openDiskCenter⟩) ↔ _
  by_cases h : ‖(z : ℂ)‖ < 1
  · simp [rawInteriorCoord, h, openDiskCenter, Subtype.ext_iff]
  · refine ⟨by simp [rawInteriorCoord, h], fun hz => (h (by simp [hz])).elim⟩
theorem centers_isClosed : IsClosed (centers f) := by
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage, isClosed_sum_iff]
  refine ⟨by convert isClosed_empty; ext; exact ⟨by rintro ⟨_, ⟨⟩⟩, False.elim⟩,
    isClosed_sigma_iff.mpr fun i => ?_⟩
  convert isClosed_eq continuous_subtype_val
    (continuous_const : Continuous fun _ : Disk => (0 : ℂ)) using 1
  ext z; simp
theorem puncturedNeighborhood_isOpen :
    IsOpen (puncturedNeighborhood f) := centers_isClosed.isOpen_compl
theorem openCover_mem (y : Space f) :
    y ∈ puncturedNeighborhood f ∨ y ∈ interiors f := by
  obtain ⟨a, rfl⟩ := (quotientMap_isQuotientMap f).surjective y
  by_cases h : quotientMap f a ∈ centers f
  · obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨⟨i, openDiskCenter⟩,
      (congrArg (quotientMap f) (eq_interiorRepresentative_of_rawInteriorCoord hi)).symm⟩
  · exact Or.inl h

variable (f) in
abbrev overlap : Set (Space f) :=
  puncturedNeighborhood f ∩ interiors f
abbrev overlapLeft : C(overlap f, puncturedNeighborhood f) :=
  ⟨fun y => ⟨y.1, y.2.1⟩, continuous_subtype_val.subtype_mk _⟩
abbrev overlapRight : C(overlap f, interiors f) :=
  ⟨fun y => ⟨y.1, y.2.2⟩, continuous_subtype_val.subtype_mk _⟩
abbrev neighborhoodToSpace : C(puncturedNeighborhood f, Space f) :=
  ⟨Subtype.val, continuous_subtype_val⟩
abbrev interiorsToSpace : C(interiors f, Space f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def radialCoefficient (t : I) (z : PuncturedDisk) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * ‖pCoord z‖⁻¹
lemma radialCoefficient_pos (t : I) (z : PuncturedDisk) :
    0 < radialCoefficient t z := by
  have := mul_le_mul_of_nonneg_left ((one_le_inv₀ (punctured_norm_pos z)).mpr z.1.2) t.2.1
  unfold radialCoefficient; linarith
def radialDeformation (t : I) (z : PuncturedDisk) : PuncturedDisk :=
  ⟨⟨radialCoefficient t z • pCoord z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialCoefficient_pos t z),
        radialCoefficient, add_mul, mul_assoc, inv_mul_cancel₀ (punctured_norm_pos z).ne']
      nlinarith [t.2.1, t.2.2, z.1.2]⟩,
    smul_ne_zero (radialCoefficient_pos t z).ne' z.2⟩
lemma radialDeformation_continuous :
    Continuous (fun p : I × PuncturedDisk => radialDeformation p.1 p.2) := by
  have : ∀ p : I × PuncturedDisk, ‖pCoord p.2‖ ≠ 0 :=
    fun p => (punctured_norm_pos p.2).ne'
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  unfold radialCoefficient; fun_prop (disch := assumption)
@[simp] lemma radialDeformation_zero (z : PuncturedDisk) : radialDeformation 0 z = z := by
  ext; simp [radialDeformation, radialCoefficient]
@[simp] lemma radialDeformation_one_coordinate (z : PuncturedDisk) :
    (radialDeformation 1 z).1.1 = (polar z : ℂ) := by
  change radialCoefficient 1 z • pCoord z = ‖pCoord z‖⁻¹ • pCoord z
  simp [radialCoefficient]
lemma radialDeformation_boundary_fixed (t : I) (z : PuncturedDisk)
    (h : ‖pCoord z‖ = 1) : radialDeformation t z = z := by
  apply Subtype.ext; apply Subtype.ext
  change radialCoefficient t z • pCoord z = pCoord z
  simp [radialCoefficient, h]
@[simp] lemma polar_radialDeformation (t : I) (z : PuncturedDisk) :
    polar (radialDeformation t z) = polar z := by
  apply Circle.ext
  change (‖radialCoefficient t z • pCoord z‖⁻¹ : ℝ) •
    (radialCoefficient t z • pCoord z) = (‖pCoord z‖⁻¹ : ℝ) • pCoord z
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialCoefficient_pos t z), smul_smul]
  congr 1
  field_simp [(radialCoefficient_pos t z).ne', (punctured_norm_pos z).ne']

abbrev PuncturedRaw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, PuncturedDisk)
def puncturedRawInclusion : PuncturedRaw X ι → Raw X ι :=
  Sum.map id (Sigma.map id fun _ => Subtype.val)
lemma puncturedRawInclusion_isOpenEmbedding :
    IsOpenEmbedding (puncturedRawInclusion : PuncturedRaw X ι → Raw X ι) := by
  have hs : IsOpenEmbedding (Sigma.map id (fun _ : ι => Subtype.val) :
      (Σ _ : ι, PuncturedDisk) → (Σ _ : ι, Disk)) :=
    (isOpenEmbedding_sigmaMap Function.injective_id).mpr fun _ =>
      (isOpen_ne.preimage continuous_subtype_val).isOpenEmbedding_subtypeVal
  exact .of_continuous_injective_isOpenMap (continuous_id.sumMap hs.continuous)
    (Sum.map_injective.mpr ⟨Function.injective_id, hs.injective⟩)
    (IsOpenMap.id.sumMap hs.isOpenMap)
lemma puncturedRawInclusion_mem (a : PuncturedRaw X ι) :
    quotientMap f (puncturedRawInclusion a) ∈ puncturedNeighborhood f := by
  rcases a with x | ⟨i, z⟩
  · exact inclusion_not_mem_centers x
  · change quotientMap f (.inr ⟨i, z.1⟩) ∉ centers f
    rw [quotient_inr_mem_centers]; exact z.2
variable (f) in
def puncturedQuotient : C(PuncturedRaw X ι, puncturedNeighborhood f) :=
  ⟨fun a => ⟨quotientMap f (puncturedRawInclusion a), puncturedRawInclusion_mem a⟩,
   Continuous.subtype_mk
     ((quotientMap f).2.comp puncturedRawInclusion_isOpenEmbedding.continuous) _⟩
lemma puncturedQuotient_isQuotientMap :
    IsQuotientMap (puncturedQuotient f) :=
  ((quotientMap_isQuotientMap f).restrictPreimage_isOpen puncturedNeighborhood_isOpen).comp
    ((⟨fun a => ⟨puncturedRawInclusion a, puncturedRawInclusion_mem a⟩,
       fun | ⟨.inl x, _⟩ => .inl x
           | ⟨.inr ⟨i, z⟩, h⟩ => .inr ⟨i, ⟨z, (quotient_inr_mem_centers i z).not.mp h⟩⟩,
       fun a => by cases a <;> rfl,
       by rintro ⟨a, _⟩; cases a <;> rfl⟩ :
       PuncturedRaw X ι ≃ (quotientMap f ⁻¹' puncturedNeighborhood f)).toHomeomorphOfIsInducing
      (puncturedRawInclusion_isOpenEmbedding.isEmbedding.codRestrict _
        puncturedRawInclusion_mem).isInducing).isQuotientMap

@[simp] lemma polar_boundary (z : Circle) :
    polar ⟨boundaryInclusion z, Circle.coe_ne_zero z⟩ = z := by
  apply Circle.ext; change (‖(z : ℂ)‖⁻¹ : ℝ) • (z : ℂ) = z; simp
variable (x₀) in
def quotientRetraction : Space f → X :=
  Quot.lift (fun
    | .inl x => x
    | .inr ⟨i, z⟩ => if h : (z : ℂ) ≠ 0 then f i (polar ⟨z, h⟩) else x₀) (by
    rintro _ _ ⟨i, z⟩
    change (if h : (z : ℂ) ≠ 0 then f i (polar ⟨boundaryInclusion z, h⟩) else x₀) = f i z
    rw [dite_eq_left (Circle.coe_ne_zero z), polar_boundary])
lemma quotientRetraction_puncturedQuotient (a : PuncturedRaw X ι) :
    quotientRetraction x₀ (puncturedQuotient f a).1 =
      Sum.elim id (fun z : Σ _ : ι, PuncturedDisk => f z.1 (polar z.2)) a := by
  rcases a with x | z <;> [rfl; exact dite_eq_left z.2.2]
variable (x₀) in
def neighborhoodRetraction : C(puncturedNeighborhood f, X) :=
  ⟨fun y => quotientRetraction x₀ y.1,
   puncturedQuotient_isQuotientMap.continuous_iff.mpr <| by
     have h : Continuous (Sum.elim id (fun z : Σ _ : ι, PuncturedDisk => f z.1 (polar z.2))) :=
       continuous_id.sumElim (continuous_sigma fun i => (f i).2.comp polar.2)
     simpa only [Function.comp_def, quotientRetraction_puncturedQuotient] using h⟩
variable (f) in
abbrev neighborhoodInclusion : C(X, puncturedNeighborhood f) :=
  ⟨fun x => ⟨inclusion f x, inclusion_not_mem_centers x⟩,
    (inclusion f).2.subtype_mk _⟩

@[simp] lemma interiorMap_mem_puncturedNeighborhood_iff (i : ι) (z : OpenDisk) :
    interiorMap f ⟨i, z⟩ ∈ puncturedNeighborhood f ↔ (z : ℂ) ≠ 0 := by
  change quotientMap f (.inr ⟨i, ⟨z, z.2.le⟩⟩) ∉ centers f ↔ _
  simp only [quotient_inr_mem_centers]
variable (f) in
def cellAnnulusToOverlap (i : ι) : C(Annulus, overlap f) :=
  ⟨fun z => ⟨interiorMap f ⟨i, z.1⟩,
    (interiorMap_mem_puncturedNeighborhood_iff i z.1).mpr z.2, ⟨⟨i, z.1⟩, rfl⟩⟩,
   Continuous.subtype_mk
     ((interiorMap f).2.comp (continuous_sigmaMk.comp continuous_subtype_val)) _⟩
def overlapToAnnulus : C(overlap f, Annulus) :=
  ⟨fun w => ⟨(interiorsHomeomorph.symm (overlapRight w)).2,
    (interiorMap_mem_puncturedNeighborhood_iff _ _).mp
      (congrArg Subtype.val (interiorsHomeomorph.apply_symm_apply (overlapRight w)).symm ▸ w.2.1)⟩,
   Continuous.subtype_mk
     ((continuous_sigma fun _ => continuous_id).comp
       (interiorsHomeomorph.symm.continuous.comp overlapRight.2)) _⟩
abbrev interiorIndex (z : interiors f) : ι :=
  (interiorsHomeomorph.symm z).1
abbrev overlapIndex (w : overlap f) : ι :=
  interiorIndex (overlapRight w)
@[simp] lemma interiorIndex_coordinates (z : Σ _ : ι, OpenDisk) :
    interiorIndex (interiorsHomeomorph (f := f) z) = z.1 := by
  simp [interiorIndex]
lemma interiorIndex_path {a b : interiors f}
    (p : Path a b) (t : I) : interiorIndex (p t) = interiorIndex a := by
  have h := (IsLocallyConstant.comp_continuous (fun S => isOpen_sigma_fst_preimage S)
    (interiorsHomeomorph.symm.continuous.comp p.continuous)).apply_eq_of_preconnectedSpace t 0
  simpa only [Function.comp_apply, p.source] using h
lemma overlapIndex_path {a b : overlap f}
    (p : Path a b) (t : I) : overlapIndex (p t) = overlapIndex a :=
  interiorIndex_path (p.map overlapRight.2) t
variable (f) in
def overlapAnchor (i : ι) : overlap f :=
  cellAnnulusToOverlap f i annulusBasepoint
def overlapAnchorPaths (w : overlap f) :
    Path (overlapAnchor f (overlapIndex w)) w :=
  ((annulusPath (overlapToAnnulus w)).map
    (cellAnnulusToOverlap f (overlapIndex w)).2).cast rfl
    (Subtype.ext (congrArg (Subtype.val : interiors f → Space f)
      (interiorsHomeomorph.apply_symm_apply (overlapRight w)).symm))
def interiorAnchorPaths (v : interiors f) :
    Path (overlapRight (overlapAnchor f (interiorIndex v))) v :=
  ((PathConnectedSpace.somePath annulusBasepoint.1 (interiorsHomeomorph.symm v).2).map
    (interiorsHomeomorph.continuous.comp (continuous_sigmaMk (i := interiorIndex v)))).cast
      rfl (interiorsHomeomorph.apply_symm_apply v).symm
@[simp] lemma neighborhoodRetraction_overlapAnchor (i : ι) :
    neighborhoodRetraction x₀ (overlapLeft (overlapAnchor f i)) = f i 1 := by
  change (if h : (annulusBasepoint.1 : ℂ) ≠ 0 then
    f i (polar ⟨⟨annulusBasepoint.1, annulusBasepoint.1.2.le⟩, h⟩) else x₀) = f i 1
  rw [dite_eq_left annulusBasepoint.2]
  exact congrArg (f i) annulusPolar_basepoint

def quotientRadial (t : I) : Space f → Space f :=
  Quot.map (fun
    | .inl x => .inl x
    | .inr ⟨i, z⟩ => if h : (z : ℂ) ≠ 0 then .inr ⟨i, (radialDeformation t ⟨z, h⟩).1⟩
        else .inr ⟨i, z⟩) (by
    rintro _ _ ⟨i, z⟩
    change AttachingRel f
      (if h : (z : ℂ) ≠ 0 then .inr ⟨i, (radialDeformation t ⟨boundaryInclusion z, h⟩).1⟩
        else .inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
    rw [dite_eq_left (Circle.coe_ne_zero z),
      radialDeformation_boundary_fixed t _ (Circle.norm_coe z)]
    exact .boundary i z)
lemma quotientRadial_puncturedQuotient (t : I) (a : PuncturedRaw X ι) :
    quotientRadial t (puncturedQuotient f a).1 =
      (puncturedQuotient f (Sum.map id (Sigma.map id fun _ => radialDeformation t) a)).1 := by
  rcases a with x | ⟨i, z⟩
  · rfl
  · change quotientMap f (if h : (z.1 : ℂ) ≠ 0 then _ else _) = _
    rw [dite_eq_left z.2]; rfl
def neighborhoodRadial (t : I) (y : puncturedNeighborhood f) : puncturedNeighborhood f :=
  ⟨quotientRadial t y.1, by
    obtain ⟨a, rfl⟩ := puncturedQuotient_isQuotientMap.surjective y
    rw [quotientRadial_puncturedQuotient]
    exact (puncturedQuotient f _).2⟩
lemma neighborhoodRadial_puncturedQuotient (t : I) (a : PuncturedRaw X ι) :
    neighborhoodRadial t (puncturedQuotient f a) =
      puncturedQuotient f (Sum.map id (Sigma.map id fun _ => radialDeformation t) a) :=
  Subtype.ext (quotientRadial_puncturedQuotient t a)
lemma neighborhoodRadial_continuous :
    Continuous (fun p : I × puncturedNeighborhood f => neighborhoodRadial p.1 p.2) := by
  apply puncturedQuotient_isQuotientMap.continuous_lift_prod_right
  simp only [neighborhoodRadial_puncturedQuotient]
  have hs : Continuous (fun p : Σ _ : ι, PuncturedDisk × I =>
      puncturedQuotient f (.inr ⟨p.1, radialDeformation p.2.2 p.2.1⟩)) :=
    continuous_sigma fun _ => (puncturedQuotient f).continuous.comp
      (continuous_inr.comp (continuous_sigmaMk.comp
        (radialDeformation_continuous.comp continuous_swap)))
  convert ((by fun_prop : Continuous fun p : I × X => puncturedQuotient f (.inl p.2)).sumElim
    (hs.comp ((Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib).continuous)).comp
      Homeomorph.prodSumDistrib.continuous using 1
  ext ⟨t, a⟩; cases a <;> rfl
@[simp] lemma neighborhoodRadial_zero (y : puncturedNeighborhood f) :
    neighborhoodRadial 0 y = y := by
  obtain ⟨a, rfl⟩ := puncturedQuotient_isQuotientMap.surjective y
  rcases a with x | ⟨i, z⟩ <;> simp [neighborhoodRadial_puncturedQuotient, Sigma.map]
lemma neighborhoodRadial_one (y : puncturedNeighborhood f) :
    neighborhoodRadial 1 y = neighborhoodInclusion f (neighborhoodRetraction x₀ y) := by
  obtain ⟨a, rfl⟩ := puncturedQuotient_isQuotientMap.surjective y
  rcases a with x | ⟨i, z⟩
  · rfl
  · refine Subtype.ext ?_
    change quotientRadial 1 (puncturedQuotient f (.inr ⟨i, z⟩)).1 =
      inclusion f (quotientRetraction x₀ (puncturedQuotient f (.inr ⟨i, z⟩)).1)
    rw [quotientRadial_puncturedQuotient, quotientRetraction_puncturedQuotient]
    dsimp; rw [← characteristic_boundary f i (polar z)]
    exact congrArg (characteristic f i) (Subtype.ext (radialDeformation_one_coordinate z))
@[simp] theorem neighborhoodRadial_inclusion (t : I) (x : X) :
    neighborhoodRadial t (neighborhoodInclusion f x) = neighborhoodInclusion f x := rfl
@[simp] theorem neighborhoodRetraction_radial (t : I) (y : puncturedNeighborhood f) :
    neighborhoodRetraction x₀ (neighborhoodRadial t y) = neighborhoodRetraction x₀ y := by
  obtain ⟨a, rfl⟩ := puncturedQuotient_isQuotientMap.surjective y
  rcases a with x | ⟨i, z⟩
  · rfl
  · change quotientRetraction x₀ (neighborhoodRadial t (puncturedQuotient f (.inr ⟨i, z⟩))).1 =
      quotientRetraction x₀ (puncturedQuotient f (.inr ⟨i, z⟩)).1
    rw [neighborhoodRadial_puncturedQuotient, quotientRetraction_puncturedQuotient,
      quotientRetraction_puncturedQuotient]
    exact congrArg (f i) (polar_radialDeformation t z)

set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory Path.Homotopic.Quotient
abbrev PQuot := @Path.Homotopic.Quotient

lemma sub_cover_or {Y : Type*} {g : Y → Space f} {S : Set Y}
    (h : ∃ b : Bool, S ⊆ if b then g ⁻¹' puncturedNeighborhood f else g ⁻¹' interiors f) :
    (∀ x ∈ S, g x ∈ puncturedNeighborhood f) ∨ (∀ x ∈ S, g x ∈ interiors f) := by
  rcases h with ⟨_ | _, hb⟩ <;> [exact Or.inr hb; exact Or.inl hb]

variable {Y : Type*} [TopologicalSpace Y]

def subPath {S : Set Y} {a b : Y}
    (s : Path a b) (hs : ∀ t, s t ∈ S) :
    Path (⟨a, s.source ▸ hs 0⟩ : S) ⟨b, s.target ▸ hs 1⟩ :=
  ⟨⟨fun t => ⟨s t, hs t⟩, s.continuous.subtype_mk hs⟩, Subtype.ext s.source, Subtype.ext s.target⟩

instance interiors_quotient_subsingleton (u v : interiors f) :
    Subsingleton (PQuot u v) :=
  ⟨by
    rintro ⟨p₁⟩ ⟨p₂⟩
    let h := interiorsHomeomorph (f := f)
    let proj (p : Path u v) : Path (h.symm u).2 (h.symm v).2 :=
      p.map ((continuous_sigma fun _ => continuous_id).comp h.symm.continuous)
    let emb : C(OpenDisk, interiors f) :=
      ⟨fun z => h ⟨interiorIndex u, z⟩, h.continuous.comp continuous_sigmaMk⟩
    have hpt (p : Path u v) (t : I) : ((proj p).map emb.continuous) t = p t := by
      change h ⟨interiorIndex u, (h.symm (p t)).2⟩ = p t
      rw [← interiorIndex_path p t]; exact h.apply_symm_apply (p t)
    have hrec (p : Path u v) : p = ((proj p).map emb.continuous).cast
        (p₁.source ▸ (hpt p₁ 0).symm) (p₁.target ▸ (hpt p₁ 1).symm) := by
      ext t; exact congrArg Subtype.val (hpt p t).symm
    rw [hrec p₁, hrec p₂]
    exact Quotient.sound ((SimplyConnectedSpace.paths_homotopic (proj p₁) (proj p₂)).map emb)⟩

@[simp] lemma quotient_symm_trans_cancel {a b c : Y}
    (p : PQuot a b) (q : PQuot b c) : p.symm.trans (p.trans q) = q := by
  rw [← trans_assoc, symm_trans, refl_trans]

@[simp] lemma quotient_trans_symm_cancel {a b c : Y}
    (p : PQuot a b) (q : PQuot a c) : p.trans (p.symm.trans q) = q := by
  rw [← trans_assoc, trans_symm, refl_trans]

@[simp] lemma quotient_symm_trans {a b c : Y}
    (p : PQuot a b) (q : PQuot b c) : (p.trans q).symm = q.symm.trans p.symm :=
  Quotient.ind₂ (fun _ _ => congrArg mk (Path.trans_symm _ _)) p q

def overlapPolar : C(overlap f, Circle) :=
  annulusPolar.comp overlapToAnnulus

@[simp] lemma overlapPolar_anchor (i : ι) :
    overlapPolar (overlapAnchor f i) = 1 := by
  change annulusPolar ⟨(interiorsHomeomorph.symm
    (interiorsHomeomorph (f := f) ⟨i, annulusBasepoint.1⟩)).2, _⟩ = 1
  simp [interiorsHomeomorph.symm_apply_apply]

lemma neighborhoodRetraction_overlapLeft (w : overlap f) :
    neighborhoodRetraction x₀ (overlapLeft w) =
      f (overlapIndex w) (overlapPolar w) := by
  let z := interiorsHomeomorph.symm (overlapRight w)
  have hw : w.1 = interiorMap f z :=
    congrArg Subtype.val (interiorsHomeomorph.apply_symm_apply (overlapRight w)).symm
  change quotientRetraction x₀ w.1 = f z.1 (annulusPolar ⟨z.2, _⟩)
  rw [hw]; exact dite_eq_left (overlapToAnnulus w).2

def retractPi1 :
    FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) →*
      FundamentalGroup X x₀ :=
  FundamentalGroup.map (neighborhoodRetraction x₀) (neighborhoodInclusion f x₀)

def radialAnchorPath (y : puncturedNeighborhood f)
    (p : Path x₀ (neighborhoodRetraction x₀ y)) :
    Path (neighborhoodInclusion f x₀) y :=
  (p.map (neighborhoodInclusion f).continuous).trans
    (Path.symm ⟨⟨fun t => neighborhoodRadial t y,
      neighborhoodRadial_continuous.comp (continuous_id.prodMk continuous_const)⟩,
      neighborhoodRadial_zero y, neighborhoodRadial_one y⟩)

lemma radialAnchorPath_retraction_class
    (y : puncturedNeighborhood f) (p : Path x₀ (neighborhoodRetraction x₀ y)) :
    mk ((radialAnchorPath y p).map (neighborhoodRetraction x₀).continuous) = mk p := by
  have h : (radialAnchorPath y p).map (neighborhoodRetraction x₀).continuous =
      p.trans (Path.refl _) := by
    rw [radialAnchorPath, Path.map_trans]; congr 1; ext t; simp
  rw [h, mk_trans, mk_refl, trans_refl]

variable (γ) in
def chosenAnchorPath (i : ι) :
    Path (neighborhoodInclusion f x₀) (overlapLeft (overlapAnchor f i)) :=
  radialAnchorPath (overlapLeft (overlapAnchor f i))
    ((γ i).cast rfl (neighborhoodRetraction_overlapAnchor i))

lemma pathFn_congr {α : Type*} (F : ∀ {a b : Y}, Path a b → α)
    {a b a' b' : Y} (s : Path a b) (s' : Path a' b') (h : ∀ u, s u = s' u) : F s = F s' := by
  have ha : a = a' := s.source.symm.trans ((h 0).trans s'.source)
  have hb : b = b' := s.target.symm.trans ((h 1).trans s'.target)
  subst ha hb; obtain rfl : s = s' := Path.ext (funext h); rfl

def seg1D (a b : I) : Path a b :=
  ⟨⟨Set.Icc.convexComb a b, by fun_prop⟩, by simp, by simp⟩

def seg2D (p q : I × I) : Path p q :=
  ⟨⟨fun t => (Set.Icc.convexComb p.1 q.1 t, Set.Icc.convexComb p.2 q.2 t), by fun_prop⟩,
   by ext <;> simp, by ext <;> simp⟩

abbrev segPath2D (H : C(I × I, Y)) (p q : I × I) :
    Path (H p) (H q) :=
  (seg2D p q).map H.continuous

def IsProdConvex (R : Set (I × I)) : Prop :=
  ∀ ⦃p q⦄, p ∈ R → q ∈ R → ∀ t : I, seg2D p q t ∈ R

lemma convexComb_mem_Icc {a b x y : I} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (t : I) :
    Set.Icc.convexComb x y t ∈ Set.Icc a b := by
  change (a : ℝ) ≤ _ ∧ (_ : ℝ) ≤ b at hx hy ⊢
  rw [Set.Icc.coe_convexComb]
  constructor <;> nlinarith [t.2.1, t.2.2]

lemma isProdConvex_Icc_prod (a₁ b₁ a₂ b₂ : I) :
    IsProdConvex (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂) := by
  rintro _ _ ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ t
  exact ⟨convexComb_mem_Icc hx₁ hy₁ t, convexComb_mem_Icc hx₂ hy₂ t⟩

lemma pullbackCover (g : C(Y, Space f)) :
    (∀ b : Bool, IsOpen (if b then g ⁻¹' puncturedNeighborhood f else g ⁻¹' interiors f)) ∧
      Set.univ ⊆ ⋃ b : Bool, if b then g ⁻¹' puncturedNeighborhood f else g ⁻¹' interiors f :=
  ⟨by rintro (_ | _) <;> [exact interiors_isOpen.preimage g.2;
        exact puncturedNeighborhood_isOpen.preimage g.2],
   fun x _ => by
     rcases openCover_mem (g x) with hU | hV
     · exact Set.mem_iUnion.mpr ⟨true, hU⟩
     · exact Set.mem_iUnion.mpr ⟨false, hV⟩⟩

def segPath1D {x y : Y} (p : Path x y) (a b : I) :
    Path (p a) (p b) :=
  (seg1D a b).map p.continuous

variable [PathConnectedSpace X]

variable (γ) in
def pathU (u : puncturedNeighborhood f) : Path (neighborhoodInclusion f x₀) u :=
  if hV : u.1 ∈ interiors f then
    (chosenAnchorPath γ (overlapIndex ⟨u.1, u.2, hV⟩)).trans
      ((overlapAnchorPaths ⟨u.1, u.2, hV⟩).map overlapLeft.continuous)
  else if hx : u = neighborhoodInclusion f x₀ then
    (Path.refl _).cast rfl hx
  else
    radialAnchorPath u (PathConnectedSpace.somePath x₀ (neighborhoodRetraction x₀ u))

@[simp] lemma pathU_self :
    pathU γ (neighborhoodInclusion f x₀) = Path.refl (neighborhoodInclusion f x₀) := by
  unfold pathU
  split_ifs with hV hx
  · exact (inclusion_not_mem_interiors x₀ hV).elim
  · rfl
  · exact (hx rfl).elim

lemma pathU_of_mem_interiors (w : overlap f) {i : ι} (hi : overlapIndex w = i) :
    ∃ α : Path (overlapAnchor f i) w,
      pathU γ ⟨w.1, w.2.1⟩ =
        (chosenAnchorPath γ i).trans (α.map overlapLeft.continuous) := by
  subst hi; exact ⟨overlapAnchorPaths w, dite_eq_left w.2.2⟩

variable (γ) in
def ΦU {a b : Space f} (s : Path a b) (hs : ∀ t, s t ∈ puncturedNeighborhood f) :
    FundamentalGroup (puncturedNeighborhood f) (neighborhoodInclusion f x₀) :=
  mk ((pathU γ ⟨a, s.source ▸ hs 0⟩).trans
    ((subPath s hs).trans (pathU γ ⟨b, s.target ▸ hs 1⟩).symm))

variable (γ) in
abbrev qMk := QuotientGroup.mk' (attachingNormalClosure f x₀ γ)

variable (γ) in
def ψ {a b : Space f} (s : Path a b) :
    FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ :=
  if hU : ∀ t, s t ∈ puncturedNeighborhood f then
    qMk γ (retractPi1 (ΦU γ s hU))
  else 1

lemma ψ_of_mem_U {a b : Space f} {s : Path a b}
    (hU : ∀ t, s t ∈ puncturedNeighborhood f) :
    ψ γ s = qMk γ (retractPi1 (ΦU γ s hU)) :=
  dite_eq_left hU

lemma ψ_of_mem_V {a b : Space f} {s : Path a b}
    (hV : ∀ t, s t ∈ interiors f) : ψ γ s = 1 := by
  unfold ψ; split_ifs with hU
  · apply (QuotientGroup.eq_one_iff _).mpr
    let sW := subPath (S := overlap f) s fun t => ⟨hU t, hV t⟩
    let i := overlapIndex ⟨a, s.source ▸ hU 0, s.source ▸ hV 0⟩
    obtain ⟨α₁, hu₁⟩ := pathU_of_mem_interiors _ (rfl : _ = i)
    obtain ⟨α₂, hu₂⟩ := pathU_of_mem_interiors _
      (sW.target ▸ overlapIndex_path sW 1 : _ = i)
    let τ := α₁.trans (sW.trans α₂.symm)
    let ℓ : Path (1 : Circle) 1 :=
      (τ.map overlapPolar.continuous).cast (overlapPolar_anchor i).symm
        (overlapPolar_anchor i).symm
    have hτ : (τ.map overlapLeft.continuous).map (neighborhoodRetraction x₀).continuous =
        (ℓ.map (f i).continuous).cast (neighborhoodRetraction_overlapAnchor i)
          (neighborhoodRetraction_overlapAnchor i) := by
      ext t
      change neighborhoodRetraction x₀ (overlapLeft (τ t)) = f i (overlapPolar (τ t))
      rw [neighborhoodRetraction_overlapLeft, overlapIndex_path τ t,
        show overlapIndex (overlapAnchor f i) = i from
          interiorIndex_coordinates ⟨i, annulusBasepoint.1⟩]
    let P := (chosenAnchorPath γ i).trans
      ((τ.map overlapLeft.continuous).trans (chosenAnchorPath γ i).symm)
    have hΦ : ΦU γ s hU = mk P := by
      unfold ΦU; rw [hu₁, hu₂, show subPath s hU = sW.map overlapLeft.continuous from rfl]
      simp [P, τ, Path.map_trans, Path.map_symm, Path.trans_symm, mk_trans, mk_symm, trans_assoc]
    have hmap : retractPi1 (ΦU γ s hU) =
        (FundamentalGroup.fundamentalGroupMulEquivOfPath (γ i)).symm
          (FundamentalGroup.map (f i) 1 (mk ℓ)) := by
      rw [hΦ]
      change mk (P.map (neighborhoodRetraction x₀).continuous) =
        mk ((γ i).trans ((ℓ.map (f i).continuous).trans (γ i).symm))
      simp only [P, Path.map_trans, mk_trans, ← Path.map_symm, mk_symm,
        chosenAnchorPath, radialAnchorPath_retraction_class, hτ]
      rw [← mk_symm, ← mk_trans, ← mk_trans]; congr 1
    obtain ⟨n, hn⟩ := circleGenerator_generates (mk ℓ)
    rw [hmap, ← hn, map_zpow, map_zpow]
    exact zpow_mem (Subgroup.subset_normalClosure (Set.mem_range.mpr ⟨i, rfl⟩)) n
  · rfl

lemma ψ_map_inclusion (p : Path x₀ x₀) :
    ψ γ (p.map (inclusion f).continuous) = qMk γ (mk p) := by
  have hU : ∀ t, (p.map (inclusion f).continuous) t ∈ puncturedNeighborhood f :=
    fun t => inclusion_not_mem_centers (p t)
  have hΦ : ΦU γ (p.map (inclusion f).continuous) hU =
      mk (p.map (neighborhoodInclusion f).continuous) := by
    change mk ((pathU γ (neighborhoodInclusion f x₀)).trans
      ((p.map (neighborhoodInclusion f).continuous).trans
        (pathU γ (neighborhoodInclusion f x₀)).symm)) = _
    rw [pathU_self]; simp
  rw [ψ_of_mem_U hU, hΦ]; rfl

lemma ψ_of_const_basepoint {a b : Space f} {s : Path a b}
    (h : ∀ t, s t = inclusion f x₀) : ψ γ s = 1 :=
  (pathFn_congr (ψ γ) s ((Path.refl x₀).map (inclusion f).continuous) h).trans
    ((ψ_map_inclusion (Path.refl x₀)).trans (map_one _))

lemma ψ_seg2D_mul {H : C(I × I, Space f)} {R : Set (I × I)}
    (hR : IsProdConvex R)
    (hcov : (∀ x ∈ R, H x ∈ puncturedNeighborhood f) ∨ (∀ x ∈ R, H x ∈ interiors f))
    {p q r : I × I} (hp : p ∈ R) (hq : q ∈ R) (hr : r ∈ R) :
    ψ γ (segPath2D H q r) * ψ γ (segPath2D H p q) = ψ γ (segPath2D H p r) := by
  rcases hcov with hU | hV
  · have hpq : ∀ t, segPath2D H p q t ∈ puncturedNeighborhood f := fun t => hU _ (hR hp hq t)
    have hqr : ∀ t, segPath2D H q r t ∈ puncturedNeighborhood f := fun t => hU _ (hR hq hr t)
    have hpr : ∀ t, segPath2D H p r t ∈ puncturedNeighborhood f := fun t => hU _ (hR hp hr t)
    rw [ψ_of_mem_U hqr, ψ_of_mem_U hpq, ψ_of_mem_U hpr, ← map_mul, ← map_mul]
    congr 2
    let α := (seg2D p q).trans (seg2D q r)
    let β := seg2D p r
    have htrans_mem : ∀ u, α u ∈ R := by
      intro u; rw [Path.trans_apply]; split_ifs <;> [exact hR hp hq _; exact hR hq hr _]
    have hq_eq : (mk (subPath (segPath2D H p q) hpq)).trans (mk (subPath (segPath2D H q r) hqr)) =
        mk (subPath (segPath2D H p r) hpr) := by
      rw [← mk_trans, show (subPath (segPath2D H p q) hpq).trans (subPath (segPath2D H q r) hqr) =
        subPath (α.map H.continuous) (fun u => hU _ (htrans_mem u)) by
          ext u; change ((subPath _ _).trans (subPath _ _) u).1 = H (α u)
          rw [Path.trans_apply, Path.trans_apply]; split_ifs <;> rfl]
      exact Quotient.sound ⟨{
        toFun su := ⟨H (seg2D (α su.2) (β su.2) su.1), hU _ (hR (htrans_mem su.2) (hR hp hr su.2) su.1)⟩
        continuous_toFun := by
          refine Continuous.subtype_mk (H.2.comp ?_) _
          change Continuous fun su : I × I =>
            (Set.Icc.convexComb (α su.2).1 (β su.2).1 su.1,
             Set.Icc.convexComb (α su.2).2 (β su.2).2 su.1)
          fun_prop
        map_zero_left u := by ext; exact congrArg H (seg2D (α u) (β u)).source
        map_one_left u := by ext; exact congrArg H (seg2D (α u) (β u)).target
        prop' s u hu := by rcases hu with rfl | rfl <;> ext <;> simp [seg2D] }⟩
    change (ΦU _ _ _).trans (ΦU _ _ _) = _
    dsimp only [ΦU]
    simp only [mk_trans, mk_symm, trans_assoc, quotient_symm_trans_cancel]
    rw [← trans_assoc _ (mk (subPath (segPath2D H q r) hqr)), hq_eq]
  · rw [ψ_of_mem_V fun t => hV _ (hR hq hr t),
      ψ_of_mem_V fun t => hV _ (hR hp hq t),
      ψ_of_mem_V fun t => hV _ (hR hp hr t), mul_one]

theorem inclusionPi1_ker_le :
    (inclusionPi1 f x₀).ker ≤ attachingNormalClosure f x₀ γ := by
  intro g hg
  obtain ⟨p₀, rfl⟩ := mk_surjective g
  obtain ⟨H⟩ : (p₀.map (inclusion f).continuous).Homotopic (Path.refl (inclusion f x₀)) :=
    Quotient.exact (MonoidHom.mem_ker.mp hg)
  let Hmap : C(I × I, Space f) := H.toContinuousMap
  obtain ⟨t, ht0, htmono, ⟨M, hM⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (pullbackCover Hmap).1 (pullbackCover Hmap).2
  have hM1 : t M = 1 := hM M le_rfl
  let rowVal (n : ℕ) : ℕ → FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ :=
    Nat.rec 1 fun k acc => ψ γ (segPath2D Hmap (t n, t k) (t n, t (k + 1))) * acc
  have hrow_step (n k : ℕ) :
      ψ γ (segPath2D Hmap (t n, t k) (t (n + 1), t k)) * rowVal n k = rowVal (n + 1) k := by
    induction k with
    | zero =>
      change ψ γ (segPath2D Hmap (t n, t 0) (t (n + 1), t 0)) * 1 = 1
      rw [mul_one]
      refine ψ_of_const_basepoint fun u => ?_
      change (H.eval (Set.Icc.convexComb (t n) (t (n + 1)) u)) (Set.Icc.convexComb (t 0) (t 0) u) = _
      rw [ht0, Set.Icc.convexComb_eq]; exact (H.eval _).source
    | succ k ih =>
      change ψ γ (segPath2D Hmap (t n, t (k + 1)) (t (n + 1), t (k + 1))) *
        (ψ γ (segPath2D Hmap (t n, t k) (t n, t (k + 1))) * rowVal n k) =
        ψ γ (segPath2D Hmap (t (n + 1), t k) (t (n + 1), t (k + 1))) * rowVal (n + 1) k
      have hR := isProdConvex_Icc_prod (t n) (t (n + 1)) (t k) (t (k + 1))
      have hn := htmono (Nat.le_succ n)
      have hk := htmono (Nat.le_succ k)
      rw [← ih, ← mul_assoc, ← mul_assoc,
        ψ_seg2D_mul hR (sub_cover_or (hsub n k))
          ⟨⟨le_rfl, hn⟩, le_rfl, hk⟩ ⟨⟨le_rfl, hn⟩, hk, le_rfl⟩ ⟨⟨hn, le_rfl⟩, hk, le_rfl⟩,
        ψ_seg2D_mul hR (sub_cover_or (hsub n k))
          ⟨⟨le_rfl, hn⟩, le_rfl, hk⟩ ⟨⟨hn, le_rfl⟩, le_rfl, hk⟩ ⟨⟨hn, le_rfl⟩, hk, le_rfl⟩]
  have hrow_M (n : ℕ) : rowVal n M = rowVal 0 M := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [← ih, ← hrow_step n M, ψ_of_const_basepoint fun u => by
        change (H.eval (Set.Icc.convexComb (t n) (t (n + 1)) u)) (Set.Icc.convexComb (t M) (t M) u) = _
        rw [hM1, Set.Icc.convexComb_eq]; exact (H.eval _).target, one_mul]
  have hvalM (k : ℕ) : rowVal M k = 1 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change ψ γ _ * rowVal M k = 1
      rw [ih, mul_one]
      refine ψ_of_const_basepoint fun u => ?_
      change H (Set.Icc.convexComb (t M) (t M) u, _) = _
      rw [hM1, Set.Icc.convexComb_eq]; exact H.apply_one _
  have h0U : ∀ x ∈ Set.Icc (t 0) (t 0) ×ˢ Set.Icc (0 : I) 1, Hmap x ∈ puncturedNeighborhood f := by
    rintro ⟨x₁, x₂⟩ ⟨hx₁, _⟩
    rw [ht0, Set.Icc_self, Set.mem_singleton_iff] at hx₁; subst hx₁
    change H (0, x₂) ∈ puncturedNeighborhood f; rw [H.apply_zero]
    exact inclusion_not_mem_centers (p₀ x₂)
  have hrow0 (k : ℕ) : rowVal 0 k = ψ γ (segPath2D Hmap (t 0, 0) (t 0, t k)) := by
    induction k with
    | zero =>
      symm; refine ψ_of_const_basepoint fun u => ?_
      change (H.eval (Set.Icc.convexComb (t 0) (t 0) u)) (Set.Icc.convexComb 0 (t 0) u) = _
      rw [ht0, Set.Icc.convexComb_eq]; exact (H.eval _).source
    | succ k ih =>
      change ψ γ _ * rowVal 0 k = _
      rw [ih]
      have hm (s : I) : (t 0, s) ∈ Set.Icc (t 0) (t 0) ×ˢ Set.Icc (0 : I) 1 :=
        ⟨⟨le_rfl, le_rfl⟩, bot_le, le_top⟩
      exact ψ_seg2D_mul (isProdConvex_Icc_prod (t 0) (t 0) 0 1)
        (Or.inl h0U) (hm _) (hm _) (hm _)
  have hval0 : rowVal 0 M = qMk γ (mk p₀) := by
    rw [hrow0 M, pathFn_congr (ψ γ) _ (p₀.map (inclusion f).continuous) fun u => ?_,
      ψ_map_inclusion]
    change H (Set.Icc.convexComb (t 0) (t 0) u, Set.Icc.convexComb 0 (t M) u) = _
    rw [ht0, hM1, Set.Icc.convexComb_eq, Set.Icc.convexComb_zero_one]
    exact H.apply_zero u
  exact (QuotientGroup.eq_one_iff _).mp (hval0.symm.trans ((hrow_M M).symm.trans (hvalM M)))

variable (γ) in
def pathY (y : Space f) : Path (inclusion f x₀) y :=
  if hyU : y ∈ puncturedNeighborhood f then
    (pathU γ ⟨y, hyU⟩).map neighborhoodToSpace.continuous
  else
    let hyV : y ∈ interiors f := (openCover_mem y).resolve_left hyU
    (((chosenAnchorPath γ (interiorIndex ⟨y, hyV⟩)).map neighborhoodToSpace.continuous).trans
      ((interiorAnchorPaths ⟨y, hyV⟩).map interiorsToSpace.continuous))

@[simp] lemma pathY_self :
    pathY γ (inclusion f x₀) = Path.refl (inclusion f x₀) := by
  unfold pathY
  split_ifs with hxU
  · ext t; change (pathU γ (neighborhoodInclusion f x₀) t).1 = inclusion f x₀
    rw [pathU_self]; rfl
  · exact (hxU (inclusion_not_mem_centers x₀)).elim

lemma pathY_class_of_interior_path {y : Space f} (hyV : y ∈ interiors f) {i : ι}
    (q : Path (overlapRight (overlapAnchor f i)) ⟨y, hyV⟩) :
    mk (pathY γ y) =
      (mk ((chosenAnchorPath γ i).map neighborhoodToSpace.continuous)).trans
        (mk (q.map interiorsToSpace.continuous)) := by
  have hi : interiorIndex ⟨y, hyV⟩ = i :=
    (q.target ▸ interiorIndex_path q 1).trans (interiorIndex_coordinates ⟨i, annulusBasepoint.1⟩)
  subst hi
  unfold pathY; split_ifs with hyU
  · obtain ⟨α, hα⟩ := pathU_of_mem_interiors ⟨y, hyU, hyV⟩ rfl
    rw [hα, Path.map_trans, mk_trans]; congr 1
    exact congrArg (fun p : PQuot _ _ => p.map interiorsToSpace)
      (Subsingleton.elim (mk (α.map overlapRight.continuous)) (mk q))
  · rw [mk_trans]; congr 1
    exact congrArg (fun p : PQuot _ _ => p.map interiorsToSpace)
      (Subsingleton.elim (mk _) (mk q))

variable (γ) in
def ΦY {a b : Space f} (s : Path a b) : FundamentalGroup (Space f) (inclusion f x₀) :=
  (mk (pathY γ a)).trans ((mk s).trans (mk (pathY γ b)).symm)

abbrev inclU := FundamentalGroup.map neighborhoodToSpace (neighborhoodInclusion f x₀)

lemma pathY_segment_mem_range {a b : Space f} {s : Path a b}
    (hcov : (∀ t, s t ∈ puncturedNeighborhood f) ∨ (∀ t, s t ∈ interiors f)) :
    ΦY γ s ∈ inclU.range := by
  rcases hcov with hU | hV
  · refine ⟨ΦU γ s hU, ?_⟩
    unfold ΦU ΦY
    rw [show pathY γ a = _ from dite_eq_left (s.source ▸ hU 0),
        show pathY γ b = _ from dite_eq_left (s.target ▸ hU 1)]
    change mk (((pathU γ _).trans ((subPath s hU).trans (pathU γ _).symm)).map
      neighborhoodToSpace.continuous) = _
    simp [Path.map_trans, ← Path.map_symm]; rfl
  · suffices h1 : ΦY γ s = 1 by rw [h1]; exact Subgroup.one_mem _
    have haV : a ∈ interiors f := s.source ▸ hV 0
    have hbV : b ∈ interiors f := s.target ▸ hV 1
    let q_a := interiorAnchorPaths ⟨a, haV⟩
    let sV : Path (⟨a, haV⟩ : interiors f) ⟨b, hbV⟩ := subPath s hV
    change (mk (pathY γ a)).trans ((mk s).trans (mk (pathY γ b)).symm) =
      mk (Path.refl (inclusion f x₀))
    rw [pathY_class_of_interior_path haV q_a,
        pathY_class_of_interior_path hbV (q_a.trans sV),
        Path.map_trans, mk_trans, show sV.map interiorsToSpace.continuous = s from rfl]
    simp [trans_assoc]

theorem inclusionPi1_surjective :
    Function.Surjective (inclusionPi1 f x₀) := by
  let γ i := PathConnectedSpace.somePath x₀ (f i 1)
  have hsurjU : Function.Surjective (inclU (f := f) (x₀ := x₀)) := by
    intro g
    obtain ⟨ℓ, rfl⟩ := mk_surjective g
    obtain ⟨t, ht0, htmono, ⟨M, hM⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (pullbackCover ℓ.toContinuousMap).1 (pullbackCover ℓ.toContinuousMap).2
    have hind (k : ℕ) : ΦY γ (segPath1D ℓ 0 (t k)) ∈ inclU.range := by
      induction k with
      | zero =>
        rw [pathFn_congr (ΦY γ) _ (Path.refl (ℓ 0)) fun u => by
          change ℓ (Set.Icc.convexComb 0 (t 0) u) = ℓ 0; rw [ht0, Set.Icc.convexComb_eq]]
        convert Subgroup.one_mem _
        change ΦY γ (Path.refl (ℓ 0)) = mk (Path.refl (inclusion f x₀))
        simp [ΦY]
      | succ k ih =>
        have hmem (u : I) := convexComb_mem_Icc ⟨le_rfl, htmono (Nat.le_succ k)⟩
          ⟨htmono (Nat.le_succ k), le_rfl⟩ u
        have hcov := (sub_cover_or (hsub k)).imp (fun h u => h _ (hmem u)) (fun h u => h _ (hmem u))
        rw [show ΦY γ (segPath1D ℓ 0 (t (k + 1))) =
            ΦY γ (segPath1D ℓ (t k) (t (k + 1))) * ΦY γ (segPath1D ℓ 0 (t k)) by
          dsimp [ΦY]
          rw [show mk (segPath1D ℓ 0 (t (k + 1))) =
            (mk (segPath1D ℓ 0 (t k))).trans (mk (segPath1D ℓ (t k) (t (k + 1)))) by
            rw [← mk_trans]; unfold segPath1D; rw [← Path.map_trans]
            exact Quotient.sound ((SimplyConnectedSpace.paths_homotopic _ _).map ℓ.toContinuousMap)]
          simp [FundamentalGroup.mul_def, trans_assoc]]
        exact Subgroup.mul_mem _ (pathY_segment_mem_range hcov) ih
    have hM_mem := hind M
    rwa [pathFn_congr (ΦY γ) _ ℓ (fun u => by
      change ℓ (Set.Icc.convexComb 0 (t M) u) = ℓ u
      rw [hM M le_rfl, Set.Icc.convexComb_zero_one]),
      show ΦY γ ℓ = mk ℓ by
        change (mk (pathY γ (inclusion f x₀))).trans
          ((mk ℓ).trans (mk (pathY γ (inclusion f x₀))).symm) = mk ℓ
        rw [pathY_self, ← mk_symm]; simp] at hM_mem
  intro g
  obtain ⟨u, rfl⟩ := hsurjU g
  obtain ⟨α, rfl⟩ := mk_surjective u
  refine ⟨mk (α.map (neighborhoodRetraction x₀).2), ?_⟩
  exact congrArg inclU
    (Quotient.sound (Path.Homotopic.symm ⟨({
      toFun ts := neighborhoodRadial ts.1 (α ts.2)
      continuous_toFun := neighborhoodRadial_continuous.comp
        (continuous_fst.prodMk (α.continuous.comp continuous_snd))
      map_zero_left s := neighborhoodRadial_zero (α s)
      map_one_left s := neighborhoodRadial_one (α s)
      prop' t s hs := by
        rcases hs with rfl | rfl <;>
          [change neighborhoodRadial t (α 0) = α 0;
           change neighborhoodRadial t (α 1) = α 1] <;>
          [rw [show α 0 = _ from α.source]; rw [show α 1 = _ from α.target]] <;>
          exact neighborhoodRadial_inclusion t x₀ } :
      α.Homotopy ((α.map (neighborhoodRetraction x₀).2).map (neighborhoodInclusion f).2))⟩))

omit [PathConnectedSpace X] in
theorem attachingNormalClosure_le_ker :
    attachingNormalClosure f x₀ γ ≤ (inclusionPi1 f x₀).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i, rfl⟩
  apply MonoidHom.mem_ker.mpr
  change mk (((γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)).map
    (inclusion f).continuous) = mk (Path.refl (inclusion f x₀))
  simp only [Path.map_trans, mk_trans, ← Path.map_symm, mk_symm]
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic
    (circleGenerator.map boundaryInclusion.continuous) (Path.refl (boundaryInclusion 1))
  rw [show mk ((circleGenerator.map (f i).continuous).map (inclusion f).continuous) =
      mk (Path.refl (inclusion f (f i 1))) from
    Quotient.sound ⟨{
      toContinuousMap := (characteristic f i).comp H.toContinuousMap
      map_zero_left t := by simp [characteristic_boundary]
      map_one_left t := by simp [characteristic_boundary]
      prop' s t ht := by rcases ht with rfl | rfl <;> simp [characteristic_boundary] }⟩]
  simp

theorem two_cell_attachment : completeStatement.{u,v} := by
  intro X _ _ ι f x₀ γ
  have hk := le_antisymm (inclusionPi1_ker_le (γ := γ)) attachingNormalClosure_le_ker
  exact ⟨inclusionPi1_surjective, hk,
    QuotientGroup.liftEquiv _ inclusionPi1_surjective hk.symm, rfl⟩

end CellAttachment
end
end CellAttachment_Geometry
