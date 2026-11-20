/-
Attaching arbitrary families of two-cells. Original construction and statement by
Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
Released under Apache-2.0.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Tactic

@[expose] public noncomputable section
open unitInterval Set
namespace CellAttachment
universe u v
abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
def boundaryInclusion : C(Circle, Disk) where
  toFun z := ⟨z, le_of_eq (Circle.norm_coe z)⟩
  continuous_toFun := by fun_prop
abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
inductive AttachingRel (f : ι → C(Circle, X)) : Raw X ι → Raw X ι → Prop
  | boundary (i : ι) (z : Circle) :
      AttachingRel f (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))
variable (f : ι → C(Circle,X))
def Space := Quot (AttachingRel f)
instance : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))
def quotientMap : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩
def inclusion : C(X, Space f) where
  toFun x := quotientMap f (.inl x)
  continuous_toFun := (quotientMap f).continuous.comp continuous_inl
def characteristic (i : ι) : C(Disk, Space f) where
  toFun z := quotientMap f (.inr ⟨i, z⟩)
  continuous_toFun := (quotientMap f).continuous.comp
    (continuous_inr.comp (continuous_sigmaMk (i := i)))
@[simp] theorem characteristic_boundary (i : ι) (z : Circle) :
    characteristic f i (boundaryInclusion z) = inclusion f (f i z) :=
  Quot.sound (.boundary i z)
def inclusionPi1 (x₀ : X) :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop
variable (x₀ : X) (γ : ∀ i, Path x₀ (f i 1))
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

-- The closed disk is convex, hence contractible.
instance : ContractibleSpace Disk :=
  (Set.sep_univ.subst ((convexOn_univ_norm (E := ℂ)).convex_le 1)).contractibleSpace ⟨0, by simp⟩

/- Fundamental group generator argument adapted from Ruize Chen's
FundamentalGroupCircle and Junyan Xu's homotopy lifting (Apache-2.0). -/
def circleGeneratorClass : FundamentalGroup Circle 1 := .mk circleGenerator

/-- The real lift of the specified generator ends at one period. -/
lemma circle_generated (g : FundamentalGroup Circle 1) :
    ∃ n : ℤ, circleGeneratorClass ^ n = g := by
  let c := Circle.isAddQuotientCoveringMap_exp
  let e := c.fundamentalGroupEquiv ⟨0, Circle.exp_zero⟩
  let a : AddSubgroup.zmultiples (2 * Real.pi) := ⟨_, 1, rfl⟩
  have h : e circleGeneratorClass = .op (.ofAdd a) := by
    apply c.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    let L : C(I, ℝ) := { toFun t := (t : ℝ) * (2 * Real.pi) }
    change _ = c.isCoveringMap.liftPath circleGenerator 0 _ 1
    rw [← (c.isCoveringMap.eq_liftPath_iff' (Γ := L) _).mpr ⟨rfl, by simp [L]⟩]
    simp [a, L]
  obtain ⟨n, hn⟩ := (e g).unop.toAdd.2
  refine ⟨n, e.injective ?_⟩
  rw [map_zpow, h]
  apply MulOpposite.unop_injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  simpa [a] using hn

@[simp] lemma norm_boundary (z : Circle) : ‖(boundaryInclusion z).val‖ = 1 := Circle.norm_coe z

/-- The universal property of the underlying set quotient. -/
def glue {A : Type*} (l : X → A) (r : ι → Disk → A)
    (h : ∀ i z, r i (boundaryInclusion z) = l (f i z)) : Space f → A :=
  Quot.lift (Sum.elim l (fun z => r z.1 z.2)) (by rintro _ _ ⟨i, z⟩; exact h i z)

def angle (z : Disk) := Circle.exp z.val.arg

variable {P : Space f → Sort*}

/-- A dependent eliminator: only strict disk interiors require a second case.
This computes on the representatives, even for families of path classes. -/
@[elab_as_elim] def visit (x : Space f) (l : ∀ a, P (inclusion f a))
    (r : ∀ i z, ‖(z : Disk).val‖ ≠ 1 → P (characteristic f i z)) : P x :=
  let d i (z : Disk) := if h : ‖z.val‖ = 1 then
    (characteristic_boundary f i ⟨z, mem_sphere_zero_iff_norm.mpr h⟩).symm ▸ l _ else r i z h
  Quot.hrecOn x (fun | .inl a => l a | .inr ⟨i, z⟩ => d i z) (by
    rintro _ _ ⟨i, z⟩; simp [d]; apply eqRec_heq)
@[simp] lemma visit_disk l r i z (hz : ‖(z : Disk).val‖ ≠ 1) :
    visit f (P := P) (characteristic f i z) l r = r i z hz := dite_eq_right hz

lemma open_parts (S : Set (Space f)) : IsOpen S ↔
    IsOpen (inclusion f ⁻¹' S) ∧ ∀ i, IsOpen (characteristic f i ⁻¹' S) :=
  isOpen_sum_iff.trans (and_congr_right' isOpen_sigma_iff)

lemma cont_parts {A : Type*} [TopologicalSpace A] {g : Space f → A} (S : TopologicalSpace.Opens (Space f))
    (l : ContinuousOn (g ∘ inclusion f) (inclusion f ⁻¹' S))
    (r : ∀ i, ContinuousOn (g ∘ characteristic f i) (characteristic f i ⁻¹' S)) : ContinuousOn g S :=
  have hs := (open_parts f _).1 S.isOpen
  (continuousOn_open_iff S.isOpen).mpr fun _ ht => (open_parts f _).mpr
    ⟨l.isOpen_inter_preimage hs.1 ht,
     fun i => (r i).isOpen_inter_preimage (hs.2 i) ht⟩

/-- Open patches: the outside (including X), and one open disk per index. -/
def patch : Option ι → TopologicalSpace.Opens (Space f)
  | none => ⟨glue f (fun _ => True) (fun _ z => 1 / 2 < ‖z.val‖) (by norm_num),
    (open_parts f _).2 ⟨isOpen_univ, fun _ => isOpen_lt continuous_const continuous_subtype_val.norm⟩⟩
  | some i => ⟨glue f (fun _ => False) (fun j z => ‖z.val‖ ≠ 1 ∧ j = i) (by simp),
    (open_parts f _).2 ⟨isOpen_empty, fun j => (isOpen_ne_fun continuous_subtype_val.norm continuous_const).inter
      (isOpen_const (p := j = i))⟩⟩
lemma patch_cover (y : Space f) : ∃ k, y ∈ patch f k := by
  induction y using visit with
  | l x => exact ⟨none, trivial⟩
  | r i z hz => exact ⟨some i, hz, rfl⟩

/-- On an interior patch, recover a continuous disk coordinate. No choice of
a continuous section on all of the quotient is necessary. -/
lemma disk_lift {K : Type*} [TopologicalSpace K] (p : C(K, Space f)) {i}
    (h : ∀ t, p t ∈ patch f (some i)) : ∃ z : C(K, Disk), p = (characteristic f i).comp z := by
  -- Keep the reconstruction equation together with the coordinate.
  let pos (y : Space f) : {z : Disk // y ∈ patch f (some i) → y = characteristic f i z} := visit f y
    (fun _ => ⟨⟨0, by simp⟩, False.elim⟩) (fun j z _ => ⟨z, by rintro ⟨_, rfl⟩; rfl⟩)
  have hc := cont_parts f (g := fun y => (pos y).1) (patch f (some i)) continuous_const.continuousOn
    fun _ => continuous_id.continuousOn.congr fun z hz => by simp [pos, hz.1]
  exact ⟨⟨_, hc.comp_continuous p.continuous h⟩, ContinuousMap.ext fun t => (pos _).2 (h t)⟩

/-- Radially expand each disk. At time one the entire outer patch maps back into X. -/
def scale (p : Disk × I) := max ‖p.1.val‖ (1 - (p.2 : ℝ) / 2)
lemma scale_pos (p) : 0 < scale p := lt_max_of_lt_right (by linarith [p.2.2.2])
def expand : C(Disk × I, Disk) where
  toFun p := ⟨(scale p)⁻¹ • (p.1 : ℂ), by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr (scale_pos ..).le), inv_mul_le_one₀ (scale_pos ..)]
    exact le_max_left ..⟩
  continuous_toFun := by unfold scale; fun_prop (disch := exact fun p => (scale_pos p).ne')
lemma angle_spec {z : Disk} (hz : 1 / 2 < ‖z.val‖) : boundaryInclusion (angle z) = expand (z, 1) := by
  ext1
  change (angle z : ℂ) = (scale (z, 1))⁻¹ • _
  rw [eq_inv_smul_iff₀ (scale_pos _).ne', scale, max_eq_left (by norm_num; linarith), Algebra.smul_def]
  exact Complex.norm_mul_exp_arg_mul_I _
-- The argument need only be continuous modulo a full turn.
lemma angle_cont : ContinuousOn angle {z | 1 / 2 < ‖(z : Disk).val‖} := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  exact AddCircle.homeomorphCircle'.continuous.continuousAt.comp
    ((Complex.continuousAt_arg_coe_angle (by rintro h; norm_num [h] at hz)).comp continuous_subtype_val.continuousAt)

/-- Descend the deformation as a map into the space of trajectories. Its
values on the rim agree with the constant trajectories from X. -/
def movie : C(Space f, C(I, Space f)) :=
  let r i := ((characteristic f i).comp expand).curry
  ⟨glue f (fun a => ContinuousMap.const I (inclusion f a)) (fun i => r i) (by
    intro i z; ext t
    refine (congrArg (characteristic f i) ?_).trans (characteristic_boundary f i z)
    ext1; simp [expand, scale, max_eq_left (sub_le_self 1 (div_nonneg t.2.1 zero_le_two))]),
   continuous_quot_lift _ (Continuous.sumElim (by fun_prop) (continuous_sigma fun i => (r i).continuous))⟩
@[simp] lemma movie_zero (y : Space f) : movie f y 0 = y := by
  induction y using visit with
  | l => rfl
  | r i z _ =>
    apply congrArg (characteristic f i)
    ext1; simp [expand, scale, max_eq_right z.2]
end CellAttachment
