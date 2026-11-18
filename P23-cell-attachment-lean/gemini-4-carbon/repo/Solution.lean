module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Tactic.Group

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CellAttachment
universe u v
open scoped unitInterval

abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}

def boundaryInclusion : C(Circle, Disk) where
  toFun z := ⟨z, le_of_eq (Circle.norm_coe z)⟩
  continuous_toFun := by fun_prop

abbrev Raw (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, Disk)

def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop

section
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

inductive AttachingRel (f : ι → C(Circle, X)) : Raw X ι → Raw X ι → Prop
  | boundary (i : ι) (z : Circle) :
      AttachingRel f (.inr ⟨i, boundaryInclusion z⟩) (.inl (f i z))

def Space (f : ι → C(Circle, X)) := Quot (AttachingRel f)

instance (f : ι → C(Circle, X)) : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (AttachingRel f)))

def quotientMap (f : ι → C(Circle, X)) : C(Raw X ι, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

def inclusion (f : ι → C(Circle, X)) : C(X, Space f) where
  toFun x := quotientMap f (.inl x)
  continuous_toFun := (quotientMap f).continuous.comp continuous_inl

def inclusionPi1 (f : ι → C(Circle, X)) (x₀ : X) :
    FundamentalGroup X x₀ →* FundamentalGroup (Space f) (inclusion f x₀) :=
  FundamentalGroup.map (inclusion f) x₀

def attachingLoop (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) : Path x₀ x₀ :=
  (γ i).trans ((circleGenerator.map (f i).continuous).trans (γ i).symm)

def attachingLoopClass (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : ι → FundamentalGroup X x₀ :=
  fun i => .mk (attachingLoop f x₀ γ i)

def attachingNormalClosure (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : Subgroup (FundamentalGroup X x₀) :=
  Subgroup.normalClosure (Set.range (attachingLoopClass f x₀ γ))

instance attachingNormalClosure_normal (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) : (attachingNormalClosure f x₀ γ).Normal := by
  unfold attachingNormalClosure
  infer_instance
end

def completeStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {ι : Type v}
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)),
    Function.Surjective (inclusionPi1 f x₀) ∧
    (inclusionPi1 f x₀).ker = attachingNormalClosure f x₀ γ ∧
    ∃ e : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀

open Topology Set Subgroup Path.Homotopic.Quotient SimplyConnectedSpace PathConnectedSpace Classical
open QuotientGroup hiding mk

variable {Z : Type*} [TopologicalSpace Z]

abbrev PQuot := @Path.Homotopic.Quotient Z _
abbrev OpenDisk := {z : Disk // ‖(z : ℂ)‖ ≠ 1}

instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, unitInterval.zero_mem⟩

lemma disk_convex : Convex ℝ {z : ℂ | ‖z‖ ≤ 1} := by
  simpa [Metric.closedBall] using convex_closedBall (0 : ℂ) 1

instance : ContractibleSpace Disk := disk_convex.contractibleSpace ⟨0, by simp⟩

def polar (z : ℂ) : Circle :=
  if h : z = 0 then 1
  else ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm h)⟩

@[fun_prop] lemma polar_continuousAt {z : ℂ} (hz : z ≠ 0) : ContinuousAt polar z :=
  IsInducing.subtypeVal.continuousAt_iff.mpr <|
    ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hz)).smul continuousAt_id).congr <|
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) fun _ (hw : _ ≠ 0) => by simp [polar, hw]

@[simp] lemma polar_coe (z : Circle) : polar z = z := by
  ext; simp [polar, Circle.coe_ne_zero z]

def dRad (z : Disk) : Path z (boundaryInclusion (polar z)) :=
  ⟨⟨fun t => ⟨(1 - (t : ℝ)) • (z : ℂ) + (t : ℝ) • (polar z : ℂ),
      disk_convex z.2 (Circle.norm_coe _).le (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _)⟩,
    by fun_prop⟩, by ext; simp, by ext; simp [boundaryInclusion]⟩

@[simp] def lPath (a b : I) : Path a b := ⟨⟨Icc.convexComb a b, by fun_prop⟩, by simp, by simp⟩

lemma lPath_mem_Icc {a b : I} (h : a ≤ b) (u : I) : lPath a b u ∈ Icc a b :=
  ⟨Icc.le_convexComb h u, Icc.convexComb_le h u⟩

@[simp] abbrev seg (g : C(I, Z)) (a b : I) : Path (g a) (g b) := (lPath a b).map g.2

@[simp] def pPair (a₁ a₂ b₁ b₂ : I) : Path (a₁, b₁) (a₂, b₂) :=
  (lPath a₁ a₂).prod (lPath b₁ b₂)

def arcPath (w : Circle) : Path (1 : Circle) w :=
  ⟨⟨fun t => Circle.exp ((t : ℝ) * w.1.arg), by fun_prop⟩, by simp, by simp⟩

lemma seg_trans_class (g : C(I, Z)) (a b c : I) :
    (mk (seg g a b)).trans (mk (seg g b c)) = mk (seg g a c) := by
  rw [← mk_trans, ← Path.map_trans]; exact eq.mpr ((paths_homotopic _ (lPath a c)).map g)

section Proof
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {f : ι → C(Circle, X)} {x₀ : X}

@[simp] def qMap (H : C(I × I, Space f)) (a₁ a₂ b₁ b₂ : I) : C(I, Space f) :=
  H.comp (pPair a₁ a₂ b₁ b₂).1

def charMap (i : ι) : C(Disk, Space f) :=
  (quotientMap f).comp ⟨fun z => .inr ⟨i, z⟩, continuous_inr.comp continuous_sigmaMk⟩
def oMap (i : ι) : C(OpenDisk, Space f) := (charMap i).comp ⟨Subtype.val, continuous_subtype_val⟩
def Uset : Set (Space f) :=
  Quot.lift (fun | .inl _ => True | .inr ⟨_, z⟩ => (z : ℂ) ≠ 0)
    fun | _, _, .boundary _ z => propext ⟨fun _ => trivial, fun _ => Circle.coe_ne_zero z⟩

def covSet : Option ι → Set (Space f)
  | none => Uset
  | some i => range (oMap i)

@[simp] lemma charMap_bdry (i : ι) (z : Circle) : charMap i (boundaryInclusion z) = inclusion f (f i z) :=
  Quot.sound (.boundary i z)

lemma oMap_open (i : ι) : IsOpenEmbedding (oMap (f := f) i) := by
  have hq {a} {z : OpenDisk} : oMap (f := f) i z = Quot.mk _ a ↔ .inr ⟨i, z.1⟩ = a := by
    rcases z with ⟨z, hz⟩
    exact ⟨fun h => (congrArg (Quot.lift ((.inr ⟨i, z⟩ : Raw X ι) = ·) fun
        | _, _, .boundary _ w => propext ⟨fun h => (hz (by cases h; exact Circle.norm_coe w)).elim, nofun⟩) h).mp rfl,
      fun h => h ▸ rfl⟩
  refine .of_continuous_injective_isOpenMap (oMap i).2
    (fun a b h => Subtype.ext (by simpa using hq.mp h))
    fun S hS => isQuotientMap_quot_mk.isCoinducing.isOpen_preimage.mp ?_
  rw [show Quot.mk _ ⁻¹' (oMap i '' S) = (fun z : OpenDisk => (.inr ⟨i, z.1⟩ : Raw X ι)) '' S by ext; simp [hq]]
  exact (isOpenMap_inr.comp <| isOpenMap_sigmaMk.comp
    (isOpen_ne.preimage (continuous_norm.comp continuous_subtype_val)).isOpenMap_subtype_val) S hS

lemma uSet_isOpen : IsOpen (Uset (f := f)) :=
  isQuotientMap_quot_mk.isCoinducing.isOpen_preimage.mp <| isOpen_sum_iff.mpr
    ⟨isOpen_univ, isOpen_sigma_iff.mpr fun _ => isOpen_ne.preimage continuous_subtype_val⟩

lemma cov_open : ∀ b, IsOpen (covSet (f := f) b)
  | none => uSet_isOpen
  | some i => (oMap_open i).isOpen_range

lemma cov_mem : ∀ y : Space f, ∃ b, y ∈ covSet b := Quot.ind fun
  | .inl _ => ⟨none, trivial⟩
  | .inr ⟨i, z⟩ => if hz : (z : ℂ) = 0 then ⟨some i, ⟨z, by simp [hz]⟩, rfl⟩ else ⟨none, hz⟩

def ret : Space f → X :=
  Quot.lift (fun | .inl x => x | .inr ⟨i, z⟩ => f i (polar z))
    fun | _, _, .boundary i z => congrArg (f i) (polar_coe z)

def uRet : C(Uset (f := f), X) :=
  ⟨_, ((isQuotientMap_quot_mk.continuousOn_isOpen_iff (g := ret) uSet_isOpen).mpr <|
    (uSet_isOpen.preimage (quotientMap f).2).continuousOn_iff.mpr fun
      | .inl _, _ => IsOpenEmbedding.inl.continuousAt_iff.mp continuousAt_id
      | .inr _, ha => (IsOpenEmbedding.inr.comp .sigmaMk).continuousAt_iff.mp <| by
          dsimp [ret, quotientMap]; fun_prop (disch := exact ha)).domRestrict⟩

def qRad (t : I) : Space f → Space f :=
  Quot.lift (fun | .inl x => inclusion f x | .inr ⟨i, z⟩ => charMap i (dRad z t))
    fun | _, _, .boundary i z =>
          (congrArg (charMap i) (by ext; simp [dRad, boundaryInclusion]; ring)).trans (charMap_bdry i z)

def rPath (y : Space f) : Path y (inclusion f (ret y)) :=
  have h := Quot.ind (β := fun y => (Continuous fun t => qRad t y) ∧ qRad 0 y = y ∧ qRad 1 y = inclusion f (ret y))
    (fun
      | .inl _ => ⟨continuous_const, rfl, rfl⟩
      | .inr ⟨i, z⟩ => ⟨(charMap i).2.comp (dRad z).1.2, congrArg (charMap i) (dRad z).2,
          (congrArg (charMap i) (dRad z).3).trans (charMap_bdry i _)⟩) y
  ⟨⟨_, h.1⟩, h.2.1, h.2.2⟩

lemma map_charMap_eq {i : ι} {a b : Disk} {a' b' : Space f} (p₁ p₂ : Path a b) {q₁ q₂ : Path a' b'}
    (h₁ : ∀ t, q₁ t = charMap i (p₁ t)) (h₂ : ∀ t, q₂ t = charMap i (p₂ t)) : mk q₁ = mk q₂ :=
  eq_of_heq <| (Path.Homotopic.hpath_hext (p₂ := p₁.map (charMap i).2) h₁).trans <|
    (heq_of_eq (eq.mpr ((paths_homotopic p₁ p₂).map _))).trans
      (Path.Homotopic.hpath_hext (p₂ := p₂.map (charMap i).2) h₂).symm

lemma lift_oMap {i : ι} {p : C(I, Space f)} (hv : ∀ s, p s ∈ range (oMap i)) :
    ∃ z : C(I, OpenDisk), p = (oMap i).comp z := by
  choose z hz using hv
  exact ⟨⟨z, (oMap_open (f := f) i).isInducing.continuous_iff.mpr
    (by simpa only [Function.comp_def, hz] using p.continuous)⟩, by ext s; exact (hz s).symm⟩

variable [PathConnectedSpace X] (γ : ∀ i, Path x₀ (f i 1))

def eta (y : Space f) : PQuot x₀ (ret y) :=
  let g : Space f → _ := Quot.lift (fun
    | .inl _ => refl x₀
    | .inr ⟨i, z⟩ => if _ : ‖(z : ℂ)‖ = 1 then refl x₀ else
        (mk ((γ i).trans ((arcPath (polar z)).map (f i).2))).trans (mk (somePath x₀ (f i (polar z)))).symm)
    fun | _, _, .boundary _ z => dite_eq_left (Circle.norm_coe z)
  (g y).trans (mk (somePath x₀ (ret y)))

def uWord (a b : Space f) (q : PQuot (ret a) (ret b)) :
    FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ :=
  mk' _ ((eta γ a).trans (q.trans (eta γ b).symm))

def edgeWord (p : C(I, Space f)) : FundamentalGroup X x₀ ⧸ attachingNormalClosure f x₀ γ :=
  if hu : ∀ s, p s ∈ Uset then
    uWord γ (p 0) (p 1) (mk ⟨uRet.comp ⟨fun s => ⟨p s, hu s⟩, by fun_prop⟩, rfl, rfl⟩)
  else 1
end Proof

theorem two_cell_attachment : completeStatement.{u, v} := by
  intro X _ _ ι f x₀ γ
  have hs : Function.Surjective (inclusionPi1 f x₀) := by
    have hcont : Continuous fun p : I × Uset (f := f) => qRad p.1 p.2.1 := by
      let F (q : I × Raw X ι) := qRad q.1 (quotientMap f q.2)
      apply (isQuotientMap_quot_mk.restrictPreimage_isOpen uSet_isOpen).continuous_lift_prod_right
      refine continuous_iff_continuousAt.mpr fun ⟨t, a, ha⟩ =>
        ContinuousAt.comp (g := F) ?_ (continuous_id.prodMap continuous_subtype_val).continuousAt
      rcases a with x | ⟨i, z⟩
      · exact (IsOpenEmbedding.id.prodMap .inl).continuousAt_iff (g := F) (x := (t, x)).mp
          ((inclusion f).2.comp continuous_snd).continuousAt
      · refine (IsOpenEmbedding.id.prodMap (IsOpenEmbedding.inr.comp (.sigmaMk (i := i)))).continuousAt_iff
          (g := F) (x := (t, z)).mp (ContinuousAt.comp (g := charMap i) (charMap i).2.continuousAt ?_)
        refine IsInducing.subtypeVal.continuousAt_iff.mpr ?_
        dsimp [dRad]; fun_prop (disch := exact ha)
    let F : ContinuousMap.Homotopy ⟨Subtype.val, continuous_subtype_val⟩ ((inclusion f).comp uRet) :=
      ⟨⟨fun p => qRad p.1 p.2.1, hcont⟩, fun _ => (rPath _).source, fun _ => (rPath _).target⟩
    have hstep {a b : Space f} (p : C(I, Space f)) {k} (hb : ∀ s, p s ∈ covSet k)
        (ha : p 0 = a := by simp) (hb' : p 1 = b := by simp) :
        ∃ q : Path (ret a) (ret b),
          (mk ⟨p, ha, hb'⟩).trans (mk (rPath b)) = (mk (rPath a)).trans (mk (q.map (inclusion f).2)) := by
      subst ha hb'
      rcases k with _ | i
      · let u : Path (⟨p 0, hb 0⟩ : Uset) ⟨p 1, hb 1⟩ := ⟨⟨fun s => ⟨p s, hb s⟩, by fun_prop⟩, rfl, rfl⟩
        exact ⟨u.map uRet.2, by rw [← mk_trans, ← mk_trans]; exact eq.mpr (.map_trans_evalAt F u)⟩
      · obtain ⟨z, rfl⟩ := lift_oMap hb
        let c := (arcPath (polar (z 0).1)).symm.trans (arcPath (polar (z 1).1))
        refine ⟨c.map (f i).2, ?_⟩
        rw [← mk_trans, ← mk_trans]
        exact map_charMap_eq
          (Path.trans ⟨⟨_, z.2.subtype_val⟩, rfl, rfl⟩ (dRad (z 1).1))
          ((dRad (z 0).1).trans (c.map boundaryInclusion.2))
          (fun s => by simp [Path.trans_apply]; split_ifs <;> exact rfl)
          (fun s => by simp [Path.trans_apply]; split_ifs <;> [exact rfl; exact (charMap_bdry i _).symm])
    intro γ₀
    obtain ⟨α, rfl⟩ := mk_surjective γ₀
    let g := α.1
    obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (fun b => (cov_open b).preimage g.2) fun s _ => mem_iUnion.mpr (cov_mem (g s))
    have hreach (k : ℕ) : ∃ q : Path (ret (g 0)) (ret (g (t k))),
        (mk (seg g 0 (t k))).trans (mk (rPath (g (t k)))) =
          (mk (rPath (g 0))).trans (mk (q.map (inclusion f).2)) := by
      induction k with
      | zero =>
        rw [ht0, show seg g 0 0 = .refl _ by ext; simp]
        exact ⟨.refl _, by rw [show (Path.refl _).map _ = .refl _ from rfl]; simp⟩
      | succ k ih =>
        obtain ⟨q₁, hq₁⟩ := ih
        obtain ⟨b, hb⟩ := hsub k
        obtain ⟨q₂, hq₂⟩ := hstep (a := g (t k)) (b := g (t (k + 1))) (seg g (t k) (t (k + 1))).1 fun s =>
          hb (lPath_mem_Icc (hmono k.le_succ) s)
        refine ⟨q₁.trans q₂, ?_⟩
        rw [← seg_trans_class g 0 (t k) (t (k + 1)), trans_assoc, hq₂, ← trans_assoc, hq₁,
          trans_assoc, ← mk_trans, ← Path.map_trans]
    obtain ⟨q, hq⟩ := hN N le_rfl ▸ hreach N
    have hEndS {y₀ y₁} (h₀ : inclusion f x₀ = y₀) (h₁ : inclusion f x₀ = y₁) (P : Path y₀ y₁)
        (q : Path (ret y₀) (ret y₁))
        (h : (mk P).trans (mk (rPath y₁)) = (mk (rPath y₀)).trans (mk (q.map (inclusion f).2))) :
        ∃ ℓ, inclusionPi1 f x₀ ℓ = mk (P.cast h₀ h₁) := by
      subst h₀ h₁
      exact ⟨mk q, by
        change mk (q.map (inclusion f).2) = mk P
        simpa [show rPath (inclusion f x₀) = .refl _ from Path.ext rfl] using h.symm⟩
    rw [← show (seg g 0 1).cast α.source.symm α.target.symm = α by ext; simp [g]]
    exact hEndS α.source.symm α.target.symm _ q hq
  let Ncl := attachingNormalClosure f x₀ γ
  have hk : (inclusionPi1 f x₀).ker = Ncl := by
    refine le_antisymm ?_ (normalClosure_le_normal ?_)
    · have hu_refl (a : Space f) : uWord γ a a (mk (.refl _)) = 1 := by simp [uWord]; exact one_mem _
      have hu_trans {a b c : Space f} (q₁ : PQuot (ret a) (ret b)) (q₂ : PQuot (ret b) (ret c)) :
          uWord γ b c q₂ * uWord γ a b q₁ = uWord γ a c (q₁.trans q₂) := by
        unfold uWord; rw [← map_mul]; congr 1
        erw [CategoryTheory.End.mul_def, FundamentalGroupoid.comp_eq]; simp only [trans_assoc]
        rw [← trans_assoc (eta γ b).symm, symm_trans, refl_trans]
      have he_eq {a b : Space f} (p : C(I, Space f)) (hu : ∀ s, p s ∈ Uset) (q : Path (ret a) (ret b))
          (ha : p 0 = a := by simp) (hb : p 1 = b := by simp) (hq : ∀ s, ret (p s) = q s := by intro; simp; rfl) :
          edgeWord γ p = uWord γ a b (mk q) := by
        subst ha hb; dsimp only [edgeWord]; rw [dite_eq_left hu]; congr 2; ext s; exact hq s
      have he_V {i : ι} {p : C(I, Space f)} (hv : ∀ s, p s ∈ range (oMap i)) : edgeWord γ p = 1 := by
        obtain ⟨z, rfl⟩ := lift_oMap hv
        unfold edgeWord; split_ifs with hu
        · let w : Path _ _ :=
            ⟨⟨fun s => polar (z s).1, continuous_iff_continuousAt.mpr fun s => by
              fun_prop (disch := exact hu s)⟩, rfl, rfl⟩
          let φ := (mk' Ncl).comp
            (((FundamentalGroup.fundamentalGroupMulEquivOfPath (γ i)).symm.toMonoidHom).comp
              (FundamentalGroup.map (f i) 1))
          have ho (v : OpenDisk) : eta γ (oMap i v) = mk ((γ i).trans ((arcPath (polar v.1)).map (f i).2)) := by
            dsimp [eta, oMap, charMap, quotientMap, ret]; simp [v.2, trans_assoc]
          let cLoop := (arcPath (polar (z 0).1)).trans (w.trans (arcPath (polar (z 1).1)).symm)
          refine Eq.trans ?_ (show φ (mk cLoop) = 1 from ?_)
          · change uWord γ (oMap i _) (oMap i _) (mk (w.map (f i).2)) =
              mk' Ncl (mk ((γ i).trans ((cLoop.map (f i).2).trans (γ i).symm)))
            unfold uWord; rw [ho (z 0), ho (z 1), ← mk_symm]
            congr 1; simp [cLoop, ← Path.map_symm, trans_assoc]
          · let c : FundamentalGroup Circle 1 := .mk circleGenerator
            let hp := Circle.isAddQuotientCoveringMap_exp
            let e : Circle.exp ⁻¹' {1} := ⟨0, Circle.exp_zero⟩
            have hgen : hp.fundamentalGroupToMulOpposite e c =
                .op (.ofAdd ⟨2 * .pi, AddSubgroup.mem_zmultiples _⟩) := by
              rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
              change (2 * .pi : ℝ) + 0 = hp.isCoveringMap.liftPath _ _ _ 1
              simp [← (hp.isCoveringMap.eq_liftPath_iff' (γ := circleGenerator) (e := e)
                (Γ := ⟨fun t : I => t * (2 * .pi), by fun_prop⟩) (by simp [e])).mpr ⟨rfl, by simp [e]⟩]
            obtain ⟨n, hn⟩ :=
              AddSubgroup.mem_zmultiples_iff.mp ((hp.fundamentalGroupToMulOpposite e (mk cLoop)).unop.toAdd).2
            rw [← (hp.fundamentalGroupToMulOpposite_injective e <| by
                rw [map_zpow, hgen]
                exact MulOpposite.unop_injective <| Multiplicative.toAdd.injective <| Subtype.ext <| by simpa using hn
                : c ^ n = mk cLoop), map_zpow,
              show φ c = 1 from (eq_one_iff _).mpr (subset_normalClosure (mem_range_self i)),
              one_zpow]
        · rfl
      intro g hg
      obtain ⟨ℓ, hℓ⟩ := mk_surjective g
      obtain ⟨H⟩ := exact (MonoidHom.mem_ker.mp (hℓ ▸ hg))
      obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsub⟩ :=
        exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
          (fun b => (cov_open b).preimage H.continuous) fun q _ => mem_iUnion.mpr (cov_mem (H q))
      have htN : t N = 1 := hN N le_rfl
      let E (a b c d : ℕ) := edgeWord γ (qMap H.toContinuousMap (t a) (t b) (t c) (t d))
      let R (i k : ℕ) : _ ⧸ Ncl := Nat.rec 1 (fun m acc => E i i m (m + 1) * acc) k
      have hrow_step (i k : ℕ) : E i (i + 1) k k * R i k = R (i + 1) k * E i (i + 1) 0 0 := by
        induction k with
        | zero => simp [R]
        | succ k ih =>
          dsimp only [R]
          rw [mul_assoc (E (i + 1) (i + 1) k (k + 1)), ← ih, ← mul_assoc, ← mul_assoc]
          congr 1
          let B := H.toContinuousMap.comp ((lPath (t i) (t (i + 1))).1.prodMap (lPath (t k) (t (k + 1))).1)
          have hmem (q : I × I) := mk_mem_prod (lPath_mem_Icc (hmono i.le_succ) q.1)
            (lPath_mem_Icc (hmono k.le_succ) q.2)
          suffices edgeWord γ (qMap B 0 1 1 1) * edgeWord γ (qMap B 0 0 0 1) =
              edgeWord γ (qMap B 1 1 0 1) * edgeWord γ (qMap B 0 1 0 0) by
            convert this using 2 <;> (dsimp only [E]; congr 1; ext; simp [B])
          obtain ⟨b, hb⟩ := hsub i k
          rcases b with _ | j
          · let M : C(I × I, X) := uRet.comp ⟨fun q => ⟨B q, hb (hmem q)⟩, by fun_prop⟩
            have hbox (c₁ c₂ d₁ d₂ : I) :
                edgeWord γ (qMap B c₁ c₂ d₁ d₂) =
                  uWord γ (B (c₁, d₁)) (B (c₂, d₂)) (mk ((pPair c₁ c₂ d₁ d₂).map M.2)) :=
              he_eq _ (fun _ => hb (hmem _)) _
            simp only [hbox, hu_trans, ← mk_trans, ← Path.map_trans]
            rw [eq.mpr ((paths_homotopic _ _).map M)]
          · have hv (p : C(I, I × I)) := he_V (p := B.comp p) fun _ => hb (hmem _)
            simp only [qMap, hv, mul_one]
      have hconst {a b c d : ℕ}
          (hh : qMap H.toContinuousMap (t a) (t b) (t c) (t d) = .const _ (inclusion f x₀) := by
            ext; simp [ht0, htN]) :
          E a b c d = 1 := by
        simp only [E, hh,
          (he_eq (.const _ (inclusion f x₀)) (fun _ => trivial) (.refl _) rfl rfl fun _ => rfl).trans (hu_refl _)]
      have hRN (k : ℕ) : R N k = 1 := by
        induction k with
        | zero => rfl
        | succ k ih => simpa [R, ih] using hconst
      have hreq (i : ℕ) : R 0 N = R i N := by
        induction i with
        | zero => rfl
        | succ i ih => exact ih.trans (by have hs := hrow_step i N; rwa [hconst, hconst, one_mul, mul_one] at hs)
      have hrow0 (k : ℕ) : R 0 k =
          uWord γ (inclusion f (ℓ 0)) (inclusion f (ℓ (t k))) (mk (seg ℓ.1 0 (t k))) := by
        induction k with
        | zero => dsimp [R]; rw [ht0, ← hu_refl (inclusion f (ℓ 0))]; congr 2; ext; simp; rfl
        | succ k ih =>
          change E 0 0 k (k + 1) * R 0 k = _; dsimp only [E]
          rw [ht0, ih, he_eq (a := inclusion f (ℓ (t k))) (b := inclusion f (ℓ (t (k + 1))))
              (qMap H.toContinuousMap 0 0 (t k) (t (k + 1))) (fun _ => by simp; trivial)
              (seg ℓ.1 (t k) (t (k + 1))), hu_trans, seg_trans_class]
      have h0N := (hrow0 N).symm.trans ((hreq N).trans (hRN N))
      have hEnd {x₁ x₂} (h₁ : x₀ = x₁) (h₂ : x₀ = x₂) (p : Path x₁ x₂) :
          uWord γ (inclusion f x₁) (inclusion f x₂) (mk p) =
            uWord γ (inclusion f x₀) (inclusion f x₀) (mk (p.cast h₁ h₂)) := by
        subst h₁ h₂; rfl
      rw [htN, hEnd ℓ.source.symm ℓ.target.symm, show (seg ℓ.1 0 1).cast _ _ = ℓ by ext; simp, hℓ] at h0N
      let e : FundamentalGroup X x₀ := eta γ (inclusion f x₀)
      change mk' _ (e⁻¹ * g * e) = 1 at h0N
      convert (attachingNormalClosure_normal f x₀ γ).conj_mem _ ((eq_one_iff _).mp h0N) e using 2
      group
    · rintro _ ⟨i, rfl⟩
      apply MonoidHom.mem_ker.mpr
      change mk ((attachingLoop f x₀ γ i).map (inclusion f).2) = .refl (inclusion f x₀)
      unfold attachingLoop
      simp only [Path.map_trans, ← Path.map_symm, mk_trans, mk_symm]
      rw [map_charMap_eq (circleGenerator.map boundaryInclusion.2) (.refl _) (q₂ := .refl (inclusion f (f i 1)))
          (fun _ => (charMap_bdry i _).symm) (fun _ => (charMap_bdry i 1).symm)]
      simp
  exact ⟨hs, hk, liftEquiv _ hs hk.symm, rfl⟩

end CellAttachment
end
