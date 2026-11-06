module

public import PottsDiscontinuity.Duality.RectangleCurlLinearEquiv
public import PottsDiscontinuity.Duality.RectangleFlowDimension

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)
variable (A : Configuration (rectangleGraph a w h))

local instance rectangleOpenIndexFintype :
    Fintype (OpenEdgeIndex (rectangleGraph a w h) A) := Fintype.ofFinite _
local instance rectangleOpenIndexDecidableEq :
    DecidableEq (OpenEdgeIndex (rectangleGraph a w h) A) := Classical.decEq _

local instance rectangleOpenFlowCarrierFintype :
    Fintype (rectanglePrimalEdgeCarrier a w h) := by
  classical
  letI : Fintype (RectangleVertex a w h) := Fintype.ofFinite _
  letI : Fintype (Sym2 (RectangleVertex a w h)) := inferInstance
  letI : Finite (rectanglePrimalEdgeCarrier a w h) :=
    Finite.of_injective (fun e : rectanglePrimalEdgeCarrier a w h => e.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

local instance rectangleOpenFlowBondFintype :
    Fintype (RectanglePrimalBond a w h) :=
  Fintype.ofEquiv (rectanglePrimalEdgeCarrier a w h)
    (rectanglePrimalEdgeBondEquiv a w h)

def rectangleBondToGraphEdge (b : RectanglePrimalBond a w h) :
    (rectangleGraph a w h).edgeSet := rectanglePrimalBondToEdge a w h b

noncomputable def rectangleOpenFlowZeroExtend
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ) : RectanglePrimalFlow a w h := by
  classical
  exact fun b =>
    let e := rectangleBondToGraphEdge a w h b
    if hb : e ∈ A then f ⟨e, hb⟩ else 0

@[simp] theorem rectangleOpenFlowZeroExtend_onOpen
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ)
    (e : OpenEdgeIndex (rectangleGraph a w h) A) :
    rectangleOpenFlowZeroExtend a w h A f ((rectanglePrimalEdgeBondEquiv a w h) e.1) = f e := by
  classical
  have he : rectangleBondToGraphEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e.1) = e.1 :=
    (rectanglePrimalEdgeBondEquiv a w h).left_inv e.1
  unfold rectangleOpenFlowZeroExtend
  dsimp only
  simp [he]

theorem rectangleOpenFlowZeroExtend_onClosed
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ)
    (b : RectanglePrimalBond a w h)
    (hb : rectangleBondToGraphEdge a w h b ∉ A) :
    rectangleOpenFlowZeroExtend a w h A f b = 0 := by
  classical
  simp [rectangleOpenFlowZeroExtend, hb]

def rectangleOpenFlowSubmodule : Submodule ℝ (RectanglePrimalFlow a w h) where
  carrier := {F | ∀ b : RectanglePrimalBond a w h,
    rectangleBondToGraphEdge a w h b ∉ A → F b = 0}
  zero_mem' := by simp
  add_mem' := by intro F H hF hH b hb; simp [hF b hb, hH b hb]
  smul_mem' := by intro c F hF b hb; simp [hF b hb]

noncomputable def rectangleOpenFlowZeroExtendEquiv :
    (OpenEdgeIndex (rectangleGraph a w h) A → ℝ) ≃ₗ[ℝ]
      rectangleOpenFlowSubmodule a w h A where
  toFun f := ⟨rectangleOpenFlowZeroExtend a w h A f,
    fun b hb => rectangleOpenFlowZeroExtend_onClosed a w h A f b hb⟩
  invFun F e := F.1 ((rectanglePrimalEdgeBondEquiv a w h) e.1)
  left_inv f := funext fun e => by simp
  right_inv F := Subtype.ext <| funext fun b => by
    classical
    unfold rectangleOpenFlowZeroExtend
    dsimp only
    split_ifs with hb
    · exact congrArg F.1 (Equiv.apply_symm_apply (rectanglePrimalEdgeBondEquiv a w h) b)
    · exact (F.2 b hb).symm
  map_add' f g := Subtype.ext <| funext fun b => by
    classical
    by_cases hb : rectangleBondToGraphEdge a w h b ∈ A <;>
      simp [rectangleOpenFlowZeroExtend, hb]
  map_smul' c f := Subtype.ext <| funext fun b => by
    classical
    by_cases hb : rectangleBondToGraphEdge a w h b ∈ A <;>
      simp [rectangleOpenFlowZeroExtend, hb]

def rectangleBondSignedTerm (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) (b : RectanglePrimalBond a w h) : ℝ :=
  (if b.1.source = v then F b else 0) -
    (if b.1.target = v then F b else 0)

theorem rectanglePrimalFlowDivergence_eq_allBonds
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h F v =
      ∑ b : RectanglePrimalBond a w h, rectangleBondSignedTerm a w h F v b := by
  classical
  let p : RectanglePrimalBond a w h → Prop :=
    fun b => b.1.source = v ∨ b.1.target = v
  let T := rectangleBondSignedTerm a w h F v
  have hterm (b : rectangleActualIncidentBonds a w h v) :
      (if b.1.1.source = v then F b.1 else -F b.1) = T b.1 := by
    rcases b.2 with hs | ht
    · have hne : b.1.1.target ≠ v := fun h => b.1.1.source_ne_target (hs.trans h.symm)
      simp [T, rectangleBondSignedTerm, hs, hne]
    · have hne : b.1.1.source ≠ v := fun h => b.1.1.source_ne_target (h.trans ht.symm)
      simp [T, rectangleBondSignedTerm, hne, ht]
  let incidentEquiv : rectangleActualIncidentBonds a w h v ≃
      {b : RectanglePrimalBond a w h // p b} := Equiv.refl _
  calc
    rectanglePrimalFlowDivergence a w h F v =
        ∑ b : rectangleActualIncidentBonds a w h v, T b.1 :=
      Finset.sum_congr rfl fun b _ => hterm b
    _ = ∑ b : {b : RectanglePrimalBond a w h // p b}, T b.1 :=
      Equiv.sum_comp incidentEquiv (fun b => T b.1)
    _ = ∑ b ∈ Finset.univ.filter p, T b :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp [p]) T).symm
    _ = ∑ b : RectanglePrimalBond a w h, T b := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hp : p b
      · simp [p, hp]
      · simp [T, rectangleBondSignedTerm, mt Or.inl hp, mt Or.inr hp]

theorem rectangleOpenFlowZeroExtend_signedDivergence
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ)
    (v : RectangleVertex a w h) :
    signedDivergence (rectangleGraph a w h) A
      (rectangleOpenEdgeOrientation a w h A) f v =
      rectanglePrimalFlowDivergence a w h
        (rectangleOpenFlowZeroExtend a w h A f) v.1 := by
  classical
  let F := rectangleOpenFlowZeroExtend a w h A f
  let q : RectanglePrimalBond a w h → Prop :=
    fun b => rectangleBondToGraphEdge a w h b ∈ A
  let T := rectangleBondSignedTerm a w h F v.1
  let eEquiv : OpenEdgeIndex (rectangleGraph a w h) A ≃
      {b : RectanglePrimalBond a w h // q b} :=
    { toFun := fun e => ⟨(rectanglePrimalEdgeBondEquiv a w h) e.1, by
        have hEdge : rectangleBondToGraphEdge a w h ((rectanglePrimalEdgeBondEquiv a w h) e.1) = e.1 :=
          (rectanglePrimalEdgeBondEquiv a w h).left_inv e.1
        dsimp [q]; rw [hEdge]; exact e.2⟩
      invFun := fun b => ⟨rectangleBondToGraphEdge a w h b.1, b.2⟩
      left_inv := fun e => Subtype.ext ((rectanglePrimalEdgeBondEquiv a w h).left_inv e.1)
      right_inv := fun b => Subtype.ext ((rectanglePrimalEdgeBondEquiv a w h).right_inv b.1) }
  have hedge (e : OpenEdgeIndex (rectangleGraph a w h) A) :
      (if (rectangleOpenEdgeOrientation a w h A).source e = v then f e else 0) -
        (if (rectangleOpenEdgeOrientation a w h A).target e = v then f e else 0) =
      T (eEquiv e).1 := by
    have hs : (rectangleOpenEdgeOrientation a w h A).source e = v ↔
        (rectanglePrimalEdgeBondEquiv a w h e.1).1.source = v.1 := Subtype.ext_iff
    have ht : (rectangleOpenEdgeOrientation a w h A).target e = v ↔
        (rectanglePrimalEdgeBondEquiv a w h e.1).1.target = v.1 := Subtype.ext_iff
    simp [T, rectangleBondSignedTerm, hs, ht, F, eEquiv]
  calc
    signedDivergence (rectangleGraph a w h) A
        (rectangleOpenEdgeOrientation a w h A) f v =
      ∑ e : OpenEdgeIndex (rectangleGraph a w h) A, T (eEquiv e).1 := by
      rw [signedDivergence_apply, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => hedge e
    _ = ∑ b : {b : RectanglePrimalBond a w h // q b}, T b.1 :=
      Equiv.sum_comp eEquiv (fun b => T b.1)
    _ = ∑ b ∈ Finset.univ.filter q, T b :=
      (Finset.sum_subtype (p := q) (Finset.univ.filter q) (fun _ => by simp [q]) T).symm
    _ = ∑ b : RectanglePrimalBond a w h, T b := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hq : q b
      · simp [q, hq]
      · have hz := rectangleOpenFlowZeroExtend_onClosed a w h A f b hq
        simp [q, hq, T, rectangleBondSignedTerm, F, hz]
    _ = rectanglePrimalFlowDivergence a w h F v.1 :=
      (rectanglePrimalFlowDivergence_eq_allBonds a w h F v.1).symm

noncomputable def rectangleOpenFlowDivergenceKernelEquiv :
    LinearMap.ker (signedDivergence (rectangleGraph a w h) A
      (rectangleOpenEdgeOrientation a w h A)) ≃ₗ[ℝ]
      @Min.min (Submodule ℝ (RectanglePrimalFlow a w h)) inferInstance
        (rectangleOpenFlowSubmodule a w h A)
        (rectangleDivergenceFreeFlowSubmodule a w h) where
  toFun f := ⟨(rectangleOpenFlowZeroExtendEquiv a w h A) f.1,
    Submodule.mem_inf.mpr ⟨(rectangleOpenFlowZeroExtendEquiv a w h A f.1).2, fun z hz => by
      change rectanglePrimalFlowDivergence a w h (rectangleOpenFlowZeroExtend a w h A f.1) z = 0
      rw [← rectangleOpenFlowZeroExtend_signedDivergence a w h A f.1 ⟨z, hz⟩]
      exact congrFun f.2 ⟨z, hz⟩⟩⟩
  invFun F := ⟨(rectangleOpenFlowZeroExtendEquiv a w h A).symm ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩,
    funext fun v => by
      have hF : rectangleOpenFlowZeroExtend a w h A
          ((rectangleOpenFlowZeroExtendEquiv a w h A).symm ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩) = F.1 :=
        congrArg Subtype.val ((rectangleOpenFlowZeroExtendEquiv a w h A).apply_symm_apply
          ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩)
      rw [rectangleOpenFlowZeroExtend_signedDivergence, hF]
      exact (Submodule.mem_inf.mp F.2).2 v.1 v.2⟩
  left_inv f := by
    apply Subtype.ext
    exact (rectangleOpenFlowZeroExtendEquiv a w h A).left_inv f.1
  right_inv F := by
    apply Subtype.ext
    change rectangleOpenFlowZeroExtend a w h A
      ((rectangleOpenFlowZeroExtendEquiv a w h A).symm ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩) = F.1
    exact congrArg Subtype.val
      ((rectangleOpenFlowZeroExtendEquiv a w h A).apply_symm_apply ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩)
  map_add' f g := by
    apply Subtype.ext
    change rectangleOpenFlowZeroExtend a w h A (f.1 + g.1) =
      rectangleOpenFlowZeroExtend a w h A f.1 + rectangleOpenFlowZeroExtend a w h A g.1
    exact congrArg Subtype.val (map_add (rectangleOpenFlowZeroExtendEquiv a w h A) f.1 g.1)
  map_smul' c f := by
    apply Subtype.ext
    change rectangleOpenFlowZeroExtend a w h A (c • f.1) =
      c • rectangleOpenFlowZeroExtend a w h A f.1
    exact congrArg Subtype.val (map_smul (rectangleOpenFlowZeroExtendEquiv a w h A) c f.1)

end
end PottsDiscontinuity.FK
