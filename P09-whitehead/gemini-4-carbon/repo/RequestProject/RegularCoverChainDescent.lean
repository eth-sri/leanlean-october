module

public import RequestProject.TreePi2Reflection
public import RequestProject.OrderNerveOneDecoding
public import RequestProject.CombPi1
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Set.Finite.Lattice
public import RequestProject.Statement
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic
public import RequestProject.OrderNerveCommonSimplex
public import Mathlib.Topology.Homotopy.Contractible
public import RequestProject.GenusCollapseIteration
public import RequestProject.CylinderPi1Surjective
public import RequestProject.GenusLoops
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import RequestProject.PresPosetReading
public import RequestProject.GenusQuotientRelativeSupport

@[expose] public section
noncomputable section
section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.RelativeTreeExtension
open SpanningTree

variable {D : Complex2} (T : SpanningTree D) {Z S : Type}

def source : D.E ⊕ Z → D.V := Sum.elim D.src (fun _ => T.root)
def target : D.E ⊕ Z → D.V := Sum.elim D.tgt (fun _ => T.root)

def loopGraph : Complex2 where
  V := D.V
  E := D.E ⊕ Z
  F := PEmpty
  src := source T
  tgt := target T
  base := PEmpty.elim
  att := PEmpty.elim
  att_isLoop f := PEmpty.elim f

def oldPath (l : List (D.E × Bool)) : List ((D.E ⊕ Z) × Bool) :=
  l.map (fun e => (Sum.inl e.1, e.2))

theorem oldPath_isPath {l : List (D.E × Bool)} {a b : D.V}
    (hl : IsPath D.src D.tgt l a b) :
    IsPath (source T) (target T) (oldPath (Z := Z) l) a b :=
  FiniteChains.Comb.isPath_map (src := D.src) (tgt := D.tgt)
    (src' := source T) (tgt' := target T) (fun x : D.V => x)
    (Sum.inl : D.E → D.E ⊕ Z) (fun _ => rfl) (fun _ => rfl) hl

def generatorLoop : NonTree T ⊕ Z → List ((D.E ⊕ Z) × Bool)
  | Sum.inl e => oldPath (conjPath T [(e.val, true)] (D.src e.val) (D.tgt e.val))
  | Sum.inr z => [(Sum.inr z, true)]

theorem generatorLoop_isPath (a : NonTree T ⊕ Z) :
    IsPath (source T) (target T) (generatorLoop T a) T.root T.root := by
  cases a with
  | inl e => exact oldPath_isPath T (conjPath_isLoop T (isPath_single (e.val, true)))
  | inr z => exact ⟨rfl, rfl⟩

def signedLoop (e : (NonTree T ⊕ Z) × Bool) : List ((D.E ⊕ Z) × Bool) :=
  if e.2 then generatorLoop T e.1 else revPath (X := loopGraph (Z := Z) T) (generatorLoop T e.1)


def readWord (l : List ((NonTree T ⊕ Z) × Bool)) : List ((D.E ⊕ Z) × Bool) :=
  l.flatMap (signedLoop T)

theorem readWord_isPath (l : List ((NonTree T ⊕ Z) × Bool)) :
    IsPath (source T) (target T) (readWord T l) T.root T.root := by
  induction l with
  | nil => rfl
  | cons a l ih => exact (show IsPath (source T) (target T) (signedLoop T a) T.root T.root by
    rcases a with ⟨a, b⟩
    cases b
    · exact isPath_revPath (X := loopGraph (Z := Z) T) (generatorLoop_isPath T a)
    · exact generatorLoop_isPath T a).append ih

variable (extra : S → FreeGroup (NonTree T ⊕ Z))

def complex : Complex2 where
  V := D.V
  E := D.E ⊕ Z
  F := D.F ⊕ S
  src := source T
  tgt := target T
  base := Sum.elim D.base (fun _ => T.root)
  att := Sum.elim (fun f => oldPath (D.att f)) (fun s => readWord T (extra s).toWord)
  att_isLoop := by
    intro f
    cases f with
    | inl f => exact oldPath_isPath T (D.att_isLoop f)
    | inr s => exact readWord_isPath T (extra s).toWord

def oldInclusion : Hom D (complex T extra) where
  onV := id
  onE := Sum.inl
  onF := Sum.inl
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

def tree : SpanningTree (complex T extra) where
  root := T.root
  ht := T.ht
  isTree := Sum.elim T.isTree (fun _ => False)
  up a ha := (Sum.inl (T.up a ha).1, (T.up a ha).2)
  ht_root := T.ht_root
  ht_eq_zero := T.ht_eq_zero
  up_src := by
    intro a ha
    cases hb : (T.up a ha).2 <;>
      simpa only [germSrc, hb, Bool.false_eq_true, if_false, if_true, source, target, complex, Sum.elim_inl] using T.up_src a ha
  up_ht := by
    intro a ha
    cases hb : (T.up a ha).2 <;>
      simpa only [germTgt, hb, Bool.false_eq_true, if_false, if_true, target, source, complex, Sum.elim_inl] using T.up_ht a ha
  isTree_iff := by
    intro e
    cases e with
    | inl e =>
        change T.isTree e ↔ ∃ a ha, Sum.inl (T.up a ha).1 = Sum.inl e
        simpa only [Sum.inl.injEq] using T.isTree_iff e
    | inr z =>
        change False ↔ ∃ a ha, Sum.inl (T.up a ha).1 = Sum.inr z
        simp

theorem tree_old (e : D.E) :
    (tree T extra).isTree ((oldInclusion T extra).onE e) ↔ T.isTree e := Iff.rfl

def generatorEquiv : NonTree (tree T extra) ≃ NonTree T ⊕ Z where
  toFun e := match e with
    | ⟨Sum.inl e, he⟩ => Sum.inl ⟨e, he⟩
    | ⟨Sum.inr z, _⟩ => Sum.inr z
  invFun a := match a with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr z => ⟨Sum.inr z, not_false⟩
  left_inv e := by rcases e with ⟨e | z, he⟩ <;> rfl
  right_inv a := by cases a <;> rfl

theorem oldPath_collapsed (l : List (D.E × Bool)) :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (oldPath (Z := Z) l)) =
        FreeGroup.map Sum.inl (pathWord T l) := by
  change FreeGroup.map (generatorEquiv T extra)
    (pathWord (tree T extra) (mapPath (oldInclusion T extra) l)) = _
  rw [pathWord_mapPath (tree_old T extra), FreeGroup.map.comp]
  rfl

theorem generatorLoop_collapsed (a : NonTree T ⊕ Z) :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (generatorLoop T a)) = FreeGroup.of a := by
  cases a with
  | inl e =>
      rw [generatorLoop, oldPath_collapsed]
      simp [conjPath, pathWord_append, pathWord_revPath, pathWord_cons,
        germWord, e.property]
  | inr z =>
      change FreeGroup.map (generatorEquiv T extra)
        (pathWord (tree T extra) [(Sum.inr z, true)]) = _
      rw [pathWord_cons, pathWord_nil, mul_one]
      simp [germWord, tree, generatorEquiv]

theorem readWord_collapsed (l : List ((NonTree T ⊕ Z) × Bool)) :
    FreeGroup.map (generatorEquiv T extra)
      (pathWord (tree T extra) (readWord T l)) = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rcases e with ⟨a, b⟩
      cases b
      · have happ := pathWord_append (tree T extra)
          (revPath (generatorLoop T a)) (readWord T l)
        have hrev := pathWord_revPath (tree T extra) (generatorLoop T a)
        have hpw : pathWord (tree T extra) (readWord T ((a, false) :: l)) =
            (pathWord (tree T extra) (generatorLoop T a))⁻¹ *
              pathWord (tree T extra) (readWord T l) :=
          happ.trans (congrArg (fun w => w * pathWord (tree T extra) (readWord T l)) hrev)
        rw [hpw, map_mul, map_inv,
          generatorLoop_collapsed, ih, mk_cons_false]
      · change FreeGroup.map (generatorEquiv T extra)
          (pathWord (tree T extra) (generatorLoop T a ++ readWord T l)) = _
        rw [pathWord_append, map_mul, generatorLoop_collapsed, ih, mk_cons_true]

/-- Collapsing the retained tree recovers exactly the prescribed relative
presentation; no homotopy classification assumption occurs here. -/
theorem treeRel_equation (f : D.F ⊕ S) :
    FreeGroup.map (generatorEquiv T extra) (treeRel (tree T extra) f) =
      Sum.elim (fun d => FreeGroup.map Sum.inl (treeRel T d)) extra f := by
  cases f with
  | inl f => exact oldPath_collapsed T extra (D.att f)
  | inr s =>
      change FreeGroup.map (generatorEquiv T extra)
        (pathWord (tree T extra) (readWord T (extra s).toWord)) = extra s
      rw [readWord_collapsed, FreeGroup.mk_toWord]

theorem connected : IsConnected (complex T extra) := by
  intro a b
  exact ⟨oldPath (revPath (T.treePath a) ++ T.treePath b),
    oldPath_isPath T ((isPath_revPath (T.treePath_isPath a)).append (T.treePath_isPath b))⟩

end FiniteChains.Comb.RelativeTreeExtension
end

section
open scoped Classical
namespace FiniteChains.Comb.RelativeTreeExtension
open SpanningTree
variable {D : Complex2} (T : SpanningTree D) {Z S R : Type}
  (extra : S → FreeGroup (NonTree T ⊕ Z))
  (extra' : R → FreeGroup (NonTree T ⊕ Z))
  (f : S → R) (hf : ∀ s, extra' (f s) = extra s)

def inclusion : Hom (complex T extra) (complex T extra') where
  onV := id
  onE := id
  onF := Sum.map id f
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF := by rintro (d | s) <;> rfl
  att_onF := by
    intro s
    cases s with
    | inl d => simp [complex]
    | inr s => simp [complex, hf]

end FiniteChains.Comb.RelativeTreeExtension
end

section
open scoped Classical unitInterval
open Set
namespace FiniteChains.PathReplacement

variable {X ι : Type} [TopologicalSpace X]

theorem range_trans_subset {x y z : X} (p : Path x y) (q : Path y z) {A : Set X}
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A) : Set.range (p.trans q) ⊆ A := by grind

theorem range_symm_subset {x y : X} (p : Path x y) {A : Set X}
    (hp : Set.range p ⊆ A) : Set.range p.symm ⊆ A := by simp_all

theorem homotopic_of_within_simplyConnected (U : Set X) (hU : IsSimplyConnected U)
    {x y : X} (p q : Path x y) (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    Path.Homotopic p q := by
  letI : SimplyConnectedSpace U := hU
  have hx  := hp p.source_mem_range
  have hy  := hp p.target_mem_range
  let P : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ := {
    toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let Q : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ := {
    toFun := fun t => ⟨q t, hq ⟨t, rfl⟩⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := Subtype.ext q.source
    target' := Subtype.ext q.target }
  have h := (SimplyConnectedSpace.paths_homotopic P Q).map
    ⟨Subtype.val, continuous_subtype_val⟩
  exact h

variable (A : Set X) (U : ι → Set X)
  (hcover : A ∪ ⋃ i, U i = Set.univ)
  (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
  (hpath : ∀ i, IsPathConnected (A ∩ U i))
  (hsc : ∀ i, IsSimplyConnected (U i))

include hcover in
omit [TopologicalSpace X] in
theorem exists_chart {x : X} (hx : x ∉ A) : ∃ i, x ∈ U i := by
  have h : x ∈ A ∪ ⋃ i, U i := by rw [hcover]; trivial
  exact Set.mem_iUnion.mp (h.resolve_left hx)

def corePoint (x : X) : X :=
  if hx : x ∈ A then x
  else Classical.choose (hpath (Classical.choose (exists_chart A U hcover hx))).nonempty

theorem corePoint_mem (x : X) : corePoint A U hcover hpath x ∈ A := by
  by_cases hx : x ∈ A
  · simpa only [corePoint, dif_pos hx] using hx
  · simpa only [corePoint, dif_neg hx] using (Classical.choose_spec
      (hpath (Classical.choose (exists_chart A U hcover hx))).nonempty).1

theorem corePoint_eq {x : X} (hx : x ∈ A) : corePoint A U hcover hpath x = x :=
  dif_pos hx

include hsc in
theorem point_joined_corePoint {x : X} (hx : x ∉ A) :
    JoinedIn (U (Classical.choose (exists_chart A U hcover hx))) x
      (corePoint A U hcover hpath x) := by
  let i := Classical.choose (exists_chart A U hcover hx)
  have hi  := Classical.choose_spec (exists_chart A U hcover hx)
  have ha : corePoint A U hcover hpath x ∈ U i := by
    simpa only [corePoint, dif_neg hx] using (Classical.choose_spec (hpath i).nonempty).2
  exact (hsc i).isPathConnected.joinedIn _ hi _ ha

def coreConnector (x : X) : Path x (corePoint A U hcover hpath x) :=
  if hx : x ∈ A then (Path.refl x).cast rfl (corePoint_eq A U hcover hpath hx)
  else (point_joined_corePoint A U hcover hpath hsc hx).somePath

theorem coreConnector_cast {x : X} (hx : x ∈ A) :
    (coreConnector A U hcover hpath hsc x).cast rfl
      (corePoint_eq A U hcover hpath hx).symm = Path.refl x := by
  apply Path.ext
  funext t
  simp only [coreConnector, dif_pos hx, Path.cast_coe]

theorem coreConnector_range_of_mem {x : X} (hx : x ∈ A) :
    Set.range (coreConnector A U hcover hpath hsc x) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  simpa only [coreConnector, dif_pos hx, Path.cast_coe, Path.refl_apply] using hx

include hdisj in
theorem coreConnector_range_chart (i : ι) {x : X} (hx : x ∈ U i) :
    Set.range (coreConnector A U hcover hpath hsc x) ⊆ U i := by
  by_cases hxA : x ∈ A
  · rintro _ ⟨t, rfl⟩
    simpa only [coreConnector, dif_pos hxA, Path.cast_coe, Path.refl_apply] using hx
  · let k := Classical.choose (exists_chart A U hcover hxA)
    have hk  := Classical.choose_spec (exists_chart A U hcover hxA)
    have hki : k = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) hk hx
    rintro _ ⟨t, rfl⟩
    rw [coreConnector, dif_neg hxA]
    simpa only [← hki] using
      (point_joined_corePoint A U hcover hpath hsc hxA).somePath_mem t

include hcover hdisj hpath hsc in
theorem path_into_core (hA : IsOpen A) (hU : ∀ i, IsOpen (U i))
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) (p : Path x y) :
    ∃ q : Path x y, Set.range q ⊆ A ∧ Path.Homotopic p q := by
  let V : Option ι → Set X
    | none => A
    | some i => U i
  have hV : ∀ i, IsOpen (V i) := by
    rintro (_ | i)
    · exact hA
    · exact hU i
  have hcov : Set.univ ⊆ ⋃ i, V i := by
    intro z _
    have hz : z ∈ A ∪ ⋃ i, U i := by rw [hcover]; trivial
    rcases hz with hz | hz
    · exact Set.mem_iUnion.mpr ⟨none, hz⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨some i, hi⟩
  have hlocal : ∀ i {b c : X} (v : Path b c), Set.range v ⊆ V i →
      ∃ w : Path (corePoint A U hcover hpath b) (corePoint A U hcover hpath c),
        Set.range w ⊆ A ∧ Path.Homotopic
          (((coreConnector A U hcover hpath hsc b).symm.trans v).trans
            (coreConnector A U hcover hpath hsc c)) w := by
    rintro (_ | i) b c v hv
    · refine ⟨_, ?_, Path.Homotopic.refl _⟩
      exact range_trans_subset _ _
        (range_trans_subset _ _
          (range_symm_subset _ (coreConnector_range_of_mem A U hcover hpath hsc
            (hv v.source_mem_range))) hv)
        (coreConnector_range_of_mem A U hcover hpath hsc (hv v.target_mem_range))
    · have hb := coreConnector_range_chart A U hcover hdisj hpath hsc i (hv v.source_mem_range)
      have hc := coreConnector_range_chart A U hcover hdisj hpath hsc i (hv v.target_mem_range)
      have hab : corePoint A U hcover hpath b ∈ A ∩ U i :=
        ⟨corePoint_mem A U hcover hpath b,
          hb (coreConnector A U hcover hpath hsc b).target_mem_range⟩
      have hac : corePoint A U hcover hpath c ∈ A ∩ U i :=
        ⟨corePoint_mem A U hcover hpath c,
          hc (coreConnector A U hcover hpath hsc c).target_mem_range⟩
      let hw := (hpath i).joinedIn _ hab _ hac
      refine ⟨hw.somePath, ?_, ?_⟩
      · rintro _ ⟨t, rfl⟩
        exact (hw.somePath_mem t).1
      · apply homotopic_of_within_simplyConnected (U i) (hsc i)
        · exact range_trans_subset _ _ (range_trans_subset _ _ (range_symm_subset _ hb) hv) hc
        · rintro _ ⟨t, rfl⟩
          exact (hw.somePath_mem t).2
  obtain ⟨q, hqA, hq⟩ := replace_of_open_cover V hV hcov A
    (corePoint A U hcover hpath) (corePoint_mem A U hcover hpath)
    (coreConnector A U hcover hpath hsc) hlocal p
  let hx' := corePoint_eq A U hcover hpath hx
  let hy' := corePoint_eq A U hcover hpath hy
  refine ⟨q.cast hx'.symm hy'.symm, hqA, ?_⟩
  have h := hq.pathCast hx'.symm hy'.symm
  rw [Path.cast_trans _ _ hx'.symm rfl hy'.symm,
    Path.cast_trans _ _ hx'.symm rfl rfl, Path.cast_symm,
    coreConnector_cast A U hcover hpath hsc hx,
    coreConnector_cast A U hcover hpath hsc hy, Path.cast_rfl_rfl] at h
  have hnorm  :=
    (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans p)
  exact hnorm.symm.trans h

end FiniteChains.PathReplacement
end

section
open scoped Classical unitInterval
open Set Topology Metric
namespace FiniteChains.RelativeAttachment

variable {E X J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

abbrev OpenNormBall (E : Type) [Norm E] := {x : E // ‖x‖ < 1}

def normBallHomeomorph : E ≃ₜ OpenNormBall E :=
  Homeomorph.unitBall.trans (Homeomorph.setCongr (by
    ext x
    change dist x 0 < 1 ↔ ‖x‖ < 1
    rw [dist_zero_right]))

theorem normBallHomeomorph_zero : (normBallHomeomorph (E := E) 0).val = 0 :=
  Homeomorph.coe_unitBall_apply_zero


def openDiskMap (r : BoundaryFamily J E → X) (j : J) : OpenNormBall E → DiskAttachment r :=
  fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j

omit [NormedSpace ℝ E] in
theorem openDiskMap_isOpenEmbedding (r : BoundaryFamily J E → X) (j : J) :
    IsOpenEmbedding (openDiskMap r j) :=
  (fresh_isOpenEmbedding r _ (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).comp
    (interiorDiskPoint_isOpenEmbedding j)

def openDisk (r : BoundaryFamily J E → X) (j : J) : Set (DiskAttachment r) :=
  Set.range (openDiskMap r j)

def puncturedAttachment (r : BoundaryFamily J E → X) : Set (DiskAttachment r) :=
  oldCollar r 0 le_rfl Set.univ

omit [NormedSpace ℝ E] in
theorem openDisk_isOpen (r : BoundaryFamily J E → X) (j : J) : IsOpen (openDisk r j) :=
  (openDiskMap_isOpenEmbedding r j).isOpen_range



theorem puncturedAttachment_isOpen (r : BoundaryFamily J E → X) (hr : Continuous r) :
    IsOpen (puncturedAttachment r) :=
  oldCollar_isOpen r hr 0 le_rfl zero_lt_one Set.univ isOpen_univ

theorem openDisk_simplyConnected (r : BoundaryFamily J E → X) (j : J) :
    IsSimplyConnected (openDisk r j) := by
  letI : ContractibleSpace (Metric.ball (0 : E) 1) := Metric.contractibleSpace_ball zero_lt_one
  let e : Metric.ball (0 : E) 1 ≃ₜ OpenNormBall E := Homeomorph.setCongr (by
    ext x
    change dist x 0 < 1 ↔ ‖x‖ < 1
    rw [dist_zero_right])
  letI := e.symm.toHomotopyEquiv.simplyConnectedSpace
  exact (openDiskMap_isOpenEmbedding r j).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace


theorem puncturedAttachment_inter_pathConnected (r : BoundaryFamily J E → X)
    (hdim : 1 < Module.rank ℝ E) (j : J) :
    IsPathConnected (puncturedAttachment r ∩ openDisk r j) := by
  rw [(show puncturedAttachment r ∩ openDisk r j =
      openDiskMap r j '' {x : OpenNormBall E | x.val ≠ 0} by
    ext z
    constructor
    · rintro ⟨hz, ⟨x, rfl⟩⟩
      obtain ⟨hx, _⟩ := hz
      refine ⟨x, ?_, rfl⟩
      exact norm_pos_iff.mp hx
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨norm_pos_iff.mpr hx, trivial⟩, ⟨x, rfl⟩⟩)]
  exact (show IsPathConnected {x : OpenNormBall E | x.val ≠ 0} by
    have hp := (isPathConnected_compl_singleton_of_one_lt_rank hdim 0).image
      (normBallHomeomorph).continuous
    have he : normBallHomeomorph '' ({0})ᶜ =
        {x : OpenNormBall E | x.val ≠ 0} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ heq
        have hy0  := (normBallHomeomorph).injective
          (Subtype.ext (heq.trans normBallHomeomorph_zero.symm))
        exact hy (Set.mem_singleton_iff.mpr hy0)
      · intro hx
        refine ⟨(normBallHomeomorph).symm x, ?_,
          (normBallHomeomorph).apply_symm_apply x⟩
        intro hzero
        have hz  := hzero
        have h := congrArg (fun z => (normBallHomeomorph z).val) hz
        rw [(normBallHomeomorph).apply_symm_apply, normBallHomeomorph_zero] at h
        exact hx h
    rwa [he] at hp).image (openDiskMap_isOpenEmbedding r j).continuous

/-- The path and its homotopy are built in the actual attachment; neither
an abstract presentation nor a surjectivity premise is used. -/
theorem diskAttachment_path_avoid_centers (r : BoundaryFamily J E → X) (hr : Continuous r)
    (hdim : 1 < Module.rank ℝ E) {x y : DiskAttachment r}
    (hx : x ∈ puncturedAttachment r) (hy : y ∈ puncturedAttachment r) (p : Path x y) :
    ∃ q : Path x y, Set.range q ⊆ puncturedAttachment r ∧ Path.Homotopic p q :=
  PathReplacement.path_into_core (puncturedAttachment r) (openDisk r)
    (by
      apply Set.eq_univ_of_forall
      rintro (x | d)
      · exact Or.inl trivial
      · apply Or.inr
        have hd  := lt_of_le_of_ne d.val.2.property
          (fun h => d.property ((boundaryFamilyInclusion_range J E _).mpr h))
        exact Set.mem_iUnion.mpr ⟨d.val.1, ⟨⟨d.val.2.val, hd⟩, rfl⟩⟩) (by
          intro i j hij
          apply Set.disjoint_left.mpr
          rintro _ ⟨x, rfl⟩ ⟨y, he⟩
          have h  := Sum.inr_injective he
          exact hij (congrArg (fun d => d.val.1) h).symm)
    (puncturedAttachment_inter_pathConnected r hdim) (openDisk_simplyConnected r)
    (puncturedAttachment_isOpen r hr) (openDisk_isOpen r) hx hy p

end FiniteChains.RelativeAttachment
end

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.RelativeAttachment

variable {E X J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

def radialDiskPoint (t : I) (x : ClosedUnitBall E) : ClosedUnitBall E :=
  ⟨((1 - (t : ℝ)) + (t : ℝ) / ‖x.val‖) • x.val, by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hr := x.property
    have hs : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖x.val‖ :=
      add_nonneg (sub_nonneg.mpr ht1) (div_nonneg ht0 (norm_nonneg _))
    rw [norm_smul, Real.norm_of_nonneg hs, add_mul]
    by_cases hx : ‖x.val‖ = 0
    · simp only [hx, mul_zero, div_zero, add_zero]
      exact zero_le_one
    · rw [div_mul_cancel₀ _ hx]
      nlinarith⟩

theorem radialDiskPoint_zero (x : ClosedUnitBall E) : radialDiskPoint 0 x = x := by
  ext
  simp [radialDiskPoint]

theorem radialDiskPoint_boundary (t : I) (x : UnitBoundary E) :
    radialDiskPoint t (unitBoundaryInclusion E x) = unitBoundaryInclusion E x := by
  ext
  simp [radialDiskPoint, unitBoundaryInclusion, x.property]




def radialCoreBack (r : BoundaryFamily J E → X) (z : puncturedAttachment r) : X :=
  match z with
  | ⟨Sum.inl x, _⟩ => x
  | ⟨Sum.inr d, hd⟩ =>
      r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, Classical.choose hd⟩⟩

omit [TopologicalSpace X] in
theorem radialCoreBack_mem_iff (r : BoundaryFamily J E → X)
    (z : puncturedAttachment r) (U : Set X) :
    radialCoreBack r z ∈ U ↔ z.val ∈ oldCollar r 0 le_rfl U := by
  rcases z with ⟨x | d, hz⟩
  · rfl
  · change r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, Classical.choose hz⟩⟩ ∈ U ↔
      ∃ h : 0 < ‖d.val.2.val‖, r ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, h⟩⟩ ∈ U
    exact ⟨fun h => ⟨Classical.choose hz, h⟩, fun ⟨_, h⟩ => h⟩

theorem radialCoreBack_continuous (r : BoundaryFamily J E → X) (hr : Continuous r) :
    Continuous (radialCoreBack r) := by
  apply continuous_def.mpr
  intro U hU
  have he : radialCoreBack r ⁻¹' U =
      Subtype.val ⁻¹' oldCollar r 0 le_rfl U := by
    ext z
    exact radialCoreBack_mem_iff r z U
  rw [he]
  exact (oldCollar_isOpen r hr 0 le_rfl zero_lt_one U hU).preimage continuous_subtype_val

def radialDiskPath (r : BoundaryFamily J E → X) (j : J) (x : ClosedUnitBall E) :
    C(I, DiskAttachment r) :=
  ⟨fun t => cell r (boundaryFamilyInclusion J E) ⟨j, radialDiskPoint t x⟩,
    (cell_continuous r _).comp (continuous_sigmaMk.comp (by
      apply Continuous.subtype_mk
      exact ((continuous_const.sub continuous_subtype_val).add
        (continuous_subtype_val.div_const _)).smul continuous_const))⟩

def radialFamily (r : BoundaryFamily J E → X) : DiskAttachment r → C(I, DiskAttachment r)
  | Sum.inl x => ContinuousMap.const I (old r (boundaryFamilyInclusion J E) x)
  | Sum.inr d => radialDiskPath r d.val.1 d.val.2

theorem radialFamily_cell (r : BoundaryFamily J E → X) (d : DiskFamily J E) :
    radialFamily r (cell r (boundaryFamilyInclusion J E) d) = radialDiskPath r d.1 d.2 := by
  by_cases hd : d ∈ Set.range (boundaryFamilyInclusion J E)
  · obtain ⟨a, rfl⟩ := hd
    rw [cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective]
    apply ContinuousMap.ext
    intro t
    change old r (boundaryFamilyInclusion J E) (r a) =
      cell r (boundaryFamilyInclusion J E) ⟨a.1, radialDiskPoint t (unitBoundaryInclusion E a.2)⟩
    rw [radialDiskPoint_boundary]
    exact (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective a).symm
  · rw [cell_of_not_mem r _ d hd]
    rfl



/-- The radial homotopy lands in the actual attachment and fixes every
old point at every time. This is the part needed to cellularize paths. -/
def radialCoreHomotopy (r : BoundaryFamily J E → X) (hr : Continuous r) :
    ContinuousMap.Homotopy
      (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedAttachment r, DiskAttachment r))
      (⟨fun z => old r (boundaryFamilyInclusion J E) (radialCoreBack r z),
        (old_continuous r _).comp (radialCoreBack_continuous r hr)⟩) := by
  let F : C(puncturedAttachment r, C(I, DiskAttachment r)) :=
    ⟨fun z => radialFamily r z.val, (show ContinuousOn (radialFamily r) (puncturedAttachment r) by
      have hq : IsQuotientMap (quotientMap r (boundaryFamilyInclusion J E)) :=
        ⟨⟨rfl⟩, quotientMap_surjective r _⟩
      apply (hq.continuousOn_isOpen_iff (puncturedAttachment_isOpen r hr)).mpr
      apply continuousOn_of_forall_continuousAt
      rintro (x | d) hz
      · apply IsOpenEmbedding.inl.continuousAt_iff.mp
        let F : C(X × I, DiskAttachment r) :=
          ⟨fun z => old r (boundaryFamilyInclusion J E) z.1, (old_continuous r _).comp continuous_fst⟩
        exact F.curry.continuous.continuousAt
      · apply IsOpenEmbedding.inr.continuousAt_iff.mp
        have he : radialFamily r ∘ cell r (boundaryFamilyInclusion J E) =
            fun d : DiskFamily J E => radialDiskPath r d.1 d.2 :=
          funext (radialFamily_cell r)
        change ContinuousAt (radialFamily r ∘ cell r (boundaryFamilyInclusion J E)) d
        rw [he]
        rcases d with ⟨j, x⟩
        apply IsOpenEmbedding.sigmaMk.continuousAt_iff.mp
        have hx  :=
          ((cell_mem_oldCollar r 0 le_rfl zero_lt_one Set.univ j x).mp hz).choose
        have ho : IsOpen {x : ClosedUnitBall E | 0 < ‖x.val‖} :=
          isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
        have hh : ContinuousAt
            (fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} => radialDiskPath r j z.val)
            ⟨x, hx⟩ := (show Continuous (fun x : {x : ClosedUnitBall E // 0 < ‖x.val‖} => radialDiskPath r j x.val) by
              let F : C({x : ClosedUnitBall E // 0 < ‖x.val‖} × I, DiskAttachment r) :=
                ⟨fun z => cell r (boundaryFamilyInclusion J E) ⟨j, radialDiskPoint z.2 z.1.val⟩,
                  (cell_continuous r _).comp (continuous_sigmaMk.comp (by
                    apply Continuous.subtype_mk
                    have hn : Continuous (fun z : {x : ClosedUnitBall E // 0 < ‖x.val‖} × I => ‖z.1.val.val‖) := by
                      fun_prop
                    exact ((continuous_const.sub continuous_snd.subtype_val).add
                      (continuous_snd.subtype_val.div hn (fun z => ne_of_gt z.1.property))).smul
                        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))))⟩
              exact F.curry.continuous).continuousAt
        exact (ho.isOpenEmbedding_subtypeVal.continuousAt_iff
          (g := fun x : ClosedUnitBall E => radialDiskPath r j x) (x := ⟨x, hx⟩)).mp hh).restrict⟩
  refine {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := ?_
    map_one_left := ?_ }
  · rintro ⟨x | d, hz⟩
    · rfl
    · change cell r (boundaryFamilyInclusion J E) ⟨d.val.1, radialDiskPoint 0 d.val.2⟩ = Sum.inr d
      rw [radialDiskPoint_zero]
      exact cell_of_not_mem r _ d.val d.property
  · rintro ⟨x | d, hz⟩
    · rfl
    · change cell r (boundaryFamilyInclusion J E) ⟨d.val.1, radialDiskPoint 1 d.val.2⟩ = _
      rw [(show radialDiskPoint 1 (d.val.2) =
      unitBoundaryInclusion E (annulusBoundary 0 le_rfl ⟨(d.val.2), (Classical.choose hz)⟩) by
        apply Subtype.ext
        simp [radialDiskPoint, annulusBoundary, unitBoundaryInclusion, one_div])]
      exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
        ⟨d.val.1, annulusBoundary 0 le_rfl ⟨d.val.2, Classical.choose hz⟩⟩

theorem radialCoreHomotopy_old (r : BoundaryFamily J E → X) (hr : Continuous r)
    (t : I) (x : X) :
    radialCoreHomotopy r hr (t, ⟨old r (boundaryFamilyInclusion J E) x, trivial⟩) =
      old r (boundaryFamilyInclusion J E) x := rfl

theorem radialDiskPoint_positive (t : I) (x : ClosedUnitBall E)
    (hx : 0 < ‖x.val‖) : 0 < ‖(radialDiskPoint t x).val‖ := by
  have hs : 0 < (1 - t) + t / ‖x.val‖ := by
    by_cases ht : t < 1
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht)
        (div_nonneg t.property.1 hx.le)
    · have ht'  := le_antisymm t.property.2 (le_of_not_gt ht)
      rw [ht']
      positivity
  change 0 < ‖((1 - t) + t / ‖x.val‖) • x.val‖
  rw [norm_smul, Real.norm_of_nonneg hs.le]
  exact mul_pos hs hx

theorem radialDiskPoint_normalize (t : I) (x : ClosedUnitBall E)
    (hx : 0 < ‖x.val‖) :
    annulusBoundary 0 le_rfl ⟨radialDiskPoint t x, radialDiskPoint_positive t x hx⟩ =
      annulusBoundary 0 le_rfl ⟨x, hx⟩ := by
  have hs : 0 < (1 - t) + t / ‖x.val‖ := by
    by_cases ht : t < 1
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht)
        (div_nonneg t.property.1 hx.le)
    · have ht'  := le_antisymm t.property.2 (le_of_not_gt ht)
      rw [ht']
      positivity
  ext
  change ‖((1 - t) + t / ‖x.val‖) • x.val‖⁻¹ •
      (((1 - t) + t / ‖x.val‖) • x.val) = ‖x.val‖⁻¹ • x.val
  rw [norm_smul, Real.norm_of_nonneg hs.le, smul_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), mul_one]

/-- Every radial ray remains over its same point of the old space. -/
theorem radialCoreHomotopy_mem_oldCollar (r : BoundaryFamily J E → X)
    (hr : Continuous r) (t : I) (z : puncturedAttachment r) (U : Set X)
    (hz : z.val ∈ oldCollar r 0 le_rfl U) :
    radialCoreHomotopy r hr (t, z) ∈ oldCollar r 0 le_rfl U := by
  rcases z with ⟨x | d, hzcore⟩
  · exact hz
  · obtain ⟨hx, hU⟩ := hz
    change cell r (boundaryFamilyInclusion J E)
      ⟨d.val.1, radialDiskPoint t d.val.2⟩ ∈ oldCollar r 0 le_rfl U
    rw [cell_mem_oldCollar r 0 le_rfl zero_lt_one]
    exact ⟨radialDiskPoint_positive t d.val.2 hx,
      by simpa only [radialDiskPoint_normalize t d.val.2 hx] using hU⟩

/-- A path between old points in a disk attachment of dimension at least
two is homotopic, fixing its endpoints, to an actual path in the old space. -/
theorem diskAttachment_path_into_old (r : BoundaryFamily J E → X) (hr : Continuous r)
    (hdim : 1 < Module.rank ℝ E) (x y : X)
    (p : Path (old r (boundaryFamilyInclusion J E) x) (old r (boundaryFamilyInclusion J E) y)) :
    ∃ q : Path x y, Path.Homotopic p (q.map (old_continuous r (boundaryFamilyInclusion J E))) := by
  obtain ⟨q, hq, hpq⟩ := diskAttachment_path_avoid_centers r hr hdim
    (x := old r (boundaryFamilyInclusion J E) x)
    (y := old r (boundaryFamilyInclusion J E) y) trivial trivial p
  let Q : Path (⟨old r (boundaryFamilyInclusion J E) x, trivial⟩ : puncturedAttachment r)
      ⟨old r (boundaryFamilyInclusion J E) y, trivial⟩ := {
    toFun := fun t => ⟨q t, hq ⟨t, rfl⟩⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := Subtype.ext q.source
    target' := Subtype.ext q.target }
  let v  := Q.map (radialCoreBack_continuous r hr)
  let H := radialCoreHomotopy r hr
  have hqv : Path.Homotopic q (v.map (old_continuous r (boundaryFamilyInclusion J E))) := by
    refine ⟨{
      toFun := fun ts => H (ts.1, Q ts.2)
      continuous_toFun := H.continuous.comp (continuous_fst.prodMk (Q.continuous.comp continuous_snd))
      map_zero_left := fun s => H.map_zero_left (Q s)
      map_one_left := fun s => H.map_one_left (Q s)
      prop' := ?_ }⟩
    intro t s hs
    rcases hs with hs | hs
    · subst s
      change H (t, Q 0) = q 0
      rw [Q.source, q.source]
      exact radialCoreHomotopy_old r hr t x
    · have hs'  := hs
      subst s
      change H (t, Q 1) = q 1
      rw [Q.target, q.target]
      exact radialCoreHomotopy_old r hr t y
  exact ⟨v, hpq.trans hqv⟩

theorem twoCellAttachment_path_into_old
    (r : BoundaryFamily J (Fin 2 → ℝ) → X) (hr : Continuous r) (x y : X)
    (p : Path (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x)
      (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) y)) :
    ∃ q : Path x y, Path.Homotopic p
      (q.map (old_continuous r (boundaryFamilyInclusion J (Fin 2 → ℝ)))) := by simp_all [rank_fun', diskAttachment_path_into_old]

end FiniteChains.RelativeAttachment
end

section
open scoped Classical
open Set Topology
namespace FiniteChains.ClassicalCW

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

/-- At most one selected point lies in each original open cell. -/
def CellSeparated (S : Set X) : Prop :=
  ∀ n (j : RelCWComplex.cell (Set.univ : Set X) n),
    (S ∩ RelCWComplex.openCell n j).Subsingleton

omit [T2Space X] in
theorem CellSeparated.mono {S T : Set X} (hS : CellSeparated S) (hTS : T ⊆ S) :
    CellSeparated T := by
  intro n j x hx y hy
  exact hS n j ⟨hTS hx.1, hx.2⟩ ⟨hTS hy.1, hy.2⟩

omit [T2Space X] in
theorem CellSeparated.finite_inter_closedCell {S : Set X} (hS : CellSeparated S)
    (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
    (S ∩ RelCWComplex.closedCell n j).Finite := by
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell n j
  have hf : (⋃ m : Fin n, ⋃ k ∈ I m.val, S ∩ RelCWComplex.openCell m.val k).Finite := by
    apply Set.finite_iUnion
    intro m
    exact (I m.val).finite_toSet.biUnion (fun k _ => (hS m.val k).finite)
  have hfront : (S ∩ RelCWComplex.cellFrontier n j).Finite := by
    apply hf.subset
    intro x hx
    obtain ⟨m, hm, k, hk, hcell⟩ := by
      simpa using hI hx.2
    exact Set.mem_iUnion.mpr ⟨⟨m, hm⟩,
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hx.1, hcell⟩⟩⟩
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell, Set.inter_union_distrib_left]
  exact hfront.union (hS n j).finite

theorem CellSeparated.isClosed {S : Set X} (hS : CellSeparated S) : IsClosed S := by
  apply (CWComplex.closed (Set.univ : Set X) S (Set.subset_univ _)).mpr
  intro n j
  exact (hS.finite_inter_closedCell n j).isClosed

theorem CellSeparated.isDiscrete {S : Set X} (hS : CellSeparated S) : IsDiscrete S := by
  constructor
  apply discreteTopology_iff_forall_isClosed.mpr
  intro T
  have hT : CellSeparated (Subtype.val '' T) := hS.mono (by
    rintro _ ⟨x, _, rfl⟩
    exact x.property)
  have hc := hT.isClosed.preimage (continuous_subtype_val : Continuous (Subtype.val : S → X))
  simpa using hc

theorem CellSeparated.finite_of_subset_compact {S K : Set X} (hS : CellSeparated S)
    (hK : IsCompact K) (hSK : S ⊆ K) : S.Finite :=
  (hK.of_isClosed_subset hS.isClosed hSK).finite hS.isDiscrete

def touchedCells (K : Set X) : Set (Σ n, RelCWComplex.cell (Set.univ : Set X) n) :=
  {c | (K ∩ RelCWComplex.openCell c.1 c.2).Nonempty}

/-- Compactness plus the actual CW weak topology rules out meeting
infinitely many different open cells. -/
theorem IsCompact.finite_touchedCells {K : Set X} (hK : IsCompact K) :
    (touchedCells K).Finite := by
  let p : touchedCells K → X := fun c => Classical.choose c.property
  have hp c : p c ∈ K ∧ p c ∈ RelCWComplex.openCell c.val.1 c.val.2 :=
    Classical.choose_spec c.property
  have heq {n m : ℕ} {i : RelCWComplex.cell Set.univ n}
      {j : RelCWComplex.cell Set.univ m} {x : X}
      (hi : x ∈ RelCWComplex.openCell n i) (hj : x ∈ RelCWComplex.openCell m j) :
      (⟨n, i⟩ : Σ n, RelCWComplex.cell Set.univ n) = ⟨m, j⟩ := by
    apply RelCWComplex.eq_of_not_disjoint_openCell
    intro hd
    exact Set.disjoint_left.mp hd hi hj
  have hinj : Function.Injective p := by
    intro c d h
    apply Subtype.ext
    exact heq (hp c).2 (by simpa only [h] using (hp d).2)
  have hs : CellSeparated (Set.range p) := by
    intro n j x hx y hy
    obtain ⟨c, rfl⟩ := hx.1
    obtain ⟨d, rfl⟩ := hy.1
    have hc := heq (hp c).2 hx.2
    have hd := heq (hp d).2 hy.2
    have hcd  := Subtype.ext (hc.trans hd.symm)
    exact congrArg p hcd
  have hpK : Set.range p ⊆ K := by
    rintro _ ⟨c, rfl⟩
    exact (hp c).1
  have hf := hs.finite_of_subset_compact hK hpK
  letI : Finite (touchedCells K) := (Set.finite_range_iff hinj).mp hf
  exact Set.toFinite _

/-- A compact subset of a lower skeleton has genuine finite support by
cells of strictly lower dimension. -/
theorem IsCompact.finite_lower_support {K : Set X} (hK : IsCompact K) (d : ℕ)
    (hKd : K ⊆ CWComplex.skeletonLT (Set.univ : Set X) (d : ℕ∞)) :
    ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
      K ⊆ ⋃ (m < d) (j ∈ I m), RelCWComplex.closedCell m j := by
  have hT := IsCompact.finite_touchedCells hK
  have hI m : ((Sigma.mk m) ⁻¹' touchedCells K).Finite :=
    Set.Finite.preimage (by intro i _ j _ h; cases h; rfl) hT
  let I := fun m => (hI m).toFinset
  refine ⟨I, ?_⟩
  intro x hx
  have hxall : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell Set.univ m,
      RelCWComplex.openCell m j := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
  obtain ⟨m, j, hj⟩ := by simpa using hxall
  have hmd : m < d := by
    by_contra h
    have hdm : (d : ℕ∞) ≤ m := by exact_mod_cast Nat.le_of_not_gt h
    exact Set.disjoint_left.mp (CWComplex.disjoint_skeletonLT_openCell
      hdm) (hKd hx) hj
  simp
  refine ⟨m, hmd, j, ?_, RelCWComplex.openCell_subset_closedCell m j hj⟩
  exact (Set.Finite.mem_toFinset (hI m)).mpr ⟨x, hx, hj⟩

end FiniteChains.ClassicalCW
end

section
open scoped Classical Topology
open Set Topology Metric
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment

theorem closedUnitBall_connectedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ConnectedSpace (ClosedUnitBall E) := by
  apply isConnected_iff_connectedSpace.mp
  convert isConnected_closedBall (x := (0 : E)) zero_le_one using 1
  ext x
  simp
  rfl

/-- Every new disk meets the old connected space along its nonempty
boundary. This holds for arbitrary, possibly infinite families of disks. -/
theorem diskAttachment_connectedSpace {X J E : Type}
    [TopologicalSpace X] [ConnectedSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : BoundaryFamily J E → X) (a : UnitBoundary E) :
    ConnectedSpace (DiskAttachment r) := by
  letI := closedUnitBall_connectedSpace (E := E)
  let x₀ : X := Classical.choice inferInstance
  let o := old r (boundaryFamilyInclusion J E)
  have ho : Set.range o ⊆ connectedComponent (o x₀) :=
    (isConnected_range (old_continuous r _)).subset_connectedComponent ⟨x₀, rfl⟩
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨o x₀, Set.eq_univ_of_forall ?_⟩
  rintro (x | d)
  · exact ho ⟨x, rfl⟩
  · let f  :=
      fun v => cell r (boundaryFamilyInclusion J E) ⟨d.val.1, v⟩
    have hf : Continuous f := (cell_continuous r _).comp continuous_sigmaMk
    have hb  :=
      cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
        ⟨d.val.1, a⟩
    have hc  :=
      (isConnected_range hf).subset_connectedComponent
        ⟨unitBoundaryInclusion E a, hb⟩
        ⟨d.val.2, cell_of_not_mem r _ d.val d.property⟩
    rw [connectedComponent_eq (ho ⟨r ⟨d.val.1, a⟩, rfl⟩)]
    exact hc

/-- A distinguished boundary point for every positive-dimensional disk,
using the same sup norm as the original classical CW characteristic maps. -/
def positiveDiskBoundaryPoint (n : ℕ) (hn : 0 < n) : UnitBoundary (Fin n → ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨fun _ => 1, by simp [pi_norm_const]⟩

variable {X J : Type} [TopologicalSpace X] [T2Space X] [Nonempty X]
  [CWComplex (Set.univ : Set X)]

/-- Count all old cells once and all new cells once. In particular there
is no finiteness assumption on the dimension index itself. -/
def attachmentTotalCellEquiv (n : ℕ) :
    (Σ m, AttachmentCell (X := X) (J := J) n m) ≃
      (Σ m, RelCWComplex.cell (Set.univ : Set X) m) ⊕ J where
  toFun
    | ⟨m, Sum.inl j⟩ => Sum.inl ⟨m, j⟩
    | ⟨_, Sum.inr j⟩ => Sum.inr j.val
  invFun
    | Sum.inl ⟨m, j⟩ => ⟨m, Sum.inl j⟩
    | Sum.inr j => ⟨n, Sum.inr ⟨j, rfl⟩⟩
  left_inv := by
    rintro ⟨m, j | ⟨j, h⟩⟩
    · rfl
    · subst m
      rfl
  right_inv := by rintro (⟨m, j⟩ | j) <;> rfl

end FiniteChains.RelativeAttachment

namespace Whitehead
open FiniteChains.RelativeAttachment

variable (K : TwoComplex) {J : Type} (n : ℕ) (hn : 0 < n) (hn₂ : n ≤ 2)
  (r : C(BoundaryFamily J (Fin n → ℝ), K)) (x₀ : K)
  (hb : FiniteLowerBoundary n r)

/-- The extension is built directly on the original space, retaining its
old cells and adding only the specified one- or two-dimensional disks. -/
def diskAttachmentTwoComplex : TwoComplex where
  space := DiskAttachment r
  topology := inferInstance
  hausdorff := diskAttachment_t2Space r r.continuous
  cw := attachmentCW n r r.continuous x₀ hb
  connected := diskAttachment_connectedSpace r (positiveDiskBoundaryPoint n hn)
  dimension m hm := ⟨by
    intro j
    change AttachmentCell (X := K) (J := J) n m at j
    rcases j with j | ⟨j, h⟩
    · exact (K.dimension m hm).false j
    · omega⟩

def diskAttachmentOldSubcomplex :
    CWComplex.Subcomplex (Set.univ : Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) :=
  attachmentOldSubcomplex n r r.continuous x₀ hb

theorem diskAttachment_finiteCells (hK : FiniteCells K) [Finite J] :
    FiniteCells (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb) := by
  letI : Finite (Σ m, RelCWComplex.cell Set.univ m) := hK
  exact Finite.of_injective (attachmentTotalCellEquiv n)
    (attachmentTotalCellEquiv n).injective

/-- A nonempty attached family makes the old subcomplex proper. The
witness is the center of any added disk. -/
theorem diskAttachment_old_ne_univ [Nonempty J] :
    (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb :
      Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) ≠ Set.univ := by
  let j : J := Classical.choice inferInstance
  let d := interiorDiskPoint (E := Fin n → ℝ) j ⟨0, by simp⟩
  intro h
  have hd : fresh r (boundaryFamilyInclusion J (Fin n → ℝ)) d ∈
      (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb :
        Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) := by
    rw [h]
    trivial
  obtain ⟨x, hx⟩ := hd
  exact Sum.inl_ne_inr hx

end Whitehead
end

namespace Whitehead
open Topology

structure CWCellEmbedding (K L : TwoComplex) where
  map : C(K, L)
  closedEmbedding : IsClosedEmbedding map
  cellIndex : ∀ m, RelCWComplex.cell (Set.univ : Set K) m ↪
    RelCWComplex.cell (Set.univ : Set L) m
  openCell_image : ∀ m j,
    map '' CWComplex.openCell (C := (Set.univ : Set K)) m j =
      CWComplex.openCell (C := (Set.univ : Set L)) m (cellIndex m j)

namespace CWCellEmbedding

variable {K L M : TwoComplex}

def refl (K : TwoComplex) : CWCellEmbedding K K where
  map := ContinuousMap.id K
  closedEmbedding := IsClosedEmbedding.id
  cellIndex _ := Function.Embedding.refl _
  openCell_image _ _ := Set.image_id _

def comp (g : CWCellEmbedding L M) (f : CWCellEmbedding K L) : CWCellEmbedding K M where
  map := g.map.comp f.map
  closedEmbedding := g.closedEmbedding.comp f.closedEmbedding
  cellIndex m := (f.cellIndex m).trans (g.cellIndex m)
  openCell_image m j := by
    change (g.map ∘ f.map) '' _ = _
    rw [Set.image_comp, f.openCell_image, g.openCell_image]
    rfl

/-- The image has the CW subcomplex structure specified by the actual
cell images, not by a separately chosen CW decomposition of the range. -/
def imageSubcomplex (e : CWCellEmbedding K L) : CWComplex.Subcomplex (Set.univ : Set L) where
  carrier := Set.range e.map
  I m := Set.range (e.cellIndex m)
  closed' := e.closedEmbedding.isClosed_range
  union' := by
    rw [Set.empty_union]
    ext z
    constructor
    · intro hz
      obtain ⟨m, ⟨j, hj⟩, hz⟩ := by simpa only [Set.mem_iUnion] using hz
      obtain ⟨j, rfl⟩ := hj
      rw [← e.openCell_image] at hz
      exact Set.image_subset_range _ _ hz
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set K) m,
          CWComplex.openCell (C := (Set.univ : Set K)) m j := by
        rw [CWComplex.iUnion_openCell_eq_complex]
        trivial
      obtain ⟨m, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
      apply Set.mem_iUnion.mpr
      refine ⟨m, Set.mem_iUnion.mpr ⟨⟨e.cellIndex m j, ⟨j, rfl⟩⟩, ?_⟩⟩
      rw [← e.openCell_image]
      exact ⟨x, hj, rfl⟩

def imageHomeomorph (e : CWCellEmbedding K L) : K ≃ₜ (e.imageSubcomplex : Set L) :=
  e.closedEmbedding.isEmbedding.toHomeomorph

@[simp] theorem imageHomeomorph_val (e : CWCellEmbedding K L) (x : K) :
    (e.imageHomeomorph x).val = e.map x := rfl

def imageCellEquiv (e : CWCellEmbedding K L) (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set K) m ≃
      {j : RelCWComplex.cell (Set.univ : Set L) m // j ∈ e.imageSubcomplex.I m} :=
  Equiv.ofInjective (e.cellIndex m) (e.cellIndex m).injective

theorem initialIdentification (e : CWCellEmbedding K L) :
    InitialIdentification e.imageSubcomplex e.imageHomeomorph := by
  intro m
  exact ⟨e.imageCellEquiv m, e.openCell_image m⟩

theorem image_connectedSpace (e : CWCellEmbedding K L) :
    ConnectedSpace (e.imageSubcomplex : Set L) :=
  e.imageHomeomorph.surjective.connectedSpace e.imageHomeomorph.continuous

end CWCellEmbedding

/-- Each actual cellular disk extension supplies a closed embedding
retaining every original cell, for use in subsequent extensions. -/
def diskAttachmentCellEmbedding (K : TwoComplex) {J : Type}
    (n : ℕ) (hn : 0 < n) (hn₂ : n ≤ 2)
    (r : C(FiniteChains.RelativeAttachment.BoundaryFamily J (Fin n → ℝ), K)) (x₀ : K)
    (hb : FiniteChains.RelativeAttachment.FiniteLowerBoundary n r) :
    CWCellEmbedding K (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb) where
  map := ⟨FiniteChains.RelativeAttachment.old r
    (FiniteChains.RelativeAttachment.boundaryFamilyInclusion J (Fin n → ℝ)),
    FiniteChains.RelativeAttachment.old_continuous _ _⟩
  closedEmbedding := FiniteChains.RelativeAttachment.old_isClosedEmbedding r _ r.continuous
    (FiniteChains.RelativeAttachment.boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))
  cellIndex _ := ⟨Sum.inl, Sum.inl_injective⟩
  openCell_image :=
    FiniteChains.RelativeAttachment.attachment_old_openCell n r r.continuous x₀ hb

/-- A finite compatible family of embeddings yields the original chain
statement in the chosen common ambient two-complex. -/
theorem hasChain_of_cellEmbeddings {n : ℕ} (K : Fin (n + 1) → TwoComplex) (L : TwoComplex)
    (e : ∀ i, CWCellEmbedding (K i) L)
    (f : ∀ i : Fin n, C(K i.castSucc, K i.succ))
    (he : ∀ i : Fin n, (e i.succ).map.comp (f i) = (e i.castSucc).map)
    (hp : ∀ i : Fin n, ∃ x : K i.succ, (e i.succ).map x ∉ Set.range (e i.castSucc).map)
    (hk : ∀ i : Fin n, KillsPi2 (f i))
    (finite : Bool) (hfin : finite = true → FiniteCells L) :
    HasChain (K 0) n finite := by
  refine ⟨L, fun i => (e i).imageSubcomplex, (e 0).imageHomeomorph,
    (e 0).initialIdentification, hfin, fun i => (e i).image_connectedSpace, ?_⟩
  intro i
  have hs : Set.range (e i.castSucc).map ⊆ Set.range (e i.succ).map := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f i x, congrArg (fun g : C(K i.castSucc, L) => g x) (he i)⟩
  refine ⟨hs, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hp i
    intro heq
    apply hx
    change Set.range (e i.castSucc).map = Set.range (e i.succ).map at heq
    rw [heq]
    exact ⟨x, rfl⟩
  · apply (killsPi2_homotopyEquiv_square_iff
      (e i.castSucc).imageHomeomorph.toHomotopyEquiv
      (e i.succ).imageHomeomorph.toHomotopyEquiv (f i)
      ⟨Set.inclusion hs, continuous_inclusion hs⟩ ?_).mpr (hk i)
    have hsq :
        (⟨Set.inclusion hs, continuous_inclusion hs⟩ :
          C(((e i.castSucc).imageSubcomplex),
            ((e i.succ).imageSubcomplex))).comp
            (e i.castSucc).imageHomeomorph.toContinuousMap =
        (e i.succ).imageHomeomorph.toContinuousMap.comp (f i) := by
      apply ContinuousMap.ext
      intro x
      ext
      exact (congrArg (fun g : C(K i.castSucc, L) => g x) (he i)).symm
    exact hsq ▸ ContinuousMap.Homotopic.refl _

end Whitehead

namespace Whitehead

namespace CWCellEmbedding

variable {K : ℕ → TwoComplex} (f : ∀ i, CWCellEmbedding (K i) (K (i + 1)))

def chain (i j : ℕ) (hij : i ≤ j) : CWCellEmbedding (K i) (K j) :=
  Nat.leRecOn (C := fun k => CWCellEmbedding (K i) (K k)) hij
    (fun {k} e => (f k).comp e) (refl (K i))

theorem chain_map_self (i : ℕ) : (chain f i i le_rfl).map = ContinuousMap.id (K i) := by
  have he  :=
    Nat.leRecOn_self (next := fun {k} e => (f k).comp e) (refl (K i))
  exact congrArg (fun q : CWCellEmbedding (K i) (K i) => q.map) he

theorem chain_map_succ_right (i j : ℕ) (hij : i ≤ j) :
    (chain f i (j + 1) (Nat.le_trans hij (Nat.le_succ j))).map =
      (f j).map.comp (chain f i j hij).map := by
  have he : chain f i (j + 1) (Nat.le_trans hij (Nat.le_succ j)) =
      (f j).comp (chain f i j hij) :=
    Nat.leRecOn_succ (next := fun {k} e => (f k).comp e) hij (refl (K i))
  exact congrArg (fun q : CWCellEmbedding (K i) (K (j + 1)) => q.map) he

theorem chain_map_step (i j : ℕ) (hij : i + 1 ≤ j) :
    (chain f i j (Nat.le_trans (Nat.le_succ i) hij)).map =
      (chain f (i + 1) j hij).map.comp (f i).map := by
  induction hij with
  | refl =>
      rw [chain_map_self, chain_map_succ_right f i i le_rfl, chain_map_self]
      rfl
  | @step j hij ih =>
      rw [chain_map_succ_right f i j (Nat.le_trans (Nat.le_succ i) hij),
        chain_map_succ_right f (i + 1) j hij, ih]
      rfl

end CWCellEmbedding

theorem hasChain_of_successive_cellEmbeddings {K : ℕ → TwoComplex}
    (f : ∀ i, CWCellEmbedding (K i) (K (i + 1))) (n : ℕ)
    (hp : ∀ i, i < n → ∃ x : K (i + 1), x ∉ Set.range (f i).map)
    (hk : ∀ i, i < n → KillsPi2 (f i).map)
    (finite : Bool) (hfin : finite = true → FiniteCells (K n)) :
    HasChain (K 0) n finite := by
  let e (i : Fin (n + 1)) : CWCellEmbedding (K i.val) (K n) :=
    CWCellEmbedding.chain f i.val n (Nat.le_of_lt_succ i.isLt)
  apply hasChain_of_cellEmbeddings (fun i : Fin (n + 1) => K i.val) (K n)
    e (fun i => (f i.val).map) ?_ ?_ (fun i => hk i.val i.isLt) finite hfin
  · intro i
    exact (CWCellEmbedding.chain_map_step f i.val n i.isLt).symm
  · intro i
    obtain ⟨x, hx⟩ := hp i.val i.isLt
    refine ⟨x, ?_⟩
    rintro ⟨y, hy⟩
    apply hx
    refine ⟨y, (e i.succ).closedEmbedding.injective ?_⟩
    have hs := congrArg (fun g : C(K i.val, K n) => g y)
      (CWCellEmbedding.chain_map_step f i.val n i.isLt)
    exact hs.symm.trans hy

end Whitehead

section
open scoped Classical
open Set Topology Metric
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalSkeletonAttachment
open RelativeAttachment

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

abbrev SkeletonCarrier (n : ℕ) :=
  {x : X // x ∈ CWComplex.skeletonLT C (n : ℕ∞)}

/-- The literal inclusion of consecutive original skeleta. -/
def skeletonInclusion (n : ℕ) : C(SkeletonCarrier C n, SkeletonCarrier C (n + 1)) where
  toFun x := ⟨x.val, CWComplex.skeletonLT_mono (C := C)
    (by exact_mod_cast Nat.le_succ n) x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The original characteristic map restricted to its genuine closed disk. -/
def characteristicDisk (n : ℕ) (j : RelCWComplex.cell C n) :
    C(ClosedUnitBall (Fin n → ℝ), X) where
  toFun x := RelCWComplex.map n j x.val
  continuous_toFun := (RelCWComplex.continuousOn n j).comp_continuous
    continuous_subtype_val (fun x => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)

def characteristicDiskFamily (n : ℕ) :
    C(DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ), X) where
  toFun d := characteristicDisk C n d.1 d.2
  continuous_toFun := continuous_sigma (fun j => (characteristicDisk C n j).continuous)

/-- The attaching map is exactly the restriction of the original CW maps. -/
def skeletonAttachingMap (n : ℕ) :
    C(BoundaryFamily (RelCWComplex.cell C n) (Fin n → ℝ), SkeletonCarrier C n) where
  toFun a := ⟨RelCWComplex.map n a.1 a.2.val,
    CWComplex.cellFrontier_subset_skeletonLT n a.1
      ⟨a.2.val, by simpa only [Metric.mem_sphere, dist_zero_right] using a.2.property, rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (characteristicDiskFamily C n).continuous.comp
      (boundaryFamilyInclusion_isClosedEmbedding (RelCWComplex.cell C n) (Fin n → ℝ)).continuous

/-- Evaluation of the literal attachment into the original ambient CW space. -/
def skeletonAttachmentOrigin (n : ℕ) : C(DiskAttachment (skeletonAttachingMap C n), X) :=
  desc (skeletonAttachingMap C n)
    (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))
    ⟨Subtype.val, continuous_subtype_val⟩ (characteristicDiskFamily C n) (fun _ => rfl)

@[simp] theorem skeletonAttachmentOrigin_old (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAttachmentOrigin C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x) = x.val := rfl

@[simp] theorem skeletonAttachmentOrigin_cell (n : ℕ)
    (j : RelCWComplex.cell C n) (x : ClosedUnitBall (Fin n → ℝ)) :
    skeletonAttachmentOrigin C n
      (cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) =
      RelCWComplex.map n j x.val := desc_cell ..

omit [T2Space X] in
theorem disk_interior_norm (n : ℕ)
    (d : DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ))
    (hd : d ∉ range (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))) :
    ‖d.2.val‖ < 1 :=
  lt_of_le_of_ne d.2.property (fun h => hd
    ((boundaryFamilyInclusion_range (RelCWComplex.cell C n) (Fin n → ℝ) d).mpr h))

omit [T2Space X] in
theorem characteristic_mem_open (n : ℕ) (j : RelCWComplex.cell C n)
    (x : Fin n → ℝ) (hx : ‖x‖ < 1) :
    RelCWComplex.map n j x ∈ CWComplex.openCell n j :=
  ⟨x, by simpa only [Metric.mem_ball, dist_zero_right] using hx, rfl⟩

/-- No new interior point is identified with an old point, or with a
different original open cell. -/
theorem skeletonAttachmentOrigin_injective (n : ℕ) :
    Function.Injective (skeletonAttachmentOrigin C n) := by
  rintro (x | ⟨⟨j, x⟩, hx⟩) (y | ⟨⟨k, y⟩, hy⟩) h
  · apply congrArg Sum.inl
    exact Subtype.ext h
  · change x.val = RelCWComplex.map n k y.val at h
    have hyopen := characteristic_mem_open C n k y.val
      (disk_interior_norm C n ⟨k, y⟩ hy)
    have hopen : x.val ∈ CWComplex.openCell n k := by rw [h]; exact hyopen
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := k)
        (show (n : ℕ∞) ≤ n from le_rfl)) x.property hopen)
  · change RelCWComplex.map n j x.val = y.val at h
    have hxopen := characteristic_mem_open C n j x.val
      (disk_interior_norm C n ⟨j, x⟩ hx)
    have hopen : y.val ∈ CWComplex.openCell n j := by rw [← h]; exact hxopen
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := j)
        (show (n : ℕ∞) ≤ n from le_rfl)) y.property hopen)
  · change RelCWComplex.map n j x.val = RelCWComplex.map n k y.val at h
    have hxlt := disk_interior_norm C n ⟨j, x⟩ hx
    have hylt := disk_interior_norm C n ⟨k, y⟩ hy
    have hxopen := characteristic_mem_open C n j x.val hxlt
    have hyopen : RelCWComplex.map n j x.val ∈ CWComplex.openCell n k := by
      rw [h]
      exact characteristic_mem_open C n k y.val hylt
    have hlabels  :=
      RelCWComplex.eq_of_not_disjoint_openCell (fun hd => Set.disjoint_left.mp hd hxopen hyopen)
    have hjk  := eq_of_heq (Sigma.mk.inj_iff.mp hlabels).2
    subst k
    have hxy  := (RelCWComplex.map n j).injOn
      (by rw [RelCWComplex.source_eq]; simpa using hxlt)
      (by rw [RelCWComplex.source_eq]; simpa using hylt) h
    apply congrArg Sum.inr
    apply Subtype.ext
    exact congrArg (Sigma.mk j) (Subtype.ext hxy)

theorem skeletonAttachmentOrigin_mem (n : ℕ)
    (z : DiskAttachment (skeletonAttachingMap C n)) :
    skeletonAttachmentOrigin C n z ∈ CWComplex.skeletonLT C (n + 1) := by
  obtain ⟨w, rfl⟩ := quotientMap_surjective (skeletonAttachingMap C n)
    (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) z
  cases w with
  | inl x =>
    exact CWComplex.skeletonLT_mono (C := C)
      (show (n : ℕ∞) ≤ n + 1 from le_self_add) x.property
  | inr d =>
    rw [show quotientMap (skeletonAttachingMap C n)
      (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) (Sum.inr d) =
      cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) d from rfl]
    rcases d with ⟨j, x⟩
    rw [skeletonAttachmentOrigin_cell]
    exact CWComplex.closedCell_subset_skeletonLT n j
      ⟨x.val, by simpa using x.property, rfl⟩

/-- The evaluation with codomain the next skeleton. -/
def skeletonAttachmentMap (n : ℕ) :
    C(DiskAttachment (skeletonAttachingMap C n), SkeletonCarrier C (n + 1)) := by
  have hm : ∀ z, skeletonAttachmentOrigin C n z ∈
      CWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) := by
    intro z
    simpa only [Nat.cast_add, Nat.cast_one] using skeletonAttachmentOrigin_mem C n z
  exact ⟨fun z => ⟨skeletonAttachmentOrigin C n z, hm z⟩,
    (skeletonAttachmentOrigin C n).continuous.subtype_mk hm⟩




/-- Weak topology is checked cell by cell; no compactness of the family
or finiteness of either skeleton is used. -/
theorem skeletonAttachmentOrigin_isClosedMap (n : ℕ) :
    IsClosedMap (skeletonAttachmentOrigin C n) := by
  intro A hA
  have hupper : skeletonAttachmentOrigin C n '' A ⊆ CWComplex.skeletonLT C (n + 1) := by
    rintro _ ⟨z, _, rfl⟩
    exact skeletonAttachmentOrigin_mem C n z
  apply CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (hupper.trans (CWComplex.skeletonLT C (n + 1)).subset_complex)
  intro m _hm j
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · right
    rw [(show skeletonAttachmentOrigin C n '' A ∩ CWComplex.closedCell m j =
      (Subtype.val '' ((old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))) ⁻¹' A)) ∩
        CWComplex.closedCell m j by
      have hcell : CWComplex.closedCell m j ⊆ CWComplex.skeletonLT C n :=
        (CWComplex.closedCell_subset_skeletonLT m j).trans
          (CWComplex.skeletonLT_mono (C := C) (by exact_mod_cast Nat.succ_le_of_lt hmn))
      ext x
      constructor
      · rintro ⟨⟨z, hz, hzx⟩, hx⟩
        let b : SkeletonCarrier C n := ⟨x, hcell hx⟩
        have hzb : z = old (skeletonAttachingMap C n)
            (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) b :=
          skeletonAttachmentOrigin_injective C n hzx
        refine ⟨⟨b, ?_, rfl⟩, hx⟩
        change old _ _ b ∈ A
        rw [← hzb]
        exact hz
      · rintro ⟨⟨b, hb, rfl⟩, hx⟩
        exact ⟨⟨old _ _ b, hb, rfl⟩, hx⟩)]
    apply IsClosed.inter _ CWComplex.isClosed_closedCell
    exact (CWComplex.skeletonLT C n).closed.isClosedMap_subtype_val _
      (hA.preimage (old_continuous _ _))
  · right
    subst m
    rw [(show skeletonAttachmentOrigin C n '' A ∩ CWComplex.closedCell n j =
      characteristicDisk C n j '' ((fun x : ClosedUnitBall (Fin n → ℝ) =>
        cell (skeletonAttachingMap C n)
          (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' A) by
      ext x
      constructor
      · rintro ⟨⟨z, hz, hzx⟩, ⟨y, hy, hyx⟩⟩
        let d : ClosedUnitBall (Fin n → ℝ) :=
          ⟨y, by simpa using hy⟩
        have hdz  :=
          skeletonAttachmentOrigin_injective C n
            ((skeletonAttachmentOrigin_cell C n j d).trans (hyx.trans hzx.symm))
        refine ⟨d, ?_, hyx⟩
        change cell _ _ ⟨j, d⟩ ∈ A
        rw [hdz]
        exact hz
      · rintro ⟨d, hd, hdx⟩
        exact ⟨⟨cell _ _ ⟨j, d⟩, hd, (skeletonAttachmentOrigin_cell C n j d).trans hdx⟩,
          ⟨d.val, by simpa using d.property, hdx⟩⟩)]
    letI : CompactSpace (ClosedUnitBall (Fin n → ℝ)) :=
      isCompact_iff_compactSpace.mp (by
        convert isCompact_closedBall (0 : Fin n → ℝ) 1 using 1
        ext x
        simp
        rfl)
    have hc : IsClosed ((fun x : ClosedUnitBall (Fin n → ℝ) =>
        cell (skeletonAttachingMap C n)
          (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' A) :=
      hA.preimage ((cell_continuous _ _).comp continuous_sigmaMk)
    exact (hc.isCompact.image (characteristicDisk C n j).continuous).isClosed
  · left
    exact (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := j)
      (show (n : ℕ∞) + 1 ≤ m by exact_mod_cast Nat.succ_le_of_lt hnm)).mono_left hupper


/-- The actual attachment is homeomorphic to the next original skeleton. -/
def skeletonAttachmentHomeomorph (n : ℕ) :
    DiskAttachment (skeletonAttachingMap C n) ≃ₜ SkeletonCarrier C (n + 1) :=
  (Equiv.ofBijective (skeletonAttachmentMap C n)
    ⟨fun _ _ h => skeletonAttachmentOrigin_injective C n (congrArg Subtype.val h),
      (by
        intro x
        have hx : x.val ∈ (CWComplex.skeletonLT C n : Set X) ∪
            ⋃ j : RelCWComplex.cell C n, CWComplex.closedCell n j := by
          rw [CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
          simpa using (show x.val ∈ (CWComplex.skeletonLT C (n + 1) : Set X) from x.property)
        rcases hx with hx | hx
        · refine ⟨old (skeletonAttachingMap C n)
            (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨x.val, hx⟩, ?_⟩
          exact Subtype.ext rfl
        · obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
          obtain ⟨y, hy, hyx⟩ := hx
          let d : ClosedUnitBall (Fin n → ℝ) :=
            ⟨y, by simpa using hy⟩
          refine ⟨cell (skeletonAttachingMap C n)
            (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, d⟩, ?_⟩
          apply Subtype.ext
          exact (skeletonAttachmentOrigin_cell C n j d).trans hyx)⟩).toHomeomorphOfContinuousClosed
    (skeletonAttachmentMap C n).continuous (show IsClosedMap (skeletonAttachmentMap C n) by
      intro A hA
      have he : skeletonAttachmentMap C n '' A =
          Subtype.val ⁻¹' (skeletonAttachmentOrigin C n '' A) := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, rfl⟩
        · rintro ⟨z, hz, hzx⟩
          exact ⟨z, hz, Subtype.ext hzx⟩
      rw [he]
      exact (skeletonAttachmentOrigin_isClosedMap C n A hA).preimage continuous_subtype_val)

/-- The same identification in the skeleton-to-attachment direction. -/
def skeletonAsDiskAttachment (n : ℕ) :
    SkeletonCarrier C (n + 1) ≃ₜ DiskAttachment (skeletonAttachingMap C n) :=
  (skeletonAttachmentHomeomorph C n).symm

@[simp] theorem skeletonAttachmentHomeomorph_old_eq (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAttachmentHomeomorph C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x) =
      skeletonInclusion C n x := rfl

@[simp] theorem skeletonAsDiskAttachment_inclusion (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAsDiskAttachment C n (skeletonInclusion C n x) =
      old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x := by
  rw [← skeletonAttachmentHomeomorph_old_eq C n x]
  exact (skeletonAttachmentHomeomorph C n).symm_apply_apply _

@[simp] theorem skeletonAttachmentHomeomorph_old (n : ℕ) (x : SkeletonCarrier C n) :
    (skeletonAttachmentHomeomorph C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x)).val = x.val := rfl

@[simp] theorem skeletonAttachmentHomeomorph_cell (n : ℕ)
    (j : RelCWComplex.cell C n) (x : ClosedUnitBall (Fin n → ℝ)) :
    (skeletonAttachmentHomeomorph C n
      (cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩)).val =
      RelCWComplex.map n j x.val := skeletonAttachmentOrigin_cell C n j x

end FiniteChains.ClassicalSkeletonAttachment
end

section
open scoped Classical
open Set Topology
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment

def OneSkeleton (K : Whitehead.TwoComplex) := SkeletonCarrier (Set.univ : Set K) 2

instance (K : Whitehead.TwoComplex) : TopologicalSpace (OneSkeleton K) :=
  inferInstanceAs (TopologicalSpace (SkeletonCarrier (Set.univ : Set K) 2))

theorem twoComplex_mem_skeleton_three (K : Whitehead.TwoComplex) (x : K) :
    x ∈ CWComplex.skeletonLT (Set.univ : Set K) (3 : ℕ∞) := by
  have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell Set.univ n,
      CWComplex.closedCell n j := by rw [CWComplex.union]; trivial
  obtain ⟨n, j, hj⟩ := by simpa using hx
  have hn : n ≤ 2 := by
    by_contra h
    letI := K.dimension n (Nat.lt_of_not_ge h)
    exact isEmptyElim j
  exact CWComplex.skeletonLT_mono
    (show (n : ℕ∞) + 1 ≤ 3 by exact_mod_cast (by omega))
    (CWComplex.closedCell_subset_skeletonLT n j hj)

/-- Every path between original one-skeleton points is homotopic to a
path entirely in that original one-skeleton, fixing both endpoints. -/
theorem path_into_oneSkeleton (K : Whitehead.TwoComplex) (x y : OneSkeleton K)
    (p : Path x.val y.val) :
    ∃ q : Path x y, Path.Homotopic p (q.map continuous_subtype_val) := by
  let P : Path (skeletonInclusion Set.univ 2 x)
      (skeletonInclusion Set.univ 2 y) := {
    toFun := fun t => ⟨p t, twoComplex_mem_skeleton_three K (p t)⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let e := skeletonAsDiskAttachment (Set.univ : Set K) 2
  let r := skeletonAttachingMap (Set.univ : Set K) 2
  let P' := (P.map e.continuous).cast
    (skeletonAsDiskAttachment_inclusion Set.univ 2 x).symm
    (skeletonAsDiskAttachment_inclusion Set.univ 2 y).symm
  obtain ⟨q, hq⟩ := twoCellAttachment_path_into_old r r.continuous x y P'
  refine ⟨q, ?_⟩
  have h := hq.map (skeletonAttachmentOrigin Set.univ 2)
  have hleft : P'.map (skeletonAttachmentOrigin Set.univ 2).continuous = p := by
    apply Path.ext
    funext t
    change (skeletonAttachmentHomeomorph Set.univ 2
      ((skeletonAttachmentHomeomorph Set.univ 2).symm (P t))).val = p t
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hright : (q.map (old_continuous r
      (boundaryFamilyInclusion (RelCWComplex.cell Set.univ 2) (Fin 2 → ℝ)))).map
        (skeletonAttachmentOrigin Set.univ 2).continuous =
      q.map continuous_subtype_val := by
    apply Path.ext
    funext t
    rfl
  rwa [hleft, hright] at h

end FiniteChains.ClassicalCW
end

section
open scoped Topology unitInterval Classical
open Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalCW
open RelativeAttachment

def pointVertexInOneSkeleton (K : Whitehead.TwoComplex) (x : K) : OneSkeleton K :=
  ⟨vertexPoint (pointVertex x), by
    apply CWComplex.skeletonLT_mono (C := (Set.univ : Set K))
      (show (0 : ℕ∞) + 1 ≤ 2 by norm_num)
    apply CWComplex.closedCell_subset_skeletonLT 0 (pointVertex x)
    rw [RelCWComplex.closedCell_zero_eq_singleton]
    rfl⟩

/-- Any continuous square-boundary map can be moved into the original
one-skeleton, without any initial condition on its corner values. -/
theorem squareBoundary_into_oneSkeleton (K : Whitehead.TwoComplex)
    (r : C(SquareBoundary, K)) :
    ∃ q : C(SquareBoundary, OneSkeleton K),
      r.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(OneSkeleton K, K)).comp q) := by
  let v  := fun z => pointVertexInOneSkeleton K (r z)
  let p z : Path (r z) (v z).val := pointVertexPath (r z)
  let E s := intervalEndpointExtension (r.comp (squareSideMap s))
    (p (squareSideMap s 0)) (p (squareSideMap s 1))
  have hE : ∀ s τ t, t = 0 ∨ t = 1 →
      (E s).map (τ, t) = p (squareSideMap s t) τ := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · exact (E s).side_zero τ
    · exact (E s).side_one τ
  let G := squareBoundaryHomotopyPasting (fun s => (E s).map) (fun τ z => p z τ) hE
  let r₁ := G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  have hG₀ : ∀ z, G (0, z) = r z := by
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
    change squareBoundaryHomotopyPasting _ _ hE (0, squareSideMap s t) = r (squareSideMap s t)
    rw [squareBoundaryHomotopyPasting_side]
    exact (E s).zero t
  let H₀ : r.Homotopy r₁ := {
    toContinuousMap := G
    map_zero_left := hG₀
    map_one_left := fun _ => rfl }
  let l s : Path (v (squareSideMap s 0)).val (v (squareSideMap s 1)).val := {
    toFun := fun t => (E s).map (1, t)
    continuous_toFun := (E s).map.continuous.comp (continuous_const.prodMk continuous_id)
    source' := ((E s).side_zero 1).trans (p (squareSideMap s 0)).target
    target' := ((E s).side_one 1).trans (p (squareSideMap s 1)).target }
  have hl : ∀ s, ∃ q : Path (v (squareSideMap s 0)) (v (squareSideMap s 1)),
      (l s).Homotopic (q.map continuous_subtype_val) := by
    intro s
    exact path_into_oneSkeleton K _ _ (l s)
  choose q hq using hl
  have hqV : ∀ s t, t = 0 ∨ t = 1 → q s t = v (squareSideMap s t) := by
    intro s t ht
    rcases ht with rfl | rfl
    · simp
    · simp
  let Q := squareBoundaryPasting (fun s => (q s).toContinuousMap) v hqV
  let H s := Classical.choice (hq s)
  have hHV : ∀ s τ t, t = 0 ∨ t = 1 →
      H s (τ, t) = (v (squareSideMap s t)).val := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · simp
    · simp
  let G₁ := squareBoundaryHomotopyPasting (fun s => (H s).toHomotopy.toContinuousMap)
    (fun _ z => (v z).val) hHV
  let ι : C(OneSkeleton K, K) := ⟨Subtype.val, continuous_subtype_val⟩
  let H₁ : r₁.Homotopy (ι.comp Q) := {
    toContinuousMap := G₁
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (0, squareSideMap s t) = G (1, squareSideMap s t)
      rw [squareBoundaryHomotopyPasting_side, squareBoundaryHomotopyPasting_side]
      exact (H s).apply_zero t
    map_one_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (1, squareSideMap s t) = (Q (squareSideMap s t)).val
      rw [squareBoundaryHomotopyPasting_side, squareBoundaryPasting_side]
      exact (H s).apply_one t }
  exact ⟨Q, ⟨H₀.trans H₁⟩⟩

/-- This is the actual normed circle used by classical CW attachments,
not a replacement of the attaching domain by a combinatorial loop. -/
theorem boundary_into_oneSkeleton (K : Whitehead.TwoComplex)
    (r : C(UnitBoundary (Fin 2 → ℝ), K)) :
    ∃ q : C(UnitBoundary (Fin 2 → ℝ), OneSkeleton K),
      r.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(OneSkeleton K, K)).comp q) := by
  let e := unitBoundarySquareHomeomorph
  obtain ⟨q, hq⟩ := squareBoundary_into_oneSkeleton K (r.comp e.symm.toContinuousMap)
  refine ⟨q.comp e.toContinuousMap, ?_⟩
  have h := hq.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  simp_all

/-- Arbitrary families are cellularized simultaneously. Each new boundary
has finite support in the original lower-dimensional cells; the whole
family and the old CW complex may both be infinite. -/
theorem boundaryFamily_into_oneSkeleton (K : Whitehead.TwoComplex) {J : Type}
    (r : C(BoundaryFamily J (Fin 2 → ℝ), K)) :
    ∃ q : C(BoundaryFamily J (Fin 2 → ℝ), K),
      r.Homotopic q ∧ FiniteLowerBoundary 2 q := by
  let rj j : C(UnitBoundary (Fin 2 → ℝ), K) :=
    r.comp ⟨fun a : UnitBoundary (Fin 2 → ℝ) => ⟨j, a⟩, by
      exact continuous_sigmaMk («σ» := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩
  have hj := fun j => boundary_into_oneSkeleton K (rj j)
  choose q hq using hj
  let ι : C(OneSkeleton K, K) := ⟨Subtype.val, continuous_subtype_val⟩
  let Q : C(BoundaryFamily J (Fin 2 → ℝ), K) :=
    ⟨fun a => (q a.1 a.2).val,
      continuous_sigma (fun j => continuous_subtype_val.comp (q j).continuous)⟩
  let H j := Classical.choice (hq j)
  let F : C(BoundaryFamily J (Fin 2 → ℝ), C(I, K)) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  refine ⟨Q, ⟨{
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }⟩, ?_⟩
  letI : CompactSpace (UnitBoundary (Fin 2 → ℝ)) := isCompact_iff_compactSpace.mp (by
    convert isCompact_sphere (0 : Fin 2 → ℝ) 1 using 1
    ext x
    simp
    rfl)
  intro j
  obtain ⟨support, hsupport⟩ := IsCompact.finite_lower_support (isCompact_range (ι.comp (q j)).continuous) 2
    (by rintro _ ⟨a, rfl⟩; exact (q j a).property)
  exact ⟨support, fun a => hsupport ⟨a, rfl⟩⟩

end FiniteChains.ClassicalCW
end

namespace Whitehead
open scoped Topology Classical
open FiniteChains.RelativeAttachment

variable (K : TwoComplex) {P J : Type} [TopologicalSpace P]
  (e : ContinuousMap.HomotopyEquiv P K) (n : ℕ)
  (r : C(BoundaryFamily J (Fin n → ℝ), P))

/-- The actual result of transfer, including the commuting old-space
square and finite/properness consequences of the concrete added disks. -/
structure CellularDiskTransfer where
  target : TwoComplex
  oldEmbedding : CWCellEmbedding K target
  comparison : ContinuousMap.HomotopyEquiv (DiskAttachment r) target
  square : comparison.toFun.comp
      (⟨old r (boundaryFamilyInclusion J (Fin n → ℝ)), old_continuous _ _⟩ :
        C(P, DiskAttachment r)) = oldEmbedding.map.comp e.toFun
  finite : FiniteCells K → Finite J → FiniteCells target
  proper : Nonempty J → ∃ z : target, z ∉ Set.range oldEmbedding.map

def cellularDiskTransferOfRepresentative (hn : 0 < n) (hn₂ : n ≤ 2)
    (q : C(BoundaryFamily J (Fin n → ℝ), K))
    (H : (e.toFun.comp r).Homotopy q) (hq : FiniteLowerBoundary n q) :
    CellularDiskTransfer K e n r := by
  let x₀ : K := Classical.choice inferInstance
  let L := diskAttachmentTwoComplex K n hn hn₂ q x₀ hq
  let E := diskAttachmentCellEmbedding K n hn hn₂ q x₀ hq
  let D := (diskAttachmentBaseChangeHomotopyEquiv r e).trans
    (diskAttachingHomotopyEquiv (e.toFun.comp r) q H)
  refine {
    target := L
    oldEmbedding := E
    comparison := D
    square := ?_
    finite := ?_
    proper := ?_ }
  · apply ContinuousMap.ext
    intro p
    change diskAttachingHomotopyEquiv (e.toFun.comp r) q H
      (diskAttachmentBaseChangeHomotopyEquiv r e (old r _ p)) = old q _ (e p)
    exact (congrArg (diskAttachingHomotopyEquiv (e.toFun.comp r) q H)
      (diskAttachmentBaseChangeHomotopyEquiv_old r e p)).trans
        (diskAttachingHomotopyEquiv_old (e.toFun.comp r) q H (e p))
  · intro hK hJ
    letI := hJ
    exact diskAttachment_finiteCells K n hn hn₂ q x₀ hq hK
  · intro hJ
    letI := hJ
    have hnrange : Set.range E.map ≠ Set.univ :=
      diskAttachment_old_ne_univ K n hn hn₂ q x₀ hq
    by_contra! hall
    exact hnrange (Set.eq_univ_of_forall hall)

/-- Every actual disk extension in one of the two permitted dimensions
has a transfer. All cellularity and finite boundary-support conditions
are supplied by the original-CW cellularization constructions. -/
def cellularDiskTransfer (hn : n = 1 ∨ n = 2) : CellularDiskTransfer K e n r := by
  by_cases h₁ : n = 1
  · subst n
    let a := e.toFun.comp r
    exact cellularDiskTransferOfRepresentative K e 1 r zero_lt_one (by omega)
      (vertexBoundaryMap a) (vertexBoundaryHomotopy a)
      (vertexBoundaryMap_finiteLowerBoundary a)
  · have h₂ : n = 2 := hn.resolve_left h₁
    subst n
    let a := e.toFun.comp r
    let h := FiniteChains.ClassicalCW.boundaryFamily_into_oneSkeleton K a
    let q := Classical.choose h
    have hq := Classical.choose_spec h
    exact cellularDiskTransferOfRepresentative K e 2 r (by omega) le_rfl q
      (Classical.choice hq.1) hq.2


end Whitehead

namespace Whitehead
open scoped Topology Classical
open FiniteChains.RelativeAttachment

variable (K : TwoComplex) {P J₁ J₂ : Type} [TopologicalSpace P]
  (e : ContinuousMap.HomotopyEquiv P K)
  (r₁ : C(BoundaryFamily J₁ (Fin 1 → ℝ), P))
  (r₂ : C(BoundaryFamily J₂ (Fin 2 → ℝ), DiskAttachment r₁))

def oneTwoAttachmentMap : C(P, DiskAttachment r₂) :=
  (⟨old r₂ (boundaryFamilyInclusion J₂ (Fin 2 → ℝ)), old_continuous _ _⟩ :
    C(DiskAttachment r₁, DiskAttachment r₂)).comp
      ⟨old r₁ (boundaryFamilyInclusion J₁ (Fin 1 → ℝ)), old_continuous _ _⟩

structure OneTwoDiskTransfer where
  target : TwoComplex
  oldEmbedding : CWCellEmbedding K target
  comparison : ContinuousMap.HomotopyEquiv (DiskAttachment r₂) target
  square : comparison.toFun.comp (oneTwoAttachmentMap r₁ r₂) =
    oldEmbedding.map.comp e.toFun
  finite : FiniteCells K → Finite J₁ → Finite J₂ → FiniteCells target
  proper : Nonempty J₁ ∨ Nonempty J₂ → ∃ z : target, z ∉ Set.range oldEmbedding.map

def oneTwoDiskTransfer : OneTwoDiskTransfer K e r₁ r₂ := by
  let T₁ := cellularDiskTransfer K e 1 r₁ (Or.inl rfl)
  let T₂ := cellularDiskTransfer T₁.target T₁.comparison 2 r₂ (Or.inr rfl)
  refine {
    target := T₂.target
    oldEmbedding := T₂.oldEmbedding.comp T₁.oldEmbedding
    comparison := T₂.comparison
    square := ?_
    finite := fun hK hJ₁ hJ₂ => T₂.finite (T₁.finite hK hJ₁) hJ₂
    proper := ?_ }
  · apply ContinuousMap.ext
    intro p
    have h₂ := congrArg (fun f : C(DiskAttachment r₁, T₂.target) =>
      f (old r₁ (boundaryFamilyInclusion J₁ (Fin 1 → ℝ)) p)) T₂.square
    have h₁ := congrArg (fun f : C(P, T₁.target) => f p) T₁.square
    exact h₂.trans (congrArg T₂.oldEmbedding.map h₁)
  · intro hJ
    rcases hJ with hJ | hJ
    · obtain ⟨z, hz⟩ := T₁.proper hJ
      refine ⟨T₂.oldEmbedding.map z, ?_⟩
      rintro ⟨x, hx⟩
      exact hz ⟨x, T₂.oldEmbedding.closedEmbedding.injective hx⟩
    · obtain ⟨z, hz⟩ := T₂.proper hJ
      refine ⟨z, ?_⟩
      rintro ⟨x, hx⟩
      exact hz ⟨T₁.oldEmbedding.map x, hx⟩

namespace OneTwoDiskTransfer

theorem killsPi2_iff (T : OneTwoDiskTransfer K e r₁ r₂) :
    KillsPi2 T.oldEmbedding.map ↔ KillsPi2 (oneTwoAttachmentMap r₁ r₂) := by
  apply killsPi2_homotopyEquiv_square_iff e T.comparison
  rw [T.square]

end OneTwoDiskTransfer
end Whitehead

namespace Whitehead
open FiniteChains.RelativeAttachment
open scoped Topology Classical

structure DiskExtensionModel (P Q : Type) [TopologicalSpace P] [TopologicalSpace Q] where
  oneCells : Type
  twoCells : Type
  oneAttaching : C(BoundaryFamily oneCells (Fin 1 → ℝ), P)
  twoAttaching : C(BoundaryFamily twoCells (Fin 2 → ℝ), DiskAttachment oneAttaching)
  comparison : ContinuousMap.HomotopyEquiv (DiskAttachment twoAttaching) Q

namespace DiskExtensionModel

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (M : DiskExtensionModel P Q)

def map : C(P, Q) := M.comparison.toFun.comp (oneTwoAttachmentMap M.oneAttaching M.twoAttaching)

theorem killsPi2_iff : KillsPi2 M.map ↔ KillsPi2 (oneTwoAttachmentMap M.oneAttaching M.twoAttaching) :=
  killsPi2_homotopyEquiv_postcomp_iff M.comparison _

end DiskExtensionModel

structure TransferredModelStage (P : Type) [TopologicalSpace P] where
  complex : TwoComplex
  comparison : ContinuousMap.HomotopyEquiv P complex

variable {P : ℕ → Type} [∀ i, TopologicalSpace (P i)]
  (M : ∀ i, DiskExtensionModel (P i) (P (i + 1)))
  (K : TwoComplex) (e₀ : ContinuousMap.HomotopyEquiv (P 0) K)

def transferredModelStage : (i : ℕ) → TransferredModelStage (P i)
  | 0 => ⟨K, e₀⟩
  | i + 1 =>
    let R := transferredModelStage i
    let T := oneTwoDiskTransfer R.complex R.comparison (M i).oneAttaching (M i).twoAttaching
    ⟨T.target, (M i).comparison.symm.trans T.comparison⟩

def transferredModelStep (i : ℕ) :
    CWCellEmbedding (transferredModelStage M K e₀ i).complex
      (transferredModelStage M K e₀ (i + 1)).complex :=
  (oneTwoDiskTransfer (transferredModelStage M K e₀ i).complex
    (transferredModelStage M K e₀ i).comparison (M i).oneAttaching (M i).twoAttaching).oldEmbedding



theorem transferredModelStage_finite (n : ℕ) (hK : FiniteCells K)
    (hfin : ∀ i, i < n → Finite (M i).oneCells ∧ Finite (M i).twoCells) :
    FiniteCells (transferredModelStage M K e₀ n).complex := by
  have h : ∀ m, m ≤ n → FiniteCells (transferredModelStage M K e₀ m).complex := by
    intro m
    induction m with
    | zero => exact fun _ => hK
    | succ m ih =>
        intro hm
        have hc := hfin m (by omega)
        exact (oneTwoDiskTransfer (transferredModelStage M K e₀ m).complex
          (transferredModelStage M K e₀ m).comparison
          (M m).oneAttaching (M m).twoAttaching).finite
            (ih (by omega)) hc.1 hc.2
  exact h n le_rfl

include e₀ in
/-- All topological transfer and common-ambient construction steps are
discharged here. Applications supply the concrete relative models and
their already-derived zero-on-pi2 and strictness conclusions. -/
theorem hasChain_of_diskExtensionModels (n : ℕ)
    (hp : ∀ i, i < n → Nonempty (M i).oneCells ∨ Nonempty (M i).twoCells)
    (hz : ∀ i, i < n → KillsPi2 (M i).map)
    (finite : Bool)
    (hfin : finite = true → FiniteCells K ∧
      ∀ i, i < n → Finite (M i).oneCells ∧ Finite (M i).twoCells) :
    HasChain K n finite := by
  apply hasChain_of_successive_cellEmbeddings (transferredModelStep M K e₀) n
    (fun i hi => ((oneTwoDiskTransfer (transferredModelStage M K e₀ i).complex
    (transferredModelStage M K e₀ i).comparison
    (M i).oneAttaching (M i).twoAttaching).proper (hp i hi)))
    (fun i hi => (by
      apply (OneTwoDiskTransfer.killsPi2_iff _ _ _ _
        (oneTwoDiskTransfer (transferredModelStage M K e₀ i).complex
          (transferredModelStage M K e₀ i).comparison (M i).oneAttaching (M i).twoAttaching)).mpr
      exact ((M i).killsPi2_iff).mp (hz i hi))) finite
  intro hf
  exact transferredModelStage_finite M K e₀ n (hfin hf).1 (hfin hf).2

end Whitehead

namespace FiniteChains.RelativeAttachment.DiskPresentationExtension
open ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} (f : A ↪ B) (c : J ↪ K)
    (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
    (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
    (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

abbrev NewGenerators := {b : B // b ∉ Set.range f}
abbrev NewRelators := {k : K // k ∉ Set.range c}

def sourceMap : C(DiskAttachment r, DiskAttachment s) :=
  desc r (boundaryFamilyInclusion J _)
    ((⟨old s (boundaryFamilyInclusion K _), old_continuous _ _⟩ : C(Rose B, _)).comp
      (diskRoseMap f))
    ⟨fun d => cell s (boundaryFamilyInclusion K _) ⟨c d.1, d.2⟩,
      continuous_sigma (fun j => (cell_continuous s _).comp
        (continuous_sigmaMk (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := c j)))⟩
    (fun z => by
      change old s (boundaryFamilyInclusion K (Fin 2 → ℝ)) (diskRoseMap f (r z)) =
        cell s (boundaryFamilyInclusion K (Fin 2 → ℝ)) ⟨c z.1, unitBoundaryInclusion _ z.2⟩
      rw [h z]
      exact (cell_boundary s _ (boundaryFamilyInclusion_isClosedEmbedding K _).injective
        ⟨c z.1, z.2⟩).symm)

@[simp] theorem sourceMap_old (x : Rose A) :
    sourceMap f c r s h (old r (boundaryFamilyInclusion J _) x) =
      old s (boundaryFamilyInclusion K _) (diskRoseMap f x) := rfl

@[simp] theorem sourceMap_cell (d : DiskFamily J (Fin 2 → ℝ)) :
    sourceMap f c r s h (cell r (boundaryFamilyInclusion J _) d) =
      cell s (boundaryFamilyInclusion K _) ⟨c d.1, d.2⟩ := desc_cell ..

def oneAttaching : C(BoundaryFamily (NewGenerators f) (Fin 1 → ℝ), DiskAttachment r) :=
  ContinuousMap.const _ (old r (boundaryFamilyInclusion J _) (roseVertex A))

def roseDiskIntoOne : C(DiskFamily B (Fin 1 → ℝ), DiskAttachment (oneAttaching f r)) where
  toFun d := if hb : d.1 ∈ Set.range f then
    old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _)
        (cell (roseAttaching A) (boundaryFamilyInclusion A _) ⟨Classical.choose hb, d.2⟩))
    else cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) ⟨⟨d.1, hb⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro b
    by_cases hb : b ∈ Set.range f
    · simp only [dif_pos hb]
      exact (old_continuous _ _).comp ((old_continuous _ _).comp
        ((cell_continuous _ _).comp
          (continuous_sigmaMk (σ := fun _ : A => ClosedUnitBall (Fin 1 → ℝ))
            (i := Classical.choose hb))))
    · simp only [dif_neg hb]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : NewGenerators f => ClosedUnitBall (Fin 1 → ℝ))
          (i := ⟨b, hb⟩))

def roseIntoOne : C(Rose B, DiskAttachment (oneAttaching f r)) :=
  desc (roseAttaching B) (boundaryFamilyInclusion B _)
    (ContinuousMap.const _ (old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _) (roseVertex A))))
    (roseDiskIntoOne f r) (by
      rintro ⟨b, x⟩
      change _ = if hb : b ∈ Set.range f then _ else _
      split_ifs with hb
      · exact congrArg (fun y => old (oneAttaching f r) _ (old r _ y))
          (cell_boundary (roseAttaching A) _
            (boundaryFamilyInclusion_isClosedEmbedding A _).injective
            ⟨Classical.choose hb, x⟩).symm
      · exact (cell_boundary (oneAttaching f r) _
          (boundaryFamilyInclusion_isClosedEmbedding (NewGenerators f) _).injective
          ⟨⟨b, hb⟩, x⟩).symm)

@[simp] theorem roseIntoOne_vertex : roseIntoOne f r (roseVertex B) =
    old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _) (roseVertex A)) := rfl

theorem roseIntoOne_cell_image (a : A) (d : ClosedUnitBall (Fin 1 → ℝ)) :
    roseIntoOne f r (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f a, d⟩) =
      old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
        (old r (boundaryFamilyInclusion J _)
          (cell (roseAttaching A) (boundaryFamilyInclusion A _) ⟨a, d⟩)) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  have hb : f a ∈ Set.range f := ⟨a, rfl⟩
  have ha  := f.injective (Classical.choose_spec hb)
  simp only [roseDiskIntoOne, ContinuousMap.coe_mk, dif_pos hb, ha]

theorem roseIntoOne_cell_new (b : NewGenerators f) (d : ClosedUnitBall (Fin 1 → ℝ)) :
    roseIntoOne f r (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨b.val, d⟩) =
      cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) ⟨b, d⟩ := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [roseDiskIntoOne, ContinuousMap.coe_mk, dif_neg b.property]

theorem roseIntoOne_map (x : Rose A) : roseIntoOne f r (diskRoseMap f x) =
    old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
      (old r (boundaryFamilyInclusion J _) x) := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (roseAttaching A) (boundaryFamilyInclusion A _) x
  cases z with
  | inl a => rfl
  | inr d =>
      change roseIntoOne f r (diskRoseMap f (cell _ _ d)) = _
      rw [diskRoseMap_cell, roseIntoOne_cell_image]
      rfl

def twoAttaching : C(BoundaryFamily (NewRelators c) (Fin 2 → ℝ),
    DiskAttachment (oneAttaching f r)) :=
  (roseIntoOne f r).comp ⟨fun z => s ⟨z.1.val, z.2⟩,
    continuous_sigma (fun k => s.continuous.comp
      (continuous_sigmaMk (σ := fun _ : K => UnitBoundary (Fin 2 → ℝ)) (i := k.val)))⟩

def oneToTarget : C(DiskAttachment (oneAttaching f r), DiskAttachment s) :=
  desc (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _)
    (sourceMap f c r s h)
    ⟨fun d => old s (boundaryFamilyInclusion K _)
      (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨d.1.val, d.2⟩),
      continuous_sigma (fun b => (old_continuous s _).comp
        ((cell_continuous _ _).comp
          (continuous_sigmaMk (σ := fun _ : B => ClosedUnitBall (Fin 1 → ℝ)) (i := b.val))))⟩
    (fun z => by
      change old s _ (diskRoseMap f (roseVertex A)) = old s _ (cell _ _ _)
      rw [diskRoseMap_vertex]
      exact congrArg (old s _) (cell_boundary (roseAttaching B) _
        (boundaryFamilyInclusion_isClosedEmbedding B _).injective ⟨z.1.val, z.2⟩).symm)

@[simp] theorem oneToTarget_old (x : DiskAttachment r) :
    oneToTarget f c r s h (old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) x) =
      sourceMap f c r s h x := rfl

@[simp] theorem oneToTarget_cell (d : DiskFamily (NewGenerators f) (Fin 1 → ℝ)) :
    oneToTarget f c r s h (cell (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _) d) =
      old s (boundaryFamilyInclusion K _)
        (cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨d.1.val, d.2⟩) := desc_cell ..

theorem oneToTarget_rose (x : Rose B) :
    oneToTarget f c r s h (roseIntoOne f r x) = old s (boundaryFamilyInclusion K _) x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (roseAttaching B) (boundaryFamilyInclusion B _) x
  cases z with
  | inl a => rfl
  | inr d =>
      rcases d with ⟨b, d⟩
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hb
        change oneToTarget f c r s h (roseIntoOne f r (cell _ _ ⟨f a, d⟩)) = _
        rw [roseIntoOne_cell_image, oneToTarget_old, sourceMap_old, diskRoseMap_cell]
        rfl
      · change oneToTarget f c r s h (roseIntoOne f r (cell _ _ ⟨b, d⟩)) = _
        rw [roseIntoOne_cell_new f r ⟨b, hb⟩ d, oneToTarget_cell]
        rfl

def extensionToTarget : C(DiskAttachment (twoAttaching f c r s), DiskAttachment s) :=
  desc (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _)
    (oneToTarget f c r s h)
    ⟨fun d => cell s (boundaryFamilyInclusion K _) ⟨d.1.val, d.2⟩,
      continuous_sigma (fun k => (cell_continuous s _).comp
        (continuous_sigmaMk (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := k.val)))⟩
    (fun z => (oneToTarget_rose f c r s h (s ⟨z.1.val, z.2⟩)).trans
      (cell_boundary s _ (boundaryFamilyInclusion_isClosedEmbedding K _).injective
        ⟨z.1.val, z.2⟩).symm)

@[simp] theorem extensionToTarget_old (x : DiskAttachment (oneAttaching f r)) :
    extensionToTarget f c r s h (old (twoAttaching f c r s)
      (boundaryFamilyInclusion (NewRelators c) _) x) = oneToTarget f c r s h x := rfl

@[simp] theorem extensionToTarget_cell (d : DiskFamily (NewRelators c) (Fin 2 → ℝ)) :
    extensionToTarget f c r s h (cell (twoAttaching f c r s)
      (boundaryFamilyInclusion (NewRelators c) _) d) =
      cell s (boundaryFamilyInclusion K _) ⟨d.1.val, d.2⟩ := desc_cell ..

end FiniteChains.RelativeAttachment.DiskPresentationExtension

namespace FiniteChains.RelativeAttachment.DiskPresentationExtension
open ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} (f : A ↪ B) (c : J ↪ K)
    (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
    (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
    (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

def sourceIntoExtension : C(DiskAttachment r, DiskAttachment (twoAttaching f c r s)) :=
  (⟨old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _),
    old_continuous _ _⟩ : C(DiskAttachment (oneAttaching f r), _)).comp
      ⟨old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _), old_continuous _ _⟩

def relatorDiskIntoExtension :
    C(DiskFamily K (Fin 2 → ℝ), DiskAttachment (twoAttaching f c r s)) where
  toFun d := if hk : d.1 ∈ Set.range c then
    sourceIntoExtension f c r s (cell r (boundaryFamilyInclusion J _) ⟨Classical.choose hk, d.2⟩)
    else cell (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _) ⟨⟨d.1, hk⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro k
    by_cases hk : k ∈ Set.range c
    · simp only [dif_pos hk]
      exact (sourceIntoExtension f c r s).continuous.comp
        ((cell_continuous r _).comp
          (continuous_sigmaMk (σ := fun _ : J => ClosedUnitBall (Fin 2 → ℝ))
            (i := Classical.choose hk)))
    · simp only [dif_neg hk]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : NewRelators c => ClosedUnitBall (Fin 2 → ℝ))
          (i := ⟨k, hk⟩))

def targetToExtension : C(DiskAttachment s, DiskAttachment (twoAttaching f c r s)) :=
  desc s (boundaryFamilyInclusion K _)
    ((⟨old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _),
      old_continuous _ _⟩ : C(DiskAttachment (oneAttaching f r), _)).comp (roseIntoOne f r))
    (relatorDiskIntoExtension f c r s) (by
      rintro ⟨k, a⟩
      change old (twoAttaching f c r s) _ (roseIntoOne f r (s ⟨k, a⟩)) =
        if hk : k ∈ Set.range c then _ else _
      split_ifs with hk
      · have hj : c (Classical.choose hk) = k := Classical.choose_spec hk
        have hs : s ⟨k, a⟩ = diskRoseMap f (r ⟨Classical.choose hk, a⟩) := by
          rw [h ⟨Classical.choose hk, a⟩, hj]
        rw [hs, roseIntoOne_map]
        exact congrArg (sourceIntoExtension f c r s)
          (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
            ⟨Classical.choose hk, a⟩).symm
      · exact (cell_boundary (twoAttaching f c r s) _
          (boundaryFamilyInclusion_isClosedEmbedding (NewRelators c) _).injective
          ⟨⟨k, hk⟩, a⟩).symm)

@[simp] theorem targetToExtension_old (x : Rose B) :
    targetToExtension f c r s h (old s (boundaryFamilyInclusion K _) x) =
      old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _)
        (roseIntoOne f r x) := rfl

theorem targetToExtension_cell_image (j : J) (d : ClosedUnitBall (Fin 2 → ℝ)) :
    targetToExtension f c r s h (cell s (boundaryFamilyInclusion K _) ⟨c j, d⟩) =
      sourceIntoExtension f c r s (cell r (boundaryFamilyInclusion J _) ⟨j, d⟩) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  have hk : c j ∈ Set.range c := ⟨j, rfl⟩
  have hj : Classical.choose hk = j := c.injective (Classical.choose_spec hk)
  simp only [relatorDiskIntoExtension, ContinuousMap.coe_mk, dif_pos hk, hj]

theorem targetToExtension_cell_new (k : NewRelators c) (d : ClosedUnitBall (Fin 2 → ℝ)) :
    targetToExtension f c r s h (cell s (boundaryFamilyInclusion K _) ⟨k.val, d⟩) =
      cell (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _) ⟨k, d⟩ := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [relatorDiskIntoExtension, ContinuousMap.coe_mk, dif_neg k.property]


theorem extensionToTarget_source (x : DiskAttachment r) :
    extensionToTarget f c r s h (sourceIntoExtension f c r s x) = sourceMap f c r s h x := rfl

theorem extensionToTarget_inverse (x : DiskAttachment s) :
    extensionToTarget f c r s h (targetToExtension f c r s h x) = x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective s (boundaryFamilyInclusion K _) x
  cases z with
  | inl x =>
      change extensionToTarget f c r s h (targetToExtension f c r s h (old s _ x)) = _
      rw [targetToExtension_old, extensionToTarget_old, oneToTarget_rose]
      rfl
  | inr d =>
      rcases d with ⟨k, d⟩
      by_cases hk : k ∈ Set.range c
      · obtain ⟨j, rfl⟩ := hk
        change extensionToTarget f c r s h (targetToExtension f c r s h (cell s _ ⟨c j, d⟩)) = _
        rw [targetToExtension_cell_image, extensionToTarget_source, sourceMap_cell]
        rfl
      · change extensionToTarget f c r s h (targetToExtension f c r s h (cell s _ ⟨k, d⟩)) = _
        rw [targetToExtension_cell_new f c r s h ⟨k, hk⟩ d, extensionToTarget_cell]
        rfl

theorem targetToExtension_inverse (x : DiskAttachment (twoAttaching f c r s)) :
    targetToExtension f c r s h (extensionToTarget f c r s h x) = x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (twoAttaching f c r s)
    (boundaryFamilyInclusion (NewRelators c) _) x
  cases z with
  | inl x =>
      obtain ⟨z, rfl⟩ := quotientMap_surjective (oneAttaching f r)
        (boundaryFamilyInclusion (NewGenerators f) _) x
      cases z with
      | inl x =>
          change targetToExtension f c r s h
            (extensionToTarget f c r s h (sourceIntoExtension f c r s x)) = _
          rw [extensionToTarget_source, (show targetToExtension f c r s h (sourceMap f c r s h x) = sourceIntoExtension f c r s x by
            obtain ⟨z, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J _) x
            cases z with
            | inl x =>
                change targetToExtension f c r s h (sourceMap f c r s h (old r _ x)) = _
                rw [sourceMap_old, targetToExtension_old, roseIntoOne_map]
                rfl
            | inr d =>
                change targetToExtension f c r s h (sourceMap f c r s h (cell r _ d)) = _
                rw [sourceMap_cell, targetToExtension_cell_image]
                rfl)]
          rfl
      | inr d =>
          change targetToExtension f c r s h (extensionToTarget f c r s h
            (old (twoAttaching f c r s) _ (cell (oneAttaching f r) _ d))) = _
          rw [extensionToTarget_old, oneToTarget_cell, targetToExtension_old,
            roseIntoOne_cell_new]
          rfl
  | inr d =>
      change targetToExtension f c r s h
        (extensionToTarget f c r s h (cell (twoAttaching f c r s) _ d)) = _
      rw [extensionToTarget_cell, targetToExtension_cell_new]
      rfl

def extensionHomeomorph : DiskAttachment (twoAttaching f c r s) ≃ₜ DiskAttachment s where
  toFun := extensionToTarget f c r s h
  invFun := targetToExtension f c r s h
  left_inv := targetToExtension_inverse f c r s h
  right_inv := extensionToTarget_inverse f c r s h
  continuous_toFun := (extensionToTarget f c r s h).continuous
  continuous_invFun := (targetToExtension f c r s h).continuous

@[simp] theorem extensionHomeomorph_old (x : DiskAttachment r) :
    extensionHomeomorph f c r s h (sourceIntoExtension f c r s x) = sourceMap f c r s h x := rfl

def extensionModel : Whitehead.DiskExtensionModel (DiskAttachment r) (DiskAttachment s) where
  oneCells := NewGenerators f
  twoCells := NewRelators c
  oneAttaching := oneAttaching f r
  twoAttaching := twoAttaching f c r s
  comparison := (extensionHomeomorph f c r s h).toHomotopyEquiv


end FiniteChains.RelativeAttachment.DiskPresentationExtension

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.RelativeAttachment

variable {E V J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace V]

def vertexStar (r : BoundaryFamily J E → V) (v : V) : Set (DiskAttachment r) :=
  oldCollar r 0 le_rfl {v}

omit [TopologicalSpace V] in
theorem vertexStar_subset_core (r : BoundaryFamily J E → V) (v : V) :
    vertexStar r v ⊆ puncturedAttachment r := by
  rintro (x | d) hx
  · trivial
  · exact ⟨hx.choose, trivial⟩

def vertexStarPoint (r : BoundaryFamily J E → V) (v : V) : vertexStar r v :=
  ⟨old r (boundaryFamilyInclusion J E) v, rfl⟩

theorem vertexStar_isOpen [DiscreteTopology V] (r : BoundaryFamily J E → V)
    (hr : Continuous r) (v : V) : IsOpen (vertexStar r v) :=
  oldCollar_isOpen r hr 0 le_rfl zero_lt_one {v} (isOpen_discrete _)

/-- Restricting the actual radial homotopy gives an actual contraction,
rather than just a claim about the induced fundamental group. -/


theorem vertexStar_simplyConnected (r : BoundaryFamily J E → V) (hr : Continuous r) (v : V) :
    IsSimplyConnected (vertexStar r v) := by
  letI := ((contractible_iff_id_nullhomotopic _).mpr
    ⟨vertexStarPoint r v, ⟨(by
      let j : C(vertexStar r v, puncturedAttachment r) :=
        ⟨fun z => ⟨z.val, vertexStar_subset_core r v z.property⟩,
          continuous_subtype_val.subtype_mk _⟩
      let H := radialCoreHomotopy r hr
      refine {
        toFun := fun tx => ⟨H (tx.1, j tx.2),
          radialCoreHomotopy_mem_oldCollar r hr tx.1 (j tx.2) {v} tx.2.property⟩
        continuous_toFun :=
          (H.continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))).subtype_mk _
        map_zero_left := ?_
        map_one_left := ?_ }
      · intro z
        exact Subtype.ext (H.map_zero_left (j z))
      · intro z
        ext
        change H (1, j z) = old r (boundaryFamilyInclusion J E) v
        refine (H.map_one_left (j z)).trans ?_
        have hz : radialCoreBack r (j z) ∈ ({v}) :=
          (radialCoreBack_mem_iff r (j z) {v}).mpr z.property
        exact congrArg (old r (boundaryFamilyInclusion J E)) hz)⟩⟩)
  change SimplyConnectedSpace (vertexStar r v)
  infer_instance

end FiniteChains.RelativeAttachment
end

section
open scoped Classical unitInterval
open Set Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords PathReplacement

abbrev GraphBall := ClosedUnitBall (Fin 1 → ℝ)

def graphBallSegment (x y : GraphBall) : Path x y where
  toFun t := ⟨Path.segment x.val y.val t, by
    have h := (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property)
      (show Path.segment x.val y.val t ∈ segment ℝ x.val y.val by
        rw [← Path.range_segment]; exact ⟨t, rfl⟩)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h⟩
  continuous_toFun := (Path.segment x.val y.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment x.val y.val).source
  target' := Subtype.ext (Path.segment x.val y.val).target

theorem graphBall_simplyConnected : SimplyConnectedSpace GraphBall := by
  letI := Metric.contractibleSpace_closedBall (E := Fin 1 → ℝ) (x := 0) zero_le_one
  let e : Metric.closedBall (0 : Fin 1 → ℝ) 1 ≃ₜ GraphBall := Homeomorph.setCongr (by
    ext x
    change dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1
    rw [dist_zero_right])
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

def graphSnapBoundary (x : GraphBall) : UnitBoundary (Fin 1 → ℝ) :=
  if h : 0 < ‖x.val‖ then annulusBoundary 0 le_rfl ⟨x, h⟩ else graphBoundaryNeg

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphCellMap (j : J) : C(GraphBall, DiskAttachment r) :=
  ⟨fun x => cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ⟨j, x⟩,
    (cell_continuous r _).comp continuous_sigmaMk⟩

theorem graphCellMap_interior (j : J) (x : OpenNormBall (Fin 1 → ℝ)) :
    graphCellMap r j ⟨x.val, x.property.le⟩ = openDiskMap r j x := by
  exact cell_of_not_mem r _ ⟨j, ⟨x.val, x.property.le⟩⟩
    (fun h => (ne_of_lt x.property)
      ((boundaryFamilyInclusion_range J (Fin 1 → ℝ) _).mp h))

def graphOpenPath (j : J) (x y : OpenNormBall (Fin 1 → ℝ))
    (P : Path (⟨x.val, x.property.le⟩ : GraphBall) ⟨y.val, y.property.le⟩) :
    Path (openDiskMap r j x) (openDiskMap r j y) :=
  (P.map (graphCellMap r j).continuous).cast (graphCellMap_interior r j x).symm
    (graphCellMap_interior r j y).symm

def graphSnap : DiskAttachment r → V
  | Sum.inl v => v
  | Sum.inr d => r ⟨d.val.1, graphSnapBoundary d.val.2⟩

def graphConnector (z : DiskAttachment r) :
    Path z (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphSnap r z)) :=
  match z with
  | Sum.inl _ => Path.refl _
  | Sum.inr d =>
      ((graphBallSegment d.val.2 (unitBoundaryInclusion _ (graphSnapBoundary d.val.2))).map
        (graphCellMap r d.val.1).continuous).cast
          (cell_of_not_mem r _ d.val d.property).symm
          (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
            ⟨d.val.1, graphSnapBoundary d.val.2⟩).symm

omit [TopologicalSpace V] in
theorem graphSnap_of_mem_vertexStar {v : V} {z : DiskAttachment r}
    (hz : z ∈ vertexStar r v) : graphSnap r z = v := by
  cases z with
  | inl w => exact hz
  | inr d =>
    obtain ⟨hx, hv⟩ := hz
    simpa only [graphSnap, graphSnapBoundary, dif_pos hx] using (Set.mem_singleton_iff.mp hv)

theorem graphConnector_eq_radial (hr : Continuous r)
    (z : puncturedAttachment r) :
    ∀ t : I, graphConnector r z.val t = radialCoreHomotopy r hr (t, z) := by
  rcases z with ⟨v | d, hz⟩
  · intro t
    rfl
  · obtain ⟨hx, _⟩ := hz
    intro t
    apply congrArg (cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
    apply congrArg (Sigma.mk d.val.1)
    apply Subtype.ext
    change Path.segment d.val.2.val (graphSnapBoundary d.val.2).val t =
      ((1 - t) + t / ‖d.val.2.val‖) • d.val.2.val
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    rw [graphSnapBoundary, dif_pos hx]
    change (1 - (t : ℝ)) • d.val.2.val +
      (t : ℝ) • (‖d.val.2.val‖⁻¹ • d.val.2.val) = _
    rw [smul_smul, add_smul, div_eq_mul_inv]

theorem graphConnector_range_vertexStar (hr : Continuous r) {v : V}
    {z : DiskAttachment r} (hz : z ∈ vertexStar r v) :
    Set.range (graphConnector r z) ⊆ vertexStar r v := by
  rintro _ ⟨t, rfl⟩
  rw [graphConnector_eq_radial r hr ⟨z, vertexStar_subset_core r v hz⟩ t]
  exact radialCoreHomotopy_mem_oldCollar r hr t _ {v} hz

def graphBoundaryPath (j : J) (a b : UnitBoundary (Fin 1 → ℝ))
    (p : Path (unitBoundaryInclusion _ a) (unitBoundaryInclusion _ b)) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, a⟩))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, b⟩)) :=
  (p.map (graphCellMap r j).continuous).cast
    (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, a⟩).symm
    (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, b⟩).symm

def graphClosedEdgePath :
    Path (unitBoundaryInclusion _ graphBoundaryNeg) (unitBoundaryInclusion _ graphBoundaryPos) where
  toFun := graphDiskHomeomorph
  continuous_toFun := graphDiskHomeomorph.continuous
  source' := graphDiskHomeomorph_zero
  target' := graphDiskHomeomorph_one

theorem graphBoundaryPath_refl (j : J) (a : UnitBoundary (Fin 1 → ℝ)) :
    graphBoundaryPath r j a a (Path.refl _) =
      Path.refl (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, a⟩)) := by
  apply Path.ext
  funext t
  exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, a⟩

theorem graphBoundaryPath_isWord (j : J) (a b : UnitBoundary (Fin 1 → ℝ))
    (p : Path (unitBoundaryInclusion _ a) (unitBoundaryInclusion _ b)) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) (graphBoundaryPath r j a b p) := by
  letI := graphBall_simplyConnected
  rcases graphBoundary_cases a with rfl | rfl <;>
    rcases graphBoundary_cases b with rfl | rfl
  · refine ⟨[], rfl, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p (Path.refl _)).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryNeg graphBoundaryNeg p)
        (graphBoundaryPath r j graphBoundaryNeg graphBoundaryNeg (Path.refl _)) := h.pathCast _ _
    rw [graphBoundaryPath_refl] at h'
    exact h'
  · refine ⟨[(j, true)], ⟨rfl, rfl⟩, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p graphClosedEdgePath).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryNeg graphBoundaryPos p)
        (graphEdgePath r j) := h.pathCast _ _
    exact h'.trans (Path.Homotopic.trans_refl (graphEdgePath r j)).symm
  · refine ⟨[(j, false)], ⟨rfl, rfl⟩, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p graphClosedEdgePath.symm).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryPos graphBoundaryNeg p)
        (graphEdgePath r j).symm := h.pathCast _ _
    exact h'.trans (Path.Homotopic.trans_refl (graphEdgePath r j).symm).symm
  · refine ⟨[], rfl, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p (Path.refl _)).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryPos graphBoundaryPos p)
        (graphBoundaryPath r j graphBoundaryPos graphBoundaryPos (Path.refl _)) := h.pathCast _ _
    rw [graphBoundaryPath_refl] at h'
    exact h'




/-- Every path between actual vertices is represented by a finite list of
the actual original oriented edges. -/
theorem graph_path_isWord [DiscreteTopology V] (hr : Continuous r) (v w : V)
    (p : Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) v)
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) w)) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) p := by
  let U  := Sum.elim (vertexStar r) (openDisk r)
  have hU : ∀ i, IsOpen (U i) := by
    rintro (v | j)
    · exact vertexStar_isOpen r hr v
    · exact openDisk_isOpen r j
  have hcover : Set.univ ⊆ ⋃ i, U i := by
    rintro (v | d) _
    · exact Set.mem_iUnion.mpr ⟨Sum.inl v, rfl⟩
    · have hd  := lt_of_le_of_ne d.val.2.property
        (fun h => d.property ((boundaryFamilyInclusion_range J _ _).mpr h))
      exact Set.mem_iUnion.mpr ⟨Sum.inr d.val.1, ⟨⟨d.val.2.val, hd⟩, rfl⟩⟩
  have hlocal : ∀ i {x y : DiskAttachment r} (p : Path x y), Set.range p ⊆ U i →
      IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
        (graphEdgePath r) (((graphConnector r x).symm.trans p).trans (graphConnector r y)) := by
    rintro (v | j) x y p hp
    · exact (by
      have hx := hp p.source_mem_range
      have hy := hp p.target_mem_range
      have hxy := (graphSnap_of_mem_vertexStar r hx).trans (graphSnap_of_mem_vertexStar r hy).symm
      refine ⟨[], hxy, ?_⟩
      apply homotopic_of_within_simplyConnected (vertexStar r v) (vertexStar_simplyConnected r hr v)
      · exact range_trans_subset _ _
          (range_trans_subset _ _ (range_symm_subset _ (graphConnector_range_vertexStar r hr hx)) hp)
          (graphConnector_range_vertexStar r hr hy)
      · rintro _ ⟨t, rfl⟩
        exact graphSnap_of_mem_vertexStar r hx)
    · exact (by
      obtain ⟨x, rfl⟩ := hp p.source_mem_range
      obtain ⟨y, rfl⟩ := hp p.target_mem_range
      obtain ⟨P, rfl⟩ := (show ∃ P : Path (⟨x.val, x.property.le⟩ : GraphBall) ⟨y.val, y.property.le⟩,
      graphOpenPath r j x y P = p by
        let e := (openDiskMap_isOpenEmbedding r j).isEmbedding.toHomeomorph
        let Q : Path (e x) (e y) := {
          toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
          continuous_toFun := p.continuous.subtype_mk _
          source' := Subtype.ext p.source
          target' := Subtype.ext p.target }
        let incl : C(OpenNormBall (Fin 1 → ℝ), GraphBall) :=
          ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
        let P := ((Q.map e.symm.continuous).cast (e.symm_apply_apply x).symm
          (e.symm_apply_apply y).symm).map incl.continuous
        refine ⟨P, ?_⟩
        apply Path.ext
        funext t
        change graphCellMap r j ⟨(e.symm (Q t)).val, (e.symm (Q t)).property.le⟩ = p t
        rw [graphCellMap_interior]
        exact congrArg Subtype.val (e.apply_symm_apply (Q t)))
      let a : GraphBall := ⟨x.val, x.property.le⟩
      let b : GraphBall := ⟨y.val, y.property.le⟩
      let A := graphSnapBoundary a
      let B := graphSnapBoundary b
      let Q := ((graphBallSegment a (unitBoundaryInclusion _ A)).symm.trans P).trans
        (graphBallSegment b (unitBoundaryInclusion _ B))
      have h := graphBoundaryPath_isWord r j A B Q
      have he : graphBoundaryPath r j A B Q =
          (((graphConnector r (openDiskMap r j x)).symm.trans (graphOpenPath r j x y P)).trans
            (graphConnector r (openDiskMap r j y))) := by
        apply Path.ext
        funext t
        simp only [graphBoundaryPath, Q, graphOpenPath, Path.cast_coe,
          Path.map_coe, Function.comp_apply, Path.trans_apply, Path.symm_apply]
        split_ifs <;> rfl
      rwa [he] at h)
  have h := isWord_of_open_cover (graphSrc r) (graphTgt r)
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) (graphEdgePath r)
    U hU hcover (graphSnap r) (graphConnector r) hlocal p
  apply h.of_homotopic
  exact ((Path.Homotopic.refl_trans p).hcomp (Path.Homotopic.refl _)
    |>.trans (Path.Homotopic.trans_refl p)).symm

theorem graphCx_isConnected [DiscreteTopology V] (hr : Continuous r)
    [PathConnectedSpace (DiskAttachment r)] : Comb.IsConnected (graphCx r) := by
  intro v w
  obtain ⟨p⟩ := PathConnectedSpace.joined
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) v)
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) w)
  obtain ⟨l, hl, _⟩ := graph_path_isWord r hr v w p
  exact ⟨l, hl⟩

end FiniteChains.ClassicalGraphModel
end

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

/-- Finite words on the four sides, with their exact corner incidences. -/
structure BoundaryWords where
  vertex : SquareBoundary → V
  word : SquareSide → List (J × Bool)
  isPath : ∀ s, Comb.IsPath (graphSrc r) (graphTgt r) (word s)
    (vertex (squareSideMap s 0)) (vertex (squareSideMap s 1))

namespace BoundaryWords

variable {r} (W : BoundaryWords r)

def sidePath (s : SquareSide) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (W.vertex (squareSideMap s 0)))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (W.vertex (squareSideMap s 1))) :=
  realize (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
    (graphEdgePath r) (W.word s) (W.isPath s)

theorem sidePath_endpoint (s : SquareSide) (t : I) (ht : t = 0 ∨ t = 1) :
    W.sidePath s t = old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      (W.vertex (squareSideMap s t)) := by grind

def squareMap : C(SquareBoundary, DiskAttachment r) :=
  squareBoundaryPasting (fun s => (W.sidePath s).toContinuousMap)
    (fun z => old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (W.vertex z))
    W.sidePath_endpoint

@[simp] theorem squareMap_side (s : SquareSide) (t : I) :
    W.squareMap (squareSideMap s t) = W.sidePath s t :=
  squareBoundaryPasting_side _ _ _ s t

def boundaryMap : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r) :=
  W.squareMap.comp unitBoundarySquareHomeomorph.toContinuousMap

/-- The based combinatorial word obtained by travelling around the four
sides, reversing the two sides whose coordinate direction opposes travel. -/
def loopWord : List (J × Bool) :=
  List.append (α := J × Bool)
    (List.append (α := J × Bool)
      (List.append (W.word (0, false)) (W.word (1, true)))
      (Comb.revPath (X := graphCx r) (W.word (0, true))))
    (Comb.revPath (X := graphCx r) (W.word (1, false)))

theorem corner01 : squareSideMap (0, false) 1 = squareSideMap (1, true) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner11 : squareSideMap (1, true) 1 = squareSideMap (0, true) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner10 : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner00 : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

omit [TopologicalSpace V] in
theorem loopWord_isPath : Comb.IsPath (graphSrc r) (graphTgt r) W.loopWord
    (W.vertex (squareSideMap (0, false) 0)) (W.vertex (squareSideMap (0, false) 0)) := by
  have h₀ := W.isPath (0, false)
  have h₁ := W.isPath (1, true)
  have h₂ := Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have h₃ := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
  rw [← corner01] at h₁
  rw [← corner11] at h₂
  rw [← corner10, corner00] at h₃
  exact ((h₀.append h₁).append h₂).append h₃

end BoundaryWords

/-- The endpoint motions and edge-word homotopies descend through the
actual four-side quotient. No cellular approximation premise is assumed. -/
theorem squareMap_homotopic_boundaryWords [DiscreteTopology V] (hr : Continuous r)
    (f : C(SquareBoundary, DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.squareMap := by
  let v  := fun z => graphSnap r (f z)
  let p z := graphConnector r (f z)
  let E s := intervalEndpointExtension (f.comp (squareSideMap s))
    (p (squareSideMap s 0)) (p (squareSideMap s 1))
  have hE : ∀ s τ t, t = 0 ∨ t = 1 →
      (E s).map (τ, t) = p (squareSideMap s t) τ := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · exact (E s).side_zero τ
    · exact (E s).side_one τ
  let G := squareBoundaryHomotopyPasting (fun s => (E s).map) (fun τ z => p z τ) hE
  let f₁ :=
    G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let H₀ : f.Homotopy f₁ := {
    toContinuousMap := G
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G (0, squareSideMap s t) = f (squareSideMap s t)
      rw [squareBoundaryHomotopyPasting_side]
      exact (E s).zero t
    map_one_left := fun _ => rfl }
  let l s :
      Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (v (squareSideMap s 0)))
        (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (v (squareSideMap s 1))) := {
    toFun := fun t => (E s).map (1, t)
    continuous_toFun := (E s).map.continuous.comp (continuous_const.prodMk continuous_id)
    source' := ((E s).side_zero 1).trans (p (squareSideMap s 0)).target
    target' := ((E s).side_one 1).trans (p (squareSideMap s 1)).target }
  have hwords := fun s => graph_path_isWord r hr _ _ (l s)
  choose w hw Hwords using hwords
  let W : BoundaryWords r := ⟨v, w, hw⟩
  let H s := Classical.choice (Hwords s)
  have hHV : ∀ s τ t, t = 0 ∨ t = 1 →
      H s (τ, t) = old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
        (v (squareSideMap s t)) := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · simp
    · simp
  let G₁ := squareBoundaryHomotopyPasting (fun s => (H s).toHomotopy.toContinuousMap)
    (fun _ z => old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (v z)) hHV
  let H₁ : f₁.Homotopy W.squareMap := {
    toContinuousMap := G₁
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (0, squareSideMap s t) = G (1, squareSideMap s t)
      rw [squareBoundaryHomotopyPasting_side, squareBoundaryHomotopyPasting_side]
      exact (H s).apply_zero t
    map_one_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (1, squareSideMap s t) = W.squareMap (squareSideMap s t)
      rw [squareBoundaryHomotopyPasting_side, BoundaryWords.squareMap_side]
      exact (H s).apply_one t }
  exact ⟨W, ⟨H₀.trans H₁⟩⟩

theorem boundaryMap_homotopic_boundaryWords [DiscreteTopology V] (hr : Continuous r)
    (f : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.boundaryMap := by
  let e := unitBoundarySquareHomeomorph
  obtain ⟨W, hW⟩ := squareMap_homotopic_boundaryWords r hr (f.comp e.symm.toContinuousMap)
  refine ⟨W, ?_⟩
  have H := hW.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  have he : (f.comp e.symm.toContinuousMap).comp e.toContinuousMap = f := by
    apply ContinuousMap.ext
    intro a
    exact congrArg f (e.symm_apply_apply a)
  rwa [he] at H

end FiniteChains.ClassicalGraphModel
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
open scoped Classical unitInterval

namespace ContinuousEdgeWords
variable {G H : Comb.Complex2} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (h : Comb.Hom G H) (f : C(X, Y)) (v : G.V → X) (w : H.V → Y)
  (edge : ∀ e, Path (v (G.src e)) (v (G.tgt e)))
  (edge' : ∀ e, Path (w (H.src e)) (w (H.tgt e)))
  (hv : ∀ a, f (v a) = w (h.onV a))
  (he : ∀ e t, f (edge e t) = edge' (h.onE e) t)

include hv he in
theorem realize_map_apply (l : List (G.E × Bool)) {a b : G.V}
    (hl : Comb.IsPath G.src G.tgt l a b) (t : I) :
    f (realize G.src G.tgt v edge l hl t) =
      realize H.src H.tgt w edge' (Comb.mapPath h l) (Comb.isPath_mapPath h hl) t := by
  have same_start {a a' b : H.V} m (ha : a = a')
      (h₁ : Comb.IsPath H.src H.tgt m a b) (h₂ : Comb.IsPath H.src H.tgt m a' b) s :
      realize H.src H.tgt w edge' m h₁ s = realize H.src H.tgt w edge' m h₂ s := by
    subst a'
    rfl
  induction l generalizing a t with
  | nil => exact hv a
  | cons g l ih =>
    change f (((germPath G.src G.tgt v edge g).cast _ _).trans
      (realize G.src G.tgt v edge l hl.2) t) =
      (((germPath H.src H.tgt w edge' (h.onE g.1, g.2)).cast _ _).trans
        (realize H.src H.tgt w edge' (Comb.mapPath h l) _) t)
    simp only [Path.trans_apply, Path.cast_coe]
    split_ifs
    · cases g with
      | mk e o => cases o <;> exact he e _
    · apply (ih hl.2 _).trans
      exact same_start (Comb.mapPath h l) (Comb.germTgt_onE h g).symm
        (Comb.isPath_mapPath h hl.2) (Comb.isPath_mapPath h hl).2 _

end ContinuousEdgeWords

namespace ClassicalGraphModel.BoundaryWords
open RelativeAttachment
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  {r : BoundaryFamily J (Fin 1 → ℝ) → V}
  {s : BoundaryFamily K (Fin 1 → ℝ) → W}

def map (h : Comb.Hom (graphCx r) (graphCx s)) (b : BoundaryWords r) : BoundaryWords s where
  vertex := h.onV ∘ b.vertex
  word i := Comb.mapPath h (b.word i)
  isPath i := Comb.isPath_mapPath h (b.isPath i)

omit [TopologicalSpace V] [TopologicalSpace W] in
theorem map_comp {Z L : Type} [TopologicalSpace Z]
    {t : BoundaryFamily L (Fin 1 → ℝ) → Z}
    (h : Comb.Hom (graphCx r) (graphCx s))
    (k : Comb.Hom (graphCx s) (graphCx t)) (b : BoundaryWords r) :
    (b.map h).map k = b.map (k.comp h) := by
  cases b
  simp only [map, Comb.mapPath, List.map_map, Comb.Hom.comp]
  rfl

omit [TopologicalSpace V] [TopologicalSpace W] in
theorem loopWord_map (h : Comb.Hom (graphCx r) (graphCx s)) (b : BoundaryWords r) :
    (b.map h).loopWord = Comb.mapPath h b.loopWord := by
  simp only [loopWord, map, Comb.mapPath, Comb.revPath,
    List.append_eq, List.map_append, List.map_reverse, List.map_map]
  rfl

theorem boundaryMap_map (h : Comb.Hom (graphCx r) (graphCx s))
    (f : C(DiskAttachment r, DiskAttachment s))
    (hv : ∀ a, f (old r _ a) = old s _ (h.onV a))
    (he : ∀ e t, f (graphEdgePath r e t) = graphEdgePath s (h.onE e) t)
    (b : BoundaryWords r) :
    f.comp b.boundaryMap = (b.map h).boundaryMap := by
  ext x
  obtain ⟨⟨i, t⟩, hi⟩ := squareSideQuotient_surjective (unitBoundarySquareHomeomorph x)
  change f (b.squareMap (unitBoundarySquareHomeomorph x)) =
    (b.map h).squareMap (unitBoundarySquareHomeomorph x)
  change squareSideMap i t = unitBoundarySquareHomeomorph x at hi
  rw [← hi, squareMap_side, squareMap_side]
  exact ContinuousEdgeWords.realize_map_apply h f (old r _) (old s _)
    (graphEdgePath r) (graphEdgePath s) hv he (b.word i) (b.isPath i) t

end ClassicalGraphModel.BoundaryWords
end FiniteChains
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X Y Z X' Y' : Complex2.{u}}

theorem zeroPi2_comp_left (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 f) :
    ZeroPi2 (g.comp f) := by
  intro x c hc
  have he : Finsupp.mapDomain (univLift X (g.comp f) x).onF c =
      Finsupp.mapDomain (univLift Y g (f.onV x)).onF
        (Finsupp.mapDomain (univLift X f x).onF c) := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun F _ => (univLiftF_comp g f x F).symm
  have hz'  := hz x c hc
  simp_all

theorem hom_retraction_square (f : Hom X Y) (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) : r.comp (g.comp a) = f := by
  rw [← hsq]
  apply Hom.ext'
  · exact funext fun x => hV (f.onV x)
  · exact funext fun x => hE (f.onE x)
  · exact funext fun x => hF (f.onF x)

theorem zeroPi2_of_retraction_square (f : Hom X Y) (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) (hz : ZeroPi2 g) : ZeroPi2 f := by
  have H := zeroPi2_comp_left r (g.comp a) (zeroPi2_comp_right g a hz)
  rwa [hom_retraction_square f g a b r hV hE hF hsq] at H


theorem pi1Trivial_of_retraction_square (f : Hom X Y) (g : Hom X' Y')
    (a : Hom X X') (b : Hom Y Y') (r : Hom Y' Y)
    (hV : ∀ y, r.onV (b.onV y) = y)
    (hE : ∀ y, r.onE (b.onE y) = y)
    (hF : ∀ y, r.onF (b.onF y) = y)
    (hsq : b.comp f = g.comp a) (hz : Pi1Trivial g) : Pi1Trivial f := by
  have H := Pi1Trivial.comp_left r (show Pi1Trivial (g.comp a) by
    intro x p hp
    simpa only [mapPath_comp, Hom.comp, Function.comp_def] using hz (a.onV x) (mapPath a p) (isPath_mapPath a hp))
  rwa [hom_retraction_square f g a b r hV hE hF hsq] at H

end FiniteChains.Comb
end

section
open scoped Classical
namespace FiniteChains.Comb.PresGeneratorRelabel
universe u
variable {A B J : Type u} [DecidableEq A] [DecidableEq B]
  (e : A ≃ B) (ρ : J → FreeGroup A) (σ : J → FreeGroup B)
  (hrel : ∀ j, σ j = FreeGroup.map e (ρ j))

def forward : Hom (presComplex ρ) (presComplex σ) :=
  presInclHom e e.injective ρ σ id hrel

omit [DecidableEq A] [DecidableEq B] in
include hrel in
theorem inverse_rel (j : J) : ρ j = FreeGroup.map e.symm (σ j) := by
  rw [hrel j, FreeGroup.map.comp]
  simp

def backward : Hom (presComplex σ) (presComplex ρ) :=
  presInclHom e.symm e.symm.injective σ ρ id (inverse_rel e ρ σ hrel)

theorem backward_forward_V (x : (presComplex ρ).V) :
    (backward e ρ σ hrel).onV ((forward e ρ σ hrel).onV x) = x :=
  Subsingleton.elim _ _

theorem backward_forward_E (x : A) :
    (backward e ρ σ hrel).onE ((forward e ρ σ hrel).onE x) = x :=
  e.symm_apply_apply x

theorem backward_forward_F (x : J) :
    (backward e ρ σ hrel).onF ((forward e ρ σ hrel).onF x) = x := rfl

end FiniteChains.Comb.PresGeneratorRelabel

namespace FiniteChains.Comb
universe u v w

theorem finsupp_filter_of_constant_label {I : Type u} {J : Type v}
    (label : I → J) (j : J) (c : I →₀ ℤ) (k : J)
    (hc : ∀ i, c i ≠ 0 → label i = j) :
    c.filter (fun i => label i = k) = if j = k then c else 0 := by
  ext i
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    by_cases hi : c i = 0
    · simp [Finsupp.filter_apply, hi]
    · simp [hc i hi]
  · rw [if_neg hjk]
    by_cases hi : c i = 0
    · simp [Finsupp.filter_apply, hi]
    · simp [hc i hi, hjk]

theorem supported_label_boundary {I : Type u} {J : Type v} {T : Type w}
    (d : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ)) (labelI : I → T) (labelJ : J → T)
    (old : I → Prop)
    (hd : ∀ i, old i → ∀ j, d (Finsupp.single i 1) j ≠ 0 → labelJ j = labelI i)
    (c : I →₀ ℤ) (hc : ∀ i ∈ c.support, old i) (k : T) :
    d (c.filter (fun i => labelI i = k)) = (d c).filter (fun j => labelJ j = k) := by
  have hs i (hi : i ∈ c.support) :
      d ((Finsupp.single i (c i)).filter (fun i => labelI i = k)) =
        (d (Finsupp.single i (c i))).filter (fun j => labelJ j = k) := by
    have hm : ∀ j, d (Finsupp.single i (c i)) j ≠ 0 → labelJ j = labelI i := by
      intro j hj
      apply hd i (hc i hi) j
      intro hz
      apply hj
      have hsingle : Finsupp.single i (c i) = (c i) • Finsupp.single i 1 := by simp
      rw [hsingle, map_smul]
      simp [hz]
    rw [finsupp_filter_of_constant_label labelJ (labelI i) _ k hm]
    by_cases hik : labelI i = k
    · simp_all
    · simp_all
  calc
    d (c.filter (fun i => labelI i = k)) =
        d ((∑ i ∈ c.support, Finsupp.single i (c i)).filter (fun i => labelI i = k)) := by
          rw [show (∑ i ∈ c.support, Finsupp.single i (c i)) = c from c.sum_single]
    _ = ∑ i ∈ c.support,
        d ((Finsupp.single i (c i)).filter (fun i => labelI i = k)) := by
          rw [Finsupp.filter_sum, map_sum]
    _ = ∑ i ∈ c.support,
        (d (Finsupp.single i (c i))).filter (fun j => labelJ j = k) :=
          Finset.sum_congr rfl hs
    _ = (d c).filter (fun j => labelJ j = k) := by
          rw [← Finsupp.filter_sum, ← map_sum]
          rw [show (∑ i ∈ c.support, Finsupp.single i (c i)) = c from c.sum_single]

theorem finsupp_sum_label_filters {I : Type u} {J : Type v}
    (label : I → J) (c : I →₀ ℤ) :
    ∑ j ∈ c.support.image label, c.filter (fun i => label i = j) = c := by
  ext i
  by_cases hi : c i = 0
  · simp [Finsupp.filter_apply, hi]
  · have hm : label i ∈ c.support.image label :=
      Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩
    simp
    rw [Finset.sum_eq_single (label i)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · exact fun h => False.elim (h hm)

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}} (f : Hom X Y)

theorem augC_chain0 (z : X.V →₀ ℤ) : augC Y (chain0 f z) = augC X z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single v n => simp [chain0, augC_single]

theorem isAcyclic_iff_of_cell_bijections
    (hV : Function.Bijective f.onV) (hE : Function.Bijective f.onE)
    (hF : Function.Bijective f.onF) : IsAcyclic X ↔ IsAcyclic Y := by
  have iV : Function.Injective (chain0 f) := Finsupp.mapDomain_injective hV.1
  have iE : Function.Injective (chain1 f) := Finsupp.mapDomain_injective hE.1
  have iF : Function.Injective (chain2 f) := Finsupp.mapDomain_injective hF.1
  have sV : Function.Surjective (chain0 f) := Finsupp.mapDomain_surjective (M := ℤ) hV.2
  have sE : Function.Surjective (chain1 f) := Finsupp.mapDomain_surjective (M := ℤ) hE.2
  have sF : Function.Surjective (chain2 f) := Finsupp.mapDomain_surjective (M := ℤ) hF.2
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      obtain ⟨a', rfl⟩ := sF a
      obtain ⟨b', rfl⟩ := sF b
      rw [bdry2_chain2, bdry2_chain2] at hab
      exact congrArg (chain2 f) (h.h2 (iE hab))
    · intro a ha
      obtain ⟨a', rfl⟩ := sE a
      have hcycle : bdry1 X a' = 0 := by
        apply iV
        rw [map_zero, ← bdry1_chain1, ha]
      obtain ⟨b, hb⟩ := h.h1 a' hcycle
      exact ⟨chain2 f b, by rw [bdry2_chain2, hb]⟩
    · intro a ha
      obtain ⟨a', rfl⟩ := sV a
      rw [augC_chain0] at ha
      obtain ⟨b, hb⟩ := h.h0 a' ha
      exact ⟨chain1 f b, by rw [bdry1_chain1, hb]⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      apply iF
      apply h.h2
      rw [bdry2_chain2, bdry2_chain2, hab]
    · intro a ha
      have hcycle : bdry1 Y (chain1 f a) = 0 := by
        rw [bdry1_chain1, ha, map_zero]
      obtain ⟨b, hb⟩ := h.h1 (chain1 f a) hcycle
      obtain ⟨b', rfl⟩ := sF b
      exact ⟨b', iE (by rwa [← bdry2_chain2])⟩
    · intro a ha
      have hcycle : augC Y (chain0 f a) = 0 := by rw [augC_chain0, ha]
      obtain ⟨b, hb⟩ := h.h0 (chain0 f a) hcycle
      obtain ⟨b', rfl⟩ := sE b
      exact ⟨b', iV (by rwa [← bdry1_chain1])⟩

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

/-! ### Changing the base vertex of the universal cover -/

section Shift

variable {X : Complex2.{u}} {y₀ w₀ : X.V} {q : List (X.E × Bool)}

/-- Prepending a fixed path to a path issued from its endpoint. -/
def shiftP (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) : PathFrom X y₀ :=
  ⟨q ++ p.1, by
    have hend : endpt X y₀ (q ++ p.1) = endpt X w₀ p.1 := by
      rw [endpt_append, endpt_eq_of_isPath hq]
    rw [hend]
    exact isPath_append_iff.mpr ⟨w₀, hq, p.2⟩⟩

theorem endpt_shiftP (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) :
    endpt X y₀ (shiftP hq p).1 = endpt X w₀ p.1 := by grind [endpt_append, endpt_eq_of_isPath, shiftP]

/-- Changing the base vertex of the universal cover, on vertices. -/
def shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (c : UV X w₀) : UV X y₀ :=
  Quotient.map (shiftP hq) (by
    intro p p' hpp
    show Htpy X y₀ (endpt X y₀ (shiftP hq p).1) (shiftP hq p).1 (shiftP hq p').1
    rw [endpt_shiftP]
    exact Htpy.append_congr hq p.2 (Htpy.refl q) hpp) c

@[simp] theorem shiftV_mk (hq : IsPath X.src X.tgt q y₀ w₀) (p : PathFrom X w₀) :
    shiftV hq (UV.mk p) = UV.mk (shiftP hq p) := rfl

@[simp] theorem endV_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (c : UV X w₀) :
    endV (shiftV hq c) = endV c := by
  induction c using UV.ind with
  | h p => exact endpt_shiftP hq p

theorem shiftV_base (hq : IsPath X.src X.tgt q y₀ w₀) :
    shiftV hq (UV.base X w₀) = UV.mk ⟨q, by rw [endpt_eq_of_isPath hq]; exact hq⟩ := by
  refine congrArg UV.mk (Subtype.ext ?_)
  exact List.append_nil q

theorem extend_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) (eb : X.E × Bool) (c : UV X w₀) :
    extend eb (shiftV hq c) = shiftV hq (extend eb c) := by
  induction c using UV.ind with
  | h p =>
      have hl : (extendP eb (shiftP hq p)).1 = (shiftP hq (extendP eb p)).1 := by
        by_cases h : endpt X w₀ p.1 = germSrc X.src X.tgt eb
        · have h' : endpt X y₀ (shiftP hq p).1 = germSrc X.src X.tgt eb := by
            rw [endpt_shiftP]; exact h
          rw [extendP_pos h']
          show (q ++ p.1) ++ [eb] = q ++ (extendP eb p).1
          rw [extendP_pos h]
          simp
        · have h' : ¬ endpt X y₀ (shiftP hq p).1 = germSrc X.src X.tgt eb := by
            rw [endpt_shiftP]; exact h
          rw [extendP_neg h']
          show (shiftP hq p).1 = q ++ (extendP eb p).1
          rw [extendP_neg h]
          rfl
      refine Quotient.sound ?_
      show Htpy X y₀ (endpt X y₀ (extendP eb (shiftP hq p)).1) (extendP eb (shiftP hq p)).1
        (shiftP hq (extendP eb p)).1
      rw [hl]
      exact Htpy.refl _

/-- Changing the base vertex of the universal cover, on edges. -/
def shiftE (hq : IsPath X.src X.tgt q y₀ w₀) (E : UE X w₀) : UE X y₀ :=
  ⟨(shiftV hq E.1.1, E.1.2), by rw [endV_shiftV]; exact E.2⟩

/-- Changing the base vertex of the universal cover, on two-cells. -/
def shiftF (hq : IsPath X.src X.tgt q y₀ w₀) (F : UF X w₀) : UF X y₀ :=
  ⟨(shiftV hq F.1.1, F.1.2), by rw [endV_shiftV]; exact F.2⟩


theorem uLiftPath_shiftV (hq : IsPath X.src X.tgt q y₀ w₀) :
    ∀ (l : List (X.E × Bool)) (c : UV X w₀) (v : X.V), IsPath X.src X.tgt l (endV c) v →
      uLiftPath l (shiftV hq c) = (uLiftPath l c).map (fun Eb => (shiftE hq Eb.1, Eb.2)) := by
  intro l
  induction l with
  | nil => simp
  | cons eb t ih =>
      intro c v hl
      have h  := hl.1
      have h' : endV (shiftV hq c) = germSrc X.src X.tgt eb := by rw [endV_shiftV]; exact h
      rw [uLiftPath_cons h', uLiftPath_cons h, List.map_cons, (show liftGerm (shiftV hq c) eb h' = (shiftE hq (liftGerm c eb h).1, (liftGerm c eb h).2) by
        obtain ⟨e, b⟩ := eb
        cases b with
        | true => rfl
        | false =>
            refine Prod.ext ?_ rfl
            refine Subtype.ext (Prod.ext ?_ rfl)
            exact extend_shiftV hq (e, false) c),
        extend_shiftV hq eb c, ih (extend eb c) v (by rw [endV_extend h]; exact hl.2)]

/-- **Change of base vertex of the universal cover.**  A path from `y₀` to `w₀` induces a
cellular map `Ũ(X, w₀) → Ũ(X, y₀)` over `X`; it sends the base vertex to the class of the
path.  For a loop this is the deck transformation attached to its class. -/
def shiftHom (hq : IsPath X.src X.tgt q y₀ w₀) :
    Hom (uCover X w₀) (uCover X y₀) where
  onV := shiftV hq
  onE := shiftE hq
  onF := shiftF hq
  src_onE := fun _ => rfl
  tgt_onE := fun E => extend_shiftV hq (E.1.2, true) E.1.1
  base_onF := fun _ => rfl
  att_onF := by
    intro F
    have hbase : endV F.1.1 = X.base F.1.2 := F.2
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [hbase]; exact X.att_isLoop F.1.2
    show uLiftPath (X.att F.1.2) (shiftV hq F.1.1) = _
    exact uLiftPath_shiftV hq (X.att F.1.2) F.1.1 (X.base F.1.2) hatt

@[simp] theorem onE_shiftHom (hq : IsPath X.src X.tgt q y₀ w₀) (E : UE X w₀) :
    ((shiftHom hq).onE E).1.2 = E.1.2 := rfl

@[simp] theorem onF_shiftHom (hq : IsPath X.src X.tgt q y₀ w₀) (F : UF X w₀) :
    ((shiftHom hq).onF F).1.2 = F.1.2 := rfl

end Shift

/-! ### Spherical classes coming from a subcomplex -/

variable {L L' E E' : Complex2.{u}}

/-- The set of spherical classes of `E` **coming from `L`** along `ι : L → E`: the images of
the two-cycles of the universal cover of `L` under all lifts of `ι` to the universal covers.
Letting the lift vary over all lifts (equivalently, over all copies of `L̃` in `Ẽ`) is what
makes the set closed under the deck group of `Ẽ`. -/
def Pi2FromSub (ι : Hom L E) (x₀ : E.V) : Set ((uCover E x₀).F →₀ ℤ) :=
  {d | ∃ (l₀ : L.V) (φ : Hom (uCover L l₀) (uCover E x₀)),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      ∃ z ∈ Pi2 L l₀, d = chain2 φ z}

/-- **The last step of the proof of Proposition 3.11.**  Let `j ∘ ι = ι' ∘ k` be a commuting
square of cellular maps in which the upper arrow `k : L → L'` is zero on `π₂`.  Then `j` kills
every spherical class of `E` which lies in the span of the classes coming from `L`. -/
theorem zeroPi2_chain_of_generated (ι : Hom L E) (k : Hom L L') (ι' : Hom L' E') (j : Hom E E')
    (hsq : j.comp ι = ι'.comp k) (hconnE' : IsConnected E') (hzero : ZeroPi2 k) {x₀ : E.V}
    {c : (uCover E x₀).F →₀ ℤ} (hgen : c ∈ Submodule.span ℤ (Pi2FromSub ι x₀)) :
    chain2 (univLift E j x₀) c = 0 := by
  have hsub : Pi2FromSub ι x₀ ≤ (LinearMap.ker (chain2 (univLift E j x₀)) : Submodule ℤ _) := by
    rintro d ⟨l₀, φ, hφV, hφE, hφF, z, hz, rfl⟩
    show chain2 (univLift E j x₀) (chain2 φ z) = 0
    -- the two maps of universal covers to be compared
    set J : Hom (uCover E x₀) (uCover E' (j.onV x₀)) := univLift E j x₀
    set A : Hom (uCover L l₀) (uCover E' (j.onV x₀)) := J.comp φ
    set kappa : Hom (uCover L l₀) (uCover L' (k.onV l₀)) := univLift L k l₀
    -- the base vertex of `A` and a path representing it
    have hbaseV : endV (A.onV (UV.base L l₀)) = ι'.onV (k.onV l₀) := by
      show endV (univLiftV x₀ j (φ.onV (UV.base L l₀))) = ι'.onV (k.onV l₀)
      rw [endV_univLiftV, hφV]
      exact congrArg (fun h : Hom L E' => h.onV l₀) hsq
    obtain ⟨tp, htp⟩ := Quotient.exists_rep (A.onV (UV.base L l₀))
    have hqpath : IsPath E'.src E'.tgt tp.1 (j.onV x₀) (ι'.onV (k.onV l₀)) := by
      have h := tp.2
      have hend : endpt E' (j.onV x₀) tp.1 = ι'.onV (k.onV l₀) := by
        rw [← hbaseV, ← htp]; rfl
      rwa [hend] at h
    -- the second map: the canonical lift of `ι'`, followed by the change of base vertex
    set chi : Hom (uCover L' (k.onV l₀)) (uCover E' (j.onV x₀)) :=
      (shiftHom hqpath).comp (univLift L' ι' (k.onV l₀))
    set B : Hom (uCover L l₀) (uCover E' (j.onV x₀)) := chi.comp kappa
    -- `A` and `B` are lifts of the same map along the universal covering of `E'`
    have hqcov : IsCovering (univProj E' (j.onV x₀)) := isCovering_univProj hconnE'
    have hE : ∀ e, (univProj E' (j.onV x₀)).onE (A.onE e)
        = (univProj E' (j.onV x₀)).onE (B.onE e) := by
      intro e
      show j.onE ((φ.onE e).1).2 = ι'.onE (k.onE (e.1.2))
      rw [hφE e]
      exact congrArg (fun h : Hom L E' => h.onE e.1.2) hsq
    have hF : ∀ f, (univProj E' (j.onV x₀)).onF (A.onF f)
        = (univProj E' (j.onV x₀)).onF (B.onF f) := by
      intro f
      show j.onF ((φ.onF f).1).2 = ι'.onF (k.onF (f.1.2))
      rw [hφF f]
      exact congrArg (fun h : Hom L E' => h.onF f.1.2) hsq
    have hbase : A.onV (UV.base L l₀) = B.onV (UV.base L l₀) := by
      show A.onV (UV.base L l₀) = shiftV hqpath ((univLift L' ι' (k.onV l₀)).onV
        (kappa.onV (UV.base L l₀)))
      have hk : kappa.onV (UV.base L l₀) = UV.base L' (k.onV l₀) := rfl
      have hi : (univLift L' ι' (k.onV l₀)).onV (UV.base L' (k.onV l₀))
          = UV.base E' (ι'.onV (k.onV l₀)) := rfl
      rw [hk, hi, shiftV_base]
      exact htp.symm
    have hV := lift_onV_eq hqcov isConnected_univCover hE hbase
    have hFeq := lift_onF_eq hqcov hF hV
    -- the upper arrow kills `z`
    have hkz : chain2 kappa z = 0 := hzero l₀ z hz
    have hAB : chain2 A z = chain2 B z :=
      congrArg (fun m => Finsupp.mapDomain m z) (funext hFeq)
    have hBz : chain2 B z = chain2 chi (chain2 kappa z) := by
      show Finsupp.mapDomain (chi.onF ∘ kappa.onF) z
        = Finsupp.mapDomain chi.onF (Finsupp.mapDomain kappa.onF z)
      rw [← Finsupp.mapDomain_comp]
    have hAz : chain2 (univLift E j x₀) (chain2 φ z) = chain2 A z := by
      show Finsupp.mapDomain J.onF (Finsupp.mapDomain φ.onF z)
        = Finsupp.mapDomain (J.onF ∘ φ.onF) z
      rw [← Finsupp.mapDomain_comp]
    rw [hAz, hAB, hBz, hkz, map_zero]
  exact Submodule.span_le.2 hsub hgen

/-- **The arrows of the descended chain are zero on `π₂` once `π₂` is generated from
upstairs.**  If every spherical class of `E` is a combination of classes coming from `L`, and
the upper arrow `k : L → L'` is zero on `π₂`, then the lower arrow `j : E → E'` is zero on
`π₂`. -/
theorem zeroPi2_of_pi2Generated (ι : Hom L E) (k : Hom L L') (ι' : Hom L' E') (j : Hom E E')
    (hsq : j.comp ι = ι'.comp k) (hconnE' : IsConnected E') (hzero : ZeroPi2 k)
    (hgen : ∀ (x₀ : E.V), ∀ c ∈ Pi2 E x₀, c ∈ Submodule.span ℤ (Pi2FromSub ι x₀)) :
    ZeroPi2 j :=
  fun x₀ c hc => zeroPi2_chain_of_generated ι k ι' j hsq hconnE' hzero (hgen x₀ c hc)

/-! ### The arrows of the descended chain -/

section Pushout

variable {D K M : Complex2.{u}}

theorem hom_ext {X Y : Complex2.{u}} : ∀ a b : Hom X Y,
    a.onV = b.onV → a.onE = b.onE → a.onF = b.onF → a = b := by
  rintro ⟨a1, a2, a3, p1, p2, p3, p4⟩ ⟨b1, b2, b3, q1, q2, q3, q4⟩ hV hE hF
  simp_all

/-- The factorization through the pushout restricts to the given map on the term upstairs. -/
theorem pushoutLift_comp_pushoutMap (p : Hom D K) (i : Hom D L) (hiV : Function.Injective i.onV)
    (hiE : Function.Injective i.onE) (hiF : Function.Injective i.onF) (f : Hom K M) (g : Hom L M)
    (hV : ∀ d, g.onV (i.onV d) = f.onV (p.onV d))
    (hE : ∀ d, g.onE (i.onE d) = f.onE (p.onE d))
    (hF : ∀ d, g.onF (i.onF d) = f.onF (p.onF d)) :
    (pushoutLift p i hiV hiE f g hV hE).comp (pushoutMap p i hiV hiE hiF) = g := by
  refine hom_ext _ _ (funext fun v => ?_) (funext fun e => ?_) (funext fun c => ?_)
  · show Sum.elim f.onV (fun w : OffV i => g.onV w.1) (pushV p i v) = g.onV v
    by_cases h : ∃ d, i.onV d = v
    · obtain ⟨d, rfl⟩ := h
      rw [pushV_of_mem p hiV d]
      exact (hV d).symm
    · rw [pushV_of_off p i ⟨v, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  · show Sum.elim f.onE (fun w : OffE i => g.onE w.1) (pushE p i e) = g.onE e
    by_cases h : ∃ d, i.onE d = e
    · obtain ⟨d, rfl⟩ := h
      rw [pushE_of_mem p hiE d]
      exact (hE d).symm
    · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
      rfl
  · show Sum.elim f.onF (fun w : OffF i => g.onF w.1) (pushF p i c) = g.onF c
    by_cases h : ∃ d, i.onF d = c
    · obtain ⟨d, rfl⟩ := h
      rw [pushF_of_mem p hiF d]
      exact (hF d).symm
    · rw [pushF_of_off p i ⟨c, fun d hd => h ⟨d, hd⟩⟩]
      rfl

/-- **The square of Proposition 3.11 commutes**: the map of pushouts induced by `L ⊆ L'`
restricted to `L` is the composite `L → L' → K ∪_p L'`. -/
theorem pushoutFunctor_comm (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hjF : Function.Injective j.onF) (hj'V : Function.Injective j'.onV)
    (hj'E : Function.Injective j'.onE) (hj'F : Function.Injective j'.onF)
    (hkj : k.comp j = j') :
    (pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj).comp (pushoutMap p j hjV hjE hjF)
      = (pushoutMap p j' hj'V hj'E hj'F).comp k := by
  have hV : ∀ d, ((pushoutMap p j' hj'V hj'E hj'F).comp k).onV (j.onV d)
      = (pushoutInl p j' hj'V hj'E).onV (p.onV d) := by
    intro d
    show pushV p j' (k.onV (j.onV d)) = Sum.inl (p.onV d)
    rw [show k.onV (j.onV d) = j'.onV d from congrFun (congrArg Hom.onV hkj) d,
      pushV_of_mem p hj'V]
  have hE : ∀ d, ((pushoutMap p j' hj'V hj'E hj'F).comp k).onE (j.onE d)
      = (pushoutInl p j' hj'V hj'E).onE (p.onE d) := by
    intro d
    show pushE p j' (k.onE (j.onE d)) = Sum.inl (p.onE d)
    rw [show k.onE (j.onE d) = j'.onE d from congrFun (congrArg Hom.onE hkj) d,
      pushE_of_mem p hj'E]
  have hF : ∀ d, ((pushoutMap p j' hj'V hj'E hj'F).comp k).onF (j.onF d)
      = (pushoutInl p j' hj'V hj'E).onF (p.onF d) := by
    intro d
    show pushF p j' (k.onF (j.onF d)) = Sum.inl (p.onF d)
    rw [show k.onF (j.onF d) = j'.onF d from congrFun (congrArg Hom.onF hkj) d,
      pushF_of_mem p hj'F]
  exact pushoutLift_comp_pushoutMap p j hjV hjE hjF _ _ hV hE hF

/-- **The arrows of the descended chain are zero on `π₂`, granted the generation statement
(3.5).**  For the cellular pushouts `E = K ∪_p L ⊆ E' = K ∪_p L'` of Proposition 3.11: if the
second homotopy module of `E` is generated by the classes coming from `L`, and `L → L'` is
zero on `π₂`, then so is `E → E'`. -/
theorem zeroPi2_pushoutFunctor (p : Hom D K) (j : Hom D L) (j' : Hom D L') (k : Hom L L')
    (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
    (hjF : Function.Injective j.onF) (hj'V : Function.Injective j'.onV)
    (hj'E : Function.Injective j'.onE) (hj'F : Function.Injective j'.onF)
    (hkj : k.comp j = j') (hconnE' : IsConnected (pushoutComplex p j' hj'V hj'E))
    (hzero : ZeroPi2 k)
    (hgen : ∀ x₀ : (pushoutComplex p j hjV hjE).V,
      ∀ c ∈ Pi2 (pushoutComplex p j hjV hjE) x₀,
        c ∈ Submodule.span ℤ (Pi2FromSub (pushoutMap p j hjV hjE hjF) x₀)) :
    ZeroPi2 (pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj) :=
  zeroPi2_of_pi2Generated (pushoutMap p j hjV hjE hjF) k (pushoutMap p j' hj'V hj'E hj'F) _
    (pushoutFunctor_comm p j j' k hjV hjE hjF hj'V hj'E hj'F hkj) hconnE' hzero hgen

end Pushout

end Comb
end FiniteChains
end

namespace FiniteChains
namespace Comb

universe u

/-! ### Chains with explicit inclusions -/

/-- The inclusion of the first term of a chain into its `i`-th term. -/
def inclFrom (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1))) :
    ∀ i, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (inc i).comp (inclFrom c inc i)

@[simp] theorem inclFrom_succ (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1)))
    (i : ℕ) : inclFrom c inc (i + 1) = (inc i).comp (inclFrom c inc i) := rfl


namespace RelChainW

section Functor

variable (K : Complex2.{u}) {L L' : Complex2.{u}} {D' : Complex2.{u}} (q : Hom D' K) (j : Hom D' L) (j' : Hom D' L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

include hkj in
theorem pushoutFunctor_injV (hkV : Function.Injective k.onV) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onV := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.V, F.onV (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffV j, F.onV (Sum.inr w) = Sum.inr ⟨k.onV w.1, off_map_V hkV hkj w⟩ :=
    fun w => pushV_of_off q j' ⟨k.onV w.1, off_map_V hkV hkj w⟩
  rintro (a | w) (b | w') h
  · grind
  · simp_all
  · simp_all
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkV (congrArg Subtype.val (Sum.inr_injective h))))

include hkj in
theorem pushoutFunctor_injE (hkE : Function.Injective k.onE) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onE := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.E, F.onE (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffE j, F.onE (Sum.inr w) = Sum.inr ⟨k.onE w.1, off_map_E hkE hkj w⟩ :=
    fun w => pushE_of_off q j' ⟨k.onE w.1, off_map_E hkE hkj w⟩
  rintro (a | w) (b | w') h
  · grind
  · simp_all
  · simp_all
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkE (congrArg Subtype.val (Sum.inr_injective h))))

include hkj in
theorem pushoutFunctor_injF (hkF : Function.Injective k.onF) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onF := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.F, F.onF (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffF j, F.onF (Sum.inr w) = Sum.inr ⟨k.onF w.1, off_map_F hkF hkj w⟩ :=
    fun w => pushF_of_off q j' ⟨k.onF w.1, off_map_F hkF hkj w⟩
  rintro (a | w) (b | w') h
  · grind
  · simp_all
  · simp_all
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkF (congrArg Subtype.val (Sum.inr_injective h))))

end Functor

/-! ### Finiteness and connectivity of the stages -/

/-! ### The arrows are zero on `π₂` -/

end RelChainW



/-! ### Strictness of the descended chain -/



/-! ### Non-vacuity: the constant chain -/

/-! ### Assembling Theorem A -/

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {I J : Type u} [LinearOrder I] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (r : J → FreeGroup I)

/-! ### Acyclicity of the presentation complex, read off the exponent-sum matrix -/

omit [LinearOrder I] [Fintype I] [Fintype J] [DecidableEq J] in
theorem bdry2_presComplex_eq_expCol :
    bdry2 (presComplex r) = Finsupp.linearCombination ℤ (expCol r) := by
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
  show bdry2 (presComplex r) (Finsupp.single j 1)
    = Finsupp.linearCombination ℤ (expCol r) (Finsupp.single j 1)
  rw [bdry2_pres_single, Finsupp.linearCombination_single, one_smul, expCol_eq_expVec]
  rfl

/-! ### The hypotheses are satisfiable -/

end Comb
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
  (hN : ∀ f, treeRel T f ∈ N)

/-- Two lifted edge chains with equal vertex boundaries are equal as soon as
their non-tree coordinates agree. The difference is a cycle supported on trees. -/
theorem piE_injective_of_same_boundary (c d : (CovQ T N × K.E) →₀ ℤ)
    (hb : bdry1 (treeCover T N hN) c = bdry1 (treeCover T N hN) d)
    (he : piE T N c = piE T N d) : c = d := by
  classical
  apply sub_eq_zero.mp
  apply treeChain_eq_zero (hN := hN)
  · apply support_isTree_of_piE_eq_zero
    rw [map_sub, he, sub_self]
  · simp_all

variable [DecidableEq (NonTree T)]

end FiniteChains.Comb.SpanningTree

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
  [DecidableEq (NonTree T)] (hN : ∀ f, treeRel T f ∈ N)

theorem piE_sectionE (z : (CovQ T N × NonTree T) →₀ ℤ) :
    piE T N (sectionE T N z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single a n =>
      rcases a with ⟨q, e⟩
      rw [sectionE, Finsupp.linearCombination_single, map_smul, piE_pathChain_liftK]
      have hl  :=
        (mk_letters (loopPath T e)).trans (pathWord_loopPath e)
      rw [pathChain_liftPath_congr (N := N) hl]
      simp [liftPath_cons_true, pathChain_cons, pathChain_nil]

omit [N.Normal] [DecidableEq (NonTree T)] in
theorem piV_iotaV (z : CovQ T N →₀ ℤ) : piV T N (iotaV T N z) = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single q n => simp

theorem coverComplex_isAcyclic_of_treeCover
    (h : IsAcyclic (treeCover T N hN)) : IsAcyclic (coverComplex N (treeRel T) hN) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply h.h2
    apply piE_injective_of_same_boundary T N hN
    · rw [bdry1_bdry2, bdry1_bdry2]
    · rw [piE_bdry2, piE_bdry2, hab]
  · intro z hz
    have hlift : bdry1 (treeCover T N hN) (sectionE T N z) = 0 := by
      rw [bdry1_sectionE, hz, map_zero]
    obtain ⟨a, ha⟩ := h.h1 (sectionE T N z) hlift
    exact ⟨a, by rw [← piE_bdry2, ha, piE_sectionE]⟩
  · intro z hz
    have hlift : augC (treeCover T N hN) (iotaV T N z) = 0 := by
      rw [← augC_piV, piV_iotaV, hz]
    obtain ⟨a, ha⟩ := h.h0 (iotaV T N z) hlift
    exact ⟨piE T N a, by rw [← piV_bdry1, ha, piV_iotaV]⟩

end FiniteChains.Comb.SpanningTree
end

section
open scoped Classical
namespace FiniteChains.Comb
universe u

theorem bdry2_presComplex_eq_expMatrix {A J : Type u} [DecidableEq A]
    (ρ : J → FreeGroup A) : bdry2 (presComplex ρ) = FiniteChains.expMatrix ρ := by
  rw [bdry2_presComplex_eq_expCol]
  apply congrArg (Finsupp.linearCombination ℤ)
  exact funext (expCol_eq_expVec ρ)

theorem oneSheetProjection_bijective {Q B : Type u} [One Q] [Subsingleton Q] :
    Function.Bijective (Prod.snd : Q × B → B) := by
  constructor
  · intro a b h
    exact Prod.ext (Subsingleton.elim _ _) h
  · intro b
    exact ⟨(1, b), rfl⟩

namespace SpanningTree
variable {D : Complex2.{u}} (T : SpanningTree D)

theorem expMatrix_bijective_of_acyclic (hD : IsAcyclic D) :
    Function.Bijective (FiniteChains.expMatrix (treeRel T)) := by
  let N : Subgroup (FreeGroup (NonTree T)) := ⊤
  let hN : ∀ f, treeRel T f ∈ N := fun _ => Subgroup.mem_top _
  letI : Subsingleton (CovQ T N) := QuotientGroup.subsingleton_quotient_top
  have htree  :=
    (isAcyclic_iff_of_cell_bijections (treeCoverProj T N hN)
      oneSheetProjection_bijective oneSheetProjection_bijective oneSheetProjection_bijective).mpr hD
  have hcover  :=
    coverComplex_isAcyclic_of_treeCover T N hN htree
  have hpres  :=
    (isAcyclic_iff_of_cell_bijections (coverProj hN)
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨1, Subsingleton.elim _ _⟩⟩
      oneSheetProjection_bijective oneSheetProjection_bijective).mp hcover
  have hb : Function.Bijective (bdry2 (presComplex (treeRel T))) :=
    ⟨hpres.h2, fun z => hpres.h1 z (bdry1_presComplex (treeRel T) z)⟩
  rwa [bdry2_presComplex_eq_expMatrix] at hb

end SpanningTree
end FiniteChains.Comb
end

namespace FiniteChains.Comb.SpanningTree
universe u
variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
  [DecidableEq (NonTree TX)] [DecidableEq (NonTree TY)]
  {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)
  (hE : Function.Injective h.onE)

theorem pi1Trivial_of_pi1Trivial_presInclHom
    (hz : Pi1Trivial (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
      (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff))) : Pi1Trivial h := by
  have hzero := (pi1Trivial_presInclHom_iff (ρ := treeRel TX)
    (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).mp hz
  intro a p hp
  have hword : wordClass TY (mapPath h p) = 1 := by
    change (QuotientGroup.mk (pathWord TY (mapPath h p))) = 1
    rw [pathWord_mapPath hiff]
    exact hzero (QuotientGroup.mk (pathWord TX p))
  have hlo : loopOf TY (isPath_mapPath h hp) = 1 := by
    apply (pi1EquivPres TY).injective
    rw [map_one]
    exact (uvQ_conjPath (isPath_mapPath h hp)).trans hword
  have H  := Quotient.exact hlo
  have Hnil : Htpy Y TY.root TY.root
      (conjPath TY [] (h.onV a) (h.onV a)) [] := by
    simpa only [conjPath, List.append_nil] using htpy_append_revPath (TY.treePath_isPath (h.onV a))
  exact htpy_of_congr_append (TY.treePath_isPath (h.onV a))
    (isPath_revPath (TY.treePath_isPath (h.onV a)))
    (isPath_mapPath h hp) rfl (H.trans Hnil.symm)

end FiniteChains.Comb.SpanningTree

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  [DiscreteTopology V] [DiscreteTopology W]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (s : BoundaryFamily K (Fin 1 → ℝ) → W) (hs : Continuous s)
  (T : Comb.SpanningTree (graphCx r)) (U : Comb.SpanningTree (graphCx s))
  (h : Comb.Hom (graphCx r) (graphCx s))
  (ht : ∀ j, U.isTree (h.onE j) ↔ T.isTree j)

def graphNonTreeMap : {j : J // ¬T.isTree j} → {k : K // ¬U.isTree k} :=
  fun j => ⟨h.onE j.val, fun hu => j.property ((ht j.val).mp hu)⟩

def graphRoseCombinatorialMap :
    Comb.Hom (graphCx (roseAttaching {j : J // ¬T.isTree j}))
      (graphCx (roseAttaching {k : K // ¬U.isTree k})) where
  onV := id
  onE := graphNonTreeMap r s T U h ht
  onF := Empty.elim
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF f := Empty.elim f
  att_onF f := Empty.elim f

def graphRoseMap : C(Rose {j : J // ¬T.isTree j}, Rose {k : K // ¬U.isTree k}) :=
  diskFamilyMap (roseAttaching _) (roseAttaching _) (ContinuousMap.id PUnit)
    (graphNonTreeMap r s T U h ht) (fun _ _ => rfl)

theorem graphRoseHomotopyEquiv_natural (f : C(DiskAttachment r, DiskAttachment s))
    (hv : ∀ v, f (old r (boundaryFamilyInclusion J _) v) =
      old s (boundaryFamilyInclusion K _) (h.onV v))
    (he : ∀ j x, f (cell r (boundaryFamilyInclusion J _) ⟨j, x⟩) =
      cell s (boundaryFamilyInclusion K _) ⟨h.onE j, x⟩) :
    (graphRoseMap r s T U h ht).comp (graphRoseHomotopyEquiv r hr T).toFun =
      (graphRoseHomotopyEquiv s hs U).toFun.comp f := by
  apply hom_ext r (boundaryFamilyInclusion J (Fin 1 → ℝ))
  · intro v
    change graphRoseMap r s T U h ht (graphRoseHomotopyEquiv r hr T (old _ _ v)) =
      graphRoseHomotopyEquiv s hs U (f (old _ _ v))
    rw [graphRoseHomotopyEquiv_old, hv]
    rw [graphRoseHomotopyEquiv_old]
    rfl
  · rintro ⟨j, x⟩
    change graphRoseMap r s T U h ht (graphRoseHomotopyEquiv r hr T (cell _ _ ⟨j, x⟩)) =
      graphRoseHomotopyEquiv s hs U (f (cell _ _ ⟨j, x⟩))
    rw [he]
    by_cases hj : T.isTree j
    · have hk := (ht j).mpr hj
      rw [graphRoseHomotopyEquiv_treeCell r hr T ⟨⟨j, hj⟩, x⟩,
        graphRoseHomotopyEquiv_treeCell s hs U ⟨⟨h.onE j, hk⟩, x⟩]
      rfl
    · have hk  := fun hk => hj ((ht j).mp hk)
      rw [graphRoseHomotopyEquiv_nonTreeCell r hr T ⟨⟨j, hj⟩, x⟩,
        graphRoseHomotopyEquiv_nonTreeCell s hs U ⟨⟨h.onE j, hk⟩, x⟩]
      exact diskFamilyMap_cell (roseAttaching _) (roseAttaching _) (ContinuousMap.id PUnit)
        (graphNonTreeMap r s T U h ht) (fun _ _ => rfl) ⟨j, hj⟩ x

end FiniteChains.ClassicalGraphModel
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords
open scoped Classical unitInterval
variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def treeLetters : List (J × Bool) → List ({j : J // ¬T.isTree j} × Bool)
  | [] => []
  | g :: l => if h : T.isTree g.1 then treeLetters l
      else (⟨g.1, h⟩, g.2) :: treeLetters l

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem treeLetters_append (l m : List (J × Bool)) :
    treeLetters r T (l ++ m) = treeLetters r T l ++ treeLetters r T m := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    by_cases h : T.isTree g.1 <;> simp only [List.cons_append, treeLetters, h,
      dite_true, dite_false, ih, List.cons_append]

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem treeLetters_revPath (l : List (J × Bool)) :
    treeLetters r T (Comb.revPath (X := graphCx r) l) =
      Comb.revPath (X := graphCx (roseAttaching {j : J // ¬T.isTree j})) (treeLetters r T l) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [Comb.revPath_cons]
    rw [treeLetters_append, ih]
    by_cases h : T.isTree g.1
    · simp only [treeLetters, Comb.revGerm, h, dite_true, List.append_nil]
    · simp only [treeLetters, Comb.revGerm, h, dite_false, Comb.revPath,
        List.reverse_cons, List.map_cons]

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem treeLetters_mk (l : List (J × Bool)) :
    FreeGroup.mk (treeLetters r T l) = Comb.SpanningTree.pathWord T l := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    by_cases h : T.isTree g.1
    · rw [treeLetters, dif_pos h, Comb.SpanningTree.pathWord_cons T g l,
        Comb.SpanningTree.germWord_of_isTree T h, one_mul, ih]
    · rw [treeLetters, dif_neg h, Comb.SpanningTree.pathWord_cons]
      change FreeGroup.mk ([(⟨g.1, h⟩, g.2)] ++ treeLetters r T l) = _
      rw [← FreeGroup.mul_mk, ih]
      congr 1
      cases g with
      | mk j o => cases o <;> simp only [Comb.SpanningTree.germWord, dif_neg h] <;> rfl

theorem rose_word_isPath {A : Type} (l : List (A × Bool)) :
    Comb.IsPath (graphCx (roseAttaching A)).src (graphCx (roseAttaching A)).tgt l
      PUnit.unit PUnit.unit := by
  induction l with
  | nil => rfl
  | cons g l ih => cases g with | mk e o => cases o <;> exact ⟨rfl, ih⟩

def treeRoseWordPath (l : List (J × Bool)) :
    Path (roseVertex {j : J // ¬T.isTree j}) (roseVertex {j : J // ¬T.isTree j}) :=
  realize _ _ (old (roseAttaching _) _) (graphEdgePath (roseAttaching _))
    (treeLetters r T l) (rose_word_isPath _)

def collapsedWordPath (l : List (J × Bool)) {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b) :
    Path (roseVertex {j : J // ¬T.isTree j}) (roseVertex {j : J // ¬T.isTree j}) :=
  ((realize _ _ (old r _) (graphEdgePath r) l hl).map
    (graphRoseHomotopyEquiv r hr T).continuous).cast
      (graphRoseHomotopyEquiv_old r hr T a).symm
      (graphRoseHomotopyEquiv_old r hr T b).symm

def collapsedGermPath (g : J × Bool) :
    Path (roseVertex {j : J // ¬T.isTree j}) (roseVertex {j : J // ¬T.isTree j}) :=
  ((graphGermPath r g).map (graphRoseHomotopyEquiv r hr T).continuous).cast
    (graphRoseHomotopyEquiv_old r hr T _).symm
    (graphRoseHomotopyEquiv_old r hr T _).symm




theorem collapsedWordPath_homotopic_treeWord (l : List (J × Bool)) {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b) :
    (collapsedWordPath r hr T l hl).Homotopic (treeRoseWordPath r T l) := by
  induction l generalizing a with
  | nil => rfl
  | cons g l ih =>
    rw [(show collapsedWordPath r hr T (g :: l) hl =
      (collapsedGermPath r hr T g).trans (collapsedWordPath r hr T l hl.2) by
      apply Path.ext
      funext t
      simp only [collapsedWordPath, collapsedGermPath, realize, Path.cast_coe,
        Path.map_coe, Function.comp_apply, Path.trans_apply]
      split_ifs
      · cases g with | mk j o => cases o <;> rfl
      · rfl)]
    by_cases hg : T.isTree g.1
    · rw [(show collapsedGermPath r hr T g = Path.refl _ by
      apply Path.ext
      funext t
      cases g with
      | mk j o =>
        cases o <;> exact graphRoseHomotopyEquiv_treePath r hr T ⟨j, hg⟩ _)]
      have ht : treeRoseWordPath r T (g :: l) = treeRoseWordPath r T l := by
        simp only [treeRoseWordPath, treeLetters, dif_pos hg]
      rw [ht]
      exact ((Path.Homotopic.refl _).hcomp (ih hl.2)).trans (Path.Homotopic.refl_trans _)
    · rw [(show collapsedGermPath r hr T g =
      germPath (graphSrc (roseAttaching _)) (graphTgt (roseAttaching _))
        (old (roseAttaching _) _) (graphEdgePath (roseAttaching _)) (⟨g.1, hg⟩, g.2) by
      apply Path.ext
      funext t
      cases g with
      | mk j o =>
        cases o <;> exact graphRoseHomotopyEquiv_nonTreeCell r hr T ⟨⟨j, hg⟩, graphDiskHomeomorph _⟩)]
      have ht : treeRoseWordPath r T (g :: l) =
          (germPath (graphSrc (roseAttaching _)) (graphTgt (roseAttaching _))
            (old (roseAttaching _) _) (graphEdgePath (roseAttaching _))
              (⟨g.1, hg⟩, g.2)).trans (treeRoseWordPath r T l) := by
        simp only [treeRoseWordPath, treeLetters, dif_neg hg, realize]
        rfl
      rw [ht]
      exact (Path.Homotopic.refl _).hcomp (ih hl.2)

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval
variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def BoundaryWords.eraseTree (W : BoundaryWords r) :
    BoundaryWords (roseAttaching {j : J // ¬T.isTree j}) where
  vertex := fun _ => PUnit.unit
  word s := treeLetters r T (W.word s)
  isPath _ := rose_word_isPath _


omit [TopologicalSpace V] [DiscreteTopology V] in
theorem BoundaryWords.eraseTree_mk (W : BoundaryWords r) :
    FreeGroup.mk (W.eraseTree r T).loopWord = Comb.SpanningTree.pathWord T W.loopWord := by
  rw [(show (W.eraseTree r T).loopWord = treeLetters r T W.loopWord by
    simp only [BoundaryWords.loopWord, BoundaryWords.eraseTree,
      List.append_eq, treeLetters_append, treeLetters_revPath]), treeLetters_mk]

theorem BoundaryWords.collapse_homotopic_eraseTree (W : BoundaryWords r) :
    ((graphRoseHomotopyEquiv r hr T).toFun.comp W.boundaryMap).Homotopic
      (W.eraseTree r T).boundaryMap := by
  let W' := W.eraseTree r T
  let H s := Classical.choice
    (collapsedWordPath_homotopic_treeWord r hr T (W.word s) (W.isPath s))
  have hend : ∀ s t u, u = 0 ∨ u = 1 →
      H s (t, u) = roseVertex {j : J // ¬T.isTree j} := by
    intro s t u hu
    rcases hu with rfl | rfl
    · simp
    · simp
  let G := squareBoundaryHomotopyPasting (fun s => (H s).toHomotopy.toContinuousMap)
    (fun _ _ => roseVertex {j : J // ¬T.isTree j}) hend
  let HG : ((graphRoseHomotopyEquiv r hr T).toFun.comp W.squareMap).Homotopy W'.squareMap := {
    toContinuousMap := G
    map_zero_left := by
      intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting _ _ hend (0, squareSideMap s u) = _
      rw [squareBoundaryHomotopyPasting_side]
      change H s (0, u) = graphRoseHomotopyEquiv r hr T (W.squareMap (squareSideMap s u))
      rw [(H s).apply_zero, W.squareMap_side]
      rfl
    map_one_left := by
      intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting _ _ hend (1, squareSideMap s u) = _
      rw [squareBoundaryHomotopyPasting_side]
      change H s (1, u) = W'.squareMap (squareSideMap s u)
      rw [(H s).apply_one, W'.squareMap_side]
      rfl }
  exact ⟨HG.compContinuousMap unitBoundarySquareHomeomorph.toContinuousMap⟩

end FiniteChains.ClassicalGraphModel
end

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  [DiscreteTopology V] [DiscreteTopology W]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)
  (s : BoundaryFamily K (Fin 1 → ℝ) → W)
  (T : Comb.SpanningTree (graphCx r)) (U : Comb.SpanningTree (graphCx s))
  (h : Comb.Hom (graphCx r) (graphCx s))
  (ht : ∀ j, U.isTree (h.onE j) ↔ T.isTree j)

omit [TopologicalSpace V] [TopologicalSpace W] [DiscreteTopology V] [DiscreteTopology W]

theorem treeLetters_map (l : List (J × Bool)) :
    treeLetters s U (Comb.mapPath h l) =
      (treeLetters r T l).map (fun g => (graphNonTreeMap r s T U h ht g.1, g.2)) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    change treeLetters s U ((h.onE g.1, g.2) :: Comb.mapPath h l) = _
    by_cases hg : T.isTree g.1
    · have hu := (ht g.1).mpr hg
      simpa only [treeLetters, dif_pos hg, dif_pos hu] using ih
    · have hu  := fun hu => hg ((ht g.1).mp hu)
      simp only [treeLetters, dif_neg hg, dif_neg hu, List.map_cons]
      rw [ih]
      rfl


theorem BoundaryWords.eraseTree_loop_natural (b : BoundaryWords r) :
    ((b.map h).eraseTree s U).loopWord =
      ((b.eraseTree r T).loopWord).map
        (fun g => (graphNonTreeMap r s T U h ht g.1, g.2)) := by
  rw [(show (b.map h).eraseTree s U =
      (b.eraseTree r T).map (graphRoseCombinatorialMap r s T U h ht) by
    have hw  :=
      fun i => treeLetters_map r s T U h ht (b.word i)
    have extWords (x y : BoundaryWords (roseAttaching {k : K // ¬U.isTree k}))
        (hv : x.vertex = y.vertex) (hw : x.word = y.word) : x = y := by
      cases x
      cases y
      cases hv
      cases hw
      rfl
    apply extWords
    · rfl
    · exact funext hw)]
  exact BoundaryWords.loopWord_map (graphRoseCombinatorialMap r s T U h ht) (b.eraseTree r T)

end FiniteChains.ClassicalGraphModel

section
open scoped Classical unitInterval Topology
namespace FiniteChains.PresModel
open ClassicalGraphModel RelativeAttachment

variable {A : Type}

theorem classicalRoseRead_append (l m : List (A × Bool)) :
    ((classicalRoseRead l).trans (classicalRoseRead m)).Homotopic (classicalRoseRead (l ++ m)) := by
  induction l with
  | nil => exact Path.Homotopic.refl_trans _
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    exact (Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp ih)

theorem classicalRoseRead_cancelHead (a : A) (b : Bool) (l : List (A × Bool)) :
    (classicalRoseRead ((a, b) :: (a, !b) :: l)).Homotopic (classicalRoseRead l) := by
  cases b
  · change (((graphEdgePath (roseAttaching A) a).symm).trans
      ((graphEdgePath (roseAttaching A) a).trans (classicalRoseRead l))).Homotopic _
    exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.symm_trans _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))
  · change ((graphEdgePath (roseAttaching A) a).trans
      (((graphEdgePath (roseAttaching A) a).symm).trans (classicalRoseRead l))).Homotopic _
    exact (Path.Homotopic.trans_assoc _ _ _).symm.trans
      (((Path.Homotopic.trans_symm _).hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.refl_trans _))



theorem classicalRoseRead_homotopic_of_red {l m : List (A × Bool)} (h : FreeGroup.Red l m) :
    (classicalRoseRead l).Homotopic (classicalRoseRead m) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (by
    cases hstep with
    | not => exact ((classicalRoseRead_append _ _).symm.trans
    (((Path.Homotopic.refl _).hcomp (classicalRoseRead_cancelHead _ _ _)).trans
      (classicalRoseRead_append _ _))))

/-- Equality in the free group is realized by an actual fixed-endpoint
homotopy of the continuous word paths. -/

def classicalRoseWordBoundary (l : List (A × Bool)) :
    C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (squareLoopDesc (classicalRoseRead l)).comp unitBoundarySquareHomeomorph.toContinuousMap


theorem classicalRoseWordBoundary_homotopic_of_mk_eq {l m : List (A × Bool)}
    (h : FreeGroup.mk l = FreeGroup.mk m) :
    (classicalRoseWordBoundary l).Homotopic (classicalRoseWordBoundary m) :=
  ((squareLoopDesc_homotopic (by
    obtain ⟨r, hl, hm⟩ := FreeGroup.Red.exact.mp h
    exact (classicalRoseRead_homotopic_of_red hl).trans (classicalRoseRead_homotopic_of_red hm).symm)).comp
    (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap))

end FiniteChains.PresModel
end

section
open scoped Classical
namespace FiniteChains.Comb
universe u v
variable {X Y : Complex2.{u}} {G : Type v} [Group G]

namespace EdgeLabels
def germ (w : X.E → G) (e : X.E × Bool) : G := if e.2 then w e.1 else (w e.1)⁻¹
def read (w : X.E → G) (p : List (X.E × Bool)) : G := (p.map (germ w)).prod

@[simp] theorem read_nil (w : X.E → G) : read w [] = 1 := rfl
@[simp] theorem read_cons (w : X.E → G) (e : X.E × Bool) (p : List (X.E × Bool)) :
    read w (e :: p) = germ w e * read w p := rfl
theorem read_append (w : X.E → G) (p q : List (X.E × Bool)) :
    read w (p ++ q) = read w p * read w q := by simp [read, List.prod_append]

theorem read_cancels (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    {p q : List (X.E × Bool)} (h : Cancels X p q) : read w p = read w q := by
  rcases h with ⟨a, b, e, rfl, rfl⟩ | ⟨a, b, f, rfl, rfl⟩
  · rw [read_append, read_append, read_cons, read_cons, (show germ w (revGerm e) = (germ w e)⁻¹ by
    rcases e with ⟨e, b⟩
    cases b <;> simp [germ, revGerm])]
    group
  · rw [read_append, read_append, read_append, hw, mul_one]

theorem read_htpy (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    {a b : X.V} {p q : List (X.E × Bool)} (h : Htpy X a b p q) : read w p = read w q := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      rcases hs with hs | hs
      · exact ih.trans (read_cancels w hw hs.2.2)
      · exact ih.trans (read_cancels w hw hs.2.2).symm

def monodromy (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1) (a : X.V) : Pi1 X a →* G where
  toFun := Quotient.lift (fun p => read w p.val) (fun _ _ h => read_htpy w hw h)
  map_one' := rfl
  map_mul' := by rintro ⟨p⟩ ⟨q⟩; exact read_append w p.val q.val

theorem read_mapPath (w : Y.E → G) (f : Hom X Y) (p : List (X.E × Bool)) :
    read w (mapPath f p) = read (w ∘ f.onE) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [mapPath, List.map_cons, read_cons] at *; rw [ih]; rfl

theorem read_potential (w : X.E → G) (v : X.V → G)
    (hw : ∀ e, w e = (v (X.src e))⁻¹ * v (X.tgt e))
    {p : List (X.E × Bool)} {a b : X.V} (hp : IsPath X.src X.tgt p a b) :
    read w p = (v a)⁻¹ * v b := by
  have hg e : germ w e =
      (v (germSrc X.src X.tgt e))⁻¹ * v (germTgt X.src X.tgt e) := by
    rcases e with ⟨e, b⟩
    cases b <;> simp [germ, germSrc, germTgt, hw, mul_inv_rev]
  induction p generalizing a with
  | nil => simp_all
  | cons e p ih =>
      obtain ⟨ha, hp⟩ := hp
      subst ha
      rw [read_cons, hg, ih hp]
      group
end EdgeLabels

/-- Paths from one root, with the empty path chosen at the root. -/
structure RootPaths (X : Complex2.{u}) (a : X.V) where
  path : X.V → List (X.E × Bool)
  valid : ∀ b, IsPath X.src X.tgt (path b) a b
  at_root : path a = []

namespace RootPaths
variable {a : X.V} (r : RootPaths X a)

def choose (hc : IsConnected X) (a : X.V) : RootPaths X a where
  path b := if b = a then [] else Classical.choose (hc a b)
  valid b := by
    split
    · simp_all
    · grind
  at_root := by simp

def conjugate (p : List (X.E × Bool)) (b c : X.V) := r.path b ++ p ++ revPath (r.path c)

theorem conjugate_valid {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) :
    IsPath X.src X.tgt (r.conjugate p b c) a a :=
  isPath_append_iff.mpr ⟨c, isPath_append_iff.mpr ⟨b, r.valid b, hp⟩, isPath_revPath (r.valid c)⟩

def classOf {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) : Pi1 X a :=
  Pi1.mk ⟨r.conjugate p b c, r.conjugate_valid hp⟩

theorem classOf_htpy {p q : List (X.E × Bool)} {b c : X.V}
    (hp : IsPath X.src X.tgt p b c) (hq : IsPath X.src X.tgt q b c)
    (h : Htpy X b c p q) : r.classOf hp = r.classOf hq :=
  Quotient.sound (h.congr_append (r.valid b) (isPath_revPath (r.valid c)))

@[simp] theorem classOf_nil (b : X.V) : r.classOf (p := []) (b := b) (c := b) rfl = 1 := by
  apply Quotient.sound
  change Htpy X a a _ _
  simpa [loopSetoid, Pi1, Loop, conjugate] using htpy_append_revPath (r.valid b)

theorem classOf_mul {p q : List (X.E × Bool)} {b c d : X.V}
    (hp : IsPath X.src X.tgt p b c) (hq : IsPath X.src X.tgt q c d) :
    r.classOf hp * r.classOf hq = r.classOf (isPath_append_iff.mpr ⟨c, hp, hq⟩) := by
  apply Quotient.sound
  change Htpy X a a _ _
  have h := (htpy_revPath_append (r.valid c)).congr_append
    (isPath_append_iff.mpr ⟨b, r.valid b, hp⟩)
    (isPath_append_iff.mpr ⟨d, hq, isPath_revPath (r.valid d)⟩)
  simpa [loopSetoid, Pi1, Loop, conjugate, List.append_assoc] using h

theorem classOf_rev {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) :
    r.classOf (isPath_revPath hp) = (r.classOf hp)⁻¹ := by
  apply Quotient.sound
  simp only [conjugate, revPath_append, revPath_revPath, List.append_assoc]
  exact Htpy.refl _

def edge (e : X.E) : Pi1 X a := r.classOf (isPath_single (e, true))


theorem read_classOf {p : List (X.E × Bool)} {b c : X.V} (hp : IsPath X.src X.tgt p b c) :
    EdgeLabels.read r.edge p = r.classOf hp := by
  induction p generalizing b with
  | nil => cases hp; exact (r.classOf_nil _).symm
  | cons e p ih =>
      obtain ⟨hb, hp⟩ := hp
      subst hb
      rw [EdgeLabels.read_cons, (show EdgeLabels.germ r.edge e = r.classOf (isPath_single e) by
        rcases e with ⟨e, b⟩
        cases b with
        | true => rfl
        | false =>
            exact (r.classOf_rev (isPath_single (e, true))).symm), ih hp]
      exact r.classOf_mul (isPath_single e) hp

theorem edge_rel (f : X.F) : EdgeLabels.read r.edge (X.att f) = 1 := by
  rw [r.read_classOf (X.att_isLoop f)]
  have h : Htpy X (X.base f) (X.base f) (X.att f) [] :=
    Htpy.of_step ⟨X.att_isLoop f, rfl, Or.inr ⟨[], [], f, by simp, rfl⟩⟩
  exact (r.classOf_htpy (q := []) (X.att_isLoop f) rfl h).trans (r.classOf_nil _)

theorem read_loop (p : Loop X a) : EdgeLabels.read r.edge p.val = Pi1.mk p := by
  rw [r.read_classOf p.property]
  apply Quotient.sound
  simp only [conjugate, r.at_root, List.nil_append, revPath_nil, List.append_nil]
  exact Htpy.refl _

end RootPaths
end FiniteChains.Comb

namespace FiniteChains.Comb.RegularCoverLabels
universe u v
variable {D K : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)

def sectionV (v : K.V) : D.V := Classical.choose (hp.surjV v)
theorem sectionV_spec (v : K.V) : p.onV (sectionV p hp v) = v := Classical.choose_spec (hp.surjV v)

def sheet (d : D.V) : Q := Classical.choose
  (hr.simply_transitive (sectionV p hp (p.onV d)) d (sectionV_spec p hp (p.onV d)))

theorem sheet_spec (d : D.V) : a.smulV (sheet p hp a hr d) (sectionV p hp (p.onV d)) = d :=
  (Classical.choose_spec (hr.simply_transitive (sectionV p hp (p.onV d)) d
    (sectionV_spec p hp (p.onV d)))).1

theorem sheet_unique (d : D.V) (q : Q)
    (hq : a.smulV q (sectionV p hp (p.onV d)) = d) : q = sheet p hp a hr d :=
  (Classical.choose_spec (hr.simply_transitive (sectionV p hp (p.onV d)) d
    (sectionV_spec p hp (p.onV d)))).2 q hq

theorem sheet_deck (q : Q) (d : D.V) :
    sheet p hp a hr (a.smulV q d) = q * sheet p hp a hr d := by
  symm
  apply sheet_unique
  rw [hr.compat, a.mul_smulV, sheet_spec]

theorem sheet_fibre_injective {d e : D.V} (hf : p.onV d = p.onV e)
    (hs : sheet p hp a hr d = sheet p hp a hr e) : d = e := by
  rw [← sheet_spec p hp a hr d, ← sheet_spec p hp a hr e, hf, hs]

def liftGerm (e : K.E) : D.E × Bool := Classical.choose
  (exists_unique_liftGerm hp (sectionV p hp (K.src e))
    (eb := (e, true)) (sectionV_spec p hp (K.src e)).symm)

theorem liftGerm_spec (e : K.E) :
    germSrc D.src D.tgt (liftGerm p hp e) = sectionV p hp (K.src e) ∧
      (p.onE (liftGerm p hp e).1, (liftGerm p hp e).2) = (e, true) :=
  (Classical.choose_spec (exists_unique_liftGerm hp (sectionV p hp (K.src e))
    (eb := (e, true)) (sectionV_spec p hp (K.src e)).symm)).1

def liftEdge (e : K.E) : D.E := (liftGerm p hp e).1
theorem liftEdge_source (e : K.E) : D.src (liftEdge p hp e) = sectionV p hp (K.src e) := by
  have h := (liftGerm_spec p hp e).1
  have hb : (liftGerm p hp e).2 = true := congrArg Prod.snd (liftGerm_spec p hp e).2
  simpa only [liftEdge, germSrc, hb, if_true] using h
theorem liftEdge_projection (e : K.E) : p.onE (liftEdge p hp e) = e :=
  congrArg Prod.fst (liftGerm_spec p hp e).2

def edge (e : K.E) : Q := sheet p hp a hr (D.tgt (liftEdge p hp e))


include he in
theorem edge_projection (e : D.E) :
    edge p hp a hr (p.onE e) = (sheet p hp a hr (D.src e))⁻¹ * sheet p hp a hr (D.tgt e) := by
  have h := congrArg (fun e => sheet p hp a hr (D.tgt e)) (by
    have h := liftGerm_unique hp
      (x := (a.smulE (sheet p hp a hr (D.src e)) (liftEdge p hp (p.onE e)), true))
      (y := (e, true)) (by
        change D.src _ = D.src e
        rw [a.src_smul, liftEdge_source, p.src_onE, sheet_spec]) rfl (by
        rw [he, liftEdge_projection])
    exact congrArg Prod.fst h)
  rw [a.tgt_smul, sheet_deck] at h
  change sheet p hp a hr (D.src e) * edge p hp a hr (p.onE e) =
    sheet p hp a hr (D.tgt e) at h
  rw [← h]
  group

include he in
theorem read_projected_path {l : List (D.E × Bool)} {d e : D.V}
    (hl : IsPath D.src D.tgt l d e) :
    EdgeLabels.read (edge p hp a hr) (mapPath p l) =
      (sheet p hp a hr d)⁻¹ * sheet p hp a hr e := by
  rw [EdgeLabels.read_mapPath]
  exact EdgeLabels.read_potential _ (sheet p hp a hr) (edge_projection p hp a hr he) hl

include he in
theorem edge_rel (f : K.F) : EdgeLabels.read (edge p hp a hr) (K.att f) = 1 := by
  obtain ⟨g, ⟨hg, hb⟩, _⟩ := exists_unique_liftCell hp f
    (sectionV_spec p hp (K.base f)).symm
  have h := read_projected_path p hp a hr he (D.att_isLoop g)
  rw [mapPath_att, hg] at h
  simpa using h

end FiniteChains.Comb.RegularCoverLabels

namespace FiniteChains.Comb
universe u
variable {D K L : Complex2.{u}}

namespace RootPaths
def relative (i : Hom D L) (hi : Function.Injective i.onV)
    (hD : IsConnected D) (hL : IsConnected L) (d₀ : D.V) : RootPaths L (i.onV d₀) where
  path v := if h : ∃ d, i.onV d = v then
    mapPath i ((choose hD d₀).path h.choose) else (choose hL (i.onV d₀)).path v
  valid v := by
    split
    · rename_i h
      simpa only [h.choose_spec] using isPath_mapPath i ((choose hD d₀).valid h.choose)
    · exact (choose hL (i.onV d₀)).valid v
  at_root := by
    have h : ∃ d, i.onV d = i.onV d₀ := ⟨d₀, rfl⟩
    rw [dif_pos h, hi h.choose_spec, (choose hD d₀).at_root, mapPath_nil]

theorem relative_path (i : Hom D L) (hi : Function.Injective i.onV)
    (hD : IsConnected D) (hL : IsConnected L) (d₀ d : D.V) :
    (relative i hi hD hL d₀).path (i.onV d) = mapPath i ((choose hD d₀).path d) := by
  have h : ∃ d', i.onV d' = i.onV d := ⟨d, rfl⟩
  simp only [relative, dif_pos h, hi h.choose_spec]

theorem relative_edge_core (i : Hom D L) (hi : Function.Injective i.onV)
    (hD : IsConnected D) (hL : IsConnected L) (d₀ : D.V) (ht : Pi1Trivial i) (e : D.E) :
    (relative i hi hD hL d₀).edge (i.onE e) = 1 := by
  apply Quotient.sound
  change Htpy L (i.onV d₀) (i.onV d₀)
    ((relative i hi hD hL d₀).path (L.src (i.onE e)) ++ [(i.onE e, true)] ++
      revPath ((relative i hi hD hL d₀).path (L.tgt (i.onE e)))) []
  rw [i.src_onE, i.tgt_onE, relative_path, relative_path]
  have h := ht d₀ ((choose hD d₀).conjugate [(e, true)] (D.src e) (D.tgt e))
    ((choose hD d₀).conjugate_valid (isPath_single (e, true)))
  simpa [conjugate, mapPath, revPath, revGerm, List.map_map, Function.comp_def] using h
end RootPaths

namespace PushoutFundamental
variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hD : IsConnected D) (hL : IsConnected L)
  (d₀ : D.V) (ht : Pi1Trivial i)

def labels : (pushoutComplex p i hiV hiE).E → Pi1 L (i.onV d₀)
  | Sum.inl _ => 1
  | Sum.inr e => (RootPaths.relative i hiV hD hL d₀).edge e.val


include ht in
theorem read_pushPath (l : List (L.E × Bool)) :
    EdgeLabels.read (labels p i hiV hiE hD hL d₀)
      (l.map (fun e => (pushE p i e.1, e.2))) =
      EdgeLabels.read (RootPaths.relative i hiV hD hL d₀).edge l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      simp
      congr 1
      rcases e with ⟨e, b⟩
      cases b <;> simp [EdgeLabels.germ, (show labels p i hiV hiE hD hL d₀ (pushE p i e) =
    (RootPaths.relative i hiV hD hL d₀).edge e by
        by_cases h : ∃ d, i.onE d = e
        · obtain ⟨d, rfl⟩ := h
          rw [pushE_of_mem p hiE]
          exact (RootPaths.relative_edge_core i hiV hD hL d₀ ht d).symm
        · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
          rfl)]

include ht in
theorem labels_rel (f : (pushoutComplex p i hiV hiE).F) :
    EdgeLabels.read (labels p i hiV hiE hD hL d₀) ((pushoutComplex p i hiV hiE).att f) = 1 := by
  cases f with
  | inl f =>
      have h : ∀ l : List (K.E × Bool), EdgeLabels.read (labels p i hiV hiE hD hL d₀)
          (l.map (fun e => (Sum.inl e.1, e.2))) = 1 := by
        intro l
        induction l with
        | nil => rfl
        | cons e l ih => simp [EdgeLabels.read_cons, EdgeLabels.germ, labels, ih]
      exact h _
  | inr f =>
      change EdgeLabels.read (labels p i hiV hiE hD hL d₀)
        ((L.att f.val).map (fun e => (pushE p i e.1, e.2))) = 1
      rw [read_pushPath p i hiV hiE hD hL d₀ ht]
      exact (RootPaths.relative i hiV hD hL d₀).edge_rel f.val

/-- The actual pushout group retracts onto the group of L. -/
def retraction :
    Pi1 (pushoutComplex p i hiV hiE) ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) →*
      Pi1 L (i.onV d₀) :=
  EdgeLabels.monodromy (labels p i hiV hiE hD hL d₀)
    (labels_rel p i hiV hiE hD hL d₀ ht) _


include hD hL ht in
/-- The factor map is injective for the genuine cellular pushout. -/
theorem pi1_pushoutMap_injective : Function.Injective
    (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀)) :=
  (show Function.LeftInverse
    (retraction p i hiV hiE hiF hD hL d₀ ht)
    (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀)) by
    intro z
    induction z using Quotient.inductionOn with
    | h l =>
        change EdgeLabels.read (labels p i hiV hiE hD hL d₀)
          (l.val.map (fun e => (pushE p i e.1, e.2))) = Pi1.mk l
        rw [read_pushPath p i hiV hiE hD hL d₀ ht]
        exact (RootPaths.relative i hiV hD hL d₀).read_loop l).injective

end PushoutFundamental
end FiniteChains.Comb
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u v

namespace EdgeLabels
variable {X : Complex2.{u}} {G : Type v} [Group G]

def vertexRead (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1) (a : X.V) : UV X a → G :=
  Quotient.lift (fun p : PathFrom X a => read w p.val) (fun _ _ h => read_htpy w hw h)

@[simp] theorem vertexRead_mk (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    (a : X.V) (p : PathFrom X a) : vertexRead w hw a (UV.mk p) = read w p.val := rfl
end EdgeLabels

namespace PushoutSheets
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

def potential (v : L.V) : Q := if h : ∃ d, i.onV d = v then
  RegularCoverLabels.sheet p hp a hr h.choose else 1

include hiV in
theorem potential_core (d : D.V) : potential p hp a hr i (i.onV d) =
    RegularCoverLabels.sheet p hp a hr d := by
  have h : ∃ e, i.onV e = i.onV d := ⟨d, rfl⟩
  simp only [potential, dif_pos h, hiV h.choose_spec]

def labels : (pushoutComplex p i hiV hiE).E → Q
  | Sum.inl e => RegularCoverLabels.edge p hp a hr e
  | Sum.inr e => (potential p hp a hr i (L.src e.val))⁻¹ * potential p hp a hr i (L.tgt e.val)

include he in
theorem labels_pushE (e : L.E) : labels p hp a hr i hiV hiE (pushE p i e) =
    (potential p hp a hr i (L.src e))⁻¹ * potential p hp a hr i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE]
    rw [i.src_onE, i.tgt_onE, potential_core p hp a hr i hiV,
      potential_core p hp a hr i hiV]
    exact RegularCoverLabels.edge_projection p hp a hr he d
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include he in
theorem read_pushPath {l : List (L.E × Bool)} {v w : L.V}
    (hl : IsPath L.src L.tgt l v w) :
    EdgeLabels.read (labels p hp a hr i hiV hiE)
      (mapPath (pushoutMap p i hiV hiE hiF) l) =
      (potential p hp a hr i v)⁻¹ * potential p hp a hr i w := by
  rw [EdgeLabels.read_mapPath]
  exact EdgeLabels.read_potential _ (potential p hp a hr i)
    (labels_pushE p hp a hr he i hiV hiE) hl

include he hiF in
theorem labels_rel (f : (pushoutComplex p i hiV hiE).F) :
    EdgeLabels.read (labels p hp a hr i hiV hiE) ((pushoutComplex p i hiV hiE).att f) = 1 := by
  cases f with
  | inl f =>
      change EdgeLabels.read _ (mapPath (pushoutInl p i hiV hiE) (K.att f)) = 1
      rw [EdgeLabels.read_mapPath]
      exact RegularCoverLabels.edge_rel p hp a hr he f
  | inr f =>
      have h := read_pushPath p hp a hr he i hiV hiE hiF (L.att_isLoop f.val)
      simpa only [inv_mul_cancel, pushoutComplex, pushoutMap, mapPath, Sum.elim_inr] using h

include hiV in
/-- An old vertex is determined by its projected vertex together with its
actual deck coordinate. Off-core vertices already retain their labels. -/
theorem pushV_potential_injective {v w : L.V}
    (hv : pushV p i v = pushV p i w)
    (hs : potential p hp a hr i v = potential p hp a hr i w) : v = w := by
  by_cases hvD : ∃ d, i.onV d = v
  · obtain ⟨d, rfl⟩ := hvD
    rw [pushV_of_mem p hiV] at hv
    by_cases hwD : ∃ e, i.onV e = w
    · obtain ⟨e, rfl⟩ := hwD
      rw [pushV_of_mem p hiV] at hv
      rw [potential_core p hp a hr i hiV, potential_core p hp a hr i hiV] at hs
      exact congrArg i.onV (RegularCoverLabels.sheet_fibre_injective p hp a hr
        (Sum.inl.inj hv) hs)
    · rw [pushV_of_off p i ⟨w, fun e he => hwD ⟨e, he⟩⟩] at hv
      exact (Sum.inl_ne_inr hv).elim
  · rw [pushV_of_off p i ⟨v, fun d hd => hvD ⟨d, hd⟩⟩] at hv
    by_cases hwD : ∃ e, i.onV e = w
    · obtain ⟨e, rfl⟩ := hwD
      rw [pushV_of_mem p hiV] at hv
      exact (Sum.inr_ne_inl hv).elim
    · rw [pushV_of_off p i ⟨w, fun e he => hwD ⟨e, he⟩⟩] at hv
      exact congrArg (fun x : OffV i => x.val) (Sum.inr.inj hv)

theorem read_univLift (v₀ : L.V) (v : UV L v₀) :
    EdgeLabels.vertexRead (labels p hp a hr i hiV hiE)
      (labels_rel p hp a hr he i hiV hiE hiF) (pushV p i v₀)
      (univLiftV v₀ (pushoutMap p i hiV hiE hiF) v) =
      (potential p hp a hr i v₀)⁻¹ * potential p hp a hr i (endV v) := by
  induction v using UV.ind with
  | h l => exact read_pushPath p hp a hr he i hiV hiE hiF l.property


include hp hr he in
theorem univLift_vertices_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF)) := by
  intro v w h
  have hv := (by
    apply pushV_potential_injective p hp a hr i hiV
    · have hv := congrArg endV h
      simpa only [endV_univLiftV, pushoutMap] using hv
    · have hv := congrArg (EdgeLabels.vertexRead (labels p hp a hr i hiV hiE)
        (labels_rel p hp a hr he i hiV hiE hiF) (pushV p i (i.onV d₀))) h
      rw [read_univLift p hp a hr he i hiV hiE hiF (i.onV d₀) v,
        read_univLift p hp a hr he i hiV hiE hiF (i.onV d₀) w] at hv
      exact mul_left_cancel hv)
  obtain ⟨g, hg, _⟩ := (isRegular_univProj).simply_transitive v w hv
  change deckV g v = w at hg
  have hfix : deckV (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀) g)
      (univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF) v) =
      univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF) v := by
    rw [← univLiftV_deckV, hg, h]
  have hgone  := PushoutFundamental.pi1_pushoutMap_injective p i hiV hiE hiF hD hL d₀ ht
    ((deckV_free _ _ _ hfix).trans (map_one _).symm)
  rw [hgone, deckV_one] at hg
  exact hg

end PushoutSheets
end FiniteChains.Comb
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u v

section EmbeddedHomology
variable {D X : Complex2.{u}} (f : Hom D X)
  (hV : Function.Injective f.onV) (hE : Function.Injective f.onE)
  (hF : Function.Injective f.onF) (hD : IsAcyclic D)

include hV hE hD in
theorem embedded_one_cycle_filling (z : X.E →₀ ℤ)
    (hs : ∀ e ∉ Set.range f.onE, z e = 0) (hz : bdry1 X z = 0) :
    ∃ y : X.F →₀ ℤ, (∀ g ∉ Set.range f.onF, y g = 0) ∧ bdry2 X y = z := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_range_mapDomain_iff f.onE hE z).mpr hs
  change bdry1 X (chain1 f c) = 0 at hz
  have hc : bdry1 D c = 0 := by
    apply Finsupp.mapDomain_injective hV
    change chain0 f (bdry1 D c) = Finsupp.mapDomain f.onV 0
    rw [← bdry1_chain1, hz]
    rfl
  obtain ⟨d, hd⟩ := hD.h1 c hc
  refine ⟨chain2 f d, ?_, ?_⟩
  · intro g hg
    exact Finsupp.mapDomain_notin_range d g hg
  · rw [bdry2_chain2, hd]
    rfl

include hE hF hD in
theorem embedded_two_cycle_zero (z : X.F →₀ ℤ)
    (hs : ∀ e ∉ Set.range f.onF, z e = 0) (hz : bdry2 X z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_range_mapDomain_iff f.onF hF z).mpr hs
  change bdry2 X (chain2 f c) = 0 at hz
  have hc : bdry2 D c = 0 := by
    apply Finsupp.mapDomain_injective hE
    change chain1 f (bdry2 D c) = Finsupp.mapDomain f.onE 0
    rw [← bdry2_chain2, hz]
    rfl
  have hc0  := hD.h2 (hc.trans (map_zero _).symm)
  simp_all
end EmbeddedHomology

namespace PushoutOldCover
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

def oldMap : Hom D (pushoutComplex p i hiV hiE) := (pushoutInl p i hiV hiE).comp p


def oldLift : Hom D (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :=
  liftHom (f := oldMap p i hiV hiE) (d₀ := d₀) hconn
    (by
      change Pi1Trivial ((pushoutInl p i hiV hiE).comp p)
      rw [← pushout_comm p i hiV hiE hiF]
      exact Pi1Trivial.comp_left _ ht)

theorem oldLift_read (d : D.V) :
    EdgeLabels.vertexRead (PushoutSheets.labels p hp a hr i hiV hiE)
      (PushoutSheets.labels_rel p hp a hr he i hiV hiE hiF) (Sum.inl (p.onV d₀))
      ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) =
      (RegularCoverLabels.sheet p hp a hr d₀)⁻¹ * RegularCoverLabels.sheet p hp a hr d := by
  change EdgeLabels.read (PushoutSheets.labels p hp a hr i hiV hiE)
    (mapPath (oldMap p i hiV hiE) (cPath hconn d₀ d)) = _
  rw [oldMap, ← mapPath_comp, EdgeLabels.read_mapPath]
  exact RegularCoverLabels.read_projected_path p hp a hr he (cPath_isPath hconn d₀ d)

include hp hr he in
theorem oldLift_injective_V : Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onV := by
  intro d e h
  have hv : p.onV d = p.onV e := by
    have h' := congrArg endV h
    change endV (liftV (oldMap p i hiV hiE) hconn d₀ d) =
      endV (liftV (oldMap p i hiV hiE) hconn d₀ e) at h'
    rw [endV_liftV, endV_liftV] at h'
    exact Sum.inl.inj h'
  have hs := congrArg (EdgeLabels.vertexRead (PushoutSheets.labels p hp a hr i hiV hiE)
    (PushoutSheets.labels_rel p hp a hr he i hiV hiE hiF) (Sum.inl (p.onV d₀))) h
  rw [oldLift_read p hp a hr he i hiV hiE hiF hconn d₀ ht d,
    oldLift_read p hp a hr he i hiV hiE hiF hconn d₀ ht e] at hs
  exact RegularCoverLabels.sheet_fibre_injective p hp a hr hv (mul_left_cancel hs)



def translatedOldLift (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Hom D (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :=
  ((univDeck _ _).cellHom g).comp (oldLift p i hiV hiE hiF hconn d₀ ht)

include hp hr he in
theorem translatedOldLift_injective_E (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE := by
  intro x y h
  apply (show Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onE by
    intro e f h
    have hs  := oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.1) h)
    have hp'  := Sum.inl.inj
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.2) h)
    have hg := liftGerm_unique hp (x := (e, true)) (y := (f, true)) rfl hs.symm
      (congrArg (fun e => (e, true)) hp')
    exact congrArg Prod.fst hg)
  have h' := congrArg ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹) h
  change (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onE x)) =
    (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onE y)) at h'
  simpa only [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE] using h'

include hp hr he in
theorem translatedOldLift_injective_F (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF := by
  intro x y h
  apply (show Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onF by
    intro e f h
    have hs  := oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
      (congrArg (fun e : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.1) h)
    have hp'  := Sum.inl.inj
      (congrArg (fun e : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.2) h)
    apply hp.cell.1
    exact Subtype.ext (Prod.ext hp' hs))
  have h' := congrArg ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹) h
  change (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onF x)) =
    (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onF y)) at h'
  simpa only [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF] using h'

end PushoutOldCover
end FiniteChains.Comb
end

section
open scoped Classical
namespace FiniteChains.Comb.AcyclicCopies
universe u v
variable {D X : Complex2.{u}} {G : Type v} (φ : G → Hom D X)
  (hV : ∀ g, Function.Injective (φ g).onV)
  (hE : ∀ g, Function.Injective (φ g).onE)
  (hF : ∀ g, Function.Injective (φ g).onF)
  (hD : IsAcyclic D)
  (hmeet : ∀ g h d e, (φ g).onV d = (φ h).onV e →
    Set.range (φ g).onV = Set.range (φ h).onV ∧
    Set.range (φ g).onE = Set.range (φ h).onE ∧
    Set.range (φ g).onF = Set.range (φ h).onF)

def vertexSet (g : G) : Set X.V := Set.range (φ g).onV
def oldEdge (e : X.E) : Prop := ∃ g, e ∈ Set.range (φ g).onE
def oldFace (f : X.F) : Prop := ∃ g, f ∈ Set.range (φ g).onF

/-- A component label is the literal vertex set of its copy.  This removes
duplicate names for copies without choosing representatives. -/
def label (v : X.V) : Set X.V :=
  {w | ∃ g, v ∈ vertexSet φ g ∧ w ∈ vertexSet φ g}

include hmeet in
theorem label_on_vertex (g : G) (d : D.V) :
    label φ ((φ g).onV d) = vertexSet φ g := by
  ext w
  constructor
  · rintro ⟨h, ⟨e, he⟩, hw⟩
    have hv := (hmeet g h d e he.symm).1
    change w ∈ Set.range (φ g).onV
    rw [hv]
    exact hw
  · intro hw
    exact ⟨g, ⟨d, rfl⟩, hw⟩

include hmeet in
theorem label_on_edge (g : G) (e : D.E) :
    label φ (X.src ((φ g).onE e)) = vertexSet φ g := by
  rw [(φ g).src_onE]
  exact label_on_vertex φ hmeet g (D.src e)

include hmeet in
theorem label_on_face (g : G) (f : D.F) :
    label φ (X.base ((φ g).onF f)) = vertexSet φ g := by
  rw [(φ g).base_onF]
  exact label_on_vertex φ hmeet g (D.base f)



include hmeet in
theorem boundary1_label (e : X.E) (he : oldEdge φ e) (v : X.V)
    (hv : bdry1 X (Finsupp.single e 1) v ≠ 0) :
    label φ v = label φ (X.src e) := by
  obtain ⟨g, d, rfl⟩ := he
  by_cases ht : v = X.tgt ((φ g).onE d)
  · rw [ht, (φ g).tgt_onE, label_on_vertex φ hmeet,
      label_on_edge φ hmeet]
  · by_cases hs : v = X.src ((φ g).onE d)
    · rw [hs]
    · exfalso
      apply hv
      simp [bdry1_single, Ne.symm ht, Ne.symm hs]

include hmeet in
theorem boundary2_label (f : X.F) (hf : oldFace φ f) (e : X.E)
    (he : bdry2 X (Finsupp.single f 1) e ≠ 0) :
    label φ (X.src e) = label φ (X.base f) := by
  obtain ⟨g, d, rfl⟩ := hf
  have hm : e ∈ Set.range (φ g).onE := by
    by_contra hn
    apply he
    rw [bdry2_single, one_smul, (φ g).att_onF, pathChain_map]
    exact Finsupp.mapDomain_notin_range (pathChain (D.att d)) e hn
  obtain ⟨l, rfl⟩ := hm
  rw [label_on_edge φ hmeet, label_on_face φ hmeet]

include hmeet in
theorem boundary1_filter (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (s : Set X.V) :
    bdry1 X (c.filter (fun e => label φ (X.src e) = s)) =
      (bdry1 X c).filter (fun v => label φ v = s) :=
  supported_label_boundary (bdry1 X) (fun e => label φ (X.src e)) (label φ)
    (oldEdge φ) (boundary1_label φ hmeet) c hc s

include hmeet in
theorem boundary2_filter (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (s : Set X.V) :
    bdry2 X (c.filter (fun f => label φ (X.base f) = s)) =
      (bdry2 X c).filter (fun e => label φ (X.src e) = s) :=
  supported_label_boundary (bdry2 X) (fun f => label φ (X.base f))
    (fun e => label φ (X.src e)) (oldFace φ) (boundary2_label φ hmeet) c hc s

include hV hE hD hmeet in
/-- The support of every nonzero labelled summand lies in one actual copy. -/
theorem edge_filter_filling (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (hz : bdry1 X c = 0)
    (s : Set X.V) (hs : s ∈ c.support.image (fun e => label φ (X.src e))) :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧
      bdry2 X y = c.filter (fun e => label φ (X.src e) = s) := by
  obtain ⟨e, he, hes⟩ := Finset.mem_image.mp hs
  obtain ⟨g, d, hd⟩ := hc e he
  have hsg : s = vertexSet φ g := by
    rw [← hes, ← hd]
    exact label_on_edge φ hmeet g d
  have hsupp : ∀ e ∉ Set.range (φ g).onE,
      (c.filter (fun e => label φ (X.src e) = s)) e = 0 := by
    intro e hn
    by_cases he : c e = 0
    · simp [Finsupp.filter_apply, he]
    · have hold := hc e (Finsupp.mem_support_iff.mpr he)
      have hl : label φ (X.src e) ≠ s := by
        intro hl
        exact hn (by
          obtain ⟨h, d, rfl⟩ := hold
          have hv  :=
            (label_on_edge φ hmeet h d).symm.trans (hl.trans hsg)
          have hm : (φ h).onV (D.src d) ∈ vertexSet φ g := by
            rw [← hv]
            exact ⟨D.src d, rfl⟩
          obtain ⟨v, hvg⟩ := hm
          grind)
      simp [hl]
  have hcycle : bdry1 X (c.filter (fun e => label φ (X.src e) = s)) = 0 := by
    rw [boundary1_filter φ hmeet c hc, hz, Finsupp.filter_zero]
  obtain ⟨y, hy, hb⟩ := embedded_one_cycle_filling (φ g) (hV g) (hE g) hD _ hsupp hcycle
  refine ⟨y, ?_, hb⟩
  intro f hf
  refine ⟨g, ?_⟩
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hf) (hy f hn)

include hV hE hD hmeet in
/-- Exact H1 filling in the union. The family of copies can be arbitrary;
only the finitely many labels met by the given chain are summed. -/
theorem one_cycle_filling (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (hz : bdry1 X c = 0) :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧ bdry2 X y = c := by
  let S := c.support.image (fun e => label φ (X.src e))
  choose y hy hb using fun s : {s : Set X.V // s ∈ S} =>
    edge_filter_filling φ hV hE hD hmeet c hc hz s.1 s.2
  refine ⟨∑ s : {s : Set X.V // s ∈ S}, y s, ?_, ?_⟩
  · intro f hf
    by_contra hn
    have hz' : (∑ s : {s : Set X.V // s ∈ S}, y s) f = 0 := by
      simp
      apply Finset.sum_eq_zero
      intro s _
      by_contra hs
      exact hn (hy s f (Finsupp.mem_support_iff.mpr hs))
    exact (Finsupp.mem_support_iff.mp hf) hz'
  · rw [map_sum]
    simp_rw [hb]
    exact (Finset.sum_coe_sort S (fun s : Set X.V =>
      c.filter (fun e => label φ (X.src e) = s))).trans
        (finsupp_sum_label_filters (fun e => label φ (X.src e)) c)

include hE hF hD hmeet in
/-- H2 vanishes in the same actual union, coefficient by coefficient. -/
theorem two_cycle_zero (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (hz : bdry2 X c = 0) : c = 0 := by
  ext f
  by_cases hf : c f = 0
  · exact hf
  · obtain ⟨g, d, hd⟩ := hc f (Finsupp.mem_support_iff.mpr hf)
    let c' := c.filter (fun f => label φ (X.base f) = vertexSet φ g)
    have hsupp : ∀ f ∉ Set.range (φ g).onF, c' f = 0 := by
      intro f hn
      by_cases hf : c f = 0
      · simp [c', Finsupp.filter_apply, hf]
      · have hold := hc f (Finsupp.mem_support_iff.mpr hf)
        have hl : label φ (X.base f) ≠ vertexSet φ g :=
          fun hl => hn (by
            obtain ⟨h, d, rfl⟩ := hold
            have hv  :=
              (label_on_face φ hmeet h d).symm.trans hl
            have hm : (φ h).onV (D.base d) ∈ vertexSet φ g := by
              rw [← hv]
              exact ⟨D.base d, rfl⟩
            obtain ⟨v, hvg⟩ := hm
            grind)
        simp [c', hl]
    have hcycle : bdry2 X c' = 0 := by
      rw [show c' = c.filter (fun f => label φ (X.base f) = vertexSet φ g) from rfl,
        boundary2_filter φ hmeet c hc, hz, Finsupp.filter_zero]
    have hc' := embedded_two_cycle_zero (φ g) (hE g) (hF g) hD c' hsupp hcycle
    have hl : label φ (X.base f) = vertexSet φ g := by
      rw [← hd]
      exact label_on_face φ hmeet g d
    have hcoeff := congrArg (fun z : X.F →₀ ℤ => z f) hc'
    simpa [c', Finsupp.filter_apply, hl] using hcoeff

end FiniteChains.Comb.AcyclicCopies

namespace FiniteChains.Comb.AcyclicLiftedSubcomplex
universe u
variable {D X : Complex2.{u}} (i : Hom D X)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)
  (hX : IsConnected X)

def lift : Hom D (uCover X (i.onV d₀)) := liftHom (f := i) (d₀ := d₀) hconn ht
def copy (g : Pi1 X (i.onV d₀)) : Hom D (uCover X (i.onV d₀)) :=
  ((univDeck X (i.onV d₀)).cellHom g).comp (lift i hconn d₀ ht)

theorem projection_V (g : Pi1 X (i.onV d₀)) (d : D.V) :
    endV ((copy i hconn d₀ ht g).onV d) = i.onV d := by
  change endV (deckV g (liftV i hconn d₀ d)) = _
  rw [endV_deckV, endV_liftV]

include hiV in
theorem copy_injective_V (g : Pi1 X (i.onV d₀)) :
    Function.Injective (copy i hconn d₀ ht g).onV := by
  intro d e h
  apply hiV
  have h' := congrArg endV h
  simpa only [projection_V] using h'

include hiE in
theorem copy_injective_E (g : Pi1 X (i.onV d₀)) :
    Function.Injective (copy i hconn d₀ ht g).onE := by
  intro d e h
  exact hiE (congrArg (fun e : UE X (i.onV d₀) => e.val.2) h)

include hiV hX in
theorem copy_ranges_eq_of_meet (g h : Pi1 X (i.onV d₀)) (d e : D.V)
    (hm : (copy i hconn d₀ ht g).onV d = (copy i hconn d₀ ht h).onV e) :
    Set.range (copy i hconn d₀ ht g).onV = Set.range (copy i hconn d₀ ht h).onV ∧
    Set.range (copy i hconn d₀ ht g).onE = Set.range (copy i hconn d₀ ht h).onE ∧
    Set.range (copy i hconn d₀ ht g).onF = Set.range (copy i hconn d₀ ht h).onF := by
  have hde : d = e := by
    apply hiV
    have h' := congrArg endV hm
    simpa only [projection_V] using h'
  subst e
  have hE : ∀ e, (univProj X (i.onV d₀)).onE ((copy i hconn d₀ ht g).onE e) =
      (univProj X (i.onV d₀)).onE ((copy i hconn d₀ ht h).onE e) := fun _ => rfl
  have hF : ∀ f, (univProj X (i.onV d₀)).onF ((copy i hconn d₀ ht g).onF f) =
      (univProj X (i.onV d₀)).onF ((copy i hconn d₀ ht h).onF f) := fun _ => rfl
  have hV := lift_onV_eq (isCovering_univProj hX) hconn hE hm
  exact ⟨congrArg Set.range (funext hV),
    congrArg Set.range (funext (lift_onE_eq (isCovering_univProj
      hX) hE hV)),
    congrArg Set.range (funext (lift_onF_eq (isCovering_univProj
      hX) hF hV))⟩



include hiV hiE hconn ht hX in
theorem one_cycle_filling (hD : IsAcyclic D) (z : UE X (i.onV d₀) →₀ ℤ)
    (hs : ∀ e ∈ z.support, e.val.2 ∈ Set.range i.onE) (hz : bdry1 (uCover X (i.onV d₀)) z = 0) :
    ∃ y : UF X (i.onV d₀) →₀ ℤ,
      (∀ f ∈ y.support, f.val.2 ∈ Set.range i.onF) ∧ bdry2 (uCover X (i.onV d₀)) y = z := by
  have hs' : ∀ e ∈ z.support, AcyclicCopies.oldEdge (copy i hconn d₀ ht) e := by
    intro e he
    obtain ⟨d, hd⟩ := hs e he
    obtain ⟨g, hg⟩ := (show ∃ g, (copy i hconn d₀ ht g).onE d = e by
      have hv : endV e.val.1 = i.onV (D.src d) := by
        rw [e.property, (hd.symm), i.src_onE]
      obtain ⟨g, hg⟩ := (show ∃ g, (copy i hconn d₀ ht g).onV (D.src d) = (e.val.1) by
        have hend : endV ((lift i hconn d₀ ht).onV (D.src d)) = endV (e.val.1) := by
          rw [hv]
          exact endV_liftV hconn (D.src d)
        obtain ⟨g, hg, _⟩ := (isRegular_univProj).simply_transitive
          ((lift i hconn d₀ ht).onV (D.src d)) (e.val.1) hend
        exact ⟨g, hg⟩)
      refine ⟨g, Subtype.ext (Prod.ext ?_ (hd.symm).symm)⟩
      exact ((copy i hconn d₀ ht g).src_onE d).trans hg)
    exact ⟨g, d, hg⟩
  obtain ⟨y, hy, hb⟩ := AcyclicCopies.one_cycle_filling (copy i hconn d₀ ht)
    (copy_injective_V i hiV hconn d₀ ht) (copy_injective_E i hiE hconn d₀ ht) hD
    (copy_ranges_eq_of_meet i hiV hconn d₀ ht hX) z hs' hz
  refine ⟨y, ?_, hb⟩
  intro f hf
  obtain ⟨g, d, rfl⟩ := hy f hf
  exact ⟨d, rfl⟩

end FiniteChains.Comb.AcyclicLiftedSubcomplex
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.PushoutOldCover
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

theorem translated_projection_V
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.V) :
    endV ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d) = Sum.inl (p.onV d) := by
  erw [endV_deckV, endV_liftV]
  rfl

theorem translated_projection_F
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.F) :
    ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d).val.2 = Sum.inl (p.onF d) := rfl


include hp in
theorem old_faces_covered
    (f : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.F)
    (hf' : f.val.2 = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d = f := by
  have hv : endV f.val.1 = Sum.inl (K.base k) := by erw [f.property, hf']; rfl
  obtain ⟨g, d, hd⟩ := (show ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d = (f.val.1) by
    obtain ⟨d, hd⟩ := hp.surjV (K.base k)
    have hend : endV ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) = endV (f.val.1) := by
      erw [hv]
      erw [endV_liftV]
      exact congrArg Sum.inl hd
    obtain ⟨g, hg, _⟩ := (isRegular_univProj
     ).simply_transitive
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) (f.val.1) hend
    exact ⟨g, d, hg⟩)
  have hbase : K.base k = p.onV d := by
    have h := translated_projection_V p i hiV hiE hiF hconn d₀ ht g d
    erw [hd, hv] at h
    exact Sum.inl.inj h
  obtain ⟨l, ⟨hlp, hl⟩, _⟩ := exists_unique_liftCell hp k hbase
  refine ⟨g, l, Subtype.ext (Prod.ext ?_ ?_)⟩
  · have h := (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).base_onF l
    exact h.trans ((congrArg _ hl).trans hd)
  · erw [translated_projection_F, hf']
    exact congrArg Sum.inl hlp

include hr he hf in
/-- Overlap is an actual deck identification of D, not an arbitrary
identification of chains. -/
theorem copies_identified_of_meet
    (hEconn : IsConnected (pushoutComplex p i hiV hiE))
    (g h : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)))
    (d e : D.V)
    (hmeet : (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV e) :
    ∃ q : Q,
      (∀ v, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV v =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV (a.smulV q v)) ∧
      (∀ l, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE l =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onE (a.smulE q l)) ∧
      (∀ f, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF f =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onF (a.smulF q f)) := by
  have hpde : p.onV d = p.onV e := by
    have h' := congrArg endV hmeet
    erw [translated_projection_V, translated_projection_V] at h'
    exact Sum.inl.inj h'
  obtain ⟨q, hq, _⟩ := hr.simply_transitive d e hpde
  let F := translatedOldLift p i hiV hiE hiF hconn d₀ ht g
  let G := (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).comp (a.cellHom q)
  have hE : ∀ l, (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onE (F.onE l) =
      (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onE (G.onE l) := by
    intro l
    change Sum.inl (p.onE l) = Sum.inl (p.onE (a.smulE q l))
    erw [he]
  have hF : ∀ l, (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onF (F.onF l) =
      (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onF (G.onF l) := by
    intro l
    change Sum.inl (p.onF l) = Sum.inl (p.onF (a.smulF q l))
    rw (config := { transparency := .default }) [hf]
  have hb : F.onV d = G.onV d := by
    change _ = (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV (a.smulV q d)
    rw (config := { transparency := .default }) [hq]
    exact hmeet
  have hV := lift_onV_eq (isCovering_univProj
    hEconn) hconn hE hb
  exact ⟨q, hV, lift_onE_eq (isCovering_univProj
    hEconn) hE hV,
    lift_onF_eq (isCovering_univProj
      hEconn) hF hV⟩

end FiniteChains.Comb.PushoutOldCover
end

section
open scoped Classical
namespace FiniteChains.Comb.PushoutOldCover
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)
  (hEconn : IsConnected (pushoutComplex p i hiV hiE))

include hr he hf hEconn in
theorem copy_ranges_eq_of_meet
    (g h : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d e : D.V)
    (hmeet : (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV e) :
    Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV =
      Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV ∧
    Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE =
      Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onE ∧
    Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF =
      Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onF := by
  obtain ⟨q, hV, hE, hF⟩ :=
    copies_identified_of_meet p a hr he hf i hiV hiE hiF hconn d₀ ht hEconn g h d e hmeet
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨a.smulV q d, (hV d).symm⟩
    · rintro ⟨d, rfl⟩
      refine ⟨a.smulV q⁻¹ d, ?_⟩
      simpa only [← a.mul_smulV, mul_inv_cancel, a.one_smulV] using hV (a.smulV q⁻¹ d)
  · ext e
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨a.smulE q d, (hE d).symm⟩
    · rintro ⟨d, rfl⟩
      refine ⟨a.smulE q⁻¹ d, ?_⟩
      simpa only [← a.mul_smulE, mul_inv_cancel, a.one_smulE] using hE (a.smulE q⁻¹ d)
  · ext f
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨a.smulF q d, (hF d).symm⟩
    · rintro ⟨d, rfl⟩
      refine ⟨a.smulF q⁻¹ d, ?_⟩
      simpa only [← a.mul_smulF, mul_inv_cancel, a.one_smulF] using hF (a.smulF q⁻¹ d)

include hp hr he hf hiF hconn ht hEconn in
theorem old_two_cycle_zero (hD : IsAcyclic D)
    (z : (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).F →₀ ℤ)
    (hs : ∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k)
    (hz : bdry2 (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) z = 0) : z = 0 := by
  let φ := translatedOldLift p i hiV hiE hiF hconn d₀ ht
  have hs' : ∀ f ∈ z.support, AcyclicCopies.oldFace φ f := by
    intro f hf'
    obtain ⟨k, hk⟩ := hs f hf'
    obtain ⟨g, d, hd⟩ := old_faces_covered p hp i hiV hiE hiF hconn d₀ ht f k hk
    exact ⟨g, d, hd⟩
  exact AcyclicCopies.two_cycle_zero φ
    (translatedOldLift_injective_E p hp a hr he i hiV hiE hiF hconn d₀ ht)
    (translatedOldLift_injective_F p hp a hr he i hiV hiE hiF hconn d₀ ht)
    hD (copy_ranges_eq_of_meet p a hr he hf i hiV hiE hiF hconn d₀ ht hEconn) z hs' hz

end FiniteChains.Comb.PushoutOldCover

namespace FiniteChains.Comb.PushoutSheets
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

include hp hiV hiE in
theorem pushE_injective_at_source {e f : L.E}
    (hs : L.src e = L.src f) (hf : pushE p i e = pushE p i f) : e = f := by
  by_cases heD : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := heD
    rw [pushE_of_mem p hiE] at hf
    by_cases hfD : ∃ e, i.onE e = f
    · obtain ⟨e, rfl⟩ := hfD
      rw [pushE_of_mem p hiE] at hf
      have hsrc  := hiV (by simpa only [i.src_onE] using hs)
      have hproj  := Sum.inl.inj hf
      have hh := liftGerm_unique hp (x := (d, true)) (y := (e, true)) rfl hsrc.symm
        (congrArg (fun z => (z, true)) hproj)
      exact congrArg i.onE (congrArg Prod.fst hh)
    · rw [pushE_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact (Sum.inl_ne_inr hf).elim
  · rw [pushE_of_off p i ⟨e, fun d hd => heD ⟨d, hd⟩⟩] at hf
    by_cases hfD : ∃ d, i.onE d = f
    · obtain ⟨d, rfl⟩ := hfD
      rw [pushE_of_mem p hiE] at hf
      exact (Sum.inr_ne_inl hf).elim
    · rw [pushE_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact congrArg (fun x : OffE i => x.val) (Sum.inr.inj hf)

include hp hiV hiF in
theorem pushF_injective_at_base {e f : L.F}
    (hs : L.base e = L.base f) (hf : pushF p i e = pushF p i f) : e = f := by
  by_cases heD : ∃ d, i.onF d = e
  · obtain ⟨d, rfl⟩ := heD
    rw [pushF_of_mem p hiF] at hf
    by_cases hfD : ∃ e, i.onF e = f
    · obtain ⟨e, rfl⟩ := hfD
      rw [pushF_of_mem p hiF] at hf
      have hbase  := hiV (by simpa only [i.base_onF] using hs)
      have hproj  := Sum.inl.inj hf
      have hh  := hp.cell.1 (Subtype.ext (Prod.ext hproj hbase))
      exact congrArg i.onF hh
    · rw [pushF_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact (Sum.inl_ne_inr hf).elim
  · rw [pushF_of_off p i ⟨e, fun d hd => heD ⟨d, hd⟩⟩] at hf
    by_cases hfD : ∃ d, i.onF d = f
    · obtain ⟨d, rfl⟩ := hfD
      rw [pushF_of_mem p hiF] at hf
      exact (Sum.inr_ne_inl hf).elim
    · rw [pushF_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact congrArg (fun x : OffF i => x.val) (Sum.inr.inj hf)

include hp hr he in
theorem univLift_edges_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onE := by
  intro e f h
  have hv  :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE)
        ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => e.val.1) h)
  have hs  :=
    e.property.symm.trans ((congrArg endV hv).trans f.property)
  have hb  := pushE_injective_at_source p hp i hiV hiE hs
    (congrArg (fun e : UE (pushoutComplex p i hiV hiE)
      ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => e.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

include hp hr he in
theorem univLift_faces_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onF := by
  intro e f h
  have hv  :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (fun f : UF (pushoutComplex p i hiV hiE)
        ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => f.val.1) h)
  have hs  :=
    e.property.symm.trans ((congrArg endV hv).trans f.property)
  have hb  := pushF_injective_at_base p hp i hiV hiF hs
    (congrArg (fun f : UF (pushoutComplex p i hiV hiE)
      ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => f.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

end FiniteChains.Comb.PushoutSheets
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

/-! ### Maps out of a simply connected complex -/

/-- A cellular map out of a simply connected complex kills `π₁`. -/
theorem pi1Trivial_of_simplyConnected {X Y : Complex2.{u}} (hX : SimplyConnected X)
    (h : Hom X Y) : Pi1Trivial h := by
  intro a p hp
  simpa using mapPath_htpy h (hX a p hp)

/-! ### Lifting a cellular map to the universal covers, with a prescribed base image -/

section Lifts

variable {L E : Complex2.{u}}

/-- **Every copy of `L̃` inside `Ẽ` is available.**  Given a cellular map `ι : L → E`, a
vertex `l₀` of `L` and a vertex `c` of the universal cover of `E` lying over `ι l₀`, there is
a lift of `ι` to the universal covers taking the base vertex of `L̃(l₀)` to `c`.  (The
universal cover of `L` is simply connected, so the composite `L̃ → L → E` lifts; a change of
base vertex moves the image of the base point to `c`.) -/
theorem exists_lift_univCover (ι : Hom L E) {x₀ : E.V} (l₀ : L.V) (c : UV E x₀)
    (hc : endV c = ι.onV l₀) :
    ∃ φ : Hom (uCover L l₀) (uCover E x₀),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      φ.onV (UV.base L l₀) = c := by
  set f : Hom (uCover L l₀) E := ι.comp (univProj L l₀)
  have htriv  := pi1Trivial_of_simplyConnected simplyConnected_univCover f
  set psi : Hom (uCover L l₀) (uCover E (ι.onV l₀)) :=
    liftHom (d₀ := UV.base L l₀) isConnected_univCover htriv
  -- a path representing `c`
  obtain ⟨tp, htp⟩ := Quotient.exists_rep c
  have hend : endpt E x₀ tp.1 = ι.onV l₀ := by rw [← hc, ← htp]; rfl
  have hq : IsPath E.src E.tgt tp.1 x₀ (ι.onV l₀) := by
    have h := tp.2
    rwa [hend] at h
  refine ⟨(shiftHom hq).comp psi, ?_, ?_, ?_, ?_⟩
  · intro v
    show endV (shiftV hq (psi.onV v)) = ι.onV (endV v)
    rw [endV_shiftV]
    exact univProj_liftHom_onV (d₀ := UV.base L l₀) isConnected_univCover htriv v
  · intro e
    exact univProj_liftHom_onE (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv e
  · intro g
    show ((shiftF hq (psi.onF g)).1).2 = ι.onF (g.1.2)
    exact univProj_liftHom_onF (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv g
  · show shiftV hq (psi.onV (UV.base L l₀)) = c
    have h1 : psi.onV (UV.base L l₀) = UV.base E (ι.onV l₀) :=
      liftHom_base (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv
    rw [h1, shiftV_base, ← htp]
    exact congrArg UV.mk (Subtype.ext rfl)

/-! ### The degree-two chains coming from the copies -/

end Lifts

/-! ### Coverings are onto on cells -/



/-! ### The map `L → K ∪_p L` of Proposition 3.11 is onto on cells -/

section Pushout

variable {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

end Pushout

end Comb
end FiniteChains
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.UniversalCopy
universe u
variable {L E : Complex2.{u}} (f : Hom L E) (a : L.V)

def map (g : Pi1 E (f.onV a)) : Hom (uCover L a) (uCover E (f.onV a)) :=
  ((univDeck E (f.onV a)).cellHom g).comp (univLift L f a)

theorem projection_V (g : Pi1 E (f.onV a)) (v : UV L a) :
    endV ((map f a g).onV v) = f.onV (endV v) := by
  change endV (deckV g (univLiftV a f v)) = _
  rw [endV_deckV, endV_univLiftV]

theorem projection_E (g : Pi1 E (f.onV a)) (e : UE L a) :
    ((map f a g).onE e).val.2 = f.onE e.val.2 := rfl

theorem projection_F (g : Pi1 E (f.onV a)) (e : UF L a) :
    ((map f a g).onF e).val.2 = f.onF e.val.2 := rfl

def vertexPair (g : Pi1 E (f.onV a)) (v : UV L a) : UV E (f.onV a) × L.V :=
  ((map f a g).onV v, endV v)

def vertices (g : Pi1 E (f.onV a)) : Set (UV E (f.onV a) × L.V) :=
  Set.range (vertexPair f a g)

def label (v : UV E (f.onV a) × L.V) : Set (UV E (f.onV a) × L.V) :=
  {w | ∃ g, v ∈ vertices f a g ∧ w ∈ vertices f a g}

theorem identified_of_meet (hE : IsConnected E)
    (g h : Pi1 E (f.onV a)) (v w : UV L a)
    (hm : vertexPair f a g v = vertexPair f a h w) :
    ∃ k : Pi1 L a,
      (∀ x, (map f a g).onV x = (map f a h).onV (deckV k x)) ∧
      (∀ e, (map f a g).onE e = (map f a h).onE (deckE k e)) ∧
      (∀ t, (map f a g).onF t = (map f a h).onF (deckF k t)) := by
  have hend  := congrArg Prod.snd hm
  obtain ⟨k, hk, _⟩ := (isRegular_univProj (x₀ := a)).simply_transitive v w hend
  let F := map f a g
  let H := (map f a h).comp ((univDeck L a).cellHom k)
  have hprojE : ∀ e, (univProj E (f.onV a)).onE (F.onE e) =
      (univProj E (f.onV a)).onE (H.onE e) := fun _ => rfl
  have hprojF : ∀ t, (univProj E (f.onV a)).onF (F.onF t) =
      (univProj E (f.onV a)).onF (H.onF t) := fun _ => rfl
  have hb : F.onV v = H.onV v := by
    change (map f a g).onV v = (map f a h).onV (deckV k v)
    change deckV k v = w at hk
    rw [hk]
    exact congrArg Prod.fst hm
  have hV := lift_onV_eq (isCovering_univProj hE) isConnected_univCover hprojE hb
  exact ⟨k, hV, lift_onE_eq (isCovering_univProj hE) hprojE hV,
    lift_onF_eq (isCovering_univProj hE) hprojF hV⟩


theorem label_on_pair (hE : IsConnected E) (g : Pi1 E (f.onV a)) (v : UV L a) :
    label f a (vertexPair f a g v) = vertices f a g := by
  ext z
  constructor
  · rintro ⟨h, ⟨w, hw⟩, hz⟩
    rw [(show vertices f a g = vertices f a h by
      obtain ⟨k, hV, _, _⟩ := identified_of_meet f a hE g h v w (hw.symm)
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨deckV k x, Prod.ext (hV x).symm (endV_deckV k x)⟩
      · rintro ⟨x, rfl⟩
        refine ⟨deckV k⁻¹ x, Prod.ext ?_ (endV_deckV k⁻¹ x)⟩
        simpa only [← deckV_mul, mul_inv_cancel, deckV_one, vertexPair, map] using hV (deckV k⁻¹ x))]
    exact hz
  · intro hz
    exact ⟨g, ⟨v, rfl⟩, hz⟩

theorem vertices_nonempty (g : Pi1 E (f.onV a)) : (vertices f a g).Nonempty :=
  ⟨vertexPair f a g (UV.base L a), ⟨UV.base L a, rfl⟩⟩


theorem faces_covered (hL : IsConnected L) (t : UF E (f.onV a)) (l : L.F)
    (ht : t.val.2 = f.onF l) :
    ∃ (g : Pi1 E (f.onV a)) (x : UF L a), (map f a g).onF x = t ∧ x.val.2 = l := by
  have hv : endV t.val.1 = f.onV (L.base l) := by
    rw [t.property, ht, f.base_onF]
  obtain ⟨g, x, hx⟩ := (show ∃ g x, vertexPair f a g x = ((t.val.1), (L.base l)) by
    obtain ⟨x, hx⟩ := endV_surjective hL (L.base l)
    have hproj : endV (univLiftV a f x) = endV (t.val.1) := by
      rw [endV_univLiftV, hx, hv]
    obtain ⟨g, hg, _⟩ := (isRegular_univProj).simply_transitive _ _ hproj
    exact ⟨g, x, Prod.ext hg hx⟩)
  let t' : UF L a := ⟨(x, l), congrArg Prod.snd hx⟩
  refine ⟨g, t', ?_, rfl⟩
  apply Subtype.ext
  have hv'  :=
    congrArg (fun z : UV E (f.onV a) × L.V => z.1) hx
  exact Prod.ext hv' ht.symm

theorem face_range_of_label (hE : IsConnected E) (hL : IsConnected L)
    (g : Pi1 E (f.onV a)) (t : UF E (f.onV a)) (l : L.F)
    (ht : t.val.2 = f.onF l)
    (hl : label f a (t.val.1, L.base l) = vertices f a g) :
    t ∈ Set.range (map f a g).onF := by
  obtain ⟨h, x, hx, hxl⟩ := faces_covered f a hL t l ht
  have hp : vertexPair f a h x.val.1 = (t.val.1, L.base l) := by
    apply Prod.ext
    · exact congrArg (fun t : UF E (f.onV a) => t.val.1) hx
    · exact x.property.trans (congrArg L.base hxl)
  have hvg : vertices f a h = vertices f a g := by
    rw [← label_on_pair f a hE h x.val.1, hp]
    exact hl
  have hmem : vertexPair f a h x.val.1 ∈ vertices f a g := by
    rw [← hvg]
    exact ⟨x.val.1, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨k, _, _, hkF⟩ := identified_of_meet f a hE h g x.val.1 y hy.symm
  exact ⟨deckF k x, (hkF x).symm.trans hx⟩

theorem map_injective_E (hE : Function.Injective (univLift L f a).onE)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onE := by
  intro e t h
  apply hE
  have hh := congrArg ((univDeck E (f.onV a)).smulE g⁻¹) h
  change (univDeck E (f.onV a)).smulE g⁻¹
      ((univDeck E (f.onV a)).smulE g ((univLift L f a).onE e)) =
    (univDeck E (f.onV a)).smulE g⁻¹
      ((univDeck E (f.onV a)).smulE g ((univLift L f a).onE t)) at hh
  simpa only [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE] using hh

theorem map_injective_F (hF : Function.Injective (univLift L f a).onF)
    (g : Pi1 E (f.onV a)) : Function.Injective (map f a g).onF := by
  intro e t h
  apply hF
  have hh := congrArg ((univDeck E (f.onV a)).smulF g⁻¹) h
  change (univDeck E (f.onV a)).smulF g⁻¹
      ((univDeck E (f.onV a)).smulF g ((univLift L f a).onF e)) =
    (univDeck E (f.onV a)).smulF g⁻¹
      ((univDeck E (f.onV a)).smulF g ((univLift L f a).onF t)) at hh
  simpa only [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF] using hh

theorem cycle_image_mem (g : Pi1 E (f.onV a)) (c : UF L a →₀ ℤ)
    (hc : bdry2 (uCover L a) c = 0) : chain2 (map f a g) c ∈ Pi2FromSub f (f.onV a) :=
  ⟨a, map f a g, projection_V f a g, projection_E f a g,
    projection_F f a g, c, hc, rfl⟩

end FiniteChains.Comb.UniversalCopy

namespace FiniteChains.Comb.PushoutRelativeCopies
universe u
variable {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (a : L.V)

abbrev target := pushoutComplex p i hiV hiE
abbrev root := (pushoutMap p i hiV hiE hiF).onV a

def oldEdge (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a)) : Prop :=
  ∃ k : K.E, e.val.2 = Sum.inl k
def oldFace (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) : Prop :=
  ∃ k : K.F, t.val.2 = Sum.inl k

def edgeLabel (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V) :=
  match e.val.2 with
  | Sum.inl _ => ∅
  | Sum.inr l => UniversalCopy.label (pushoutMap p i hiV hiE hiF) a (e.val.1, L.src l.val)

def faceLabel (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V) :=
  match t.val.2 with
  | Sum.inl _ => ∅
  | Sum.inr l => UniversalCopy.label (pushoutMap p i hiV hiE hiF) a (t.val.1, L.base l.val)

theorem oldEdge_map_iff (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (e : UE L a) :
    oldEdge p i hiV hiE hiF a ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e) ↔
      e.val.2 ∈ Set.range i.onE := by
  by_cases h : ∃ d, i.onE d = e.val.2
  · obtain ⟨d, hd⟩ := h
    have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e).val.2 =
        Sum.inl (p.onE d) := by
      change pushE p i e.val.2 = _
      rw [← hd, pushE_of_mem p hiE]
    exact ⟨fun _ => ⟨d, hd⟩, fun _ => ⟨p.onE d, hp'⟩⟩
  · have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e).val.2 =
        Sum.inr ⟨e.val.2, fun d hd => h ⟨d, hd⟩⟩ := by
      exact pushE_of_off p i ⟨e.val.2, fun d hd => h ⟨d, hd⟩⟩
    constructor
    · rintro ⟨k, hk⟩
      rw [hp'] at hk
      exact (Sum.inr_ne_inl hk).elim
    · simp_all

theorem oldFace_map_iff (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (t : UF L a) :
    oldFace p i hiV hiE hiF a ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t) ↔
      t.val.2 ∈ Set.range i.onF := by
  by_cases h : ∃ d, i.onF d = t.val.2
  · obtain ⟨d, hd⟩ := h
    have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
        Sum.inl (p.onF d) := by
      change pushF p i t.val.2 = _
      rw [← hd, pushF_of_mem p hiF]
    exact ⟨fun _ => ⟨d, hd⟩, fun _ => ⟨p.onF d, hp'⟩⟩
  · have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
        Sum.inr ⟨t.val.2, fun d hd => h ⟨d, hd⟩⟩ := by
      exact pushF_of_off p i ⟨t.val.2, fun d hd => h ⟨d, hd⟩⟩
    constructor
    · rintro ⟨k, hk⟩
      rw [hp'] at hk
      exact (Sum.inr_ne_inl hk).elim
    · simp_all


theorem faceLabel_on_copy (hT : IsConnected (target p i hiV hiE))
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (t : UF L a)
    (ht : ¬ oldFace p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t)) :
    faceLabel p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t) =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  have hn  := fun d hd =>
    ht ((oldFace_map_iff p i hiV hiE hiF a g t).mpr ⟨d, hd⟩)
  have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
      Sum.inr ⟨t.val.2, hn⟩ := by
    exact pushF_of_off p i ⟨t.val.2, hn⟩
  unfold faceLabel
  rw [hp']
  change UniversalCopy.label _ a
    ((UniversalCopy.map _ a g).onV t.val.1, L.base t.val.2) = _
  rw [← t.property]
  exact UniversalCopy.label_on_pair _ a hT g t.val.1

theorem old_face_boundary_old (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : oldFace p i hiV hiE hiF a t)
    (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a))
    (he : ¬ oldEdge p i hiV hiE hiF a e) :
    bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a)) (Finsupp.single t 1) e = 0 := by
  obtain ⟨k, hk⟩ := ht
  have hb : endV t.val.1 = (pushoutInl p i hiV hiE).onV (K.base k) := by
    rw [t.property, hk]
    rfl
  obtain ⟨φ, hV, hE, hF, hbase⟩ :=
    exists_lift_univCover (pushoutInl p i hiV hiE) (K.base k) t.val.1 hb
  let k' : UF K (K.base k) := ⟨(UV.base K (K.base k), k), rfl⟩
  have hkt : φ.onF k' = t := by
    apply Subtype.ext
    apply Prod.ext
    · exact (φ.base_onF k').trans hbase
    · exact (hF k').trans hk.symm
  have hnot : e ∉ Set.range φ.onE := by
    rintro ⟨d, rfl⟩
    exact he ⟨d.val.2, hE d⟩
  have hb' := bdry2_chain2 φ (Finsupp.single k' 1)
  have hs : chain2 φ (Finsupp.single k' 1) = Finsupp.single t 1 := by
    change Finsupp.mapDomain φ.onF (Finsupp.single k' 1) = _
    rw [Finsupp.mapDomain_single, hkt]
  rw [← hs, hb']
  exact Finsupp.mapDomain_notin_range _ e hnot

def relativeBoundary :
    (UF (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ) →ₗ[ℤ]
      (UE (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ) where
  toFun c := (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a)) c).filter
    (fun e => ¬ oldEdge p i hiV hiE hiF a e)
  map_add' c d := by rw [map_add, Finsupp.filter_add]
  map_smul' n c := by rw [map_smul, Finsupp.filter_smul]; rfl

theorem relative_boundary_label (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a))
    (he : relativeBoundary p i hiV hiE hiF a (Finsupp.single t 1) e ≠ 0) :
    edgeLabel p i hiV hiE hiF a e = faceLabel p i hiV hiE hiF a t := by
  have heoff : ¬ oldEdge p i hiV hiE hiF a e := by
    intro heold
    apply he
    simp [relativeBoundary, heold]
  have hb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a))
      (Finsupp.single t 1) e ≠ 0 := by
    change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a))
      (Finsupp.single t 1)).filter (fun e => ¬ oldEdge p i hiV hiE hiF a e)) e ≠ 0 at he
    rw [Finsupp.filter_apply, if_pos heoff] at he
    exact he
  have htoff  := fun ht =>
    hb (old_face_boundary_old p i hiV hiE hiF a t ht e heoff)
  obtain ⟨l, hl⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (htoff ⟨k, hh⟩)
    | inr l => simp
  have hlf : t.val.2 = (pushoutMap p i hiV hiE hiF).onF l.val := by
    rw [hl]
    exact (pushF_of_off p i l).symm
  obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered (pushoutMap p i hiV hiE hiF) a hL t l.val hlf
  have hmem : e ∈ Set.range (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE := by
    by_contra hn
    apply hb
    rw [← hx, bdry2_single, one_smul,
      (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).att_onF, pathChain_map]
    exact Finsupp.mapDomain_notin_range _ e hn
  obtain ⟨y, hy⟩ := hmem
  have hyoff : ¬ oldEdge p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE y) := by rwa [hy]
  have hxoff : ¬ oldFace p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF x) := by rwa [hx]
  rw [← hy, (show edgeLabel p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE y) =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g by
    have hn  := fun d hd =>
      hyoff ((oldEdge_map_iff p i hiV hiE hiF a g y).mpr ⟨d, hd⟩)
    have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE y).val.2 =
        Sum.inr ⟨y.val.2, hn⟩ := by
      exact pushE_of_off p i ⟨y.val.2, hn⟩
    unfold edgeLabel
    rw [hp']
    change UniversalCopy.label _ a
      ((UniversalCopy.map _ a g).onV y.val.1, L.src y.val.2) = _
    rw [← y.property]
    exact UniversalCopy.label_on_pair _ a hT g y.val.1),
    ← hx, faceLabel_on_copy p i hiV hiE hiF a hT g x hxoff]

theorem relative_boundary_filter (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ)
    (s : Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V)) :
    relativeBoundary p i hiV hiE hiF a
      (c.filter (fun t => faceLabel p i hiV hiE hiF a t = s)) =
    (relativeBoundary p i hiV hiE hiF a c).filter
      (fun e => edgeLabel p i hiV hiE hiF a e = s) :=
  supported_label_boundary (relativeBoundary p i hiV hiE hiF a)
    (faceLabel p i hiV hiE hiF a) (edgeLabel p i hiV hiE hiF a) (fun _ => True)
    (fun t _ e => relative_boundary_label p i hiV hiE hiF a hT hL t e) c (fun _ _ => trivial) s

theorem faceLabel_empty_of_old
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : oldFace p i hiV hiE hiF a t) : faceLabel p i hiV hiE hiF a t = ∅ := by
  obtain ⟨k, hk⟩ := ht
  simp only [faceLabel, hk]

theorem faceLabel_of_not_old (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : ¬ oldFace p i hiV hiE hiF a t) :
    ∃ g, faceLabel p i hiV hiE hiF a t =
      UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  obtain ⟨l, hl⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (ht ⟨k, hh⟩)
    | inr l => simp
  have hlf  :=
    hl.trans (pushF_of_off p i l).symm
  obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered (pushoutMap p i hiV hiE hiF) a hL t l.val hlf
  refine ⟨g, ?_⟩
  rw [← hx]
  apply faceLabel_on_copy p i hiV hiE hiF a hT
  rwa [hx]

theorem faceLabel_empty_iff (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    faceLabel p i hiV hiE hiF a t = ∅ ↔ oldFace p i hiV hiE hiF a t := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF a hT hL t hn
    have hn' := UniversalCopy.vertices_nonempty (pushoutMap p i hiV hiE hiF) a g
    rw [← hg, he] at hn'
    exact Set.not_nonempty_empty hn'
  · exact faceLabel_empty_of_old p i hiV hiE hiF a t

theorem face_range_of_label (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a))
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (hl : faceLabel p i hiV hiE hiF a t =
      UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g) :
    t ∈ Set.range (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF := by
  have htoff : ¬ oldFace p i hiV hiE hiF a t := by
    intro ht
    have hh := faceLabel_empty_of_old p i hiV hiE hiF a t ht
    rw [hl] at hh
    have hn := UniversalCopy.vertices_nonempty (pushoutMap p i hiV hiE hiF) a g
    rw [hh] at hn
    exact Set.not_nonempty_empty hn
  obtain ⟨l, he⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (htoff ⟨k, hh⟩)
    | inr l => simp
  apply UniversalCopy.face_range_of_label (pushoutMap p i hiV hiE hiF) a hT hL g t l.val
  · exact he.trans (pushF_of_off p i l).symm
  · simpa only [faceLabel, he] using hl

end FiniteChains.Comb.PushoutRelativeCopies

namespace FiniteChains.Comb.PushoutRelativeCopies
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hDconn : IsConnected D) (hL : IsConnected L)
  (d₀ : D.V) (ht : Pi1Trivial i) (hD : IsAcyclic D)
  (hT : IsConnected (target p i hiV hiE))

def oldFaceChains : Submodule ℤ
    (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) where
  carrier := {c | ∀ f, ¬ oldFace p i hiV hiE hiF (i.onV d₀) f → c f = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hc hd f hf := by simp only [Finsupp.add_apply, hc f hf, hd f hf, add_zero]
  smul_mem' n c hc f hf := by simp only [Finsupp.smul_apply, hc f hf, smul_zero]

include hp hr he hf hDconn ht hD hT in
theorem oldFaceChains_cycle_zero
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : c ∈ oldFaceChains p i hiV hiE hiF d₀)
    (hz : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) : c = 0 := by
  have hzero : ∀ z : UF (target p i hiV hiE)
      (pushV p i (i.onV d₀)) →₀ ℤ,
      (∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k) →
        bdry2 (uCover (target p i hiV hiE) (pushV p i (i.onV d₀))) z = 0 → z = 0 := by
    rw [pushV_of_mem p hiV]
    exact PushoutOldCover.old_two_cycle_zero p hp a hr he hf i hiV hiE hiF
      hDconn d₀ ht hT hD
  apply hzero c _ hz
  intro f hf'
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hf') (hc f hn)


include hp hr he hf hDconn hL ht hD hT in
/-- The actual finite-support spherical generation statement at the core
base point. No `Pi2GeneratedByUpstairs` or exactness input remains. -/
theorem cycle_mem_span_at_core
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) :
    c ∈ Submodule.span ℤ
      (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀))) := by
  let label := faceLabel p i hiV hiE hiF (i.onV d₀)
  let S := c.support.image label
  let W := oldFaceChains p i hiV hiE hiF d₀
  let P : Submodule ℤ (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := Submodule.span ℤ
    (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)))
  have hpiece (s : {s // s ∈ S}) :
      ∃ z, z ∈ P ∧ bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
        c.filter (fun f => label f = s.val) - z ∈ W := by
    by_cases hs : s.val = ∅
    · refine ⟨0, P.zero_mem, map_zero _, ?_⟩
      rw [sub_zero]
      intro f hf'
      have hn : label f ≠ s.val := by
        rw [hs]
        exact fun hh => hf' ((faceLabel_empty_iff p i hiV hiE hiF (i.onV d₀) hT hL f).mp hh)
      simp [hn]
    · obtain ⟨f, hf', hfs⟩ := Finset.mem_image.mp s.property
      have hfoff : ¬ oldFace p i hiV hiE hiF (i.onV d₀) f := by
        intro hh
        exact hs (hfs.symm.trans (faceLabel_empty_of_old p i hiV hiE hiF (i.onV d₀) f hh))
      obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF (i.onV d₀) hT hL f hfoff
      obtain ⟨z, hz, hzc, hzd⟩ := (show ∃ z : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ,
      z ∈ Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)) ∧
      bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
      c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g) - z ∈
          oldFaceChains p i hiV hiE hiF d₀ by
        let φ := UniversalCopy.map (pushoutMap p i hiV hiE hiF) (i.onV d₀) g
        let φ2 : (UF L (i.onV d₀) →₀ ℤ) →ₗ[ℤ]
            (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := chain2 φ
        let s := UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g
        let d := c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f = s)
        have hφE := UniversalCopy.map_injective_E
          (pushoutMap p i hiV hiE hiF) (i.onV d₀)
          (PushoutSheets.univLift_edges_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
        have hφF : Function.Injective φ.onF := UniversalCopy.map_injective_F
          (pushoutMap p i hiV hiE hiF) (i.onV d₀)
          (PushoutSheets.univLift_faces_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
        have hd : ∀ f ∉ Set.range φ.onF, d f = 0 := by
          intro f hf'
          have hn : faceLabel p i hiV hiE hiF (i.onV d₀) f ≠ s := fun hl =>
            hf' (face_range_of_label p i hiV hiE hiF (i.onV d₀) hT hL g f hl)
          simp [d, hn]
        obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff φ.onF hφF d).mpr hd
        change UF L (i.onV d₀) →₀ ℤ at b
        have hb' : φ2 b = d := hb
        have hdr : relativeBoundary p i hiV hiE hiF (i.onV d₀) d = 0 := by
          rw [show d = c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f = s) from rfl,
            relative_boundary_filter p i hiV hiE hiF (i.onV d₀) hT hL]
          have hcr : relativeBoundary p i hiV hiE hiF (i.onV d₀) c = 0 := by
            change (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c).filter _ = 0
            rw [hc, Finsupp.filter_zero]
          rw [hcr, Finsupp.filter_zero]
        have hbs : ∀ e ∈ (Comb.bdry2 (uCover L (i.onV d₀)) b).support, e.val.2 ∈ Set.range i.onE := by
          intro e he'
          by_contra hn
          have hnot : ¬ oldEdge p i hiV hiE hiF (i.onV d₀) (φ.onE e) :=
            fun hh => hn ((oldEdge_map_iff p i hiV hiE hiF (i.onV d₀) g e).mp hh)
          have hcoeff : Comb.bdry2 (uCover L (i.onV d₀)) b e = 0 := by
            have hh := congrArg (fun z => z (φ.onE e)) hdr
            have hbd : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d =
                chain1 φ (bdry2 (uCover L (i.onV d₀)) b) := by
              exact (congrArg (bdry2 (uCover (target p i hiV hiE)
                (root p i hiV hiE hiF (i.onV d₀)))) hb'.symm).trans (bdry2_chain2 φ b)
            change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d).filter
              (fun e => ¬ oldEdge p i hiV hiE hiF (i.onV d₀) e))
              (φ.onE e) = 0 at hh
            rw [Finsupp.filter_apply, if_pos hnot, hbd] at hh
            exact (Finsupp.mapDomain_apply_of_injective hφE _ e).symm.trans hh
          exact (Finsupp.mem_support_iff.mp he') hcoeff
        obtain ⟨w, hw, hwb⟩ := AcyclicLiftedSubcomplex.one_cycle_filling i hiV hiE hDconn d₀ ht hL hD
          (bdry2 (uCover L (i.onV d₀)) b) hbs (bdry1_bdry2 (X := uCover L (i.onV d₀)) b)
        have hcycle : bdry2 (uCover L (i.onV d₀)) (b - w) = 0 := by rw [map_sub, hwb, sub_self]
        refine ⟨φ2 (b - w), UniversalCopy.cycle_image_mem
          (pushoutMap p i hiV hiE hiF) (i.onV d₀) g (b - w) hcycle, ?_, ?_⟩
        · change bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)))
            (chain2 φ (b - w)) = 0
          rw [bdry2_chain2, hcycle, map_zero]
        · have heq : d - φ2 (b - w) = φ2 w := by rw [map_sub, hb']; abel
          change d - φ2 (b - w) ∈ oldFaceChains p i hiV hiE hiF d₀
          rw [heq]
          intro f hf'
          by_contra hn
          have hm : f ∈ (Finsupp.mapDomain φ.onF w).support := Finsupp.mem_support_iff.mpr hn
          obtain ⟨t, ht', htf⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
          apply hf'
          rw [← htf]
          exact (oldFace_map_iff p i hiV hiE hiF (i.onV d₀) g t).mpr (hw t ht'))
      refine ⟨z, Submodule.subset_span hz, hzc, ?_⟩
      have hsg  :=
        hfs.symm.trans hg
      simpa only [hsg] using hzd
  choose z hz hzc hzd using hpiece
  let zsum := ∑ s : {s // s ∈ S}, z s
  have hzp : zsum ∈ P := P.sum_mem (fun s _ => hz s)
  have hzb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) zsum = 0 := by
    simp only [zsum, map_sum, hzc, Finset.sum_const_zero]
  have hdiff : c - zsum ∈ W := by
    have hh := W.sum_mem (fun s (_ : s ∈ Finset.univ) => hzd s)
    rw [Finset.sum_sub_distrib] at hh
    have hsum : (∑ s : {s // s ∈ S}, c.filter (fun f => label f = s.val)) = c := by
      exact (Finset.sum_coe_sort S (fun s => c.filter (fun f => label f = s))).trans
        (finsupp_sum_label_filters label c)
    rw [hsum] at hh
    exact hh
  have hzero : c - zsum = 0 := oldFaceChains_cycle_zero p hp a hr he hf i hiV hiE hiF
    hDconn d₀ ht hD hT _ hdiff (by rw [map_sub, hc, hzb, sub_self])
  rw [sub_eq_zero.mp hzero]
  exact hzp

end FiniteChains.Comb.PushoutRelativeCopies
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {x y : X.V} {p : List (X.E × Bool)}


theorem shiftF_reverse_cancel (hp : IsPath X.src X.tgt p x y) (f : UF X x) :
    shiftF hp (shiftF (isPath_revPath hp) f) = f :=
  Subtype.ext (Prod.ext (show shiftV hp (shiftV (isPath_revPath hp) (f.val.1)) = (f.val.1) by
    induction (f.val.1) using UV.ind with
    | h q =>
        apply Quotient.sound
        change Htpy X x (endpt X x (shiftP hp (shiftP (isPath_revPath hp) q)).val)
          (p ++ (revPath p ++ q.val)) q.val
        rw [endpt_shiftP, endpt_shiftP]
        have h := Htpy.append_congr (hp.append (isPath_revPath hp)) q.property
          (htpy_append_revPath hp) (Htpy.refl q.val)
        simpa using h) rfl)



theorem pi2Generated_changeBase {L : Complex2.{u}} (f : Hom L X)
    (hp : IsPath X.src X.tgt p x y)
    (hgen : ∀ c : UF X y →₀ ℤ, bdry2 (uCover X y) c = 0 → c ∈ Submodule.span ℤ (Pi2FromSub f y))
    (c : UF X x →₀ ℤ) (hc : bdry2 (uCover X x) c = 0) :
    c ∈ Submodule.span ℤ (Pi2FromSub f x) := by
  let d := chain2 (shiftHom (isPath_revPath hp)) c
  have hd : bdry2 (uCover X y) d = 0 := by rw [bdry2_chain2, hc, map_zero]
  have hg := hgen d hd
  have hm : chain2 (shiftHom hp) d ∈ Submodule.span ℤ (Pi2FromSub f x) := by
    have hle : Submodule.span ℤ (Pi2FromSub f y) ≤
        (Submodule.span ℤ (Pi2FromSub f x)).comap (chain2 (shiftHom hp)) := by
      apply Submodule.span_le.mpr
      intro z hz
      exact Submodule.subset_span (by
        obtain ⟨l, φ, hV, hE, hF, z, hz, rfl⟩ := hz
        refine ⟨l, (shiftHom hp).comp φ, ?_, hE, hF, z, hz, ?_⟩
        · intro v
          change endV (shiftV hp (φ.onV v)) = _
          rw [endV_shiftV, hV]
        · change Finsupp.mapDomain (shiftF hp) (Finsupp.mapDomain φ.onF z) =
            Finsupp.mapDomain ((shiftHom hp).comp φ).onF z
          rw [← Finsupp.mapDomain_comp]
          rfl)
    exact hle hg
  rw [show chain2 (shiftHom hp) d = c from (by
    change Finsupp.mapDomain (shiftF hp) (Finsupp.mapDomain (shiftF (isPath_revPath hp)) c) = c
    rw [← Finsupp.mapDomain_comp]
    have hf : shiftF hp ∘ shiftF (isPath_revPath hp) = id := funext (shiftF_reverse_cancel hp)
    rw [hf, Finsupp.mapDomain_id])] at hm
  exact hm

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u v
variable {D K : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)

include hp in
theorem isConnected_of_covering (hD : IsConnected D) : IsConnected K := by
  intro x y
  obtain ⟨d, rfl⟩ := hp.surjV x
  obtain ⟨e, rfl⟩ := hp.surjV y
  obtain ⟨l, hl⟩ := hD d e
  exact ⟨mapPath p l, isPath_mapPath p hl⟩

include hp hr he hf in
/-- Every genuine two-cycle of every universal cover of the pushout lies
in the span of actual lifted spherical classes from L. -/
theorem regularCover_cycle_mem_pi2FromSub_span
    (hDconn : IsConnected D) (hD : IsAcyclic D) (d₀ : D.V)
    {L : Complex2.{u}} (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hiF : Function.Injective i.onF) (hL : IsConnected L) (ht : Pi1Trivial i)
    (x : (pushoutComplex p i hiV hiE).V)
    (c : UF (pushoutComplex p i hiV hiE) x →₀ ℤ)
    (hc : bdry2 (uCover (pushoutComplex p i hiV hiE) x) c = 0) :
    c ∈ Submodule.span ℤ (Pi2FromSub (pushoutMap p i hiV hiE hiF) x) := by
  have hT := isConnected_pushoutComplex p i hiV hiE
    (isConnected_of_covering p hp hDconn) hL d₀
  obtain ⟨l, hl⟩ := hT x ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀))
  apply pi2Generated_changeBase (pushoutMap p i hiV hiE hiF) hl _ c hc
  exact PushoutRelativeCopies.cycle_mem_span_at_core p hp a hr he hf i hiV hiE hiF
    hDconn hL d₀ ht hD hT

end FiniteChains.Comb

section
open scoped Classical
namespace FiniteChains.Comb
universe u v

theorem pushE_eq_inr_imp {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
    (hi : Function.Injective i.onE) (e : L.E) (w : OffE i)
    (h : pushE p i e = Sum.inr w) : e = w.val := by
  by_cases he : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := he
    rw [pushE_of_mem p hi] at h
    exact (Sum.inl_ne_inr h).elim
  · rw [pushE_of_off p i ⟨e, fun d hd => he ⟨d, hd⟩⟩] at h
    exact congrArg (fun x : OffE i => x.val) (Sum.inr.inj h)

theorem pushF_eq_inr_imp {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
    (hi : Function.Injective i.onF) (e : L.F) (w : OffF i)
    (h : pushF p i e = Sum.inr w) : e = w.val := by
  by_cases he : ∃ d, i.onF d = e
  · obtain ⟨d, rfl⟩ := he
    rw [pushF_of_mem p hi] at h
    exact (Sum.inl_ne_inr h).elim
  · rw [pushF_of_off p i ⟨e, fun d hd => he ⟨d, hd⟩⟩] at h
    exact congrArg (fun x : OffF i => x.val) (Sum.inr.inj h)

section Proper
variable {D K L L' : Complex2.{u}} (p : Hom D K) (j : Hom D L) (j' : Hom D L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

end Proper

/-- Only actual map properties used in descent; no finite-cell assumptions. -/
structure RelativeCellChain (c : ℕ → Complex2.{u}) (n : ℕ) where
  inc : ∀ i, Hom (c i) (c (i + 1))
  incV : ∀ i, Function.Injective (inc i).onV
  incE : ∀ i, Function.Injective (inc i).onE
  incF : ∀ i, Function.Injective (inc i).onF
  conn : ∀ i, IsConnected (c i)
  zero : ∀ i < n, ZeroPi2 (inc i)
  pi1 : ∀ i, 1 ≤ i → i ≤ n → Pi1Trivial (inclFrom c inc i)
  proper : ∀ i < n, (¬ Function.Surjective (inc i).onE) ∨
    (¬ Function.Surjective (inc i).onF)

namespace RelativeCellChain
variable {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelativeCellChain c n)

theorem inclV (i : ℕ) : Function.Injective (inclFrom c R.inc i).onV := by
  induction i with
  | zero => exact Function.injective_id
  | succ i hi => exact (R.incV i).comp hi
theorem inclE (i : ℕ) : Function.Injective (inclFrom c R.inc i).onE := by
  induction i with
  | zero => exact Function.injective_id
  | succ i hi => exact (R.incE i).comp hi
theorem inclF (i : ℕ) : Function.Injective (inclFrom c R.inc i).onF := by
  induction i with
  | zero => exact Function.injective_id
  | succ i hi => exact (R.incF i).comp hi

variable {K : Complex2.{u}} (p : Hom (c 0) K)

def desc : ℕ → Complex2.{u}
  | 0 => K
  | i + 1 => pushoutComplex p (inclFrom c R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))

def descInc : ∀ i, Hom (R.desc p i) (R.desc p (i + 1))
  | 0 => pushoutInl p (inclFrom c R.inc 1) (R.inclV 1) (R.inclE 1)
  | i + 1 => pushoutFunctor p (inclFrom c R.inc (i + 1)) (inclFrom c R.inc (i + 2))
      (R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))
      (R.inclV (i + 2)) (R.inclE (i + 2)) (R.inclF (i + 2)) rfl

theorem descInc_injective_V : ∀ i, Function.Injective (R.descInc p i).onV
  | 0 => Sum.inl_injective
  | i + 1 => RelChainW.pushoutFunctor_injV K p _ _ _ _ _ _ _ _ rfl (R.incV (i + 1))
theorem descInc_injective_E : ∀ i, Function.Injective (R.descInc p i).onE
  | 0 => Sum.inl_injective
  | i + 1 => RelChainW.pushoutFunctor_injE K p _ _ _ _ _ _ _ _ rfl (R.incE (i + 1))
theorem descInc_injective_F : ∀ i, Function.Injective (R.descInc p i).onF
  | 0 => Sum.inl_injective
  | i + 1 => RelChainW.pushoutFunctor_injF K p _ _ _ _ _ _ _ _ rfl (R.incF (i + 1))

theorem desc_connected (hp : IsCovering p) (d₀ : (c 0).V) : ∀ i, IsConnected (R.desc p i)
  | 0 => isConnected_of_covering p hp (R.conn 0)
  | i + 1 => isConnected_pushoutComplex p (inclFrom c R.inc (i + 1))
      (R.inclV (i + 1)) (R.inclE (i + 1))
      (isConnected_of_covering p hp (R.conn 0)) (R.conn (i + 1)) d₀

theorem descInc_zeroPi2 (hp : IsCovering p) {Q : Type v} [Group Q]
    (a : DeckAction (c 0) Q) (hr : IsRegular p a)
    (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
    (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
    (hD : IsAcyclic (c 0)) (d₀ : (c 0).V) : ∀ i < n, ZeroPi2 (R.descInc p i)
  | 0, hi => zeroPi2_pushoutInl (inclFrom c R.inc 1) (R.inclV 1) (R.inclE 1) (R.inclF 1)
      hp hD (R.conn 0) (isConnected_of_covering p hp (R.conn 0)) (R.conn 1)
      (R.pi1 1 le_rfl (by omega))
  | i + 1, hi => by
      apply zeroPi2_pushoutFunctor p _ _ _ _ _ _ _ _ _ rfl
        (R.desc_connected p hp d₀ (i + 2)) (R.zero (i + 1) hi)
      intro x z hz
      exact regularCover_cycle_mem_pi2FromSub_span p hp a hr he hf (R.conn 0) hD d₀
        (inclFrom c R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))
        (R.inclF (i + 1)) (R.conn (i + 1))
        (R.pi1 (i + 1) (by omega) (by omega)) x z hz

end RelativeCellChain
end FiniteChains.Comb
end
