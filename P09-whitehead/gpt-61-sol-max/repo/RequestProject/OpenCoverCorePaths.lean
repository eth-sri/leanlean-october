import Mathlib.Tactic

import RequestProject.OpenCoverPathReplacement

/-! Paths can be moved into an open core when its complementary charts are
disjoint simply connected sets with path-connected intersections with the
core. This is the concrete open-cover step for removing two-cell centers.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval


namespace FiniteChains.PathReplacement

variable {X ι : Type} [TopologicalSpace X]

theorem range_trans_subset {x y z : X} (p : Path x y) (q : Path y z) {A : Set X}
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A) : Set.range (p.trans q) ⊆ A := by
  grind

theorem range_symm_subset {x y : X} (p : Path x y) {A : Set X}
    (hp : Set.range p ⊆ A) : Set.range p.symm ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact hp ⟨_, rfl⟩

theorem homotopic_of_within_simplyConnected (U : Set X) (hU : IsSimplyConnected U)
    {x y : X} (p q : Path x y) (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    Path.Homotopic p q := by
  letI : SimplyConnectedSpace U := hU
  have hx := hp p.source_mem_range
  have hy := hp p.target_mem_range
  let lift (r : Path x y) (hr : Set.range r ⊆ U) : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ := {
    toFun := fun t => ⟨r t, hr ⟨t, rfl⟩⟩
    continuous_toFun := r.continuous.subtype_mk _
    source' := Subtype.ext r.source
    target' := Subtype.ext r.target }
  exact (SimplyConnectedSpace.paths_homotopic (lift p hp) (lift q hq)).map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))

variable (A : Set X) (U : ι → Set X)
  (hcover : A ∪ ⋃ i, U i = Set.univ)
  (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
  (hpath : ∀ i, IsPathConnected (A ∩ U i))
  (hsc : ∀ i, IsSimplyConnected (U i))

variable {x : X}
include hcover in
omit [TopologicalSpace X] in
abbrev exists_chart  (hx : x ∉ A)  :=
  have h := Eq.mpr (id (congrArg (fun (_a : Set X) => x ∈ _a) hcover)) True.intro;
  Set.mem_iUnion.mp (Or.resolve_left h hx)

def corePoint (x : X)  :=
  if hx : x ∈ A then x
  else Classical.choose (hpath (Classical.choose (exists_chart A U hcover hx))).nonempty

theorem corePoint_mem (x : X) : corePoint A U hcover hpath x ∈ A := by
  grind [corePoint]

variable (hx : x ∈ A)
include hx in
theorem corePoint_eq   : corePoint A U hcover hpath x = x :=
  dif_pos hx

include hsc in
theorem point_joined_corePoint  (hx : x ∉ A) :
    JoinedIn (U (Classical.choose (exists_chart A U hcover hx))) x
      (corePoint A U hcover hpath x) := by
  let i := Classical.choose (exists_chart A U hcover hx)
  have hi : x ∈ U i := by grind
  have ha : corePoint A U hcover hpath x ∈ U i := by
    grind [corePoint]
  exact (hsc i).isPathConnected.joinedIn _ hi _ ha

def coreConnector (x : X)  :=
  if hx : x ∈ A then (Path.refl x).cast rfl (corePoint_eq A U hcover hpath hx)
  else (point_joined_corePoint A U hcover hpath hsc hx).somePath

include hx in
theorem coreConnector_cast   :
    (coreConnector A U hcover hpath hsc x).cast rfl
      (corePoint_eq A U hcover hpath hx).symm = Path.refl x := by aesop (add simp [coreConnector])

include hx in
theorem coreConnector_range_of_mem   :
    Set.range (coreConnector A U hcover hpath hsc x) ⊆ A := by
  simp_all [coreConnector]

include hdisj in
theorem coreConnector_range_chart (i : ι) {x : X} (hx : x ∈ U i) :
    Set.range (coreConnector A U hcover hpath hsc x) ⊆ U i := by
  by_cases hxA : x ∈ A
  · simp_all [coreConnector]
  · let k := Classical.choose (exists_chart A U hcover hxA)
    have hk  := Classical.choose_spec (exists_chart A U hcover hxA)
    have hki : k = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) hk hx
    rintro _ ⟨t, rfl⟩
    aesop (add simp [coreConnector])

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
    simpa only [Set.iUnion_option, V] using hcover.ge
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
        · aesop (add simp [range_trans_subset])
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
