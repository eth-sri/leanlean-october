module

public import RequestProject.OpenCoverPathReplacement

@[expose] public section

noncomputable section
open scoped Classical unitInterval
open Set

namespace FiniteChains.PathReplacement

variable {X ι : Type} [TopologicalSpace X]

theorem range_trans_subset {x y z : X} (p : Path x y) (q : Path y z) {A : Set X}
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A) : Set.range (p.trans q) ⊆ A := by
  rw [Path.trans_range]; exact Set.union_subset hp hq

theorem range_symm_subset {x y : X} (p : Path x y) {A : Set X}
    (hp : Set.range p ⊆ A) : Set.range p.symm ⊆ A := by
  rintro _ ⟨_, rfl⟩; exact hp ⟨_, rfl⟩

theorem homotopic_of_within_simplyConnected (U : Set X) (hU : IsSimplyConnected U)
    {x y : X} (p q : Path x y) (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    Path.Homotopic p q := by
  let _ : SimplyConnectedSpace U := hU
  let P : Path (⟨x, hp p.source_mem_range⟩ : U) ⟨y, hp p.target_mem_range⟩ :=
    { toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let Q : Path (⟨x, hp p.source_mem_range⟩ : U) ⟨y, hp p.target_mem_range⟩ :=
    { toFun := fun t => ⟨q t, hq ⟨t, rfl⟩⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  exact (SimplyConnectedSpace.paths_homotopic P Q).map ⟨Subtype.val, continuous_subtype_val⟩

variable (A : Set X) (U : ι → Set X)
  (hcover : A ∪ ⋃ i, U i = Set.univ)
  (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
  (hpath : ∀ i, IsPathConnected (A ∩ U i))
  (hsc : ∀ i, IsSimplyConnected (U i))

include hcover in
omit [TopologicalSpace X] in
theorem exists_chart {x : X} (hx : x ∉ A) : ∃ i, x ∈ U i :=
  Set.mem_iUnion.mp ((by rw [hcover]; trivial : x ∈ A ∪ ⋃ i, U i).resolve_left hx)

def corePoint (x : X) : X :=
  if hx : x ∈ A then x
  else Classical.choose (hpath (Classical.choose (exists_chart A U hcover hx))).nonempty

theorem corePoint_mem (x : X) : corePoint A U hcover hpath x ∈ A := by
  by_cases hx : x ∈ A
  · simpa only [corePoint, dif_pos hx] using hx
  · simpa only [corePoint, dif_neg hx] using (Classical.choose_spec
      (hpath (Classical.choose (exists_chart A U hcover hx))).nonempty).1

include hsc in
theorem point_joined_corePoint {x : X} (hx : x ∉ A) :
    JoinedIn (U (Classical.choose (exists_chart A U hcover hx))) x
      (corePoint A U hcover hpath x) :=
  (hsc _).isPathConnected.joinedIn _ (Classical.choose_spec (exists_chart A U hcover hx)) _
    (by simpa only [corePoint, dif_neg hx] using (Classical.choose_spec (hpath _).nonempty).2)

def coreConnector (x : X) : Path x (corePoint A U hcover hpath x) :=
  if hx : x ∈ A then (Path.refl x).cast rfl (show corePoint A U hcover hpath x = x from dif_pos hx)
  else (point_joined_corePoint A U hcover hpath hsc hx).somePath

include hcover hdisj hpath hsc in
theorem path_into_core (hA : IsOpen A) (hU : ∀ i, IsOpen (U i))
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) (p : Path x y) :
    ∃ q : Path x y, Set.range q ⊆ A ∧ Path.Homotopic p q := by
  let V : Option ι → Set X | none => A | some i => U i
  have hlocal : ∀ i {b c : X} (v : Path b c), Set.range v ⊆ V i →
      ∃ w : Path (corePoint A U hcover hpath b) (corePoint A U hcover hpath c),
        Set.range w ⊆ A ∧ Path.Homotopic
          (((coreConnector A U hcover hpath hsc b).symm.trans v).trans
            (coreConnector A U hcover hpath hsc c)) w := by
    rintro (_ | i) b c v hv
    · have hmem {z : X} (hz : z ∈ A) : Set.range (coreConnector A U hcover hpath hsc z) ⊆ A := by
        rintro _ ⟨t, rfl⟩; simpa only [coreConnector, dif_pos hz, Path.cast_coe, Path.refl_apply] using hz
      exact ⟨_, range_trans_subset _ _ (range_trans_subset _ _
        (range_symm_subset _ (hmem (hv v.source_mem_range))) hv) (hmem (hv v.target_mem_range)),
        Path.Homotopic.refl _⟩
    · have hchart {z : X} (hz : z ∈ U i) : Set.range (coreConnector A U hcover hpath hsc z) ⊆ U i := by
        by_cases hzA : z ∈ A
        · rintro _ ⟨t, rfl⟩; simpa only [coreConnector, dif_pos hzA, Path.cast_coe, Path.refl_apply] using hz
        · have hki : Classical.choose (exists_chart A U hcover hzA) = i := by
            by_contra hne
            exact Set.disjoint_left.mp (hdisj hne) (Classical.choose_spec (exists_chart A U hcover hzA)) hz
          rintro _ ⟨t, rfl⟩; rw [coreConnector, dif_neg hzA]
          simpa only [← hki] using (point_joined_corePoint A U hcover hpath hsc hzA).somePath_mem t
      have hb := hchart (hv v.source_mem_range)
      have hc := hchart (hv v.target_mem_range)
      let hw := (hpath i).joinedIn _ ⟨corePoint_mem A U hcover hpath b, hb (coreConnector A U hcover hpath hsc b).target_mem_range⟩
        _ ⟨corePoint_mem A U hcover hpath c, hc (coreConnector A U hcover hpath hsc c).target_mem_range⟩
      exact ⟨hw.somePath, by rintro _ ⟨t, rfl⟩; exact (hw.somePath_mem t).1,
        homotopic_of_within_simplyConnected (U i) (hsc i) _ _
          (range_trans_subset _ _ (range_trans_subset _ _ (range_symm_subset _ hb) hv) hc)
          (by rintro _ ⟨t, rfl⟩; exact (hw.somePath_mem t).2)⟩
  obtain ⟨q, hqA, hq⟩ := replace_of_open_cover V (by rintro (_ | i); exacts [hA, hU i])
    (fun z _ => by
      rcases (by rw [hcover]; trivial : z ∈ A ∪ ⋃ i, U i) with hz | hz
      · exact Set.mem_iUnion.mpr ⟨none, hz⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz; exact Set.mem_iUnion.mpr ⟨some i, hi⟩)
    A (corePoint A U hcover hpath) (corePoint_mem A U hcover hpath)
    (coreConnector A U hcover hpath hsc) hlocal p
  have hcast {z : X} (hz : z ∈ A) :
      (coreConnector A U hcover hpath hsc z).cast rfl (show corePoint A U hcover hpath z = z from dif_pos hz).symm =
        Path.refl z := Path.ext (funext fun t => by simp [coreConnector, dif_pos hz])
  let hx' : corePoint A U hcover hpath x = x := dif_pos hx
  let hy' : corePoint A U hcover hpath y = y := dif_pos hy
  have h := hq.pathCast hx'.symm hy'.symm
  rw [Path.cast_trans _ _ hx'.symm rfl hy'.symm, Path.cast_trans _ _ hx'.symm rfl rfl,
    Path.cast_symm, hcast hx, hcast hy, Path.cast_rfl_rfl] at h
  exact ⟨q.cast hx'.symm hy'.symm, hqA,
    ((Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans p)).symm.trans h⟩

end FiniteChains.PathReplacement
