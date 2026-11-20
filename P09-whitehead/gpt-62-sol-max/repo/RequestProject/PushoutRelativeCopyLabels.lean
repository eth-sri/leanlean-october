module

public import RequestProject.UniversalCoverCopyLabels
public import RequestProject.SupportedLabelChains
public import RequestProject.CombPushout

@[expose] public section

/-! Outside K every lifted cell has exactly one L-cell label.  The labels
below make the relative boundary block diagonal over the actual lifted
copies of L. No cycle-generation statement is assumed. Unverified source. -/

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.PushoutRelativeCopies
universe u
/-- The maps and cellular embedding data for one pushout. -/
structure Diagram (D K L : Complex2.{u}) where
  p : Hom D K
  i : Hom D L
  injV : Function.Injective i.onV
  injE : Function.Injective i.onE
  injF : Function.Injective i.onF

namespace Diagram
variable {D K L : Complex2.{u}} (diag : Diagram D K L) (a : L.V)

abbrev target := pushoutComplex diag.p diag.i diag.injV diag.injE
abbrev toTarget := pushoutMap diag.p diag.i diag.injV diag.injE diag.injF
abbrev root := diag.toTarget.onV a
abbrev cover := uCover diag.target (diag.root a)
abbrev Edge := UE diag.target (diag.root a)
abbrev Face := UF diag.target (diag.root a)
abbrev CopyGroup := Pi1 diag.target (diag.root a)
abbrev Label := Set (UV diag.target (diag.root a) × L.V)
abbrev copyMap (g : diag.CopyGroup a) := UniversalCopy.map diag.toTarget a g
abbrev copyVertices (g : diag.CopyGroup a) := UniversalCopy.vertices diag.toTarget a g

end Diagram

variable {D K L : Complex2.{u}} (diag : Diagram D K L) (a : L.V)

def oldEdge (e : diag.Edge a) : Prop :=
  ∃ k : K.E, e.val.2 = Sum.inl k
def oldFace (t : diag.Face a) : Prop :=
  ∃ k : K.F, t.val.2 = Sum.inl k

def cellLabel {A B C : Type u} {j : A → B} (base : B → L.V)
    (v : UV diag.target (diag.root a)) (x : C ⊕ OffRange j) :
    diag.Label a :=
  x.elim (fun _ => ∅) (fun b => UniversalCopy.label diag.toTarget a (v, base b.val))

def edgeLabel (e : diag.Edge a) :=
  cellLabel diag a L.src e.val.1 e.val.2

def faceLabel (t : diag.Face a) :=
  cellLabel diag a L.base t.val.1 t.val.2

theorem oldEdge_map_iff (g : diag.CopyGroup a) (e : UE L a) :
    oldEdge diag a ((diag.copyMap a g).onE e) ↔
      e.val.2 ∈ Set.range diag.i.onE :=
  glueCell_inl_iff diag.p.onE diag.injE e.val.2

theorem oldFace_map_iff (g : diag.CopyGroup a) (t : UF L a) :
    oldFace diag a ((diag.copyMap a g).onF t) ↔
      t.val.2 ∈ Set.range diag.i.onF :=
  glueCell_inl_iff diag.p.onF diag.injF t.val.2

private theorem cellLabel_on_copy {A B C : Type u} {j : A → B} (hI : Function.Injective j)
    (p' : A → C) (base : B → L.V) (hT : IsConnected diag.target)
    (g : diag.CopyGroup a) (v : UV L a) (x : B)
    (hv : endV v = base x) (hoff : ¬ ∃ k, glueCell p' j x = Sum.inl k) :
    cellLabel diag a base ((diag.copyMap a g).onV v)
      (glueCell p' j x) = diag.copyVertices a g := by
  have hx := (glueCell_inl_iff p' hI x).not.mp hoff
  rw [glueCell_of_off p' ⟨x, fun y hy => hx ⟨y, hy⟩⟩]
  change UniversalCopy.label _ a ((UniversalCopy.map _ a g).onV v, base x) = _
  rw [← hv]
  exact UniversalCopy.label_on_pair _ a hT g v

theorem edgeLabel_on_copy (hT : IsConnected diag.target)
    (g : diag.CopyGroup a) (e : UE L a)
    (he : ¬ oldEdge diag a
      ((diag.copyMap a g).onE e)) :
    edgeLabel diag a
      ((diag.copyMap a g).onE e) =
        diag.copyVertices a g := by
  exact cellLabel_on_copy diag a diag.injE diag.p.onE L.src hT g _ _ e.property he

theorem faceLabel_on_copy (hT : IsConnected diag.target)
    (g : diag.CopyGroup a) (t : UF L a)
    (ht : ¬ oldFace diag a
      ((diag.copyMap a g).onF t)) :
    faceLabel diag a
      ((diag.copyMap a g).onF t) =
        diag.copyVertices a g := by
  exact cellLabel_on_copy diag a diag.injF diag.p.onF L.base hT g _ _ t.property ht

theorem old_face_boundary_old (t : diag.Face a)
    (ht : oldFace diag a t)
    (e : diag.Edge a)
    (he : ¬ oldEdge diag a e) :
    bdry2 (diag.cover a) (Finsupp.single t 1) e = 0 := by
  obtain ⟨k, hk⟩ := ht
  rw [bdry2_single, one_smul]
  apply pathChain_apply_zero_of_edge_absent
  intro d hd rfl
  let π := univProj diag.target (diag.root a)
  have hd' : (d.1.val.2, d.2) ∈ mapPath π ((uCover _ _).att t) := List.mem_map.mpr ⟨d, hd, rfl⟩
  have hp : mapPath π ((diag.cover a).att t) = diag.target.att t.val.2 :=
    (π.att_onF t).symm
  rw [hp, hk] at hd'
  obtain ⟨b, _, h⟩ := List.mem_map.mp hd'
  exact he ⟨b.1, (congrArg Prod.fst h).symm⟩

private theorem offFace_exists_copy (hL : IsConnected L)
    (t : diag.Face a)
    (ht : ¬ oldFace diag a t) :
    ∃ g x, (diag.copyMap a g).onF x = t := by
  cases h : t.val.2 with
  | inl k => exact (ht ⟨k, h⟩).elim
  | inr l =>
    obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered diag.toTarget a hL t
      l.val (h.trans (pushF_of_off diag.p diag.i l).symm)
    exact ⟨g, x, hx⟩

def relativeBoundary :
    (diag.Face a →₀ ℤ) →ₗ[ℤ]
      (diag.Edge a →₀ ℤ) where
  toFun c := (bdry2 (diag.cover a) c).filter
    (fun e => ¬ oldEdge diag a e)
  map_add' c d := by simp
  map_smul' n c := by rw [map_smul, Finsupp.filter_smul]; rfl

theorem relative_boundary_label (hT : IsConnected diag.target) (hL : IsConnected L)
    (t : diag.Face a)
    (e : diag.Edge a)
    (he : relativeBoundary diag a (Finsupp.single t 1) e ≠ 0) :
    edgeLabel diag a e = faceLabel diag a t := by
  have heoff : ¬ oldEdge diag a e := fun h => he (by simp [relativeBoundary, h])
  have hb : bdry2 (diag.cover a) (Finsupp.single t 1) e ≠ 0 := by
    change ((bdry2 (diag.cover a) (Finsupp.single t 1)).filter _) e ≠ 0 at he
    rwa [Finsupp.filter_apply, ite_eq_left heoff] at he
  have ht := fun h => hb (old_face_boundary_old diag a t h e heoff)
  obtain ⟨g, x, rfl⟩ := offFace_exists_copy diag a hL t ht
  have hmem : e ∈ Set.range (diag.copyMap a g).onE := by
    by_contra hn
    exact hb (bdry2_single_image_zero (diag.copyMap a g) x e hn)
  obtain ⟨y, rfl⟩ := hmem
  rw [edgeLabel_on_copy diag a hT g y heoff,
    faceLabel_on_copy diag a hT g x ht]

theorem relative_boundary_filter (hT : IsConnected diag.target) (hL : IsConnected L)
    (c : diag.Face a →₀ ℤ)
    (s : diag.Label a) :
    relativeBoundary diag a
      (c.filter (fun t => faceLabel diag a t = s)) =
    (relativeBoundary diag a c).filter
      (fun e => edgeLabel diag a e = s) :=
  supported_label_boundary (relativeBoundary diag a)
    (faceLabel diag a) (edgeLabel diag a) (fun _ => True)
    (fun t _ e => relative_boundary_label diag a hT hL t e) c (fun _ _ => trivial) s

theorem faceLabel_empty_of_old
    (t : diag.Face a)
    (ht : oldFace diag a t) : faceLabel diag a t = ∅ := by
  obtain ⟨k, hk⟩ := ht
  simp only [faceLabel, cellLabel, hk, Sum.elim_inl]

theorem faceLabel_of_not_old (hT : IsConnected diag.target) (hL : IsConnected L)
    (t : diag.Face a)
    (ht : ¬ oldFace diag a t) :
    ∃ g, faceLabel diag a t =
      diag.copyVertices a g := by
  obtain ⟨g, x, rfl⟩ := offFace_exists_copy diag a hL t ht
  exact ⟨g, faceLabel_on_copy diag a hT g x ht⟩

theorem faceLabel_empty_iff (hT : IsConnected diag.target) (hL : IsConnected L)
    (t : diag.Face a) :
    faceLabel diag a t = ∅ ↔ oldFace diag a t := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨g, hg⟩ := faceLabel_of_not_old diag a hT hL t hn
    have hn' := UniversalCopy.vertices_nonempty diag.toTarget a g
    simp_all
  · exact faceLabel_empty_of_old diag a t

theorem face_range_of_label (hT : IsConnected diag.target) (hL : IsConnected L)
    (g : diag.CopyGroup a)
    (t : diag.Face a)
    (hl : faceLabel diag a t =
      diag.copyVertices a g) :
    t ∈ Set.range (diag.copyMap a g).onF := by
  have htoff : ¬ oldFace diag a t := by
    intro ht
    have hh := faceLabel_empty_of_old diag a t ht
    rw [hl] at hh
    have hn := UniversalCopy.vertices_nonempty diag.toTarget a g
    simp_all
  obtain ⟨l, he⟩ : ∃ l : OffF diag.i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => tauto
    | inr l => tauto
  apply UniversalCopy.face_range_of_label diag.toTarget a hT hL g t l.val
  · exact he.trans (pushF_of_off diag.p diag.i l).symm
  · simpa only [faceLabel, cellLabel, he, Sum.elim_inr] using hl

end FiniteChains.Comb.PushoutRelativeCopies
