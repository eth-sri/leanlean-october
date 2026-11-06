module

public import RequestProject.UniversalCoverCopyLabels
public import RequestProject.SupportedLabelChains
public import RequestProject.CombPushout

@[expose] public section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

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
    exact ⟨fun _ => ⟨d, hd⟩, fun _ => ⟨p.onE d, by change pushE p i e.val.2 = _; rw [← hd, pushE_of_mem p hiE]⟩⟩
  · refine ⟨fun ⟨k, hk⟩ => ?_, fun he => False.elim (h he)⟩
    rw [show ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e).val.2 =
      Sum.inr (⟨e.val.2, fun d hd => h ⟨d, hd⟩⟩ : OffE i) from
        pushE_of_off p i ⟨e.val.2, fun d hd => h ⟨d, hd⟩⟩] at hk
    exact (Sum.inr_ne_inl hk).elim

theorem oldFace_map_iff (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (t : UF L a) :
    oldFace p i hiV hiE hiF a ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t) ↔
      t.val.2 ∈ Set.range i.onF := by
  by_cases h : ∃ d, i.onF d = t.val.2
  · obtain ⟨d, hd⟩ := h
    exact ⟨fun _ => ⟨d, hd⟩, fun _ => ⟨p.onF d, by change pushF p i t.val.2 = _; rw [← hd, pushF_of_mem p hiF]⟩⟩
  · refine ⟨fun ⟨k, hk⟩ => ?_, fun ht => False.elim (h ht)⟩
    rw [show ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
      Sum.inr (⟨t.val.2, fun d hd => h ⟨d, hd⟩⟩ : OffF i) from
        pushF_of_off p i ⟨t.val.2, fun d hd => h ⟨d, hd⟩⟩] at hk
    exact (Sum.inr_ne_inl hk).elim

theorem faceLabel_on_copy (hT : IsConnected (target p i hiV hiE))
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (t : UF L a)
    (ht : ¬ oldFace p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t)) :
    faceLabel p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t) =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  have hn : ∀ d, i.onF d ≠ t.val.2 := fun d hd =>
    ht ((oldFace_map_iff p i hiV hiE hiF a g t).mpr ⟨d, hd⟩)
  unfold faceLabel
  rw [show ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
    Sum.inr (⟨t.val.2, hn⟩ : OffF i) from pushF_of_off p i ⟨t.val.2, hn⟩]
  change UniversalCopy.label _ a ((UniversalCopy.map _ a g).onV t.val.1, L.base t.val.2) = _
  rw [← t.property]
  exact UniversalCopy.label_on_pair _ a hT g t.val.1

def relativeBoundary :
    (UF (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ) →ₗ[ℤ]
      (UE (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ) where
  toFun c := (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a)) c).filter
    (fun e => ¬ oldEdge p i hiV hiE hiF a e)
  map_add' c d := by rw [map_add, Finsupp.filter_add]
  map_smul' n c := by rw [map_smul, Finsupp.filter_smul]; rfl

theorem relative_boundary_filter (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ)
    (s : Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V)) :
    relativeBoundary p i hiV hiE hiF a
      (c.filter (fun t => faceLabel p i hiV hiE hiF a t = s)) =
    (relativeBoundary p i hiV hiE hiF a c).filter
      (fun e => edgeLabel p i hiV hiE hiF a e = s) := by
  refine supported_label_boundary (relativeBoundary p i hiV hiE hiF a)
    (faceLabel p i hiV hiE hiF a) (edgeLabel p i hiV hiE hiF a) (fun _ => True)
    (fun t _ e he => ?_) c (fun _ _ => trivial) s
  have heoff : ¬ oldEdge p i hiV hiE hiF a e := fun heold => he (by simp [relativeBoundary, heold])
  have hb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a))
      (Finsupp.single t 1) e ≠ 0 := by
    change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a))
      (Finsupp.single t 1)).filter (fun e => ¬ oldEdge p i hiV hiE hiF a e)) e ≠ 0 at he
    rwa [Finsupp.filter_apply, if_pos heoff] at he
  have htoff : ¬ oldFace p i hiV hiE hiF a t := fun ⟨k, hk⟩ => hb <| by
    obtain ⟨φ, hV, hE, hF, hbase⟩ := exists_lift_univCover (pushoutInl p i hiV hiE)
      (K.base k) t.val.1 (by rw [t.property, hk]; rfl)
    let k' : UF K (K.base k) := ⟨(UV.base K (K.base k), k), rfl⟩
    have hs : chain2 φ (Finsupp.single k' 1) = Finsupp.single t 1 := by
      change Finsupp.mapDomain φ.onF (Finsupp.single k' 1) = _
      rw [Finsupp.mapDomain_single, Subtype.ext (Prod.ext ((φ.base_onF k').trans hbase) ((hF k').trans hk.symm))]
    rw [← hs, bdry2_chain2]
    exact Finsupp.mapDomain_notin_range _ e fun ⟨d, hd⟩ => heoff ⟨d.val.2, hd ▸ hE d⟩
  obtain ⟨l, hl⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (htoff ⟨k, hh⟩)
    | inr l => exact ⟨l, rfl⟩
  obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered (pushoutMap p i hiV hiE hiF) a hL t l.val
    (hl.trans (pushF_of_off p i l).symm)
  obtain ⟨y, hy⟩ : e ∈ Set.range (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE := by
    by_contra hn; apply hb
    rw [← hx, bdry2_single, one_smul, (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).att_onF, pathChain_map]
    exact Finsupp.mapDomain_notin_range _ e hn
  have hyoff : ¬ oldEdge p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE y) := hy ▸ heoff
  have hn : ∀ d, i.onE d ≠ y.val.2 := fun d hd =>
    hyoff ((oldEdge_map_iff p i hiV hiE hiF a g y).mpr ⟨d, hd⟩)
  rw [← hy, ← hx, faceLabel_on_copy p i hiV hiE hiF a hT g x (hx ▸ htoff)]
  unfold edgeLabel
  rw [show ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE y).val.2 =
    Sum.inr (⟨y.val.2, hn⟩ : OffE i) from pushE_of_off p i ⟨y.val.2, hn⟩]
  change UniversalCopy.label _ a ((UniversalCopy.map _ a g).onV y.val.1, L.src y.val.2) = _
  rw [← y.property]
  exact UniversalCopy.label_on_pair _ a hT g y.val.1

theorem faceLabel_empty_of_old
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : oldFace p i hiV hiE hiF a t) : faceLabel p i hiV hiE hiF a t = ∅ := by
  obtain ⟨k, hk⟩ := ht; simp only [faceLabel, hk]

theorem faceLabel_of_not_old (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : ¬ oldFace p i hiV hiE hiF a t) :
    ∃ g, faceLabel p i hiV hiE hiF a t =
      UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  obtain ⟨l, hl⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (ht ⟨k, hh⟩)
    | inr l => exact ⟨l, rfl⟩
  obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered (pushoutMap p i hiV hiE hiF) a hL t l.val
    (hl.trans (pushF_of_off p i l).symm)
  exact ⟨g, hx ▸ faceLabel_on_copy p i hiV hiE hiF a hT g x (hx ▸ ht)⟩

theorem faceLabel_empty_iff (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    faceLabel p i hiV hiE hiF a t = ∅ ↔ oldFace p i hiV hiE hiF a t := by
  refine ⟨fun he => ?_, faceLabel_empty_of_old p i hiV hiE hiF a t⟩
  by_contra hn
  obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF a hT hL t hn
  exact Set.not_nonempty_empty (he ▸ hg ▸ UniversalCopy.vertices_nonempty (pushoutMap p i hiV hiE hiF) a g)

theorem face_range_of_label (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a))
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (hl : faceLabel p i hiV hiE hiF a t =
      UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g) :
    t ∈ Set.range (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF := by
  have htoff : ¬ oldFace p i hiV hiE hiF a t := fun ht =>
    Set.not_nonempty_empty (faceLabel_empty_of_old p i hiV hiE hiF a t ht ▸
      hl ▸ UniversalCopy.vertices_nonempty (pushoutMap p i hiV hiE hiF) a g)
  obtain ⟨l, he⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (htoff ⟨k, hh⟩)
    | inr l => exact ⟨l, rfl⟩
  exact UniversalCopy.face_range_of_label (pushoutMap p i hiV hiE hiF) a hT hL g t l.val
    (he.trans (pushF_of_off p i l).symm) (by simpa only [faceLabel, he] using hl)
