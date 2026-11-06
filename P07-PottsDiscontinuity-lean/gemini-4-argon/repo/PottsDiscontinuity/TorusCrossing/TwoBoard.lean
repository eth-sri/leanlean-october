module

public import PottsDiscontinuity.TorusCrossing.ExploreLocal

/-!
# Two explorations in the two ends of a board

A board `Q` contains a bottom sub-board `B` (height `bB`) and a top sub-board `T` (height `bT`),
with at least one row of gap.  From the bottom of `B` and from the top of `T` we explore the
dual cluster of the port row; the explored regions are vertex-disjoint.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

/-- Bottom sub-board of height `bB`. -/
def botB (Q : Rect) (bB : ℕ) : Rect := ⟨Q.x0, Q.y0, Q.w, bB⟩

/-- Top sub-board of height `bT`. -/
def topT (Q : Rect) (bT : ℕ) : Rect := ⟨Q.x0, Q.y0 + Q.h - bT, Q.w, bT⟩

@[simp] theorem botB_x0 (Q : Rect) (bB : ℕ) : (Q.botB bB).x0 = Q.x0 := rfl
@[simp] theorem botB_y0 (Q : Rect) (bB : ℕ) : (Q.botB bB).y0 = Q.y0 := rfl
@[simp] theorem botB_w (Q : Rect) (bB : ℕ) : (Q.botB bB).w = Q.w := rfl
@[simp] theorem botB_h (Q : Rect) (bB : ℕ) : (Q.botB bB).h = bB := rfl
@[simp] theorem topT_x0 (Q : Rect) (bT : ℕ) : (Q.topT bT).x0 = Q.x0 := rfl
@[simp] theorem topT_y0 (Q : Rect) (bT : ℕ) : (Q.topT bT).y0 = Q.y0 + Q.h - bT := rfl
@[simp] theorem topT_w (Q : Rect) (bT : ℕ) : (Q.topT bT).w = Q.w := rfl
@[simp] theorem topT_h (Q : Rect) (bT : ℕ) : (Q.topT bT).h = bT := rfl

/-- Explored medial vertices in the bottom sub-board. -/
noncomputable def exB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.botB bB).expRm Q.y0 (Q.y0 + bB) A

/-- Explored medial vertices in the top sub-board. -/
noncomputable def exT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.topT bT).expRm (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A

/-- Boundary of the exploration in the bottom sub-board. -/
noncomputable def bdB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.botB bB).expBd Q.y0 (Q.y0 + bB) A

/-- Boundary of the exploration in the top sub-board. -/
noncomputable def bdT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.topT bT).expBd (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A

/-- No dual path joins the bottom row of `B` to its top row. -/
def barB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Prop :=
  ∀ t ∈ (Q.botB bB).faceRow (Q.y0 + bB), t ∉ (Q.botB bB).expD Q.y0 A

/-- No dual path joins the top row of `T` to its bottom row. -/
def barT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Prop :=
  ∀ t ∈ (Q.topT bT).faceRow (Q.y0 + Q.h - bT), t ∉ (Q.topT bT).expD (Q.y0 + Q.h) A

/-- The union of the two explored regions. -/
noncomputable def exAll (Q : Rect) (bB bT : ℕ) (A : Finset Cell) : Finset Cell :=
  Q.exB bB A ∪ Q.exT bT A

/-- Both barriers. -/
def barAll (Q : Rect) (bB bT : ℕ) (A : Finset Cell) : Prop := Q.barB bB A ∧ Q.barT bT A

/-- Geometric hypotheses on the two sub-boards. -/
structure Geo (Q : Rect) (bB bT : ℕ) : Prop where
  hw : 0 < Q.w
  hbB : 0 < bB
  hbT : 0 < bT
  hgap : bB + bT < Q.h

variable {Q : Rect} {bB bT : ℕ}

theorem botB_inner_subset (Q : Rect) (bB : ℕ) (h : bB ≤ Q.h) : (Q.botB bB).inner ⊆ Q.inner := by
  intro m hm
  rw [Rect.mem_inner] at hm ⊢
  simp only [botB_x0, botB_y0, botB_w, botB_h] at hm
  omega

theorem topT_inner_subset (Q : Rect) (bT : ℕ) (h : bT ≤ Q.h) : (Q.topT bT).inner ⊆ Q.inner := by
  intro m hm
  rw [Rect.mem_inner] at hm ⊢
  simp only [topT_x0, topT_y0, topT_w, topT_h] at hm
  omega

theorem exB_subset_inner (A : Finset Cell) (h : bB ≤ Q.h) : Q.exB bB A ⊆ Q.inner :=
  fun _ hm => botB_inner_subset Q bB h (mem_expRm_iff.1 hm).1

theorem exT_subset_inner (A : Finset Cell) (h : bT ≤ Q.h) : Q.exT bT A ⊆ Q.inner :=
  fun _ hm => topT_inner_subset Q bT h (mem_expRm_iff.1 hm).1

theorem exAll_subset_inner (A : Finset Cell) (hg : Q.Geo bB bT) : Q.exAll bB bT A ⊆ Q.inner :=
  have := hg.hgap
  Finset.union_subset (exB_subset_inner A (by omega)) (exT_subset_inner A (by omega))

theorem exAll_stop {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A) :
    (Q.botB bB).expD Q.y0 A' = (Q.botB bB).expD Q.y0 A ∧
      (Q.topT bT).expD (Q.y0 + Q.h) A' = (Q.topT bT).expD (Q.y0 + Q.h) A :=
  ⟨expD_stop Q.y0 (Q.y0 + bB) (by
      simpa [exAll, exB, Finset.inter_assoc] using congrArg (· ∩ Q.exB bB A) h),
   expD_stop (Q.y0 + Q.h) (Q.y0 + Q.h - bT) (by
      simpa [exAll, exT, Finset.inter_assoc] using congrArg (· ∩ Q.exT bT A) h)⟩

theorem exAll_congr {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A) :
    Q.exAll bB bT A' = Q.exAll bB bT A ∧ Q.exB bB A' = Q.exB bB A ∧ Q.exT bT A' = Q.exT bT A ∧
      Q.bdB bB A' = Q.bdB bB A ∧ Q.bdT bT A' = Q.bdT bT A ∧
      (Q.barB bB A' ↔ Q.barB bB A) ∧ (Q.barT bT A' ↔ Q.barT bT A) := by
  obtain ⟨hB, hT⟩ := exAll_stop (bB := bB) (bT := bT) h
  have e1 : Q.exB bB A' = Q.exB bB A := (Q.botB bB).expRm_congr hB
  have e2 : Q.exT bT A' = Q.exT bT A := (Q.topT bT).expRm_congr hT
  exact ⟨by unfold exAll; rw [e1, e2], e1, e2, (Q.botB bB).expBd_congr hB,
    (Q.topT bT).expBd_congr hT, by unfold barB; rw [hB], by unfold barT; rw [hT]⟩

def Vtx (S : Finset Cell) (c : Cell) : Prop :=
  ∃ e ∈ S, c = (primalEnds e).1 ∨ c = (primalEnds e).2

theorem primalEnds_fst_row (e : Cell) : (primalEnds e).1.2 = e.2 := by
  unfold primalEnds; split_ifs <;> rfl

theorem primalEnds_snd_row (e : Cell) : (primalEnds e).2.2 = e.2 - 1 := by
  unfold primalEnds; split_ifs <;> rfl

theorem Vtx_iff_corners {S : Finset Cell} {c : Cell} (hc : IsPrimal c) :
    Vtx S c ↔ ∃ e ∈ S, e ∈ corners c :=
  ⟨fun ⟨e, he, h⟩ => ⟨e, he, (mem_primalEnds_iff c e hc).1 h⟩,
   fun ⟨e, he, h⟩ => ⟨e, he, (mem_primalEnds_iff c e hc).2 h⟩⟩

theorem Vtx_mono {S S' : Finset Cell} (h : S ⊆ S') {c : Cell} (hc : Vtx S c) : Vtx S' c := by
  obtain ⟨e, he, h'⟩ := hc; exact ⟨e, h he, h'⟩

theorem Vtx_row_of_inner {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell} (hc : Vtx S c) :
    R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  obtain ⟨e, he, rfl | rfl⟩ := hc <;> have := Rect.mem_inner.1 (hS he)
  · rw [primalEnds_fst_row]; omega
  · rw [primalEnds_snd_row]; omega

theorem Vtx_mem_pcells {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell}
    (hc : Vtx S c) : c ∈ R.pcells := by
  obtain ⟨e, he, rfl | rfl⟩ := hc <;> have hd := R.pData.mem e (hS he)
  · exact hd.1
  · exact hd.2

def Wlow (Q : Rect) (bB : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.exB bB A) c ∨ c.2 = Q.y0

def Wup (Q : Rect) (bT : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.exT bT A) c ∨ c.2 = Q.y0 + Q.h

theorem Vtx_exB_row {A : Finset Cell} {c : Cell} (hc : Vtx (Q.exB bB A) c) :
    Q.y0 ≤ c.2 ∧ c.2 ≤ Q.y0 + bB :=
  Vtx_row_of_inner (fun _ hm => (mem_expRm_iff.1 hm).1) hc

theorem Vtx_exT_row {A : Finset Cell} {c : Cell} (hc : Vtx (Q.exT bT A) c) :
    Q.y0 + Q.h - bT ≤ c.2 ∧ c.2 ≤ Q.y0 + Q.h := by
  have := Vtx_row_of_inner (R := Q.topT bT) (fun _ hm => (mem_expRm_iff.1 hm).1) hc
  simp only [topT_y0, topT_h] at this; omega

theorem Wlow_row (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell} (hc : Q.Wlow bB A c) :
    c.2 ≤ Q.y0 + bB :=
  hc.elim (fun h => (Vtx_exB_row h).2) (by have := hg.hbB; omega)

theorem Wup_row (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell} (hc : Q.Wup bT A c) :
    Q.y0 + Q.h - bT ≤ c.2 :=
  hc.elim (fun h => (Vtx_exT_row h).1) (by have := hg.hbT; omega)

theorem Wlow_Wup_disjoint (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell}
    (h1 : Q.Wlow bB A c) (h2 : Q.Wup bT A c) : False := by
  have := Wlow_row hg h1; have := Wup_row hg h2; have := hg.hgap; omega

theorem Vtx_of_mem (S : Finset Cell) {m : Cell} (hm : m ∈ S) :
    Vtx S (primalEnds m).1 ∧ Vtx S (primalEnds m).2 :=
  ⟨⟨m, hm, Or.inl rfl⟩, ⟨m, hm, Or.inr rfl⟩⟩

theorem exB_ends_Wlow {A : Finset Cell} {m : Cell} (hm : m ∈ Q.exB bB A) :
    Q.Wlow bB A (primalEnds m).1 ∧ Q.Wlow bB A (primalEnds m).2 :=
  ⟨Or.inl (Vtx_of_mem _ hm).1, Or.inl (Vtx_of_mem _ hm).2⟩

theorem exT_ends_Wup {A : Finset Cell} {m : Cell} (hm : m ∈ Q.exT bT A) :
    Q.Wup bT A (primalEnds m).1 ∧ Q.Wup bT A (primalEnds m).2 :=
  ⟨Or.inl (Vtx_of_mem _ hm).1, Or.inl (Vtx_of_mem _ hm).2⟩

theorem exAll_ends {A : Finset Cell} {m : Cell} (hm : m ∈ Q.exAll bB bT A) :
    (Q.Wlow bB A (primalEnds m).1 ∧ Q.Wlow bB A (primalEnds m).2) ∨
      (Q.Wup bT A (primalEnds m).1 ∧ Q.Wup bT A (primalEnds m).2) :=
  (Finset.mem_union.1 hm).imp exB_ends_Wlow exT_ends_Wup

theorem corner_coords {c e : Cell} (he : e ∈ corners c) :
    (e.1 = c.1 ∨ e.1 = c.1 + 1) ∧ (e.2 = c.2 ∨ e.2 = c.2 + 1) := by
  unfold corners at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp

theorem cell_mem_pcells_of_corner {R : Rect} {c e : Cell} (hc : IsPrimal c) (he : e ∈ corners c)
    (hein : e ∈ R.inner) : c ∈ R.pcells :=
  Vtx_mem_pcells (S := {e}) (Finset.singleton_subset_iff.2 hein)
    ⟨e, Finset.mem_singleton_self e, (mem_primalEnds_iff c e hc).2 he⟩

theorem Wlow_Un_bd (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barB bB A) {c : Cell}
    (hc : IsPrimal c) (hW : Q.Wlow bB A c)
    (hUn : ∃ e ∈ corners c, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A) :
    Vtx (Q.bdB bB A) c := by
  have hgap := hg.hgap; have hbB := hg.hbB
  obtain ⟨e', he', hQ, hne'⟩ := hUn
  have hcQ := Rect.mem_cells.1 (Rect.mem_pcells.1 (cell_mem_pcells_of_corner hc he' hQ)).1
  have hco := corner_coords he'
  have hQi := Rect.mem_inner.1 hQ
  have hexB : e' ∉ Q.exB bB A := fun h => hne' (Finset.mem_union_left _ h)
  have hcr := Wlow_row hg hW
  have hcB : c ∈ (Q.botB bB).pcells := by
    rw [Rect.mem_pcells, Rect.mem_cells]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hc⟩ <;> simp only [botB_x0, botB_y0, botB_w, botB_h] <;> omega
  rcases hW with ⟨e1, hv1, hv1'⟩ | hrow
  · obtain ⟨e, he, hbd⟩ := Rect.vex_vun (R := Q.botB bB) (by simpa using hbB)
      (Or.inl ⟨rfl, rfl⟩) hbar Q.inner
      (fun c hcc hne e he hein => by
        have hcc' := Rect.mem_cells.1 (Rect.mem_pcells.1 hcc).1
        have := corner_coords he; have := Rect.mem_inner.1 hein
        rw [Rect.mem_inner]; simp only [botB_x0, botB_y0, botB_w, botB_h] at hcc' hne ⊢; omega)
      hcB ⟨e1, (mem_primalEnds_iff c e1 hc).1 hv1', hv1⟩ ⟨e', he', hQ, hexB⟩
    exact (Vtx_iff_corners hc).2 ⟨e, hbd, he⟩
  · exact (hexB (Rect.corner_expRm_of_row_p1 (R := Q.botB bB) (p₂ := Q.y0 + bB) (A := A) hcB
      (by simpa using hrow) he' (by rw [Rect.mem_inner]; simp only [botB_x0, botB_y0, botB_w, botB_h]; omega))).elim

theorem Wup_Un_bd (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barT bT A) {c : Cell}
    (hc : IsPrimal c) (hW : Q.Wup bT A c)
    (hUn : ∃ e ∈ corners c, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A) :
    Vtx (Q.bdT bT A) c := by
  have hgap := hg.hgap; have hbT := hg.hbT
  obtain ⟨e', he', hQ, hne'⟩ := hUn
  have hcQ := Rect.mem_cells.1 (Rect.mem_pcells.1 (cell_mem_pcells_of_corner hc he' hQ)).1
  have hco := corner_coords he'
  have hQi := Rect.mem_inner.1 hQ
  have hexT : e' ∉ Q.exT bT A := fun h => hne' (Finset.mem_union_right _ h)
  have hcr := Wup_row hg hW
  have hcT : c ∈ (Q.topT bT).pcells := by
    rw [Rect.mem_pcells, Rect.mem_cells]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hc⟩ <;> simp only [topT_x0, topT_y0, topT_w, topT_h] <;> omega
  rcases hW with ⟨e1, hv1, hv1'⟩ | hrow
  · obtain ⟨e, he, hbd⟩ := Rect.vex_vun (R := Q.topT bT) (by simpa using hbT)
      (Or.inr ⟨by simp, rfl⟩) hbar Q.inner
      (fun c hcc hne e he hein => by
        have hcc' := Rect.mem_cells.1 (Rect.mem_pcells.1 hcc).1
        have := corner_coords he; have := Rect.mem_inner.1 hein
        rw [Rect.mem_inner]; simp only [topT_x0, topT_y0, topT_w, topT_h] at hcc' hne ⊢; omega)
      hcT ⟨e1, (mem_primalEnds_iff c e1 hc).1 hv1', hv1⟩ ⟨e', he', hQ, hexT⟩
    exact (Vtx_iff_corners hc).2 ⟨e, hbd, he⟩
  · exact (hexT (Rect.corner_expRm_of_row_p1 (R := Q.topT bT) (p₂ := Q.y0 + Q.h - bT) (A := A) hcT
      (by simpa using hrow) he' (by rw [Rect.mem_inner]; simp only [topT_x0, topT_y0, topT_w, topT_h]; omega))).elim

theorem step_ends {S : Finset Cell} {z z' : Cell} (h : StepRel primalEnds S z z') :
    ∃ m ∈ S, (z = (primalEnds m).1 ∧ z' = (primalEnds m).2) ∨
      (z = (primalEnds m).2 ∧ z' = (primalEnds m).1) := by
  obtain ⟨m, hm, h | h⟩ := h
  · exact ⟨m, hm, Or.inl ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩⟩
  · exact ⟨m, hm, Or.inr ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩⟩

theorem step_of_mem {S : Finset Cell} {m : Cell} (hm : m ∈ S) :
    StepRel primalEnds S (primalEnds m).1 (primalEnds m).2 := ⟨m, hm, Or.inl rfl⟩

theorem bdB_subset_exB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Q.bdB bB A ⊆ Q.exB bB A :=
  expBd_subset_expRm _ _ _

theorem bdT_subset_exT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Q.bdT bT A ⊆ Q.exT bT A :=
  expBd_subset_expRm _ _ _

theorem cross_to_success (hg : Q.Geo bB bT) {A₀ A : Finset Cell} (hbar : Q.barAll bB bT A₀)
    (hA : A ⊆ Q.inner) {u v : Cell} (hu : u.2 = Q.y0)
    (hv : v.2 = Q.y0 + Q.h)
    (hpath : Relation.ReflTransGen (StepRel primalEnds A) u v) :
    ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
      Relation.ReflTransGen (StepRel primalEnds
        ((A \ Q.exAll bB bT A₀) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y := by
  by_contra hS
  set EX := Q.exAll bB bT A₀
  set D := (A \ EX) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀
  have hprim (m z : Cell) (hz : z = (primalEnds m).1 ∨ z = (primalEnds m).2) : IsPrimal z := by
    rcases hz with rfl | rfl <;> [exact primalEnds_fst_primal m; exact primalEnds_snd_primal m]
  have hUn (m : Cell) (hm : m ∈ A \ EX) (z : Cell)
      (hz : z = (primalEnds m).1 ∨ z = (primalEnds m).2) :
      ∃ e ∈ corners z, e ∈ Q.inner ∧ e ∉ EX :=
    ⟨m, (mem_primalEnds_iff z m (hprim m z hz)).1 hz, hA (Finset.mem_sdiff.1 hm).1,
      (Finset.mem_sdiff.1 hm).2⟩
  have hW' (x : Cell) (hx : Vtx (Q.bdB bB A₀) x) :
      ∀ z, Relation.ReflTransGen (StepRel primalEnds D) x z → ¬ Q.Wup bT A₀ z := by
    intro z hxz
    induction hxz with
    | refl => exact Wlow_Wup_disjoint hg (Or.inl (Vtx_mono (bdB_subset_exB Q bB A₀) hx))
    | @tail b c hbx hstep _ =>
      intro hW
      obtain ⟨m, hm, hc⟩ := step_ends hstep
      have hcend : c = (primalEnds m).1 ∨ c = (primalEnds m).2 :=
        hc.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
      rcases Finset.mem_union.1 hm with hm1 | hm2
      · rcases Finset.mem_union.1 hm1 with hm11 | hm12
        · exact hS ⟨x, c, hx, Wup_Un_bd hg hbar.2 (hprim m c hcend) hW (hUn m hm11 c hcend),
            hbx.tail hstep⟩
        · exact Wlow_Wup_disjoint hg (Or.inl ⟨m, bdB_subset_exB Q bB A₀ hm12, hcend⟩) hW
      · exact hS ⟨x, c, hx, ⟨m, hm2, hcend⟩, hbx.tail hstep⟩
  let L : Cell → Prop := fun z => Q.Wlow bB A₀ z ∨
    ∃ x, Vtx (Q.bdB bB A₀) x ∧ Relation.ReflTransGen (StepRel primalEnds D) x z
  have hclosed (z z' : Cell) (hz : L z) (hstep : StepRel primalEnds A z z') : L z' := by
    obtain ⟨m, hm, hmeq⟩ := hstep
    obtain ⟨_, _, hends⟩ := step_ends ⟨m, hm, hmeq⟩
    have hzend : z = (primalEnds m).1 ∨ z = (primalEnds m).2 := by
      rcases hmeq with h | h
      · exact Or.inl (congrArg Prod.fst h).symm
      · exact Or.inr (congrArg Prod.snd h).symm
    have hz'end : z' = (primalEnds m).1 ∨ z' = (primalEnds m).2 := by
      rcases hmeq with h | h
      · exact Or.inr (congrArg Prod.snd h).symm
      · exact Or.inl (congrArg Prod.fst h).symm
    by_cases hmEX : m ∈ EX
    · rcases Finset.mem_union.1 hmEX with hB | hT
      · exact Or.inl (Or.inl ⟨m, hB, hz'end⟩)
      · exact (hz.elim (fun hlz => Wlow_Wup_disjoint hg hlz (Or.inl ⟨m, hT, hzend⟩))
          (fun ⟨x, hx, hxz⟩ => hW' x hx z hxz (Or.inl ⟨m, hT, hzend⟩))).elim
    · have hmD : m ∈ A \ EX := Finset.mem_sdiff.2 ⟨hm, hmEX⟩
      have hstepD : StepRel primalEnds D z z' :=
        ⟨m, Finset.mem_union_left _ (Finset.mem_union_left _ hmD), hmeq⟩
      exact Or.inr (hz.elim
        (fun hlz => ⟨z, Wlow_Un_bd hg hbar.1 (hprim m z hzend) hlz (hUn m hmD z hzend),
          Relation.ReflTransGen.single hstepD⟩)
        (fun ⟨x, hx, hxz⟩ => ⟨x, hx, hxz.tail hstepD⟩))
  have key : ∀ w, Relation.ReflTransGen (StepRel primalEnds A) u w → L w := by
    intro w hw
    induction hw with
    | refl => exact Or.inl (Or.inr hu)
    | @tail b c _ hstep ih => exact hclosed b c ih hstep
  rcases key v hpath with hl | ⟨x, hx, hxv⟩
  · have := Wlow_row hg hl; have := hg.hgap; have := hg.hbT; omega
  · exact hW' x hx v hxv (Or.inr hv)

private theorem Vtx_bd_connected_aux {S : Finset Cell} {x y : Cell}
    (hx : Vtx S x) (hy : Vtx S y)
    (hconn : ∀ m ∈ S, ∀ m' ∈ S,
      Relation.ReflTransGen (StepRel primalEnds S) (primalEnds m).1 (primalEnds m').1) :
    Relation.ReflTransGen (StepRel primalEnds S) x y := by
  obtain ⟨m, hm, hxm⟩ := hx
  obtain ⟨m', hm', hym⟩ := hy
  have hmx : Relation.ReflTransGen (StepRel primalEnds S) x (primalEnds m).1 := by
    rcases hxm with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (stepRel_symm (step_of_mem hm))
  have hmy : Relation.ReflTransGen (StepRel primalEnds S) (primalEnds m').1 y := by
    rcases hym with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (step_of_mem hm')
  exact hmx.trans ((hconn m hm m' hm').trans hmy)

theorem Vtx_bdB_connected (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barB bB A) {x y : Cell}
    (hx : Vtx (Q.bdB bB A) x) (hy : Vtx (Q.bdB bB A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.bdB bB A)) x y :=
  Vtx_bd_connected_aux hx hy fun _ hm _ hm' =>
    (Q.botB bB).bd_connected (by simpa using hg.hbB) (by simpa using hg.hw)
      (Or.inl ⟨rfl, rfl⟩) hbar hm hm'

theorem Vtx_bdT_connected (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barT bT A) {x y : Cell}
    (hx : Vtx (Q.bdT bT A) x) (hy : Vtx (Q.bdT bT A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.bdT bT A)) x y :=
  Vtx_bd_connected_aux hx hy fun _ hm _ hm' =>
    (Q.topT bT).bd_connected (by simpa using hg.hbT) (by simpa using hg.hw)
      (Or.inr ⟨by simp, rfl⟩) hbar hm hm'

def sideSetoid (hg : Q.Geo bB bT) (A₀ : Finset Cell) : Setoid Q.pcells where
  r a b := a = b ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ b.1) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ b.1)
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro a b (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
        · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      trans := by
        rintro a b c (rfl | h | h) (rfl | h' | h')
        · exact Or.inl rfl
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inl ⟨h.1, h'.2⟩)
        · exact (Wlow_Wup_disjoint hg h.2 h'.1).elim
        · exact Or.inr (Or.inr h)
        · exact (Wlow_Wup_disjoint hg h'.1 h.2).elim
        · exact Or.inr (Or.inr ⟨h.1, h'.2⟩) }

theorem componentSetoid_le_side (hg : Q.Geo bB bT) (A₀ : Finset Cell) :
    FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀)) ≤ sideSetoid hg A₀ := by
  have hsub := exAll_subset_inner A₀ hg
  apply FK.componentSetoid_le
  · intro a b hab
    rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData _ hsub] at hab
    have key : ∀ z, Relation.ReflTransGen (StepRel primalEnds (Q.exAll bB bT A₀)) z b.1 →
        ∀ hz : z ∈ Q.pcells, (sideSetoid hg A₀).r ⟨z, hz⟩ b := by
      intro z hz
      induction hz using Relation.ReflTransGen.head_induction_on with
      | refl => intro _; exact (sideSetoid hg A₀).refl b
      | @head u w hstep _ ih =>
        intro hu
        obtain ⟨m, hm, h | h⟩ := step_ends hstep
        · have hw : w ∈ Q.pcells := h.2 ▸ (Q.pData.mem m (hsub hm)).2
          refine (sideSetoid hg A₀).trans ?_ (ih hw)
          exact Or.inr ((exAll_ends hm).imp (fun hl => ⟨h.1.symm ▸ hl.1, h.2.symm ▸ hl.2⟩)
            (fun hu' => ⟨h.1.symm ▸ hu'.1, h.2.symm ▸ hu'.2⟩))
        · have hw : w ∈ Q.pcells := h.2 ▸ (Q.pData.mem m (hsub hm)).1
          refine (sideSetoid hg A₀).trans ?_ (ih hw)
          exact Or.inr ((exAll_ends hm).imp (fun hl => ⟨h.1.symm ▸ hl.2, h.2.symm ▸ hl.1⟩)
            (fun hu' => ⟨h.1.symm ▸ hu'.2, h.2.symm ▸ hu'.1⟩))
    exact key a.1 hab a.2
  · rintro a b (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨Or.inr h.1, Or.inr h.2⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h.1, Or.inr h.2⟩)

theorem kc (hg : Q.Geo bB bT) {A₀ : Finset Cell} (hbar : Q.barAll bB bT A₀) {x y : Q.pcells}
    (hx : Vtx (Q.inner \ Q.exAll bB bT A₀) x.1) (hy : Vtx (Q.inner \ Q.exAll bB bT A₀) y.1)
    (h : (FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀))).r x y) :
    x = y ∨ (Vtx (Q.bdB bB A₀) x.1 ∧ Vtx (Q.bdB bB A₀) y.1) ∨
      (Vtx (Q.bdT bT A₀) x.1 ∧ Vtx (Q.bdT bT A₀) y.1) := by
  have hxp := (Rect.mem_pcells.1 x.2).2
  have hyp := (Rect.mem_pcells.1 y.2).2
  have hUn (z : Cell) (hz : IsPrimal z) (hv : Vtx (Q.inner \ Q.exAll bB bT A₀) z) :
      ∃ e ∈ corners z, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A₀ := by
    obtain ⟨e, he, hec⟩ := (Vtx_iff_corners hz).1 hv
    exact ⟨e, hec, (Finset.mem_sdiff.1 he).1, (Finset.mem_sdiff.1 he).2⟩
  rcases componentSetoid_le_side hg A₀ h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨Wlow_Un_bd hg hbar.1 hxp h1 (hUn x.1 hxp hx),
      Wlow_Un_bd hg hbar.1 hyp h2 (hUn y.1 hyp hy)⟩)
  · exact Or.inr (Or.inr ⟨Wup_Un_bd hg hbar.2 hxp h1 (hUn x.1 hxp hx),
      Wup_Un_bd hg hbar.2 hyp h2 (hUn y.1 hyp hy)⟩)

end Rect

end PottsDiscontinuity.TorusCrossing
