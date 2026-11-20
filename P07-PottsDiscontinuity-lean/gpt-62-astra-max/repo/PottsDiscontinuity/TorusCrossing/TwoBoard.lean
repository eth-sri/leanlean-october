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

section
variable (Q : Rect) (bB : ℕ) (bT : ℕ) (A : Finset Cell)
include Q

include bB in
/-- Bottom sub-board of height `bB`. -/
def botB : Rect := ⟨Q.x0, Q.y0, Q.w, bB⟩

include bT in
/-- Top sub-board of height `bT`. -/
def topT : Rect := ⟨Q.x0, Q.y0 + Q.h - bT, Q.w, bT⟩

@[simp] theorem botB_x0 : (Q.botB bB).x0 = Q.x0 := rfl
@[simp] theorem botB_y0 : (Q.botB bB).y0 = Q.y0 := rfl
@[simp] theorem botB_w : (Q.botB bB).w = Q.w := rfl
@[simp] theorem botB_h : (Q.botB bB).h = bB := rfl
@[simp] theorem topT_x0 : (Q.topT bT).x0 = Q.x0 := rfl
@[simp] theorem topT_y0 : (Q.topT bT).y0 = Q.y0 + Q.h - bT := rfl
@[simp] theorem topT_w : (Q.topT bT).w = Q.w := rfl
@[simp] theorem topT_h : (Q.topT bT).h = bT := rfl

include bB A in
/-- Explored medial vertices in the bottom sub-board. -/
noncomputable def exB : Finset Cell :=
  (Q.botB bB).expRm Q.y0 (Q.y0 + bB) A

include bT A in
/-- Explored medial vertices in the top sub-board. -/
noncomputable def exT : Finset Cell :=
  (Q.topT bT).expRm (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A

include bB A in
/-- Boundary of the exploration in the bottom sub-board. -/
noncomputable def bdB : Finset Cell :=
  (Q.botB bB).expBd Q.y0 (Q.y0 + bB) A

include bT A in
/-- Boundary of the exploration in the top sub-board. -/
noncomputable def bdT : Finset Cell :=
  (Q.topT bT).expBd (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A

include bB A in
/-- No dual path joins the bottom row of `B` to its top row. -/
def barB : Prop :=
  ∀ t ∈ (Q.botB bB).faceRow (Q.y0 + bB), t ∉ (Q.botB bB).expD Q.y0 A

include bT A in
/-- No dual path joins the top row of `T` to its bottom row. -/
def barT : Prop :=
  ∀ t ∈ (Q.topT bT).faceRow (Q.y0 + Q.h - bT), t ∉ (Q.topT bT).expD (Q.y0 + Q.h) A

/-- The union of the two explored regions. -/
noncomputable def exAll (bB bT : ℕ) (A : Finset Cell) : Finset Cell :=
  Q.exB bB A ∪ Q.exT bT A

/-- Both barriers. -/
def barAll (bB bT : ℕ) (A : Finset Cell) : Prop := Q.barB bB A ∧ Q.barT bT A

/-- Geometric hypotheses on the two sub-boards. -/
structure Geo (bB bT : ℕ) : Prop where
  hw : 0 < Q.w
  hbB : 0 < bB
  hbT : 0 < bT
  hgap : bB + bT < Q.h

end

variable {Q : Rect} {bB bT : ℕ}

theorem botB_inner_subset (Q : Rect) (bB : ℕ) (h : bB ≤ Q.h) : (Q.botB bB).inner ⊆ Q.inner := by
  grind [Rect.mem_inner, botB_x0, botB_y0, botB_w, botB_h]

theorem topT_inner_subset (Q : Rect) (bT : ℕ) (h : bT ≤ Q.h) : (Q.topT bT).inner ⊆ Q.inner := by
  grind [Rect.mem_inner, topT_x0, topT_y0, topT_w, topT_h]

theorem exB_subset_inner (A : Finset Cell) (h : bB ≤ Q.h) : Q.exB bB A ⊆ Q.inner := fun ⦃m⦄ hm => botB_inner_subset Q bB h (mem_expRm_iff.mp hm).left

theorem exT_subset_inner (A : Finset Cell) (h : bT ≤ Q.h) : Q.exT bT A ⊆ Q.inner := fun ⦃m⦄ hm => topT_inner_subset Q bT h (mem_expRm_iff.mp hm).left

theorem exAll_subset_inner (A : Finset Cell) (hg : Q.Geo bB bT) : Q.exAll bB bT A ⊆ Q.inner := by
  intro m hm
  rcases Finset.mem_union.1 hm with h | h
  · exact exB_subset_inner A (by have := hg.hgap; omega) h
  · exact exT_subset_inner A (by have := hg.hgap; omega) h

/-- Stopping property of the two explorations. -/
theorem exAll_stop {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A) :
    (Q.botB bB).expD Q.y0 A' = (Q.botB bB).expD Q.y0 A ∧
      (Q.topT bT).expD (Q.y0 + Q.h) A' = (Q.topT bT).expD (Q.y0 + Q.h) A := by
  constructor
  · apply expD_stop Q.y0 _
    have hsub : (Q.botB bB).expRm Q.y0 (Q.y0 + bB) A ⊆ Q.exAll bB bT A :=
      Finset.subset_union_left
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
      have  := Finset.mem_inter.2 ⟨hx1, hsub hx2⟩
      grind
    · intro hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
      have  := Finset.mem_inter.2 ⟨hx1, hsub hx2⟩
      grind
  · apply expD_stop _ _
    have hsub : (Q.topT bT).expRm (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A ⊆ Q.exAll bB bT A :=
      Finset.subset_union_right
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
      have  := Finset.mem_inter.2 ⟨hx1, hsub hx2⟩
      grind
    · intro hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
      have  := Finset.mem_inter.2 ⟨hx1, hsub hx2⟩
      grind

theorem exAll_congr {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A) :
    Q.exAll bB bT A' = Q.exAll bB bT A ∧ Q.exB bB A' = Q.exB bB A ∧ Q.exT bT A' = Q.exT bT A ∧
      Q.bdB bB A' = Q.bdB bB A ∧ Q.bdT bT A' = Q.bdT bT A ∧
      (Q.barB bB A' ↔ Q.barB bB A) ∧ (Q.barT bT A' ↔ Q.barT bT A) := by
  obtain ⟨hB, hT⟩ := exAll_stop h
  have e1 : Q.exB bB A' = Q.exB bB A := (Q.botB bB).expRm_congr hB
  have e2 : Q.exT bT A' = Q.exT bT A := (Q.topT bT).expRm_congr hT
  refine ⟨?_, e1, e2, (Q.botB bB).expBd_congr hB, (Q.topT bT).expBd_congr hT, ?_, ?_⟩ <;> simp [e1, e2, exAll, hB, barB, hT, barT]

/-- A cell is an end of the primal edge of some medial vertex of `S`. -/
def Vtx (S : Finset Cell) (c : Cell) : Prop :=
  ∃ e ∈ S, c = (primalEnds e).1 ∨ c = (primalEnds e).2

section
variable {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {A : Finset Cell} {c : Cell}
    (hc : Vtx S c) (e : Cell)

theorem primalEnds_fst_row : (primalEnds e).1.2 = e.2 := by
  grind [primalEnds]

theorem primalEnds_snd_row : (primalEnds e).2.2 = e.2 - 1 := by
  grind [primalEnds]

theorem Vtx_iff_corners (hc : IsPrimal c) :
    Vtx S c ↔ ∃ e ∈ S, e ∈ corners c := by
  constructor
  · rintro ⟨e, he, h⟩; exact ⟨e, he, (mem_primalEnds_iff c e hc).1 h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, (mem_primalEnds_iff c e hc).2 h⟩

theorem Vtx_mono {S S' : Finset Cell} (h : S ⊆ S') {c : Cell} (hc : Vtx S c) : Vtx S' c := by
  obtain ⟨e, he, h'⟩ := hc; exact ⟨e, h he, h'⟩

include hS hc in
theorem Vtx_row_of_inner :
    R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  obtain ⟨e, he, h⟩ := hc
  have := Rect.mem_inner.1 (hS he)
  rcases h with rfl | rfl
  · grind [primalEnds_fst_row]
  · rw [primalEnds_snd_row]; omega

include hS hc in
theorem Vtx_mem_pcells : c ∈ R.pcells := by
  obtain ⟨e, he, h⟩ := hc
  have hd := R.pData.mem e (hS he)
  grind

/-- Cells on the lower side of the explored region of `B` (or on the bottom row). -/
def Wlow (Q : Rect) (bB : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.exB bB A) c ∨ c.2 = Q.y0

/-- Cells on the upper side of the explored region of `T` (or on the top row). -/
def Wup (Q : Rect) (bT : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.exT bT A) c ∨ c.2 = Q.y0 + Q.h

theorem Vtx_exB_row (hc : Vtx (Q.exB bB A) c) :
    Q.y0 ≤ c.2 ∧ c.2 ≤ Q.y0 + bB := Vtx_row_of_inner (fun m hm => (mem_expRm_iff.mp hm).left) hc

theorem Vtx_exT_row (hc : Vtx (Q.exT bT A) c) :
    Q.y0 + Q.h - bT ≤ c.2 ∧ c.2 ≤ Q.y0 + Q.h := by
  have := Vtx_row_of_inner (fun m hm => ((mem_expRm_iff).1 hm).1) hc
  grind [topT_y0, topT_h]

end

theorem Wlow_row {A : Finset Cell} {c : Cell} (hc : Q.Wlow bB A c) :
    c.2 ≤ Q.y0 + bB := by
  rcases hc with h | h
  · exact (Vtx_exB_row h).2
  · omega

theorem Wup_row {A : Finset Cell} {c : Cell} (hc : Q.Wup bT A c) :
    Q.y0 + Q.h - bT ≤ c.2 := by
  rcases hc with h | h
  · exact (Vtx_exT_row h).1
  · omega

theorem Wlow_Wup_disjoint (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell}
    (h1 : Q.Wlow bB A c) (h2 : Q.Wup bT A c) : False := by
  have a := Wlow_row h1
  have b := Wup_row h2
  have := hg.hgap
  omega

section
variable {A : Finset Cell} {m : Cell}

theorem exB_ends_Wlow (hm : m ∈ Q.exB bB A) :
    Q.Wlow bB A (primalEnds m).1 ∧ Q.Wlow bB A (primalEnds m).2 :=
  ⟨Or.inl ⟨m, hm, Or.inl rfl⟩, Or.inl ⟨m, hm, Or.inr rfl⟩⟩

theorem exT_ends_Wup (hm : m ∈ Q.exT bT A) :
    Q.Wup bT A (primalEnds m).1 ∧ Q.Wup bT A (primalEnds m).2 :=
  ⟨Or.inl ⟨m, hm, Or.inl rfl⟩, Or.inl ⟨m, hm, Or.inr rfl⟩⟩

end

theorem exAll_ends {A : Finset Cell} {m : Cell} (hm : m ∈ Q.exAll bB bT A) :
    (Q.Wlow bB A (primalEnds m).1 ∧ Q.Wlow bB A (primalEnds m).2) ∨
      (Q.Wup bT A (primalEnds m).1 ∧ Q.Wup bT A (primalEnds m).2) := by
  rcases Finset.mem_union.1 hm with h | h
  · exact Or.inl (exB_ends_Wlow h)
  · exact Or.inr (exT_ends_Wup h)

section
variable {R : Rect} {c e : Cell} (hc : IsPrimal c) (he : e ∈ corners c)
include he

theorem corner_coords :
    (e.1 = c.1 ∨ e.1 = c.1 + 1) ∧ (e.2 = c.2 ∨ e.2 = c.2 + 1) := by
  unfold corners at he
  grind

include hc in
theorem cell_mem_pcells_of_corner
    (hein : e ∈ R.inner) : c ∈ R.pcells :=
  Vtx_mem_pcells (Finset.singleton_subset_iff.2 hein)
    ⟨e, Finset.mem_singleton_self e, (mem_primalEnds_iff c e hc).2 he⟩

end

/-- A primal cell on the lower side of the explored region of `B` that sees an unexplored edge
of `Q` sees a boundary edge of `B`. -/
theorem Wlow_Un_bd (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barB bB A) {c : Cell}
    (hc : IsPrimal c) (hW : Q.Wlow bB A c)
    (hUn : ∃ e ∈ corners c, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A) :
    ∃ e ∈ corners c, e ∈ Q.bdB bB A := by
  have hbB := hg.hbB
  obtain ⟨e', he', hQ, hne'⟩ := hUn
  have hco := corner_coords he'
  have hQi := Rect.mem_inner.1 hQ
  have hexB := fun h => hne' (Finset.mem_union_left _ h)
  rcases hW with hV | hrow
  · have hcr := Vtx_exB_row hV
    obtain ⟨e1, hv1, hv1'⟩ := hV
    refine Rect.vex_vun (R := Q.botB bB) (by exact hbB) (Or.inl ⟨rfl, rfl⟩) hbar Q.inner (by
      intro c hcc hne e he hein
      have hcc' := Rect.mem_cells.1 (Rect.mem_pcells.1 hcc).1
      have hco := corner_coords he
      grind [Rect.mem_inner, botB_x0, botB_y0, botB_w, botB_h]) (by grind [Rect.mem_pcells, Rect.mem_cells, botB_x0, botB_y0, botB_w, botB_h])
      ⟨e1, ?_, hv1⟩ ⟨e', he', hQ, hexB⟩
    exact (mem_primalEnds_iff c e1 hc).1 hv1'
  · exfalso
    have hB' : e' ∈ (Q.botB bB).inner := by
      grind [Rect.mem_inner, botB_x0, botB_y0, botB_w, botB_h]
    have hcB : c ∈ (Q.botB bB).pcells := by
      grind [Rect.mem_pcells, Rect.mem_cells, botB_x0, botB_y0, botB_w, botB_h]
    exact hexB (by apply Rect.corner_expRm_of_row_p1 <;> assumption)

/-- The same for the upper side. -/
theorem Wup_Un_bd (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barT bT A) {c : Cell}
    (hc : IsPrimal c) (hW : Q.Wup bT A c)
    (hUn : ∃ e ∈ corners c, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A) :
    ∃ e ∈ corners c, e ∈ Q.bdT bT A := by
  have hbT := hg.hbT
  obtain ⟨e', he', hQ, hne'⟩ := hUn
  have hco := corner_coords he'
  have hQi := Rect.mem_inner.1 hQ
  have hexT := fun h => hne' (Finset.mem_union_right _ h)
  rcases hW with hV | hrow
  · have hcr := Vtx_exT_row hV
    obtain ⟨e1, hv1, hv1'⟩ := hV
    refine Rect.vex_vun (R := Q.topT bT) (by exact hbT) (Or.inr ⟨by simp, rfl⟩) hbar Q.inner (by
      intro c hcc hne e he hein
      have hcc' := Rect.mem_cells.1 (Rect.mem_pcells.1 hcc).1
      have hco := corner_coords he
      grind [Rect.mem_inner, topT_x0, topT_y0, topT_w, topT_h]) (by grind [Rect.mem_pcells, Rect.mem_cells, topT_x0, topT_y0, topT_w, topT_h])
      ⟨e1, ?_, hv1⟩ ⟨e', he', hQ, hexT⟩
    exact (mem_primalEnds_iff c e1 hc).1 hv1'
  · exfalso
    have hT' : e' ∈ (Q.topT bT).inner := by
      grind [Rect.mem_inner, topT_x0, topT_y0, topT_w, topT_h]
    have hcT : c ∈ (Q.topT bT).pcells := by
      grind [Rect.mem_pcells, Rect.mem_cells, topT_x0, topT_y0, topT_w, topT_h]
    exact hexT (by apply Rect.corner_expRm_of_row_p1 <;> assumption)

section
variable (Q : Rect) (bT : ℕ) (bB : ℕ) (A : Finset Cell) {S : Finset Cell}

theorem step_ends {z z' : Cell} (h : StepRel primalEnds S z z') :
    ∃ m ∈ S, (z = (primalEnds m).1 ∧ z' = (primalEnds m).2) ∨
      (z = (primalEnds m).2 ∧ z' = (primalEnds m).1) := by
  obtain ⟨m, hm, h⟩ := h
  grind

theorem step_of_mem {m : Cell} (hm : m ∈ S) :
    StepRel primalEnds S (primalEnds m).1 (primalEnds m).2 := ⟨m, hm, Or.inl rfl⟩

theorem bdB_subset_exB : Q.bdB bB A ⊆ Q.exB bB A :=
  expBd_subset_expRm _ _ _

theorem bdT_subset_exT : Q.bdT bT A ⊆ Q.exT bT A :=
  expBd_subset_expRm _ _ _

end

theorem Vtx_of_mem (S : Finset Cell) {m : Cell} (hm : m ∈ S) :
    Vtx S (primalEnds m).1 ∧ Vtx S (primalEnds m).2 :=
  ⟨⟨m, hm, Or.inl rfl⟩, ⟨m, hm, Or.inr rfl⟩⟩

/-- The key topological consequence of the local analysis: an open path from the bottom row to the
top row of `Q`, in a configuration containing all explored edges, yields a path from the boundary
of the lower exploration to the boundary of the upper exploration which uses only unexplored open
edges and boundary edges. -/
theorem cross_to_success (hg : Q.Geo bB bT) {A₀ A : Finset Cell} (hbar : Q.barAll bB bT A₀)
    (hA : A ⊆ Q.inner) {u v : Cell} (hu : u.2 = Q.y0)
    (hv : v.2 = Q.y0 + Q.h)
    (hpath : Relation.ReflTransGen (StepRel primalEnds A) u v) :
    ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
      Relation.ReflTransGen (StepRel primalEnds
        ((A \ Q.exAll bB bT A₀) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y := by
  by_contra hS
  have hgap := hg.hgap
  set EX := Q.exAll bB bT A₀ with hEXdef
  set D := (A \ EX) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀ with hD
  have hprim : ∀ m z, (z = (primalEnds m).1 ∨ z = (primalEnds m).2) → IsPrimal z := by
    intro m z hz
    rcases hz with rfl | rfl
    · exact primalEnds_fst_primal m
    · exact primalEnds_snd_primal m
  -- an unexplored open edge sees only boundary edges on the exploration sides
  have hUn : ∀ m ∈ A \ EX, ∀ z, (z = (primalEnds m).1 ∨ z = (primalEnds m).2) →
      ∃ e ∈ corners z, e ∈ Q.inner ∧ e ∉ EX := by
    intro m hm z hz
    have hmA := Finset.mem_sdiff.1 hm
    exact ⟨m, (mem_primalEnds_iff z m (hprim m z hz)).1 hz, hA hmA.1, hmA.2⟩
  have hlow : ∀ m ∈ A \ EX, ∀ z, (z = (primalEnds m).1 ∨ z = (primalEnds m).2) →
      Q.Wlow bB A₀ z → Vtx (Q.bdB bB A₀) z := by
    intro m hm z hz hW
    obtain ⟨e, he, hbd⟩ := Wlow_Un_bd hg hbar.1 (hprim m z hz) hW (hUn m hm z hz)
    exact (Vtx_iff_corners (hprim m z hz)).2 ⟨e, hbd, he⟩
  have hup : ∀ m ∈ A \ EX, ∀ z, (z = (primalEnds m).1 ∨ z = (primalEnds m).2) →
      Q.Wup bT A₀ z → Vtx (Q.bdT bT A₀) z := by
    intro m hm z hz hW
    obtain ⟨e, he, hbd⟩ := Wup_Un_bd hg hbar.2 (hprim m z hz) hW (hUn m hm z hz)
    exact (Vtx_iff_corners (hprim m z hz)).2 ⟨e, hbd, he⟩
  -- no success: D-paths from the lower boundary never reach the upper side
  have hW' : ∀ x, Vtx (Q.bdB bB A₀) x → ∀ z, Relation.ReflTransGen (StepRel primalEnds D) x z →
      ¬ Q.Wup bT A₀ z := by
    intro x hx z hxz
    induction hxz with
    | refl =>
      intro hW
      exact Wlow_Wup_disjoint hg (Or.inl (Vtx_mono (bdB_subset_exB Q bB A₀) hx)) hW
    | @tail b c hbx hstep ih =>
      intro hW
      obtain ⟨m, hm, hc⟩ := step_ends hstep
      have hcend : c = (primalEnds m).1 ∨ c = (primalEnds m).2 := by
        grind
      have hsucc := fun y hy hxy => hS ⟨x, y, hx, hy, hxy⟩
      have hcT := hbx.tail hstep
      rcases Finset.mem_union.1 hm with hm1 | hm2
      · rcases Finset.mem_union.1 hm1 with hm11 | hm12
        · grind
        · have := Vtx_of_mem _ hm12
          have hb' : Vtx (Q.exB bB A₀) c := by
            rcases hcend with rfl | rfl
            · exact Vtx_mono (bdB_subset_exB Q bB A₀) this.1
            · exact Vtx_mono (bdB_subset_exB Q bB A₀) this.2
          exact Wlow_Wup_disjoint hg (Or.inl hb') hW
      · have := Vtx_of_mem _ hm2
        grind
  -- the set L of cells reachable on the lower side is closed under open steps
  let L := fun z => Q.Wlow bB A₀ z ∨
    ∃ x, Vtx (Q.bdB bB A₀) x ∧ Relation.ReflTransGen (StepRel primalEnds D) x z
  have hclosed : ∀ z z', L z → StepRel primalEnds A z z' → L z' := by
    intro z z' hz hstep
    obtain ⟨m, hm, hmeq⟩ := hstep
    have hzend : z = (primalEnds m).1 ∨ z = (primalEnds m).2 := by
      grind
    have hz'end : z' = (primalEnds m).1 ∨ z' = (primalEnds m).2 := by
      grind
    by_cases hmEX : m ∈ EX
    · rcases Finset.mem_union.1 hmEX with hB | hT
      · refine Or.inl ?_
        have := exB_ends_Wlow (A := A₀) hB
        grind
      · exfalso
        have hT' := exT_ends_Wup (A := A₀) hT
        have hWz : Q.Wup bT A₀ z := by
          grind
        rcases hz with hlz | ⟨x, hx, hxz⟩
        · exact Wlow_Wup_disjoint hg hlz hWz
        · grind
    · have hmD := Finset.mem_sdiff.2 ⟨hm, hmEX⟩
      have hstepD : StepRel primalEnds D z z' :=
        ⟨m, Finset.mem_union_left _ (Finset.mem_union_left _ hmD), hmeq⟩
      grind
  have hLu : L u := Or.inl (Or.inr hu)
  have key : ∀ w, Relation.ReflTransGen (StepRel primalEnds A) u w → L w := by
    intro w hw
    induction hw with
    | refl => exact hLu
    | @tail b c _ hstep ih => grind
  have hLv := key v hpath
  rcases hLv with hl | ⟨x, hx, hxv⟩
  · have := Wlow_row hl
    omega
  · exact hW' x hx v hxv (Or.inr hv)

theorem Vtx_bdB_connected (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barB bB A) {x y : Cell}
    (hx : Vtx (Q.bdB bB A) x) (hy : Vtx (Q.bdB bB A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.bdB bB A)) x y := by
  obtain ⟨m, hm, hxm⟩ := hx
  obtain ⟨m', hm', hym⟩ := hy
  have hconn := (Q.botB bB).bd_connected (by simpa using hg.hbB) (by simpa using hg.hw)
    (p₁ := Q.y0) (p₂ := Q.y0 + bB) (A := A) (Or.inl ⟨rfl, rfl⟩) hbar hm hm'
  have hmy : Relation.ReflTransGen (StepRel primalEnds (Q.bdB bB A)) (primalEnds m').1 y := by
    rcases hym with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (step_of_mem hm')
  have hmx' : Relation.ReflTransGen (StepRel primalEnds (Q.bdB bB A)) x (primalEnds m).1 := by
    rcases hxm with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (stepRel_symm (step_of_mem hm))
  exact hmx'.trans (hconn.trans hmy)

theorem Vtx_bdT_connected (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barT bT A) {x y : Cell}
    (hx : Vtx (Q.bdT bT A) x) (hy : Vtx (Q.bdT bT A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.bdT bT A)) x y := by
  obtain ⟨m, hm, hxm⟩ := hx
  obtain ⟨m', hm', hym⟩ := hy
  have hconn := (Q.topT bT).bd_connected (by simpa using hg.hbT) (by simpa using hg.hw)
    (p₁ := Q.y0 + Q.h) (p₂ := Q.y0 + Q.h - bT) (A := A) (Or.inr ⟨by simp, rfl⟩) hbar hm hm'
  have hmy : Relation.ReflTransGen (StepRel primalEnds (Q.bdT bT A)) (primalEnds m').1 y := by
    rcases hym with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (step_of_mem hm')
  have hmx' : Relation.ReflTransGen (StepRel primalEnds (Q.bdT bT A)) x (primalEnds m).1 := by
    rcases hxm with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (stepRel_symm (step_of_mem hm))
  exact hmx'.trans (hconn.trans hmy)

/-- The equivalence relation whose classes are the lower side, the upper side and singletons. -/
def sideSetoid (hg : Q.Geo bB bT) (A₀ : Finset Cell) : Setoid Q.pcells where
  r a b := a = b ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ b.1) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ b.1)
  iseqv :=
    { refl := fun a => Or.inl rfl
      symm := by
        rintro a b (h | h | h)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
        · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      trans := by
        rintro a b c (h | h | h) (h' | h' | h')
        · exact Or.inl (h.trans h')
        · subst h; exact Or.inr (Or.inl h')
        · subst h; exact Or.inr (Or.inr h')
        · subst h'; exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inl ⟨h.1, h'.2⟩)
        · exact (Wlow_Wup_disjoint hg h.2 h'.1).elim
        · subst h'; exact Or.inr (Or.inr h)
        · exact (Wlow_Wup_disjoint hg h'.1 h.2).elim
        · exact Or.inr (Or.inr ⟨h.1, h'.2⟩) }

theorem componentSetoid_le_side (hg : Q.Geo bB bT) (A₀ : Finset Cell) :
    FK.componentSetoid Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀)) ≤ sideSetoid hg A₀ := by
  have hsub := exAll_subset_inner A₀ hg
  apply FK.componentSetoid_le
  · intro a b hab
    rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData hsub] at hab
    have key : ∀ z, Relation.ReflTransGen (StepRel primalEnds (Q.exAll bB bT A₀)) a.1 z →
        z = a.1 ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ z) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ z) := by
      intro z hz
      induction hz with
      | refl => exact Or.inl rfl
      | @tail b c _ hstep ih =>
        obtain ⟨m, hm, hmeq⟩ := step_ends hstep
        have hbend : b = (primalEnds m).1 ∨ b = (primalEnds m).2 := by
          grind
        have hcend : c = (primalEnds m).1 ∨ c = (primalEnds m).2 := by
          grind
        rcases exAll_ends hm with hl | hu
        · have hWb : Q.Wlow bB A₀ b := by
            grind
          have hWc : Q.Wlow bB A₀ c := by
            grind
          rcases ih with rfl | ⟨h1, _⟩ | ⟨h1, h2⟩
          · grind
          · grind
          · exact (Wlow_Wup_disjoint hg hWb h2).elim
        · have hWb : Q.Wup bT A₀ b := by
            grind
          have hWc : Q.Wup bT A₀ c := by
            grind
          rcases ih with rfl | ⟨h1, h2⟩ | ⟨h1, _⟩
          · grind
          · exact (Wlow_Wup_disjoint hg h2 hWb).elim
          · grind
    rcases key b.1 hab with h | h | h
    · exact Or.inl (Subtype.ext h.symm)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro a b hab
    rcases hab with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨Or.inr h.1, Or.inr h.2⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h.1, Or.inr h.2⟩)

/-- **Boundary comparison at the cell level**: two cells seeing unexplored edges and related in the
partition induced by the sep-wiring and the explored edges are equal or lie on the same boundary. -/
theorem kc (hg : Q.Geo bB bT) {A₀ : Finset Cell} (hbar : Q.barAll bB bT A₀) {x y : Q.pcells}
    (hx : Vtx (Q.inner \ Q.exAll bB bT A₀) x.1) (hy : Vtx (Q.inner \ Q.exAll bB bT A₀) y.1)
    (h : (FK.componentSetoid Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀))).r x y) :
    x = y ∨ (Vtx (Q.bdB bB A₀) x.1 ∧ Vtx (Q.bdB bB A₀) y.1) ∨
      (Vtx (Q.bdT bT A₀) x.1 ∧ Vtx (Q.bdT bT A₀) y.1) := by
  have hxp := (Rect.mem_pcells.1 x.2).2
  have hyp := (Rect.mem_pcells.1 y.2).2
  have hs := componentSetoid_le_side hg A₀ h
  have hUn : ∀ z : Cell, IsPrimal z → Vtx (Q.inner \ Q.exAll bB bT A₀) z →
      ∃ e ∈ corners z, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A₀ := by
    intro z hz hv
    obtain ⟨e, he, hec⟩ := (Vtx_iff_corners hz).1 hv
    grind
  rcases hs with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1
  · right; left
    exact ⟨(Vtx_iff_corners hxp).2 (by
        obtain ⟨e, he, hec⟩ := Wlow_Un_bd hg hbar.1 hxp h1 (hUn x.1 hxp hx)
        grind),
      (Vtx_iff_corners hyp).2 (by
        obtain ⟨e, he, hec⟩ := Wlow_Un_bd hg hbar.1 hyp h2 (hUn y.1 hyp hy)
        grind)⟩
  · right; right
    exact ⟨(Vtx_iff_corners hxp).2 (by
        obtain ⟨e, he, hec⟩ := Wup_Un_bd hg hbar.2 hxp h1 (hUn x.1 hxp hx)
        grind),
      (Vtx_iff_corners hyp).2 (by
        obtain ⟨e, he, hec⟩ := Wup_Un_bd hg hbar.2 hyp h2 (hUn y.1 hyp hy)
        grind)⟩

end Rect

end PottsDiscontinuity.TorusCrossing
