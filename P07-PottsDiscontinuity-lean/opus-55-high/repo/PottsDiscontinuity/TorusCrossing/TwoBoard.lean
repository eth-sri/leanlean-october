module

public import PottsDiscontinuity.TorusCrossing.ExploreLocal

/-!
# Two explorations in the two ends of a board

A board `Q` contains a bottom sub-board `B` (height `bB`) and a top sub-board `T` (height `bT`),
with at least one row of gap.  From the bottom of `B` and from the top of `T` we explore the
dual cluster of the port row; the explored regions are vertex-disjoint.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

/-- Bottom sub-board of height `bB`. -/
def botB (Q : Rect) (bB : ℕ) : Rect := ⟨Q.x0, Q.y0, Q.w, bB⟩

/-- Top sub-board of height `bT`. -/
def topT (Q : Rect) (bT : ℕ) : Rect := ⟨Q.x0, Q.y0 + Q.h - bT, Q.w, bT⟩

section
variable (Q : Rect) (bB : ℕ)
include Q
@[simp] theorem botB_x0  : (Q.botB bB).x0 = Q.x0 := rfl
@[simp] theorem botB_y0  : (Q.botB bB).y0 = Q.y0 := rfl
@[simp] theorem botB_w  : (Q.botB bB).w = Q.w := rfl
@[simp] theorem botB_h  : (Q.botB bB).h = bB := rfl
end
section
variable (Q : Rect) (bT : ℕ)
include Q
@[simp] theorem topT_x0  : (Q.topT bT).x0 = Q.x0 := rfl
@[simp] theorem topT_y0  : (Q.topT bT).y0 = Q.y0 + Q.h - bT := rfl
@[simp] theorem topT_w  : (Q.topT bT).w = Q.w := rfl
@[simp] theorem topT_h  : (Q.topT bT).h = bT := rfl
end

/-- Explored medial vertices in the bottom sub-board. -/
def exB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.botB bB).expRm Q.y0 (Q.y0 + bB) A

/-- Explored medial vertices in the top sub-board. -/
def exT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.topT bT).expRm (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A

/-- Boundary of the exploration in the bottom sub-board. -/
def bdB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.botB bB).expBd Q.y0 (Q.y0 + bB) A

/-- Boundary of the exploration in the top sub-board. -/
def bdT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.topT bT).expBd (Q.y0 + Q.h) (Q.y0 + Q.h - bT) A

/-- No dual path joins the bottom row of `B` to its top row. -/
def barB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Prop :=
  ∀ t ∈ (Q.botB bB).faceRow (Q.y0 + bB), t ∉ (Q.botB bB).expD Q.y0 A

/-- No dual path joins the top row of `T` to its bottom row. -/
def barT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Prop :=
  ∀ t ∈ (Q.topT bT).faceRow (Q.y0 + Q.h - bT), t ∉ (Q.topT bT).expD (Q.y0 + Q.h) A

/-- The union of the two explored regions. -/
def exAll (Q : Rect) (bB bT : ℕ) (A : Finset Cell) : Finset Cell :=
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
  grind [botB_x0, botB_y0, botB_w, botB_h]

theorem topT_inner_subset (Q : Rect) (bT : ℕ) (h : bT ≤ Q.h) : (Q.topT bT).inner ⊆ Q.inner := by
  intro m hm
  rw [Rect.mem_inner] at hm ⊢
  grind [topT_x0, topT_y0, topT_w, topT_h]

section
variable (A : Finset Cell)
theorem exB_subset_inner (h : bB ≤ Q.h) : Q.exB bB A ⊆ Q.inner := by
  intro m hm
  exact botB_inner_subset Q bB h (((mem_expRm_iff).1 hm).1)

theorem exT_subset_inner (h : bT ≤ Q.h) : Q.exT bT A ⊆ Q.inner := by
  intro m hm
  exact topT_inner_subset Q bT h (((mem_expRm_iff).1 hm).1)

theorem exAll_subset_inner (hg : Q.Geo bB bT) : Q.exAll bB bT A ⊆ Q.inner := by
  intro m hm
  rcases Finset.mem_union.1 hm with h | h
  · exact exB_subset_inner A (by have := hg.hgap; omega) h
  · exact exT_subset_inner A (by have := hg.hgap; omega) h
end

section
variable {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A)
include h
/-- Stopping property of the two explorations. -/
theorem exAll_stop  :
    (Q.botB bB).expD Q.y0 A' = (Q.botB bB).expD Q.y0 A ∧
      (Q.topT bT).expD (Q.y0 + Q.h) A' = (Q.topT bT).expD (Q.y0 + Q.h) A := by
  constructor <;> [apply expD_stop (p₂ := Q.y0 + bB); apply expD_stop (p₂ := Q.y0 + Q.h - bT)] <;>
    ext x <;> have := congrArg (x ∈ ·) h <;> simp [exAll, exB, exT] at this ⊢ <;> grind

theorem exAll_congr  :
    Q.exAll bB bT A' = Q.exAll bB bT A ∧ Q.exB bB A' = Q.exB bB A ∧ Q.exT bT A' = Q.exT bT A ∧
      Q.bdB bB A' = Q.bdB bB A ∧ Q.bdT bT A' = Q.bdT bT A ∧
      (Q.barB bB A' ↔ Q.barB bB A) ∧ (Q.barT bT A' ↔ Q.barT bT A) := by
  obtain ⟨hB, hT⟩ := exAll_stop h
  have e1 : Q.exB bB A' = Q.exB bB A := (Q.botB bB).expRm_congr hB
  have e2 : Q.exT bT A' = Q.exT bT A := (Q.topT bT).expRm_congr hT
  refine ⟨?_, e1, e2, (Q.botB bB).expBd_congr hB, (Q.topT bT).expBd_congr hT, ?_, ?_⟩
  · simp_all [exAll]
  · simp_all [barB]
  simp_all [barT]
end

/-- A cell is an end of the primal edge of some medial vertex of `S`. -/
def Vtx (S : Finset Cell) (c : Cell) : Prop :=
  ∃ e ∈ S, c = (primalEnds e).1 ∨ c = (primalEnds e).2

section
variable (e : Cell)
theorem primalEnds_fst_row  : (primalEnds e).1.2 = e.2 := by
  unfold primalEnds; grind

theorem primalEnds_snd_row  : (primalEnds e).2.2 = e.2 - 1 := by
  unfold primalEnds; grind
end

theorem Vtx_primal {S : Finset Cell} {c : Cell} : Vtx S c → IsPrimal c := by
  rintro ⟨m, -, rfl | rfl⟩; exacts [primalEnds_fst_primal m, primalEnds_snd_primal m]

theorem Vtx_iff_corners {S : Finset Cell} {c : Cell} (hc : IsPrimal c) :
    Vtx S c ↔ ∃ e ∈ corners c, e ∈ S := by
  constructor
  · rintro ⟨e, he, h⟩; exact ⟨e, (mem_primalEnds_iff c e hc).1 h, he⟩
  · rintro ⟨e, h, he⟩; exact ⟨e, he, (mem_primalEnds_iff c e hc).2 h⟩

theorem Vtx_mono {S S' : Finset Cell} (h : S ⊆ S') {c : Cell} (hc : Vtx S c) : Vtx S' c := by
  obtain ⟨e, he, h'⟩ := hc; exact ⟨e, h he, h'⟩

section
variable {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell} (hc : Vtx S c)
include R S hS c hc
theorem Vtx_row_of_inner  :
    R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  obtain ⟨e, he, h⟩ := hc
  have := Rect.mem_inner.1 (hS he)
  rcases h with rfl | rfl
  · grind [primalEnds_fst_row]
  · rw [primalEnds_snd_row]; omega

theorem Vtx_mem_pcells  : c ∈ R.pcells := by
  obtain ⟨e, he, h⟩ := hc
  have hd := R.pData.mem e (hS he)
  grind
end

/-- Cells on the lower side of the explored region of `B` (or on the bottom row). -/
def Wlow (Q : Rect) (bB : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.exB bB A) c ∨ c.2 = Q.y0

/-- Cells on the upper side of the explored region of `T` (or on the top row). -/
def Wup (Q : Rect) (bT : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.exT bT A) c ∨ c.2 = Q.y0 + Q.h

section
variable {A : Finset Cell} {c : Cell}
theorem Vtx_exB_row (hc : Vtx (Q.exB bB A) c) :
    Q.y0 ≤ c.2 ∧ c.2 ≤ Q.y0 + bB := by
  have := Vtx_row_of_inner (fun m hm => ((mem_expRm_iff).1 hm).1) hc
  simp_all

theorem Vtx_exT_row (hc : Vtx (Q.exT bT A) c) :
    Q.y0 + Q.h - bT ≤ c.2 ∧ c.2 ≤ Q.y0 + Q.h := by
  have := Vtx_row_of_inner (fun m hm => ((mem_expRm_iff).1 hm).1) hc
  simp_all

theorem Wlow_row (hc : Q.Wlow bB A c) : Q.y0 ≤ c.2 ∧ c.2 ≤ Q.y0 + bB := by
  rcases hc with h | h; exacts [Vtx_exB_row h, by omega]

theorem Wup_row (hc : Q.Wup bT A c) : Q.y0 + Q.h - bT ≤ c.2 ∧ c.2 ≤ Q.y0 + Q.h := by
  rcases hc with h | h; exacts [Vtx_exT_row h, by omega]
end

section
variable (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell}
include hg
theorem Wlow_Wup_disjoint (h1 : Q.Wlow bB A c) (h2 : Q.Wup bT A c) : False := by
  have := (Wlow_row h1).2
  have := (Wup_row h2).1
  have := hg.hgap
  omega
end

section
variable {A : Finset Cell} {m : Cell}
theorem exB_ends_Wlow (hm : m ∈ Q.exB bB A) :
    Q.Wlow bB A (primalEnds m).1 ∧ Q.Wlow bB A (primalEnds m).2 :=
  ⟨Or.inl ⟨m, hm, Or.inl rfl⟩, Or.inl ⟨m, hm, Or.inr rfl⟩⟩

theorem exT_ends_Wup (hm : m ∈ Q.exT bT A) :
    Q.Wup bT A (primalEnds m).1 ∧ Q.Wup bT A (primalEnds m).2 :=
  ⟨Or.inl ⟨m, hm, Or.inl rfl⟩, Or.inl ⟨m, hm, Or.inr rfl⟩⟩

theorem exAll_ends (hm : m ∈ Q.exAll bB bT A) :
    (Q.Wlow bB A (primalEnds m).1 ∧ Q.Wlow bB A (primalEnds m).2) ∨
      (Q.Wup bT A (primalEnds m).1 ∧ Q.Wup bT A (primalEnds m).2) := by
  rcases Finset.mem_union.1 hm with h | h
  · exact Or.inl (exB_ends_Wlow h)
  simp [exT_ends_Wup, h]
end

theorem corner_coords {c e : Cell} (he : e ∈ corners c) :
    (e.1 = c.1 ∨ e.1 = c.1 + 1) ∧ (e.2 = c.2 ∨ e.2 = c.2 + 1) := by
  unfold corners at he
  grind

theorem cell_mem_pcells_of_corner {R : Rect} {c e : Cell} (hc : IsPrimal c) (he : e ∈ corners c)
    (hein : e ∈ R.inner) : c ∈ R.pcells :=
  Vtx_mem_pcells (Finset.singleton_subset_iff.2 hein)
    ⟨e, Finset.mem_singleton_self e, (mem_primalEnds_iff c e hc).2 he⟩

theorem W_Un_bd {R : Rect} {p₁ p₂ : ℤ} {A : Finset Cell}
    (hR : R.x0 = Q.x0 ∧ R.w = Q.w ∧ Q.y0 ≤ R.y0 ∧ R.y0 + R.h ≤ Q.y0 + Q.h) (hh : 0 < R.h)
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h ∧ p₁ = Q.y0) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0 ∧ p₁ = Q.y0 + Q.h))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) {c : Cell}
    (hW : Vtx (R.expRm p₁ p₂ A) c ∨ c.2 = p₁) (hUn : Vtx (Q.inner \ R.expRm p₁ p₂ A) c) :
    Vtx (R.expBd p₁ p₂ A) c := by
  have hc := Vtx_primal hUn
  obtain ⟨e', he', hQ⟩ := (Vtx_iff_corners hc).1 hUn
  obtain ⟨hQ, hne'⟩ := Finset.mem_sdiff.1 hQ
  refine (Vtx_iff_corners hc).2 ?_
  have hcQ := Rect.mem_cells.1 (Rect.mem_pcells.1 (cell_mem_pcells_of_corner hc he' hQ)).1
  have hcr : R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
    rcases hW with h | h
    exacts [Vtx_row_of_inner (fun m hm => ((mem_expRm_iff).1 hm).1) h, by omega]
  have hcB : c ∈ R.pcells := by
    rw [Rect.mem_pcells, Rect.mem_cells]
    grind
  rcases hW with ⟨e1, hv1, hv1'⟩ | hrow
  · refine Rect.vex_vun hh (by omega) hb Q.inner (fun c hcc hne e he hein => ?_) hcB
      ⟨e1, (mem_primalEnds_iff c e1 hc).1 hv1', hv1⟩ ⟨e', he', hQ, hne'⟩
    have := Rect.mem_cells.1 (Rect.mem_pcells.1 hcc).1
    have := corner_coords he
    have := Rect.mem_inner.1 hein
    rw [Rect.mem_inner]
    grind
  · have := corner_coords he'
    have := Rect.mem_inner.1 hQ
    exact (hne' (Rect.corner_expRm_of_row_p1 hcB hrow he' (by rw [Rect.mem_inner]; grind))).elim

section
variable (hg : Q.Geo bB bT) {A : Finset Cell}
include hg
theorem Wlow_Un_bd (hbar : Q.barB bB A) {c : Cell} (hW : Q.Wlow bB A c)
    (hUn : Vtx (Q.inner \ Q.exAll bB bT A) c) : Vtx (Q.bdB bB A) c :=
  W_Un_bd (by simp; grind [hg.hgap]) hg.hbB (by simp) hbar hW
    (Vtx_mono (Finset.sdiff_subset_sdiff le_rfl Finset.subset_union_left) hUn)

theorem Wup_Un_bd (hbar : Q.barT bT A) {c : Cell} (hW : Q.Wup bT A c)
    (hUn : Vtx (Q.inner \ Q.exAll bB bT A) c) : Vtx (Q.bdT bT A) c :=
  W_Un_bd (by simp; grind [hg.hgap]) hg.hbT (by simp) hbar hW
    (Vtx_mono (Finset.sdiff_subset_sdiff le_rfl Finset.subset_union_right) hUn)
end

section
variable {S : Finset Cell}
theorem step_ends {z z' : Cell} (h : StepRel primalEnds S z z') :
    ∃ m ∈ S, (z = (primalEnds m).1 ∧ z' = (primalEnds m).2) ∨
      (z = (primalEnds m).2 ∧ z' = (primalEnds m).1) := by
  obtain ⟨m, hm, h⟩ := h
  aesop

theorem step_of_mem {m : Cell} (hm : m ∈ S) :
    StepRel primalEnds S (primalEnds m).1 (primalEnds m).2 := ⟨m, hm, Or.inl rfl⟩
end

theorem bdB_subset_exB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Q.bdB bB A ⊆ Q.exB bB A :=
  expBd_subset_expRm _ _ _

theorem bdT_subset_exT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Q.bdT bT A ⊆ Q.exT bT A :=
  expBd_subset_expRm _ _ _

theorem Vtx_connected {S : Finset Cell} (hc : ∀ {m m'}, m ∈ S → m' ∈ S →
    Relation.ReflTransGen (StepRel primalEnds S) (primalEnds m).1 (primalEnds m').1) {x y : Cell}
    (hx : Vtx S x) (hy : Vtx S y) : Relation.ReflTransGen (StepRel primalEnds S) x y := by
  obtain ⟨m, hm, hxm | hxm⟩ := hx <;> obtain ⟨m', hm', hym | hym⟩ := hy <;> subst hxm hym <;>
    grind [Relation.ReflTransGen.single (stepRel_symm (step_of_mem hm)),
      Relation.ReflTransGen.single (step_of_mem hm'), Relation.ReflTransGen.trans]

section
variable (hg : Q.Geo bB bT)
include hg
/-- The key topological consequence of the local analysis: an open path from the bottom row to the
top row of `Q`, in a configuration containing all explored edges, yields a path from the boundary
of the lower exploration to the boundary of the upper exploration which uses only unexplored open
edges and boundary edges. -/
theorem cross_to_success {A₀ A : Finset Cell} (hbar : Q.barAll bB bT A₀)
    (hA : A ⊆ Q.inner) {u v : Cell} (hu : u.2 = Q.y0)
    (hv : v.2 = Q.y0 + Q.h)
    (hpath : Relation.ReflTransGen (StepRel primalEnds A) u v) :
    ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
      Relation.ReflTransGen (StepRel primalEnds
        ((A \ Q.exAll bB bT A₀) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y := by
  by_contra hS
  have hgap := hg.hgap
  set EX := Q.exAll bB bT A₀
  set D := (A \ EX) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀
  have hW' : ∀ x, Vtx (Q.bdB bB A₀) x → ∀ z, Relation.ReflTransGen (StepRel primalEnds D) x z →
      ¬ Q.Wup bT A₀ z := by
    intro x hx z hxz hW
    induction hxz with
    | refl => exact Wlow_Wup_disjoint hg (.inl (Vtx_mono (bdB_subset_exB Q bB A₀) hx)) hW
    | @tail b c hbx hstep ih =>
      obtain ⟨m, hm, hc⟩ := step_ends hstep
      have hcend : c = (primalEnds m).1 ∨ c = (primalEnds m).2 := by grind
      rcases Finset.mem_union.1 hm with hm | hm
      rcases Finset.mem_union.1 hm with hm | hm
      · exact hS ⟨x, c, hx, Wup_Un_bd hg hbar.2 hW
          ⟨m, Finset.sdiff_subset_sdiff hA subset_rfl hm, hcend⟩, hbx.tail hstep⟩
      · exact Wlow_Wup_disjoint hg (.inl (Vtx_mono (bdB_subset_exB Q bB A₀) ⟨m, hm, hcend⟩)) hW
      · exact hS ⟨x, c, hx, ⟨m, hm, hcend⟩, hbx.tail hstep⟩
  have key : ∀ w, Relation.ReflTransGen (StepRel primalEnds A) u w → Q.Wlow bB A₀ w ∨
      ∃ x, Vtx (Q.bdB bB A₀) x ∧ Relation.ReflTransGen (StepRel primalEnds D) x w := by
    intro w hw
    induction hw with
    | refl => exact .inl (.inr hu)
    | @tail z z' _ hstep hz =>
      obtain ⟨m, hm, hmeq⟩ := hstep
      have hzend : z = (primalEnds m).1 ∨ z = (primalEnds m).2 := by grind
      by_cases hmEX : m ∈ EX
      · rcases Finset.mem_union.1 hmEX with hB | hT
        · have := exB_ends_Wlow hB
          grind
        · have hT' := exT_ends_Wup hT
          have hWz : Q.Wup bT A₀ z := by grind
          rcases hz with hlz | ⟨x, hx, hxz⟩
          exacts [(Wlow_Wup_disjoint hg hlz hWz).elim, (hW' x hx z hxz hWz).elim]
      · have hmD := Finset.mem_sdiff.2 ⟨hm, hmEX⟩
        have hstepD : StepRel primalEnds D z z' := ⟨m, Finset.mem_union_left _ (Finset.mem_union_left _ hmD), hmeq⟩
        rcases hz with hlz | ⟨x, hx, hxz⟩
        · exact .inr ⟨z, Wlow_Un_bd hg hbar.1 hlz
            ⟨m, Finset.sdiff_subset_sdiff hA subset_rfl hmD, hzend⟩, .single hstepD⟩
        · exact .inr ⟨x, hx, hxz.tail hstepD⟩
  rcases key v hpath with hl | ⟨x, hx, hxv⟩
  · have := Wlow_row hl; omega
  · exact hW' x hx v hxv (.inr hv)

theorem Vtx_bdB_connected {A : Finset Cell} (hbar : Q.barB bB A) {x y : Cell} :
    Vtx (Q.bdB bB A) x → Vtx (Q.bdB bB A) y →
    Relation.ReflTransGen (StepRel primalEnds (Q.bdB bB A)) x y :=
  Vtx_connected ((Q.botB bB).bd_connected hg.hbB hg.hw (Or.inl ⟨rfl, rfl⟩) hbar)

theorem Vtx_bdT_connected {A : Finset Cell} (hbar : Q.barT bT A) {x y : Cell} :
    Vtx (Q.bdT bT A) x → Vtx (Q.bdT bT A) y →
    Relation.ReflTransGen (StepRel primalEnds (Q.bdT bT A)) x y :=
  Vtx_connected ((Q.topT bT).bd_connected hg.hbT hg.hw (Or.inr ⟨by simp, rfl⟩) hbar)
end


/-- The equivalence relation whose classes are the lower side, the upper side and singletons. -/
def sideSetoid (hg : Q.Geo bB bT) (A₀ : Finset Cell) : Setoid Q.pcells where
  r a b := a = b ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ b.1) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ b.1)
  iseqv :=
    { refl := fun a => Or.inl rfl
      symm := by
        grind
      trans := by
        rintro a b c (h | h | h) (h' | h' | h') <;> grind [Wlow_Wup_disjoint] }

section
variable (hg : Q.Geo bB bT)
include hg
theorem componentSetoid_le_side (A₀ : Finset Cell) :
    FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀)) ≤ sideSetoid hg A₀ := by
  apply FK.componentSetoid_le
  · intro a b hab
    rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData _ (exAll_subset_inner A₀ hg)] at hab
    have key : ∀ z, Relation.ReflTransGen (StepRel primalEnds (Q.exAll bB bT A₀)) a.1 z →
        z = a.1 ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ z) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ z) := by
      intro z hz
      induction hz with
      | refl => simp
      | @tail b c _ hstep ih =>
        obtain ⟨m, hm, hmeq⟩ := step_ends hstep
        rcases exAll_ends hm with hl | hu <;> grind [Wlow_Wup_disjoint]
    exact (key b.1 hab).imp_left fun h => Subtype.ext h.symm
  · rintro a b (h | h | h)
    exacts [.inl h, .inr (.inl ⟨.inr h.1, .inr h.2⟩), .inr (.inr ⟨.inr h.1, .inr h.2⟩)]

/-- **Boundary comparison at the cell level**: two cells seeing unexplored edges and related in the
partition induced by the sep-wiring and the explored edges are equal or lie on the same boundary. -/
theorem kc {A₀ : Finset Cell} (hbar : Q.barAll bB bT A₀) {x y : Q.pcells}
    (hx : Vtx (Q.inner \ Q.exAll bB bT A₀) x.1) (hy : Vtx (Q.inner \ Q.exAll bB bT A₀) y.1)
    (h : (FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀))).r x y) :
    x = y ∨ (Vtx (Q.bdB bB A₀) x.1 ∧ Vtx (Q.bdB bB A₀) y.1) ∨
      (Vtx (Q.bdT bT A₀) x.1 ∧ Vtx (Q.bdT bT A₀) y.1) := by
  rcases componentSetoid_le_side hg A₀ h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp_all
  · exact .inr (.inl ⟨Wlow_Un_bd hg hbar.1 h1 hx, Wlow_Un_bd hg hbar.1 h2 hy⟩)
  · exact .inr (.inr ⟨Wup_Un_bd hg hbar.2 h1 hx, Wup_Un_bd hg hbar.2 h2 hy⟩)
