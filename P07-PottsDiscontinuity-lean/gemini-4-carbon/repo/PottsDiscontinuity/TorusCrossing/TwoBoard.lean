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

theorem botB_inner_subset (Q : Rect) (bB : ℕ) (h : bB ≤ Q.h) : (Q.botB bB).inner ⊆ Q.inner := fun m hm => by
  rw [Rect.mem_inner] at hm ⊢; simp only [botB_x0, botB_y0, botB_w, botB_h] at hm; omega

theorem topT_inner_subset (Q : Rect) (bT : ℕ) (h : bT ≤ Q.h) : (Q.topT bT).inner ⊆ Q.inner := fun m hm => by
  rw [Rect.mem_inner] at hm ⊢; simp only [topT_x0, topT_y0, topT_w, topT_h] at hm; omega

theorem exAll_subset_inner (A : Finset Cell) (hg : Q.Geo bB bT) : Q.exAll bB bT A ⊆ Q.inner := fun m hm => by
  have := hg.hgap
  rcases Finset.mem_union.1 hm with h | h
  · exact botB_inner_subset Q bB (by omega) ((mem_expRm_iff.1 h).1)
  · exact topT_inner_subset Q bT (by omega) ((mem_expRm_iff.1 h).1)

theorem exAll_congr {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A) :
    Q.exAll bB bT A' = Q.exAll bB bT A ∧ Q.exB bB A' = Q.exB bB A ∧ Q.exT bT A' = Q.exT bT A ∧
      Q.bdB bB A' = Q.bdB bB A ∧ Q.bdT bT A' = Q.bdT bT A ∧
      (Q.barB bB A' ↔ Q.barB bB A) ∧ (Q.barT bT A' ↔ Q.barT bT A) := by
  have hsub_inter {S : Finset Cell} (hS : S ⊆ Q.exAll bB bT A) : A' ∩ S = A ∩ S := by
    ext x; simp only [Finset.mem_inter]
    exact ⟨fun ⟨hx1, hx2⟩ => ⟨(Finset.mem_inter.1 (h ▸ Finset.mem_inter.2 ⟨hx1, hS hx2⟩)).1, hx2⟩,
      fun ⟨hx1, hx2⟩ => ⟨(Finset.mem_inter.1 (h.symm ▸ Finset.mem_inter.2 ⟨hx1, hS hx2⟩)).1, hx2⟩⟩
  have hB := expD_stop (R := Q.botB bB) Q.y0 (Q.y0 + bB) (hsub_inter Finset.subset_union_left)
  have hT := expD_stop (R := Q.topT bT) (Q.y0 + Q.h) (Q.y0 + Q.h - bT) (hsub_inter Finset.subset_union_right)
  have e1 : Q.exB bB A' = Q.exB bB A := (Q.botB bB).expRm_congr hB
  have e2 : Q.exT bT A' = Q.exT bT A := (Q.topT bT).expRm_congr hT
  exact ⟨by unfold exAll; rw [e1, e2], e1, e2, (Q.botB bB).expBd_congr hB, (Q.topT bT).expBd_congr hT,
    by unfold barB; rw [hB], by unfold barT; rw [hT]⟩

/-- A cell is an end of the primal edge of some medial vertex of `S`. -/
def Vtx (S : Finset Cell) (c : Cell) : Prop :=
  ∃ e ∈ S, c = (primalEnds e).1 ∨ c = (primalEnds e).2

theorem primalEnds_fst_row (e : Cell) : (primalEnds e).1.2 = e.2 := by unfold primalEnds; split_ifs <;> rfl
theorem primalEnds_snd_row (e : Cell) : (primalEnds e).2.2 = e.2 - 1 := by unfold primalEnds; split_ifs <;> rfl

theorem Vtx_mem_pcells {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell} (hc : Vtx S c) :
    c ∈ R.pcells := by
  obtain ⟨e, he, rfl | rfl⟩ := hc <;> [exact (R.pData.mem e (hS he)).1; exact (R.pData.mem e (hS he)).2]

theorem step_of_mem {S : Finset Cell} {m : Cell} (hm : m ∈ S) :
    StepRel primalEnds S (primalEnds m).1 (primalEnds m).2 := ⟨m, hm, .inl rfl⟩

theorem bdB_subset_exB (Q : Rect) (bB : ℕ) (A : Finset Cell) : Q.bdB bB A ⊆ Q.exB bB A := expBd_subset_expRm _ _ _
theorem bdT_subset_exT (Q : Rect) (bT : ℕ) (A : Finset Cell) : Q.bdT bT A ⊆ Q.exT bT A := expBd_subset_expRm _ _ _

private theorem Vtx_iff_corners {S : Finset Cell} {c : Cell} (hc : IsPrimal c) :
    Vtx S c ↔ ∃ e ∈ S, e ∈ corners c :=
  ⟨fun ⟨e, he, h⟩ => ⟨e, he, (mem_primalEnds_iff c e hc).1 h⟩,
   fun ⟨e, he, h⟩ => ⟨e, he, (mem_primalEnds_iff c e hc).2 h⟩⟩

private theorem Vtx_row_of_inner {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell} (hc : Vtx S c) :
    R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  obtain ⟨e, he, rfl | rfl⟩ := hc <;> have := Rect.mem_inner.1 (hS he)
  · rw [primalEnds_fst_row]; omega
  · rw [primalEnds_snd_row]; omega

private def Wlow (Q : Rect) (bB : ℕ) (A : Finset Cell) (c : Cell) : Prop := Vtx (Q.exB bB A) c ∨ c.2 = Q.y0
private def Wup (Q : Rect) (bT : ℕ) (A : Finset Cell) (c : Cell) : Prop := Vtx (Q.exT bT A) c ∨ c.2 = Q.y0 + Q.h

private theorem Wlow_row (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell} (hc : Q.Wlow bB A c) : c.2 ≤ Q.y0 + bB := by
  rcases hc with h | h
  · simpa using (Vtx_row_of_inner (R := Q.botB bB) (fun _ hm => (mem_expRm_iff.1 hm).1) h).2
  · have := hg.hbB; omega

private theorem Wup_row (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell} (hc : Q.Wup bT A c) : Q.y0 + Q.h - bT ≤ c.2 := by
  rcases hc with h | h
  · have := (Vtx_row_of_inner (R := Q.topT bT) (fun _ hm => (mem_expRm_iff.1 hm).1) h).1
    simp only [topT_y0] at this; omega
  · have := hg.hbT; omega

private theorem Wlow_Wup_disjoint (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell}
    (h1 : Q.Wlow bB A c) (h2 : Q.Wup bT A c) : False := by
  have := Wlow_row hg h1; have := Wup_row hg h2; have := hg.hgap; omega

private theorem corner_coords {c e : Cell} (he : e ∈ corners c) :
    (e.1 = c.1 ∨ e.1 = c.1 + 1) ∧ (e.2 = c.2 ∨ e.2 = c.2 + 1) := by
  unfold corners at he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp

private theorem sub_Un_bd (R : Rect) (hh : 0 < R.h) (hx0 : R.x0 = Q.x0) (hw : R.w = Q.w)
    (p₁ p₂ : ℤ) (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    {A : Finset Cell} (hbar : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    (hamb : ∀ c ∈ R.pcells, c.2 ≠ p₂ → ∀ e ∈ corners c, e ∈ Q.inner → e ∈ R.inner)
    (hrow_in : ∀ c ∈ Q.pcells, ∀ e, c.2 = p₁ → e ∈ corners c → e ∈ Q.inner → e ∈ R.inner)
    {c : Cell} (hc : IsPrimal c) (hW : Vtx (R.expRm p₁ p₂ A) c ∨ c.2 = p₁)
    {e' : Cell} (he' : e' ∈ corners c) (hQ : e' ∈ Q.inner) (hex : e' ∉ R.expRm p₁ p₂ A) :
    ∃ e ∈ corners c, e ∈ R.expBd p₁ p₂ A := by
  have hcP : c ∈ Q.pcells := Vtx_mem_pcells (R := Q) (S := {e'})
    (Finset.singleton_subset_iff.2 hQ) ⟨e', Finset.mem_singleton_self e', (mem_primalEnds_iff c e' hc).2 he'⟩
  have hcQ := Rect.mem_cells.1 (Rect.mem_pcells.1 hcP).1
  rcases hW with hV | hrow
  · have hcr := Vtx_row_of_inner (R := R) (fun _ hm => (mem_expRm_iff.1 hm).1) hV
    have hcR : c ∈ R.pcells := by rw [Rect.mem_pcells, Rect.mem_cells]; refine ⟨⟨?_, ?_, hcr.1, hcr.2⟩, hc⟩ <;> omega
    obtain ⟨e1, hv1, hv1'⟩ := hV
    exact Rect.vex_vun hh hp hbar Q.inner hamb hcR ⟨e1, (mem_primalEnds_iff c e1 hc).1 hv1', hv1⟩ ⟨e', he', hQ, hex⟩
  · have hhℤ : (0 : ℤ) < R.h := by exact_mod_cast hh
    have hcR : c ∈ R.pcells := by rw [Rect.mem_pcells, Rect.mem_cells]; refine ⟨⟨?_, ?_, ?_, ?_⟩, hc⟩ <;> omega
    exact absurd (Rect.corner_expRm_of_row_p1 hcR hrow he' (hrow_in c hcP e' hrow he' hQ)) hex

private theorem Wlow_Un_bd (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barB bB A) {c : Cell}
    (hc : IsPrimal c) (hW : Q.Wlow bB A c) (hUn : ∃ e ∈ corners c, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A) :
    ∃ e ∈ corners c, e ∈ Q.bdB bB A := by
  obtain ⟨e', he', hQ, hne'⟩ := hUn
  have := hg.hbB; have := hg.hgap
  refine sub_Un_bd (Q := Q) (Q.botB bB) (by simpa using hg.hbB) rfl rfl Q.y0 (Q.y0 + bB) (.inl ⟨rfl, rfl⟩) hbar ?_ ?_ hc hW he' hQ
    (fun h => hne' (Finset.mem_union_left _ h))
  · intro d hd hne e he hein
    have hd' := Rect.mem_cells.1 (Rect.mem_pcells.1 hd).1; have hco := corner_coords he; have hi := Rect.mem_inner.1 hein
    rw [Rect.mem_inner]; simp only [botB_x0, botB_y0, botB_w, botB_h] at hd' hi ⊢; omega
  · intro d hd e hrow he hein
    have hd' := Rect.mem_cells.1 (Rect.mem_pcells.1 hd).1; have hco := corner_coords he; have hi := Rect.mem_inner.1 hein
    rw [Rect.mem_inner]; simp only [botB_x0, botB_y0, botB_w, botB_h] at *; omega

private theorem Wup_Un_bd (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barT bT A) {c : Cell}
    (hc : IsPrimal c) (hW : Q.Wup bT A c) (hUn : ∃ e ∈ corners c, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A) :
    ∃ e ∈ corners c, e ∈ Q.bdT bT A := by
  obtain ⟨e', he', hQ, hne'⟩ := hUn
  have := hg.hbT; have := hg.hgap
  refine sub_Un_bd (Q := Q) (Q.topT bT) (by simpa using hg.hbT) rfl rfl (Q.y0 + Q.h) (Q.y0 + Q.h - bT) (.inr ⟨by simp, rfl⟩) hbar ?_ ?_ hc hW he' hQ
    (fun h => hne' (Finset.mem_union_right _ h))
  · intro d hd hne e he hein
    have hd' := Rect.mem_cells.1 (Rect.mem_pcells.1 hd).1; have hco := corner_coords he; have hi := Rect.mem_inner.1 hein
    rw [Rect.mem_inner]; simp only [topT_x0, topT_y0, topT_w, topT_h] at hd' hi ⊢; omega
  · intro d hd e hrow he hein
    have hd' := Rect.mem_cells.1 (Rect.mem_pcells.1 hd).1; have hco := corner_coords he; have hi := Rect.mem_inner.1 hein
    rw [Rect.mem_inner]; simp only [topT_x0, topT_y0, topT_w, topT_h] at *; omega

/-- The key topological consequence of the local analysis: an open path from the bottom row to the
top row of `Q`, in a configuration containing all explored edges, yields a path from the boundary
of the lower exploration to the boundary of the upper exploration which uses only unexplored open
edges and boundary edges. -/
theorem cross_to_success (hg : Q.Geo bB bT) {A₀ A : Finset Cell} (hbar : Q.barAll bB bT A₀)
    (hA : A ⊆ Q.inner) {u v : Cell} (hu : u.2 = Q.y0) (hv : v.2 = Q.y0 + Q.h)
    (hpath : Relation.ReflTransGen (StepRel primalEnds A) u v) :
    ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
      Relation.ReflTransGen (StepRel primalEnds
        ((A \ Q.exAll bB bT A₀) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y := by
  by_contra hS
  set EX := Q.exAll bB bT A₀
  set D := (A \ EX) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀
  have hprim {m z : Cell} (hz : z = (primalEnds m).1 ∨ z = (primalEnds m).2) : IsPrimal z := by
    rcases hz with rfl | rfl <;> [exact primalEnds_fst_primal m; exact primalEnds_snd_primal m]
  have hUn {m z : Cell} (hm : m ∈ A \ EX) (hz : z = (primalEnds m).1 ∨ z = (primalEnds m).2) :
      ∃ e ∈ corners z, e ∈ Q.inner ∧ e ∉ EX :=
    ⟨m, (mem_primalEnds_iff z m (hprim hz)).1 hz, hA (Finset.mem_sdiff.1 hm).1, (Finset.mem_sdiff.1 hm).2⟩
  have hW' {x : Cell} (hx : Vtx (Q.bdB bB A₀) x) :
      ∀ z, Relation.ReflTransGen (StepRel primalEnds D) x z → ¬ Q.Wup bT A₀ z := by
    intro z hxz; induction hxz with
    | refl => exact fun hW => Wlow_Wup_disjoint hg (.inl ⟨hx.choose, bdB_subset_exB Q bB A₀ hx.choose_spec.1, hx.choose_spec.2⟩) hW
    | @tail b c hbx hstep _ =>
      intro hW
      rcases hstep with ⟨m, hm, hmeq⟩
      have hcend : c = (primalEnds m).1 ∨ c = (primalEnds m).2 := by
        rcases hmeq with h | h <;> [exact .inr (congrArg Prod.snd h).symm; exact .inl (congrArg Prod.fst h).symm]
      rcases Finset.mem_union.1 hm with hm1 | hm2
      · rcases Finset.mem_union.1 hm1 with hm11 | hm12
        · obtain ⟨e, he, hbd⟩ := Wup_Un_bd hg hbar.2 (hprim hcend) hW (hUn hm11 hcend)
          exact hS ⟨x, c, hx, (Vtx_iff_corners (hprim hcend)).2 ⟨e, hbd, he⟩, hbx.tail ⟨m, hm, hmeq⟩⟩
        · exact Wlow_Wup_disjoint hg (.inl ⟨m, bdB_subset_exB Q bB A₀ hm12, hcend⟩) hW
      · exact hS ⟨x, c, hx, ⟨m, hm2, hcend⟩, hbx.tail ⟨m, hm, hmeq⟩⟩
  let L (z : Cell) : Prop := Q.Wlow bB A₀ z ∨ ∃ x, Vtx (Q.bdB bB A₀) x ∧ Relation.ReflTransGen (StepRel primalEnds D) x z
  have key : ∀ w, Relation.ReflTransGen (StepRel primalEnds A) u w → L w := by
    intro w hw; induction hw with
    | refl => exact .inl (.inr hu)
    | @tail z z' _ hstep ih =>
      obtain ⟨m, hm, hmeq⟩ := hstep
      have hzend : z = (primalEnds m).1 ∨ z = (primalEnds m).2 := by
        rcases hmeq with h | h <;> [exact .inl (congrArg Prod.fst h).symm; exact .inr (congrArg Prod.snd h).symm]
      have hz'end : z' = (primalEnds m).1 ∨ z' = (primalEnds m).2 := by
        rcases hmeq with h | h <;> [exact .inr (congrArg Prod.snd h).symm; exact .inl (congrArg Prod.fst h).symm]
      by_cases hmEX : m ∈ EX
      · rcases Finset.mem_union.1 hmEX with hB | hT
        · exact .inl (.inl ⟨m, hB, hz'end⟩)
        · rcases ih with hlz | ⟨x, hx, hxz⟩
          · exact (Wlow_Wup_disjoint hg hlz (.inl ⟨m, hT, hzend⟩)).elim
          · exact (hW' hx z hxz (.inl ⟨m, hT, hzend⟩)).elim
      · have hmD : m ∈ A \ EX := Finset.mem_sdiff.2 ⟨hm, hmEX⟩
        have hstepD : StepRel primalEnds D z z' := ⟨m, Finset.mem_union_left _ (Finset.mem_union_left _ hmD), hmeq⟩
        rcases ih with hlz | ⟨x, hx, hxz⟩
        · obtain ⟨e, he, hbd⟩ := Wlow_Un_bd hg hbar.1 (hprim hzend) hlz (hUn hmD hzend)
          exact .inr ⟨z, (Vtx_iff_corners (hprim hzend)).2 ⟨e, hbd, he⟩, .single hstepD⟩
        · exact .inr ⟨x, hx, hxz.tail hstepD⟩
  rcases key v hpath with hl | ⟨x, hx, hxv⟩
  · have := Wlow_row hg hl; have := hg.hgap; omega
  · exact hW' hx v hxv (.inr hv)

private theorem Vtx_bd_conn_aux (R : Rect) (hh : 0 < R.h) (hw : 0 < R.w) (p₁ p₂ : ℤ)
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    {A : Finset Cell} (hbar : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {x y : Cell} (hx : Vtx (R.expBd p₁ p₂ A) x) (hy : Vtx (R.expBd p₁ p₂ A) y) :
    Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A)) x y := by
  obtain ⟨m, hm, hxm⟩ := hx; obtain ⟨m', hm', hym⟩ := hy
  have h1 : Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A)) x (primalEnds m).1 := by
    rcases hxm with rfl | rfl <;> [exact .refl; exact .single (stepRel_symm (step_of_mem hm))]
  have h2 : Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A)) (primalEnds m').1 y := by
    rcases hym with rfl | rfl <;> [exact .refl; exact .single (step_of_mem hm')]
  exact h1.trans ((R.bd_connected hh hw hp hbar hm hm').trans h2)

theorem Vtx_bdB_connected (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barB bB A) {x y : Cell}
    (hx : Vtx (Q.bdB bB A) x) (hy : Vtx (Q.bdB bB A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.bdB bB A)) x y :=
  Vtx_bd_conn_aux (Q.botB bB) (by simpa using hg.hbB) (by simpa using hg.hw) Q.y0 (Q.y0 + bB) (.inl ⟨rfl, rfl⟩) hbar hx hy

theorem Vtx_bdT_connected (hg : Q.Geo bB bT) {A : Finset Cell} (hbar : Q.barT bT A) {x y : Cell}
    (hx : Vtx (Q.bdT bT A) x) (hy : Vtx (Q.bdT bT A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.bdT bT A)) x y :=
  Vtx_bd_conn_aux (Q.topT bT) (by simpa using hg.hbT) (by simpa using hg.hw) (Q.y0 + Q.h) (Q.y0 + Q.h - bT) (.inr ⟨by simp, rfl⟩) hbar hx hy

private def sideSetoid (hg : Q.Geo bB bT) (A₀ : Finset Cell) : Setoid Q.pcells where
  r a b := a = b ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ b.1) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ b.1)
  iseqv :=
    { refl := fun _ => .inl rfl
      symm := by rintro a b (rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [exact .inl rfl; exact .inr (.inl ⟨h2, h1⟩); exact .inr (.inr ⟨h2, h1⟩)]
      trans := by
        rintro a b c (rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩) (rfl | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
        · exact .inl rfl
        · exact .inr (.inl ⟨h1', h2'⟩)
        · exact .inr (.inr ⟨h1', h2'⟩)
        · exact .inr (.inl ⟨h1, h2⟩)
        · exact .inr (.inl ⟨h1, h2'⟩)
        · exact (Wlow_Wup_disjoint hg h2 h1').elim
        · exact .inr (.inr ⟨h1, h2⟩)
        · exact (Wlow_Wup_disjoint hg h1' h2).elim
        · exact .inr (.inr ⟨h1, h2'⟩) }

/-- **Boundary comparison at the cell level**: two cells seeing unexplored edges and related in the
partition induced by the sep-wiring and the explored edges are equal or lie on the same boundary. -/
theorem kc (hg : Q.Geo bB bT) {A₀ : Finset Cell} (hbar : Q.barAll bB bT A₀) {x y : Q.pcells}
    (hx : Vtx (Q.inner \ Q.exAll bB bT A₀) x.1) (hy : Vtx (Q.inner \ Q.exAll bB bT A₀) y.1)
    (h : (FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀))).r x y) :
    x = y ∨ (Vtx (Q.bdB bB A₀) x.1 ∧ Vtx (Q.bdB bB A₀) y.1) ∨
      (Vtx (Q.bdT bT A₀) x.1 ∧ Vtx (Q.bdT bT A₀) y.1) := by
  have hle : FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀)) ≤ sideSetoid hg A₀ := by
    apply FK.componentSetoid_le
    · intro a b hab
      rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData _ (exAll_subset_inner A₀ hg)] at hab
      have key : ∀ z, Relation.ReflTransGen (StepRel primalEnds (Q.exAll bB bT A₀)) a.1 z →
          z = a.1 ∨ (Q.Wlow bB A₀ a.1 ∧ Q.Wlow bB A₀ z) ∨ (Q.Wup bT A₀ a.1 ∧ Q.Wup bT A₀ z) := by
        intro z hz; induction hz with
        | refl => exact .inl rfl
        | @tail b c _ hstep ih =>
          obtain ⟨m, hm, hmeq⟩ := hstep
          have hbend : b = (primalEnds m).1 ∨ b = (primalEnds m).2 := by
            rcases hmeq with h | h <;> [exact .inl (congrArg Prod.fst h).symm; exact .inr (congrArg Prod.snd h).symm]
          have hcend : c = (primalEnds m).1 ∨ c = (primalEnds m).2 := by
            rcases hmeq with h | h <;> [exact .inr (congrArg Prod.snd h).symm; exact .inl (congrArg Prod.fst h).symm]
          rcases Finset.mem_union.1 hm with hB | hT
          · rcases ih with rfl | ⟨h1, _⟩ | ⟨_, h2⟩
            · exact .inr (.inl ⟨.inl ⟨m, hB, hbend⟩, .inl ⟨m, hB, hcend⟩⟩)
            · exact .inr (.inl ⟨h1, .inl ⟨m, hB, hcend⟩⟩)
            · exact (Wlow_Wup_disjoint hg (.inl ⟨m, hB, hbend⟩) h2).elim
          · rcases ih with rfl | ⟨_, h2⟩ | ⟨h1, _⟩
            · exact .inr (.inr ⟨.inl ⟨m, hT, hbend⟩, .inl ⟨m, hT, hcend⟩⟩)
            · exact (Wlow_Wup_disjoint hg h2 (.inl ⟨m, hT, hbend⟩)).elim
            · exact .inr (.inr ⟨h1, .inl ⟨m, hT, hcend⟩⟩)
      rcases key b.1 hab with h1 | h1 | h1
      · exact .inl (Subtype.ext h1.symm)
      · exact .inr (.inl h1)
      · exact .inr (.inr h1)
    · intro a b hab
      rcases hab with h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl ⟨.inr h1.1, .inr h1.2⟩)
      · exact .inr (.inr ⟨.inr h1.1, .inr h1.2⟩)
  have hxp := (Rect.mem_pcells.1 x.2).2; have hyp := (Rect.mem_pcells.1 y.2).2
  have hUn {z : Cell} (hz : IsPrimal z) (hv : Vtx (Q.inner \ Q.exAll bB bT A₀) z) :
      ∃ e ∈ corners z, e ∈ Q.inner ∧ e ∉ Q.exAll bB bT A₀ := by
    obtain ⟨e, he, hec⟩ := (Vtx_iff_corners hz).1 hv
    exact ⟨e, hec, (Finset.mem_sdiff.1 he).1, (Finset.mem_sdiff.1 he).2⟩
  rcases hle h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl h1
  · obtain ⟨ex, hex, hbdx⟩ := Wlow_Un_bd hg hbar.1 hxp h1 (hUn hxp hx)
    obtain ⟨ey, hey, hbdy⟩ := Wlow_Un_bd hg hbar.1 hyp h2 (hUn hyp hy)
    exact .inr (.inl ⟨(Vtx_iff_corners hxp).2 ⟨ex, hbdx, hex⟩, (Vtx_iff_corners hyp).2 ⟨ey, hbdy, hey⟩⟩)
  · obtain ⟨ex, hex, hbdx⟩ := Wup_Un_bd hg hbar.2 hxp h1 (hUn hxp hx)
    obtain ⟨ey, hey, hbdy⟩ := Wup_Un_bd hg hbar.2 hyp h2 (hUn hyp hy)
    exact .inr (.inr ⟨(Vtx_iff_corners hxp).2 ⟨ex, hbdx, hex⟩, (Vtx_iff_corners hyp).2 ⟨ey, hbdy, hey⟩⟩)

end Rect

end PottsDiscontinuity.TorusCrossing
