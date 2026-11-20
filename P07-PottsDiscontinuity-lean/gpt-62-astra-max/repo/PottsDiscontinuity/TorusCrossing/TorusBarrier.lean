module

public import PottsDiscontinuity.Torus.DiamondDualTranslation
public import PottsDiscontinuity.TorusCrossing.TorusEvents

/-!
# Failure of a barrier gives a vertical crossing of the translated dual configuration

A dual-open path of a board, joining the two port rows of a sub-board, becomes (after the
unit horizontal translation exchanging face colours) an open primal path of the translated
complementary configuration.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength PottsDiscontinuity.SixVertex
open scoped Classical

variable {N M : ℕ}

theorem periodicCoordinate_succ (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp (z + 1) = nxt (periodicCoordinate hp z) := by
  grind [finRotate_apply, periodicCoordinate_val, Fin.val_add, Int.add_emod z 1]

variable (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ} (hg : Q.Geo bB bT)
    (n : ℕ) (hn : 0 < n) (a ρ : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * n)
    {ends : Cell → Cell × Cell} {S : Finset Cell} (m : Cell) (Φ : Cell → Prop) {x y : Cell}

theorem translatedDual_at (hNp : 0 < N) (hMp : 0 < M) (i j : ℤ) :
    translatedDualConfig A (periodicCoordinate hNp (i + 1), periodicCoordinate hMp j) =
      !(A (periodicCoordinate hNp i, periodicCoordinate hMp j)) := by
  rw [periodicCoordinate_succ]
  have := shiftRCConfig_nxt (dualConfig A) (periodicCoordinate hNp i, periodicCoordinate hMp j)
  exact this

theorem dualEnds_fst_row : (dualEnds m).1.2 = m.2 := by
  grind [dualEnds]

theorem dualEnds_snd_row : (dualEnds m).2.2 = m.2 - 1 := by
  grind [dualEnds]

/-- The primal-coloured vertex obtained from a dual cell by the unit horizontal translation. -/
def toRVd (z : Cell) (hz : ¬ IsPrimal z) : RotatedVertex :=
  ⟨(z.1 + 1, z.2), by
    grind [IsPrimal, Int.even_iff]⟩

theorem rotAdj_dualEnds :
    rotatedLattice.Adj (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  unfold toRVd dualEnds
  change _ ∧ _
  grind

theorem liftedEdgeIndex_dualEnds :
    liftedEdgeIndex hNp hMp (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) =
      (periodicCoordinate hNp (m.1 + 1), periodicCoordinate hMp m.2) := by
  unfold liftedEdgeIndex toRVd dualEnds
  grind

theorem dual_adj_oriented (a b : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ b) {m : Cell} (hmin : m ∈ Q.inner)
    (hmA : m ∉ boardOf Q hNp hMp A) :
    (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj
      (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  have hd := Q.dData.mem m hmin
  have h1 := Rect.mem_cells.1 (Rect.mem_dcells.1 hd.1).1
  have h2 := Rect.mem_cells.1 (Rect.mem_dcells.1 hd.2).1
  have hAm : A (periodicCoordinate hNp m.1, periodicCoordinate hMp m.2) = false := by
    by_contra hne
    apply hmA
    exact Finset.mem_filter.2 ⟨hmin, by simpa [toFin] using hne⟩
  refine ⟨rotAdj_dualEnds m, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp [liftedEdgeIndex_dualEnds, translatedDual_at, hAm]
  · change a ≤ (dualEnds m).1.1 + 1; omega
  · change (dualEnds m).1.1 + 1 ≤ b; omega
  · change a ≤ (dualEnds m).2.1 + 1; omega
  · change (dualEnds m).2.1 + 1 ≤ b; omega

theorem rtg_to_walk_map {α β : Type*} {G : SimpleGraph β} {φ : α → β} {P : β → Prop}
    (S : α → α → Prop) (hS : ∀ p q, S p q → G.Adj (φ p) (φ q) ∧ P (φ p) ∧ P (φ q)) {x y : α}
    (h : Relation.ReflTransGen S x y) (hx : P (φ x)) :
    ∃ w : G.Walk (φ x) (φ y), ∀ z ∈ w.support, P z := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simpa using hx⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨hadj, hPb, hPc⟩ := hS b c hbc
    refine ⟨w.concat hadj, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_concat] at hz
    grind

theorem dual_step_row {p q : Cell} (h : StepRel dualEnds S p q) :
    q.2 ≤ p.2 + 1 ∧ p.2 ≤ q.2 + 1 := by
  obtain ⟨m, _, h⟩ := h
  rcases h with h | h
  · have h1 := congrArg (fun z : Cell × Cell => z.1.2) h
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h
    simp only [dualEnds_fst_row, dualEnds_snd_row] at h1 h2
    omega
  · have h1 := congrArg (fun z : Cell × Cell => z.1.2) h
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h
    simp only [dualEnds_fst_row, dualEnds_snd_row] at h1 h2
    omega

theorem notPrimal_of_dstep {x c : Cell} (h : StepRel dualEnds S x c) :
    ¬ IsPrimal x := by
  obtain ⟨m, _, h⟩ := h
  grind [dualEnds_fst_not_primal, dualEnds_snd_not_primal]

theorem rtg_lift_dual
    (h : Relation.ReflTransGen (fun p q => StepRel dualEnds S p q ∧ Φ p ∧ Φ q) x y)
    (hx : ¬ IsPrimal x) :
    ∃ hy, Relation.ReflTransGen
      (fun u v : {z : Cell // ¬ IsPrimal z} => StepRel dualEnds S u.1 v.1 ∧ Φ u.1 ∧ Φ v.1)
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => grind
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hr⟩ := ih
    obtain ⟨hstep, hΦb, hΦc⟩ := hbc
    obtain ⟨m, hm, hmeq⟩ := hstep
    exact ⟨(by grind [dualEnds_snd_not_primal, dualEnds_fst_not_primal]), hr.tail ⟨⟨m, hm, hmeq⟩, hΦb, hΦc⟩⟩

theorem dual_lifted_adj_of_step
    (a b : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ b) {S : Finset Cell}
    (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A)
    {u v : {z : Cell // ¬ IsPrimal z}} (h : StepRel dualEnds S u.1 v.1) :
    (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj (toRVd u.1 u.2) (toRVd v.1 v.2) := by
  obtain ⟨m, hm, hmeq⟩ := h
  rcases hmeq with h | h
  · grind [dual_adj_oriented]
  · have hu : toRVd u.1 u.2 = toRVd _ (dualEnds_snd_not_primal m) := by
      grind
    have hv : toRVd v.1 v.2 = toRVd _ (dualEnds_fst_not_primal m) := by
      grind
    rw [hu, hv]
    exact (dual_adj_oriented hNp hMp Q A a b hcol (hS hm) (hSA m hm)).symm

include hn hcol in
/-- A dual-open path (avoiding the open edges of the board) joining a low face to a high face
gives a lifted vertical crossing of the translated complementary configuration. -/
theorem dual_to_vCross (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A) {p t : Cell}
    (hpath : Relation.ReflTransGen (StepRel dualEnds S) p t) (hp : p.2 ≤ ρ) (ht : ρ + n ≤ t.2) :
    vCross hNp hMp n a ρ (translatedDualConfig A) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ivt_path _ _
    (fun p q h => dual_step_row h) ρ n hpath hp ht
  have hxy' : Relation.ReflTransGen
      (fun p q => StepRel dualEnds S p q ∧ (ρ ≤ p.2 ∧ p.2 ≤ ρ + n) ∧ (ρ ≤ q.2 ∧ q.2 ≤ ρ + n)) x y :=
    by grind
  have hxp : ¬ IsPrimal x := by
    grind [notPrimal_of_dstep]
  obtain ⟨hyp, hlift⟩ := rtg_lift_dual _ hxy' hxp
  obtain ⟨w, hw⟩ := rtg_to_walk_map
    (φ := (fun u : {z : Cell // ¬ IsPrimal z} => toRVd u.1 u.2))
    (P := (fun z : RotatedVertex => ρ ≤ z.val.2 ∧ z.val.2 ≤ ρ + n))
    _
    (fun p q h => ⟨dual_lifted_adj_of_step hNp hMp Q A a (a + 3 * (n : ℤ)) hcol hS hSA h.1,
      h.2.1, h.2.2⟩) hlift ⟨by grind [toRVd], by grind [toRVd]⟩
  exact ⟨toRVd x hxp, toRVd y hyp, by assumption, by assumption, w, hw⟩

theorem rtg_stepRel_symm
    (h : Relation.ReflTransGen (StepRel ends S) x y) :
    Relation.ReflTransGen (StepRel ends S) y x := Relation.ReflTransGen.rec Relation.ReflTransGen.refl (fun {b c} a hbc ih => Relation.ReflTransGen.head (stepRel_symm hbc) ih) h

include hg hn hcol in
theorem notBarB_to_vCross
    (hρ1 : Q.y0 ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + bB)
    (hbar : ¬ Q.barB bB (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.barB at hbar
  push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.botB bB).mem_expD.1 htD
  have hp2 := ((Q.botB bB).faceRow_mem.1 hp).2
  have ht2 := ((Q.botB bB).faceRow_mem.1 ht).2
  refine dual_to_vCross hNp hMp Q A n hn a ρ hcol (S := (Q.botB bB).inner \ boardOf Q hNp hMp A)
    ?_ ?_ hpath (by omega) (by omega)
  · exact Finset.sdiff_subset.trans (Rect.botB_inner_subset Q bB (by have := hg.hgap; omega))
  · grind

include hg hn hcol in
theorem notBarT_to_vCross
    (hρ1 : Q.y0 + Q.h - bT ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + Q.h)
    (hbar : ¬ Q.barT bT (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.barT at hbar
  push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.topT bT).mem_expD.1 htD
  have hp2 := ((Q.topT bT).faceRow_mem.1 hp).2
  have ht2 := ((Q.topT bT).faceRow_mem.1 ht).2
  refine dual_to_vCross hNp hMp Q A n hn a ρ hcol (S := (Q.topT bT).inner \ boardOf Q hNp hMp A)
    ?_ ?_ (rtg_stepRel_symm hpath) (by omega) (by omega)
  · exact Finset.sdiff_subset.trans (Rect.topT_inner_subset Q bT (by have := hg.hgap; omega))
  · grind

end PottsDiscontinuity.TorusCrossing
