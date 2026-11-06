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
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  apply Fin.ext
  apply Int.ofNat.inj
  change ((periodicCoordinate hp (z + 1)).val : ℤ) =
    ((finRotate (N' + 1) (periodicCoordinate hp z)).val : ℤ)
  rw [finRotate_apply, periodicCoordinate_val, Fin.val_add]
  push_cast
  rw [periodicCoordinate_val, Int.add_emod z 1]
  push_cast
  rfl

theorem translatedDual_at (A : RCConfig N M) (hNp : 0 < N) (hMp : 0 < M) (i j : ℤ) :
    translatedDualConfig A (periodicCoordinate hNp (i + 1), periodicCoordinate hMp j) =
      !(A (periodicCoordinate hNp i, periodicCoordinate hMp j)) := by
  rw [periodicCoordinate_succ]
  exact shiftRCConfig_nxt (dualConfig A) (periodicCoordinate hNp i, periodicCoordinate hMp j)

theorem dualEnds_fst_row (m : Cell) : (dualEnds m).1.2 = m.2 := by
  unfold dualEnds; split_ifs <;> rfl

theorem dualEnds_snd_row (m : Cell) : (dualEnds m).2.2 = m.2 - 1 := by
  unfold dualEnds; split_ifs <;> rfl

def toRVd (z : Cell) (hz : ¬ IsPrimal z) : RotatedVertex :=
  ⟨(z.1 + 1, z.2), Int.even_iff.2 (by unfold IsPrimal at hz; dsimp only; omega)⟩

theorem rotAdj_dualEnds (m : Cell) :
    rotatedLattice.Adj (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  unfold toRVd dualEnds
  change |_| = 1 ∧ |_| = 1
  split_ifs <;> refine ⟨?_, ?_⟩ <;> (dsimp; rw [abs_eq (by norm_num)]; omega)

theorem liftedEdgeIndex_dualEnds (hNp : 0 < N) (hMp : 0 < M) (m : Cell) :
    liftedEdgeIndex hNp hMp (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) =
      (periodicCoordinate hNp (m.1 + 1), periodicCoordinate hMp m.2) := by
  unfold liftedEdgeIndex toRVd dualEnds
  by_cases h : (m.1 + m.2) % 2 = 0 <;> simp only [h, ite_true, ite_false]
  · rw [max_eq_right (by omega), max_eq_left (by omega)]
  · rw [max_eq_left (by omega), max_eq_left (by omega)]

theorem dual_adj_oriented (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (a b : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ b) {m : Cell} (hmin : m ∈ Q.inner)
    (hmA : m ∉ boardOf Q hNp hMp A) :
    (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj
      (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  have hd := Q.dData.mem m hmin
  have h1 := Rect.mem_cells.1 (Rect.mem_dcells.1 hd.1).1
  have h2 := Rect.mem_cells.1 (Rect.mem_dcells.1 hd.2).1
  have hAm : A (periodicCoordinate hNp m.1, periodicCoordinate hMp m.2) = false :=
    Bool.eq_false_iff.2 fun hne => hmA (Finset.mem_filter.2 ⟨hmin, by simpa [toFin] using hne⟩)
  refine ⟨rotAdj_dualEnds m, by rw [liftedEdgeIndex_dualEnds, translatedDual_at, hAm]; rfl,
    ⟨by change a ≤ (dualEnds m).1.1 + 1; omega, by change (dualEnds m).1.1 + 1 ≤ b; omega⟩,
    ⟨by change a ≤ (dualEnds m).2.1 + 1; omega, by change (dualEnds m).2.1 + 1 ≤ b; omega⟩⟩

theorem rtg_to_walk_map {α β : Type*} (G : SimpleGraph β) (φ : α → β) (P : β → Prop)
    (S : α → α → Prop) (hS : ∀ p q, S p q → G.Adj (φ p) (φ q) ∧ P (φ p) ∧ P (φ q)) {x y : α}
    (h : Relation.ReflTransGen S x y) (hx : P (φ x)) :
    ∃ w : G.Walk (φ x) (φ y), ∀ z ∈ w.support, P z := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simpa using hx⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨hadj, _, hPc⟩ := hS b c hbc
    refine ⟨w.concat hadj, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_concat] at hz
    exact (List.mem_append.1 hz).elim (hw z) fun h => List.mem_singleton.1 h ▸ hPc

theorem dual_step_row {S : Finset Cell} {p q : Cell} (h : StepRel dualEnds S p q) :
    q.2 ≤ p.2 + 1 ∧ p.2 ≤ q.2 + 1 := by
  obtain ⟨m, _, h | h⟩ := h <;>
    have h1 := congrArg (fun z : Cell × Cell => z.1.2) h <;>
    have h2 := congrArg (fun z : Cell × Cell => z.2.2) h <;>
    simp only [dualEnds_fst_row, dualEnds_snd_row] at h1 h2 <;> omega

theorem notPrimal_of_dstep {S : Finset Cell} {x c : Cell} (h : StepRel dualEnds S x c) :
    ¬ IsPrimal x := by
  obtain ⟨m, _, h | h⟩ := h
  · simpa [h] using dualEnds_fst_not_primal m
  · simpa [h] using dualEnds_snd_not_primal m

theorem rtg_lift_dual {S : Finset Cell} (Φ : Cell → Prop) {x y : Cell}
    (h : Relation.ReflTransGen (fun p q => StepRel dualEnds S p q ∧ Φ p ∧ Φ q) x y)
    (hx : ¬ IsPrimal x) :
    ∃ hy : ¬ IsPrimal y, Relation.ReflTransGen
      (fun u v : {z : Cell // ¬ IsPrimal z} => StepRel dualEnds S u.1 v.1 ∧ Φ u.1 ∧ Φ v.1)
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hr⟩ := ih
    obtain ⟨⟨m, hm, hmeq⟩, hΦb, hΦc⟩ := hbc
    have hc : ¬ IsPrimal c := by
      rcases hmeq with h | h
      · simpa [h] using dualEnds_snd_not_primal m
      · simpa [h] using dualEnds_fst_not_primal m
    exact ⟨hc, hr.tail ⟨⟨m, hm, hmeq⟩, hΦb, hΦc⟩⟩

theorem dual_lifted_adj_of_step (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M)
    (a b : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ b) {S : Finset Cell}
    (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A)
    {u v : {z : Cell // ¬ IsPrimal z}} (h : StepRel dualEnds S u.1 v.1) :
    (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj (toRVd u.1 u.2) (toRVd v.1 v.2) := by
  obtain ⟨m, hm, h | h⟩ := h
  · rw [show toRVd u.1 u.2 = toRVd (dualEnds m).1 (dualEnds_fst_not_primal m) by
        congr 1; exact (congrArg Prod.fst h).symm,
      show toRVd v.1 v.2 = toRVd (dualEnds m).2 (dualEnds_snd_not_primal m) by
        congr 1; exact (congrArg Prod.snd h).symm]
    exact dual_adj_oriented hNp hMp Q A a b hcol (hS hm) (hSA m hm)
  · rw [show toRVd u.1 u.2 = toRVd (dualEnds m).2 (dualEnds_snd_not_primal m) by
        congr 1; exact (congrArg Prod.snd h).symm,
      show toRVd v.1 v.2 = toRVd (dualEnds m).1 (dualEnds_fst_not_primal m) by
        congr 1; exact (congrArg Prod.fst h).symm]
    exact (dual_adj_oriented hNp hMp Q A a b hcol (hS hm) (hSA m hm)).symm

theorem dual_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (n : ℕ)
    (hn : 0 < n) (a ρ : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    {S : Finset Cell} (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A) {p t : Cell}
    (hpath : Relation.ReflTransGen (StepRel dualEnds S) p t) (hp : p.2 ≤ ρ) (ht : ρ + n ≤ t.2) :
    vCross hNp hMp n a ρ (translatedDualConfig A) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ivt_path (StepRel dualEnds S) (fun c : Cell => c.2)
    (fun p q h => dual_step_row h) ρ n hpath hp ht
  have hxy' : Relation.ReflTransGen
      (fun p q => StepRel dualEnds S p q ∧ (ρ ≤ p.2 ∧ p.2 ≤ ρ + n) ∧ (ρ ≤ q.2 ∧ q.2 ≤ ρ + n)) x y :=
    Relation.ReflTransGen.mono (fun p q h => ⟨h.1, ⟨h.2.1, h.2.2.1⟩, ⟨h.2.2.2.1, h.2.2.2.2⟩⟩) x y hxy
  have hxp : ¬ IsPrimal x := by
    rcases Relation.ReflTransGen.cases_head hxy' with rfl | ⟨c, hc, _⟩
    · omega
    · exact notPrimal_of_dstep hc.1
  obtain ⟨hyp, hlift⟩ := rtg_lift_dual (S := S) (fun c : Cell => ρ ≤ c.2 ∧ c.2 ≤ ρ + n) hxy' hxp
  obtain ⟨w, hw⟩ := rtg_to_walk_map (liftedStripGraph hNp hMp (translatedDualConfig A) a
      (a + 3 * (n : ℤ)))
    (fun u : {z : Cell // ¬ IsPrimal z} => toRVd u.1 u.2)
    (fun z : RotatedVertex => ρ ≤ z.val.2 ∧ z.val.2 ≤ ρ + n)
    (fun u v : {z : Cell // ¬ IsPrimal z} => StepRel dualEnds S u.1 v.1 ∧
      (ρ ≤ u.1.2 ∧ u.1.2 ≤ ρ + n) ∧ (ρ ≤ v.1.2 ∧ v.1.2 ≤ ρ + n))
    (fun p q h => ⟨dual_lifted_adj_of_step hNp hMp Q A a (a + 3 * (n : ℤ)) hcol hS hSA h.1,
      h.2.1, h.2.2⟩) hlift ⟨by simp only [toRVd]; omega, by simp only [toRVd]; omega⟩
  exact ⟨toRVd x hxp, toRVd y hyp, by simpa [toRVd] using hx, by simpa [toRVd] using hy, w, hw⟩

theorem rtg_stepRel_symm {ends : Cell → Cell × Cell} {S : Finset Cell} {x y : Cell}
    (h : Relation.ReflTransGen (StepRel ends S) x y) :
    Relation.ReflTransGen (StepRel ends S) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.head (stepRel_symm hbc) ih

theorem notBarB_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ}
    (hg : Q.Geo bB bT) (n : ℕ) (hn : 0 < n) (a ρ : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    (hρ1 : Q.y0 ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + bB)
    (hbar : ¬ Q.barB bB (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.barB at hbar; push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.botB bB).mem_expD.1 htD
  have := ((Q.botB bB).faceRow_mem.1 hp).2
  have := ((Q.botB bB).faceRow_mem.1 ht).2
  exact dual_to_vCross hNp hMp Q A n hn a ρ hcol
    (Finset.sdiff_subset.trans (Rect.botB_inner_subset Q bB (by have := hg.hgap; omega)))
    (fun _ hm => (Finset.mem_sdiff.1 hm).2) hpath (by omega) (by omega)

theorem notBarT_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ}
    (hg : Q.Geo bB bT) (n : ℕ) (hn : 0 < n) (a ρ : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    (hρ1 : Q.y0 + Q.h - bT ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + Q.h)
    (hbar : ¬ Q.barT bT (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.barT at hbar; push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.topT bT).mem_expD.1 htD
  have := ((Q.topT bT).faceRow_mem.1 hp).2
  have := ((Q.topT bT).faceRow_mem.1 ht).2
  exact dual_to_vCross hNp hMp Q A n hn a ρ hcol
    (Finset.sdiff_subset.trans (Rect.topT_inner_subset Q bT (by have := hg.hgap; omega)))
    (fun _ hm => (Finset.mem_sdiff.1 hm).2) (rtg_stepRel_symm hpath) (by omega) (by omega)

end PottsDiscontinuity.TorusCrossing
