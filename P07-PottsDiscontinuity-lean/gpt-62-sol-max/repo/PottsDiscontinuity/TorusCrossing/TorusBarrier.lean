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
  have := shiftRCConfig_nxt (dualConfig A) (periodicCoordinate hNp i, periodicCoordinate hMp j)
  exact this

theorem dualEnds_fst_row (m : Cell) : (dualEnds m).1.2 = m.2 := by
  unfold dualEnds; split_ifs <;> rfl

theorem dualEnds_snd_row (m : Cell) : (dualEnds m).2.2 = m.2 - 1 := by
  unfold dualEnds; split_ifs <;> rfl

/-- The primal-coloured vertex obtained from a dual cell by the unit horizontal translation. -/
def toRVd (z : Cell) (hz : ¬ IsPrimal z) : RotatedVertex :=
  ⟨(z.1 + 1, z.2), by
    unfold IsPrimal at hz
    exact Int.even_iff.2 (by dsimp only; omega)⟩

theorem rotAdj_dualEnds (m : Cell) :
    rotatedLattice.Adj (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) := by
  unfold toRVd dualEnds
  change |_| = 1 ∧ |_| = 1
  by_cases h : (m.1 + m.2) % 2 = 0
  · simp only [h, ite_true]
    constructor <;> rw [abs_eq (by norm_num)] <;> omega
  · simp only [h, ite_false]
    constructor <;> rw [abs_eq (by norm_num)] <;> omega

theorem liftedEdgeIndex_dualEnds (hNp : 0 < N) (hMp : 0 < M) (m : Cell) :
    liftedEdgeIndex hNp hMp (toRVd (dualEnds m).1 (dualEnds_fst_not_primal m))
      (toRVd (dualEnds m).2 (dualEnds_snd_not_primal m)) =
      (periodicCoordinate hNp (m.1 + 1), periodicCoordinate hMp m.2) := by
  unfold liftedEdgeIndex toRVd dualEnds
  by_cases h : (m.1 + m.2) % 2 = 0
  · simp only [h, ite_true]
    rw [max_eq_right (by omega), max_eq_left (by omega)]
  · simp only [h, ite_false]
    rw [max_eq_left (by omega), max_eq_left (by omega)]

theorem dual_adj_oriented (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (a b : ℤ)
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
  · rw [liftedEdgeIndex_dualEnds, translatedDual_at, hAm]; rfl
  · change a ≤ (dualEnds m).1.1 + 1; omega
  · change (dualEnds m).1.1 + 1 ≤ b; omega
  · change a ≤ (dualEnds m).2.1 + 1; omega
  · change (dualEnds m).2.1 + 1 ≤ b; omega

section

variable (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M)

/-- A dual-open path (avoiding the open edges of the board) joining a low face to a high face
gives a lifted vertical crossing of the translated complementary configuration. -/
theorem dual_to_vCross (n : ℕ)
    (hn : 0 < n) (a ρ : ℤ) (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    {S : Finset Cell} (hS : S ⊆ Q.inner) (hSA : ∀ m ∈ S, m ∉ boardOf Q hNp hMp A) {p t : Cell}
    (hpath : Relation.ReflTransGen (StepRel dualEnds S) p t) (hp : p.2 ≤ ρ) (ht : ρ + n ≤ t.2) :
    vCross hNp hMp n a ρ (translatedDualConfig A) := by
  exact stepRel_to_vCross hNp hMp n hn a ρ (translatedDualConfig A) toRVd (fun _ _ => rfl) dualEnds
    (fun m _ => ⟨dualEnds_fst_not_primal m, dualEnds_snd_not_primal m⟩)
    (fun m _ => by rw [dualEnds_fst_row, dualEnds_snd_row]; omega)
    (fun m hm => dual_adj_oriented hNp hMp Q A _ _ hcol (hS hm) (hSA m hm)) hpath hp ht

end

theorem notBar_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M)
    (s : Side) {b n : ℕ} (hb : b ≤ Q.h) (hn : 0 < n) (a ρ : ℤ)
    (hcol : a ≤ Q.x0 + 1 ∧ Q.x0 + Q.w + 1 ≤ a + 3 * (n : ℤ))
    (hρ1 : (Q.endBoard s b).y0 ≤ ρ) (hρ2 : ρ + n ≤ (Q.endBoard s b).y0 + b)
    (hbar : ¬ Q.hasBarrier s b (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ (translatedDualConfig A) := by
  unfold Rect.hasBarrier at hbar
  push Not at hbar
  obtain ⟨t, ht, htD⟩ := hbar
  obtain ⟨_, p, hp, hpath⟩ := (Q.endBoard s b).mem_expD.1 htD
  have hp2 := ((Q.endBoard s b).faceRow_mem.1 hp).2
  have ht2 := ((Q.endBoard s b).faceRow_mem.1 ht).2
  have hi : (Q.endBoard s b).inner \ boardOf Q hNp hMp A ⊆ Q.inner :=
    Finset.sdiff_subset.trans (Rect.endBoard_inner_subset s hb)
  have hc : ∀ m ∈ (Q.endBoard s b).inner \ boardOf Q hNp hMp A, m ∉ boardOf Q hNp hMp A :=
    fun _ hm => (Finset.mem_sdiff.1 hm).2
  cases s <;> simp [Rect.endBoard, Rect.outerRow, Rect.innerRow] at hp2 ht2 hρ1 hρ2
  · exact dual_to_vCross hNp hMp Q A n hn a ρ hcol hi hc hpath (by omega) (by omega)
  · exact dual_to_vCross hNp hMp Q A n hn a ρ hcol hi hc (symm hpath) (by omega) (by omega)

end PottsDiscontinuity.TorusCrossing
