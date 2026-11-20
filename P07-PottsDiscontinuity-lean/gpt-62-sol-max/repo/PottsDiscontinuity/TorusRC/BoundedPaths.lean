module

public import PottsDiscontinuity.Torus.RibbonAttachment
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Lifted paths avoiding the horizontal seam -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- An actual open path in the lifted horizontal strip, with every vertex
also constrained to the prescribed vertical interval. -/
def liftedBoundedConnection (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b lo hi : ℤ) (u v : RotatedVertex) : Prop :=
  ∃ w : (liftedStripGraph hNp hMp A a b).Walk u v,
    ∀ z ∈ w.support, lo ≤ z.val.2 ∧ z.val.2 ≤ hi

/-- Every edge of a nonnegative lifted path below height M avoids row zero
of the indexed torus. -/
theorem liftedEdgeIndex_row_ne_zero (hNp : 0 < N) (hMp : 0 < M)
    {u v : RotatedVertex} (huv : rotatedLattice.Adj u v)
    (hu : 0 ≤ u.val.2 ∧ u.val.2 < (M : ℤ))
    (hv : 0 ≤ v.val.2 ∧ v.val.2 < (M : ℤ)) :
    (liftedEdgeIndex hNp hMp u v).2.val ≠ 0 := by
  have hmax : 0 < max u.val.2 v.val.2 := by
    have hd := huv.2
    have hne : u.val.2 ≠ v.val.2 := by
      intro heq
      simp_all
    omega
  have hval := periodicCoordinate_val hMp (max u.val.2 v.val.2)
  rw [Int.emod_eq_of_lt hmax.le (max_lt hu.2 hv.2)] at hval
  change (periodicCoordinate hMp (max u.val.2 v.val.2)).val ≠ 0
  omega

/-- Changing only the indexed seam edges leaves every bounded path below
height M unchanged. This is the locality needed before closing the seam. -/
theorem liftedBoundedConnection_congr_away_seam (hNp : 0 < N) (hMp : 0 < M)
    (A B : RCConfig N M) (a b lo hi : ℤ) (hlo : 0 ≤ lo) (hhi : hi < (M : ℤ))
    (hagree : ∀ e : Fin N × Fin M, e.2.val ≠ 0 → A e = B e)
    (u v : RotatedVertex) :
    liftedBoundedConnection hNp hMp A a b lo hi u v ↔
      liftedBoundedConnection hNp hMp B a b lo hi u v := by
  have hforward (A B : RCConfig N M)
      (heq : ∀ e : Fin N × Fin M, e.2.val ≠ 0 → A e = B e)
      (hconn : liftedBoundedConnection hNp hMp A a b lo hi u v) :
      liftedBoundedConnection hNp hMp B a b lo hi u v := by
    obtain ⟨w,hw⟩ := hconn
    have hB : ∀ e, e ∈ w.edges → e ∈ (liftedStripGraph hNp hMp B a b).edgeSet := by
      intro e
      induction e using Sym2.ind with
      | h x y =>
        intro he
        have h := w.adj_of_mem_edges he
        have hx := hw x (w.fst_mem_support_of_mem_edges he)
        have hy := hw y (w.snd_mem_support_of_mem_edges he)
        have hi := liftedEdgeIndex_row_ne_zero hNp hMp h.1
          ⟨hlo.trans hx.1, hx.2.trans_lt hhi⟩ ⟨hlo.trans hy.1, hy.2.trans_lt hhi⟩
        exact ⟨h.1, heq _ hi ▸ h.2.1, h.2.2⟩
    exact ⟨w.transfer _ hB, by simpa only [SimpleGraph.Walk.support_transfer] using hw⟩
  exact ⟨hforward A B hagree, hforward B A (fun e he => (hagree e he).symm)⟩

/-- In particular, bounded connections are invariant under toggling any
seam edge. -/
theorem liftedBoundedConnection_toggle_seam (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b lo hi : ℤ) (hlo : 0 ≤ lo) (hhi : hi < (M : ℤ))
    (e : Fin N × Fin M) (he : e.2.val = 0) (u v : RotatedVertex) :
    liftedBoundedConnection hNp hMp A a b lo hi u v ↔
      liftedBoundedConnection hNp hMp (toggleEdge A e) a b lo hi u v := by
  apply liftedBoundedConnection_congr_away_seam hNp hMp A (toggleEdge A e)
    a b lo hi hlo hhi _ u v
  intro f hf
  exact (toggleEdge_away A (show f ≠ e by grind)).symm

end PottsDiscontinuity.TorusRC
