module

public import PottsDiscontinuity.Torus.RibbonAttachment
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Lifted paths avoiding the horizontal seam -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section
variable (hNp : 0 < N) (hMp : 0 < M)
/-- An actual open path in the lifted horizontal strip, with every vertex
also constrained to the prescribed vertical interval. -/
def liftedBoundedConnection (A : RCConfig N M) (a b lo hi : ℤ) (u v : RotatedVertex) : Prop :=
  ∃ w : (liftedStripGraph hNp hMp A a b).Walk u v,
    ∀ z ∈ w.support, lo ≤ z.val.2 ∧ z.val.2 ≤ hi

/-- Every edge of a nonnegative lifted path below height M avoids row zero
of the indexed torus. -/
theorem liftedEdgeIndex_row_ne_zero {u v : RotatedVertex} (huv : rotatedLattice.Adj u v)
    (hu : 0 ≤ u.val.2 ∧ u.val.2 < (M : ℤ))
    (hv : 0 ≤ v.val.2 ∧ v.val.2 < (M : ℤ)) :
    (liftedEdgeIndex hNp hMp u v).2.val ≠ 0 := by
  have hmax : 0 < max u.val.2 v.val.2 := by
    have hd := huv.2
    grind
  have hval := periodicCoordinate_val hMp (max u.val.2 v.val.2)
  rw [Int.emod_eq_of_lt hmax.le (max_lt hu.2 hv.2)] at hval
  change (periodicCoordinate hMp (max u.val.2 v.val.2)).val ≠ 0
  omega

theorem walk_rebuild_away_seam (A B : RCConfig N M) (a b H : ℤ) (hH : H < (M : ℤ))
    (hagree : ∀ e : Fin N × Fin M, e.2.val ≠ 0 → A e = B e)
    {u v : RotatedVertex} (w : (liftedStripGraph hNp hMp A a b).Walk u v) :
    (∀ z ∈ w.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ H) →
    ∃ w' : (liftedStripGraph hNp hMp B a b).Walk u v, w'.support = w.support := by
  induction w with
  | nil => tauto
  | @cons u v z huv p ih =>
    intro hw
    have hu := hw u (by simp)
    have hv := hw v (by simp)
    have hidx := liftedEdgeIndex_row_ne_zero hNp hMp huv.1
      ⟨hu.1,hu.2.trans_lt hH⟩ ⟨hv.1,hv.2.trans_lt hH⟩
    have huvB : (liftedStripGraph hNp hMp B a b).Adj u v := by
      refine ⟨huv.1,?_,huv.2.2⟩
      rw [← hagree _ hidx]
      exact huv.2.1
    obtain ⟨p',hp'⟩ := ih (fun z hz => hw z (by grind))
    exact ⟨.cons huvB p',by grind⟩

/-- Changing only the indexed seam edges leaves every bounded path below
height M unchanged. This is the locality needed before closing the seam. -/
theorem liftedBoundedConnection_congr_away_seam (A B : RCConfig N M) (a b lo hi : ℤ) (hlo : 0 ≤ lo) (hhi : hi < (M : ℤ))
    (hagree : ∀ e : Fin N × Fin M, e.2.val ≠ 0 → A e = B e)
    (u v : RotatedVertex) :
    liftedBoundedConnection hNp hMp A a b lo hi u v ↔
      liftedBoundedConnection hNp hMp B a b lo hi u v := by
  have hforward (A B : RCConfig N M)
      (heq : ∀ e : Fin N × Fin M, e.2.val ≠ 0 → A e = B e)
      (hconn : liftedBoundedConnection hNp hMp A a b lo hi u v) :
      liftedBoundedConnection hNp hMp B a b lo hi u v := by
    obtain ⟨w,hw⟩ := hconn
    obtain ⟨w',hs⟩ := walk_rebuild_away_seam hNp hMp A B a b hi hhi heq w
      (fun z hz => ⟨hlo.trans (hw z hz).1,(hw z hz).2⟩)
    exact ⟨w',by grind⟩
  grind

/-- In particular, bounded connections are invariant under toggling any
seam edge. -/
theorem liftedBoundedConnection_toggle_seam (A : RCConfig N M) (a b lo hi : ℤ) (hlo : 0 ≤ lo) (hhi : hi < (M : ℤ))
    (e : Fin N × Fin M) (he : e.2.val = 0) (u v : RotatedVertex) :
    liftedBoundedConnection hNp hMp A a b lo hi u v ↔
      liftedBoundedConnection hNp hMp (toggleEdge A e) a b lo hi u v := by
  apply liftedBoundedConnection_congr_away_seam hNp hMp A (toggleEdge A e)
    a b lo hi hlo hhi _ u v
  intro f hf
  exact (toggleEdge_away A (show f ≠ e by grind)).symm
end

end PottsDiscontinuity.TorusRC
