module

public import PottsDiscontinuity.Torus.DiamondDualTranslation
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover
public import PottsDiscontinuity.Duality.RayIndexSeparation

/-! In square-lattice coordinates a translated dual vertex is the face base
one row below its rotated primal representative. Crossing edges project to
the same torus edge after the corresponding column shift. -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC
open Torus CorrLength SixVertex FK FK.Medial Duality SimpleGraph
variable {N M : ℕ}

def squareLift (k : ℤ) (u : RotatedVertex) : ℤ × ℤ :=
  (rotatedToSquareVertex u + (0,k))

abbrev stripSquareHom (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (a b k : ℤ) :
    liftedStripGraph hNp hMp A a b →g squareLattice where
  toFun := squareLift k
  map_rel' h := (squareLattice_adj_translate_iff (0,k) _ _).mpr (rotatedLatticeIso.map_rel_iff.mpr h.1)

-- The difference and sum recover the original column and row.
lemma squareLift_coordinates (k : ℤ) (u : RotatedVertex) :
    (squareLift k u).1 - (squareLift k u).2 = u.val.1 - k ∧
      (squareLift k u).1 + (squareLift k u).2 = u.val.2 + k := by
  have e := congrArg Subtype.val (squareToRotated_rotatedToSquare u)
  simp only [squareToRotatedVertex, Prod.ext_iff] at e
  simp only [squareLift, Prod.fst_add, Prod.snd_add, add_zero]
  omega

private def primalCorner : Sym2 (ℤ × ℤ) → ℤ × ℤ :=
  Sym2.lift ⟨fun u v => (max (u.1-u.2) (v.1-v.2), max (u.1+u.2) (v.1+v.2)),
    fun _ _ => by simp [max_comm]⟩

private theorem primalCorner_dual (b : LatticeBond) :
    primalCorner (dualBondOfPrimal b).toSym2 = primalCorner b.toSym2 + (0,-1) := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [primalCorner, dualBondOfPrimal, LatticeBond.toSym2,
    LatticeBond.source, LatticeBond.target] <;> omega

private theorem primalCorner_lift (k : ℤ) (u v : RotatedVertex) :
    primalCorner s(squareLift k u, squareLift k v) =
      (max u.val.1 v.val.1 - k, max u.val.2 v.val.2 + k) := by
  change (max ((squareLift k u).1 - (squareLift k u).2) ((squareLift k v).1 - (squareLift k v).2),
    max ((squareLift k u).1 + (squareLift k u).2) ((squareLift k v).1 + (squareLift k v).2)) = _
  simp [(squareLift_coordinates k u).1, (squareLift_coordinates k u).2, (squareLift_coordinates k v).1, (squareLift_coordinates k v).2, max_sub_sub_right]

private theorem crossing_corners {u v x y : RotatedVertex} {b : LatticeBond}
    (hp : b.toSym2 = s(squareLift 0 u, squareLift 0 v))
    (hq : (dualBondOfPrimal b).toSym2 = s(squareLift (-1) x, squareLift (-1) y)) :
    (max u.val.1 v.val.1, max u.val.2 v.val.2) =
      (max x.val.1 y.val.1+1, max x.val.2 y.val.2) := by
  have he := primalCorner_dual b
  rw [hp,hq] at he
  simp only [primalCorner_lift, sub_zero, add_zero, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
    sub_neg_eq_add] at he
  exact Prod.ext (by omega) (by omega)

private theorem periodicCoordinate_next (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp (z+1) = nxt (periodicCoordinate hp z) := by
  have h := congrArg nxt (TorusTopology.periodicCoordinate_sub_one hp (z+1))
  simpa only [add_sub_cancel_right, Equiv.apply_symm_apply] using h.symm

/-- Complementary open steps cannot cross any edge of the dual walk. -/
theorem stripStep_avoids_shiftedDual (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) {a b c d : ℤ} {u v x y : RotatedVertex}
    (h : (liftedStripGraph hNp hMp (translatedDualConfig A) a b).Adj u v)
    (q : (liftedStripGraph hNp hMp A c d).Walk x y) :
    (circuitAvoidanceGraph (q.map (stripSquareHom hNp hMp A c d (-1)))).Adj
      (squareLift 0 u) (squareLift 0 v) := by
  refine ⟨(stripSquareHom hNp hMp (translatedDualConfig A) a b 0).map_rel h, ?_⟩
  intro e he hd
  rw [Walk.edges_map] at hd
  obtain ⟨d,hd,hdmap⟩ := List.mem_map.mp hd
  rw [Walk.edges_eq_map_darts] at hd
  obtain ⟨δ,_,rfl⟩ := List.mem_map.mp hd
  have hc := crossing_corners he hdmap.symm
  have hidx : liftedEdgeIndex hNp hMp u v =
      (nxt (liftedEdgeIndex hNp hMp δ.fst δ.snd).1,(liftedEdgeIndex hNp hMp δ.fst δ.snd).2) := by
    unfold liftedEdgeIndex
    have hx := congrArg Prod.fst hc
    have hy := congrArg Prod.snd hc
    dsimp only at hx hy
    rw [hx, hy, periodicCoordinate_next]
  have hopen := h.2.1
  rw [hidx] at hopen
  change shiftRCConfig (dualConfig A) (nxt (liftedEdgeIndex hNp hMp δ.fst δ.snd).1,
    (liftedEdgeIndex hNp hMp δ.fst δ.snd).2) = true at hopen
  rw [shiftRCConfig_nxt] at hopen
  have hdopen := δ.adj.2.1
  change Bool.not (A (liftedEdgeIndex hNp hMp δ.fst δ.snd)) = true at hopen
  simp_all

end PottsDiscontinuity.TorusRC
