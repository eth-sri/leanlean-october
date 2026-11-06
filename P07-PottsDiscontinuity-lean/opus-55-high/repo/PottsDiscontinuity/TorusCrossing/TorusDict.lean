module

public import PottsDiscontinuity.FK.SubgraphComparison
public import PottsDiscontinuity.TorusCrossing.Planar
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-!
# Dictionary between boards of the rotated lattice and the diamond torus

A board whose cell block fits in one period of the torus embeds in the primal diamond torus
graph.  The cell at integer position `(x, y)` is the torus vertex `(x mod N, y mod M)`, and the
medial vertex `m` carries the torus edge with index `(m.1 mod N, m.2 mod M)`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength
open scoped Classical

variable {N M : ℕ}

/-- The rotated vertex of a primal cell. -/
def toRV (c : Cell) (hc : IsPrimal c) : RotatedVertex :=
  ⟨c, Int.even_iff.2 hc⟩

section
variable (hNp : 0 < N) (hMp : 0 < M)
/-- Torus index of a medial vertex. -/
def toFin (m : Cell) : Fin N × Fin M :=
  (periodicCoordinate hNp m.1, periodicCoordinate hMp m.2)

theorem liftedEdgeIndex_primalEnds (m : Cell) :
    liftedEdgeIndex hNp hMp (toRV (primalEnds m).1 (primalEnds_fst_primal m))
      (toRV (primalEnds m).2 (primalEnds_snd_primal m)) = toFin hNp hMp m := by
  grind [liftedEdgeIndex, toFin, toRV, primalEnds]
end

theorem rotAdj_primalEnds (m : Cell) :
    rotatedLattice.Adj (toRV (primalEnds m).1 (primalEnds_fst_primal m))
      (toRV (primalEnds m).2 (primalEnds_snd_primal m)) := by
  unfold toRV primalEnds
  change |_| = 1 ∧ |_| = 1
  grind

theorem periodic_inj (hNp : 0 < N) {z z' : ℤ}
    (h : periodicCoordinate hNp z = periodicCoordinate hNp z') (hlt : |z - z'| < N) : z = z' := by
  have h1 : z % (N : ℤ) = z' % (N : ℤ) := by
    simpa only [periodicCoordinate_val] using (congrArg (fun i : Fin N => (i.val : ℤ)) h)
  have := Int.eq_zero_of_abs_lt_dvd (Int.ModEq.dvd h1.symm) hlt
  omega

section Embedding

variable (Q : Rect) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)

/-- The torus vertex of a primal cell of the board. -/
def iotaFun (c : Q.pcells) : FaceVertex N M true :=
  liftedFaceVertex hN hM hNp hMp (toRV c.1 (Rect.mem_pcells.1 c.2).2)

theorem iotaFun_val (c : Q.pcells) :
    (iotaFun Q hN hM hNp hMp c).val = (periodicCoordinate hNp c.1.1, periodicCoordinate hMp c.1.2) :=
  rfl

section
variable (hQN : Q.w + 1 ≤ N)
include hQN
theorem iotaFun_inj (hQM : Q.h + 1 ≤ M) :
    Function.Injective (iotaFun Q hN hM hNp hMp) := by
  intro c d h
  have h' := congrArg Subtype.val h
  rw [iotaFun_val, iotaFun_val, Prod.ext_iff] at h'
  have hc := Rect.mem_cells.1 (Rect.mem_pcells.1 c.2).1
  have hd := Rect.mem_cells.1 (Rect.mem_pcells.1 d.2).1
  grind [periodic_inj]

/-- The embedding of the board's primal vertices into the diamond torus. -/
def iota (hQM : Q.h + 1 ≤ M) : Q.pcells ↪ FaceVertex N M true :=
  ⟨iotaFun Q hN hM hNp hMp, iotaFun_inj Q hN hM hNp hMp hQN hQM⟩

theorem iota_le (hQM : Q.h + 1 ≤ M) :
    Q.pG.map (iota Q hN hM hNp hMp hQN hQM) ≤ fullDiamondGraph hN hM := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
  obtain ⟨hne, hm⟩ := hab
  refine ⟨?_, fun h => hne ((iota Q hN hM hNp hMp hQN hQM).injective h)⟩
  have key : ∀ m : Cell, (primalEnds m = (a.1, b.1) ∨ primalEnds m = (b.1, a.1)) →
      s(iotaFun Q hN hM hNp hMp a, iotaFun Q hN hM hNp hMp b) =
        s(faceEndpoint hN hM true (toFin hNp hMp m) false,
          faceEndpoint hN hM true (toFin hNp hMp m) true) := by
    intro m hmm
    have hlift := liftedFaceEndpoints_eq hN hM hNp hMp
      (toRV (primalEnds m).1 (primalEnds_fst_primal m))
      (toRV (primalEnds m).2 (primalEnds_snd_primal m)) (rotAdj_primalEnds m)
    rw [liftedEdgeIndex_primalEnds] at hlift
    rcases hmm with h | h
    · have ha : iotaFun Q hN hM hNp hMp a = liftedFaceVertex hN hM hNp hMp
          (toRV (primalEnds m).1 (primalEnds_fst_primal m)) := by
        simp_all [iotaFun]
      have hb : iotaFun Q hN hM hNp hMp b = liftedFaceVertex hN hM hNp hMp
          (toRV (primalEnds m).2 (primalEnds_snd_primal m)) := by
        simp_all [iotaFun]
      simp_all
    · have ha : iotaFun Q hN hM hNp hMp a = liftedFaceVertex hN hM hNp hMp
          (toRV (primalEnds m).2 (primalEnds_snd_primal m)) := by
        simp_all [iotaFun]
      have hb : iotaFun Q hN hM hNp hMp b = liftedFaceVertex hN hM hNp hMp
          (toRV (primalEnds m).1 (primalEnds_fst_primal m)) := by
        simp_all [iotaFun]
      rw [ha, hb, Sym2.eq_swap]; omega
  rcases hm with ⟨m, _, hmm⟩ | ⟨m, _, hmm⟩
  · exact ⟨toFin hNp hMp m, rfl, key m (Or.inl hmm)⟩
  · exact ⟨toFin hNp hMp m, rfl, key m (Or.inr hmm)⟩
end

theorem iota_edge (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hQN : Q.w + 1 ≤ N) (hQM : Q.h + 1 ≤ M) {m : Cell}
    (hm : m ∈ Q.inner) :
    FK.embeddedEdgeEmbedding Q.pG (fullDiamondGraph hN hM) (iota Q hN hM hNp hMp hQN hQM)
      (iota_le Q hN hM hNp hMp hQN hQM) (endEdgeEquiv Q.pData ⟨m, hm⟩) =
      torusIndexedEdgeEmbedding hN hM hN4 hM4 (toFin hNp hMp m) := by
  apply Subtype.ext
  have hlift := liftedFaceEndpoints_eq hN hM hNp hMp
    (toRV (primalEnds m).1 (primalEnds_fst_primal m))
    (toRV (primalEnds m).2 (primalEnds_snd_primal m)) (rotAdj_primalEnds m)
  rw [liftedEdgeIndex_primalEnds] at hlift
  tauto

/-- The board configuration read off a torus configuration. -/
noncomputable def boardOf (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) : Finset Cell :=
  Q.inner.filter (fun m => A (toFin hNp hMp m) = true)

theorem openMedials_restr_torus (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hQN : Q.w + 1 ≤ N)
    (hQM : Q.h + 1 ≤ M) (A : RCConfig N M) :
    openMedials Q.pData (FK.embeddedConfigurationRestriction Q.pG (fullDiamondGraph hN hM)
      (iota Q hN hM hNp hMp hQN hQM) (iota_le Q hN hM hNp hMp hQN hQM)
      (torusRCConfigurationEquiv hN hM hN4 hM4 A)) = boardOf Q hNp hMp A := by
  ext m
  rw [mem_openMedials, boardOf, Finset.mem_filter]
  simp_all [iota_edge]

end Embedding

end PottsDiscontinuity.TorusCrossing
