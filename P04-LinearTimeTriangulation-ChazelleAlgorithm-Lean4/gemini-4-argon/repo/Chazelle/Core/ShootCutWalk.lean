module

public import Chazelle.Core.ShootCutPiece
public import Chazelle.Core.NFLocateChain

/-!
# WP-G, part 2: run stretches of the walk of a host chain

Let `C` be a chain of a host polygon `C.P = H.poly Q` (`N` host points).  The walk vertex
`i + 6` of `chainModel C` (`i ≤ 2m`) is the chain vertex `sideIdx i = sideE m J`,
`J = (S + i) mod 2m` (`S = sideS sideBeta`), which is the host point of index
`(C.s + sideE m J) mod N`.  When this host point lies in a `run a ℓ` item at offset `t`, the walk
continues through the consecutive vertices of `Q`:

* `run_up`: for `J < m` (the tour climbs the chain), `d` more steps (`J + d ≤ m`, `t + d ≤ ℓ`,
  no wrap of `Q`-indices) visit `Q.vtx (q + d)`, `q = (a + t) mod n`;
* `run_down`: for `J ≥ m` (the tour descends), `d` steps with `J + d ≤ 2m`, `d ≤ t`, `d ≤ q`
  visit `Q.vtx (q - d)`.

For an aligned block `[x, x + w)` of such a stretch, the walk agrees with the tour of the chain of
`Q` with start `x` and `w` edges, read upward or downward (`block_up`, `block_down`); `grade_vertex`
identifies the vertices of such a chain.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)

namespace ShootCut

section Run

variable (C : Chain) {Q : Polygon} {H : Host}

/-- The tour coordinate of tour position `i`. -/
noncomputable def tJ (i : ℕ) : ℕ := (C.sideS C.sideBeta + i) % (2 * C.m)

theorem tJ_lt (i : ℕ) : tJ C i < 2 * C.m := Nat.mod_lt _ C.two_m_pos

theorem tJ_add {i d : ℕ} (h : tJ C i + d < 2 * C.m) : tJ C (i + d) = tJ C i + d := by
  unfold tJ at h ⊢
  rw [← Nat.add_assoc, ← Nat.mod_add_mod, Nat.mod_eq_of_lt h]

/-- The walk vertex of tour position `i` is the chain vertex `sideE m (tJ i)`. -/
theorem walk_vtx (i : ℕ) (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx (i + 6) = C.vertex (sideE C.m (tJ C i)) := by
  show (C.sideWalk C.sideBeta).vtx (i + 6) = _
  rw [C.sideWalk_vtx_tour _ hi]
  rfl

/-- The chain index at tour position `i + d` when the tour climbs. -/
theorem sideE_up {i d : ℕ} (hJ : tJ C i + d ≤ C.m) :
    sideE C.m (tJ C (i + d)) = sideE C.m (tJ C i) + d := by
  have h1 := C.one_le
  rw [tJ_add C (by omega)]
  unfold sideE
  rw [ite_eq_left hJ, ite_eq_left (by omega)]

/-- The chain index at tour position `i + d` when the tour descends. -/
theorem sideE_down {i d : ℕ} (hm : C.m ≤ tJ C i) (hJ : tJ C i + d ≤ 2 * C.m) :
    sideE C.m (tJ C (i + d)) = sideE C.m (tJ C i) - d := by
  have h1 := C.one_le
  rcases (show tJ C i + d < 2 * C.m ∨ tJ C i + d = 2 * C.m by omega) with h | h
  · rw [tJ_add C h]
    unfold sideE
    split_ifs <;> omega
  · have e : tJ C (i + d) = 0 := by
      have e1 : tJ C (i + d) = (tJ C i + d) % (2 * C.m) := by
        unfold tJ; rw [← Nat.add_assoc, ← Nat.mod_add_mod]
      rw [e1, h, Nat.mod_self]
    rw [e]
    unfold sideE
    split_ifs <;> omega

/-- **A run stretch, climbing.** -/
theorem run_up (hP : C.P = H.poly Q) {i d : ℕ} (hJ : tJ C i + d ≤ C.m) (hi : i + d ≤ 2 * C.m)
    {r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : (C.s + sideE C.m (tJ C i)) % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t + d ≤ ℓ)
    (hq : (a + t) % Q.n + d < Q.n) :
    (chainModel C).W.vtx (i + d + 6) = Q.vtx ((a + t) % Q.n + d) := by
  have hN : C.P.n = (H.pts Q.n).length := by rw [hP]; simp [Host.poly, Polygon.n]
  have hsucc := NFLoc.preLen_succ Q.n H hr
  have hlen := NFLoc.preLen_mono Q.n H (show r + 1 ≤ H.length by omega)
  rw [NFLoc.preLen_length] at hlen
  rw [hrun] at hsucc
  simp only [NFLoc.itemCnt] at hsucc
  -- host index
  have hidx : (C.s + sideE C.m (tJ C (i + d))) % C.P.n = NFLoc.preLen Q.n H r + (t + d) := by
    rw [sideE_up C hJ, ← Nat.add_assoc, Nat.add_mod, hu, Nat.mod_eq_of_lt (show d < C.P.n by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hpt : (H.pts Q.n)[(C.s + sideE C.m (tJ C (i + d))) % C.P.n]? =
      some (SymPt.vtx ((a + (t + d)) % Q.n)) := by
    rw [hidx, NFLoc.pts_getElem? Q.n H hr (by omega) (by rw [hrun]; simp [NFLoc.itemCnt]; omega),
      hrun, show NFLoc.preLen Q.n H r + (t + d) - NFLoc.preLen Q.n H r = t + d by omega,
      NFLoc.run_pts_getElem? _ _ _ ht]
  rw [show i + d + 6 = (i + d) + 6 by ring, walk_vtx C _ hi,
    NFLoc.chain_vertex_host C hP _ hpt]
  show Q.vtx _ = _
  congr 1
  rw [← Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt (show d < Q.n by omega),
    Nat.mod_eq_of_lt hq]

/-- **A run stretch, descending.** -/
theorem run_down (hP : C.P = H.poly Q) {i d : ℕ} (hm : C.m ≤ tJ C i) (hJ : tJ C i + d ≤ 2 * C.m)
    (hi : i + d ≤ 2 * C.m)
    {r a ℓ t : ℕ} (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : (C.s + sideE C.m (tJ C i)) % C.P.n = NFLoc.preLen Q.n H r + t) (ht : t ≤ ℓ) (hdt : d ≤ t)
    (hq : d ≤ (a + t) % Q.n) (hn : 0 < Q.n) :
    (chainModel C).W.vtx (i + d + 6) = Q.vtx ((a + t) % Q.n - d) := by
  have hN : C.P.n = (H.pts Q.n).length := by rw [hP]; simp [Host.poly, Polygon.n]
  have hsucc := NFLoc.preLen_succ Q.n H hr
  have hlen := NFLoc.preLen_mono Q.n H (show r + 1 ≤ H.length by omega)
  rw [NFLoc.preLen_length] at hlen
  rw [hrun] at hsucc
  simp only [NFLoc.itemCnt] at hsucc
  have hkd : d ≤ sideE C.m (tJ C i) := by
    have := sideE_down C (d := d) hm hJ
    unfold sideE at *
    split_ifs at * <;> omega
  have hidx : (C.s + sideE C.m (tJ C (i + d))) % C.P.n = NFLoc.preLen Q.n H r + (t - d) := by
    rw [sideE_down C hm hJ]
    have e := Nat.div_add_mod (C.s + sideE C.m (tJ C i)) C.P.n
    rw [hu] at e
    have e2 : C.s + (sideE C.m (tJ C i) - d) =
        C.P.n * ((C.s + sideE C.m (tJ C i)) / C.P.n) + (NFLoc.preLen Q.n H r + (t - d)) := by
      omega
    rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hpt : (H.pts Q.n)[(C.s + sideE C.m (tJ C (i + d))) % C.P.n]? =
      some (SymPt.vtx ((a + (t - d)) % Q.n)) := by
    rw [hidx, NFLoc.pts_getElem? (p := NFLoc.preLen Q.n H r + (t - d)) Q.n H hr (by omega)
        (by rw [hrun]; simp only [NFLoc.itemCnt]; omega),
      hrun, show NFLoc.preLen Q.n H r + (t - d) - NFLoc.preLen Q.n H r = t - d by omega,
      NFLoc.run_pts_getElem? _ _ _ (by omega)]
  rw [show i + d + 6 = (i + d) + 6 by ring, walk_vtx C _ hi,
    NFLoc.chain_vertex_host C hP _ hpt]
  show Q.vtx _ = _
  congr 1
  have e := Nat.div_add_mod (a + t) Q.n
  have e2 : a + (t - d) = Q.n * ((a + t) / Q.n) + ((a + t) % Q.n - d) := by omega
  rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt (a + t) hn; omega)]

end Run

/-! ## Chains of `Q` -/

/-- **The vertices of a chain of `Q`** without wrap: `Q.vtx (x + d)`. -/
theorem grade_vertex {Q : Polygon} {Cα : Chain} (hP : Cα.P = Q) (hx : Cα.s + Cα.m < Q.n) {d : ℕ}
    (hd : d ≤ Cα.m) : Cα.vertex d = Q.vtx (Cα.s + d) := by
  unfold Chain.vertex Chain.edgeIdx
  subst hP
  rw [Nat.mod_eq_of_lt (by omega)]

end ShootCut

end

end Chazelle.Core
