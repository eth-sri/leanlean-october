module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutPiece
public import Chazelle.Core.Lemma41Host
public import Chazelle.Core.DownPhaseTransSide

/-!
# WP-M (E7-B, part 1): the chain of an interior subarc

For the interior oracles (finding E7-B), a subarc of the interior walk of `Q` spanning the input
vertices `a, a + 1, …, a + m` (indices modulo `n`) is served through the chain `subChain Q a m` of
`Q` (host `Host.whole`, start `a`, `m` edges; it may pass the last edge `e_{n-1}`):
* its chain model is an `OkModel` (`okModel_sub`);
* read from the walk vertex `uStart` (`a` if `LeftInside Q`, else the reversed index of vertex
  `a + m`), the interior walk visits the tour of the chain read from `jStart` (`0`, resp. `m`):
  the chain's vertices upward, resp. downward (`iw_tour`);
* hence the interior walk satisfies `PieceWalk` for the chain (`pieceWalk_sub`): one stretch of
  the chain model's walk, or two meeting at its top.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideE)

/-- **The chain of the input vertices `a, …, a + m`** of `Q`. -/
def subChain (Q : Polygon) (a m : ℕ) (hm1 : 1 ≤ m) (hm : m + 1 ≤ Q.n) : Chain :=
  ⟨Q, a, m, hm1, hm⟩

variable {Q : Polygon} {a m : ℕ} {hm1 : 1 ≤ m} {hm : m + 1 ≤ Q.n}

theorem subChain_vertex (k : ℕ) : (subChain Q a m hm1 hm).vertex k = Q.vtx ((a + k) % Q.n) := rfl

/-- **The chain model of a chain of the geometry polygon is served by the oracles.** -/
theorem okModel_sub {P : Polygon} (hG : GoodEnv P) {hm' : m + 1 ≤ (Qof P).n} :
    OkModel P (chainModel (subChain (Qof P) a m hm1 hm')) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn : 1 ≤ P.n := by have := hG.1.1; omega
  refine ⟨Host.whole P.n, subChain (Qof P) a m hm1 hm', by simp [HostOk, Host.whole],
    by rw [hQn]; exact L41.hostRegular_whole hn, ?_, ?_, rfl⟩
  · have := L41.poly_whole (Qof P) (by omega); rw [hQn] at this; exact this.symm
  · exact (shearInvariance (epsOf P) P).1 hG.1

/-- The start of the interior walk's pass along the chain. -/
noncomputable def uStart (Q : Polygon) (a m : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then a % Q.n else Q.n - 1 - (a + m) % Q.n

/-- The tour position of the chain from which the interior walk reads it. -/
noncomputable def jStart (Q : Polygon) (m : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then 0 else m

/-- Reversed indices: `n - 1 - ((n - 1 - r + d) mod n) = (r + n - d) mod n`. -/
theorem rev_idx {n r d : ℕ} (hr : r < n) (hd : d < n) :
    n - 1 - ((n - 1 - r + d) % n) = (r + n - d) % n := by
  rcases Nat.lt_or_ge d (r + 1) with h | h
  · rw [Nat.mod_eq_of_lt (by omega : n - 1 - r + d < n),
      show r + n - d = (r - d) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show n - 1 - r + d = (d - r - 1) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- `(a + (m - d)) mod n = ((a + m) mod n + n - d) mod n` for `d ≤ m`, `d < n`. -/
theorem sub_idx {n a m d : ℕ} (hn : 0 < n) (hd : d ≤ m) (hdn : d < n) :
    (a + (m - d)) % n = ((a + m) % n + n - d) % n := by
  have h1 := Nat.div_add_mod (a + m) n
  have hr : (a + m) % n < n := Nat.mod_lt _ hn
  generalize (a + m) / n = q at h1
  generalize (a + m) % n = r at h1 hr ⊢
  rcases Nat.lt_or_ge r d with h | h
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; rw [mul_zero, zero_add] at h1; omega
      · exact ⟨q - 1, by omega⟩
    have e2 : n * (q' + 1) = n * q' + n := by rw [mul_add, mul_one]
    have e : a + (m - d) = (r + n - d) + n * q' := by omega
    rw [e, Nat.add_mul_mod_self_left]
  · have e : a + (m - d) = (r - d) + n * q := by omega
    rw [e, Nat.add_mul_mod_self_left, show r + n - d = (r - d) + n by omega, Nat.add_mod_right]

/-- **The interior walk visits the tour of the chain.** -/
theorem iw_tour (hQn : 1 ≤ Q.n) {d : ℕ} (hd : d ≤ m) :
    (interiorWalk Q).vtx ((uStart Q a m + d) % (interiorWalk Q).n) =
      WalkEmbed.tourV (subChain Q a m hm1 hm) (jStart Q m) d := by
  have hn : (interiorWalk Q).n = Q.n := Trans.iw_n
  Ξ hn
  unfold uStart jStart
  by_cases hL : Mountain.LeftInside Q
  · ϴ hL, ↓reduceIte
    Ξ ShootCut.tourV_up _ hd, Trans.iw_vtx_left hL, subChain_vertex, Nat.mod_add_mod
  · ϴ hL, ↓reduceIte
    have e : WalkEmbed.tourV (subChain Q a m hm1 hm) m d =
        (subChain Q a m hm1 hm).vertex (m - d) := ShootCut.tourV_down _ hd
    rw [e, Trans.iw_vtx_right hL (Nat.mod_lt _ (⋄)), subChain_vertex]
    congr 1
    rw [rev_idx (Nat.mod_lt _ (⋄)) (by omega), sub_idx (by omega) hd (by omega)]

end

end IOrc

end Chazelle.Core
