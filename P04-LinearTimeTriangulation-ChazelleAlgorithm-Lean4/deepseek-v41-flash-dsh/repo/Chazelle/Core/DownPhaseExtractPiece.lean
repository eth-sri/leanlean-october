module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseExtractGeom

/-!
# WP-M (X, part 12): the pieces of an arc on the host chain

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q` (`Ctx`), a chord gap
`g` and an arc `(l, r)` of `R` with data `ArcData … i_l d`:

* chain vertex `kl + j` of the host chain is the walk point of the `j`-th host key of the arc
  (`vertex_arc`), where `kl` is the chain index of `l`;
* the chain edge `kl + j` (`j < d`) is a piece of one interior walk edge `p` (modulo `n`),
  traversed in the same direction (`piece`);
* at an inner host key (a walk vertex), the pieces before and after meet at the walk vertex
  (`piece_inner`).
-/

namespace Chazelle.Core

namespace Extract

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf)
open Chazelle.Geometry (lerp)
open DownHost
open ArcT (wrapK)

/-- The hypotheses on the region. -/
structure Ctx (Q : Polygon) (S : Set (Set Point)) (R : Set Point) : Prop where
  hQ : Q.Simple
  hFam : (interiorModel Q).ChordFamily Q S
  hne : S.Nonempty
  hR : R ∈ (interiorModel Q).regions S

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

namespace Ctx

variable (X : Ctx Q S R)
include X

theorem walkAx : WalkAx (interiorModel Q) := walkAx_interiorModel X.hQ

theorem three : 3 ≤ nk (interiorModel Q) S R := three_le_nk X.hQ X.hFam X.hne X.hR

end Ctx

/-- The chain index of the host key `i`. -/
noncomputable def kIdx (N g i : ℕ) : ℕ := (i + N - (g + 1) % N) % N

variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **The chain vertices along an arc.** -/
theorem vertex_arc (X : Ctx Q S R) {i_l : ℕ} (hil : i_l < nk (interiorModel Q) S R) (j : ℕ) :
    (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j) =
      hostPt (interiorModel Q).W (hk (interiorModel Q) S R ((i_l + j) % nk (interiorModel Q) S R)) := by
  have hN : 0 < nk (interiorModel Q) S R := by have := X.three; omega
  Ξ hostChain_vertex, ← add_assoc
  unfold kIdx
  Ξ chain_idx (Nat.mod_lt _ hN) hil

/-- The walk point of an unwrapped key in `[p, p + 1)` is at position `(p mod n, key - p)`. -/
theorem wrapK_edge {n p : ℕ} (_hn : 0 < n) (hp : p < 2 * n) {y : ℝ} (hy1 : (p : ℝ) ≤ y)
    (hy2 : y < p + 1) : wrapK n y = ((p % n : ℕ) : ℝ) + (y - p) := by
  unfold wrapK
  split_ifs with h
  · have hpn : p < n := by
      have : (p : ℝ) < n := lt_of_le_of_lt hy1 h
      exact_mod_cast this
    rw [Nat.mod_eq_of_lt hpn]; ring
  · push Not at h
    have hpn : n ≤ p := by
      by_contra hpn; push Not at hpn
      have : (p : ℝ) + 1 ≤ n := by exact_mod_cast hpn
      linarith
    rw [Nat.mod_eq_sub_mod hpn, Nat.mod_eq_of_lt (⋄)]
    push_cast [hpn]; ring

/-- **A piece of an arc**: chain edge `kl + j` lies on interior walk edge `p` (mod `n`). -/
theorem piece (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData (interiorModel Q) S R l r i_l d) {j : ℕ} (hj : j < d) :
    ∃ p : ℕ, p < 2 * (interiorModel Q).W.n ∧
      (p : ℝ) ≤ ukey (interiorModel Q) S R i_l j ∧
      ukey (interiorModel Q) S R i_l (j + 1) ≤ p + 1 ∧
      (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j) =
        lerp ((interiorModel Q).W.vtx (p % (interiorModel Q).W.n))
          ((interiorModel Q).W.vtx ((p % (interiorModel Q).W.n + 1) % (interiorModel Q).W.n))
          (ukey (interiorModel Q) S R i_l j - p) ∧
      (hostChain Q S R g h3).vertex (kIdx (nk (interiorModel Q) S R) g i_l + j + 1) =
        lerp ((interiorModel Q).W.vtx (p % (interiorModel Q).W.n))
          ((interiorModel Q).W.vtx ((p % (interiorModel Q).W.n + 1) % (interiorModel Q).W.n))
          (ukey (interiorModel Q) S R i_l (j + 1) - p) ∧
      ∀ y, ukey (interiorModel Q) S R i_l j ≤ y → y ≤ ukey (interiorModel Q) S R i_l (j + 1) →
        hostPt (interiorModel Q).W (wrapK (interiorModel Q).W.n y) =
          lerp ((interiorModel Q).W.vtx (p % (interiorModel Q).W.n))
            ((interiorModel Q).W.vtx ((p % (interiorModel Q).W.n + 1) % (interiorModel Q).W.n))
            (y - p) := by
  have hM := X.walkAx
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  have hdN := hA.hdN
  obtain ⟨p, hp1, hp2, hp3, hq⟩ := arc_piece hM hF hfin hA hj
  have hjj := ukey_mono (U := R) hM hF hfin hA.hil (Nat.lt_succ_self j) (⋄)
  refine ⟨p, hp3, hp1, hp2, ?_, ?_, hq⟩
  · rw [vertex_arc X hA.hil, ← wrapK_ukey hM hF hfin hA.hil (⋄)]
    exact hq _ le_rfl hjj.le
  · rw [add_assoc, vertex_arc X hA.hil, ← wrapK_ukey hM hF hfin hA.hil (⋄)]
    exact hq _ hjj.le le_rfl

/-- **Inner host keys are integers.** -/
theorem ukey_inner_int (X : Ctx Q S R) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData (interiorModel Q) S R l r i_l d) {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    ∃ k : ℕ, ukey (interiorModel Q) S R i_l j = k := by
  have hM := X.walkAx
  have hF := X.hFam.2.1
  have hfin := X.hFam.1
  obtain ⟨⟨k, hk⟩, -⟩ := hA.inner j hj0 hjd
  have hdN := hA.hdN
  rw [ukey_eq_unwrap hM hF hfin hA.hil (⋄), hk]
  unfold unwrapK
  split_ifs
  · exact ⟨k, rfl⟩
  · exact ⟨k + (interiorModel Q).W.n, by push_cast; ring⟩

/-- **At an inner host key the pieces meet at a walk vertex**: the piece before ends at the end of
its walk edge, the piece after starts at the start of the next one. -/
theorem piece_inner {i_l j p p' : ℕ} (K : ℕ)
    (hK : ukey (interiorModel Q) S R i_l j = K)
    (hp1 : (p : ℝ) ≤ ukey (interiorModel Q) S R i_l j)
    (hp2 : ukey (interiorModel Q) S R i_l (j + 1) ≤ p + 1)
    (hlt : ukey (interiorModel Q) S R i_l j < ukey (interiorModel Q) S R i_l (j + 1))
    (hp1' : (p' : ℝ) ≤ ukey (interiorModel Q) S R i_l (j - 1))
    (hp2' : ukey (interiorModel Q) S R i_l (j - 1 + 1) ≤ p' + 1)
    (hlt' : ukey (interiorModel Q) S R i_l (j - 1) < ukey (interiorModel Q) S R i_l j)
    (hj0 : 0 < j) : p = K ∧ p' + 1 = K := by
  rw [Nat.sub_add_cancel hj0] at hp2'
  rw [hK] at hp1 hlt hp2' hlt'
  constructor
  · have h1 : p ≤ K := by exact_mod_cast hp1
    have h2 : (K : ℝ) < p + 1 := lt_of_lt_of_le hlt hp2
    have h2' : K < p + 1 := by exact_mod_cast h2
    omega
  · have h1 : (p' : ℝ) < K := lt_of_le_of_lt hp1' hlt'
    have h1' : p' < K := by exact_mod_cast h1
    have h2 : K ≤ p' + 1 := by exact_mod_cast hp2'
    omega

end

end Extract

end Chazelle.Core
