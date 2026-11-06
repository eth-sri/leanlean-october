module

public import Chazelle.Core.DownPhaseHostArc

/-!
# WP-M (X, part 7): the host chain of a region

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q`, the host polygon
`hostPoly Q S R` (simple, H1) without the edge after the host key `g` is the **host chain**
`hostChain Q S R g`.  When `g` is a chord gap, every arc `(l, r)` of `R` is a run of consecutive
chain edges `k_l, …, k_l + d - 1` without wrap-around (`arc_chain`): chain vertex `k_l + j` is the
walk point of the `j`-th host key of the arc.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The host polygon** of `R`. -/
noncomputable def hostPoly (Q : Polygon) (S : Set (Set Point)) (R : Set Point) : Polygon :=
  ⟨hostPts (interiorModel Q) S R⟩

theorem hostPoly_n : (hostPoly Q S R).n = nk (interiorModel Q) S R := by
  simp [hostPoly, Polygon.n, hostPts, nk]

theorem hostPoly_vtx {i : ℕ} (hi : i < nk (interiorModel Q) S R) :
    (hostPoly Q S R).vtx i = hostPt (interiorModel Q).W (hk (interiorModel Q) S R i) := by
  have hi' : i < (hostPts (interiorModel Q) S R).length := by simpa [hostPts, nk] using hi
  unfold hostPoly Polygon.vtx
  rw [List.getD_eq_getElem _ _ hi']
  simp only [hostPts, List.getElem_map, hk]
  rw [List.getD_eq_getElem _ _ (by simpa [hostPts] using hi')]

/-- At least three host keys. -/
theorem three_le_nk (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) : 3 ≤ nk (interiorModel Q) S R := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have hS := hostKeys_finite (U := R) hM hFam.2.1 hFam.1
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := three_le hQ hFam hne hR
  unfold nk
  rw [hostKeyList_eq hS, Finset.length_sort]
  exact Finset.two_lt_card.2 ⟨x, by simpa using hx, y, by simpa using hy, z, by simpa using hz,
    hxy, hxz, hyz⟩

/-- **The host chain**: the host polygon without the edge after the host key `g`. -/
noncomputable def hostChain (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (g : ℕ)
    (h3 : 3 ≤ nk (interiorModel Q) S R) : Chain where
  P := hostPoly Q S R
  s := (g + 1) % nk (interiorModel Q) S R
  m := nk (interiorModel Q) S R - 1
  one_le := by omega
  add_one_le := by rw [hostPoly_n]; omega

variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}

theorem hostChain_m : (hostChain Q S R g h3).m = nk (interiorModel Q) S R - 1 := rfl

/-- **The chain vertices** are the walk points of the host keys from `g + 1` on. -/
theorem hostChain_vertex (k : ℕ) :
    (hostChain Q S R g h3).vertex k = hostPt (interiorModel Q).W
      (hk (interiorModel Q) S R (((g + 1) % nk (interiorModel Q) S R + k) %
        nk (interiorModel Q) S R)) := by
  show (hostPoly Q S R).vtx (((g + 1) % nk (interiorModel Q) S R + k) % (hostPoly Q S R).n) = _
  rw [hostPoly_n, hostPoly_vtx (Nat.mod_lt _ (by omega))]

/-- Mod arithmetic of chain indices. -/
theorem chain_idx {N s i j : ℕ} (hs : s < N) (hi : i < N) :
    (s + (i + N - s) % N + j) % N = (i + j) % N := by
  rw [Nat.add_mod (s + (i + N - s) % N) j, add_steps_mod hs hi, Nat.add_mod_mod]

/-- **An arc is a run of chain edges without wrap-around**: for a chord gap `g`, the chain index
`k_l` of the start `l = hk i_l` of an arc and its number `d` of gaps satisfy `k_l + d ≤ m`. -/
theorem arc_chain (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g) {l r : ℝ} (harc : (interiorModel Q).IsArc S R l r)
    {i_l d : ℕ} (hil : i_l < nk (interiorModel Q) S R) (hd0 : 0 < d)
    (hdN : d < nk (interiorModel Q) S R)
    (hr : hk (interiorModel Q) S R ((i_l + d) % nk (interiorModel Q) S R) = r)
    (hinner : ∀ j, 0 < j → j < d →
      sideInArc l r (hk (interiorModel Q) S R ((i_l + j) % nk (interiorModel Q) S R)))
    (hgaps : ∀ j, j < d → ∀ y : ℝ, 0 ≤ y → y < (interiorModel Q).W.n →
      sideInArc (hk (interiorModel Q) S R ((i_l + j) % nk (interiorModel Q) S R))
        (hk (interiorModel Q) S R ((i_l + (j + 1)) % nk (interiorModel Q) S R)) y →
      sideInArc l r y) :
    (i_l + nk (interiorModel Q) S R - (g + 1) % nk (interiorModel Q) S R) %
      nk (interiorModel Q) S R + d ≤ nk (interiorModel Q) S R - 1 := by
  set M := interiorModel Q
  set N := nk M S R
  set s := (g + 1) % N with hs
  have hsN : s < N := Nat.mod_lt _ (by omega)
  set kl := (i_l + N - s) % N with hkl
  have hklN : kl < N := Nat.mod_lt _ (by omega)
  have hM : WalkAx M := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  -- the key of chain vertex `0` is a cut
  obtain ⟨c, hc, p, p', t, t', hA, hB, ha, hb, hAB⟩ := hgc
  have hscut : M.IsCut S (hk M S R s) := ⟨c, hc, p', t', hB, hb⟩
  -- no step of the arc reaches the chain start
  have hno : ∀ j, 0 < j → j ≤ d → (i_l + j) % N ≠ s := by
    intro j hj0 hjd he
    rcases hjd.lt_or_eq with hjd | hjd
    · exact harc.2.2.2.2.2.1 _ (hinner j hj0 hjd) (he ▸ hscut)
    · -- the last gap of the arc would be the chord gap `g`
      subst hjd
      have hg' : (i_l + (j - 1)) % N = g := by
        have e1 : ((i_l + (j - 1)) % N + 1) % N = s := by
          rw [Nat.add_mod ((i_l + (j - 1)) % N) 1, Nat.mod_mod, ← Nat.add_mod,
            show i_l + (j - 1) + 1 = i_l + j by omega]
          exact he
        have e2 : (g + 1) % N = s := rfl
        have hgl : (i_l + (j - 1)) % N < N := Nat.mod_lt _ (by omega)
        -- `x ↦ (x + 1) % N` is injective on `[0, N)`
        by_contra hne'
        rcases Nat.lt_or_gt_of_ne hne' with h | h
        · have := e1.trans e2.symm
          rcases Nat.lt_or_ge ((i_l + (j - 1)) % N + 1) N with h1 | h1 <;>
            rcases Nat.lt_or_ge (g + 1) N with h2 | h2
          · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
          · rw [Nat.mod_eq_of_lt h1, show g + 1 = N by omega, Nat.mod_self] at this; omega
          · omega
          · omega
        · have := e1.trans e2.symm
          rcases Nat.lt_or_ge ((i_l + (j - 1)) % N + 1) N with h1 | h1 <;>
            rcases Nat.lt_or_ge (g + 1) N with h2 | h2
          · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
          · omega
          · rw [show (i_l + (j - 1)) % N + 1 = N by omega, Nat.mod_self,
              Nat.mod_eq_of_lt h2] at this; omega
          · omega
      have hN2 : 2 ≤ N := by omega
      have hAG : ArcGap M S R g := by
        refine ⟨l, r, harc, fun y hy0 hyn hy => ?_⟩
        rw [← hg'] at hy
        have e3 : ((i_l + (j - 1)) % N + 1) % N = (i_l + (j - 1 + 1)) % N := by
          rw [Nat.add_mod ((i_l + (j - 1)) % N) 1, Nat.mod_mod, ← Nat.add_mod]; ring_nf
        rw [e3] at hy
        exact hgaps (j - 1) (by omega) y hy0 hyn hy
      exact not_arc_and_chord hM hF hfin hN2 hg hAG ⟨c, hc, p, p', t, t', hA, hB, ha, hb, hAB⟩
  -- hence no wrap-around
  by_contra hwrap
  push Not at hwrap
  have hj : 0 < N - kl ∧ N - kl ≤ d := ⟨by omega, by omega⟩
  apply hno (N - kl) hj.1 hj.2
  have := chain_idx (j := N - kl) hsN hil
  rw [← hkl, show s + kl + (N - kl) = s + N by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hsN] at this
  exact this.symm

end

end DownHost

end Chazelle.Core
