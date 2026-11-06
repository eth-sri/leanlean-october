module

public import Chazelle.Core.RestoreStretch
public import Chazelle.Core.ShootCutPiece

/-!
# WP-E, the search: the stretches of a kind-1 piece

A kind-1 piece whose walk vertices are read from the tour position `J` of its chain (`J = 0`
upward, `J = m` downward) agrees with the chain's model walk on one stretch from
`g' = 6 + tpos J` of length `m`, or on two stretches (`L₁ = 2m - tpos J`, then from `6`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open WalkEmbed (tpos tourV)

/-- **The stretches of a kind-1 piece.** -/
theorem piece_stretches {M : Model} {Cα : Chain} {p₀ J : ℕ} (hp₀ : p₀ < M.W.n)
    (hmn : Cα.m < M.W.n)
    (hV : ∀ d, d ≤ Cα.m → M.W.vtx ((p₀ + d) % M.W.n) = tourV Cα J d) :
    (tpos Cα J + Cα.m ≤ 2 * Cα.m → Stretch M Cα p₀ (6 + tpos Cα J) Cα.m) ∧
    (2 * Cα.m < tpos Cα J + Cα.m →
      Stretch M Cα p₀ (6 + tpos Cα J) (2 * Cα.m - tpos Cα J) ∧
      Stretch M Cα ((p₀ + (2 * Cα.m - tpos Cα J)) % M.W.n) 6 (Cα.m - (2 * Cα.m - tpos Cα J))) := by
  have h1 := Cα.one_le
  have ht := WalkEmbed.tpos_lt Cα J
  have hn' := WalkEmbed.cm_n Cα
  refine ⟨fun hs => ⟨fun d hd => ?_, hp₀, h1, hmn, by omega, by omega⟩, fun hs => ⟨⟨fun d hd => ?_,
    hp₀, by omega, by omega, by omega, by omega⟩, ⟨fun d hd => ?_, Nat.mod_lt _ (by omega),
    by omega, by omega, le_rfl, by omega⟩⟩⟩
  · rw [hV d hd, WalkEmbed.walk_tour Cα J d (by omega)]
  · rw [hV d (by omega), WalkEmbed.walk_tour Cα J d (by omega)]
  · have e1 : ((p₀ + (2 * Cα.m - tpos Cα J)) % M.W.n + d) % M.W.n =
        (p₀ + ((2 * Cα.m - tpos Cα J) + d)) % M.W.n := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    have e2 : (6 + d) % (chainModel Cα).W.n =
        (6 + tpos Cα J + (2 * Cα.m - tpos Cα J) + 7 + d) % (chainModel Cα).W.n := by
      rw [hn', show 6 + tpos Cα J + (2 * Cα.m - tpos Cα J) + 7 + d =
        (6 + d) + (2 * Cα.m + 7) by omega, Nat.add_mod_right]
    rw [e1, hV _ (by omega), e2, WalkEmbed.walk_after Cα J d (by omega)]

/-- **The direction test**: the height vertex `h` of the piece's first vertex is the chain's first
vertex iff the walk goes up the chain. -/
theorem dir_correct {M : Model} {Q : Polygon} (hDH : DistinctHeights Q) {Cα : Chain}
    (hQ : Cα.P = Q) {s h : ℕ} (hh : h < Q.n) (hsP : Cα.s < Q.n) (hsn : s < M.W.n)
    (hy : (Q.vtx h).2 = (M.W.vtx s).2)
    (hdir : (∀ d, d ≤ Cα.m → M.W.vtx ((s + d) % M.W.n) = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m → M.W.vtx ((s + d) % M.W.n) = Cα.vertex (Cα.m - d))) :
    ∀ d, d ≤ Cα.m → M.W.vtx ((s + d) % M.W.n) = tourV Cα (if h = Cα.s then 0 else Cα.m) d := by
  have h1 := Cα.one_le
  have hmn := Cα.add_one_le
  rw [hQ] at hmn
  have v0 : Cα.vertex 0 = Q.vtx Cα.s := by
    unfold Chain.vertex Chain.edgeIdx; rw [hQ, Nat.add_zero, Nat.mod_eq_of_lt hsP]
  have vm : Cα.vertex Cα.m = Q.vtx ((Cα.s + Cα.m) % Q.n) := by
    unfold Chain.vertex Chain.edgeIdx; rw [hQ]
  have hs0 : (s + 0) % M.W.n = s := by rw [Nat.add_zero, Nat.mod_eq_of_lt hsn]
  rcases hdir with hu | hd
  · have e := hu 0 (Nat.zero_le _)
    rw [hs0, v0] at e
    have hhs : h = Cα.s := by
      by_contra hne; exact hDH h Cα.s hh hsP hne (by rw [hy, e])
    rw [ite_eq_left hhs]
    intro d hd'; rw [hu d hd', ShootCut.tourV_up Cα hd']
  · have e := hd 0 (Nat.zero_le _)
    rw [hs0, Nat.sub_zero, vm] at e
    have hlt := Nat.mod_lt (Cα.s + Cα.m) (by omega : 0 < Q.n)
    have hne : (Cα.s + Cα.m) % Q.n ≠ Cα.s := by
      intro h'
      by_cases hc : Cα.s + Cα.m < Q.n
      · rw [Nat.mod_eq_of_lt hc] at h'; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h'; omega
    have hhs : h = (Cα.s + Cα.m) % Q.n := by
      by_contra hne'; exact hDH h _ hh hlt hne' (by rw [hy, e])
    rw [ite_eq_right (by rw [hhs]; exact hne)]
    intro d hd'; rw [hd d hd', ShootCut.tourV_down Cα hd']

end

end Restore

end Chazelle.Core
