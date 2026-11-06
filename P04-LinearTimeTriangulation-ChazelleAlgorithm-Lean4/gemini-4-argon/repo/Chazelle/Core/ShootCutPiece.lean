module

public import Chazelle.Core.WalkEmbedChain
public import Chazelle.Core.NFBuildWt

/-!
# WP-G, part 1: the kind-1 pieces of the arc-cutter

A kind-1 piece of the arc-cutter (`CutterOK`, p. 501 (ii)) is a stretch of `w` consecutive walk
edges `p₀, …, p₀ + w - 1` of a model `M` whose walk vertices are, in order, the vertices of a
chain `Cα` read from some tour position of `Cα` (`M.W.vtx (p₀ + d) = tourV Cα J d`).  For the
cutter, `Cα` is a grade chain of `Q` traversed upward (`J = 0`) or downward (`J = m`).

* `arcSet_nat`: the point set of the key interval `[p₀, p₀ + w]` is the union of the `w` walk
  edge segments;
* `arcSet_tour`: for a stretch agreeing with the tour of `Cα` from `J = 0` or `J = Cα.m`, it is
  `Cα.set`;
* `pieceWalk_tour`: the stretch satisfies `PieceWalk` (review finding E5), for any tour position
  `J`: one stretch of the walk of `chainModel Cα`, or two meeting at its top;
* `arcWt_chain_nat`: in a chain model, a stretch of `w` counted edges has weight `w`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)
open Chazelle.Geometry (lerp)

namespace ShootCut

/-! ## The point set of a key interval between two walk vertices -/

/-- The parameter of a walk vertex position is `0`. -/
@[simp] theorem param_hgt0 (M : Model) (Q : Polygon) (p : ℕ) : M.param Q ⟨p, 0⟩ = 0 := rfl

@[simp] theorem key_hgt0 (M : Model) (Q : Polygon) (p : ℕ) : M.key Q ⟨p, 0⟩ = p := by
  simp [Model.key]

theorem lerp_mem_segment {a b : Point} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lerp a b t ∈ Chazelle.segment a b := ⟨t, h0, h1, rfl⟩

/-- **The point set of the key interval `[p₀, p₀ + w]`** (walk vertices, `w ≥ 1`): the union of
the segments of the walk edges `p₀, …, p₀ + w - 1`. -/
theorem arcSet_nat {M : Model} {p₀ w : ℕ} (hw : 1 ≤ w) (hn : p₀ + w < M.W.n) (x : Point) :
    x ∈ M.arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ) ↔
      ∃ d, d < w ∧ x ∈ Chazelle.segment (M.W.vtx (p₀ + d)) (M.W.vtx (p₀ + d + 1)) := by
  have hab : (p₀ : ℝ) < ((p₀ + w : ℕ) : ℝ) := by exact_mod_cast (by omega : p₀ < p₀ + w)
  have hwb : ∀ p, p + 1 < M.W.n → M.wb p = M.W.vtx (p + 1) := fun p hp => by
    unfold Model.wb; rw [Nat.mod_eq_of_lt hp]
  constructor
  · rintro ⟨p, t, hp, ht0, ht1, hc, rfl⟩
    have hrange : (p₀ : ℝ) ≤ p + t ∧ (p : ℝ) + t ≤ ((p₀ + w : ℕ) : ℝ) := by
      rcases hc with hc | hc | hc
      · unfold sideInArc at hc; rw [ite_eq_left hab] at hc; exact ⟨hc.1.le, hc.2.le⟩
      · exact ⟨hc.ge, by linarith⟩
      · exact ⟨by linarith, hc.le⟩
    push_cast at hrange
    by_cases hlo : p < p₀
    · -- `p = p₀ - 1`, `t = 1`: the vertex `p₀`
      have h1 : (p : ℝ) + 1 ≤ p₀ := by exact_mod_cast hlo
      have ht : t = 1 := by linarith
      have hpp : p + 1 = p₀ := by
        have : (p₀ : ℝ) ≤ p + 1 := by linarith
        have : p₀ ≤ p + 1 := by exact_mod_cast this
        omega
      refine ⟨0, by omega, 0, le_rfl, zero_le_one, ?_⟩
      unfold Model.wa
      rw [ht, hwb p (by omega), hpp]
      simp [lerp]
    by_cases hhi : p₀ + w ≤ p
    · -- `p = p₀ + w`, `t = 0`: the vertex `p₀ + w`
      have h1 : ((p₀ + w : ℕ) : ℝ) ≤ p := by exact_mod_cast hhi
      push_cast at h1
      have ht : t = 0 := by linarith
      have hpp : p = p₀ + w := by
        have : (p : ℝ) ≤ p₀ + w := by linarith
        have : p ≤ p₀ + w := by exact_mod_cast this
        omega
      refine ⟨w - 1, by omega, 1, zero_le_one, le_rfl, ?_⟩
      unfold Model.wa
      rw [ht, hpp, show p₀ + (w - 1) + 1 = p₀ + w by omega]
      simp [lerp]
    · refine ⟨p - p₀, by omega, t, ht0, ht1, ?_⟩
      unfold Model.wa
      rw [hwb p (by omega), show p₀ + (p - p₀) = p by omega]
      rfl
  · rintro ⟨d, hd, t, ht0, ht1, rfl⟩
    refine ⟨p₀ + d, t, by omega, ht0, ht1, ?_, ?_⟩
    · have hk0 : (p₀ : ℝ) ≤ ((p₀ + d : ℕ) : ℝ) + t := by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      have hk1 : ((p₀ + d : ℕ) : ℝ) + t ≤ ((p₀ + w : ℕ) : ℝ) := by
        have : ((d : ℕ) : ℝ) + 1 ≤ w := by exact_mod_cast hd
        push_cast; linarith
      rcases hk0.lt_or_eq with hk0 | hk0
      · rcases hk1.lt_or_eq with hk1 | hk1
        · left; unfold sideInArc; rw [ite_eq_left hab]; exact ⟨hk0, hk1⟩
        · right; right; exact hk1
      · right; left; exact hk0.symm
    · unfold Model.wa
      rw [hwb (p₀ + d) (by omega)]
      rfl

/-! ## Stretches along the tour of a chain -/

theorem tourV_up (Cα : Chain) {d : ℕ} (hd : d ≤ Cα.m) : WalkEmbed.tourV Cα 0 d = Cα.vertex d := by
  unfold WalkEmbed.tourV
  have := Cα.one_le
  rw [zero_add, Nat.mod_eq_of_lt (by omega)]
  unfold sideE; rw [ite_eq_left hd]

theorem tourV_down (Cα : Chain) {d : ℕ} (hd : d ≤ Cα.m) :
    WalkEmbed.tourV Cα Cα.m d = Cα.vertex (Cα.m - d) := by
  unfold WalkEmbed.tourV
  have := Cα.one_le
  rcases hd.lt_or_eq with hd | rfl
  · rw [Nat.mod_eq_of_lt (by omega)]
    unfold sideE
    by_cases h : Cα.m + d ≤ Cα.m
    · have : d = 0 := by omega
      subst this; simp
    · rw [ite_eq_right h]; congr 1; omega
  · rw [show Cα.m + Cα.m = 2 * Cα.m by ring, Nat.mod_self]
    unfold sideE; simp

theorem segment_mem_set (Cα : Chain) {k : ℕ} (hk : k < Cα.m) {x : Point}
    (hx : x ∈ Chazelle.segment (Cα.vertex k) (Cα.vertex (k + 1))) : x ∈ Cα.set :=
  ⟨k, hk, by rw [Cα.chainEdge_eq]; exact hx⟩

/-- **The point set of a kind-1 piece**: a stretch of `Cα.m` walk edges whose vertices are those
of the tour of `Cα` read upward (`J = 0`) or downward (`J = Cα.m`) has the point set `Cα.set`. -/
theorem arcSet_tour {M : Model} {Cα : Chain} {p₀ J : ℕ} (hJ : J = 0 ∨ J = Cα.m)
    (hn : p₀ + Cα.m < M.W.n)
    (hV : ∀ d, d ≤ Cα.m → M.W.vtx (p₀ + d) = WalkEmbed.tourV Cα J d) :
    M.arcSet (p₀ : ℝ) ((p₀ + Cα.m : ℕ) : ℝ) = Cα.set := by
  have h1 := Cα.one_le
  ext x
  rw [arcSet_nat h1 hn]
  rcases hJ with rfl | rfl
  · have hV' : ∀ d, d ≤ Cα.m → M.W.vtx (p₀ + d) = Cα.vertex d := fun d hd => by
      rw [hV d hd, tourV_up Cα hd]
    constructor
    · rintro ⟨d, hd, hx⟩
      rw [hV' d hd.le, show p₀ + d + 1 = p₀ + (d + 1) by ring, hV' (d + 1) hd] at hx
      exact segment_mem_set Cα hd hx
    · rintro ⟨k, hk, hx⟩
      rw [Cα.chainEdge_eq] at hx
      refine ⟨k, hk, ?_⟩
      rwa [hV' k hk.le, show p₀ + k + 1 = p₀ + (k + 1) by ring, hV' (k + 1) hk]
  · have hV' : ∀ d, d ≤ Cα.m → M.W.vtx (p₀ + d) = Cα.vertex (Cα.m - d) := fun d hd => by
      rw [hV d hd, tourV_down Cα hd]
    constructor
    · rintro ⟨d, hd, hx⟩
      rw [hV' d hd.le, show p₀ + d + 1 = p₀ + (d + 1) by ring, hV' (d + 1) hd,
        Chazelle.Geometry.segment_comm] at hx
      refine segment_mem_set Cα (k := Cα.m - (d + 1)) (by omega) ?_
      rwa [show Cα.m - (d + 1) + 1 = Cα.m - d by omega]
    · rintro ⟨k, hk, hx⟩
      rw [Cα.chainEdge_eq] at hx
      refine ⟨Cα.m - (k + 1), by omega, ?_⟩
      rwa [hV' _ (by omega), show p₀ + (Cα.m - (k + 1)) + 1 = p₀ + (Cα.m - k) by omega,
        hV' _ (by omega), show Cα.m - (Cα.m - (k + 1)) = k + 1 by omega,
        show Cα.m - (Cα.m - k) = k by omega, Chazelle.Geometry.segment_comm]

/-- **The walk of a kind-1 piece** (`PieceWalk`, finding E5): a stretch of `Cα.m` walk edges of
`M` agreeing with the tour of `Cα` read from any tour position `J`. -/
theorem pieceWalk_tour {M : Model} {Cα : Chain} {p₀ J : ℕ} (hp₀ : p₀ < M.W.n)
    (hV : ∀ d, d ≤ Cα.m → M.W.vtx ((p₀ + d) % M.W.n) = WalkEmbed.tourV Cα J d) :
    PieceWalk M Cα ⟨p₀, 0⟩ ⟨(p₀ + Cα.m) % M.W.n, 0⟩ := by
  have ht := WalkEmbed.tpos_lt Cα J
  have hn' := WalkEmbed.cm_n Cα
  refine ⟨rfl, rfl, hp₀, rfl, ?_⟩
  by_cases hs : WalkEmbed.tpos Cα J + Cα.m ≤ 2 * Cα.m
  · refine ⟨6 + WalkEmbed.tpos Cα J, by omega, Or.inl ?_⟩
    intro d hd
    rw [hV d hd, WalkEmbed.walk_tour Cα J d (by omega)]
  · set L₁ := 2 * Cα.m - WalkEmbed.tpos Cα J
    refine ⟨6 + WalkEmbed.tpos Cα J, by omega, Or.inr ⟨L₁, by omega, by omega, by omega, ?_, ?_⟩⟩
    · intro d hd
      rw [hV d (by omega), WalkEmbed.walk_tour Cα J d (by omega)]
    · intro d hd
      have e1 : ((p₀ + L₁) % M.W.n + d) % M.W.n = (p₀ + (L₁ + d)) % M.W.n := by
        rw [Nat.mod_add_mod, Nat.add_assoc]
      have e2 : (6 + d) % (chainModel Cα).W.n =
          (6 + WalkEmbed.tpos Cα J + (2 * Cα.m - WalkEmbed.tpos Cα J) + 7 + d) %
            (chainModel Cα).W.n := by
        rw [hn', show 6 + WalkEmbed.tpos Cα J + (2 * Cα.m - WalkEmbed.tpos Cα J) + 7 + d =
          (6 + d) + (2 * Cα.m + 7) by omega, Nat.add_mod_right]
      rw [e1, hV _ (by omega), e2, WalkEmbed.walk_after Cα J d (by omega)]

/-! ## Weights in a chain model -/

/-- **The weight of a stretch of counted edges** in a chain model: `w`. -/
theorem arcWt_chain_nat (C : Chain) {p₀ w : ℕ} (hw : 1 ≤ w) (h6 : 6 ≤ p₀)
    (hn : p₀ + w ≤ 2 * C.m + 6) :
    (chainModel C).arcWt (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ) = w := by
  have h := (chainModel C).arcWt_closed (lo := 6) (hi := 2 * C.m + 6)
    (fun p hp => chainModel_counted_iff C p hp) (by rw [chainModel_n]; omega)
    (ea := p₀) (eb := p₀ + w) (fa := 0) (fb := 0) ⟨le_rfl, zero_lt_one⟩ ⟨le_rfl, zero_lt_one⟩
  simp only [add_zero] at h
  rw [h]
  unfold arcWtNat keyCeil
  rw [ite_eq_left (by exact_mod_cast (by omega : p₀ < p₀ + w)), ite_eq_left rfl]
  omega

end ShootCut

end

end Chazelle.Core
