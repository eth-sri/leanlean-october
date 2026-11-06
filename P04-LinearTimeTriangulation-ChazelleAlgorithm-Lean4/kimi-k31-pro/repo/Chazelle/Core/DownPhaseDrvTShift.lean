module

public import Chazelle.Core.DownPhaseTransMain
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# Down-phase transition (D2), part 1: the inner-side shift, explicitly

For the top chain `C` of a simple polygon `Q` with distinct heights, the interior walk of `Q`
(`interiorWalk Q`) runs along one side of the double boundary of `C`: chain walk vertex
`j + c₀` is interior walk vertex `j` for `j ≤ m` (`Trans.exists_shift`).  Here the shift is
given explicitly (`c0 C li = i0 C li + 6`, `i0` the side-`A` tour index of chain edge `0` if
`LeftInside Q`, else of chain edge `m`), so that the RAM can compute it from the top index, the
orientation bit `sideBeta` and the `LeftInside` bit:

* `shift_c0`: `Trans.Shift Q C (c0 C li)`;
* `uturn_zero`, `uturn_last`: when the interior walk vertex `0` (resp. `m`) is not the top
  vertex, the chain walk turns around there (the walk vertices before and after it agree);
* `sideLeft_uturn`: at such a turn every horizontal direction is in the left sector;
* `idxI`: the input index of an interior walk vertex.
-/

namespace Chazelle.Core

namespace DrvT

@[expose] public section

open Set
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideE sideCcw sideCross sideDot)
open TourA (sA tourA)

variable {Q : Polygon} {C : Chain}

/-- The input index of interior walk vertex `j` (`n` vertices). -/
def idxI (li : Bool) (n j : ℕ) : ℕ := if li then j else n - 1 - j

/-- **The tour index** of interior walk vertex `0`: the side-`A` tour index of chain edge `0`
(if `LeftInside`) or of chain edge `m`. -/
noncomputable def i0 (C : Chain) (li : Bool) : ℕ := tourA C C.sideBeta (if li then 0 else C.m)

/-- **The inner-side shift** of the top chain. -/
noncomputable def c0 (C : Chain) (li : Bool) : ℕ := i0 C li + 6

theorem iw_vtx_idx {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {j : ℕ} (hj : j < Q.n) :
    (interiorWalk Q).vtx j = Q.vtx (idxI li Q.n j) := by
  unfold idxI
  by_cases h : li = true
  · rw [ite_eq_left h]; exact Trans.iw_vtx_left (hli.1 h) j
  · rw [ite_eq_right h]; exact Trans.iw_vtx_right (fun h' => h (hli.2 h')) hj

theorem idxI_lt {li : Bool} {n j : ℕ} (hj : j < n) : idxI li n j < n := by
  unfold idxI; splao

/-- The tour start residue at `i0`. -/
theorem mod_i0 (li : Bool) :
    (C.sideS C.sideBeta + i0 C li) % (2 * C.m) = if li then 0 else C.m := by
  have hm := C.one_le
  unfold i0
  split_ifs with h
  · exact TourA.mod_tourA (by omega)
  · exact TourA.mod_tourA (by omega)

/-- `sA` is the reduced tour start. -/
theorem sA_eq : sA C C.sideBeta = C.sideS C.sideBeta % (2 * C.m) := rfl

/-- The value of `i0` in terms of `sA`. -/
theorem i0_eq (li : Bool) :
    i0 C li = if li then (2 * C.m - sA C C.sideBeta) % (2 * C.m)
      else (3 * C.m - sA C C.sideBeta) % (2 * C.m) := by
  unfold i0 tourA
  split_ifs with h
  · rw [zero_add]
  · congr 1; omega

/-- **`sA` and the top index.** -/
theorem sA_top : (sA C C.sideBeta = C.topIdx ∧ C.topIdx < 2 * C.m) ∨
    (sA C C.sideBeta = 2 * C.m - C.topIdx ∧ 0 < C.topIdx) := by
  have hT := C.topIdx_le
  have hm := C.one_le
  rcases C.sideS_mod C.sideBeta with ⟨h, -⟩ | ⟨h, h0, -⟩
  · left; exact ⟨h, by omega⟩
  · right; exact ⟨h, h0⟩

theorem sA_lt' : sA C C.sideBeta < 2 * C.m := TourA.sA_lt

/-- `sA = 0` exactly when the top is the first vertex. -/
theorem sA_zero_iff : sA C C.sideBeta = 0 ↔ C.topIdx = 0 := by
  have hT := C.topIdx_le
  have hm := C.one_le
  rcases sA_top (C := C) with ⟨h, -⟩ | ⟨h, h0⟩ <;> omega

/-- `sA = m` exactly when the top is the last vertex. -/
theorem sA_m_iff : sA C C.sideBeta = C.m ↔ C.topIdx = C.m := by
  have hT := C.topIdx_le
  have hm := C.one_le
  rcases sA_top (C := C) with ⟨h, -⟩ | ⟨h, h0⟩ <;> omega

variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli

/-- `i0 ≤ m`. -/
theorem i0_le : i0 C li ≤ C.m := by
  have hm := C.one_le
  have hs := sA_lt' (C := C)
  obtain ⟨hL1, hL2⟩ := Trans.sA_inner hQ T hD
  rw [i0_eq]
  by_cases h : li = true
  · rw [ite_eq_left h]
    rcases hL1 (hli.1 h) with h0 | h0
    · rwo [h0, Nat.sub_zero, Nat.mod_self]
    · rwo [Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h]
    have h1 := hL2 (fun h' => h (hli.2 h'))
    rw [show 3 * C.m - sA C C.sideBeta = (C.m - sA C C.sideBeta) + 2 * C.m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Chain walk vertex `j + c₀` is interior walk vertex `j`.** -/
theorem vtx_c0 {j : ℕ} (hj : j ≤ C.m) :
    (C.sideWalk C.sideBeta).vtx (j + c0 C li) = (interiorWalk Q).vtx j := by
  have hm := C.one_le
  have hmn := T.hm
  have hle := i0_le hQ T hD hli
  have hr := mod_i0 (C := C) li
  unfold c0
  rw [show j + (i0 C li + 6) = (j + i0 C li) + 6 by ring,
    C.sideWalk_vtx_tour _ (by omega), iw_vtx_idx hli (by omega)]
  unfold Chain.sideTour
  rw [Chain.sideIdx_eq, show C.sideS C.sideBeta + (j + i0 C li) =
      (C.sideS C.sideBeta + i0 C li) + j by ring, Nat.add_mod, hr]
  have hv : ∀ k, k ≤ C.m → C.vertex k = Q.vtx k := fun k hk => T.vertex_eq (by omega)
  unfold idxI
  by_cases h : li = true
  · simp only [h, ite_true, zero_add, Nat.mod_mod]
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold sideE; rw [ite_eq_left hj]; exact hv j hj
  · simp only [h, Bool.false_eq_true, ite_false]
    rw [Nat.mod_eq_of_lt (show j < 2 * C.m by omega)]
    rcases hj.lt_or_eq with hj' | rfl
    · rw [Nat.mod_eq_of_lt (by omega)]
      unfold sideE
      rw [hv _ (by splao)]
      congr 1
      splao
    · rw [show C.m + C.m = 2 * C.m by ring,
        Nat.mod_self, Chazelle.Chain.sideE_zero, hv 0 (by omega)]
      congr 1; omega

/-- **The explicit shift.** -/
theorem shift_c0 : Trans.Shift Q C (c0 C li) := by
  have hle := i0_le hQ T hD hli
  exact ⟨by ufo c0, by ufo c0, fun j hj => vtx_c0 hQ T hD hli hj⟩

/-- **The turn at interior walk vertex `0`**: unless it is the top vertex, the chain walk comes
back from interior walk vertex `1` and goes on to it. -/
theorem uturn_zero (hne : (interiorWalk Q).vtx 0 ≠ C.top) :
    1 ≤ i0 C li ∧ (C.sideWalk C.sideBeta).vtx (c0 C li - 1) = (interiorWalk Q).vtx 1 := by
  have hm := C.one_le
  have hmn := T.hm
  have hle := i0_le hQ T hD hli
  have hr := mod_i0 (C := C) li
  have hs := sA_lt' (C := C)
  obtain ⟨hL1, hL2⟩ := Trans.sA_inner hQ T hD
  have hv : ∀ k, k ≤ C.m → C.vertex k = Q.vtx k := fun k hk => T.vertex_eq (by omega)
  have htop : C.top = Q.vtx C.topIdx := hv _ C.topIdx_le
  have h1 : 1 ≤ i0 C li := by
    by_contra h0
    push Not at h0
    have hi0 : i0 C li = 0 := by omega
    apply hne
    rw [htop, iw_vtx_idx hli (by omega)]
    unfold idxI
    rw [i0_eq] at hi0
    by_cases h : li = true
    · rw [ite_eq_left h] at hi0 ⊢
      have : sA C C.sideBeta = 0 := by
        by_contra hne0
        rwo [Nat.mod_eq_of_lt (by omega)] at hi0
      rw [sA_zero_iff.1 this]
    · rw [ite_eq_right h] at hi0 ⊢
      have h2 := hL2 (fun h' => h (hli.2 h'))
      rw [show 3 * C.m - sA C C.sideBeta = (C.m - sA C C.sideBeta) + 2 * C.m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hi0
      rw [sA_m_iff.1 (by omega)]
      congr 1; omega
  refine ⟨h1, ?_⟩
  unfold c0
  rw [show i0 C li + 6 - 1 = (i0 C li - 1) + 6 by omega, C.sideWalk_vtx_tour _ (by omega),
    iw_vtx_idx hli (by omega)]
  unfold Chain.sideTour
  rw [Chain.sideIdx_eq]
  -- the residue before `i0`
  set q := (C.sideS C.sideBeta + (i0 C li - 1)) % (2 * C.m) with hq
  have hqlt : q < 2 * C.m := Nat.mod_lt _ (by omega)
  have hsucc : (q + 1) % (2 * C.m) = if li then 0 else C.m := by
    rw [← hr, show C.sideS C.sideBeta + i0 C li = (C.sideS C.sideBeta + (i0 C li - 1)) + 1 by
      omega, Nat.add_mod (C.sideS C.sideBeta + (i0 C li - 1)) 1,
      Nat.mod_eq_of_lt (show 1 < 2 * C.m by omega)]
  unfold idxI
  by_cases h : li = true
  · rw [ite_eq_left h] at hsucc ⊢
    have hq' : q = 2 * C.m - 1 := by
      rcases (show q + 1 < 2 * C.m ∨ q + 1 = 2 * C.m by omega) with h2 | h2
      · rwo [Nat.mod_eq_of_lt h2] at hsucc
      · omega
    rw [hq', hv _ (by unfold sideE; splao)]
    congr 1; unfold sideE; splao
  · rw [ite_eq_right h] at hsucc ⊢
    have hq' : q = C.m - 1 := by
      rcases (show q + 1 < 2 * C.m ∨ q + 1 = 2 * C.m by omega) with h2 | h2
      · rwo [Nat.mod_eq_of_lt h2] at hsucc
      · rwo [h2, Nat.mod_self] at hsucc
    rw [hq', hv _ (by unfold sideE; splao)]
    congr 1; unfold sideE; splao

/-- **The turn at interior walk vertex `m`**: unless it is the top vertex, the chain walk goes
back to interior walk vertex `m - 1`. -/
theorem uturn_last (hne : (interiorWalk Q).vtx C.m ≠ C.top) :
    i0 C li < C.m ∧
      (C.sideWalk C.sideBeta).vtx (c0 C li + C.m + 1) = (interiorWalk Q).vtx (C.m - 1) := by
  have hm := C.one_le
  have hmn := T.hm
  have hle := i0_le hQ T hD hli
  have hr := mod_i0 (C := C) li
  have hs := sA_lt' (C := C)
  obtain ⟨hL1, hL2⟩ := Trans.sA_inner hQ T hD
  have hv : ∀ k, k ≤ C.m → C.vertex k = Q.vtx k := fun k hk => T.vertex_eq (by omega)
  have htop : C.top = Q.vtx C.topIdx := hv _ C.topIdx_le
  have h1 : i0 C li < C.m := by
    by_contra h0
    push Not at h0
    have hi0 : i0 C li = C.m := by omega
    apply hne
    rw [htop, iw_vtx_idx hli (by omega)]
    unfold idxI
    rw [i0_eq] at hi0
    by_cases h : li = true
    · rw [ite_eq_left h] at hi0 ⊢
      have : sA C C.sideBeta = C.m := by
        by_cases h00 : sA C C.sideBeta = 0
        · rwo [h00, Nat.sub_zero, Nat.mod_self] at hi0
        · rwo [Nat.mod_eq_of_lt (by omega)] at hi0
      rw [sA_m_iff.1 this]
    · rw [ite_eq_right h] at hi0 ⊢
      have h2 := hL2 (fun h' => h (hli.2 h'))
      rw [show 3 * C.m - sA C C.sideBeta = (C.m - sA C C.sideBeta) + 2 * C.m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hi0
      rw [sA_zero_iff.1 (by omega)]
      congr 1; omega
  refine ⟨h1, ?_⟩
  unfold c0
  rw [show i0 C li + 6 + C.m + 1 = (i0 C li + C.m + 1) + 6 by ring,
    C.sideWalk_vtx_tour _ (by omega), iw_vtx_idx hli (by omega)]
  unfold Chain.sideTour
  rw [Chain.sideIdx_eq, show C.sideS C.sideBeta + (i0 C li + C.m + 1) =
      (C.sideS C.sideBeta + i0 C li) + (C.m + 1) by ring, Nat.add_mod, hr]
  unfold idxI
  by_cases h : li = true
  · simp only [h, ite_true, zero_add, Nat.mod_mod]
    rcases (show C.m + 1 < 2 * C.m ∨ C.m + 1 = 2 * C.m by omega) with h2 | h2
    · rw [Nat.mod_eq_of_lt h2, hv _ (by unfold sideE; splao)]
      congr 1; unfold sideE; splao
    · rw [h2, Nat.mod_self, Chazelle.Chain.sideE_zero, hv 0 (by omega)]
      congr 1; omega
  · simp only [h, Bool.false_eq_true, ite_false]
    rcases (show C.m + 1 < 2 * C.m ∨ C.m + 1 = 2 * C.m by omega) with h2 | h2
    · rw [Nat.mod_eq_of_lt h2, show C.m + (C.m + 1) = 1 + 2 * C.m by ring, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), hv _ (by unfold sideE; split_ifs; omega)]
      congr 1; unfold sideE; split_ifs; omega
    · rw [h2, Nat.mod_self, add_zero, Nat.mod_eq_of_lt (by omega),
        hv _ (by unfold sideE; splao)]
      congr 1; unfold sideE; splao

omit hQ T hD hli in
/-- **At a turn every horizontal direction is in the left sector.** -/
theorem sideLeft_uturn {W : Polygon} {p : ℕ} {a : Point}
    (hprev : W.vtx ((p + W.n - 1) % W.n) = a) (hnext : W.vtx ((p + 1) % W.n) = a)
    (ha : a.2 ≠ (W.vtx p).2) {x : Point} (hx : x.2 = (W.vtx p).2) (hxv : x ≠ W.vtx p) :
    sideLeft W p 0 x := by
  rw [Chazelle.Chain.sideLeft_zero, hprev, hnext]
  unfold sideLeftOf sideCcw
  right; right; right
  have hB : a - W.vtx p ≠ 0 := by
    intro h; apply ha; have := congrArg Prod.snd h; sil at this
  refine ⟨Chazelle.Chain.sideCross_self _, Chazelle.Chain.sideDot_self_pos hB, Or.inl ?_⟩
  have hx1 : x.1 ≠ (W.vtx p).1 := fun h => hxv (Prod.ext h hx)
  unfold sideCross
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [hx, sub_self, mul_zero, zero_sub, neg_ne_zero]
  exact mul_ne_zero (sub_ne_zero.2 ha) (sub_ne_zero.2 hx1)

end

end DrvT

end Chazelle.Core
