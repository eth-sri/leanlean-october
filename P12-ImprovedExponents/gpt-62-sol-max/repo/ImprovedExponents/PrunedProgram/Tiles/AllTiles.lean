module

import ThreeSumApsp.Lang.Lib.Rect

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles
public import ImprovedExponents.PrunedProgram.Tiles.Contracts
import all ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles

@[expose] public section

/-!
# The tries of all tiles, on pruned encodings

The rectangular traversal calls `tile` with the addresses of its two encodings, but does not
read those encodings itself. Its invariant `AllTiles.Mem` tracks the trie and roots in memory.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

open private length_roots_triesBefore tries_tileArgs
  from ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles

namespace AllTilesP

open AllTiles

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ}

/-- The surroundings of the tile (β, β'). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.tileCtx)
private theorem tileCtx (C : AllTilesPreP lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB) :
    TileCtx lim x.L x.m x.t (x.encA β) (x.encB β') (x.aENCA + β * 10 ^ x.L)
      (x.aENCB + β' * 10 ^ x.L) x.tr x.cap x.fp x.cur x.box := by
  have horder := C.order
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  obtain ⟨A, B, hA, hB, hAB⟩ := C.value_le
  generalize β * 10 ^ x.L = a at *
  generalize β' * 10 ^ x.L = b at *
  generalize x.nB * 10 ^ x.L = z at *
  generalize x.nB * x.nB = q at *
  exact
    { std := C.std, ht := C.t_le, hmL := C.m_le, value_le := ⟨A, B, hA β, hB β', hAB⟩
      pow_le := C.pow_le, layout := by light_order }

/-- Before the tile (β, β') the memory holds what tile assumes: the encodings of the two bands
are right at the leaves with few symbols `P₀`, as nothing below cur has changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean
-- (AllTiles.tileArgs_pre)
private theorem tileArgs_pre (C : AllTilesPreP lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB)
    {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') : TilePreP lim μ' (tileArgs x β β') := by
  light_facts C
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hlenR := length_roots_triesBefore x β β'
  have hlenT := length_allTries_le x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  rw [length_tilesBefore] at hlenT
  have hroom := Nat.mul_add_le_mul hi (le_refl (11 * (1 + x.L * (boxes x.L x.m x.t).card)))
  have hA : SegOn x.m μ' (x.aENCA + β * 10 ^ x.L) (x.encA β) :=
    (C.segA β hβ).keep (by light_keep [M.same])
  have hB : SegOn x.m μ' (x.aENCB + β' * 10 ^ x.L) (x.encB β') :=
    (C.segB β' hβ').keep (by light_keep [M.same])
  have hlenT' : (triesBefore x β β').cells.length
      ≤ 1 + (β * x.nB + β') * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) := hlenT
  exact
    { ctx := tileCtx C hβ hβ'
      rep := allTries_rep x.L x.m x.t _
      trie := M.trie
      roots := M.roots
      segA := hA
      segB := hB
      room := by simp only [tileArgs]; omega
      rootsPlace := by simp only [tileArgs, TileArgs.cells]; omega }

/-- The call of `tile` for the tile (β, β') leads from the memory before this tile to the memory
before the next one. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.tile_meets)
private theorem tile_meets (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 3 ≤ lim.depth) {μ' : ℕ → ℤ} (M : Mem μ μ' x β β') :
    Meets lim P Proc.tile d [(x.aENCA + β * 10 ^ x.L : ℕ), (x.aENCB + β' * 10 ^ x.L : ℕ),
      (x.aR + (β * x.nB + β') : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ'
      (tTile x.L x.m x.t) fun _ μ'' => Mem μ μ'' x β (β' + 1) := by
  have horder := C.order
  have hlenR := length_roots_triesBefore x β β'
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hmeets := hTile _ μ' (tileArgs_pre C hβ hβ' M) _ hd
  rw [← hlenR]
  refine hmeets.mono le_rfl fun _ μ'' ⟨htrie, hroots, same⟩ =>
    ⟨tries_tileArgs x β β' ▸ htrie, tries_tileArgs x β β' ▸ hroots,
      M.same.then same fun c hc => ⟨hc, ?_⟩⟩
  -- a cell below cur or behind the trie area is none of those that tile may change
  light_side [hc, TileArgs.Kept, tileArgs, Outside]

end AllTilesP

open AllTiles AllTilesP in
/-- Build all tile tries on pruned encodings. -/
theorem allTilesP_spec {lim : Limits} {P : Program} (hP : P[Proc.allTiles]? = some allTilesBody)
    (hTile : TileSpecP lim P) : AllTilesSpecP lim P := by
  intro x μ C d hd
  refine ⟨allTilesBody, hP, ?_⟩
  light_facts C C.std
  have hnB : x.nB ≤ x.nB * x.nB := Nat.le_mul_self _
  let args : List ℤ := [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp,
    x.cur, x.box, x.L, (x.m - x.t : ℕ)]
  change Ends _ _ _ _ ⟨frame args, μ⟩ _ _
  rw [← frame_append_zeros args 3]
  unfold allTilesBody tAllTiles
  refine Ends.forRect (fun r : ℤ => frame (args ++ [0, 0, r])) (fun i j _ η => Mem μ η x i j)
    (n := x.nB) (m := x.nB) (b := tTile x.L x.m x.t + 40) 0 ?_ (by omega) (by omega) (by simp [args]) (by simp [args]) ?_ ?_ ?_
    (hT := by
      have h := Nat.mul_le_mul_left x.nB (show tTile x.L x.m x.t + 40 + 8 ≤ tTile x.L x.m x.t + 80 by omega)
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add h (by decide))) (by decide))
  · refine ⟨?_, ?_, .refl⟩ <;> rw [triesBefore, tilesBefore_zero]
    · exact C.trie
    · simp [allTries, SegN, Seg]
  · intro i j r η hi hj I
    have hb (k : ℕ) (hk : k < x.nB) : (k : ℤ) * 10 ^ x.L + 10 ^ x.L ≤ (x.nB : ℤ) * 10 ^ x.L := by
      exact_mod_cast Nat.mul_add_le_mul hk (le_refl (10 ^ x.L))
    have hrow := hb i hi
    have hpow0 : (0 : ℤ) ≤ 10 ^ x.L := by positivity
    have hi₀ : 0 ≤ (i : ℤ) * (10 : ℤ) ^ x.L := by positivity
    have hj₀ : 0 ≤ (j : ℤ) * (10 : ℤ) ^ x.L := by positivity
    have hcol := hb j hj
    have hA : (x.aENCA : ℤ) + (x.nB : ℤ) * 10 ^ x.L ≤ x.aENCB := by exact_mod_cast C.order.1
    have hB : (x.aENCB : ℤ) + (x.nB : ℤ) * 10 ^ x.L ≤ x.cur := by exact_mod_cast C.order.2.1
    have hij := Nat.mul_add_lt_mul hi hj
    simp only [rectLoc, update_frame_setLocal]
    refine Ends.callTo (tile_meets hTile C hi hj (by omega) I) ?_ (ha := by light_side [args])
    exact fun v η' hv => ⟨v, rfl, hv⟩
  · intro i r η hi I
    have hb : triesBefore x i x.nB = triesBefore x (i + 1) 0 := by
      rw [triesBefore, tilesBefore_row, triesBefore]
    exact ⟨hb ▸ I.trie, hb ▸ I.roots, I.same⟩
  · intro r j η I
    have hall : triesBefore x x.nB 0 = x.tries := by
      rw [triesBefore, tilesBefore_all, AllTilesArgs.tries]
    exact ⟨hall ▸ I.trie, hall ▸ I.roots, I.same⟩

end Light.Sec4
