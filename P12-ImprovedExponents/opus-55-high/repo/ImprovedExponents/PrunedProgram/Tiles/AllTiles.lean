
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles
import ImprovedExponents.PrunedProgram.Tiles.Contracts
import ThreeSumApsp.Programs.Sec4.Theorem30.AllTiles


/-!
# The tries of all tiles, on pruned encodings

Upstream's `allTiles_spec` proves `allTilesBody` (procedure 51) under `AllTilesPre`, with the
encodings of all bands as full arrays, calling `tile` under `TileSpec`.  The routine reads no
encoding cell; it only computes the addresses of the two encodings of each tile and hands them
on.  So the same body meets the same specification with the encodings right at the leaves with
at most `m` symbols `P₀` only (`AllTilesPreP`, `allTilesP_spec`), given `tile` under `TileSpecP`.
The proof is upstream's; only `tileArgs_pre` changes, which carries the encodings of the two
bands (`SegOn.keep` in place of `Seg.keep`).  The invariant `AllTiles.Mem` and the lemmas
`AllTiles.triesBefore`, `AllTiles.tileArgs` are reused.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec


namespace AllTilesP

open AllTiles

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The surroundings of the tile (β, β'). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.tileCtx)
theorem tileCtx (C : AllTilesPreP lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB) :
    TileCtx lim x.L x.m x.t (x.encA β) (x.encB β') (x.aENCA + β * 10 ^ x.L)
      (x.aENCB + β' * 10 ^ x.L) x.tr x.cap x.fp x.cur x.box := by
  have horder := C.order
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  obtain ⟨A, B, hA, hB, hAB⟩ := C.value_le
  exact
    ⟨C.std, C.t_le, C.m_le, ⟨A, B, hA β, hB β', hAB⟩, C.pow_le, by light_order⟩

variable {μ' : ℕ → ℤ}

/-- Before the tile (β, β') the memory holds what tile assumes: the encodings of the two bands
are right at the leaves with few symbols `P₀`, as nothing below cur has changed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean
-- (AllTiles.tileArgs_pre)
theorem tileArgs_pre (C : AllTilesPreP lim μ x) (hβ : β < x.nB) (hβ' : β' < x.nB)
    (M : Mem μ μ' x β β') : TilePreP lim μ' (tileArgs x β β') := by
  light_facts C
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hrow := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
  have hcol := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  have hlenR := length_roots_triesBefore x β β'
  have hlenT := length_allTries_le x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  rw [length_tilesBefore] at hlenT
  have hroom := Nat.mul_add_le_mul hi (le_refl (11 * (1 + x.L * (boxes x.L x.m x.t).card)))
  have hlenT' : (triesBefore x β β').cells.length
      ≤ 1 + (β * x.nB + β') * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) := hlenT
  exact
    ⟨tileCtx C hβ hβ', allTries_rep x.L x.m x.t _, M.trie, M.roots, (C.segA β hβ).keep (by light_keep [M.same]), (C.segB β' hβ').keep (by light_keep [M.same]), by grind [tileArgs], by grind [tileArgs, TileArgs.cells]⟩

/-- The call of `tile` for the tile (β, β') leads from the memory before this tile to the memory
before the next one. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.tile_meets)
theorem tile_meets (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 3 ≤ lim.depth) (M : Mem μ μ' x β β') :
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
  simp [TileArgs.Kept, tileArgs]
  omega

/-- One tile: the call, and the pointers move on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.step_spec)
theorem step_spec (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hβ' : β' < x.nB) (hd : d + 4 ≤ lim.depth) (h : Inv μ x β β' σ) :
    Ends lim P d allTilesStep σ (tTile x.L x.m x.t + 23) (Inv μ x β (β' + 1)) := by
  obtain ⟨void, μ₁, rfl, M⟩ := h
  light_facts C C.std
  -- tile(rowEnc, colEnc, rootPtr, …)
  light_call (tile_meets hTile C hβ hβ' (by omega) M) with void' μ₂ M₂
  -- rootPtr := rootPtr + 1; colEnc := colEnc + leaves; colBand := colBand + 1
  have hptr : x.aR + (β * x.nB + (β' + 1)) = x.aR + (β * x.nB + β') + 1 := by ring
  have hcol : x.aENCB + (β' + 1) * 10 ^ x.L = x.aENCB + β' * 10 ^ x.L + 10 ^ x.L := by ring
  have hi := Nat.mul_add_lt_mul hβ hβ'
  have hcolS := Nat.mul_add_le_mul hβ' (le_refl (10 ^ x.L))
  unfold AllTiles.Inv
  generalize β * x.nB + β' = ptr at *
  generalize β' * 10 ^ x.L = off at *
  generalize 10 ^ x.L = leaves at *
  light_set (x.aR + ptr + 1)
  light_set (x.aENCB + off + leaves)
  light_set (β' + 1)
  aesop

/-- One row of tiles. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (AllTiles.row_spec)
theorem row_spec (hTile : TileSpecP lim P) (C : AllTilesPreP lim μ x) (hβ : β < x.nB)
    (hd : d + 4 ≤ lim.depth) (h : Inv μ x β 0 σ) :
    Ends lim P d allTilesRow σ (x.nB * (tTile x.L x.m x.t + 27) + 16) (Inv μ x (β + 1) 0) := by
  light_facts C C.std
  -- while β' < nB: one tile
  refine Ends.next _ (Ends.whileConst (Inv μ x β) x.nB (tTile x.L x.m x.t + 23) h ?_ ?_
    le_rfl) (by simp; linarith)
  ·
    rintro β' σ hβ' hI
    have hstep := step_spec hTile C hβ hβ' hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    simp_all
  ·
    rintro _ ⟨void, μ', rfl, M⟩
    refine ⟨by simp, by simp, ?_⟩
    -- rowEnc := rowEnc + leaves; rowBand := rowBand + 1; colBand := 0; colEnc := encB
    have hptr : x.aR + (β + 1) * x.nB + 0 = x.aR + (β * x.nB + x.nB) := by ring
    have hrow : x.aENCA + (β + 1) * 10 ^ x.L = x.aENCA + β * 10 ^ x.L + 10 ^ x.L := by ring
    have hrowS := Nat.mul_add_le_mul hβ (le_refl (10 ^ x.L))
    have hbands : x.nB ≤ x.nB * 10 ^ x.L := by simp_all [Nat.le_mul_of_pos_right]
    have hbefore : triesBefore x β x.nB = triesBefore x (β + 1) 0 := by
      grind [triesBefore, tilesBefore_row]
    have M' : Mem μ μ' x _ 0 := ⟨hbefore ▸ M.trie, hbefore ▸ M.roots, M.same⟩
    unfold AllTiles.Inv
    generalize β * 10 ^ x.L = off at *
    generalize 10 ^ x.L = leaves at *
    light_set (x.aENCA + off + leaves)
    light_set (β + 1)
    light_set 0
    light_set x.aENCB
    aesop

end AllTilesP

open AllTiles AllTilesP in
/-- **allTiles on pruned encodings** meets its specification. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean (allTiles_spec)
theorem allTilesP_spec {lim : Limits} {P : Program} (hP : P[Proc.allTiles]? = some allTilesBody)
    (hTile : TileSpecP lim P) : AllTilesSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨allTilesBody, hP, ?_⟩
  light_facts C.std
  have htime := time_le x.nB (tTile x.L x.m x.t)
  unfold tAllTiles
  -- β := 0; β' := 0; the three pointers at the first tile
  light_set 0
  light_set 0
  light_set x.aR
  light_set x.aENCA
  light_set x.aENCB
  light_set 0
  -- while β < nB: one row
  refine Ends.whileConst (fun β => Inv μ x β 0) x.nB (x.nB * (tTile x.L x.m x.t + 27) + 16) ?_
    ?_ ?_ (by simp; omega)
  ·
    refine ⟨0, μ, by simp, ?_, ?_, .refl⟩
    · exact C.trie
    tauto
  ·
    rintro β σ hβ hI
    have hrow := row_spec hTile C hβ hd hI
    obtain ⟨void, μ', rfl, -⟩ := hI
    simp_all
  ·
    rintro _ ⟨void, μ', rfl, M⟩
    have hall : triesBefore x x.nB 0 = x.tries := by
      rw [triesBefore, tilesBefore_all, AllTilesArgs.tries]
    exact ⟨by simp, by simp, hall ▸ M.trie, hall ▸ M.roots, M.same⟩
