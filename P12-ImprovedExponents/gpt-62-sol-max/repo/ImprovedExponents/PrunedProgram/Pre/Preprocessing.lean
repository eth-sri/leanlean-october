module

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec4.Theorem30.Program
public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ImprovedExponents.PrunedProgram.Tiles.FillList
public import ImprovedExponents.PrunedProgram.Tiles.Tile
public import ImprovedExponents.PrunedProgram.Tiles.AllTiles

@[expose] public section

/-!
# The preprocessing of Theorem 30 with the pruned shared stage

Upstream's `preCoreBody` runs the shared stage `Sec2.pShared`, notes `t` in the directory,
computes the addresses of the areas of Section 4 (`preCoreAddr`) and builds the tries of all
tiles (`preCoreFinish`).  The new procedure `preCoreP` (`preCorePBody`) is the same statement
with the pruned shared stage `Proc.sharedP` in place of `Sec2.pShared`: it leaves the encodings
right at the leaves with at most `m` symbols `P₀` only (`Sec2.SharedReadyP`), which is all that
`allTiles` on pruned encodings assumes (`AllTilesPreP`), and it establishes `DSReadyP` in the
time `tPreCoreP`.  The proofs are upstream's with `SharedReadyP` in place of `SharedReady`:

* `SharedReadyP.dirCells`: the cells of the directory that the routine reads.
* `preCoreP_spec` verifies all phases under `Sec2.SharedSpecP` and `AllTilesSpecP`.
* `preCoreP_of_base58`: for a program `base58 ++ R` that holds `preCorePBody` at `Proc.preCoreP`
  and meets `Sec2.SharedSpecP`, the specification `PreCoreSpecP` holds; the bodies and the
  specifications of upstream's routines 40 to 48 come from `at_base58` and `specs40`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Directory.lean`, `Areas.lean`,
`Preprocessing.lean`, `Routines.lean` and `Program.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ImprovedExponents

variable {lim : Limits} {P : Program} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The program -/

open PreCore in
/-- preCoreP(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on, with the pruned shared stage: upstream's `preCoreBody` with `Proc.sharedP`
in place of `Sec2.pShared`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (preCoreBody)
def preCorePBody : Stmt :=
  .call Proc.sharedP [v Levels, v Inner, v Size, v Width, v MatX, v MatY, v Base] Void ;;
  .store (v Base +' k Dir.switch) (v Switch) ;;
  preCoreAddr ;;
  preCoreFinish

/-- The block, after the pruned shared stage and with the trie array [0], holds what allTiles on
pruned encodings assumes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (allArgs_pre)
theorem allArgsP_pre (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ)
    (hTM : TrieMem μ (aTR p b0) (trieCap p t) (aFP p b0) [0]) :
    AllTilesPreP lim μ (allArgs p t hmL b0 X Y) := by
  -- a negative bound U is possible only if there are no entries; then 0 is a bound as well
  obtain ⟨U', hU0, hX', hY', hvalue⟩ : ∃ U' : ℤ, 0 ≤ U' ∧ (∀ i j, |X i j| ≤ U') ∧
      (∀ i j, |Y i j| ≤ U') ∧ 10 ^ p.m * ((7 ^ p.L * U') * (7 ^ p.L * U')) ≤ lim.word := by
    rcases le_or_gt 0 U with h0 | h0
    · exact ⟨U, h0, hX, hY, h.value⟩
    · have hword : (0 : ℤ) ≤ lim.word := le_trans (by norm_num) h.std.const_le
      exact ⟨0, le_rfl, fun i j => absurd ((abs_nonneg _).trans (hX i j)) (not_le.mpr h0),
        fun i j => absurd ((abs_nonneg _).trans (hY i j)) (not_le.mpr h0), by assumption⟩
  have hsp := h.space
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  exact
    { std := h.std
      t_le := ht
      m_le := hmL
      value_le := ⟨7 ^ p.L * U', 7 ^ p.L * U',
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).1 τ,
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).2 τ, hvalue⟩
      pow_le := h.pow_le
      cap_ge := le_rfl
      order := by simp only [allArgs]; grind
      segA := fun β hβ => hSR.encA β hβ
      segB := fun β hβ => hSR.encB β hβ
      trie := hTM }

/-! ## The routine -/

/-- **preCoreP** meets its specification: the pruned shared stage, then upstream's own parts. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (preCore_spec)
theorem preCoreP_spec {c : ℕ} (hP : P[Proc.preCoreP]? = some preCorePBody)
    (hShared : Sec2.SharedSpecP lim P c) (hAll : AllTilesSpecP lim P) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hX hY hMX hMY haX haY
  refine fun d hd => ⟨preCorePBody, hP, ?_⟩
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCoreP
  -- the pruned shared stage
  light_call (hShared p hmL aX aY b0 μ X Y U
    { space := by omega, matX := hMX, matY := hMY, belowX := haX, belowY := haY, absX := hX
      absY := hY, seven := hlim.enc, ten := hlim.pow }) with r μ₁ ⟨hSR₁, same₁⟩
  -- dir[31] := t
  light_step
  have hSR₂ : Sec2.SharedReadyP p hmL aX aY b0 X Y (Function.update μ₁ (b0 + 31) t) :=
    hSR₁.of_agree fun b _ hb => Function.update_of_ne hb ..
  have dir := hSR₂.dirCells
  unfold preCoreAddr preCoreFinish
  have hsq : (p.nB : ℤ) * p.nB ≤ lim.space := by exact_mod_cast (show p.nB * p.nB ≤ lim.space by omega)
  have hsq₀ : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  light_set (p.nB : ℕ) using dir.bands
  light_set (aCUR p b0 : ℕ)
  light_set (aBOX p b0 : ℕ)
  light_set (aFP p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  light_set (p.m - t : ℕ)
  light_set (aTR p b0 : ℕ)
  light_steps
  let μ₂ := Function.update μ₁ (b0 + 31) (t : ℤ)
  let μ₃ := Function.update (Function.update μ₂ (aTR p b0) 0) (aFP p b0) 1
  have same : SameOutside μ₂ μ₃ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    (SameOutside.refl.update (by omega) 0).update (by omega) 1
  have hSR₃ := hSR₂.of_agree (μ' := μ₃) fun b hb _ => same b (Or.inl (by omega))
  have hDir := hSR₃.dirCells
  change Ends _ _ _ _ ⟨frame (preLocals p t aX aY b0 r), μ₃⟩ _ _
  unfold preLocals preShared
  light_call (hAll _ μ₃ (allArgsP_pre hlim ht hX hY hSR₃ (trieMem_start p t b0 μ₂)))
    using allArgs, hDir.encA, hDir.encB, hDir.leaves, Sec2.Par.T with - μ₄ ⟨hTM, hroots, same₄⟩
  have keep : SameOutside μ₂ μ₄ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    same.then same₄ fun b hb => ⟨hb, by change b < aCUR p b0 ∨ aTR p b0 + trieCap p t ≤ b; omega⟩
  refine ⟨⟨hSR₂.of_agree fun b hb _ => keep b (.inl (by omega)),
    (keep _ (.inl (by omega))).trans (Function.update_self ..), hroots, hTM.seg⟩,
    fun b hb => ?_⟩
  change μ₄ b = μ b
  rw [keep b (by omega)]
  exact (Function.update_of_ne (by omega) ..).trans (same₁ b (by omega))

/-! ## In a program that begins with `base58` -/

/-- **The preprocessing with the pruned shared stage**, in every program that begins with
upstream's `base58`, holds `preCorePBody` at `Proc.preCoreP` and meets the specification of the
pruned shared stage.  The routines 40 to 48 are upstream's (`specs40`), and so are the bodies of
`fillList`, `tile` and `allTiles`, which are re-verified on pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (preCoreSpec_of,
-- preCoreSpec_all) and Program.lean (preCore_base58)
theorem preCoreP_of_base58 {P R : Program} {c : ℕ} (hP : P = base58 ++ R)
    (hpre : P[Proc.preCoreP]? = some preCorePBody) (hsh : Sec2.SharedSpecP lim P c) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim
  have h40 : Has40 P := hP ▸ has40_base58 R
  have S := specs40 h40 hlim.std
  have hFill : FillListSpecP lim P :=
    fillListP_meets (h40 9 (by omega)) S.nineFirst S.nineNext S.starFirst S.horner S.insert
      S.sumTen
  have hTile : TileSpecP lim P := tileP_spec (h40 10 (by omega)) S.newRoot hFill
  have hAll : AllTilesSpecP lim P := allTilesP_spec (h40 11 (by omega)) hTile
  exact preCoreP_spec hpre hsh hAll p t hmL aX aY b0 X Y U μ ht hlim

end Light.Sec4
