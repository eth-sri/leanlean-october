module

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ImprovedExponents.PrunedProgram.Encode.AllBands
public import ImprovedExponents.PrunedProgram.Shared.Contracts

@[expose] public section

/-!
# The shared stage with the pruned encoder

Upstream's shared stage (`ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean`) is a straight
line in three parts: `sharedA` (the tables of powers), `sharedB` (the other tables) and `sharedC`
(the number of bands, the last addresses, the two calls of `encodeBands`, and the directory).  The
pruned shared stage `sharedPBody = sharedA ;; sharedB ;; sharedCP` keeps the first two parts and
exchanges, in the third, the two calls of `encodeBands` for calls of `encodeBandsP`, which
encodes every band with the pruned encoder.  What it leaves behind is `SharedReadyP` (the
encodings right at the leaves with at most `m` symbols `P₀`), and its time has the shape
`sharedShapeP` (`sharedTimeP_le`).  `sharedP_entry` puts the parts together: if every callee of
upstream's stage meets its entry with the constant `c`, and `encodeBandsP`, `encodeP`, `encStep`
and `bandArray` are in the program at their numbers with `cBandArray + cEncP + 51 ≤ c`, then
`sharedP` meets `SharedSpecP` with the constant `12 c + 600`, as upstream.

Adapted from upstream `ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean` (Apache-2.0).
-/

namespace Light.Sec2

open ThreeSumApsp ImprovedExponents

variable {lim : Limits} {P : Program}

open Shared

/-! ## The text -/

def sharedEncode (left : Bool) : Stmt :=
  .call Proc.encodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings,
    v Leaves, v Bands, k (if left then 0 else 1), v (if left then AdrX else AdrY),
    if left then v Cols else k 1, if left then k 1 else v Rows,
    v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v (if left then AdrPhi else AdrPsi),
    v AdrP7, v AdrP10, v (if left then AdrEncA else AdrEncB)] Void

/-- The third part of the pruned shared stage: the number of bands, the last addresses, the
encodings of all bands with the pruned encoder, and the directory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedC)
def sharedCP : Stmt :=
  sharedBands ;;
  .set AdrEncB (v AdrEncA +' v Bands *' v Leaves) ;;
  .set AdrArr (v AdrEncB +' v Bands *' v Leaves) ;;
  .set AdrZs (v AdrArr +' v Strings) ;;
  .set AdrEnd (v AdrZs +' v Strings) ;;
  sharedEncode true ;; sharedEncode false ;;
  storeLocals 0 [Levels, Inner, Rows, Cols, Outer, BlockRows, Subsets, Root, Table, Bands, Leaves,
    Strings, AdrX, AdrY, AdrP3, AdrP4, AdrP7, AdrP10, AdrPas, AdrPhi, AdrPsi, AdrMask, AdrBand,
    AdrBlock, AdrDig3, AdrDig4, AdrEncA, AdrEncB, AdrArr, AdrZs, AdrEnd]

/-- sharedP(L, m, N, D, aX, aY, b0): upstream's shared stage with the pruned encoder. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedBody)
def sharedPBody : Stmt := sharedA ;; sharedB ;; sharedCP

/-- The time of the third part, if every callee meets its entry with the constant c. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedTimeC)
def sharedTimeCP (c : ℕ) (p : Par) : ℕ :=
  2 * (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) + 236

/-- The time of the pruned shared stage has the shape of its entry. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedTime_le)
theorem sharedTimeP_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeCP c p) ≤ (12 * c + 600) * sharedShapeP p := by
  unfold sharedTimeA sharedTimeB sharedTimeCP sharedShapeP
  -- The terms that are not in the shape: L + 1 ≤ (L + 1)², N + 1 ≤ (N + 1) (L - m + 1), 1 ≤ (L +
  -- 1)².
  lia

set_option maxHeartbeats 1000000 in
/-- **sharedP** meets its entry of the map: if every callee of upstream's shared stage meets its
entry with the constant c, and encodeBandsP, encodeP, encStep and bandArray are in the program at
their numbers with `cBandArray + cEncP + 51 ≤ c`, then sharedP meets `SharedSpecP` with the
constant 12 c + 600 (upstream's `cShared5 = 2000` is enough: `120 + 778 + 51 ≤ 2000`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (shared_entry)
theorem sharedP_entry (std : Std lim) (hP : P[Proc.sharedP]? = some sharedPBody)
    (hPB : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hBA : P[pBandArray]? = some bandArrayBody) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {c : ℕ} (C : SharedCallees lim P c) (hcb : cBandArray + cEncP + 51 ≤ c)
    {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpecP lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTimeP_le c p) fun _ h => h)) hc
  light_facts std
  have hsp := pre.space
  have h10 := pre.ten
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  have eKK : p.KK = p.K0 * p.K0 := rfl
  unfold sharedPBody
  refine Ends.next (sharedTimeA c p) ?_ (Nat.le_add_right ..)
  unfold sharedA sharedTimeA
  -- the addresses of the first eight areas
  light_set (p.aP3 b0 : ℕ)
  light_set (p.aP4 b0 : ℕ)
  light_set (p.aP7 b0 : ℕ)
  light_set (p.aP10 b0 : ℕ)
  light_set (p.aPAS b0 : ℕ)
  light_set (p.aPHI b0 : ℕ)
  light_set (p.aPSI b0 : ℕ)
  light_set (p.aMASK b0 : ℕ)
  -- the powers of 3, 4, 7 and 10
  light_call (C.powTable h10 3 (p.aP3 b0) μ) with rP3 μP3 ⟨sP3, fP3⟩
  light_call (C.powTable h10 4 (p.aP4 b0) μP3) with rP4 μP4 ⟨sP4, fP4⟩
  light_call (C.powTable h10 7 (p.aP7 b0) μP4) with rP7 μP7 ⟨sP7, fP7⟩
  light_call (C.powTable h10 10 (p.aP10 b0) μP7) with rP10 μP10 ⟨sP10, fP10⟩
  have lp (b : ℕ) := length_powList b (p.L + 1)
  have powTables : PowTables p b0 μP10 :=
    ⟨sP3.keep (by light_keep [lp]), sP4.keep (by light_keep [lp]), sP7.keep (by light_keep [lp]), sP10⟩
  have sameA : SameOutside μ μP10 (p.aP3 b0) (p.aPAS b0 - p.aP3 b0) := by light_keep
  -- L - m, and then N₀ = 3^{L-m}, 10^L and 7^L from the tables
  have read : ∀ {b a i : ℕ}, Seg μP10 a (powList b (p.L + 1)) → i ≤ p.L →
      μP10 (a + i) = (b ^ i : ℕ) :=
    fun h hi => by rw [h.get (by rw [length_powList]; omega), getElem_powList]
  have hN0 : μP10 (p.aP3 b0 + p.Lo) = (p.N0 : ℕ) := read powTables.p3 (by omega)
  have hT : μP10 (p.aP10 b0 + p.L) = (p.T : ℕ) := read powTables.p10 le_rfl
  have hS7 : μP10 (p.aP7 b0 + p.L) = (p.S7 : ℕ) := read powTables.p7 le_rfl
  light_set (p.Lo : ℕ)
  light_set (p.N0 : ℕ) using hN0
  light_set (p.T : ℕ) using hT
  light_set (p.S7 : ℕ) using hS7
  rw [Nat.add_sub_cancel_left]
  refine Ends.next (sharedTimeB c p) ?_ (Nat.le_add_right ..)
  unfold sharedB sharedTimeB
  -- K := binom(L, m)
  light_call (C.binom p.L p.m (p.aPAS b0) μP10 (by omega) hmL
    (le_trans (by exact_mod_cast p.two_pow_le_T) (by omega : (p.T : ℤ) ≤ lim.word)))
    with r μPas ⟨hr, fPas⟩
  obtain rfl : r = (p.K : ℕ) := hr
  -- K₀ := ⌊√K⌋ and K₀²
  light_call (C.sqrt p.K μPas (by push_cast; omega)) with r μPas' ⟨hr, hμ⟩
  obtain rfl : r = (p.K0 : ℕ) := hr
  obtain rfl : μPas = μPas' := hμ.symm
  light_set (p.KK : ℕ)
  -- the coefficients and the table of subsets
  light_call (C.coef (p.aPHI b0) μPas (by omega)) with rPhi μPhi ⟨sphi, spsi, fPhi⟩
  light_call (C.subsets p.L p.m p.KK (p.aMASK b0) μPhi (by omega) hmL p.KK_le_K
    (by push_cast; omega)) with rMask μMask ⟨smask, fMask⟩
  -- band and block of every row
  iterate 3 light_step
  light_call (C.counters p.N p.K0 p.N0 (p.aBAND b0) μMask (by omega) (by omega)
    (by omega) (by push_cast; omega)) with rBand μBand ⟨sband, fBand⟩
  -- the digits of every row and of every column
  light_call (C.digits p.N 3 p.Lo (p.aDIG3 b0) μBand (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig3 μDig3 ⟨sdig3, fDig3⟩
  light_set (p.aDIG4 b0 : ℕ)
  light_call (C.digits p.D 4 p.m (p.aDIG4 b0) μDig3 (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig4 μB ⟨sdig4, fDig4⟩
  light_set (p.aENCA b0 : ℕ)
  have hb : Kept μBand μB (p.aDIG3 b0) := by light_keep
  have rows : RowTables p b0 μB := by
    refine {
      phi := sphi.keep (by light_keep [Spec.length_phiFlat])
      psi := spsi.keep (by light_keep [Spec.length_psiFlat])
      band := fun i hi => (hb _ (by omega)).trans (sband i hi).1
      block := fun i hi => (hb _ (by omega)).trans (sband i hi).2
      mask := fun i hi => (smask i hi).keep ?_
      dig3 := fun i hi => (sdig3 i hi).keep ?_
      dig4 := fun i hi => by simpa only [Nat.mod_eq_of_lt (show i < 4 ^ p.m from hi)] using sdig4 i hi }
    · have := Nat.mul_add_le_mul hi (le_refl p.L)
      light_keep [Spec.length_unrank]
    · have := Nat.mul_add_le_mul hi (le_refl p.Lo)
      light_keep [ThreeSumApsp.digitList]
  have sameB : SameOutside μP10 μB (p.aPAS b0) (p.aENCA b0 - p.aPAS b0) := by light_keep
  have sameAB : SameOutside μ μB (p.aP3 b0) (p.aENCA b0 - p.aP3 b0) := by light_keep
  have tb : SharedTables p b0 μB :=
    { rows with
      p3 := powTables.p3.keep (by light_keep [lp])
      p4 := powTables.p4.keep (by light_keep [lp])
      p7 := powTables.p7.keep (by light_keep [lp])
      p10 := powTables.p10.keep (by light_keep [lp]) }
  rw [Nat.add_sub_cancel_left]
  -- the third part; the matrices lie below the block, and max V 0 bounds their entries as well
  have low : Kept μ μB b0 := by light_keep
  let V' := max V 0
  have hVB : 7 ^ (p.L + 1) * V' ≤ lim.word := by
    rcases max_cases V 0 with ⟨he, -⟩ | ⟨he, -⟩
    · simpa [V', he] using pre.seven
    · simpa [V', he] using (show (0 : ℤ) ≤ lim.word by have := std.const_le; omega)
  have hX := pre.matX.congr_below low pre.belowX
  have hY := pre.matY.congr_below low pre.belowY
  have hV0 : 0 ≤ V' := le_max_right V 0
  have hVX i j := (pre.absX i j).trans (le_max_left V 0)
  have hVY i j := (pre.absY i j).trans (le_max_left V 0)
  have encode := encodeBandsP_entry std hPB hS hE (bandArray_entry std hBA) hcb
  unfold sharedCP sharedTimeCP
  -- the number of bands
  refine Ends.next 13 ((sharedBands_spec std hmL pre.space μB rDig4 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  -- the last four addresses
  light_steps
  -- the encodings of the row bands of X
  have preA : BandsPre lim p μB (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat V' :=
    tb.bandsPre pre.space hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)
  light_call (encode .left p hmL _ aX μB X V' preA hX
    (pre.belowX.trans (show b0 ≤ p.aENCA b0 by omega)) hVX) using sharedEncode with rEncA μEncA ⟨sA, fEncA⟩
  -- the encodings of the column bands of Y
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μB x := fun x hx => fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have hYle' : aY + ThreeSumApsp.D p.m * p.N ≤ p.aENCA b0 := le_trans pre.belowY (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V' :=
    tbEncA.bandsPre pre.space hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
  light_call (encode .right p hmL _ aY μEncA Y V' preB (hY.congr_below lowEncA hYle')
    (pre.belowY.trans (show b0 ≤ p.aENCB b0 by omega)) hVY) using sharedEncode with rEncB μEncB ⟨sB, fEncB⟩
  -- the directory
  refine (storeLocals_spec std.space_le (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  change SameOutside μEncB μDir b0 31 at fDir
  change SameOutside μB μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0) at fEncA
  change SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0) at fEncB
  have above : ∀ x, p.aP3 b0 ≤ x → μDir x = μEncB x :=
    fun x hx => fDir x (Or.inr (by omega))
  have tbDir : SharedTables p b0 μDir := tb.congr fun a ha hb => by
    rw [above a ha, fEncB a (.inl (by omega)), lowEncA a hb]
  refine ⟨{ tbDir with
    dir := by simpa [Par.aDIR, SegN, dirList, Par.aENCB, Par.aARR, Par.aZS, Par.sharedEnd] using sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => ?_
    encB := fun β hβ => (sB β hβ).congr fun i hi => ?_ }, fun x hx => ?_⟩
  · change μDir (p.aENCA b0 + β * p.T + i) = _
    have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
    rw [above _ (by omega), fEncB _ (.inl (by omega))]
    rfl
  · exact above (p.aENCB b0 + β * p.T + i) (by omega)
  · change μDir x = μ x
    rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega), sameAB x (by omega)]

end Light.Sec2
