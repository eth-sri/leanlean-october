
import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
import ImprovedExponents.PrunedProgram.Encode.AllBands
import ImprovedExponents.PrunedProgram.Shared.Contracts


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

/-- The third part of the pruned shared stage: the number of bands, the last addresses, the
encodings of all bands with the pruned encoder, and the directory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedC)
def sharedCP : Stmt :=
  sharedBands ;;
  .set AdrEncB (v AdrEncA +' v Bands *' v Leaves) ;;
  .set AdrArr (v AdrEncB +' v Bands *' v Leaves) ;;
  .set AdrZs (v AdrArr +' v Strings) ;;
  .set AdrEnd (v AdrZs +' v Strings) ;;
  .call Proc.encodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings,
    v Leaves, v Bands, k 0, v AdrX, v Cols, k 1, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs,
    v AdrPhi, v AdrP7, v AdrP10, v AdrEncA] Void ;;
  .call Proc.encodeBandsP [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings,
    v Leaves, v Bands, k 1, v AdrY, k 1, v Rows, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs,
    v AdrPsi, v AdrP7, v AdrP10, v AdrEncB] Void ;;
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

/-- The entries of the routines that the pruned shared stage calls, with their constants: those of
upstream's stage, and the two entries of `encodeBandsP`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (SharedCallees)
structure SharedCalleesP (lim : Limits) (P : Program) (c : ℕ) : Prop
    extends SharedCallees lim P c where
  bandsLP : EncodeBandsLSpecP lim P c
  bandsRP : EncodeBandsRSpecP lim P c

variable {p : Par} {b0 aX aY : ℕ} {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ} {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ}

/-! ## The third part -/

/-- What the two calls of encodeBandsP and the stores of the directory leave in the memory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean
-- (SharedReady.of_calls)
theorem SharedReadyP.of_calls (hmL : p.m ≤ p.L)
   
    {μ μEncA μEncB μDir : ℕ → ℤ}
    (tb : SharedTables p b0 μ)
    (sA : ∀ β < p.nB, SegOn p.m μEncA (p.aENCA b0 + β * p.T)
      (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))
    (fEncA : SameOutside μ μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0))
    (sB : ∀ β < p.nB, SegOn p.m μEncB (p.aENCB b0 + β * p.T)
      (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))
    (fEncB : SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0))
    (sdir : SegN μDir b0 (dirList p aX aY b0)) (fDir : SameOutside μEncB μDir b0 31) :
    SharedReadyP p hmL aX aY b0 X Y μDir ∧ SameOutside μ μDir b0 (p.sharedEnd b0 - b0) := by
  have hplaces := p.places b0
  have above : ∀ x, p.aP3 b0 ≤ x → μDir x = μEncB x := fun x hx => fDir x (by omega)
  have tbDir : SharedTables p b0 μDir := tb.congr fun x h1 h2 => by
    rw [above x h1, fEncB x (by omega), fEncA x (Or.inl h2)]
  refine ⟨{ tbDir with
    dir := sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => ?_
    encB := fun β hβ => (sB β hβ).congr fun i hi => by grind }, fun x hx => ?_⟩
  · have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
    rw [above _ (by omega), fEncB _ (by omega)]
  · rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega)]

variable {c : ℕ}

/-- **The third part of sharedP.** -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedC_spec)
theorem sharedCP_spec (std : Std lim) (C : SharedCalleesP lim P c) {d : ℕ}
    (hmL : p.m ≤ p.L) (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space)
    (μ : ℕ → ℤ) (r0 : ℤ)
    {V : ℤ} (hX : MatAt μ aX X)
    (hY : MatAt μ aY Y) (hXle : aX + p.N * p.D ≤ b0) (hYle : aY + p.D * p.N ≤ b0) (hV0 : 0 ≤ V)
    (hVX : ∀ i j, |X i j| ≤ V) (hVY : ∀ i j, |Y i j| ≤ V) (hVB : 7 ^ (p.L + 1) * V ≤ lim.word)
    (tb : SharedTables p b0 μ) :
    Ends lim P d sharedCP ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ (sharedTimeCP c p) fun σ' =>
      SharedReadyP p hmL aX aY b0 X Y σ'.mem ∧ SameOutside μ σ'.mem b0 (p.sharedEnd b0 - b0) := by
  have hplaces := p.places b0
  unfold sharedCP sharedTimeCP
  -- the number of bands
  refine Ends.next 13 ((sharedBands_spec std hmL hsp μ r0 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  -- the last four addresses
  light_set (p.aENCB b0)
  light_set (p.aARR b0)
  light_set (p.aZS b0)
  light_set (p.sharedEnd b0)
  -- the encodings of the row bands of X
  light_call (C.bandsLP p hmL _ aX μ X V (tb.bandsPre hsp hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)) hX
    (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX) with rEncA μEncA ⟨sA, fEncA⟩
  -- the encodings of the column bands of Y
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μ x := by tauto
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => by simp_all
  have hYle' : aY + ThreeSumApsp.D p.m * p.N ≤ p.aENCA b0 := le_trans hYle (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V :=
    tbEncA.bandsPre hsp hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
  light_call (C.bandsRP p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
    (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY) with rEncB μEncB ⟨sB, fEncB⟩
  -- the directory
  apply (storeLocals_spec std.space_le (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega)
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  exact SharedReadyP.of_calls hmL tb sA fEncA sB fEncB (by assumption)
    (by assumption)

/-! ## The whole stage -/

/-- The time of the pruned shared stage has the shape of its entry. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (sharedTime_le)
theorem sharedTimeP_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeCP c p) ≤ (12 * c + 600) * sharedShapeP p := by
  unfold sharedTimeA sharedTimeB sharedTimeCP sharedShapeP
  -- The terms that are not in the shape: L + 1 ≤ (L + 1)², N + 1 ≤ (N + 1) (L - m + 1), 1 ≤ (L +
  -- 1)².
  grind

variable {c' : ℕ}

/-- **sharedP** meets its entry, for callees described by their entries: if every callee meets its
entry with the constant c, then sharedP does with the constant 12 c + 600. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (shared_entry)
theorem sharedP_entry_of_callees (std : Std lim) (hP : P[Proc.sharedP]? = some sharedPBody)
    (C : SharedCalleesP lim P c) (hc : 12 * c + 600 ≤ c') :
    SharedSpecP lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTimeP_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros _ 26]
  light_piece (sharedA_spec std C.toSharedCallees hmL hd pre.space pre.ten μ)
    with ⟨locA, μA⟩ ⟨⟨rA, hlocA⟩, hA⟩
  obtain rfl := hlocA
  dsimp at hA
  -- the second part
  light_piece (sharedB_spec std C.toSharedCallees hmL hd pre.space pre.ten μA rA)
    with ⟨locB, μB⟩ ⟨⟨rB, hlocB⟩, hB⟩
  obtain rfl := hlocB
  dsimp at hB
  -- the third part; the matrices lie below the block, and max V 0 bounds their entries as well
  have low : ∀ x < b0, μB x = μ x := fun x hx => by
    rw [hB.same x (by omega), hA.same x (by omega)]
  have hVB' : 7 ^ (p.L + 1) * max V 0 ≤ lim.word := by
    rcases le_total V 0 with h | h
    · rw [max_eq_right h]
      exact le_trans (by norm_num) std.const_le
    · rw [max_eq_left h]
      exact pre.seven
  apply (sharedCP_spec std C hmL hd pre.space μB rB (pre.matX.congr_below low pre.belowX)
    (pre.matY.congr_below low pre.belowY) pre.belowX pre.belowY (by omega)
    (fun i j => (pre.absX i j).trans (by omega))
    (fun i j => (pre.absY i j).trans (by omega)) hVB' (.of_parts hA hB)).mono (by omega)
  rintro σ' ⟨hR, hf⟩
  exact ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩

/-- **sharedP** meets its entry of the map: if every callee of upstream's shared stage meets its
entry with the constant c, and encodeBandsP, encodeP, encStep and bandArray are in the program at
their numbers with `cBandArray + cEncP + 51 ≤ c`, then sharedP meets `SharedSpecP` with the
constant 12 c + 600 (upstream's `cShared5 = 2000` is enough: `120 + 778 + 51 ≤ 2000`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean (shared_entry)
theorem sharedP_entry (std : Std lim) (hP : P[Proc.sharedP]? = some sharedPBody)
    (hPB : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hBA : P[pBandArray]? = some bandArrayBody) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    (C : SharedCallees lim P c) (hcb : cBandArray + cEncP + 51 ≤ c)
    (hc : 12 * c + 600 ≤ c') : SharedSpecP lim P c' :=
  sharedP_entry_of_callees std hP
    { C with
      bandsLP := encodeBandsPL_entry std hPB hS hE (bandArrayL_entry std hBA) hcb
      bandsRP := encodeBandsPR_entry std hPB hS hE (bandArrayR_entry std hBA) hcb }
    hc
