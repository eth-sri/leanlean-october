module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.AllBands
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning
public import ImprovedExponents.PrunedProgram.Encode.Recursion
public import ImprovedExponents.PrunedProgram.Procs
import all ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
import all ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning

@[expose] public section

/-!
# The encodings of all bands of one matrix with the pruned encoder

As in upstream's `encodeBands`, each round builds one band of a matrix in the scratch array.
It then calls `encodeP` with budget `m`, proving the encoding at leaves with at most `m` copies
of `P₀` without requiring the other leaves to be written.

Adapted from upstream `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean` and
`Encode/Contract.lean` (Apache-2.0).
-/

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

variable {lim : Limits} {P : Program}

open private scrSize_le pow_of_seg from ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract

open private encIdx_eq_computeEncoding EncodePre.of_seg
  from ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning

open Bands in
/-- encodeBandsP(L, m, N, D, K0, N0, S7, T, nB, side, aA, sI, sK, mask, dig3, dig4, arr, zs, tab,
p7, p10, enc): for each band, the input array is formed at arr and encoded with the budget m into
the T cells from enc + β T. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBandsBody)
def encodeBandsPBody : Stmt :=
  .for BandNo (v NumBands) (
    .call pBandArray [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo,
      v Side, v Source, v StepRow, v StepCol, v MaskTable, v Digits3, v Digits4, v Arr] Res ;;
    .call Proc.encodeP [v Levels, v Size, v Arr, v Enc +' v BandNo *' v Leaves, v Scratch, v Table,
      v Pow7, v Pow10] Res)

/-- The time of the loop is at most the constant cB + cE + 51 times the shape of the entries. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean (encodeBands_time)
theorem encodeBandsP_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * encWorkP p.L p.m + 51) + 6
      ≤ (cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1) := by
  have hW : 1 ≤ encWorkP p.L p.m :=
    (Nat.one_le_pow _ _ (by norm_num)).trans (pow_seven_le_encWorkP p.L p.m)
  have hfifty : p.nB * 51 ≤ p.nB * (51 * encWorkP p.L p.m) := Nat.mul_le_mul_left _ (by omega)
  lia

namespace BandSide

def flat : BandSide → List ℤ | .left => phiFlat | .right => psiFlat

def coeff : (s : BandSide) → Term → s.Symbol → ℤ | .left => phi | .right => psi

noncomputable abbrev encoding {p : Par} (s : BandSide) (hmL : p.m ≤ p.L) (X : s.Mat p) (β : ℕ) :
    Leaf p.L → ℤ :=
  fun τ => encodeWith s.coeff τ (s.array hmL X β)

private theorem flat_length (s : BandSide) : s.flat.length = 70 := by cases s <;> rfl

private theorem flat_range (s : BandSide) : ∀ x ∈ s.flat, -1 ≤ x ∧ x ≤ 1 := by
  cases s <;> decide

private theorem flat_spec (s : BandSide) (lam : Term) (a : s.Symbol) :
    s.flat.getD (7 * (termIdx lam : ℕ) + (s.alphabet a : ℕ)) 0 = s.coeff lam a := by
  cases s
  · exact phiFlat_spec lam a
  · exact psiFlat_spec lam a

private theorem array_bound {p : Par} (s : BandSide) (hmL : p.m ≤ p.L) {X : s.Mat p} {V : ℤ}
    (hV0 : 0 ≤ V) (hV : ∀ i j, |X i j| ≤ V) (β : ℕ) : ∀ u, |s.array hmL X β u| ≤ V := by
  cases s
  · exact abs_bandArrayL_le (stdLayout hmL) hV0 hV β
  · exact abs_bandArrayR_le (stdLayout hmL) hV0 hV β

end BandSide

/-- Encode every band, retaining the leaves with at most m occurrences of P₀. -/
def EncodeBandsSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (s : BandSide) (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aA : ℕ) (μ : ℕ → ℤ)
    (X : s.Mat p) (V : ℤ), BandsPre lim p μ x s.flat V → MatAt μ aA X →
    aA + s.rows p * s.cols p ≤ x.enc → (∀ i j, |X i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth →
    Meets lim P Proc.encodeBandsP d (x.vals p s.tag aA (s.strideI p) (s.strideK p)) μ
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
      (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T) (s.encoding hmL X β)) ∧
        SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- Both orientations use the same band and pruned encoding loops. -/
theorem encodeBandsP_entry (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {cB c : ℕ} (hB : BandArraySpec lim P cB) (hc : cB + cEncP + 51 ≤ c) :
    EncodeBandsSpecP lim P c := by
  intro s p hmL x aA μ X V pre hM hMle hV d hd
  refine .mono_const (.of_body hP (Ends.mono (T := p.nB *
    (cB * bandArrayShape p + cEncP * encWorkP p.L p.m + 51) + 6) ?_
    (encodeBandsP_time p cB cEncP) fun _ h => h)) hc
  light_facts pre std
  have hT : p.T = 10 ^ p.L := rfl
  have hS7 : p.S7 = 7 ^ p.L := rfl
  have hnB : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  have hmword : (p.m : ℤ) ≤ lim.word := by omega
  -- The encodings of the bands below β are in place.
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, s.tag, aA, s.strideI p, s.strideK p,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β _ μ' => (∀ β' < β, SegOn p.m μ' (x.enc + β' * p.T) (s.encoding hmL X β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cEncP * encWorkP p.L p.m + 43) 0
    ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  -- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr)
  have low : Kept μ μ' x.enc := by light_keep
  light_call (hB s p hmL β aA x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
    (hM.congr_below low hMle) (by omega) ((pre.tables.congr_below low).mono (by omega))
    hβ _ (by omega)) with r₁ μ₁ ⟨hA, same₁⟩
  -- encodeP(L, m, arr, enc + β T, zs, tab, p7, p10)
  have low₁ : Kept μ μ₁ x.enc := by light_keep
  let e := s.alphabet
  let A := s.array hmL X β
  have hpl := pre.encodePlaces hβ low₁
  have hVB : ((7 ^ p.L : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ pre.word
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)) pre.V_nonneg
  have hA' : ∀ u, |A u| ≤ V := s.array_bound hmL pre.V_nonneg hV β
  have hbdd : ∀ z ∈ arrStr e A, -V ≤ z ∧ z ≤ V := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact abs_le.1 (hA' _)
  have hflat := s.flat_length
  have encPre := EncodePre.of_seg (hpl.layout std) (length_arrStr e A) hA hbdd hflat
    (pre.coef.congr fun i hi => low₁ _ (by omega)) s.flat_range
    (pow_of_seg hpl.hp7 hpl.n_le) (pow_of_seg hpl.hp10 hpl.n_le) hVB
  have ht := tEncP_le p.L p.m
  light_call (encodeP_meets hS hE (d := d + 1) (by omega) p.m μ₁ x.arr
    (x.enc + β * p.T) x.zs V _ hmword encPre) with r₂ μ₂ ⟨hraw, same₂⟩
  have hEβ : SegOn p.m μ₂ (x.enc + β * p.T) (s.encoding hmL X β) := by
    intro τ hτ
    rw [hraw τ hτ, encIdx_eq_computeEncoding e s.coeff s.flat_spec p.L A
      (fun i hi => getD_arrStr_of_lt e A hi) (codeT_lt τ), show decodeT p.L (codeT τ) = τ from decodeStr_codeStr termEquiv τ]
    exact computeEncoding_eq_encodeWith s.coeff _ _
  have hscr : scrSize p.L ≤ p.S7 := Nat.le_of_succ_le (scrSize_le p.L)
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by light_keep⟩
  rcases Nat.lt_or_ge β' β with h | h
  · -- The encodings of the earlier bands lie below enc + β T and have not been touched.
    have hβ'T : β' * p.T + p.T ≤ β * p.T := Nat.mul_add_le_mul h le_rfl
    exact (hdone β' h).keep
  grind

end Light.Sec2
