module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.SharedStage
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArray
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.AllBands
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning
public import ImprovedExponents.PrunedProgram.Encode.Recursion
import all ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning
import all ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

open private encIdx_eq_computeEncoding EncodePre.of_seg
  from ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning
open private scrSize_le pow_of_seg from ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Contract

section EncodeEntry

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out dst scr tab p7 p10 L n Lmax j : ℕ}
  {V : ℤ}

theorem encodeP_str {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ) {T : List ℤ}
    (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) {pS pE : ℕ}
    (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodePBody pS pE))
    (lay : EncodeLayout lim src out scr tab p7 p10 L) (A : (Fin L → α) → ℤ)
    (hsrc : Seg μ src (arrStr e A)) (hV : ∀ u, |A u| ≤ V) (htab : Seg μ tab T)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) (hd : d + L ≤ lim.depth) (hj : (j : ℤ) ≤ lim.word) :
    Ends lim P d (encodePBody pS pE) ⟨frame [L, j, src, out, scr, tab, p7, p10], μ⟩
      (cEncP * encWorkP L j) fun σ' => SegOn j σ'.mem out (computeEncoding coef L A) ∧
        SameOutside2 μ σ'.mem out (10 ^ L) scr (scrSize L) := by
  have hbound : ∀ x ∈ arrStr e A, -V ≤ x ∧ x ≤ V := fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx; exact abs_le.1 (hV _)
  have pre := EncodePre.of_seg lay (length_arrStr e A) hsrc hbound hT htab hc h7 h10 hVB
  refine (encodeP_spec hS hE hd hj pre).mono (tEncP_le L j) fun σ' h => ⟨fun τ hτ => ?_, h.2⟩
  rw [h.1 τ hτ,
    encIdx_eq_computeEncoding e coef hcoef L A (fun i hi => getD_arrStr_of_lt e A hi) (codeT_lt τ)]
  exact congrArg (computeEncoding coef L A) (decodeStr_codeStr termEquiv τ)

theorem encodeP_entry {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)
    {T : List ℤ} (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) (std : Std lim)
    (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {d : ℕ} (hd : d + (n + 1) ≤ lim.depth) (hpl : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ)
    (htab : Seg μ tab T) (A : (Fin n → α) → ℤ) (hsrc : Seg μ src (arrStr e A)) {V : ℤ}
    (hV : ∀ u, |A u| ≤ V) (hVB : 7 ^ (n + 1) * V ≤ lim.word) (hj : (j : ℤ) ≤ lim.word) :
    Meets lim P Proc.encodeP d [n, j, src, dst, scr, tab, p7, p10] μ (cEncP * encWorkP n j)
      fun _ μ' => SegOn j μ' dst (computeEncoding coef n A) ∧
        SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n) := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV fun _ => e.symm 0)
  have hVB' : ((7 ^ n : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ hVB
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hV0
  have := scrSize_le n
  exact .of_body hE ((encodeP_str e coef hT hc hcoef hS hE (hpl.layout std) A hsrc hV htab
    (pow_of_seg hpl.hp7 hpl.n_le) (pow_of_seg hpl.hp10 hpl.n_le) hVB' (by omega) hj).mono le_rfl
    fun _ h => ⟨h.1, h.2.mono fun _ _ => by omega⟩)

end EncodeEntry

section BandsAndShared

variable {lim : Limits} {P : Program}

open Bands in
def encodeBandsPBody : Stmt :=
  .for BandNo (v NumBands) (
    .call pBandArray [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo,
      v Side, v Source, v StepRow, v StepCol, v MaskTable, v Digits3, v Digits4, v Arr] Res ;;
    .call Proc.encodeP [v Levels, v Size, v Arr, v Enc +' v BandNo *' v Leaves, v Scratch, v Table,
      v Pow7, v Pow10] Res)

theorem encodeBandsP_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * encWorkP p.L p.m + 51) + 6
      ≤ (cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1) := by
  have hW : 1 ≤ encWorkP p.L p.m :=
    (Nat.one_le_pow _ _ (by norm_num)).trans (pow_seven_le_encWorkP p.L p.m)
  have hfifty : p.nB * 51 ≤ p.nB * (51 * encWorkP p.L p.m) := Nat.mul_le_mul_left _ (by omega)
  generalize encWorkP p.L p.m = W at hW hfifty ⊢
  calc p.nB * (cB * bandArrayShape p + cE * W + 51) + 6
      = p.nB * (cB * bandArrayShape p) + p.nB * (cE * W) + p.nB * 51 + 6 := by ring
    _ ≤ p.nB * (cB * bandArrayShape p) + p.nB * (cE * W) + p.nB * (51 * W) + 6
        + (p.nB * (cB * W) + p.nB * ((cE + 51) * bandArrayShape p) + (cB + cE + 45)) := by omega
    _ = (cB + cE + 51) * (p.nB * (W + bandArrayShape p) + 1) := by ring

theorem encodeBandsP_proc {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ : ℕ → ℤ}
    (std : Std lim) (hP : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    {d side aA sI sK cB cE : ℕ} {A : ℕ → List ℤ} {E : ℕ → Leaf p.L → ℤ}
    (pre : BandsPre lim p μ x coefs V) (hd : d < lim.depth)
    (HB : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc →
      Meets lim P pBandArray (d + 1)
        [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, side, aA, sI, sK, x.mask, x.dig3, x.dig4, x.arr]
        μ' (cB * bandArrayShape p) fun _ μ'' =>
          Seg μ'' x.arr (A β) ∧ SameOutside μ' μ'' x.arr p.S7)
    (HE : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc → Seg μ' x.arr (A β) →
      Meets lim P Proc.encodeP (d + 1)
        [p.L, p.m, x.arr, (x.enc + β * p.T : ℕ), x.zs, x.tab, x.p7, x.p10] μ'
        (cE * encWorkP p.L p.m) fun _ μ'' => SegOn p.m μ'' (x.enc + β * p.T) (E β) ∧
          SameOutside2 μ' μ'' (x.enc + β * p.T) (10 ^ p.L) x.zs (7 ^ p.L)) :
    Meets lim P Proc.encodeBandsP d (x.vals p side aA sI sK) μ
      ((cB + cE + 51) * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (x.enc + β * p.T) (E β)) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc) := by
  refine .of_body hP (Ends.mono ?_ (encodeBandsP_time p cB cE) fun _ h => h)
  light_facts pre std
  have hT : p.T = 10 ^ p.L := rfl; have hS7 : p.S7 = 7 ^ p.L := rfl
  have hnB : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β μ' => (∀ β' < β, SegOn p.m μ' (x.enc + β' * p.T) (E β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cE * encWorkP p.L p.m + 43) 0
    ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  light_call (HB β hβ μ' (by light_keep)) with r₁ μ₁ ⟨hA, same₁⟩
  light_call (HE β hβ μ₁ (by light_keep) hA) with r₂ μ₂ ⟨hEβ, same₂⟩
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by light_keep⟩
  rcases Nat.lt_or_ge β' β with h | h
  · have := Nat.mul_add_le_mul h (le_refl p.T); exact (hdone β' h).keep
  · obtain rfl : β' = β := by omega
    exact hEβ

private theorem BandsPre.m_le_word {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ : ℕ → ℤ}
    (std : Std lim) (pre : BandsPre lim p μ x coefs V) (hmL : p.m ≤ p.L) :
    (p.m : ℤ) ≤ lim.word := by
  light_facts pre; light_side

structure SharedReadyP (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop
  extends SharedTables p b0 μ where
  dir : SegN μ (p.aDIR b0) (dirList p aX aY b0)
  encA : ∀ β < p.nB, SegOn p.m μ (p.aENCA b0 + β * p.T)
    (encodingL (bandArrayL (Spec.stdLayout hmL) X β))
  encB : ∀ β < p.nB, SegOn p.m μ (p.aENCB b0 + β * p.T)
    (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))

theorem SharedReadyP.congr {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
    (h : SharedReadyP p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyP p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc {a β i : ℕ} (ha : p.aENCA b0 ≤ a) (hend : a + p.nB * p.T ≤ p.sharedEnd b0)
      (hβ : β < p.nB) (hi : i < p.T) : μ' (a + β * p.T + i) = μ (a + β * p.T + i) := by
    have := Nat.mul_add_lt_mul hβ hi; exact hag _ (by omega) (by omega) (by omega)
  have hT : p.T = 10 ^ p.L := rfl
  refine { tb with
    dir := h.dir.congr fun i hi => ?_
    encA := fun β hβ => (h.encA β hβ).congr fun i hi => henc le_rfl (by omega) hβ (hT ▸ hi)
    encB := fun β hβ => (h.encB β hβ).congr fun i hi => henc (by omega) (by omega) hβ (hT ▸ hi) }
  simp  [dirList, List.length_map] at hi
  simp only [Par.aDIR]; exact hag _ (by omega) (by omega) (by omega)

theorem SharedReadyP.of_agree {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
    (h : SharedReadyP p hmL aX aY b0 X Y μ)
    (hag : ∀ a, a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReadyP p hmL aX aY b0 X Y μ' :=
  h.congr fun a _ => hag a

def sharedShapeP (p : Par) : ℕ :=
  (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1) + p.nB * (encWorkP p.L p.m + bandArrayShape p)

def SharedSpecP (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    SharedPre lim p aX aY b0 X Y V μ →
    ∀ d, d + (p.L + 3) ≤ lim.depth →
    Meets lim P Proc.sharedP d [p.L, p.m, p.N, p.D, aX, aY, b0] μ (c * sharedShapeP p) fun _ μ' =>
      SharedReadyP p hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (p.sharedEnd b0 - b0)

open Shared

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

def sharedPBody : Stmt := sharedA ;; sharedB ;; sharedCP

def sharedTimeCP (c : ℕ) (p : Par) : ℕ :=
  2 * (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) + 236

theorem SharedReadyP.of_calls {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μEncA μEncB μDir : ℕ → ℤ}
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
  have above (x : ℕ) (hx : p.aP3 b0 ≤ x) : μDir x = μEncB x := fDir x (Or.inr (by omega))
  have tbDir : SharedTables p b0 μDir := tb.congr fun x h1 h2 => by
    rw [above x h1, fEncB x (Or.inl (by omega)), fEncA x (Or.inl h2)]
  refine ⟨{ tbDir with
    dir := sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => ?_
    encB := fun β hβ => (sB β hβ).congr fun i _ => above _ (by omega) }, fun x hx => ?_⟩
  · have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
    rw [above _ (by omega), fEncB _ (Or.inl (by omega))]
  · show μDir x = μ x
    rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega)]

theorem sharedTimeP_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeCP c p) ≤ (12 * c + 600) * sharedShapeP p := by
  unfold sharedTimeA sharedTimeB sharedTimeCP sharedShapeP
  have hL : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN : p.N + 1 ≤ (p.N + 1) * (p.Lo + 1) := Nat.le_mul_of_pos_right _ (by omega)
  generalize (p.L + 1) ^ 2 = s, Nat.sqrt p.K + 1 = q, (p.KK + 1) * (p.L + 1) = u,
    (p.N + 1) * (p.Lo + 1) = w, (p.D + 1) * (p.m + 1) = x,
    p.nB * (encWorkP p.L p.m + bandArrayShape p) = y at hL hN ⊢
  have hcL := Nat.mul_le_mul_left c hL
  have hcN := Nat.mul_le_mul_left c hN
  have hc1 := Nat.mul_le_mul_left c (show 1 ≤ s by omega)
  have hy : c * (y + 1) = c * y + c := Nat.mul_succ c y
  have hright : (12 * c + 600) * (s + q + u + w + x + y) = 12 * (c * s) + 12 * (c * q)
      + 12 * (c * u) + 12 * (c * w) + 12 * (c * x) + 12 * (c * y)
      + 600 * (s + q + u + w + x + y) := by ring
  omega

theorem sharedP_entry (std : Std lim) (hP : P[Proc.sharedP]? = some sharedPBody)
    (hPB : P[Proc.encodeBandsP]? = some encodeBandsPBody)
    (hBA : P[pBandArray]? = some bandArrayBody) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[Proc.encodeP]? = some (encodePBody pEncStep Proc.encodeP))
    {c : ℕ} (C : SharedCallees lim P c) (hcb : cBandArray + cEncP + 51 ≤ c)
    {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpecP lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0; have hw := std.space_le; have h100 := std.const_le
  have hsp := pre.space; have hsizes := p.sizes hmL; have hTw := Par.ten_T_le pre.ten
  have hbX := pre.belowX; have hbY := pre.belowY
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTimeP_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros [(p.L : ℤ), p.m, p.N, p.D, aX, aY, b0] 26]
  unfold sharedPBody
  light_piece (sharedA_spec std C hmL hd pre.space pre.ten μ) with ⟨locA, μA⟩ ⟨⟨rA, rfl⟩, hA⟩
  dsimp only at hA
  light_piece (sharedB_spec std C hmL hd pre.space pre.ten μA rA) with ⟨locB, μB⟩ ⟨⟨rB, rfl⟩, hB⟩
  dsimp only at hB
  have low (x : ℕ) (hx : x < b0) : μB x = μ x :=
    (hB.same x (Or.inl (by omega))).trans (hA.same x (Or.inl (by omega)))
  have hVB' : 7 ^ (p.L + 1) * max V 0 ≤ lim.word := by
    rcases le_total V 0 with h | h
    · rw [max_eq_right h, mul_zero]; exact le_trans (by norm_num) h100
    · rw [max_eq_left h]; exact pre.seven
  have tb : SharedTables p b0 μB := .of_parts hA hB
  have mX := pre.matX.congr_below low pre.belowX
  have mY := pre.matY.congr_below low pre.belowY
  have hVX (i : Fin p.N) (j : Fin (ThreeSumApsp.D p.m)) := (pre.absX i j).trans (le_max_left V 0)
  have hVY (i : Fin (ThreeSumApsp.D p.m)) (j : Fin p.N) := (pre.absY i j).trans (le_max_left V 0)
  refine Ends.mono (T := sharedTimeCP c p)
    (Q := fun σ' => SharedReadyP p hmL aX aY b0 X Y σ'.mem ∧ SameOutside μB σ'.mem b0 (p.sharedEnd b0 - b0))
    ?_ (by omega) fun σ' ⟨hR, hf⟩ =>
      ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩
  unfold sharedCP sharedTimeCP
  refine Ends.next 13 ((sharedBands_spec std hmL pre.space μB rB tb).mono le_rfl ?_)
  rintro _ rfl; unfold sharedLocB
  light_set (p.aENCB b0 : ℕ); light_set (p.aARR b0 : ℕ)
  light_set (p.aZS b0 : ℕ); light_set (p.sharedEnd b0 : ℕ)
  have preA : BandsPre lim p μB (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat (max V 0) :=
    tb.bandsPre pre.space (le_max_right V 0) hVB' tb.phi (coef_le := by omega) (le_enc := le_rfl)
      (enc_le := by omega)
  have hBL : Meets lim P Proc.encodeBandsP (d + 1)
      ((p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)).vals p 0 aX p.D 1) μB
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (p.aENCA b0 + β * p.T)
          (encodingL (bandArrayL (Spec.stdLayout hmL) X β))) ∧
          SameOutside μB μ' (p.aENCA b0)
            ((p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)).zs + p.S7 - p.aENCA b0) := by
    light_facts preA; dsimp only [Par.bandsArgs] at *
    refine .mono_const (encodeBandsP_proc (A := fun β => Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β))
      std hPB preA (by omega)
      (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hArr => ?_) hcb
    · dsimp only [Par.bandsArgs] at hlow
      simpa using bandArrayL_entry std hBA p hmL β aX _ _ _ _ μ' X (by omega)
        (mX.congr_below hlow (by change aX + p.N * p.D ≤ _; omega)) (by omega)
        ((preA.tables.congr_below hlow).mono (by dsimp [Par.bandsArgs]; omega)) hβ _ (by omega)
    · dsimp only [Par.bandsArgs] at hlow
      exact computeEncoding_phi _ ▸ encodeP_entry leftEquiv phi (by decide) (by decide) phiFlat_spec
        std hS hE (by omega) (preA.encodePlaces hβ hlow)
        (preA.coef.congr fun i hi => hlow _ (by dsimp [Par.bandsArgs]; have := Spec.length_phiFlat; omega))
        _ hArr (abs_bandArrayL_le (Spec.stdLayout hmL) preA.V_nonneg hVX β) preA.word
        (preA.m_le_word std hmL)
  light_call hBL with _ μEncA ⟨sA, fEncA⟩
  have lowEncA (x : ℕ) (hx : x < p.aENCA b0) : μEncA x = μB x := fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat (max V 0) :=
    tbEncA.bandsPre pre.space (le_max_right V 0) hVB' tbEncA.psi (coef_le := by omega)
      (le_enc := by omega) (enc_le := by omega)
  have hBR : Meets lim P Proc.encodeBandsP (d + 1)
      ((p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)).vals p 1 aY 1 p.N) μEncA
      (c * (p.nB * (encWorkP p.L p.m + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, SegOn p.m μ' (p.aENCB b0 + β * p.T)
          (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))) ∧
          SameOutside μEncA μ' (p.aENCB b0)
            ((p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)).zs + p.S7 - p.aENCB b0) := by
    light_facts preB; dsimp only [Par.bandsArgs] at *
    refine .mono_const (encodeBandsP_proc (A := fun β => Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β))
      std hPB preB (by omega)
      (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hArr => ?_) hcb
    · dsimp only [Par.bandsArgs] at hlow
      simpa using bandArrayR_entry std hBA p hmL β aY _ _ _ _ μ' Y (by omega)
        ((mY.congr_below lowEncA (by change aY + p.D * p.N ≤ _; omega)).congr_below hlow
          (by change aY + p.D * p.N ≤ _; omega)) (by omega)
        ((preB.tables.congr_below hlow).mono (by dsimp [Par.bandsArgs]; omega)) hβ _ (by omega)
    · dsimp only [Par.bandsArgs] at hlow
      exact computeEncoding_psi _ ▸ encodeP_entry rightEquiv psi (by decide) (by decide) psiFlat_spec
        std hS hE (by omega) (preB.encodePlaces hβ hlow)
        (preB.coef.congr fun i hi => hlow _ (by dsimp [Par.bandsArgs]; have := Spec.length_psiFlat; omega))
        _ hArr (abs_bandArrayR_le (Spec.stdLayout hmL) preB.V_nonneg hVY β) preB.word
        (preB.m_le_word std hmL)
  light_call hBR with _ μEncB ⟨sB, fEncB⟩
  refine (storeLocals_spec hw (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  exact SharedReadyP.of_calls hmL tb sA fEncA sB fEncB (by simpa [SegN, dirList] using sdir)
    (by simpa using fDir)

end BandsAndShared

end Light.Sec2
