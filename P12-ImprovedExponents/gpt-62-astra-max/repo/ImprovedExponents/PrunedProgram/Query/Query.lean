module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Query
public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ImprovedExponents.PrunedProgram.Boxes.Routines

@[expose] public section

/-!
# A query, from the block that holds the data structure on pruned encodings

Upstream's `queryAt_spec` proves the routine `queryAtBody` (procedure 55: the sizes and the bands
from the directory, the areas, the digits of the output string by `outDigits`, the sum of Lemma 28
by `queryCore`) under `DSReady`, which holds the encodings of all bands as full segments.  Of the
data structure, the routine reads the directory, the tables, the roots, the tries and — in
`queryCore` only — the cells of the leaves of order below `t` contributing to the output string of
the position, which have at most `m` symbols `P₀`.  So the routine is correct under `DSReadyP`,
where the encodings are right at these leaves only: `queryAtP_spec` is `queryAt_spec` with
`DSReadyP` in the pre- and postcondition and `QueryCoreSpecP` (`queryCoreP_spec`) in place of
`QueryCoreSpec`; the body and the time are upstream's.  The parts of the proof that do not read
the data structure (`queryAtAreas_spec`, `coreArgs`, `coreArgs_value`, …) are reused; those that
do are copied with `DSReadyP` in place of `DSReady`, under the same names with a `P`.

`queryAtP_of_base58` discharges the assumptions for every program `base58 ++ R` that begins with
upstream's 58 procedures, as upstream's `queryAt_base58`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean`, `Directory.lean`,
`Areas.lean`, `Routines.lean` and `Program.lean` (Apache-2.0).
-/

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first part -/

section
variable (hlim : Lim30 lim p t b0 U)
  (hds : DSReadyP p t hmL aX aY b0 X Y μ)
  {I J : ℕ}
  (hI : I < p.N)
  (hJ : J < p.N)
include hlim hds hI hJ

/-- The first part reads the sizes, the addresses of the tables, and the two bands. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtReads_spec)
theorem queryAtReadsP_spec :
    Ends lim P d queryAtReads ⟨frame [(I : ℤ), (J : ℤ), (b0 : ℤ)], μ⟩ 90
      (· = ⟨frame (queryAtRead p t b0 I J), μ⟩) := by
  have hw := hlim.std.space_le
  have hdir : b0 + 31 < lim.space ∧ p.aBAND b0 + p.N ≤ lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have dir := hds.shared.dirCells
  have cellT : μ ((b0 : ℤ) + 31).toNat = (t : ℕ) :=
    (congrArg μ (toNat_natCast_add_natCast b0 31)).trans hds.cellT
  have bandI := hds.shared.band I hI
  have bandJ := hds.shared.band J hJ
  -- levels := dir[0]; inner := dir[1]; switch := dir[31]; outer := dir[4]
  light_set (p.L : ℕ) using dir.levels
  light_set (p.m : ℕ) using dir.inner
  light_set (t : ℕ) using cellT
  light_set (p.Lo : ℕ) using dir.outer
  -- blocks := dir[7]; bands := dir[9]; leaves := dir[10]
  light_set (p.K0 : ℕ) using dir.blocks
  light_set (p.nB : ℕ) using dir.bands
  light_set (p.T : ℕ) using dir.leaves
  -- bandTab := dir[22]; blockTab := dir[23]; digitTab := dir[24]; digits := dir[30]
  light_set (p.aBAND b0 : ℕ) using dir.band
  light_set (p.aBLOCK b0 : ℕ) using dir.block
  light_set (p.aDIG3 b0 : ℕ) using dir.digits
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  -- bandI := bandTab[I]; bandJ := bandTab[J]
  light_set (I / (p.K0 * p.N0) : ℕ) using bandI
  light_set (J / (p.K0 * p.N0) : ℕ) using bandJ
  rfl

/-! ## The call of outDigits -/

/-- The block holds what outDigits assumes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (outArgs_pre)
theorem outArgsP_pre : OutDigitsPre lim μ (outArgs p b0 I J) := by
  have hgI : I / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hgJ : J / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hidx : I / p.N0 % p.K0 * p.K0 + J / p.N0 % p.K0 < p.KK := Nat.mul_add_lt_mul hgI hgJ
  -- the three tables lie below WD, and WD inside the memory
  have hsp := hlim.space
  have hmaskI := Nat.mul_add_le_mul hidx (le_refl p.L)
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hLo : p.L - p.m = p.Lo := rfl
  obtain ⟨⟩ := areas p t b0
  refine
    { std := hlim.std
      m_le := hmL
      gI_lt := hgI
      gJ_lt := hgJ
      index_lt := tableIndex_lt p.L p.m (⟨_, hgI⟩, ⟨_, hgJ⟩)
      segMask := segN_of_segB (hds.shared.mask _ hidx)
      segI := hds.shared.dig3 I hI
      segJ := hds.shared.dig3 J hJ
      lenI := length_digitList ..
      lenJ := length_digitList ..
      ltI := fun _ => lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => lt_of_mem_digitList (by norm_num)
      spaceMasks := by change p.aMASK b0 + p.KK * p.L < lim.space; omega
      apartMask := ?_
      apartI := ?_
      apartJ := ?_
      spaceI := ?_
      spaceJ := ?_
      spaceDest := ?_ }
  -- the six fields that are left: the tables lie apart from WD, and all within the memory
  all_goals
    simp [outArgs, OutDigitsArgs.base]
    omega

end

/-- The third part writes the digits of the output string of (I, J) at WD. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtOut_spec)
theorem queryAtOutP_spec (hOut : OutDigitsSpec lim P) (hlim : Lim30 lim p t b0 U)
    (hds : DSReadyP p t hmL aX aY b0 X Y μ) {I J } (hI : I < p.N) (hJ : J < p.N)
    (hd : d + 1 ≤ lim.depth) :
    Ends lim P d queryAtOut ⟨frame (queryAtLocals p t b0 I J), μ⟩ (tOutDigits p.L + 40) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ'⟩ ∧
        SegN μ' (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J)) ∧
        SameOutside μ μ' (aWD p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := outArgsP_pre hlim hds hI hJ
  have blockI := hds.shared.block I hI
  have blockJ := hds.shared.block J hJ
  have hsp := hlim.space
  have hrowI := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have hrowJ := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have hbound : b0 + 31 < lim.space ∧ p.aBLOCK b0 + p.N ≤ lim.space ∧
      p.aDIG3 b0 + p.N * p.Lo ≤ lim.space := by
    obtain ⟨⟩ := areas p t b0
    omega
  have hprodI : ((p.aDIG3 b0 + I * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega)
  have hprodJ : ((p.aDIG3 b0 + J * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega)
  light_call (hOut _ μ hpre) using queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
    hds.shared.dirCells.mask with r μ' h
  refine ⟨r, μ', rfl, ?_, h.2⟩
  rw [digitsO_outStrOfPos]
  exact h.1

/-! ## The call of queryCore -/

/-- Choose the precomputed page by its row-major tile index. -/
def pageArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (I J : ℕ) :
    BoxTable.QueryCoreArgs where
  toTile := (grid p t hmL b0 X Y).tile (I / (p.K0*p.N0)) (J / (p.K0*p.N0))
  wd := aWD p b0
  ss := aSS p b0
  η := outStrOfPos (stdLayout hmL) I J

theorem coreArgsP_pre (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReadyP p t hmL aX aY b0 X Y μ) (I J : Fin p.N)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    BoxTable.Pre lim μ (pageArgs p t hmL b0 X Y I J) := by
  have hU := (abs_nonneg _).trans (hX I ⟨0, Nat.pow_pos (by norm_num)⟩)
  have hβ : (I : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N I I.isLt
  have hβ' : (J : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N J J.isLt
  let β := (I:ℕ) / (p.K0*p.N0)
  let γ := (J:ℕ) / (p.K0*p.N0)
  let x := grid p t hmL b0 X Y
  have hsp := hlim.space
  have hx := hds.pages β hβ γ hβ' (Nat.mul_add_lt_mul hβ hβ')
  have room := BoxTable.Grid.room (x:=x) hβ hβ'
  have left := Nat.mul_add_le_mul hβ (le_refl p.T); have right := Nat.mul_add_le_mul hβ' (le_refl p.T)
  have card := card_innerSetO_outStrOfPos (stdLayout hmL) I J
  obtain ⟨hA,hB⟩ := abs_enc_le hmL X Y U hU hX hY β γ
  refine ⟨hlim.std,ht,card,hds.shared.encA _ hβ,hds.shared.encB _ hβ',?_,hwd,
    fun j => (abs_query_partial_sum_le hA hB ht card j).trans hlim.value,
    abs_enc_mul_le hlim hU hX hY β γ,hlim.pow_le,?_⟩
  · intro l hl
    obtain ⟨π,hπ,rfl⟩ := exists_of_mem_boxesOf ht card l hl
    obtain ⟨V,hV,hπ⟩ := Finset.mem_biUnion.mp hπ
    have mem := (isBoxDigits_digitsC p.m t π).2 (Theorem30.lookup hV hπ)
    apply hx _ _ mem (.inl ?_)
    obtain ⟨s,hs,-⟩ := List.mem_map.1 mem
    have := (mem_nineStrs _).1 hs
    change starCount (digitsC π) < p.m-t+1; omega
  · obtain ⟨⟩ := areas p t b0
    dsimp only [pageArgs,BoxTable.Grid.tile,grid]
    change aPage p b0 + (β*p.nB+γ)*(p.T*p.T) + p.T*p.T ≤ aPage p b0 + pageCells p at room
    change p.aENCA b0 + β*p.T + p.T ≤ aWD p b0 ∧ p.aENCB b0 + γ*p.T + p.T ≤ aWD p b0 ∧ _ ∧ _ ∧
      aSS p b0 + p.m ≤ aPage p b0 + (β*p.nB+γ)*(p.T*p.T) ∧
      aPage p b0 + (β*p.nB+γ)*(p.T*p.T) + p.T*p.T < lim.space
    change β*p.T + p.T ≤ _ at left; change γ*p.T + p.T ≤ _ at right
    omega

/-- The fourth part returns (XY)[I, J] and changes the scratch strings BOX and SS only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtCore_spec)
theorem queryAtCoreP_spec (hCore : BoxTable.QueryCoreSpecP lim P) (ht : t ≤ p.m)
    (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hds : DSReadyP p t hmL aX aY b0 X Y μ) (I J : Fin p.N) (hd : d + 2 ≤ lim.depth) (r : ℤ)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    Ends lim P d queryAtCore ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ⟩
      (tQueryCore p.L p.m t + 60) fun σ' =>
        σ'.loc 0 = (X * Y) I J ∧ SameOutside2 μ σ'.mem (aSS p b0) p.m (aBOX p b0) p.L := by
  have hw := hlim.std.space_le
  have hpre := coreArgsP_pre ht hlim hX hY hds I J hwd
  have dir := hds.shared.dirCells
  let x := pageArgs p t hmL b0 X Y I J
  have hvalue : x.terms.sum = (X*Y) I J :=
    (sum_queryTerms_storedD ht x.A x.B (card_innerSetO_outStrOfPos (stdLayout hmL) I J)).trans
      (Theorem30.correct t ht (stdLayout hmL) X Y I J)
  let β := (I:ℕ)/(p.K0*p.N0); let γ := (J:ℕ)/(p.K0*p.N0)
  have layout := hpre.layout
  change p.aENCA b0 + β*p.T + p.T ≤ aWD p b0 ∧ p.aENCB b0 + γ*p.T + p.T ≤ aWD p b0 ∧
    aWD p b0 + p.L ≤ aBOX p b0 ∧ aBOX p b0 + p.L ≤ aSS p b0 ∧
    aSS p b0 + p.m ≤ aPage p b0 + (β*p.nB+γ)*(p.T*p.T) ∧
    aPage p b0 + (β*p.nB+γ)*(p.T*p.T) + p.T*p.T < lim.space at layout
  have o := Nat.le_mul_of_pos_right (β*p.nB+γ) (Nat.mul_pos (show 0<p.T by exact pow_pos (by decide) _) (show 0<p.T by exact pow_pos (by decide) _))
  have hd' := wd_ge p b0
  have hn (a b : ℕ) : (0:ℤ) ≤ a*b := by positivity
  have hn' : (0:ℤ) ≤ (β*p.nB+γ)*(p.T*p.T) := by positivity
  have meets := hCore x μ hpre _ (by omega)
  change Meets _ _ _ _ [p.aENCA b0 + β*p.T, p.aENCB b0 + γ*p.T, aPage p b0 + (β*p.nB+γ)*(p.T*p.T),
    aWD p b0,aSS p b0,aBOX p b0,p.L,p.m,t] _ (tQueryCore p.L p.m t) _ at meets
  unfold queryAtLocals queryAtRead
  dsimp only [β,γ] at layout o hn' meets
  generalize (I : ℕ) / (p.K0*p.N0) = i at layout o hn' meets ⊢
  generalize (J : ℕ) / (p.K0*p.N0) = j at layout o hn' meets ⊢
  zify at layout o
  have := hn i p.T; have := hn j p.T; have := hn i p.nB; have := hn p.T p.T
  light_call meets using dir.encA,dir.encB with r' ν ⟨hr,same⟩
  exact ⟨hr.trans hvalue,same⟩

/-! ## The routine -/

/-- **queryAt** meets its specification on pruned encodings: upstream's routine, under the
assumption that the encodings of the bands are right at the leaves with at most `m` symbols `P₀`
only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAt_spec)
theorem queryAtP_spec (hP : P[Proc.queryAt]? = some queryAtBody) (hOut : OutDigitsSpec lim P)
    (hCore : BoxTable.QueryCoreSpecP lim P) : QueryAtSpecP lim P := by
  intro p t hmL aX aY b0 X Y U μ I J ht hlim hX hY hds
  refine fun d hd => ⟨queryAtBody, hP, ?_⟩
  unfold tQueryAt
  -- the sizes, the tables, the bands
  light_piece (queryAtReadsP_spec hlim hds I.isLt J.isLt) with _ rfl
  -- the areas
  light_piece (queryAtAreas_spec hlim I J) with _ rfl
  -- the digits of the output string, which change WD only
  light_piece (queryAtOutP_spec hOut hlim hds I.isLt J.isLt (by omega))
    with _ ⟨r, μ₁, rfl, hwd, same₁⟩
  have same₁' : SameOutside μ μ₁ (aWD p b0) (3 * p.L + p.m) := same₁.mono le_rfl (by omega)
  -- the sum of Lemma 28, which changes BOX and SS only
  light_piece (queryAtCoreP_spec hCore ht hlim hX hY (hds.of_same same₁') I J (by omega) r hwd)
    with ⟨loc₂, μ₂⟩ ⟨hr, same₂⟩
  have same₂' : SameOutside μ μ₂ (aWD p b0) (3 * p.L + p.m) := by
    obtain ⟨⟩ := areas p t b0
    exact same₁'.then same₂ fun b hb => ⟨hb, by omega, by omega⟩
  exact ⟨hr, hds.of_same same₂', same₂'⟩

end Proof

theorem queryAtSpecP_all {P} (h : BoxTable.Has P) (h55 : P[Proc.queryAt]? = some queryAtBody) :
    ∀ lim, QueryAtSpecP lim P := fun _ p t hmL aX aY b0 X Y U μ I J ht hlim =>
  queryAtP_spec h55 (outDigits_spec (h 12 (by decide))) (BoxTable.querySpec h hlim.std)
    p t hmL aX aY b0 X Y U μ I J ht hlim

end Light.Sec4
