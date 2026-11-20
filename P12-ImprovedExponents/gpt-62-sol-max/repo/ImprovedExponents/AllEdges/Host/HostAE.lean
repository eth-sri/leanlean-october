module

import ThreeSumApsp.Lang.Symbolic

public import ImprovedExponents.AllEdges.Host.LoopAE
public import ImprovedExponents.AllEdges.Host.BruteAE
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total

@[expose] public section

/-!
# The all-edges host: the program, its time and its need

The all-edges variant of the host of Theorem 17 is the host of `ImprovedExponents.HostMid` (the
solver is charged at the inner dimension `midSize D g`) with the loop over the instances replaced
by `hostLoopAE`, the brute force by `bruteAE`, and the solver's free pointer moved up by `n²` cells
that hold the flags (`et17TablesAE`, `aeCoreBody`).  The top procedure `aeTopBody` copies the `n²`
flags to the place `out` of the task (`aeTask`).

This file holds the text, the time (`hostTimeAE`), the need (`hostNeedAE`), the specifications of
the parts (`et17TablesAE_spec`, `aeCore_spec`, `aeTop_spec`), the assembled program (`aeProcs`)
and the statement that it solves all-edges Exact Triangle (`ae17_solves`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-! ## The text -/

open Et17 in
/-- The third part of the all-edges host: upstream's `et17Tables` with the all-edges loop, whose
free pointer is `n²` cells above the answers; the flags lie in between. -/
def et17TablesAE (ν : Et17Nums) (pLoopAE : ℕ) : Stmt :=
  ResidueTables.body ν.pDbl ν.pResidues ;;
  .call ν.pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
  .call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;;
  .set NumInst (v NumPieces *' v NumChunks) ;;
  .call pLoopAE [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst, v AdrAB, v AdrBC,
    v AdrAC, v ResAC, v ResBC, v Rows, v Cols, v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut,
    v SolverFree +' v SizeSq] 0

open Et17 in
/-- aeCore(n, U, ab, bc, ac, fr): the parameters, then the brute force or the three parts of the
variant host; it returns the address of the `n²` flags, which lie at or above `fr`. -/
def aeCoreBody (ν : Et17Nums) (pBruteAE pLoopAE : ℕ) : Stmt :=
  et17Params ν ;;
  .ite (v Small =' k 1)
    (.call pBruteAE [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free, v Free +' v Size *' v Size] 0)
    (et17Sizes ν ;; et17TablesAE ν pLoopAE)

/-- ae(n, U, ab, bc, ac, out, fr): the core, then the `n²` flags are copied to `out`. -/
def aeTopBody (pCore pCopy : ℕ) : Stmt :=
  .call pCore [v 0, v 1, v 2, v 3, v 4, v 6] 7 ;;
  .call pCopy [v 7, v 5, v 0 *' v 0] 7

/-! ## Time and need -/

/-- A bound on the time of the all-edges loop: as `hostLoopBound'`, with the all-edges scan of the
answers, at most `falsePositiveBound + n²` scans, and the filling of the flags. -/
noncomputable def hostLoopBoundAE (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n (midSize D g) (queryCapNat n D)
        + tAnswersAE (queryCapNat n D))
    + tScanCallAE (pieceSizeNat D g) * (falsePositiveBound n U D + n * n) + fillTime (n * n) + 40

/-- The time of the core after the tests, if n is not small. -/
noncomputable def hostMainAE (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBoundAE Tn n U D g + 300

/-- A bound on the time of the core in the worst case. -/
noncomputable def hostCoreTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBruteAE n + 20
    else hostMainAE Tn n U (Dfun n) (Gfun (Dfun n))

/-- **A bound on the time of the all-edges host in the worst case**, for the parameter functions
Dfun, Gfun with the times tD, tG, over a solver with the time Tn: the core and the copy. -/
noncomputable def hostTimeAE (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostCoreTime Dfun Gfun tD tG Tn n U + copyTime (n * n) + 20

/-- One extra level for the call of the core. -/
def hostNeedAE (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeed Dfun Gfun wD wG need n U 1

/-- The time of the third part in a run of the all-edges host. -/
def hostRunTimeAE (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tHostLoopAE Tn X + 80

/-! ## The context -/

/-- The context of the all-edges host: that of the variant host, and the new procedures. -/
structure AeCtx (P₀ R : Program) (ν : Et17Nums) (pScanPairsAE pFill pBruteAE pLoopAE : ℕ)
    (Tn : List ℕ → ℕ) (need : List ℕ → Need) (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  base : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG
  scanPairsAE : (P₀ ++ R)[pScanPairsAE]? = some (scanPairsAEBody ν.pScan)
  fill : (P₀ ++ R)[pFill]? = some fillBody
  bruteAE : (P₀ ++ R)[pBruteAE]? = some (bruteAEBody ν.pScan)
  loopAE : (P₀ ++ R)[pLoopAE]? =
    some (hostLoopAEBody ν.pS ν.pWriteX ν.pWriteY pScanPairsAE pFill)

variable {P₀ R : Program} {ν : Et17Nums} {pScanPairsAE pFill pBruteAE pLoopAE : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- The context of the all-edges loop. -/
theorem AeCtx.loop (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG
    wD wG) :
    HostCtxAE P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScan pScanPairsAE pFill Tn need :=
  { C.base.loop with scanPairsAE := C.scanPairsAE, fill := C.fill }

/-! ## The third part -/

/-- The core returns the address of a scratch array of flags and leaves the inputs unchanged. -/
def FlagsAt (lim : Limits) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ) (ν : ℕ → ℤ) : Prop :=
  ∃ flg : ℕ, fr ≤ flg ∧ flg + x.n * x.n ≤ lim.space ∧ r = flg ∧
    Seg ν flg (aeFlags x.n x.AB x.BC x.AC) ∧ Kept μ ν fr

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Arrays.lean
set_option maxHeartbeats 800000 in
open Et17 in
/-- **The third part of the all-edges host**: the result is the address of the flags, which hold
the flags of all-edges Exact Triangle; only cells from the free pointer on change. -/
theorem et17TablesAE_spec
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17TablesAE ν pLoopAE) ⟨frame (et17LocB x fr D g), μ⟩
      (hostRunTimeAE Tn (hostData x D g) x.U)
      fun σ' => FlagsAt lim x μ fr (σ'.loc 0) σ'.mem := by
  have hr := ready_of hpre hbig hok
  have hlim := hostLim_of_ok hbig hok
  have hv := hostData_valid hpre hbig
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  unfold et17LocB
  generalize hX : hostData x D g = X at hr hlim hv ⊢
  have hn : X.n = x.n := by rw [← hX]; rfl
  have hfr : fr ≤ aX X x.U fr := by
    have := host_places X x.U fr
    omega
  unfold et17TablesAE hostRunTimeAE
  -- the table of doubles and the residues; the classes and the chunks
  have hplaces := host_places X x.U fr
  have htop := hr.top
  light_piece (ResidueTables.spec C.base.hDbl C.base.hResid C.base.hResidues hr.toArrays
    hr.space hr.prime (Nat.lt_size_self _) hr.word hr.depth (by change aCls X x.U fr ≤ _; omega))
    with _ ⟨r₁, μ₁, rfl, tabs, same⟩
  dsimp only [ResidueTables.time, hostInput]
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.arrAB.len
  have ltRAB : ∀ r ∈ X.RAB, r < X.p := fun r hmem => lt_of_mem_residList hr.prime hmem
  have hroom : (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length ≤ X.n * X.n + X.p :=
    hr.chunkCount_le hv.cap_pos
  -- Small := pClasses(ResAB, Size, ThePrime, Cls, Cur, Rows, Cols)
  refine Ends.callToThen (classes_meets C.base.hClasses hr.space
    { rab := aRab X x.U fr, n := X.n, p := X.p, cls := aCls X x.U fr, cur := aCur X x.U fr,
      qi := aQi X x.U fr, qj := aQj X x.U fr, RAB := X.RAB } μ₁
    { seg := tabs.rab, len := lenRAB, lt := ltRAB }) ?_ (by simp <;> rfl)
  rintro r₂ μ₂ ⟨hcls, hqi, hqj, same₂⟩
  dsimp only at hcls hqi hqj same₂
  have htc : tChunks X.p (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length =
      tChunks X.p X.chunkCount := rfl
  -- NumChunks := pChunks(Cls, ThePrime, Cap, TabR, TabL, TabW)
  refine Ends.callToThen (chunks_meets C.base.hChunks hr.space
    { cls := aCls X x.U fr, p := X.p, cap := X.cap, cr := aCr X x.U fr, cl := aCl X x.U fr,
      cw := aCw X x.U fr, R := X.n * X.n + X.p, B := X.n * X.n, C := classStarts X.n X.p X.RAB } μ₂
    { seg := hcls, len := length_classStarts X.n X.p X.RAB,
      le := fun y hy => le_of_mem_classStarts hy, room := hroom, hcap := hv.cap_pos }) ?_ (by simp)
    (hT := by light_time [ChunksArgs.table, htc])
  rintro _ μ₃ ⟨rfl, hcr, hcl, hcw, same₃⟩
  simp only [ChunksArgs.table, ChunksArgs.Same] at hcr hcl hcw same₃ ⊢
  have hsorted : (sortedIdx X.n X.p X.RAB).length ≤ X.n * X.n := by
    rw [length_sortedIdx_eq]
    exact classStart_le_sq X.n X.RAB X.p
  have keepChunks : Kept μ₂ μ₃ (aCr X x.U fr) := fun c hc => same₃ _ ⟨by omega, by omega, by omega⟩
  have keepClass : Kept μ₁ μ₃ (aCls X x.U fr) := fun c hc =>
    (keepChunks c (by omega)).trans (same₂ c (Or.inl hc))
  have keepInputs : Kept μ μ₃ fr :=
    (SameOn.mono same fun _ => Or.inl).trans (keepClass.mono fun _ _ => by omega)
  have ha := hr.toArrays.keep keepInputs
  have lenRAC : X.RAC.length = X.n * X.n := (length_residList _ _).trans hr.arrAC.len
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.arrBC.len
  have keepSeg {ν : ℕ → ℤ} {a e : ℕ} {l : List ℕ} (hk : Kept ν μ₃ e)
      (h : SegN ν a l) (hb : a + l.length ≤ e) : SegN μ₃ a l :=
    h.keep (hk.mono fun _ hc => hc.2.trans_le hb)
  have hmem : HostMem X (hostAddr x X fr) μ₃ :=
    ⟨ha.arrAB.seg, ha.arrBC.seg, ha.arrAC.seg, keepSeg (a := aRac X x.U fr) keepClass tabs.rac (by omega),
      keepSeg (a := aRbc X x.U fr) keepClass tabs.rbc (by omega),
      keepSeg (l := X.QI) (a := aQi X x.U fr) keepChunks hqi (by simp [HostData.QI, queryRows]; omega),
      keepSeg (l := X.QJ) (a := aQj X x.U fr) keepChunks hqj (by simp [HostData.QJ, queryCols]; omega), hcr, hcl, hcw⟩
  -- NumInst := NumPieces * NumChunks
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := Int.natCast_mul ..
  change Ends _ _ _ _ ⟨frame (locals x X fr g (Nat.sqrt D : ℕ) X.chunkCount r₂), μ₃⟩ _ _
  rw [htc]
  light_step using hm
  -- the result is pLoopAE(…)
  have hlay := hostLay_of hr (hr.chunkCount_le hv.cap_pos)
  have hx : aX X x.U fr ≤ aFr X x.U fr := by omega
  have hfrS : aFr X x.U fr + X.n * X.n < lim.space := hlim.fr
  have hsw := hlim.space
  have hfrW : (aFr X x.U fr : ℤ) + (X.n : ℤ) * (X.n : ℤ) ≤ lim.word := by
    omega
  have houtA : (hostAddr x X fr).out = aOut X x.U fr := rfl
  have hF : FlagsPlace X (hostAddr x X fr) (aFr X x.U fr) := ⟨rfl, hx, fun t ht => Nat.add_le_add_left (X.w_le_cap ht) _⟩
  have hargs : ((aFr X x.U fr + X.n * X.n : ℕ) : ℤ) = (aFr X x.U fr : ℤ) + ((X.n * X.n : ℕ) : ℤ) :=
    by push_cast; rfl
  have hrac : ResidueTables.rac fr (bitLen x.U) X.n = aRac X x.U fr := rfl
  have hrbc : ResidueTables.rbc fr (bitLen x.U) X.n = aRbc X x.U fr := rfl
  light_call (hostLoopAE_meets C.loopAE C.loop ⟨hv, hr.arrAB.bound, hr.arrBC.bound, hr.arrAC.bound⟩
    hmem hlay hlim hF) using hostLoopArgs, hostAddr, hargs, hrac, hrbc with _ μ₄ ⟨rfl, hflags, hkept⟩
  exact ⟨aFr X x.U fr, by omega, by rw [← hn]; exact hfrS.le, rfl,
    by rw [← hX] at hflags ⊢; exact hflags, fun c hc => (hkept c (hc.trans_le hfr)).trans (keepInputs c hc)⟩

/-! ## The time of a run is within the worst case -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Time.lean
/-- The time of an instance of the all-edges host with a piece of `len ≤ q` vertices, `w ≤ cap`
query pairs and `execs` scans is at most the worst case for `q` and `cap` plus the time of the
scans. -/
theorem instanceAE_le (Tn : List ℕ → ℕ) (n D g execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n (midSize D g) len + Tn [n, midSize D g, w] + tScanPairsAE w len execs
      ≤ tWrites n D q + supTime Tn n (midSize D g) cap + tAnswersAE cap
        + tScanCallAE q * execs := by
  have hwrites := tWrites_le n (midSize_le D g) hlen
  have hsolver : Tn [n, midSize D g, w] ≤ supTime Tn n (midSize D g) cap :=
    Finset.le_sup (f := fun w => Tn [n, midSize D g, w]) (Finset.mem_range.2 (by omega))
  have hanswers : tAnswersAE w ≤ tAnswersAE cap := by
    unfold tAnswersAE
    gcongr
  have hscans : tScanCallAE len * execs ≤ tScanCallAE q * execs := by
    unfold tScanCallAE tScan
    gcongr
  unfold tScanPairsAE
  omega

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- Each scan fails or sets a flag: at most `falsePositiveBound + n²` scans. -/
theorem sum_execsAE_le_falsePositiveBound (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) :
    ∑ t ∈ Finset.range (hostData x D g).m, (hostData x D g).execsAE t
      ≤ falsePositiveBound x.n x.U D + x.n * x.n :=
  ((hostData x D g).sum_execsAE_le (hostData_valid hpre hbig)).trans (Nat.add_le_add_right
    ((HostData.sum_fails_le (hostData_valid hpre hbig)).trans (F_le_falsePositiveBound hpre hbig))
    _)

/-- The time of the all-edges loop is within its bound. -/
theorem tHostLoopAE_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tHostLoopAE Tn (hostData x D g) ≤ hostLoopBoundAE Tn x.n x.U D g := by
  unfold tHostLoopAE hostLoopBoundAE
  exact Nat.add_le_add_right (Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instanceAE_le Tn x.n D g _ (Nat.min_le_left _ _) ((hostData x D g).w_le_cap ht))
    (hostData_m_le hbig) (sum_execsAE_le_falsePositiveBound hpre hbig)) _) _

/-- **The time of a run of the all-edges host after the choice of the prime is within the worst
case.** -/
theorem hostRunTimeAE_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    hostRunTimeAE Tn (hostData x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBoundAE Tn x.n x.U D g + 80 := by
  have hprime : (hostData x D g).p ≤ Nat.sqrt D := hostData_p_le x g hbig.sixteen_le
  have hchunks : (hostData x D g).chunkCount ≤ 4 * x.n * g :=
    (chunkCount_le_m (hostData_valid hpre hbig)).trans (hostData_m_le hbig)
  have hloop := tHostLoopAE_le hpre hbig Tn
  have hn : (hostData x D g).n = x.n := rfl
  unfold hostRunTimeAE
  rw [hn]
  unfold tClasses tChunks
  omega

end ImprovedExponents.AllEdges
