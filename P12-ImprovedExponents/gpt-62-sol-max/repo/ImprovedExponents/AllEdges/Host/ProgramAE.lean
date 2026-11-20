module

public import ImprovedExponents.AllEdges.Host.HostAE
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial

@[expose] public section

/-!
# The all-edges host solves all-edges Exact Triangle; the program, assembled

With a solver of Lop-AE-SparseTri and two parameter procedures, the assembled program solves
`aeTask` with the time `hostTimeAE` and the need `hostNeedAE`.
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

variable {P₀ R : Program} {ν : Et17Nums} {pScanPairsAE pFill pBruteAE pLoopAE : ℕ}
  {Tn : List ℕ → ℕ} {need : List ℕ → Need} {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-! ## The core -/

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean
/-- **The core of the all-edges host**: within `hostCoreTime`, it returns the address of the flags
of all-edges Exact Triangle, which lie at or above the free pointer; no cell below the free
pointer changes. -/
theorem aeCore_meets {p : ℕ} (hP : (P₀ ++ R)[p]? = some (aeCoreBody ν pBruteAE pLoopAE))
    (C : AeCtx P₀ R ν pScanPairsAE pFill pBruteAE pLoopAE Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (hostCoreTime Dfun Gfun tD tG Tn x.n x.U)
      (FlagsAt lim x μ fr) := by
  refine .of_body hP ?_
  have hparams := et17Params_spec C.base x μ fr hpre hok
  have hone : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeed, hostNeedAt, hostWord] at hword
    omega
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 28]
  unfold hostNeed at hok
  unfold aeCoreBody hostCoreTime hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  -- the parameters
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  -- if n is small: the brute force
  by_cases hs : SmallCase x.n D g
  · rw [ite_eq_left hs]
    refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [et17LocA, hs]) h)
    have hbrute : (bruteNeed x.n x.U).Ok lim (fr + x.n * x.n) (d + 1) :=
      hok.mono (by light_side [bruteNeed, hostNeedAt, hostWord])
        (by simp only [bruteNeed, hostNeedAt]; omega) (by simp only [bruteNeed, hostNeedAt]; omega)
    have hdepth := hok.depth
    have hcells := hok.cells
    simp only [hostNeedAt] at hdepth hcells
    have hw := hok.space
    refine Ends.callTo (bruteAE_meets C.bruteAE C.base.loop.scan (AeInst.scratch x fr) μ _
      (AeInst.scratch_pre hpre) hbrute) ?_ (by light_side [et17LocA])
    rintro _ _ ⟨rfl, hseg, hkept⟩
    exact ⟨fr, le_rfl, by omega, rfl, hseg, fun b hb => hkept b (.inl hb)⟩
  rw [ite_eq_right hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_)
  -- otherwise: the sizes, then the tables and the loop over the instances
  have hbig := not_smallCase_iff.1 hs
  have htime := hostRunTimeAE_le hpre hbig Tn
  refine Ends.next _ ((et17Sizes_spec C.base x μ fr D g _ _ hpre hbig hok).mono
    le_rfl ?_) (by unfold hostMainAE; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  refine (et17TablesAE_spec C x μ' fr D g _ _ (hpre.keep hk) hbig hok).mono
    (by unfold hostMainAE; simp; omega) ?_
  rintro σ'' ⟨flg, hfr, hsp, hres, hseg, hk'⟩
  exact ⟨flg, hfr, hsp, hres, hseg, hk.trans hk'⟩

/-! ## The program -/

/-- The procedures of the all-edges host: the variant host's `et17Procs` (numbers `o + 0` to
`o + 28`), then the all-edges scan of the pairs (29), the brute force (30), the loop (31), the core
(32), the top procedure (33) and `copy` (34). -/
def aeExtra (pS pD pG o : ℕ) : Program :=
  [scanPairsAEBody (o + 1),                                                   -- 29
    bruteAEBody (o + 1),                                                      -- 30
    hostLoopAEBody pS (o + 23) (o + 24) (o + 29) (o + 14),                    -- 31
    aeCoreBody (et17NumsAt pS pD pG o) (o + 30) (o + 31),                     -- 32
    aeTopBody (o + 32) (o + 34),                                              -- 33
    copyBody]                                                                 -- 34

@[inherit_doc aeExtra]
def aeProcs (pS pD pG o : ℕ) : Program := et17Procs pS pD pG o ++ aeExtra pS pD pG o

variable {pS pD pG : ℕ}

/-- **The all-edges host as a solver of all-edges Exact Triangle**: from a solver of
Lop-AE-SparseTri and two procedures that compute the parameters, in one program `P₀`, the appended
procedures make a solver of `aeTask` with the time `hostTimeAE` and the need `hostNeedAE`. -/
theorem ae17_solves (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves aeTask (P₀ ++ aeProcs pS pD pG P₀.length) (P₀.length + 33)
      (hostTimeAE Dfun Gfun tD tG Tn) (hostNeedAE Dfun Gfun wD wG need) := by
  let o := P₀.length
  let B := aeProcs pS pD pG o
  refine ⟨aeTopBody (o + 32) (o + 34), getElem?_append_append [] (B := B) (i := 33) rfl, ?_⟩
  intro R lim d x μ fr hpre hok
  change (hostNeedAE Dfun Gfun wD wG need x.n x.U).Ok lim fr d at hok
  rw [List.append_assoc]
  have get {i : ℕ} {body : Stmt} (h : B[i]? = some body) := getElem?_append_append R h (P₀ := P₀)
  have C : AeCtx P₀ (B ++ R) (et17NumsAt pS pD pG o) (o + 29) (o + 14) (o + 30) (o + 31)
      Tn need Dfun Gfun tD tG wD wG := by
    dsimp [B, aeProcs]
    rw [List.append_assoc]
    exact ⟨et17Ctx_assembled hsol hD hG hpos _, get rfl, get rfl, get rfl, get rfl⟩
  change Ends _ _ _ _ ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.out, fr], μ⟩
    (hostTimeAE Dfun Gfun tD tG Tn x.n x.U) _
  have hdepth := hok.depth
  have hcells := hok.cells
  have hw := hok.space
  simp only [hostNeedAE, hostNeed, hostNeedAt] at hdepth hcells
  have hok₁ : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr (d + 1) :=
    hok.mono le_rfl le_rfl (by simp only [hostNeedAE, hostNeed]; omega)
  have hlay : 3 * (x.n * x.n) ≤ hostLayout x.n x.U (Dfun x.n) := by unfold hostLayout; omega
  have hout := hpre.belowOut
  unfold aeTopBody hostTimeAE
  -- flg := aeCore(n, U, ab, bc, ac, fr)
  light_call (aeCore_meets (get (i := 32) rfl) C x.toTriInst μ fr hpre.toPre hok₁)
    with r μ₁ ⟨flg, hfr, hsp, rfl, hseg, hkept⟩
  -- flg := copy(flg, out, n * n)
  have hn : ((x.n * x.n : ℕ) : ℤ) = (x.n : ℤ) * (x.n : ℤ) := by rfl
  have hsep : Apart flg (x.n * x.n) x.out (x.n * x.n) := Or.inr (by omega)
  refine Ends.callTo (copy_meets (get (i := 34) rfl) hw hsp (by omega) hsep)
    ?_ (by light_side [hn])
  rintro _ μ₂ ⟨hcopy, hsame⟩
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · rw [length_aeFlags] at hi
    aesop
  · exact (hsame c hc.2).trans (hkept c hc.1)

end ImprovedExponents.AllEdges
