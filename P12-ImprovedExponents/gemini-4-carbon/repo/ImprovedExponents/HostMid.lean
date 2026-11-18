module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total

@[expose] public section

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

def midSize (D g : ℕ) : ℕ := pieceSizeNat D g * Nat.sqrt D

theorem pieceSizeNat_le_sqrt (D g : ℕ) : pieceSizeNat D g ≤ Nat.sqrt D := by
  unfold pieceSizeNat
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · exact (ceilDiv_le_iff_le_smul hg).2 (by simpa using Nat.le_mul_of_pos_left _ hg)

theorem midSize_le (D g : ℕ) : midSize D g ≤ D :=
  (Nat.mul_le_mul_right _ (pieceSizeNat_le_sqrt D g)).trans (Nat.sqrt_le D)

theorem one_le_midSize {D g : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) : 1 ≤ midSize D g := by
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  exact Nat.mul_pos ((Nat.lt_ceilDiv_iff hg).2 (by omega)) (by omega)

def midArgs (G : ℕ → ℕ) : List ℕ → List ℕ
  | [n, D, w] => [n, midSize D (G D), w]
  | ps => ps

theorem polyBound_midArgs_le (G : ℕ → ℕ) (s k : ℕ) (ps : List ℕ) :
    polyBound s k (midArgs G ps) ≤ polyBound s k ps := by
  unfold midArgs
  split
  · simp  [polyBound]
    gcongr; exact midSize_le _ _
  · exact le_rfl

theorem polyNeedN_midArgs {need : List ℕ → Need} (G : ℕ → ℕ) (h : PolyNeedN need) :
    PolyNeedN fun ps => need (midArgs G ps) := by
  obtain ⟨s, k, hle⟩ := h
  exact ⟨s, k, fun ps => ⟨(hle _).1.trans (polyBound_midArgs_le G s k ps),
    (hle _).2.1.trans (polyBound_midArgs_le G s k ps),
    (hle _).2.2.trans (polyBound_midArgs_le G s k ps)⟩⟩

open Et17 in
def et17Sizes' (ν : Et17Nums) : Stmt :=
  .call ν.pChoose [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v ParD, v Free] ThePrime ;;
  .call ν.pCap [v Size, v ParD] Cap ;;
  .call ν.pCeil [v RootD, v ParG] PieceLen ;;
  .call ν.pCeil [v Size, v PieceLen] NumPieces ;;
  .call ν.pBitLen [v Bound] Bits ;;
  .set ParD (v PieceLen *' v RootD) ;;
  et17Addr

noncomputable def hostLoopBound' (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n (midSize D g) (queryCapNat n D)
        + tAnswers (queryCapNat n D))
    + tScanCall (pieceSizeNat D g) * (falsePositiveBound n U D + 1) + 14

noncomputable def hostMain' (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBound' Tn n U D g + 300

noncomputable def hostTime' (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBrute n + 20
    else hostMain' Tn n U (Dfun n) (Gfun (Dfun n))

def hostNeedAt' (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n (midSize D g) (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n (midSize D g) (queryCapNat n D)).cells
      + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n (midSize D g) (queryCapNat n D)).depth⟩

def hostNeed' (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedAt' (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

theorem hostTime'_eq (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) :
    hostTime' Dfun Gfun tD tG Tn n U
      = hostTime Dfun Gfun tD tG (fun ps => Tn (midArgs Gfun ps)) n U := rfl

def hostData' (x : TriInst) (D g : ℕ) : HostData :=
  ⟨x.n, midSize D g, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB,
    x.BC, x.AC⟩

def et17LocB' (x : TriInst) (fr D g : ℕ) : List ℤ :=
  Et17.locals x (hostData' x D g) fr g (Nat.sqrt D : ℕ) 0 0

theorem hostData'_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData' x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

theorem hostData'_m_le {x : TriInst} {D g : ℕ} (h : BigCase x.n D g) :
    (hostData' x D g).m ≤ 4 * x.n * g :=
  hostData_m_le h

theorem hostData'_valid {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData' x D g).Valid :=
  have hv := hostData_valid hpre h
  ⟨hv.n_pos, hv.p_pos, hv.q_pos, hv.cap_pos,
    Nat.mul_le_mul_left _ (hostData'_p_le x g h.sixteen_le), hv.lenAB, hv.lenBC, hv.lenAC⟩

theorem aFr_le' {x : TriInst} {D g : ℕ} (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData' x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have hp : chosenPrime x.n D x.AB x.BC x.AC ≤ Nat.sqrt D := chosenPrime_le_sqrt x.AB x.BC x.AC hD
  have hmid : x.n * midSize D g ≤ x.n * D := Nat.mul_le_mul_left _ (midSize_le D g)
  simp  [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab, hostData']
  unfold hostLayout; omega

theorem hostLim_of_ok' {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst}
    {fr D g : ℕ} (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData' x D g) x.U (hostAddr x (hostData' x D g) fr) need := by
  have hD : 16 ≤ D := hbig.sixteen_le
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).depth) ≤ lim.depth := hok.depth
  have hword : ((hostWord a b x.n x.U D g
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have hfr := aFr_le' (x := x) (g := g) hD fr
  have hp := hostData'_p_le x g hD
  have hm := hostData'_m_le hbig
  have hlay : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    { space := hok.space
      fr := by change aFr (hostData' x D g) x.U fr < lim.space; omega
      prime := by omega
      count := le_word_of_le_hostWord hok0 (hm.trans (by unfold hostWord; omega))
      step := le_word_of_le_hostWord hok0 (by change x.n + pieceSizeNat D g ≤ _; unfold hostWord; omega)
      weights := le_word_of_le_hostWord hok0
      depth := by omega
      solver := fun t ht => by
        have hmem := Finset.mem_range.2 (Nat.lt_succ_of_le ((hostData' x D g).w_le_cap ht))
        have hsword : (need [x.n, midSize D g, (hostData' x D g).w t]).word
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).word :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).word) hmem
        have hscells : (need [x.n, midSize D g, (hostData' x D g).w t]).cells
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).cells) hmem
        have hsdepth : (need [x.n, midSize D g, (hostData' x D g).w t]).depth
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).depth :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).depth) hmem
        change (need [x.n, midSize D g, (hostData' x D g).w t]).Ok lim
          (aFr (hostData' x D g) x.U fr) (d + 1 + 1)
        exact ⟨le_trans (Nat.cast_le.2 (hsword.trans (Nat.le_add_left _ _))) hword, by omega,
          hok.space, by omega⟩ }

theorem et17Params_spec' {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}
    (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  replace hok : (hostNeed Dfun Gfun wD wG (fun ps => need (midArgs Gfun ps)) x.n x.U).Ok lim fr d :=
    hok
  unfold hostNeed at hok
  have hdepth := hok.depth; simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *; generalize hg : Gfun D = g at *
  have hwD : ((wD x.n : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : ((wG D : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : ((3 * D + 4 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have h16 : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  light_call (C.dProc lim d x.n μ hn hok.space hwD (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hD]
  light_call (C.gProc lim d D μ hDpos hok.space hwG (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hg]
  light_call (sqrt_meets (K := D) C.hSqrt μ hsqrt) with _ μ ⟨rfl, rfl⟩
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]

theorem et17Sizes_spec' {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}
    (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ)
    (hpre : x.Pre μ fr) (hbig : BigCase x.n D g)
    (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Sizes' ν) ⟨frame (et17LocA x fr D g), μ⟩
      (chooseTime x.n x.U D + tQueryCapNat x.n D + tCeilDiv (Nat.sqrt D) g +
        tCeilDiv x.n (pieceSizeNat D g) + tBitLen x.U + 120)
      fun σ' => ∃ μ', σ' = ⟨frame (et17LocB' x fr D g), μ'⟩ ∧ Kept μ μ' fr := by
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hr := sizesReady_of (x := x) hbig hok0
  have hdepth := hr.depth
  have htop : aFr (hostData' x D g) x.U fr ≤ lim.space := by
    have := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
    have hcells := hok.cells; simp  [hostNeedAt'] at hcells; omega
  have hmid : ((midSize D g : ℕ) : ℤ) = ((Nat.sqrt D ⌈/⌉ g : ℕ) : ℤ) * (Nat.sqrt D : ℤ) := by
    rfl
  have hmidWord : ((midSize D g : ℕ) : ℤ) ≤ lim.word :=
    le_word_of_le_hostWord hok0 ((midSize_le D g).trans (by unfold hostWord; omega))
  unfold et17Sizes' et17LocA
  rw [ite_eq_right (not_smallCase_iff.2 hbig)]
  light_call (choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok0)) with _ μ₁ ⟨rfl, hμ₁⟩
  light_call (queryCapNat_meets C.hCap hr.one_le_D hr.wordCap) with _ μ₁ ⟨rfl, rfl⟩
  light_call (ceilDiv_meets C.hCeil hr.one_le_g hr.wordPiece) with _ μ₁ ⟨rfl, rfl⟩
  light_call (ceilDiv_meets C.hCeil hr.one_le_piece hr.wordPieces) using pieceSizeNat
    with _ μ₁ ⟨rfl, rfl⟩
  light_call (bitLen_meets C.hBitLen hr.wordBits) with _ μ₁ ⟨rfl, rfl⟩
  light_set (midSize D g : ℕ) using hmid
  refine (et17Addr_spec x (hostData' x D g) hok.space htop).mono (by simp [et17Addr]; omega) ?_
  rintro _ rfl
  exact ⟨μ₁, rfl, fun c hc => hμ₁ c (Or.inl hc)⟩

theorem ready_of' {lim : Limits} {d : ℕ} {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}
    {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Et17.Ready lim d x (hostData' x D g) μ fr := by
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hr := Et17.ready_of hpre hbig hok0
  have := aFr_le' (x := x) (g := g) hbig.sixteen_le fr
  have hcells := hok.cells; simp  [hostNeedAt'] at hcells
  exact ⟨hr.space, hr.depth, hr.prime, hr.word, by omega, hr.segAB, hr.segBC, hr.segAC,
    hr.lenAB, hr.lenBC, hr.lenAC, hr.leAB, hr.leBC, hr.leAC, hr.belowAB, hr.belowBC, hr.belowAC⟩

theorem tWrites_le (n : ℕ) {D D' a b : ℕ} (hD : D ≤ D') (h : a ≤ b) :
    tWrites n D a ≤ tWrites n D' b := by
  unfold tWrites tWriteX tWriteY; gcongr

theorem sum_le_mul_add {m M A B E : ℕ} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos; have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]; omega
  exact Nat.le_mul_of_pos_left _ hpieces

def et17Procs' (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody, scanBody, .skip, primesBody ν.ch.pSqrt ν.ch.pSieve, bitLenBody, dblTableBody,
    residBody, residuesBody ν.pResid, spreadTableBody, szTableBody, buildZBody, countZeroBody,
    vlinBody, cconvBody, fillBody, phaseBody ν.ch.cp.str, strBody ν.ch.cp.str,
    countPrimeBody ν.ch.cp, choosePrimeBody ν.ch, queryCapNatBody, ceilDivBody, classesBody,
    chunksBody, writeXBody, writeYBody, .skip, .skip, .skip, sieveBody]

theorem et17Ctx_assembled' {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs' pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun
      Gfun tD tG wD wG := by
  have L : ∀ {i : ℕ} {body : Stmt}, (et17Procs' pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs' pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact ⟨⟨hsol, L rfl, L rfl, L rfl⟩, L (i := 0) rfl, L rfl,
    ⟨L rfl, L rfl, L rfl, ⟨L rfl, L rfl, L rfl, L rfl, L rfl, L rfl, L rfl,
      ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩, ⟨L (i := 0) rfl, L rfl⟩⟩,
    L rfl, L rfl, L rfl, L rfl, L rfl, L rfl, L rfl, L rfl, hD _, hG _, hpos⟩

theorem hostNeed_poly' {Dfun Gfun wD wG : ℕ → ℕ} {need : List ℕ → Need}
    (hD : PolyBounded fun n _ => Dfun n) (hG : PolyBounded fun n _ => Gfun (Dfun n))
    (hwD : PolyBounded fun n _ => wD n) (hwG : PolyBounded fun n _ => wG (Dfun n))
    (h : PolyNeedN need) : PolyNeed (hostNeed' Dfun Gfun wD wG need) :=
  hostNeed_poly hD hG hwD hwG (polyNeedN_midArgs Gfun h)

def Claim17Mid (M : DetTimeModel) (MM : ℕ → ℝ) (D g : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ 4 * (n : ℝ) * (g n : ℝ) *
            (T n (midSize (D n) (g n)) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
          C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

noncomputable def bound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ) (n : ℕ)
    (κ : ℝ) : ℝ :=
  4 * (n : ℝ) * (g n : ℝ) *
      (T n (midSize (D n) (g n)) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
    C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

def ObeysBound17Mid (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Tn : List ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℝ),
    (∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' → (Tn [m, d, w] : ℝ) ≤ T m d w') →
    ∀ (n U : ℕ) (κ : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
      (U : ℝ) ≤ (n : ℝ) ^ κ → (time Tn n U : ℝ) ≤ bound17Mid MM D g C T n κ

theorem obeysBound17Mid_hostTime (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17Mid strassen D g (hostTime' Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hbound⟩ := obeysBound17_hostTime D g hDf hGf hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  let T' : ℕ → ℕ → ℕ → ℝ := fun m d w =>
    if 1 ≤ midSize d (Gfun d) then T m (midSize d (Gfun d)) w
    else (((Finset.range (w + 1)).sup fun v => Tn [m, midSize d (Gfun d), v] : ℕ) : ℝ)
  have hT' : ∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' →
      ((Tn (midArgs Gfun [m, d, w]) : ℕ) : ℝ) ≤ T' m d w' := by
    intro m d w w' hm _ hw
    by_cases hmid : 1 ≤ midSize d (Gfun d)
    · simp  [T', ite_eq_left hmid]; exact hT m _ w w' hm hmid hw
    · simp  [T', ite_eq_right hmid]
      exact_mod_cast Finset.le_sup (f := fun v => Tn [m, midSize d (Gfun d), v])
        (Finset.mem_range.2 (by omega))
  have hn1 : 1 ≤ n := by omega
  have hmid : 1 ≤ midSize (D n) (g n) := one_le_midSize h16 hg1
  have h := hbound (fun ps => Tn (midArgs Gfun ps)) T' hT' n U κ h16 hDn hg1 hg hκ hU
  rw [hostTime'_eq]
  exact h.trans_eq (by simp  [bound17, bound17Mid, T', hGf n hn1, ite_eq_left hmid])

end ImprovedExponents.HostMid
