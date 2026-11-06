
import ImprovedExponents.HostMid.Defs


/-!
# The variant host: the data of a run, the limits, the first part

For the host with the inner dimension `midSize D g` this file proves what upstream proves for its
host in `Host/Need.lean` and `Host/ParametersStage.lean`: the data of a run are valid
(`hostData'_valid`; this is where `q p ≤ q ⌊√D⌋` is used), the arrays fit (`aFr_le'`), the limits
cover what the loop over the instances asks for (`hostLim_of_ok'`), and the first part and the
small case behave as upstream's (`et17Params_spec'`, `et17Small_spec'`).
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp.Spec

variable {D : ℕ}

/-! ## The data of a run -/

/-- The chosen prime is at most √D. -/
theorem hostData'_p_le (x : TriInst) (g : ℕ) (hD : 16 ≤ D) :
    (hostData' x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

variable {x : TriInst} {g : ℕ}

/-- There are at most `4ng` instances: the number of instances does not depend on the inner
dimension. -/
theorem hostData'_m_le (h : BigCase x.n D g) :
    (hostData' x D g).m ≤ 4 * x.n * g :=
  hostData_m_le h

variable {fr : ℕ}

/-- The data of a run are valid: the middle part `piece × ℤ_p` of an instance has at most
`q p ≤ q ⌊√D⌋ = midSize D g` vertices. -/
theorem hostData'_valid {μ : ℕ → ℤ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData' x D g).Valid :=
  have hv := hostData_valid hpre h
  ⟨hv.n_pos, hv.p_pos, hv.q_pos, hv.cap_pos, Nat.mul_le_mul_left _ (hostData'_p_le x g h.sixteen_le), hv.lenAB, hv.lenBC, hv.lenAC⟩

/-! ## The addresses -/

/-- The arrays of the variant fit into the cells that upstream's `hostLayout` counts. -/
theorem aFr_le' (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData' x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have hp : chosenPrime x.n D x.AB x.BC x.AC ≤ Nat.sqrt D := chosenPrime_le_sqrt x.AB x.BC x.AC hD
  have hmid : x.n * midSize D g ≤ x.n * D := Nat.mul_le_mul_left _ (midSize_le D g)
  simp [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab, hostData']
  unfold hostLayout
  omega

/-! ## The limits -/

/-- What hostLoop asks of the limits. -/
theorem hostLim_of_ok' {lim : Limits} {d a b : ℕ} {need : List ℕ → Need}
    (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData' x D g) x.U (hostAddr x (hostData' x D g) fr) need := by
  have hD := hbig.sixteen_le
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n _ _).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8
      + (supNeed need x.n _ _).depth) ≤ lim.depth := hok.depth
  have hword : hostWord a b x.n x.U D g
      + (supNeed need x.n _ _).word ≤ lim.word := hok.word
  have hfr := aFr_le' (x := x) (g := g) hD fr
  have hp := hostData'_p_le x g hD
  have hm := hostData'_m_le hbig
  have hlay : 2 * D.sqrt ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    ⟨hok.space, by change aFr _ x.U fr < lim.space; omega, by omega, by grind [hostWord], le_word_of_le_hostWord hok0 (by
        change x.n + pieceSizeNat D g ≤ _
        unfold hostWord
        omega), le_word_of_le_hostWord hok0, by omega, fun t ht => by
        have hwc : (hostData' x D g).w t ≤ queryCapNat x.n D := (hostData' x D g).w_le_cap ht
        have hmem : (hostData' x D g).w t ∈ Finset.range (queryCapNat x.n D + 1) :=
          by simp_all
        have hsword : (need _).word
            ≤ (supNeed need x.n _ _).word :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).word) hmem
        have hscells : (need _).cells
            ≤ (supNeed need x.n _ _).cells :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).cells) hmem
        have hsdepth : (need _).depth
            ≤ (supNeed need x.n _ _).depth :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).depth) hmem
        change (need [x.n, midSize D g, (hostData' x D g).w t]).Ok lim
          (aFr (hostData' x D g) x.U fr) _
        exact ⟨by omega, by omega,
          hok.space, by omega⟩⟩

/-! ## The first part and the small case -/

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean
/-- **The first part of et17**, within the limits of the variant: the parameters, and whether n is
small.  No cell changes. -/
theorem et17Params_spec' (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  replace hok : (hostNeed Dfun Gfun wD wG (fun ps => need (midArgs Gfun ps)) x.n x.U).Ok lim fr d :=
    hok
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.
  have hwD : wD x.n ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : wG D ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : (3 * D + 4 : ℕ) ≤ lim.word := le_word_of_le_hostWord hok
  have h16 : (16 : ℕ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  -- D := Dfun(n); g := Gfun(D)
  light_call (C.dProc lim d x.n μ hn hok.space hwD (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hD]
  light_call (C.gProc lim d D μ hDpos hok.space hwG (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hg]
  -- s := sqrt(D)
  light_call (sqrt_meets (K := D) C.hSqrt μ hsqrt) with _ μ ⟨rfl, rfl⟩
  -- the four tests: D < 16, n < D, g < 1, s < g
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : D.sqrt < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean
open Et17 in
/-- **The small case**, within the limits of the variant: the call of the brute force. -/
theorem et17Small_spec' (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (.call ν.pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
      ⟨frame (et17LocA x fr D g), μ⟩ (tBrute x.n + 8)
      fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok.mono (by grind [bruteNeed, hostNeedAt', hostWord])
      (by grind [bruteNeed]) (by grind [bruteNeed, hostNeedAt'])
  have hdepth := hok.depth
  simp [hostNeedAt'] at hdepth
  refine Ends.callTo (brute_meets C.hBrute C.loop.scan x μ fr hpre hbrute) ?_ (by aesop)
  rintro _ _ ⟨rfl, rfl⟩
  tauto
