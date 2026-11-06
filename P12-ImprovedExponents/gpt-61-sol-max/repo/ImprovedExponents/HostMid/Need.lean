module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ImprovedExponents.HostMid.Defs

@[expose] public section

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

/-! ## The data of a run -/

/-- The chosen prime is at most √D. -/
theorem hostData'_p_le x {D} g (hD : 16 ≤ D) :
    (hostData' x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

/-- There are at most `4ng` instances: the number of instances does not depend on the inner
dimension. -/
def hostData'_m_le {x : TriInst} {D g} (h : BigCase x.n D g) :=
  hostData_m_le h

/-- The data of a run are valid: the middle part `piece × ℤ_p` of an instance has at most
`q p ≤ q ⌊√D⌋ = midSize D g` vertices. -/
theorem hostData'_valid {x} {μ} {fr D g} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData' x D g).Valid :=

  { (hostData_valid hpre h) with
    qp_le := Nat.mul_le_mul_left _ (hostData'_p_le x g h.sixteen_le)}

/-! ## The addresses -/

/-- The arrays of the variant fit into the cells that upstream's `hostLayout` counts. -/
theorem aFr_le' {x} {D g} (hD : 16 ≤ D) fr :
    aFr (hostData' x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have  : chosenPrime x.n D x.AB x.BC x.AC ≤ Nat.sqrt D := chosenPrime_le_sqrt x.AB x.BC x.AC hD
  have  : x.n * midSize D g ≤ x.n * D := Nat.mul_le_mul_left _ (midSize_le D g)
  ram_safe [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab, hostData', hostLayout]

/-! ## The limits -/

/-- What hostLoop asks of the limits. -/
theorem hostLim_of_ok' {lim} {d a b} {need} {x}
    {fr D g} (hbig : BigCase x.n D g) (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData' x D g) x.U (hostAddr x (hostData' x D g) fr) need := by
  have hD := hbig.sixteen_le
  have hok0 : (hostNeedAt a b (fun ps => need (midArgs (fun _ => g) ps)) x.n x.U D g).Ok lim fr d :=
    hok
  have  : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have  : d + (2 * Nat.clog 2 x.n + 8
      + (supNeed need x.n (midSize D g) (queryCapNat x.n D)).depth) ≤ lim.depth := hok.depth

  have  := aFr_le' (x := x) (g := g) hD fr
  have  := hostData'_p_le x g hD

  have  : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    { space := hok.space
      fr := by change aFr (hostData' x D g) x.U fr < lim.space; omega
      prime := by omega
      count := le_word_of_le_hostWord hok0 ((hostData'_m_le hbig).trans (by unfold hostWord; omega))
      step := le_word_of_le_hostWord hok0 (by
        change x.n + pieceSizeNat D g ≤ _
        unfold hostWord
        omega)
      weights := le_word_of_le_hostWord hok0
      depth := by omega
      solver := fun t ht => by
        have  : (hostData' x D g).w t ≤ queryCapNat x.n D := (hostData' x D g).w_le_cap ht
        have hmem : (hostData' x D g).w t ∈ Finset.range (queryCapNat x.n D + 1) :=
          Finset.mem_range.2 (by omega)
        have hsword :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).word) hmem
        have  : (need [x.n, midSize D g, (hostData' x D g).w t]).cells
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).cells :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).cells) hmem
        have  : (need [x.n, midSize D g, (hostData' x D g).w t]).depth
            ≤ (supNeed need x.n (midSize D g) (queryCapNat x.n D)).depth :=
          Finset.le_sup (f := fun v => (need [x.n, midSize D g, v]).depth) hmem
        change (need [x.n, midSize D g, (hostData' x D g).w t]).Ok lim
          (aFr (hostData' x D g) x.U fr) (d + 1 + 1)
        exact ⟨le_trans (Nat.cast_le.2 (hsword.trans (Nat.le_add_left _ _))) hok.word, by omega,
          hok.space, by omega⟩ }

/-! ## The first part and the small case -/

variable {P₀ R : Program} {ν : Et17Nums} {Tn : Light.InputTime} {need : Light.InputNeed}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean
variable (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)

include C in
/-- **The first part of et17**, within the limits of the variant: the parameters, and whether n is
small.  No cell changes. -/
theorem et17Params_spec'  x
     μ fr (hpre : x.Pre μ fr)
    (hok : (hostNeed' Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + 18 * Nat.sqrt (Dfun x.n) + 12 + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  replace hok : (hostNeed Dfun Gfun wD wG (fun ps => need (midArgs Gfun ps)) x.n x.U).Ok lim fr d :=
    hok
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.



  have  : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  -- D := Dfun(n); g := Gfun(D)
  light_call (C.dProc lim d x.n μ hn hok.space (le_word_of_le_hostWord hok) (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hD]
  light_call (C.gProc lim d D μ hDpos hok.space (le_word_of_le_hostWord hok) (by omega)) with _ μ ⟨rfl, rfl⟩
  rw [hg]
  -- s := sqrt(D)
  light_call (sqrt_meets (K := D) C.hSqrt μ (le_word_of_le_hostWord hok)) with _ μ ⟨rfl, rfl⟩
  -- the four tests: D < 16, n < D, g < 1, s < g
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/ParametersStage.lean

include C in
/-- **The small case**, within the limits of the variant: the call of the brute force. -/
theorem et17Small_spec'  (x )
    (μ ) (fr D g a b ) (hpre : x.Pre μ fr)
    (hok : (hostNeedAt' a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (.call ν.pBrute [v 0, v 1, v 2, v 3, v 4, v 5] 0)
      ⟨frame (et17LocA x fr D g), μ⟩ (tBrute x.n + 8)
      fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok.mono (by grind [bruteNeed, hostNeedAt', hostWord])
      (by simp only [bruteNeed]; omega) (by grind [bruteNeed, hostNeedAt'])
  have hdepth := hok.depth
  simp only [hostNeedAt'] at hdepth
  refine Ends.callTo (brute_meets C.hBrute C.loop.scan x μ fr hpre hbrute) ?_ (by simp [et17LocA])
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨rfl, fun _ _ => rfl⟩

end ImprovedExponents.HostMid
