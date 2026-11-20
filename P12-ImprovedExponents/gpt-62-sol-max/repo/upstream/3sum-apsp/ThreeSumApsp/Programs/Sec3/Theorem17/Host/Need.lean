/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Tactics

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceCount
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text

/-!
# The host of Theorem 17: the limits

The host procedure `et17` (Exact Triangle by Theorem 17) states what it needs of the limits of a
run: word size, memory, depth of calls (`hostNeedAt`).  This file shows that this need covers what
the procedures that it calls ask for.

* The arrays of the host lie one behind the other and fit into the cells that `hostLayout` counts
  (`aFr_le`).
* Every number that is at most `hostWord` fits in a word (`le_word_of_le_hostWord`).
* So the preconditions of the choice of the prime and of the loop over the instances hold
  (`choosePre_of_ok`, `hostLim_of_ok`).  For the solver this uses that an instance has at most
  `⌊n²/√D⌋` query pairs (`HostData.w_le_cap`, `need_le_supNeed`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The case that n is not small -/

/-- The host falls back on the brute force exactly if the hypotheses of Theorem 17 fail. -/
theorem not_smallCase_iff {n D g : ℕ} : ¬ SmallCase n D g ↔ BigCase n D g := by
  unfold SmallCase
  exact ⟨fun h => ⟨by omega, by omega, by omega, by omega⟩,
    fun ⟨_, _, _, _⟩ => by omega⟩

/-- The chosen prime is at most √D. -/
theorem hostData_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

/-- The chosen prime is at least 2. -/
theorem two_le_hostData_p (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) : 2 ≤ (hostData x D g).p :=
  two_le_chosenPrime x.AB x.BC x.AC hD

/-- There are at most `4ng` instances. -/
theorem hostData_m_le {x : TriInst} {D g : ℕ} (h : BigCase x.n D g) :
    (hostData x D g).m ≤ 4 * x.n * g :=
  HostData.m_le (AB := x.AB) (BC := x.BC) (AC := x.AC) h
    (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le)

/-- The data of a run are valid. -/
theorem hostData_valid {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData x D g).Valid :=
  HostData.valid_of_params h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le) hpre.arrAB.len hpre.arrBC.len
    hpre.arrAC.len (Nat.mul_le_mul_left _ (hostData_p_le x g h.sixteen_le))

/-! ## The addresses -/

/-- The arrays fit into the cells that upstream's `hostLayout` counts. -/
theorem aFr_le {x : TriInst} {D g : ℕ} (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have hp : chosenPrime x.n D x.AB x.BC x.AC ≤ Nat.sqrt D := chosenPrime_le_sqrt x.AB x.BC x.AC hD
  have hmid : x.n * midSize D g ≤ x.n * D := Nat.mul_le_mul_left _ (midSize_le D g)
  simp only [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, hostData, hostLayout,
    ResidueTables.top, ResidueTables.rac, ResidueTables.rbc, ResidueTables.rab]
  omega

/-! ## The words -/

/-- The numbers of the host fit in a word. -/
private theorem hostWord_le {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) :
    ((hostWord a b n U D g : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast Nat.le_add_right _ _) hok.word

/-- A number that is at most hostWord fits in a word. -/
theorem le_word_of_le_hostWord {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) {z : ℕ}
    (hz : z ≤ hostWord a b n U D g := by unfold hostWord; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hz) (hostWord_le hok)

/-- What choosePrime needs. -/
theorem choosePre_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst} {μ : ℕ → ℤ}
    {fr D g : ℕ} (hpre : x.Pre μ fr) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    ChoosePrimePre lim (d + 1) μ x D fr := by
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [hostNeedAt] at hcells hdepth
  exact
    { space_le := hok.space
      inst := hpre
      cells := by omega
      wordD := le_word_of_le_hostWord hok
      wordU := le_word_of_le_hostWord hok
      wordN := le_word_of_le_hostWord hok
      wordDbl := le_word_of_le_hostWord hok
      wordStr := le_word_of_le_hostWord hok
      wordSum := le_word_of_le_hostWord hok
      depth := by omega }

/-- The dimensions, workspace and call depth provided to the loop and its solver. -/
theorem hostLim_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst}
    {fr D g : ℕ} (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData x D g) x.U (hostAddr x (hostData x D g) fr) need := by
  have hfr := aFr_le (x := x) (g := g) hbig.sixteen_le fr
  have hp := hostData_p_le x g hbig.sixteen_le
  have hm := hostData_m_le (x := x) hbig
  have hcells := hok.cells
  have hdepth := hok.depth
  have hword := hok.word
  simp only [hostNeedAt, supNeed] at hcells hdepth hword
  have hlay : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  refine ⟨hok.space, ?_, by omega,
    le_word_of_le_hostWord hok (hm.trans (by unfold hostWord; omega)),
    le_word_of_le_hostWord hok (z := x.n + pieceSizeNat D g), le_word_of_le_hostWord hok,
    by omega, ?_⟩
  · change aFr (hostData x D g) x.U fr + x.n * x.n < lim.space
    omega
  · intro t ht
    let w := (hostData x D g).w t
    have hw : w ≤ queryCapNat x.n D := (hostData x D g).w_le_cap ht
    have hsup (f : Need → ℕ) : f (need [x.n, midSize D g, w]) ≤
        (Finset.range (queryCapNat x.n D + 1)).sup (fun v => f (need [x.n, midSize D g, v])) :=
      Finset.le_sup (f := fun v => f (need [x.n, midSize D g, v]))
        (Finset.mem_range.2 (by omega : w < queryCapNat x.n D + 1))
    have hw' := Nat.cast_le (α := ℤ) |>.2 (hsup Need.word)
    have hc' := hsup Need.cells
    have hd' := hsup Need.depth
    change (need [x.n, midSize D g, w]).Ok lim
      (aFr (hostData x D g) x.U fr + x.n * x.n) (d + 1 + 1)
    push_cast at hword
    exact ⟨by omega, by omega, hok.space, by omega⟩

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- **The first part of et17**, within the limits of the variant: the parameters, and whether n is
small.  No cell changes. -/
theorem et17Params_spec (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.
  have hwD : ((wD x.n : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : ((wG D : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : ((3 * D + 4 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have h16 : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
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
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]


end Light.Sec3
