/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceCount
import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text

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


namespace Light.Sec3

open ThreeSumApsp.Spec

variable {n g D : ℕ}

/-! ## The case that n is not small -/

/-- The host falls back on the brute force exactly if the hypotheses of Theorem 17 fail. -/
theorem not_smallCase_iff : ¬ SmallCase n D g ↔ BigCase n D g := by
  unfold SmallCase
  exact ⟨fun h => ⟨by omega, by omega, by omega, by omega⟩,
    fun ⟨_, _, _, _⟩ => by omega⟩

/-- The chosen prime is at most √D. -/
theorem hostData_p_le (x : TriInst) (g : ℕ) (hD : 16 ≤ D) :
    (hostData x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

/-- The chosen prime is at least 2. -/
theorem two_le_hostData_p (x : TriInst) (g : ℕ) (hD : 16 ≤ D) : 2 ≤ (hostData x D g).p :=
  two_le_chosenPrime x.AB x.BC x.AC hD

variable {x : TriInst}

/-- There are at most `4ng` instances. -/
theorem hostData_m_le (h : BigCase x.n D g) :
    (hostData x D g).m ≤ 4 * x.n * g :=
  HostData.m_le h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le)

variable {μ : ℕ → ℤ} {fr : ℕ}

/-- The data of a run are valid. -/
theorem hostData_valid (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData x D g).Valid :=
  HostData.valid_of_params h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le) hpre.lenAB hpre.lenBC
    hpre.lenAC

/-! ## The addresses -/

/-- The free pointer of the solver, written out. -/
theorem aFr_eq (X : HostData) (U fr : ℕ) :
    aFr X U fr = fr + (bitLen U + 1) + 3 * (X.n * X.n) + (X.p + 1) + X.p + 2 * (X.n * X.n)
      + 3 * (X.n * X.n + X.p) + 2 * (X.n * X.D) + X.cap := by
  simp [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab]
  omega

/-- The arrays of et17 fit into the cells that hostLayout counts. -/
theorem aFr_le (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  grind [hostData_p_le, aFr_eq, hostLayout, bitLen, hostData, queryCapNat]

variable {lim : Limits} {a b d U : ℕ} {need : List ℕ → Need}

/-! ## The words -/

/-- The numbers of the host fit in a word. -/
theorem hostWord_le     (hok : (hostNeedAt a b need n U D g).Ok lim fr d) :
    ((hostWord a b n U D g : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast Nat.le_add_right _ _) hok.word

/-- A number that is at most hostWord fits in a word. -/
theorem le_word_of_le_hostWord     (hok : (hostNeedAt a b need n U D g).Ok lim fr d) {z : ℕ}
    (hz : z ≤ hostWord a b n U D g := by unfold hostWord; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by omega) (hostWord_le hok)

/-- What choosePrime needs. -/
theorem choosePre_of_ok     (hpre : x.Pre μ fr) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    ChoosePrimePre lim (d + 1) μ x D fr := by
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n D _).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8 + (supNeed need x.n D _).depth)
      ≤ lim.depth := hok.depth
  exact
    ⟨hok.space, hpre, by omega, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, by omega⟩


