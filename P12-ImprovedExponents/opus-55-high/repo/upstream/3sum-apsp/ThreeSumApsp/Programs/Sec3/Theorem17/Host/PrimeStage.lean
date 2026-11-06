/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the prime, the sizes, the addresses

This file proves the specification of the second part of the host procedure `et17` (Exact Triangle
by Theorem 17), which chooses the prime and computes the sizes and the addresses of the arrays:
five calls (`et17Sizes_spec`) and then seventeen assignments (`et17Addr_spec`).
-/


namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

variable {fr : ℕ}

/-- **The sizes and the addresses.**  Of the locals that are set before, only Size, Free, ParD,
ThePrime, Cap and Bits are read. -/
theorem et17Addr_spec {μ : ℕ → ℤ} (x : TriInst) (X : HostData) {g s : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (htop : aFr X x.U fr ≤ lim.space) :
    Ends lim P d et17Addr
      ⟨frame [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s,
        (X.p : ℤ), (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], μ⟩
      et17Addr.blockCost fun σ' => σ' = ⟨frame (Et17.locals x X fr g s 0 0), μ⟩ := by
  have hplaces := host_places X x.U fr
  unfold et17Addr
  -- SizeSq := Size * Size ; Area := Size * ParD ; Room := SizeSq + ThePrime
  light_set (X.n * X.n)
  light_set (X.n * X.D)
  light_set (X.n * X.n + X.p)
  -- ResAB := Free + (Bits + 1) ; ResBC := ResAB + SizeSq ; ResAC := ResBC + SizeSq
  light_set (aRab X x.U fr)
  light_set (aRbc X x.U fr)
  light_set (aRac X x.U fr)
  -- Cls := ResAC + SizeSq ; Cur := Cls + (ThePrime + 1) ; Rows := Cur + ThePrime
  light_set (aCls X x.U fr)
  light_set (aCur X x.U fr)
  light_set (aQi X x.U fr)
  -- Cols := Rows + SizeSq ; TabR := Cols + SizeSq ; TabL := TabR + Room ; TabW := TabL + Room
  light_set (aQj X x.U fr)
  light_set (aCr X x.U fr)
  light_set (aCl X x.U fr)
  light_set (aCw X x.U fr)
  -- MatX := TabW + Room ; MatY := MatX + Area ; AdrOut := MatY + Area
  light_set (aX X x.U fr)
  light_set (aY X x.U fr)
  light_set (aOut X x.U fr)
  -- SolverFree := AdrOut + Cap
  light_set (aFr X x.U fr)
  rfl

/-- What the second part uses: the parameters are not small, and the limits allow for one more
level of calls, for the arrays and for the numbers that the four small procedures form. -/
structure SizesReady (lim : Limits) (d : ℕ) (x : TriInst) (fr D g : ℕ) : Prop where
  one_le_D : 1 ≤ D
  one_le_g : 1 ≤ g
  one_le_piece : 1 ≤ pieceSizeNat D g
  depth : d < lim.depth
  top : aFr (hostData x D g) x.U fr ≤ lim.space
  wordCap : ((4 * x.n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word
  wordPiece : ((Nat.sqrt D + g + 1 : ℕ) : ℤ) ≤ lim.word
  wordPieces : ((x.n + pieceSizeNat D g + 1 : ℕ) : ℤ) ≤ lim.word
  wordBits : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word

variable {need : List ℕ → Need}

/-- The need of the host provides what the second part uses. -/
theorem sizesReady_of {x : TriInst} {D g a b : ℕ}
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    SizesReady lim d x fr D g := by
  have hD16 := hbig.sixteen_le
  have hg1 := hbig.one_le_g
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hdepth := hok.depth
  have hcells := hok.cells
  have htop := aFr_le (x := x) (g := g) hD16 fr
  simp [hostNeedAt] at hdepth hcells
  exact
    ⟨by omega, hg1, (Nat.lt_ceilDiv_iff hg1).2 (by omega), by omega, by omega, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok, le_word_of_le_hostWord hok⟩

