/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the prime, the sizes, the addresses

This file proves the specification of the second part of the host procedure `et17` (Exact Triangle
by Theorem 17), which chooses the prime and computes the sizes and the addresses of the arrays:
five calls (`et17Sizes_spec`) and then seventeen assignments (`et17Addr_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- **The sizes and the addresses.**  Of the locals that are set before, only Size, Free, ParD,
ThePrime, Cap and Bits are read. -/
theorem et17Addr_spec {μ} x X {fr} {g s}
    (hw : (lim.space : ℤ) ≤ lim.word) (htop : aFr X x.U fr ≤ lim.space) :
    Ends lim P d et17Addr
      ⟨frame [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s,
        (X.p : ℤ), (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], μ⟩
      et17Addr.blockCost fun σ' => σ' = ⟨frame (Et17.locals x X fr g s 0 0), μ⟩ := by
  have  := host_places X x.U fr
  unfold et17Addr
  -- SizeSq := Size * Size ; Area := Size * ParD ; Room := SizeSq + ThePrime
  light_set (X.n * X.n : ℕ)
  light_set (X.n * X.D : ℕ)
  light_set (X.n * X.n + X.p : ℕ)
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
  wordCap : ((4 * x.n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word
  wordPiece : ((Nat.sqrt D + g + 1 : ℕ) : ℤ) ≤ lim.word
  wordPieces : ((x.n + pieceSizeNat D g + 1 : ℕ) : ℤ) ≤ lim.word
  wordBits : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word

/-- The need of the host provides what the second part uses. -/
theorem sizesReady_of {need} {x} {fr D g a b}
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    SizesReady lim d x fr D g := by
  have hD16 := hbig.sixteen_le
  have hg1 := hbig.one_le_g
  have  : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 hD16
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  exact
    { one_le_D := by omega
      one_le_g := hg1
      one_le_piece := (Nat.lt_ceilDiv_iff hg1).2 (by omega)
      depth := by omega
      wordCap := le_word_of_le_hostWord hok
      wordPiece := le_word_of_le_hostWord hok
      wordPieces := le_word_of_le_hostWord hok
      wordBits := le_word_of_le_hostWord hok }

end Light.Sec3
