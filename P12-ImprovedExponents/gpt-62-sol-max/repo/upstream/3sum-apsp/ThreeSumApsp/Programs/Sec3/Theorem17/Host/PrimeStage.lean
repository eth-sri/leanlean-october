/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the prime, the sizes, the addresses

This file proves the specification of the second part of the host procedure `et17` (Exact Triangle
by Theorem 17), which chooses the prime and computes the sizes and the addresses of the arrays:
five calls followed by the address assignments (`et17Sizes_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- **The sizes and the addresses.**  Of the locals that are set before, only Size, Free, ParD,
ThePrime, Cap and Bits are read. -/
theorem et17Addr_spec {μ : ℕ → ℤ} (x : TriInst) (X : HostData) {fr : ℕ} {g s : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (htop : aFr X x.U fr ≤ lim.space) :
    Ends lim P d et17Addr
      ⟨frame [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.p : ℤ),
          ((bitLen x.U : ℕ) : ℤ), (X.D : ℤ), 0, 0, 0, 0, 0, 0, g, s, (X.cap : ℤ), (X.q : ℤ),
          (X.h : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], μ⟩
      et17Addr.blockCost fun σ' => σ' = ⟨frame (Et17.locals x X fr g s 0 0), μ⟩ := by
  have hplaces := host_places X x.U fr
  unfold et17Addr ResidueTables.addresses
  -- SizeSq := Size * Size ; Area := Size * ParD ; Room := SizeSq + ThePrime
  light_steps
  rfl

/-- **The second part of the variant**: the prime, the sizes and the addresses are in the locals,
and `ParD` holds `midSize D g`; only cells from the free pointer on have changed. -/
theorem et17Sizes_spec {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Sizes ν) ⟨frame (et17LocA x fr D g), μ⟩
      (chooseTime x.n x.U D + tQueryCapNat x.n D + tCeilDiv (Nat.sqrt D) g +
        tCeilDiv x.n (pieceSizeNat D g) + tBitLen x.U + 120)
      fun σ' => ∃ μ', σ' = ⟨frame (et17LocB x fr D g), μ'⟩ ∧ Kept μ μ' fr := by
  have hw := hok.space
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [hostNeedAt] at hcells hdepth
  have hD16 := hbig.sixteen_le
  have hg1 := hbig.one_le_g
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hpiece : 1 ≤ pieceSizeNat D g := (Nat.lt_ceilDiv_iff hg1).2 (by omega)
  have htop : aFr (hostData x D g) x.U fr ≤ lim.space := (aFr_le hD16 fr).trans (by omega)
  -- The new inner dimension is at most `D`, so it fits in a word.
  have hmid : ((midSize D g : ℕ) : ℤ) = ((Nat.sqrt D ⌈/⌉ g : ℕ) : ℤ) * (Nat.sqrt D : ℤ) := by
    rfl
  have hmidWord : ((midSize D g : ℕ) : ℤ) ≤ lim.word :=
    le_word_of_le_hostWord hok ((midSize_le D g).trans (by unfold hostWord; omega))
  unfold et17Sizes et17LocA
  rw [ite_eq_right (not_smallCase_iff.2 hbig)]
  -- ThePrime := pChoose(Size, Bound, AdrAB, AdrBC, AdrAC, ParD, Free)
  light_call (choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok)) with _ μ₁ ⟨rfl, hμ₁⟩
  -- Cap := pCap(Size, ParD)
  light_call (queryCapNat_meets (n := x.n) (D := D) C.hCap (by omega) (le_word_of_le_hostWord hok)) with _ μ₁ ⟨rfl, rfl⟩
  -- PieceLen := pCeil(RootD, ParG)
  light_call (ceilDiv_meets (a := Nat.sqrt D) C.hCeil hg1 (le_word_of_le_hostWord hok)) with _ μ₁ ⟨rfl, rfl⟩
  -- NumPieces := pCeil(Size, PieceLen)
  light_call (ceilDiv_meets (a := x.n) C.hCeil hpiece (le_word_of_le_hostWord hok)) using pieceSizeNat
    with _ μ₁ ⟨rfl, rfl⟩
  -- Bits := pBitLen(Bound)
  light_call (bitLen_meets (U := x.U) C.hBitLen (le_word_of_le_hostWord hok)) with _ μ₁ ⟨rfl, rfl⟩
  -- ParD := PieceLen * RootD
  light_step using hmid
  -- the sizes and the addresses
  light_piece (et17Addr_spec x (hostData x D g) hok.space htop) using et17Addr, ResidueTables.addresses
    with _ rfl
  exact ⟨μ₁, rfl, fun a ha => hμ₁ a (Or.inl ha)⟩

end Light.Sec3
