/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Residues

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

/-- A list of residues is as long as the list of numbers. -/
@[simp] theorem length_residList (p : ℕ) (l : List ℤ) : (residList p l).length = l.length := by
  simp [residList]

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

namespace ResidueTables

/-- The common part of the hashing and instance hosts' frames. Slots 1 and 8 are not read here. -/
registers [Size, _, AdrAB, AdrBC, AdrAC, Free, ThePrime, Bits, _, SizeSq, ResAB, ResBC, ResAC, Small]

/-- The address of the residues of the list ab. -/
def rab (w len : ℕ) : ℕ := w + (len + 1)

/-- The address of the residues of the list bc. -/
def rbc (w len n : ℕ) : ℕ := rab w len + n * n

/-- The address of the residues of the list ac. -/
def rac (w len n : ℕ) : ℕ := rbc w len n + n * n

/-- The address of the next work area. -/
def top (w len n : ℕ) : ℕ := rac w len n + n * n

/-- Allocate the doubles and the three equal-length residue tables, ending at `next`. -/
def addresses (next : ℕ) : Stmt :=
  .set SizeSq (v Size *' v Size) ;;
  .set ResAB (v Free +' (v Bits +' k 1)) ;;
  .set ResBC (v ResAB +' v SizeSq) ;;
  .set ResAC (v ResBC +' v SizeSq) ;;
  .set next (v ResAC +' v SizeSq)

/-- Write the doubles, then reduce the three input matrices modulo `p`. -/
def body (pDbl pResidues : ℕ) : Stmt :=
  .call pDbl [v Free, v ThePrime, v Bits] Small ;;
  .call pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
  .call pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
  .call pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small

abbrev locals (n ab bc ac w p len : ℕ) (a b r : ℤ) : List ℤ :=
  [n, a, ab, bc, ac, w, p, len, b, (n * n : ℕ), rab w len, rbc w len n, rac w len n, r]

abbrev time (n len : ℕ) : ℕ := tDblTable len + 3 * tResidues (n * n) len + 26

structure Tables (x : TriInst) (w p len : ℕ) (μ : ℕ → ℤ) : Prop where
  dbl : Seg μ w (dblList p len)
  rab : SegN μ (rab w len) (residList p x.AB)
  rbc : SegN μ (rbc w len x.n) (residList p x.BC)
  rac : SegN μ (rac w len x.n) (residList p x.AC)

/-- The tables occupy a single contiguous work area, following the inputs. -/
theorem spec {pDbl pRes pResidues w p len : ℕ} {x : TriInst} {a b r : ℤ} {rest : List ℤ}
    (hDbl : P[pDbl]? = some dblTableBody) (hRes : P[pRes]? = some residBody)
    (hResidues : P[pResidues]? = some (residuesBody pRes))
    (h : x.Arrays μ w) (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hU : x.U < 2 ^ len)
    (hword : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d + 2 ≤ lim.depth)
    (htop : top w len x.n ≤ lim.space) :
    Ends lim P d (body pDbl pResidues)
      ⟨frame (locals x.n x.ab x.bc x.ac w p len a b r ++ rest), μ⟩ (time x.n len)
      fun σ' => ∃ r' μ', σ' = ⟨frame (locals x.n x.ab x.bc x.ac w p len a b r' ++ rest), μ'⟩ ∧
        Tables x w p len μ' ∧ SameOn (fun c => c < w ∨ top w len x.n ≤ c) μ μ' := by
  have places : rab w len = w + (len + 1) ∧ rbc w len x.n = rab w len + x.n * x.n ∧
      rac w len x.n = rbc w len x.n + x.n * x.n ∧ top w len x.n = rac w len x.n + x.n * x.n :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hpow : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by decide)
      (Nat.le_succ len))) hword
  light_facts h.arrAB h.arrBC h.arrAC
  unfold body time
  light_call (dblTable_meets (dst := w) hDbl hw (by omega) hpow) with _ μ₁ ⟨dbl₁, same₁⟩
  light_call (residues_meets hResidues hRes (by omega)
    (ResiduesPre.of_array (dst := rab w len) h.arrAB.keep dbl₁ hw hp hU hword))
    with _ μ₂ ⟨rab₂, same₂⟩
  light_call (residues_meets hResidues hRes (by omega)
    (ResiduesPre.of_array (dst := rbc w len x.n) h.arrBC.keep dbl₁.keep hw hp hU hword))
    with _ μ₃ ⟨rbc₃, same₃⟩
  light_call (residues_meets hResidues hRes (by omega)
    (ResiduesPre.of_array (dst := rac w len x.n) h.arrAC.keep dbl₁.keep hw hp hU hword))
    with r' μ₄ ⟨rac₄, same₄⟩
  exact ⟨r', μ₄, rfl, ⟨dbl₁.keep, rab₂.keep, rbc₃.keep, rac₄⟩, by light_keep⟩

end ResidueTables

end Light.Sec3
