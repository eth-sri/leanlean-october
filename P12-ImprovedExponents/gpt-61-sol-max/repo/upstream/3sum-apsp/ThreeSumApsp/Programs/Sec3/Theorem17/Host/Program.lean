/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Arrays
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.PrimeStage
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Time

/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3



/-- The numbers of the procedures of Strassen's algorithm, if the list of the procedures of the host
starts at the number `o`. -/
def strNumsAt (o : ℕ) : StrNums := ⟨o + 12, o + 13, o + 14, o + 15, o + 16⟩

/-- The numbers of the procedures that countPrime calls. -/
def cpNumsAt (o : ℕ) : CpNums := ⟨o + 5, o + 6, o + 7, o + 8, o + 9, o + 10, o + 11, strNumsAt o⟩

/-- The numbers of the procedures that choosePrime calls. -/
def chNumsAt (o : ℕ) : ChNums := ⟨o + 3, o + 4, o + 17, cpNumsAt o, o, o + 28⟩

/-- The numbers of the procedures that the top procedure calls: `pS` is the solver, `pD` and `pG`
compute the parameters. -/
def et17NumsAt (pS pD pG o : ℕ) : Et17Nums where
  pD := pD
  pG := pG
  pSqrt := o
  pBrute := o + 2
  pScan := o + 1
  pChoose := o + 18
  pCap := o + 19
  pCeil := o + 20
  pBitLen := o + 4
  pDbl := o + 5
  pResid := o + 6
  pResidues := o + 7
  pClasses := o + 21
  pChunks := o + 22
  pLoop := o + 26
  pS := pS
  pWriteX := o + 23
  pWriteY := o + 24
  pScanPairs := o + 25
  ch := chNumsAt o

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : Light.InputTime} {need : Light.InputNeed}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

end Light.Sec3
