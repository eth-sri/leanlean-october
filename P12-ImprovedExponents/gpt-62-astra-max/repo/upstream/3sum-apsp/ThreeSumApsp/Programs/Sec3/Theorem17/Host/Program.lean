/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Arrays
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

open ThreeSumApsp ThreeSumApsp.Spec

/-- Residues, power table, matrix maps, trace kernel and the two residue loops. -/
def cpNumsAt (o : ℕ) : CpNums := ⟨o+4,o+5,o+6,o+7,o+8,o+9,o+10,o+11,o+12,o+14⟩

/-- The numbers of the procedures that choosePrime calls. -/
def chNumsAt (o : ℕ) : ChNums := ⟨o + 2, o + 3, o + 15, cpNumsAt o, o, o + 23⟩

/-- The numbers of the procedures that the top procedure calls: `pS` is the solver, `pD` and `pG`
compute the parameters. -/
def et17NumsAt (pS pD pG o : ℕ) : Et17Nums where
  pD := pD
  pG := pG
  pSqrt := o
  pScan := o + 1
  pChoose := o + 16
  pCap := o + 17
  pCeil := o + 18
  pBitLen := o + 3
  pDbl := o + 4
  pResid := o + 5
  pResidues := o + 6
  pClasses := o + 19
  pChunks := o + 20
  pS := pS
  pWriteX := o + 21
  pWriteY := o + 22
  ch := chNumsAt o

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

end Light.Sec3
