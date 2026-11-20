/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

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
  pS := pS
  pWriteX := o + 23
  pWriteY := o + 24
  ch := chNumsAt o

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

/-- The procedures of the variant host: procedure number `i` of this list gets the number `o + i`.
Unused slots retain their original numbers. -/
def et17Procs (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody,                                                -- 0
    scanBody,                                               -- 1
     .skip,                                      -- 2
    primesBody ν.ch.pSqrt ν.ch.pSieve,                      -- 3
    bitLenBody,                                             -- 4
    dblTableBody,                                           -- 5
    residBody,                                              -- 6
    residuesBody ν.pResid,                                  -- 7
    spreadTableBody,                                        -- 8
    szTableBody,                                            -- 9
    buildZBody,                                             -- 10
    countZeroBody,                                          -- 11
    vlinBody,                                               -- 12
    cconvBody,                                              -- 13
    fillBody,                                               -- 14
    phaseBody ν.ch.cp.str,                                  -- 15
    strBody ν.ch.cp.str,                                    -- 16
    countPrimeBody ν.ch.cp,                                 -- 17
    choosePrimeBody ν.ch,                                   -- 18
    queryCapNatBody,                                        -- 19
    ceilDivBody,                                            -- 20
    classesBody,                                            -- 21
    chunksBody,                                             -- 22
    writeXBody,                                             -- 23
    writeYBody,                                             -- 24
    .skip, .skip, .skip,                                    -- 25–27
    sieveBody]                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Program.lean
/-- **The context of the top procedure**, in the assembled program of the variant with anything
appended to it. -/
theorem et17Ctx_assembled (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun
      Gfun tD tG wD wG := by
  -- Procedure number `i` of the list.
  have L : ∀ {i : ℕ} {body : Stmt}, (et17Procs pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact
    { loop := ⟨hsol, L rfl, L rfl, L rfl⟩
      hSqrt := L (i := 0) rfl
      hChoose := L rfl
      ch := ⟨L rfl, L rfl, L rfl,
        ⟨L rfl, L rfl, L rfl, L rfl, L rfl,
          L rfl, L rfl,
          ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩,
        ⟨L (i := 0) rfl, L rfl⟩⟩
      hCap := L rfl
      hCeil := L rfl
      hBitLen := L rfl
      hDbl := L rfl
      hResid := L rfl
      hResidues := L rfl
      hClasses := L rfl
      hChunks := L rfl
      dProc := hD _
      gProc := hG _
      D_pos := hpos }


end Light.Sec3
