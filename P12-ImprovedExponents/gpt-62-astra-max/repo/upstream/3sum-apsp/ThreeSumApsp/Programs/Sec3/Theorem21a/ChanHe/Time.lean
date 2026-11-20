/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts

/-!
# 3SUM from Convolution-3SUM: the time and the need of the host

The host s3(n, U, x, fr) has a parameter `κ` (a natural number, fixed with the program): it first
replaces the bound `U` by `max U (n^κ)`. So on all inputs with `U ≤ n^κ` it asks the
Convolution-3SUM solver for instances of one and the same length and bound, `8 m²` and
`120 n^κ + 40` with `m = mPar n (2 n^κ)`. (A running time `T N B` of an arbitrary solver need not be
monotone in `N`.)

The time is split into the host's own work and the number of calls of the solver. This file has the
definitions and one identity (`tNodes_eq`); the arithmetic (`claim_CH20_Theorem_5_1_of_host`) starts
from them.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-- An upper bound on the number of calls of the recursive procedure for one three-set input. -/
def callsB (n : ℕ) : ℕ := visits (fuel n)

/-- The cost of one call of the recursive procedure without the call of the solver. -/
def nodeOwn (n V m np : ℕ) : ℕ := tModulus np n n n V + tNodeArray m n n n V + 3 * tHeavy n V + 360

/-- The time of the recursive procedure, split into its own work and the calls of the solver. -/
theorem tNodes_eq (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) :
    tNodes T n V m np calls = calls * (nodeOwn n V m np + T m (2 * V + 1)) := by
  unfold tNodes tNode nodeOwn
  ring

/-- The time of params: four logarithms and a square root. -/
def tParams (n V : ℕ) : ℕ :=
  tLog2 (2 * V) + (18 * Nat.sqrt n + 12) + tLog2 (wPar n V + 1) + tLog2 n +
    (tLog2 (Nat.log 2 n + 2) + 30) + 160

namespace Separate

def width (n : ℕ) := 5 * Lam (n^3) + 1
/-- A division-free majorant for the separating modulus. -/
def bound (n : ℕ) := width n * (2*width n+4)
def tPick (n : ℕ) := 140*n+40
def moreTime (B t : ℕ) := (B+1)*(t+80)

end Separate
open Separate

/-- Params, index-modulus bound, prime list and count table. -/
def tSetup (n V : ℕ) := let m := mPar n V
  tParams n V + tLog2 (2*n^3) + tPrimes m + (13*(m*m)+6) + 300

def inputsB (n : ℕ) := (bound n+1)^4
def coreCalls (n : ℕ) := inputsB n * callsB n
def leafOwn (n V : ℕ) := 3*Separate.tPick n + 180 + callsB n * nodeOwn n V (mPar n V) #(Nat.primesLE (mPar n V))
def coreOwn (n V : ℕ) := tSetup n V + inputsB n * (leafOwn n V + 400)

/-- The time of the host after the bound has been fixed. -/
def coreTime (T : ℕ → ℕ → ℕ) (n V : ℕ) : ℕ :=
  coreOwn n V + coreCalls n * T (mPar n V) (2 * V + 1)

/-- **The time of the host.** -/
def chTime (κ : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 20 * κ + 40 + coreTime T n (2 * max U (n ^ κ))

/-- Room for the disjoint tables and for expressions forming indices and counts.
The table indexed by input value is sparse: only touched flags are cleared. -/
def slack (n V : ℕ) := let m := mPar n V
  8*(m+1)^2 + 9*V + 8*n + 10*n^3 + 2*n^2 + 4*bound n + n*(4*bound n) + 500

def coreNeed (r : ℕ → ℕ → Need) (n V : ℕ) : Need :=
  let h := nodesNeed r n V (mPar n V) (fuel n)
  ⟨h.word,h.cells+slack n V,h.depth+10⟩

/-- **The need of the host.** -/
def chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(coreNeed r n (2 * max U (n ^ κ))).word + 2 * n ^ κ + 2 * U,
    (coreNeed r n (2 * max U (n ^ κ))).cells,
    (coreNeed r n (2 * max U (n ^ κ))).depth + 1⟩

end Light.Sec3.ChanHe
