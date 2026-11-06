/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Bits
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Distinct
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Grid
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Host
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.LibraryContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Modulus
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeArray
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Parameters
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Prepare
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduction
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.TimeBound

/-!
# The program of the reduction from 3SUM to Convolution-3SUM, assembled

The procedures of the reduction are appended to the program of an arbitrary solver of
Convolution-3SUM. Each of them meets its specification because the procedures that it calls meet
theirs; the last one, the host, solves 3SUM (`isHost_s3`).  That the answer is right comes from
`core_spec`, through `threeSum_iff_trees`.  With the arithmetic of `claim_CH20_Theorem_5_1_of_host`
this gives [CH20, Theorem 5.1] (Theorem 21(a)) for programs of the light language
(`claim_CH20_Theorem_5_1`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe




/-- The procedures of the reduction, for a solver of Convolution-3SUM that is procedure number pC3
of a program with o procedures: the procedure at the place i of this list gets the number o + i.
The places have the names `Proc.emod`, …, `Proc.host`, in the order of the list. -/
def chBodies κ pC3 o :=
  [emodBody,
    log2Body,
    clog2Body,
    sqrtBody,
    sieveBody,
    halfBody,
    mergeBody,
    copyBody,
    fillBody,
    sortBody (o + 9) (o + 5) (o + 6) (o + 7),
    residBody (o + 0),
    tallyBody,
    collBody (o + 10) (o + 11),
    heavyBody (o + 10) (o + 11),
    searchBody (o + 12),
    modulusBody (o + 14) (o + 12),
    nodeArrayBody (o + 10) (o + 11),
    nodesBody (o + 17) (o + 15) (o + 16) pC3 (o + 13),
    distinctBody,
    twiceBody,
    zeroThreeBody,
    bitsBody,
    pickBody,
    roundBody (o + 22) (o + 17),
    rowBody (o + 23),
    gridBody (o + 24),
    paramsBody (o + 1) (o + 2) (o + 3),
    prepBody (o + 4) (o + 8) (o + 7) (o + 9) (o + 18)
      (o + 21),
    coreBody (o + 26) (o + 27) (o + 25) (o + 19) (o + 20)
      (o + 17),
    hostBody κ (o + 28)]

/-- **The host**: from every solver of Convolution-3SUM, the procedures of the reduction make a
solver of 3SUM. -/
theorem isHost_s3 κ : IsHost c3Task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + 29,
    hostBody κ (P₀.length + 28), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r hr => polyNeed_chNeed κ r hr⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := 29)
      rfl
    rwa [List.append_nil] at this
  rw [List.append_assoc]
  have L : ∀ {i } {body }, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hEmod : EmodSpec lim (P₀ ++ (chBodies κ pC3 P₀.length ++ R)) P₀.length :=
    emodSpec_of (L (i := 0) rfl)
  have hLog2 := log2Spec_of (lim := lim) (L (i := 1) rfl)
  have hClog2 := clog2Spec_of (lim := lim) (L (i := 2) rfl)
  have hPrimes := primesSpec_of (lim := lim) (L (i := 4) rfl)
  have hSort :=
    sortSpec_of (lim := lim) ⟨L (i := 9) rfl, L (i := 5) rfl,
      L (i := 6) rfl, L (i := 7) rfl⟩
  have hResid := resid_spec (L (i := 10) rfl) hEmod
  have hTally := tally_spec (lim := lim) (L (i := 11) rfl)
  have hColl := coll_spec (L (i := 12) rfl) hResid hTally
  have hHeavy := heavy_spec (L (i := 13) rfl) hResid hTally
  have hModulus := modulusSpec_of (L (i := 15) rfl) (L (i := 14) rfl) hColl
  have hArray := nodeArray_spec (L (i := 16) rfl) hResid hTally
  have hNodes := nodes_spec ⟨hsol, L (i := 17) rfl, hModulus, hArray, hHeavy⟩
  have hDistinct := distinct_spec (lim := lim) (L (i := 18) rfl)
  have hTwice := twice_spec (lim := lim) (L (i := 19) rfl)
  have hZero := zeroThree_spec (lim := lim) (L (i := 20) rfl)
  have hBits := bits_spec (lim := lim) (L (i := 21) rfl)
  have hPick := pick_spec (lim := lim) (L (i := 22) rfl)
  have hRound := round_spec (L (i := 23) rfl) hPick hNodes
  have hRow := row_spec (L (i := 24) rfl) hRound
  have hGrid := grid_spec (L (i := 25) rfl) hRow
  have hParams := params_spec (L (i := 26) rfl) hLog2 hClog2 (L (i := 3) rfl)
  have hPrep :=
    prep_spec (L (i := 27) rfl) hPrimes (L (i := 8) rfl) (L (i := 7) rfl)
      hSort hDistinct hBits
  have hCore := core_spec (L (i := 28) rfl) hParams hPrep hGrid hTwice hZero hNodes
  exact host_spec hCore hpre hok

/-- [CH20, Theorem 5.1] for programs of the light language: 3SUM from Convolution-3SUM. -/
def claim_CH20_Theorem_5_1 :=
  claim_CH20_Theorem_5_1_of_host isHost_s3

end Light.Sec3.ChanHe
