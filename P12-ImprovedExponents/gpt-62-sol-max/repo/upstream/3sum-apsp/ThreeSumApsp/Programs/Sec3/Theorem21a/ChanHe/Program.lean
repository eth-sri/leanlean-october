/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

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

open ThreeSumApsp

namespace Proc

/-- The places of the procedures in the list `chBodies`. -/
registers [emod, log2, clog2, sqrt, sieve, half, merge, copy, fill, sort, count, clear, coll,
  heavy, search, modulus, nodeArray, nodes, distinct, repeated, bits, pick, round, grid, params,
  prep, core, host]

end Proc

/-- The procedures of the reduction, for a solver of Convolution-3SUM that is procedure number pC3
of a program with o procedures: the procedure at the place i of this list gets the number o + i.
The places have the names `Proc.emod`, …, `Proc.host`, in the order of the list. -/
def chBodies (κ pC3 o : ℕ) : Program :=
  [emodBody,
    log2Body,
    clog2Body,
    sqrtBody,
    sieveBody,
    halfBody,
    mergeBody,
    copyBody,
    fillBody,
    sortBody (o + Proc.sort) (o + Proc.half) (o + Proc.merge) (o + Proc.copy),
    countBody (o + Proc.emod),
    clearBucketsBody,
    collBody (o + Proc.count) (o + Proc.clear),
    heavyBody (o + Proc.count) (o + Proc.clear),
    searchBody (o + Proc.coll),
    modulusBody (o + Proc.search) (o + Proc.coll),
    nodeArrayBody (o + Proc.count) (o + Proc.clear),
    nodesBody (o + Proc.nodes) (o + Proc.modulus) (o + Proc.nodeArray) pC3 (o + Proc.heavy),
    distinctBody,
    repeatedBody,
    bitsBody,
    pickBody,
    roundBody (o + Proc.pick) (o + Proc.nodes),
    gridBody (o + Proc.round),
    paramsBody (o + Proc.log2) (o + Proc.clog2) (o + Proc.sqrt),
    prepBody (o + Proc.sieve) (o + Proc.fill) (o + Proc.copy) (o + Proc.sort) (o + Proc.distinct)
      (o + Proc.bits),
    coreBody (o + Proc.params) (o + Proc.prep) (o + Proc.grid) (o + Proc.repeated),
    hostBody κ (o + Proc.core)]

/-- **The host**: from every solver of Convolution-3SUM, the procedures of the reduction make a
solver of 3SUM. -/
theorem isHost_s3 (κ : ℕ) : IsHost c3Task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + Proc.host,
    hostBody κ (P₀.length + Proc.core), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r hr => polyNeed_chNeed κ r hr⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := Proc.host)
      rfl
    assumption
  rw [List.append_assoc]
  have L : ∀ {i : ℕ} {body : Stmt}, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hEmod : EmodSpec lim (P₀ ++ (chBodies κ pC3 P₀.length ++ R)) P₀.length :=
    emodSpec_of (L (i := Proc.emod) rfl)
  have hLog2 := log2Spec_of (lim := lim) (L (i := Proc.log2) rfl)
  have hClog2 := clog2Spec_of (lim := lim) (L (i := Proc.clog2) rfl)
  have hPrimes := primesSpec_of (lim := lim) (L (i := Proc.sieve) rfl)
  have hSort :=
    sortSpec_of (lim := lim) ⟨L (i := Proc.sort) rfl, L (i := Proc.half) rfl,
      L (i := Proc.merge) rfl, L (i := Proc.copy) rfl⟩
  have hCount : CountSpec lim _ _ := count_spec (L (i := Proc.count) rfl) hEmod
  have hClear : ClearSpec lim _ _ := clearBuckets_spec (L (i := Proc.clear) rfl)
  have hColl := coll_spec (L (i := Proc.coll) rfl) hCount hClear
  have hHeavy := heavy_spec (L (i := Proc.heavy) rfl) hCount hClear
  have hModulus := modulusSpec_of (L (i := Proc.modulus) rfl) (L (i := Proc.search) rfl) hColl
  have hArray := nodeArray_spec (L (i := Proc.nodeArray) rfl) hCount hClear
  have hNodes := nodes_spec ⟨hsol, L (i := Proc.nodes) rfl, hModulus, hArray, hHeavy⟩
  have hDistinct := distinct_spec (lim := lim) (L (i := Proc.distinct) rfl)
  have hBits := bits_spec (lim := lim) (L (i := Proc.bits) rfl)
  have hPick := pick_spec (lim := lim) (L (i := Proc.pick) rfl)
  have hRound := round_spec (L (i := Proc.round) rfl) hPick hNodes
  have hGrid := grid_spec (L (i := Proc.grid) rfl) hRound
  have hParams := params_spec (L (i := Proc.params) rfl) hLog2 hClog2 (L (i := Proc.sqrt) rfl)
  have hPrep :=
    prep_spec (L (i := Proc.prep) rfl) hPrimes (L (i := Proc.fill) rfl) (L (i := Proc.copy) rfl)
      hSort hDistinct hBits
  have hCore := core_spec (L (i := Proc.core) rfl) hParams hPrep hGrid (L (i := Proc.repeated) rfl)
  exact host_spec hCore hpre hok

/-- [CH20, Theorem 5.1] for programs of the light language: 3SUM from Convolution-3SUM. -/
theorem claim_CH20_Theorem_5_1 : Claim.CH20_Theorem_5_1 lightModel :=
  claim_CH20_Theorem_5_1_of_host isHost_s3

end Light.Sec3.ChanHe
