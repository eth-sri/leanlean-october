/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Bits
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Distinct
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Grid
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Host
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.LibraryContracts
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Modulus
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeArray
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Parameters
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Prepare
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduction
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.TimeBound

/-!
# The program of the reduction from 3SUM to Convolution-3SUM, assembled

The procedures of the reduction are appended to the program of an arbitrary solver of
Convolution-3SUM. Each of them meets its specification because the procedures that it calls meet
theirs; the last one, the host, solves 3SUM (`isHost_s3`).  That the answer is right comes from
`core_spec`, through `threeSum_iff_trees`.  With the arithmetic of `claim_CH20_Theorem_5_1_of_host`
this gives [CH20, Theorem 5.1] (Theorem 21(a)) for programs of the light language
(`claim_CH20_Theorem_5_1`).
-/


namespace Light.Sec3.ChanHe

open ThreeSumApsp

namespace Proc

/- The places of the procedures in the list `chBodies`. -/
slots emod log2 clog2 sqrt sieve half merge copy fill sort resid tally coll heavy search modulus nodeArray nodes distinct twice zeroThree bits pick round row grid params prep core host

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
    residBody (o + Proc.emod),
    tallyBody,
    collBody (o + Proc.resid) (o + Proc.tally),
    heavyBody (o + Proc.resid) (o + Proc.tally),
    searchBody (o + Proc.coll),
    modulusBody (o + Proc.search) (o + Proc.coll),
    nodeArrayBody (o + Proc.resid) (o + Proc.tally),
    nodesBody (o + Proc.nodes) (o + Proc.modulus) (o + Proc.nodeArray) pC3 (o + Proc.heavy),
    distinctBody,
    twiceBody,
    zeroThreeBody,
    bitsBody,
    pickBody,
    roundBody (o + Proc.pick) (o + Proc.nodes),
    rowBody (o + Proc.round),
    gridBody (o + Proc.row),
    paramsBody (o + Proc.log2) (o + Proc.clog2) (o + Proc.sqrt),
    prepBody (o + Proc.sieve) (o + Proc.fill) (o + Proc.copy) (o + Proc.sort) (o + Proc.distinct)
      (o + Proc.bits),
    coreBody (o + Proc.params) (o + Proc.prep) (o + Proc.grid) (o + Proc.twice) (o + Proc.zeroThree)
      (o + Proc.nodes),
    hostBody κ (o + Proc.core)]

/-- **The host**: from every solver of Convolution-3SUM, the procedures of the reduction make a
solver of 3SUM. -/
theorem isHost_s3 (κ : ℕ) : IsHost c3Task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + Proc.host,
    hostBody κ (P₀.length + Proc.core), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, by grind [polyNeed_chNeed]⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := Proc.host)
      rfl
    assumption
  rw [List.append_assoc]
  have L : ∀ {i : ℕ} {body : Stmt}, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    by grind
  have hEmod : EmodSpec lim _ P₀.length :=
    emodSpec_of (L (i := Proc.emod) rfl)
  have hResid := resid_spec (L (i := Proc.resid) rfl) hEmod
  have hTally := tally_spec (lim := lim) (L (i := Proc.tally) rfl)
  have hNodes := nodes_spec ⟨hsol, L (i := Proc.nodes) rfl, (modulusSpec_of (L (i := Proc.modulus) rfl) (by aesop) (coll_spec (L (i := Proc.coll) rfl) hResid hTally)), (nodeArray_spec (L (i := Proc.nodeArray) rfl) hResid hTally), (heavy_spec (L (i := Proc.heavy) rfl) hResid hTally)⟩
  exact host_spec (core_spec (L (i := Proc.core) rfl) (params_spec (L (i := Proc.params) rfl) (log2Spec_of (lim := lim) (L (i := Proc.log2) rfl)) (clog2Spec_of (lim := lim) (L (i := Proc.clog2) rfl)) (L (i := Proc.sqrt) rfl)) (prep_spec (L (i := Proc.prep) rfl) (primesSpec_of (lim := lim) (L (i := Proc.sieve) rfl)) (L (i := Proc.fill) rfl) (L (i := Proc.copy) rfl)
      (sortSpec_of (lim := lim) ⟨L (i := Proc.sort) rfl, by aesop,
      L rfl, L rfl⟩) (distinct_spec (lim := lim) (L (i := Proc.distinct) rfl)) (bits_spec (lim := lim) (L (i := Proc.bits) rfl))) (grid_spec (L (i := Proc.grid) rfl) (row_spec (L (i := Proc.row) rfl) (round_spec (L (i := Proc.round) rfl) (pick_spec (lim := lim) (L (i := Proc.pick) rfl)) hNodes))) (twice_spec (lim := lim) (L (i := Proc.twice) rfl)) (zeroThree_spec (lim := lim) (L (i := Proc.zeroThree) rfl)) hNodes) hpre hok

/-- [CH20, Theorem 5.1] for programs of the light language: 3SUM from Convolution-3SUM. -/
theorem claim_CH20_Theorem_5_1 : Claim.CH20_Theorem_5_1 lightModel :=
  claim_CH20_Theorem_5_1_of_host isHost_s3
