/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ImprovedExponents.PrunedProgram.Boxes.Query
public import ThreeSumApsp.Programs.Sec4.Theorem30.OutDigits
public import ThreeSumApsp.Programs.Sec4.Theorem30.NineNext
public import ThreeSumApsp.Programs.Sec4.Theorem30.Scatter
public import ThreeSumApsp.Programs.Sec4.Theorem30.StarFirst

@[expose] public section
namespace Light.Sec4.BoxTable

/-- Box routines, linked at the procedure numbers used by the staged solver. -/
def procs : Program := [nineFirstBody,nineNextBody,scatterBody,starFirstBody,radixBody 10,
  radixBody 11,.skip,.skip,sumBody,Fill.body,Tile.body,Grid.body,outDigitsBody,queryCoreBody]

def Has (P : Program) := ∀ i < 14, P[40+i]? = procs[i]?

variable {lim : Limits} {P : Program} (h : Has P) (std : Std lim)
include h std
theorem passes : Passes lim P := by
  have code := radix_spec (b:=11) (by decide) (by decide) (h 5 (by decide)) std
  exact ⟨nineFirst_spec (h 0 (by decide)) std,nineNext_spec (h 1 (by decide)) std,
    starFirst_spec (h 3 (by decide)) std,radix_spec (b:=10) (by decide) (by decide) (h 4 (by decide)) std,code,
    sum_spec (h 8 (by decide)) code std⟩

theorem querySpec : QueryCoreSpecP lim P := by
  have k := passes h std
  exact queryCoreP_spec (h 13 (by decide)) ⟨k.first,k.next,scatter_spec (h 2 (by decide)) std,k.decimal,k.boxCode⟩
end Light.Sec4.BoxTable
