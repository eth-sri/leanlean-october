/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec4.Theorem30.Areas

/-!
# The cells of the directory, by name

The routines of Section 4 find the sizes and the addresses of the tables in the directory, the
first cells of the block.  `DirCells p b0 μ` says what the cells that they read hold, one equation
for each cell, under the name that the cell has in the program texts (`Dir.bands`, `Dir.encA`, …).
A proof that treats `x := mem[b0 + Dir.bands]` names the equation `bands`.  The shared stage
establishes all of them (`SharedReady.dirCells`).
-/

@[expose] public section

namespace Light.Sec4



/-- What the cells of the directory that the routines of Section 4 read hold. -/
structure DirCells (p : Sec2.Par) (b0 : ℕ) (μ : Light.Memory) : Prop where
  levels : μ b0 = p.L
  inner : μ (b0 + 1) = p.m
  outer : μ ((b0 : ℤ) + 4).toNat = p.Lo
  blocks : μ ((b0 : ℤ) + 7).toNat = p.K0
  bands : μ ((b0 : ℤ) + 9).toNat = p.nB
  leaves : μ ((b0 : ℤ) + 10).toNat = p.T
  mask : μ ((b0 : ℤ) + 21).toNat = p.aMASK b0
  band : μ ((b0 : ℤ) + 22).toNat = p.aBAND b0
  block : μ ((b0 : ℤ) + 23).toNat = p.aBLOCK b0
  digits : μ ((b0 : ℤ) + 24).toNat = p.aDIG3 b0
  encA : μ ((b0 : ℤ) + 26).toNat = p.aENCA b0
  encB : μ ((b0 : ℤ) + 27).toNat = p.aENCB b0
  sharedEnd : μ ((b0 : ℤ) + 30).toNat = aWD p b0

end Light.Sec4
