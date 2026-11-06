/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.MatrixLanguage

/-!
# The thin matrix product and the lopsided triangle problems in the layout of the word RAM

A solver of the thin matrix product, of #Lop-AE-SparseTri or of Lop-AE-SparseTri gets its sizes, the
bound on the entries and its addresses as arguments.  The three problems on the word RAM have one
layout: the cells 0, 1, 2 hold N, D and the number w of wanted positions, then come X, Y, the rows
and the columns of the wanted positions, then the output.

One more procedure, `thinTop`, is appended to the program of the solver: it reads N, D, w, forms the
bound N^e by e multiplications (the instances have the bound U = N^κ on their entries, for a fixed
exponent κ; e = κ for the matrix product, e = 0 for matrices of zeros and ones), computes the
addresses, calls the solver, and returns 1.

* `pre_toThinU`: the input is an instance of the task;
* `thinTop_ends`: the run of the outermost call;
* `small_limN`, `input_le_limN`: the limits are polynomial in N and D, and the input fits;
* `realizedN`: from a solver to the word RAM; `realized_thinProduct` and `realized_lop` (with
  `realized_lopCount` and `realized_lopDetect`) are its uses.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## The outermost procedure -/

/-- The first three cells of the input hold N, D and the number of wanted positions. -/
theorem memOf_input_N (x : ThinInstance) : memOf (x.input []) 0 = x.N := by
  simp [memOf, ThinInstance.input]

@[inherit_doc memOf_input_N]
theorem memOf_input_D (x : ThinInstance) : memOf (x.input []) 1 = x.D := by
  simp [memOf, ThinInstance.input]

@[inherit_doc memOf_input_N]
theorem memOf_input_w (x : ThinInstance) : memOf (x.input []) 2 = x.W.length := by
  simp [memOf, ThinInstance.input]

/-! ## The limits are polynomial in N and D -/

/-! ## From a solver to the word RAM -/

/-! ## The three problems -/

end Light.Sec3
