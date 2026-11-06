/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Preprocessing
public import ThreeSumApsp.Programs.Sec4.Theorem30.ThinLayout
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize

/-!
# Theorem 30 on the word RAM: the two main procedures for the trusted layout

The trusted layout of the input, the one in the statement of the theorem (`ThinPair.input`), is N,
D, m, L, t, X, Y (`Layout`, `layout_input`). The main procedure of the preprocessing reads the sizes
and calls preCore with the block of the data structure right behind the input (`preMain_meets`); the
main procedure of a query reads N and D, computes the address of the block and calls queryAt
(`queryMain_meets`); between them the memory satisfies `DS`. `Meets.main` and
`AnswersQueries.of_meets` pass from the procedures to the outermost statement.

Time, space and the nesting of calls are within a constant times the expressions of the theorem
(`exists_bounds30`, from `exists_tPreCore_le`, `exists_tQueryAt_le`, `exists_top_sub_le`), the
limits `lim30` suffice and are polynomial in N (`lim30_ok`, `small_lim30`), and the numbers of the
input fit in a word (`abs_input_le`). This makes the light program a data structure (`top30`). The
compiler (`isDataStructure_of_program_scaled`) then gives Items.Theorem_30 for every program that
holds the two main procedures at their numbers and meets the specifications of preCore and queryAt
(`theorem_30_of`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

namespace Thm30

/-- The locals of the two main procedures: the answer, which in a query is at first the row I, and
the column J; then N, D, the product N D, and in preMain the address of Y.  The last local is the
address of the block. -/
abbrev Ans : ℕ := 0
 abbrev Col : ℕ := 1
 abbrev Size : ℕ := 2
 abbrev Dim : ℕ := 3
 abbrev Area : ℕ := 4
 abbrev MatY : ℕ := 5
 abbrev Block : ℕ := 6
 abbrev QBlock : ℕ := 5

end Thm30

namespace Thm30

end Thm30

open Thm30

section
variable {lim : Limits} {P : Program} {N m L t : ℕ} {hmL : m ≤ L}
  {X : Matrix (Fin N) (Fin (D m)) ℤ} {Y : Matrix (Fin (D m)) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ}

end

end Light.Sec4
