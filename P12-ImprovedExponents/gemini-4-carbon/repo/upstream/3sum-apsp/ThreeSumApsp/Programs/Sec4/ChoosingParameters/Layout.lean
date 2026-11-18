/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

/-!
# Section 4.4, the data structure: the two main procedures for the layout of the statements

The input is N, D, X, Y (`ThinPair.input []`), as in the statements of the corollaries; the free
pointer is the first cell after it. The texts `preMain31Body` and `queryMain31Body` serve all
rational parameters c and θ. Each reads N and D, computes the address of Y and the free pointer, and
calls the relocatable routine: `preMain31_meets` for the preprocessing, `queryMain31_meets` for a
query. Between them the memory satisfies `InputReady31`. The relocatable routines enter through
their specifications `PreSpec31` and `QuerySpec31`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The texts -/

namespace Main31

/-- The locals of the two main procedures: the answer, which in a query is at first the row I, and
the column J; then N, D, the product N D, the address of Y, the free pointer, and in the
preprocessing the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Col : ℕ := 1
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Area : ℕ := 4
@[inherit_doc Ans] abbrev MatY : ℕ := 5
@[inherit_doc Ans] abbrev Free : ℕ := 6
@[inherit_doc Ans] abbrev Res : ℕ := 7

end Main31

open Main31 in
/-- The main procedure of the preprocessing: read the sizes, compute the two addresses, call pre31,
answer 1. -/
def preMain31Body : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Area (v Size *' v Dim) ;;
  .set MatY (k 2 +' v Area) ;; .set Free (v MatY +' v Area) ;;
  .call Proc.pre31 [v Size, v Dim, k 2, v MatY, v Free] Res ;;
  .set Ans (k 1)

open Main31 in
/-- The main procedure of a query (I, J): the same five assignments, then call query31. -/
def queryMain31Body : Stmt :=
  .set Size (M (k 0)) ;; .set Dim (M (k 1)) ;; .set Area (v Size *' v Dim) ;;
  .set MatY (k 2 +' v Area) ;; .set Free (v MatY +' v Area) ;;
  .call Proc.query31 [v Ans, v Col, v Size, v Dim, k 2, v MatY, v Free] Ans

/-! ## What they do -/

end Light.Sec4
