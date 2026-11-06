module

public import PaperStatements
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Tasks

@[expose] public section

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 21(a): Convolution-3SUM reduces to Exact Triangle

[VW13, Theorem 4.3] in the form needed for Theorem 21(a): Convolution-3SUM on `N < t²`
numbers becomes `2t` instances of Exact Triangle on `t` vertices per part.  In instance `s` the
triangle `(a, b, c)` stands for the pair `i = at + b`, `j = ct + s - b` (`convTemplate`).  Every
solution is such a triangle (`exists_hasZeroTriangle`), and a zero triangle is a solution, because
an index out of range gives a weight so large that the sum is positive
(`convolution3SUM_of_isZeroTriangle`).  Together: `convolution3SUM_iff`, and with `t = ⌊√N⌋ + 1`,
`theorem_21a_convolution_to_exact`.
-/


namespace ThreeSumApsp

namespace Theorem21

/-- Instance `s` of the reduction from Convolution-3SUM.  The triangle `(a, b, c)` stands for the
pair `i = a t + b`, `j = c t + s - b`, for which `i + j = (a + c) t + s`: the edge `(a, b)` carries
`x_i`, the edge `(b, c)` carries `x_j`, and the edge `(a, c)` carries `-x_{i+j}`.  An edge whose
index is out of range gets the filler weight. -/
def convTemplate (t N s : ℕ) : TriangleTemplate t N where
  eAB a b := if h : a.val * t + b.val < N then some (false, ⟨a.val * t + b.val, h⟩) else none
  eBC b c :=
    if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
      some (false, ⟨c.val * t + s - b.val, h.2⟩)
    else none
  eAC a c :=
    if h : (a.val + c.val) * t + s < N then some (true, ⟨(a.val + c.val) * t + s, h⟩) else none

/-- The weight of the edge `(a, b)`. -/
theorem convTemplate_AB {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (a b : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAB a b)
      = if h : a.val * t + b.val < N then x ⟨a.val * t + b.val, h⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- The weight of the edge `(b, c)`. -/
theorem convTemplate_BC {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (b c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eBC b c)
      = if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
          x ⟨c.val * t + s - b.val, h.2⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- The weight of the edge `(a, c)`. -/
theorem convTemplate_AC {t N s : ℕ} {x : Fin N → ℤ} {fill : ℤ} (a c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAC a c)
      = if h : (a.val + c.val) * t + s < N then -x ⟨(a.val + c.val) * t + s, h⟩ else fill := by
  simp only [convTemplate]
  split <;> rfl

/-- A solution `(i, j)` is the triangle `(⌊i/t⌋, i mod t, ⌊j/t⌋)` of the instance
`s = (j mod t) + (i mod t)`. -/
theorem exists_hasZeroTriangle {t N : ℕ} {x : Fin N → ℤ} {fill : ℤ} (hNt : N < t * t)
    {i j : Fin N} (hij : i.val + j.val < N) (h : x i + x j = x ⟨i.val + j.val, hij⟩) :
    ∃ s < 2 * t, ((convTemplate t N s).instantiate x fill).HasZeroTriangle := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hit := Nat.mod_lt i.val ht
  have := Nat.mod_lt j.val ht
  have := Nat.div_add_mod' j.val t
  -- The three indices are `i`, `j` and `i + j`, so they are in range.
  have hAB : i.val / t * t + i.val % t = i.val := Nat.div_add_mod' i.val t
  have hBC : j.val / t * t + (j.val % t + i.val % t) - i.val % t = j.val := by omega
  have hAC : (i.val / t + j.val / t) * t + (j.val % t + i.val % t) = i.val + j.val := by
    rw [Nat.add_mul]
    omega
  refine ⟨j.val % t + i.val % t, by omega, ⟨i.val / t, Nat.div_lt_of_lt_mul (i.isLt.trans hNt)⟩,
    ⟨i.val % t, hit⟩, ⟨j.val / t, Nat.div_lt_of_lt_mul (j.isLt.trans hNt)⟩, ?_⟩
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate,
    convTemplate_AB, convTemplate_BC, convTemplate_AC]
  rw [dif_pos (hAB.trans_lt i.isLt), dif_pos ⟨by omega, hBC.trans_lt j.isLt⟩,
    dif_pos (hAC.trans_lt hij)]
  simp only [hAB, hBC, hAC, Fin.eta, h]
  ring

/-- With the filler `2U + 1`, every weight is at least `-U`. -/
theorem neg_le_templateWeight {N : ℕ} {x : Fin N → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) (o : Option (Bool × Fin N)) : -U ≤ templateWeight x (2 * U + 1) o := by
  rcases o with _ | ⟨_ | _, i⟩ <;> simp only [templateWeight]
  · omega
  · exact (abs_le.mp (hx i)).1
  · exact neg_le_neg (abs_le.mp (hx i)).2

/-- A zero triangle of an instance with the filler `2U + 1` is a solution. -/
theorem convolution3SUM_of_isZeroTriangle {t N s : ℕ} {x : Fin N → ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) {a b c : Fin t}
    (h : ((convTemplate t N s).instantiate x (2 * U + 1)).IsZeroTriangle a b c) :
    Convolution3SUM x := by
  simp only [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate] at h
  have := neg_le_templateWeight hU hx ((convTemplate t N s).eAB a b)
  have := neg_le_templateWeight hU hx ((convTemplate t N s).eBC b c)
  have := neg_le_templateWeight hU hx ((convTemplate t N s).eAC a c)
  -- One filler `2U + 1` and two weights that are at least `-U` have a positive sum, so the three
  -- indices are in range.
  have hAB : a.val * t + b.val < N := by
    by_contra hout
    rw [convTemplate_AB, dif_neg hout] at h
    omega
  have hBC : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N := by
    by_contra hout
    rw [convTemplate_BC, dif_neg hout] at h
    omega
  have hAC : (a.val + c.val) * t + s < N := by
    by_contra hout
    rw [convTemplate_AC, dif_neg hout] at h
    omega
  rw [convTemplate_AB, convTemplate_BC, convTemplate_AC, dif_pos hAB, dif_pos hBC, dif_pos hAC] at h
  -- The triangle stands for `i = at + b` and `j = ct + s - b`, and `i + j = (a + c)t + s`.
  have hsum : a.val * t + b.val + (c.val * t + s - b.val) = (a.val + c.val) * t + s := by
    rw [Nat.add_mul]
    omega
  refine ⟨⟨a.val * t + b.val, hAB⟩, ⟨c.val * t + s - b.val, hBC.2⟩, hsum ▸ hAC, ?_⟩
  simp only [hsum]
  -- `h` says `x_i + x_j - x_{i+j} = 0`.
  linarith [h]

/-- The reduction of [VW13, Theorem 4.3], for `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the instances `s < 2t`, with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_iff {t N : ℕ} {x : Fin N → ℤ} {U : ℤ} (hN : 1 ≤ N) (hNt : N < t * t)
    (hx : ∀ i, |x i| ≤ U) :
    Convolution3SUM x ↔
      ∃ s < 2 * t, ((convTemplate t N s).instantiate x (2 * U + 1)).HasZeroTriangle := by
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact exists_hasZeroTriangle hNt hij h
  · rintro ⟨s, -, a, b, c, h⟩
    exact convolution3SUM_of_isZeroTriangle ((abs_nonneg _).trans (hx ⟨0, hN⟩)) hx h

end Theorem21

end ThreeSumApsp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM reduces to Exact Triangle, on lists

Theorem 21(a), after [VW13, Theorem 4.3]: from `N < t²` numbers the reduction makes `2t` instances
of Exact Triangle, each on `t` vertices per part (`Theorem21.convTemplate`).  Here
the instances are lists of integers, row by row, in the form in which a routine fills them
(`convAB`, `convBC`, `convAC`): every weight is a cell of the input, or minus a cell of the input,
at an index that is computed from the two vertices, or a filler if this index is out of range
(`cellOr`).

The three lists are the instance of the template (`triOf_conv`).  So there are `i`, `j` with
`x_i + x_j = x_{i+j}` if and only if one of the `2t` instances has a zero triangle
(`convolution3SUM_vecOf_iff`), and the weights are bounded by a bound for the numbers and the filler
(`abs_convAB_le`, `abs_convBC_le`, `abs_convAC_le`).
-/


namespace ThreeSumApsp.Spec

/-- Cell number `z` of a list of `N` numbers, or the filler `F` if `z` is not one of
`0, …, N - 1`. -/
def cellOr (N : ℕ) (F : ℤ) (X : List ℤ) (z : ℤ) : ℤ := if 0 ≤ z ∧ z < N then X.getD z.toNat 0 else F

/-- The weights `w(a,b) = x_{a t + b}`. -/
def convAB (t N : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ => cellOr N F X (q : ℤ)

/-- The weights `w(b,c) = x_{c t + s - b}` of instance number `s`. -/
def convBC (t N s : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ => cellOr N F X (((q % t : ℕ) : ℤ) * t + s - ((q / t : ℕ) : ℤ))

/-- The weights `w(a,c) = -x_{(a + c) t + s}` of instance number `s`.  The filler `-F` inside the
minus sign gives the weight `F`. -/
def convAC (t N s : ℕ) (F : ℤ) (X : List ℤ) : List ℤ :=
  (List.range (t * t)).map fun q : ℕ =>
    -cellOr N (-F) X ((((q / t : ℕ) : ℤ) + ((q % t : ℕ) : ℤ)) * t + s)

/-- The first list has `t²` entries. -/
@[simp] theorem length_convAB (t N : ℕ) (F : ℤ) (X : List ℤ) : (convAB t N F X).length = t * t := by
  simp [convAB]

/-- The second list has `t²` entries. -/
@[simp] theorem length_convBC (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    (convBC t N s F X).length = t * t := by
  simp [convBC]

/-- The third list has `t²` entries. -/
@[simp] theorem length_convAC (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    (convAC t N s F X).length = t * t := by
  simp [convAC]

/-- At an index in range `cellOr` reads the cell. -/
theorem cellOr_of_lt {N : ℕ} {F : ℤ} {X : List ℤ} {z : ℤ} {i : ℕ} (hz : z = i) (hi : i < N) :
    cellOr N F X z = X.getD i 0 := by
  subst hz
  rw [cellOr, if_pos ⟨Int.natCast_nonneg i, Int.ofNat_lt.2 hi⟩, Int.toNat_natCast]

/-- At an index out of range `cellOr` returns the filler. -/
theorem cellOr_of_not {N : ℕ} {F : ℤ} {X : List ℤ} {z : ℤ} (hz : ¬ (0 ≤ z ∧ z < N)) :
    cellOr N F X z = F :=
  if_neg hz

/-- A bound for the list and the filler is a bound for `cellOr`. -/
theorem abs_cellOr_le {N : ℕ} {F V : ℤ} {X : List ℤ} (hX : AbsLe X V) (hF : |F| ≤ V) (z : ℤ) :
    |cellOr N F X z| ≤ V := by
  unfold cellOr
  split_ifs
  · exact AbsLe.abs_getD_le ((abs_nonneg F).trans hF) hX _
  · exact hF

/-- The three lists are the instance that the template of the reduction produces. -/
theorem triOf_conv (t N s : ℕ) (F : ℤ) (X : List ℤ) :
    triOf t (convAB t N F X) (convBC t N s F X) (convAC t N s F X) =
      (Theorem21.convTemplate t N s).instantiate (vecOf N X) F := by
  unfold triOf TriangleTemplate.instantiate
  congr 1
  · funext a b
    rw [convAB, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt b.isLt), Theorem21.convTemplate_AB]
    split_ifs with h
    · exact cellOr_of_lt rfl h
    · exact cellOr_of_not fun h' => h (by exact_mod_cast h'.2)
  · funext b c
    rw [convBC, List.getD_map_range _ (Nat.mul_add_lt_mul b.isLt c.isLt),
      Nat.mul_add_div_of_lt c.isLt,
      Nat.mul_add_mod_of_lt c.isLt, Theorem21.convTemplate_BC]
    split_ifs with h
    · exact cellOr_of_lt (by push_cast [h.1]; ring) h.2
    · exact cellOr_of_not fun h' => h (by omega)
  · funext a c
    rw [convAC, List.getD_map_range _ (Nat.mul_add_lt_mul a.isLt c.isLt),
      Nat.mul_add_div_of_lt c.isLt,
      Nat.mul_add_mod_of_lt c.isLt, Theorem21.convTemplate_AC]
    split_ifs with h
    · exact congrArg Neg.neg (cellOr_of_lt (by push_cast; ring) h)
    · rw [cellOr_of_not fun h' => h (by exact_mod_cast h'.2), neg_neg]

section Bounds

variable {t N s : ℕ} {F V : ℤ} {X : List ℤ}

/-- The weights `w(a,b)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convAB_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convAB t N F X) V :=
  List.forall_mem_map.2 fun _ _ => abs_cellOr_le hX hF _

/-- The weights `w(b,c)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convBC_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convBC t N s F X) V :=
  List.forall_mem_map.2 fun _ _ => abs_cellOr_le hX hF _

/-- The weights `w(a,c)` are bounded by a bound for the numbers and the filler. -/
theorem abs_convAC_le (hX : AbsLe X V) (hF : |F| ≤ V) : AbsLe (convAC t N s F X) V :=
  List.forall_mem_map.2 fun _ _ => (abs_neg _).trans_le (abs_cellOr_le hX (by rwa [abs_neg]) _)

end Bounds

/-- **The reduction on lists.**  For a list of `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the `2t` instances, filled with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_vecOf_iff {t N : ℕ} (hN : 1 ≤ N) (hNt : N < t * t) {X : List ℤ} {U : ℤ}
    (hU : 0 ≤ U) (hX : AbsLe X U) :
    Convolution3SUM (vecOf N X) ↔
      ∃ s < 2 * t, (triOf t (convAB t N (2 * U + 1) X) (convBC t N s (2 * U + 1) X)
        (convAC t N s (2 * U + 1) X)).HasZeroTriangle := by
  simp only [triOf_conv]
  exact Theorem21.convolution3SUM_iff hN hNt fun i => AbsLe.abs_getD_le hU hX _

end ThreeSumApsp.Spec

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM from Exact Triangle: writing one instance

Theorem 21(a), after [VW13, Theorem 4.3].  convFill(t, N, s, F, x, ab, bc,
ac) writes the three weight matrices of instance number s of the reduction, each of t² cells, row
by row, to ab, bc, ac: w(a,b) = x[a t + b], w(b,c) = x[c t + s - b], w(a,c) = -x[(a + c) t + s], and
the filler F where the index is out of range.  One loop runs through the t² cells; it keeps the
number of the cell, its row and its column in three counters.

The proof follows the text.  pickStmt reads a cell of x or the filler (`pick_runs`); putStmt
computes an index, picks, and stores (`put_runs`); fillCells does this for the three matrices
(`cells_runs`); then the counters move on.  After q rounds the memory is `A.filled μ q`: the first q
cells of each matrix have been written (`filled_succ` is one round).  The result is
`convFill_meets`.
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace ConvFill

/-- The local variables of convFill: the arguments t (Side), N (Len), s (Inst), F (Filler), x
(Input), ab, bc, ac (MatAB, MatBC, MatAC); the row, the column and the number of the current cell
(Row, Col, Cell); an index into x and what is picked there (Index, Value); -F (NegFiller) and t²
(Area). -/
abbrev Side : ℕ := 0
@[inherit_doc Side] abbrev Len : ℕ := 1
@[inherit_doc Side] abbrev Inst : ℕ := 2
@[inherit_doc Side] abbrev Filler : ℕ := 3
@[inherit_doc Side] abbrev Input : ℕ := 4
@[inherit_doc Side] abbrev MatAB : ℕ := 5
@[inherit_doc Side] abbrev MatBC : ℕ := 6
@[inherit_doc Side] abbrev MatAC : ℕ := 7
@[inherit_doc Side] abbrev Row : ℕ := 8
@[inherit_doc Side] abbrev Col : ℕ := 9
@[inherit_doc Side] abbrev Cell : ℕ := 10
@[inherit_doc Side] abbrev Index : ℕ := 11
@[inherit_doc Side] abbrev Value : ℕ := 12
@[inherit_doc Side] abbrev NegFiller : ℕ := 13
@[inherit_doc Side] abbrev Area : ℕ := 14

end ConvFill

open ConvFill

/-- Value := x[Index] if 0 ≤ Index < N, and the content of local f, a filler, if not. -/
def pickStmt (f : ℕ) : Stmt :=
  .set Value (v f) ;;
  .ite (v Index <' k 0) .skip
    (.ite (v Index <' v Len) (.set Value (M (v Input +' v Index))) .skip)

/-- Computes the index ze, picks the cell there (or the filler in local f), and stores it, or minus
it if neg is set, into the current cell of the matrix whose address is in local dst. -/
def putStmt (ze : Expr) (f dst : ℕ) (neg : Bool) : Stmt :=
  .set Index ze ;; pickStmt f ;; .store (v dst +' v Cell) (if neg then k 0 -' v Value else v Value)

/-- The current cell of each of the three matrices. -/
def fillCells : Stmt :=
  putStmt (v Cell) Filler MatAB false ;;
  putStmt (v Col *' v Side +' v Inst -' v Row) Filler MatBC false ;;
  putStmt ((v Row +' v Col) *' v Side +' v Inst) NegFiller MatAC true

/-- One round: the current cell of each matrix, and on to the next cell. -/
def fillRound : Stmt :=
  fillCells ;; .set Cell (v Cell +' k 1) ;; nextPair Row Col Side

/-- convFill(t, N, s, F, x, ab, bc, ac). -/
def convFillBody : Stmt :=
  .set NegFiller (k 0 -' v Filler) ;;
  .set Area (v Side *' v Side) ;;
  .set Row (k 0) ;;
  .set Col (k 0) ;;
  .set Cell (k 0) ;;
  .while (v Cell <' v Area) fillRound

/-- The time of convFill. -/
def convFillTime (t : ℕ) : ℕ := 106 * (t * t) + 18

namespace ConvFill

/-! ## Picking and storing

The two lemmas of this section have the form of the rules for blocks: if R holds of the state in
which the part ends, then the part runs, within the limits, into R. -/

section parts

variable {μ : ℕ → ℤ} {R : State → Prop} {N x : ℕ} {F : ℤ} {X : List ℤ}

/-- The list X of N numbers stands at x, within the memory, and addresses fit in a word. -/
structure InputAt (lim : Limits) (μ : ℕ → ℤ) (x N : ℕ) (X : List ℤ) : Prop where
  seg : Seg μ x X
  len : X.length = N
  space : x + N ≤ lim.space
  addr : (lim.space : ℤ) ≤ lim.word

/-- pickStmt puts `cellOr N F X z` into Value and changes nothing else. -/
theorem pick_runs {loc : ℕ → ℤ} {f : ℕ} (z : ℤ)
    (h : R ⟨Function.update loc Value (cellOr N F X z), μ⟩) (hX : InputAt lim μ x N X)
    (hz : loc Index = z) (hN : loc Len = N) (hx : loc Input = x) (hf : loc f = F) :
    (pickStmt f).Runs lim ⟨loc, μ⟩ R := by
  obtain ⟨hseg, hlen, hspace, haddr⟩ := hX
  unfold pickStmt
  -- Value := f
  refine .seq ⟨trivial, ?_⟩
  by_cases hneg : z < 0
  · -- if Index < 0
    rw [cellOr_of_not (by omega)] at h
    exact .ite_pos ⟨trivial, by simpa [hf] using h⟩ (by simpa [hz] using hneg) (by simp; omega)
  refine .ite_neg ?_ (by simpa [hz] using hneg) (by simp; omega)
  by_cases hlt : z < N
  · -- if Index < N: Value := x[Index]
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hneg)
    rw [cellOr_of_lt rfl (by omega), ← hseg.getD (by omega)] at h
    refine .ite_pos ⟨?_, by simpa [hz, hx] using h⟩ (by simpa [hz, hN] using hlt) (by simp)
    simp [hz, hx, Limits.Addr, abs_le]
    omega
  · rw [cellOr_of_not (by omega)] at h
    exact .ite_neg ⟨trivial, by simpa [hf] using h⟩ (by simpa [hz, hN] using hlt) (by simp)

/-- putStmt stores `cellOr N F X z`, or minus it, into cell q of the matrix at D.  Of the locals it
changes only Index and Value. -/
theorem put_runs {l : List ℤ} {ze : Expr} {f dst : ℕ} {neg : Bool} (z : ℤ) (D q : ℕ)
    (h : R ⟨frame (setLocal (setLocal l Index z) Value (cellOr N F X z)),
      Function.update μ (D + q) (if neg then -cellOr N F X z else cellOr N F X z)⟩)
    (hX : InputAt lim μ x N X) (hD : D + q < lim.space) (hV : |cellOr N F X z| ≤ lim.word)
    (hze : ze.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hN : frame l Len = N := by rfl) (hx : frame l Input = x := by rfl)
    (hq : frame l Cell = q := by rfl) (hf : frame l f = F := by rfl)
    (hdst : frame l dst = D := by rfl)
    (hne : f ≠ Index ∧ dst ≠ Index ∧ dst ≠ Value := by decide) :
    (putStmt ze f dst neg).Runs lim ⟨frame l, μ⟩ R := by
  rw [← update_frame_setLocal, ← update_frame_setLocal] at h
  generalize frame l = loc at *
  obtain ⟨hfI, hdI, hdV⟩ := hne
  obtain ⟨hsafe, hval⟩ := hze
  have := hX.addr
  unfold putStmt
  -- Index := ze
  refine .seq ⟨hsafe, ?_⟩
  -- Value := x[Index] or the filler
  refine .seq (pick_runs z ?_ hX (by simp [hval]) (by simpa using hN) (by simpa using hx)
    (by simpa [hfI] using hf))
  -- dst[Cell] := Value or -Value
  cases neg
  · refine ⟨?_, by simpa [hval, hdI, hdV, hdst, hq] using h⟩
    simp [hdI, hdV, hdst, hq, Limits.Addr, abs_le]
    omega
  · refine ⟨?_, by simpa [hval, hdI, hdV, hdst, hq] using h⟩
    rw [abs_le] at hV
    simp [hdI, hdV, hdst, hq, Limits.Addr, abs_le]
    omega

end parts

/-! ## The data and the memory -/

/-- The arguments of convFill, with the list X that stands at x. -/
structure Args : Type where
  t : ℕ
  N : ℕ
  s : ℕ
  F : ℤ
  x : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  X : List ℤ

/-- What convFill assumes: there is at least one row; the input lies below the three matrices, which
follow each other within the memory; V bounds the input and the filler; words hold addresses, V and
the indices. -/
structure Ctx (lim : Limits) (μ : ℕ → ℤ) (A : Args) (V : ℕ) : Prop where
  side : 1 ≤ A.t
  addr : (lim.space : ℤ) ≤ lim.word
  input : Seg μ A.x A.X
  len : A.X.length = A.N
  belowAB : A.x + A.N ≤ A.ab
  belowBC : A.ab + A.t * A.t ≤ A.bc
  belowAC : A.bc + A.t * A.t ≤ A.ac
  space : A.ac + A.t * A.t ≤ lim.space
  inputLe : AbsLe A.X V
  fillerLe : |A.F| ≤ V
  valueLe : (V : ℤ) ≤ lim.word
  indexLe : ((2 * (A.t * A.t) + A.s + 1 : ℕ) : ℤ) ≤ lim.word

/-- What convFill achieves: the three matrices stand in the memory, and no cell before the first or
after the last of them has changed. -/
structure Post (A : Args) (μ μ' : ℕ → ℤ) : Prop where
  segAB : Seg μ' A.ab (convAB A.t A.N A.F A.X)
  segBC : Seg μ' A.bc (convBC A.t A.N A.s A.F A.X)
  segAC : Seg μ' A.ac (convAC A.t A.N A.s A.F A.X)
  same : SameOutside μ μ' A.ab (A.ac + A.t * A.t - A.ab)

/-- The index into x for cell q of the second matrix: c t + s - b for row b and column c. -/
def Args.idxBC (A : Args) (q : ℕ) : ℤ := ((q % A.t : ℕ) : ℤ) * A.t + A.s - ((q / A.t : ℕ) : ℤ)

/-- The index into x for cell q of the third matrix: (a + c) t + s for row a and column c. -/
def Args.idxAC (A : Args) (q : ℕ) : ℤ := (((q / A.t : ℕ) : ℤ) + ((q % A.t : ℕ) : ℤ)) * A.t + A.s

/-- The memory after q rounds: the first q cells of each matrix have been written. -/
def Args.filled (A : Args) (μ : ℕ → ℤ) (q : ℕ) : ℕ → ℤ :=
  wrote (wrote (wrote μ A.ab (fun i => cellOr A.N A.F A.X i) q)
    A.bc (fun i => cellOr A.N A.F A.X (A.idxBC i)) q)
    A.ac (fun i => -cellOr A.N (-A.F) A.X (A.idxAC i)) q

/-- The local variables before round q; z and w are what the last round has left in Index and
Value. -/
abbrev Args.locals (A : Args) (q : ℕ) (z w : ℤ) : List ℤ :=
  [A.t, A.N, A.s, A.F, A.x, A.ab, A.bc, A.ac, (q / A.t : ℕ), (q % A.t : ℕ), q, z, w, -A.F,
    (A.t * A.t : ℕ)]

section memory

variable {μ : ℕ → ℤ} {A : Args} {V q : ℕ}

/-- One round writes cell q of each matrix. -/
theorem filled_succ (C : Ctx lim μ A V) (hq : q < A.t * A.t) :
    Function.update (Function.update (Function.update (A.filled μ q)
      (A.ab + q) (cellOr A.N A.F A.X q)) (A.bc + q) (cellOr A.N A.F A.X (A.idxBC q)))
      (A.ac + q) (-cellOr A.N (-A.F) A.X (A.idxAC q)) = A.filled μ (q + 1) := by
  obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
  have offBC : A.ab + q < A.bc ∨ A.bc + q ≤ A.ab + q := by omega
  have offAC (y : ℕ) (hy : y ≤ A.bc + q) : y < A.ac ∨ A.ac + q ≤ y := by omega
  unfold Args.filled
  rw [update_wrote (offAC _ (by omega)), update_wrote offBC, wrote_succ,
    update_wrote (offAC _ le_rfl), wrote_succ, wrote_succ]

/-- No cell before the first matrix or after the last one changes. -/
theorem sameOutside_filled (C : Ctx lim μ A V) (hq : q ≤ A.t * A.t) :
    SameOutside μ (A.filled μ q) A.ab (A.ac + A.t * A.t - A.ab) := fun b hb => by
  obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
  have off (dst : ℕ) (h₁ : A.ab ≤ dst) (h₂ : dst ≤ A.ac) : b < dst ∨ dst + q ≤ b := by
    unfold Outside at hb
    omega
  rw [Args.filled, wrote_rest (off _ (by omega) le_rfl), wrote_rest (off _ (by omega) (by omega)),
    wrote_rest (off _ le_rfl (by omega))]

/-- At the end the three matrices stand in the memory. -/
theorem post_filled (C : Ctx lim μ A V) : Post A μ (A.filled μ (A.t * A.t)) where
  segAB i hi := by
    obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
    rw [length_convAB] at hi
    rw [Args.filled, wrote_rest (by omega), wrote_rest (by omega), wrote_done hi]
    simp [convAB]
  segBC i hi := by
    have := C.belowAC
    rw [length_convBC] at hi
    rw [Args.filled, wrote_rest (by omega), wrote_done hi]
    simp [convBC, Args.idxBC]
  segAC i hi := by
    rw [length_convAC] at hi
    rw [Args.filled, wrote_done hi]
    simp [convAC, Args.idxAC]
  same := sameOutside_filled C le_rfl

/-- The input is still there after q rounds. -/
theorem inputAt_filled (C : Ctx lim μ A V) (hq : q ≤ A.t * A.t) :
    InputAt lim (A.filled μ q) A.x A.N A.X where
  seg := C.input.keep (by light_keep [sameOutside_filled C hq, C.len, C.belowAB])
  len := C.len
  space := by
    have := C.belowAB
    have := C.belowBC
    have := C.belowAC
    have := C.space
    omega
  addr := C.addr

/-- A write to a cell of the matrices leaves the input alone. -/
theorem InputAt.write {μ' : ℕ → ℤ} (hX : InputAt lim μ' A.x A.N A.X) (C : Ctx lim μ A V)
    {b : ℕ} (hb : A.ab ≤ b) (w : ℤ) : InputAt lim (Function.update μ' b w) A.x A.N A.X :=
  { hX with seg := hX.seg.update_out (Or.inr (by have := C.len; have := C.belowAB; omega)) w }

/-- What is picked fits in a word. -/
theorem abs_cellOr_le_word (C : Ctx lim μ A V) (z : ℤ) :
    |cellOr A.N A.F A.X z| ≤ lim.word ∧ |cellOr A.N (-A.F) A.X z| ≤ lim.word :=
  ⟨(abs_cellOr_le C.inputLe C.fillerLe z).trans C.valueLe,
    (abs_cellOr_le C.inputLe (by rw [abs_neg]; exact C.fillerLe) z).trans C.valueLe⟩

end memory

/-! ## The loop -/

section loop

variable {μ : ℕ → ℤ} {A : Args} {V q : ℕ}

/-- The row and the column of a cell q < t² are below t, so the products that the two index
expressions form lie between 0 and 2t². -/
structure IndexBounds (t q : ℕ) : Prop where
  row : 0 ≤ (q : ℤ) / t ∧ (q : ℤ) / t < t
  col : 0 ≤ (q : ℤ) % t ∧ (q : ℤ) % t < t
  colSide : 0 ≤ (q : ℤ) % t * t ∧ (q : ℤ) % t * t ≤ t * t
  sumSide : 0 ≤ ((q : ℤ) / t + (q : ℤ) % t) * t ∧ ((q : ℤ) / t + (q : ℤ) % t) * t ≤ 2 * (t * t)
  side : (t : ℤ) ≤ t * t

theorem indexBounds {t : ℕ} (hq : q < t * t) : IndexBounds t q := by
  have hrow : q / t < t := Nat.div_lt_of_lt_mul hq
  have hcol : q % t < t := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hq)
  exact ⟨by exact_mod_cast And.intro (Nat.zero_le _) hrow,
    by exact_mod_cast And.intro (Nat.zero_le _) hcol,
    by exact_mod_cast And.intro (Nat.zero_le _) (Nat.mul_le_mul_right t hcol.le),
    by exact_mod_cast And.intro (Nat.zero_le _) ((Nat.mul_le_mul_right t
      (show q / t + q % t ≤ 2 * t by omega)).trans_eq (Nat.mul_assoc ..)),
    by exact_mod_cast Nat.le_mul_self t⟩

/-- fillCells writes cell q of each matrix. -/
theorem cells_runs {R : State → Prop} (C : Ctx lim μ A V) (hq : q < A.t * A.t) (z w : ℤ)
    (h : R ⟨frame (A.locals q (A.idxAC q) (cellOr A.N (-A.F) A.X (A.idxAC q))),
      A.filled μ (q + 1)⟩) :
    fillCells.Runs lim ⟨frame (A.locals q z w), A.filled μ q⟩ R := by
  obtain ⟨hrow, hcol, hcolSide, hsumSide, hside⟩ := indexBounds hq
  obtain ⟨hBC, hAC, hspace⟩ := And.intro C.belowBC (And.intro C.belowAC C.space)
  have := C.indexLe
  have hX := inputAt_filled C hq.le
  rw [← filled_succ C hq] at h
  unfold fillCells
  -- ab[q] := x[q] or F
  refine .seq (put_runs (q : ℤ) A.ab q ?_ hX (by omega) (abs_cellOr_le_word C _).1)
  -- bc[q] := x[c t + s - b] or F, for row b and column c
  refine .seq (put_runs (A.idxBC q) A.bc q ?_ (hX.write C (by omega) _) (by omega)
    (abs_cellOr_le_word C _).1 (by light_side [Args.idxBC]))
  -- ac[q] := -(x[(a + c) t + s] or -F), for row a and column c
  exact put_runs (A.idxAC q) A.ac q h ((hX.write C (by omega) _).write C (by omega) _) (by omega)
    (abs_cellOr_le_word C _).2 (by light_side [Args.idxAC])

/-- The invariant of the loop: before round q the counters stand at cell q, and the first q cells of
each matrix have been written. -/
def LoopInv (A : Args) (μ : ℕ → ℤ) (q : ℕ) (σ : State) : Prop :=
  ∃ z w : ℤ, σ = ⟨frame (A.locals q z w), A.filled μ q⟩

/-- Round q: cell q of each matrix is written, and the counters move on to cell q + 1. -/
theorem round_spec (C : Ctx lim μ A V) (hq : q < A.t * A.t) (z w : ℤ) :
    Ends lim P d fillRound ⟨frame (A.locals q z w), A.filled μ q⟩ fillRound.blockCost
      (LoopInv A μ (q + 1)) := by
  have := C.indexLe
  have : A.t ≤ A.t * A.t := Nat.le_mul_self _
  unfold fillRound
  -- the three cells
  refine Ends.next _ (Ends.block (cells_runs C hq z w ?_) le_rfl)
  -- Cell := Cell + 1
  refine Ends.setToThen ((q + 1 : ℕ) : ℤ) ?_ (by light_side) (by simp [nextPair])
  -- on to the next row and column
  exact Ends.nextPair ⟨_, _, rfl⟩ C.side (by omega) (by omega) rfl rfl rfl
    (hT := by simp [nextPair])

end loop

end ConvFill

/-- **convFill** writes the three matrices of instance number s, changes no cell before the first or
after the last of them, and takes O(t²) steps. -/
theorem convFill_meets {p : ℕ} (hp : P[p]? = some convFillBody) {μ : ℕ → ℤ} {A : Args} {V : ℕ}
    (C : Ctx lim μ A V) :
    Meets lim P p d [A.t, A.N, A.s, A.F, A.x, A.ab, A.bc, A.ac] μ (convFillTime A.t)
      fun _ μ' => Post A μ μ' := by
  have := C.indexLe
  have := abs_le.1 (C.fillerLe.trans C.valueLe)
  refine .of_body hp ?_
  unfold convFillBody convFillTime
  -- NegFiller := 0 - Filler; Area := Side * Side
  light_set (-A.F)
  light_set (A.t * A.t : ℕ)
  -- Row := 0; Col := 0; Cell := 0
  light_set 0
  light_set 0
  light_set 0
  -- while Cell < Area
  refine Ends.whileConst (LoopInv A μ) (A.t * A.t) fillRound.blockCost ?start ?round ?done
    (by simp [fillRound, fillCells, putStmt, pickStmt, nextPair]; omega)
  case start => exact ⟨0, 0, by simp [Args.filled, wrote_zero, Args.locals]⟩
  case round =>
    rintro q _ hq ⟨z, w, rfl⟩
    exact ⟨by light_side, by light_side, round_spec C hq z w⟩
  case done =>
    rintro _ ⟨z, w, rfl⟩
    exact ⟨by light_side, by light_side, post_filled C⟩

end Light.Sec3
end

section
open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/

namespace ConvHost

/-- The local variables of c3: the arguments N (Len; as local 0 it also takes the result), U
(Bound), x (Input), fr (Free); then t (Side), the number s of the instance (Inst), the answer so far
(Found), the result of a call (Answer), t² (Area) and the filler 2U + 1 (Filler). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Input : ℕ := 2
@[inherit_doc Len] abbrev Free : ℕ := 3
@[inherit_doc Len] abbrev Side : ℕ := 4
@[inherit_doc Len] abbrev Inst : ℕ := 5
@[inherit_doc Len] abbrev Found : ℕ := 6
@[inherit_doc Len] abbrev Answer : ℕ := 7
@[inherit_doc Len] abbrev Area : ℕ := 8
@[inherit_doc Len] abbrev Filler : ℕ := 9

end ConvHost

open ConvHost

/-- One round: writes instance number Inst at the free pointer and asks the solver. -/
def c3Round (pET pFill : ℕ) : Stmt :=
  .call pFill [v Side, v Len, v Inst, v Filler, v Input, v Free, v Free +' v Area,
    v Free +' k 2 *' v Area] Answer ;;
  .call pET [v Side, v Filler, v Free, v Free +' v Area, v Free +' k 2 *' v Area,
    v Free +' k 3 *' v Area] Answer ;;
  .ite (v Answer =' k 1) (.set Found (k 1)) .skip

/-- c3(N, U, x, fr), over the procedures pET (a solver of Exact Triangle), pSqrt (the integer square
root) and pFill (convFill).  The result is returned in local 0. -/
def c3Body (pET pSqrt pFill : ℕ) : Stmt :=
  .call pSqrt [v Len] Side ;;
  .set Side (v Side +' k 1) ;;
  .set Area (v Side *' v Side) ;;
  .set Filler (k 2 *' v Bound +' k 1) ;;
  .set Found (k 0) ;;
  .for Inst (k 2 *' v Side) (c3Round pET pFill) ;;
  .set Len (v Found)

/-- The time of one round: it writes 3t² cells and runs the solver on t vertices per part with the
bound 2U + 1. -/
def c3RoundTime (T : ℕ → ℕ → ℕ) (t U : ℕ) : ℕ := convFillTime t + 40 + T t (2 * U + 1)

/-- The time of the host: the square root, and 2t rounds with t = ⌊√N⌋ + 1. -/
def c3Time (T : ℕ → ℕ → ℕ) (N U : ℕ) : ℕ :=
  18 * Nat.sqrt N + 41 + 2 * (Nat.sqrt N + 1) * (c3RoundTime T (Nat.sqrt N + 1) U + 10)

/-- The need of the host: 3t² cells more than the solver, one level of calls more, and words for the
square root (3N + 4), the filler (2U + 1) and the indices (2t² + 2t). -/
def c3Need (r : ℕ → ℕ → Need) (N U : ℕ) : Need where
  word := (r (Nat.sqrt N + 1) (2 * U + 1)).word + 3 * N + 2 * U +
    2 * ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) + 2 * (Nat.sqrt N + 1) + 5
  cells := 3 * ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) + (r (Nat.sqrt N + 1) (2 * U + 1)).cells
  depth := (r (Nat.sqrt N + 1) (2 * U + 1)).depth + 1

namespace ConvHost

/-! ## One round -/

/-- What the host assumes about the program: it begins with the solver's program and holds the two
helpers. -/
structure Ctx (P R : Program) (pET pSqrt pFill : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop where
  sol : Solves etTask P pET T r
  sqrt : (P ++ R)[pSqrt]? = some sqrtBody
  fill : (P ++ R)[pFill]? = some convFillBody

/-- What the rounds assume: the input lies below the free pointer, N < t², and the limits allow for
the need of the host, written with t. -/
structure Ready (lim : Limits) (r : ℕ → ℕ → Need) (d : ℕ) (x : VecInst) (μ : ℕ → ℤ) (fr t : ℕ) :
    Prop where
  pre : x.Pre μ fr
  lenLt : x.N < t * t
  word : ((r t (2 * x.U + 1)).word : ℤ) + 3 * x.N + 2 * x.U + 2 * (t * t) + 2 * t + 5 ≤ lim.word
  cells : fr + (3 * (t * t) + (r t (2 * x.U + 1)).cells) ≤ lim.space
  addr : (lim.space : ℤ) ≤ lim.word
  depth : d + ((r t (2 * x.U + 1)).depth + 1) ≤ lim.depth

/-- The arguments of convFill for instance number s: the three matrices follow each other at the
free pointer, and the filler is 2U + 1. -/
def fillArgs (x : VecInst) (fr t s : ℕ) : ConvFill.Args :=
  ⟨t, x.N, s, 2 * x.U + 1, x.a, fr, fr + t * t, fr + 2 * (t * t), x.X⟩

/-- Instance number s of the reduction, at the free pointer. -/
def inst (x : VecInst) (fr t s : ℕ) : TriInst :=
  ⟨t, 2 * x.U + 1, fr, fr + t * t, fr + 2 * (t * t), convAB t x.N (2 * x.U + 1) x.X,
    convBC t x.N s (2 * x.U + 1) x.X, convAC t x.N s (2 * x.U + 1) x.X⟩

/-- Instance number s has a zero triangle. -/
def Hit (x : VecInst) (t s : ℕ) : Prop :=
  (triOf t (inst x 0 t s).AB (inst x 0 t s).BC (inst x 0 t s).AC).HasZeroTriangle

/-- The local variables in round s. -/
abbrev locals (x : VecInst) (fr t s : ℕ) (found res : ℤ) : List ℤ :=
  [x.N, x.U, x.a, fr, t, s, found, res, (t * t : ℕ), 2 * x.U + 1]

variable {P R : Program} {pET pSqrt pFill : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {lim : Limits}
  {d : ℕ} {x : VecInst} {μ μ' : ℕ → ℤ} {fr t s : ℕ}

/-- There is at least one vertex per part. -/
theorem Ready.one_le (H : Ready lim r d x μ fr t) : 1 ≤ t :=
  Nat.pos_of_ne_zero fun h => by simpa [h] using H.lenLt

/-- The numbers of the input are bounded by 2U + 1. -/
theorem Ready.input_le (H : Ready lim r d x μ fr t) : AbsLe x.X ((2 * x.U + 1 : ℕ) : ℤ) :=
  fun e he => (H.pre.le e he).trans (by push_cast; omega)

/-- The filler is bounded by 2U + 1. -/
theorem abs_filler_le (x : VecInst) : |2 * (x.U : ℤ) + 1| ≤ ((2 * x.U + 1 : ℕ) : ℤ) := by
  rw [abs_of_nonneg (by positivity)]
  push_cast
  exact le_rfl

/-- convFill can be called in every round. -/
theorem fill_ctx (H : Ready lim r d x μ fr t) (hk : Kept μ μ' fr) (hs : s < 2 * t) :
    ConvFill.Ctx lim μ' (fillArgs x fr t s) (2 * x.U + 1) where
  side := H.one_le
  addr := H.addr
  input := H.pre.seg.of_sameOn hk fun i hi => by have := H.pre.below; have := H.pre.len; omega
  len := H.pre.len
  belowAB := H.pre.below
  belowBC := le_rfl
  belowAC := by simp only [fillArgs]; omega
  space := by have := H.cells; simp only [fillArgs]; omega
  inputLe := H.input_le
  fillerLe := abs_filler_le x
  valueLe := by have := H.word; have := mul_self_nonneg (t : ℤ); push_cast; omega
  indexLe := by have := H.word; simp only [fillArgs]; push_cast; omega

/-- After convFill the instance lies in the memory. -/
theorem inst_pre {μ₁ : ℕ → ℤ} (H : Ready lim r d x μ fr t)
    (hpost : ConvFill.Post (fillArgs x fr t s) μ' μ₁) :
    (inst x fr t s).Pre μ₁ (fr + 3 * (t * t)) where
  n_pos := H.one_le
  U_pos := by simp [inst]
  lenAB := by simp [inst]
  lenBC := by simp [inst]
  lenAC := by simp [inst]
  segAB := hpost.segAB
  segBC := hpost.segBC
  segAC := hpost.segAC
  leAB := abs_convAB_le H.input_le (abs_filler_le x)
  leBC := abs_convBC_le H.input_le (abs_filler_le x)
  leAC := abs_convAC_le H.input_le (abs_filler_le x)
  belowAB := by simp only [inst]; omega
  belowBC := by simp only [inst]; omega
  belowAC := by simp only [inst]; omega

/-- The limits allow for the solver, after the three matrices and one level of calls down. -/
theorem solver_ok (H : Ready lim r d x μ fr t) :
    (r t (2 * x.U + 1)).Ok lim (fr + 3 * (t * t)) (d + 1) where
  word := by have := H.word; have := mul_self_nonneg (t : ℤ); omega
  cells := by have := H.cells; omega
  space := H.addr
  depth := by have := H.depth; omega

/-- **One round**: if Found says whether one of the instances before s has a zero triangle, then
afterwards it says so of the instances up to s.  No cell below the free pointer changes. -/
theorem round_spec (C : Ctx P R pET pSqrt pFill T r) (H : Ready lim r d x μ fr t)
    (hk : Kept μ μ' fr) (hs : s < 2 * t) (res : ℤ) :
    Ends lim (P ++ R) d (c3Round pET pFill)
      ⟨frame (locals x fr t s (flag (∃ s' < s, Hit x t s')) res), μ'⟩ (c3RoundTime T t x.U)
      fun σ' => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals x fr t s (flag (∃ s' < s + 1, Hit x t s')) res'), μ''⟩ ∧
          Kept μ μ'' fr := by
  obtain ⟨hword, hcells, haddr, hdepth⟩ := And.intro H.word (And.intro H.cells
    (And.intro H.addr H.depth))
  have := mul_self_nonneg (t : ℤ)
  unfold c3Round c3RoundTime
  -- Answer := convFill(t, N, s, 2U + 1, x, fr, fr + t², fr + 2t²)
  refine Ends.callToThen (T' := convFillTime t) (convFill_meets C.fill (fill_ctx H hk hs)) ?_
    (by light_side [fillArgs])
  rintro - μ₁ hpost
  -- Answer := et(t, 2U + 1, fr, fr + t², fr + 2t², fr + 3t²)
  refine Ends.callToThen (T' := T t (2 * x.U + 1)) (C.sol.meets R (inst x fr t s) (fr + 3 * (t * t))
    (inst_pre H hpost) (solver_ok H)) ?_ (by light_side [etTask, inst])
  rintro res' μ₂ ⟨hres, hk₂⟩
  replace hres : res' = flag (Hit x t s) := hres
  -- both calls write only from the free pointer on
  have hkept : Kept μ μ₂ fr := (hk.then hpost.same fun b hb => ⟨hb, Or.inl hb⟩).then hk₂
    fun b hb => ⟨hb, by omega⟩
  -- if Answer = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- Found := 1
    have hit : Hit x t s := flag_eq_one_iff.1 (by simpa [hres] using hyes)
    exact Ends.setTo 1
      ⟨res', μ₂, by rw [flag_of (Nat.exists_lt_succ_right.2 (Or.inr hit))]; rfl, hkept⟩
  · have miss : ¬ Hit x t s := fun hit => hno (by simp [hres, flag_of hit])
    exact Ends.skip
      ⟨res', μ₂, by rw [flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left miss))]; rfl, hkept⟩

/-! ## The host -/

/-- The invariant of the loop: before round s, Found says whether one of the instances before s has
a zero triangle, and no cell below the free pointer has changed. -/
def LoopInv (x : VecInst) (μ : ℕ → ℤ) (fr t s : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr t s (flag (∃ s' < s, Hit x t s')) res), μ'⟩ ∧ Kept μ μ' fr

/-- The need of the host allows for the rounds. -/
theorem ready (hpre : x.Pre μ fr) (hok : (c3Need r x.N x.U).Ok lim fr d) :
    Ready lim r d x μ fr (Nat.sqrt x.N + 1) where
  pre := hpre
  lenLt := Nat.lt_succ_sqrt x.N
  word := by have := hok.word; simp only [c3Need] at this; push_cast at this ⊢; omega
  cells := hok.cells
  addr := hok.space
  depth := hok.depth

end ConvHost

open ConvHost in
/-- **The host is correct**, in every program that begins with the solver's and contains the two
helpers. -/
theorem c3_spec {P R : Program} {pET pSqrt pFill : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (C : Ctx P R pET pSqrt pFill T r) {lim : Limits} {d : ℕ} {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (c3Need r x.N x.U).Ok lim fr d) :
    Ends lim (P ++ R) d (c3Body pET pSqrt pFill) ⟨frame [(x.N : ℤ), x.U, x.a, fr], μ⟩
      (c3Time T x.N x.U) fun σ' =>
        σ'.loc 0 = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have H := ready hpre hok
  unfold c3Time
  have : Nat.sqrt x.N ≤ x.N := Nat.sqrt_le_self _
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.sqrt x.N + 1 := ⟨_, rfl⟩
  rw [← ht] at H ⊢
  obtain ⟨hword, hdepth⟩ := And.intro H.word H.depth
  have := mul_self_nonneg (t : ℤ)
  unfold c3Body
  -- Side := sqrt(N)
  light_call (sqrt_meets (K := x.N) C.sqrt μ (by push_cast; omega)) with _ μ₀ ⟨rfl, hμ⟩
  obtain rfl := hμ.symm
  -- Side := Side + 1; Area := Side * Side; Filler := 2 * Bound + 1; Found := 0
  light_set t
  light_set (t * t : ℕ)
  light_set (2 * (x.U : ℤ) + 1)
  light_set 0
  -- for Inst < 2 * Side
  refine Ends.next _ (Ends.for (LoopInv x μ fr t) (2 * t) (c3RoundTime T t x.U)
    ?start ?round ?done ?bound (hT := le_rfl))
  case start =>
    exact ⟨0, μ, by simp [update_frame_setLocal, locals, flag_of_not], SameOn.refl⟩
  case round =>
    rintro s _ hs - ⟨res, μ', rfl, hk⟩
    refine (round_spec C H hk hs res).mono le_rfl ?_
    rintro _ ⟨res', μ'', rfl, hk'⟩
    exact ⟨rfl, res', μ'', by simp [update_frame_setLocal, locals], hk'⟩
  case done =>
    rintro _ - ⟨res, μ', rfl, hk⟩
    -- Len := Found: the result
    exact Ends.setTo (flag (∃ s' < 2 * t, Hit x t s'))
      ⟨flag_congr (convolution3SUM_vecOf_iff hpre.N_pos H.lenLt (by positivity) hpre.le).symm, hk⟩
  case bound =>
    rintro s _ - - ⟨res, μ', rfl, -⟩
    exact ⟨by light_side, by simp⟩

/-! ## The need is polynomially bounded -/

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_c3Need {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (c3Need r) := by
  unfold c3Need
  poly_need [hr.word, hr.cells, hr.depth]

/-- **Convolution-3SUM from Exact Triangle**: the host makes a solver of Convolution-3SUM from every
solver of Exact Triangle. -/
theorem isHost_c3 : IsHost etTask c3Task c3Time c3Need := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_c3Need hr⟩
  refine ⟨[sqrtBody, convFillBody, c3Body p P.length (P.length + 1)], P.length + 2,
    c3Body p P.length (P.length + 1), by simp, ?_⟩
  intro R lim d x μ fr hpre hok
  rw [List.append_assoc]
  exact c3_spec ⟨hsol, by simp, by simp⟩ hpre hok

end Light.Sec3
end
