module
public import GS.Results.CellRank
public import GS.Topology.Germs
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
@[expose] public section

/-! A single pivot chart works for *any* number of rows. Read the first
row and the remaining row multipliers; decoding is one outer product. -/
noncomputable section
open Matrix Set Filter GS.Local
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace GS.RankLocus
variable {κ : Type} [Fintype κ] {r e : ℕ}
abbrev Locus (r : ℕ) (κ : Type) [Fintype κ] := {X : Matrix (Fin r) κ ℝ // X.rank ≤ 1}
def tip : Locus r κ := ⟨0,by simp⟩
def outer {m} (u : Fin m → ℝ) (v : κ → ℝ) : Locus m κ := ⟨vecMulVec u v,rank_vecMulVec_le ..⟩
@[fun_prop] lemma continuous_row (i : Fin r) : Continuous (fun X : Locus r κ => X.val i) := (continuous_apply i).comp continuous_subtype_val
@[fun_prop] lemma continuous_entry (i : Fin r) (j : κ) : Continuous (fun X : Locus r κ => X.val i j) := (continuous_apply j).comp (continuous_row i)
@[simp] lemma outer_zero (u : Fin r → ℝ) : outer u (0 : κ → ℝ) = tip := Subtype.ext (by ext; simp [outer,tip,vecMulVec])
@[simp] lemma zero_outer (v : κ → ℝ) : outer (0 : Fin r → ℝ) v = tip := Subtype.ext (by ext; simp [outer,tip,vecMulVec])
lemma factors (X : Locus r κ) : ∃ u v, outer u v = X := by
  obtain ⟨A,B,h⟩ := (Results.CellRank.rank_le_card_iff_factorization (τ := Fin 1) X.val).1 (by exact X.property)
  exact ⟨A.col 0,B 0,Subtype.ext (by ext; simp [outer,h,mul_apply,vecMulVec])⟩

abbrev Space (e r : ℕ) (κ : Type) [Fintype κ] := (Fin e → ℝ) × Locus r κ
end GS.RankLocus
