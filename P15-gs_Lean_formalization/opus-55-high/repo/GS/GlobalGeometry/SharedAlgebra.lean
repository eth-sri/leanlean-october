module

public import GS.GlobalGeometry.ExactSharing
public import GS.Continuation.ExponentialBasics
public import GS.Shared.Algebra

@[expose] public section


/-!
# Algebra and exponential closure of actual tied blocks

Full physical blocks have identical local index sets. This gives closure of
actual entry sharing under multiplication and under the matrix exponential.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation Filter
open scoped BigOperators Topology

namespace GS.GlobalGeometry

variable {n b : ℕ} {τ : ℕ → ℕ} {A B C : Mat n}

namespace TiedEntries


theorem smul (a : ℝ) (hA : TiedEntries b τ A) : TiedEntries b τ (a • A) := by
  intro i j i' j' h h' hτ hi hj
  aesop


end TiedEntries

namespace TiedEntries

theorem pow (hb : 0 < b) (hbn : b ∣ n)
    (hAs : BlockDiagonal b A) (hA : TiedEntries b τ A) (k : ℕ) :
    TiedEntries b τ (A ^ k) := by
  induction k with
  | zero => simpa [TiedEntries, Shared.Tied] using Shared.Tied.one (𝕜 := ℝ) (n := n) b τ
  | succ k ih =>
    simpa [pow_succ, TiedEntries, Shared.Tied] using Shared.Tied.mul hb hbn (supported_pow hAs k) ih hA

theorem sum {α : Type*} (s : Finset α) (F : α → Mat n)
    (hF : ∀ a ∈ s, TiedEntries b τ (F a)) : TiedEntries b τ (∑ a ∈ s, F a) := by
  classical
  intro i j i' j' h h' hτ hi hj
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  aesop

end TiedEntries

theorem expLine_tied (hb : 0 < b) (hbn : b ∣ n)
    (hCs : BlockDiagonal b C) (hC : TiedEntries b τ C) (t : ℝ) :
    TiedEntries b τ (expLine C t) := by
  refine IsClosed.mem_of_tendsto (?_ : IsClosed {A : Mat n | TiedEntries b τ A}) (matrixExp_hasSum _)
    (.of_forall fun s => TiedEntries.sum s _ fun k _ => (TiedEntries.pow hb hbn (Supported.smul t hCs) (hC.smul t) k).smul _)
  simp only [TiedEntries, Set.setOf_forall]
  repeat' first | apply isClosed_iInter; intro
  exact isClosed_eq (by fun_prop) (by fun_prop)




end GS.GlobalGeometry
