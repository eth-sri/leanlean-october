module

public import GS.NonmanifoldClosure.ChartRetractions
public import GS.Nonmanifold.RankOneGeometry

@[expose] public section


/-!
# Regular pivot charts of the rank-one cone, and regular points arbitrarily near zero

For the `(m+1)`-row real rank-one cone with a Euclidean factor, the explicit pivot chart
has dimension card(ι)+card(κ)+m. One rank-one ray suffices to find regular points in each
-/
noncomputable section
open Matrix GS GS.NonmanifoldObstruction GS.NonmanifoldFinal GS.GlobalGeometry
namespace GS.NonmanifoldClosure

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {m : ℕ}

abbrev Cone (ι κ : Type*) [Fintype κ] (m : ℕ) :=
  (ι → ℝ) × {W : Matrix (Fin (m+1)) κ ℝ // W.rank ≤ 1}

/-- Pivot coordinates: the first row and the remaining row ratios. -/
def pivotProductHomeomorph (j : κ) : {p : Cone ι κ m // p.2.val 0 j ≠ 0} ≃ₜ
    {q : (ι → ℝ) × ((κ → ℝ) × (Fin m → ℝ)) // q.2.1 j ≠ 0} where
  toFun p := ⟨(p.1.1, p.1.2.1 0, fun i => p.1.2.1 i.succ j / p.1.2.1 0 j), p.2⟩
  invFun q := ⟨(q.1.1, ⟨vecMulVec (Fin.cons 1 q.1.2.2) q.1.2.1, rank_vecMulVec_le _ _⟩), (one_mul _).trans_ne q.2⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
    ext i k
    cases i using Fin.cases with
    | zero => simp [vecMulVec]
    | succ i =>
      have := rank_le_one_minor _ p.1.2.2 i.succ 0 j k
      simp [vecMulVec]
      grind
  right_inv q := by
    refine Subtype.ext (Prod.ext rfl (Prod.ext ?_ ?_)) <;> ext <;> simp [vecMulVec, q.2]
  continuous_toFun := .subtype_mk (by fun_prop (disch := simp)) _
  continuous_invFun := by fun_prop

def coordsEuclidean : (ι → ℝ) × ((κ → ℝ) × (Fin m → ℝ)) ≃ₜ
    Eucl (Fintype.card ι + Fintype.card κ + m) :=
  (((Homeomorph.refl _).prodCongr sumCoordinates).trans sumCoordinates).trans
    ((reindexReal (Fintype.equivFinOfCardEq (by simp [add_assoc]))).trans
      (EuclideanSpace.equiv _ ℝ).symm.toHomeomorph)

section
variable (j : κ)
/-- Genuine open chart of the cone. -/
def pivotProductChart :
    OpenEuclideanChart (Cone ι κ m) (Fintype.card ι + Fintype.card κ + m) where
  source := {p | p.2.val 0 j ≠ 0}
  target := coordsEuclidean '' {q | q.2.1 j ≠ 0}
  source_open := isOpen_ne_fun (by fun_prop) (by fun_prop)
  target_open := coordsEuclidean.isOpenMap _ (isOpen_ne_fun (by fun_prop) (by fun_prop))
  chart := (pivotProductHomeomorph j).trans (Homeomorph.image coordsEuclidean _)

/-- Every open vertex-neighborhood meets the regular pivot chart. -/
theorem exists_regular_in_open (U : Set (Cone ι κ m)) (hU : IsOpen U)
    (h0 : (0, ⟨0, by simp⟩) ∈ U) : ∃ p ∈ U, p ∈ (pivotProductChart (ι := ι) j).source := by
  let r (t : ℝ) : Cone ι κ m :=
    (0, ⟨vecMulVec (t • Pi.single 0 1) (Pi.single j 1), rank_vecMulVec_le _ _⟩)
  have hr : Continuous r := by fun_prop
  have h : r 0 = (0, ⟨0, by simp⟩) := by aesop
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ((hU.preimage hr).mem_nhds (h ▸ h0))
  exact ⟨r (δ/2), hball (by simp [abs_of_pos hδ]; linarith), by simp [r, pivotProductChart, vecMulVec_apply, hδ.ne']⟩

end

end GS.NonmanifoldClosure
