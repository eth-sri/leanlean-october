import Mathlib.Tactic
import GS.NonmanifoldClosure.ChartRetractions
import Mathlib.Analysis.Normed.Module.FiniteDimension
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix GS.NonmanifoldClosure
namespace GS.Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable (n : ℕ)

variable (j : κ)

abbrev ConeProduct  (ι κ : Type*) [Fintype κ] :=
  (ι → ℝ) × {W : Matrix (Fin (n+1)) κ ℝ // W.rank ≤ 1}
abbrev RankCoordinates  (ι κ : Type*) :=
  (ι → ℝ) × ((κ → ℝ) × (Fin n → ℝ))
def rankPivotSource   : Set (ConeProduct n ι κ) := {p | p.2.val 0 j ≠ 0}
def rankPivotDomain   : Set (RankCoordinates n ι κ) := {p | p.2.1 j ≠ 0}

variable [DecidableEq κ]
def rankPivot   : rankPivotSource n (ι := ι) j ≃ₜ
    rankPivotDomain n (ι := ι) j where
  toFun p := ⟨(p.val.1,(p.val.2.val 0,
    fun i => p.val.2.val i.succ j / p.val.2.val 0 j)),p.property⟩
  invFun p := ⟨(p.val.1,⟨vecMulVec (Fin.cons 1 p.val.2.2) p.val.2.1,
    Matrix.rank_vecMulVec_le _ _⟩),mul_ne_zero one_ne_zero p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i k
      refine Fin.cases ?_ (fun a => ?_) i
      · simp [vecMulVec]
      · change (p.val.2.val a.succ j / p.val.2.val 0 j) * p.val.2.val 0 k = _
        obtain ⟨u,z,he⟩ := GS.RankOne.exists_outer p.val.2.val p.val.2.property
        have hn : p.val.2.val 0 j ≠ 0 := p.property
        rw [← he] at hn ⊢
        dsimp [vecMulVec] at hn ⊢
        field_simp [left_ne_zero_of_mul hn,right_ne_zero_of_mul hn]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext <;> simp_all [vecMulVec]
      · ext a; simp [vecMulVec,show p.val.2.1 j ≠ 0 from p.property]
  continuous_toFun := by
    have hW : Continuous (fun p : rankPivotSource n (ι := ι) j => p.val.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · exact (continuous_apply 0).comp hW
      · apply continuous_pi
        intro i
        exact ((continuous_apply j).comp ((continuous_apply i.succ).comp hW)).div
          ((continuous_apply j).comp ((continuous_apply 0).comp hW)) (fun p => p.property)
  continuous_invFun := by fun_prop

def rankCoordinatesEuclidean  : RankCoordinates n ι κ ≃ₜ
    Eucl (Fintype.card ι + Fintype.card κ + n) :=
  (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (by simp_all [Nat.add_assoc,Module.finrank_prod])).toHomeomorph

def rankPivotChart   : OpenEuclideanChart (ConeProduct n ι κ)
    (Fintype.card ι + Fintype.card κ + n) where
  source := rankPivotSource n j
  target := rankCoordinatesEuclidean n '' rankPivotDomain n j
  source_open := isOpen_ne_fun ((continuous_apply j).comp ((continuous_apply 0).comp
    (continuous_subtype_val.comp continuous_snd))) continuous_const
  target_open := (rankCoordinatesEuclidean n).isOpenMap _
    (isOpen_ne_fun (by fun_prop) continuous_const)
  chart := (rankPivot n j).trans ((rankCoordinatesEuclidean n).image _)

def rankRay   (t : ℝ) : ConeProduct n ι κ :=
  (0,⟨vecMulVec (Fin.cons t 0) (fun k => if k=j then 1 else 0),
    Matrix.rank_vecMulVec_le _ _⟩)

theorem continuous_rankRay   : Continuous (rankRay n (ι := ι) j) := by
  fun_prop [rankRay]

@[simp] theorem rankRay_zero   : rankRay n (ι := ι) j 0 = (0,⟨0,by simp⟩) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    ext i k
    refine Fin.cases ?_ (fun a => ?_) i <;> simp [rankRay,vecMulVec]

@[simp] theorem rankRay_pivot   (t : ℝ) :
    (rankRay n (ι := ι) j t).2.val 0 j = t := by simp [rankRay,vecMulVec]

theorem exists_regular   (U : Set (ConeProduct n ι κ))
    (hU : IsOpen U) (hzero : (0,⟨0,by simp⟩) ∈ U) :
    ∃ p, p ∈ U ∧ p ∈ (rankPivotChart n (ι := ι) j).source := by
  have hopen := hU.preimage (continuous_rankRay n j)
  have hz : (0 : ℝ) ∈ rankRay n j ⁻¹' U := by simpa using hzero
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  refine ⟨rankRay n j (δ/2),hball ?_,?_⟩
  · simp_all [abs_of_pos,Metric.mem_ball]
  · change (rankRay n j (δ/2)).2.val 0 j ≠ 0
    rw [rankRay_pivot]
    linarith
end GS.Topology
