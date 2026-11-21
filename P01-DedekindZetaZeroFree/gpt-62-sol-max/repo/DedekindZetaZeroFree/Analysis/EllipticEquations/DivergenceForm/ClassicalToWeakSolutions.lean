module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

open MeasureTheory KPContLocalNorm Raw

theorem coordinateDerivativeList_contDiffOn_open {n : ℕ} {U : Set (Space n)}
    (hU : IsOpen U) {u : Space n → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (l : List (Fin n)) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem coordinateDerivative_memLp_of_closedBall {n k : ℕ} (B : LocalBall n)
    {U : Set (Space n)} (hU : IsOpen U)
    (hclosed : Metric.closedBall B.center B.radius ⊆ U)
    {u : Space n → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (α : MultiIndex n k) :
    MemLp (coordinateDerivative α u) 2 (volume.restrict B.carrier) := by
  have hsub : B.carrier ⊆ Metric.closedBall B.center B.radius :=
    Metric.ball_subset_closedBall
  have hcompact : IsCompact (Metric.closedBall B.center B.radius) :=
    isCompact_closedBall _ _
  have hc := (coordinateDerivativeList_contDiffOn_open hU hu α.directions).continuousOn
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hc.mono hclosed)
  have hfinite : volume B.carrier < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) hcompact.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict B.carrier) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  apply MemLp.of_enorm_bound ((hc.mono (hsub.trans hclosed)).aestronglyMeasurable
    Metric.isOpen_ball.measurableSet) ENNReal.ofReal_ne_top
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact (ofReal_norm_eq_enorm _).symm.le.trans (ENNReal.ofReal_le_ofReal (hC x (hsub hx)))


@[simp] theorem coordinateDerivative_zeroIndex {n k : ℕ} (u : Space n → ℂ) :
    coordinateDerivative (zeroIndex n k) u = u := by
  have hnil : (List.finRange n).flatMap (fun _ => ([] : List (Fin n))) = [] :=
    List.flatMap_eq_nil_iff.mpr (by simp)
  simp [coordinateDerivative, zeroIndex, MultiIndex.directions, coordinateDerivativeList, hnil]

@[simp] theorem firstIndex_directions {n : ℕ} (i : Fin n) :
    (firstIndex i).directions = [i] := by
  classical
  have h : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      l.flatMap (fun j => if j = i then [j] else []) = [i] := by
    intro l hn hi
    induction l with
    | nil => simp at hi
    | cons j l ih =>
      simp only [List.nodup_cons] at hn
      simp only [List.mem_cons] at hi
      simp only [List.flatMap_cons]
      by_cases hj : j = i
      · subst j
        rw [if_pos rfl]
        have hz : l.flatMap (fun j => if j = i then [j] else []) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro j hj
          rw [if_neg (by intro he; subst j; exact hn.1 hj)]
        simp [hz]
      · rw [if_neg hj]
        simpa using ih hn.2 (hi.resolve_left (Ne.symm hj))
  rw [MultiIndex.directions]
  convert h (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i) using 1
  apply List.flatMap_congr
  intro j _
  by_cases hj : j = i <;> simp [firstIndex, hj]

def derivativeTest {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) : TestFunction B.toOpens ℂ ⊤ :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ

@[simp] theorem derivativeTest_apply {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) (x : Space n) :
    derivativeTest φ i x = coordinateDerivativeList [i] (fun y => φ y) x := by
  rw [derivativeTest, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv



def conjugateTest {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) : TestFunction B.toOpens ℂ ⊤ :=
  TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap φ

@[simp] theorem conjugateTest_apply {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (x : Space n) :
    conjugateTest φ x = star (φ x) := rfl

@[simp] theorem coordinateDerivative_conjugateTest {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) (x : Space n) :
    coordinateDerivativeList [i] (fun y => conjugateTest φ y) x =
      star (coordinateDerivativeList [i] (fun y => φ y) x) := by
  simp only [coordinateDerivativeList, conjugateTest_apply, fderiv_star]
  rfl





end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
