module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalNorm

open MeasureTheory Topology

private def iteratedDerivativeTest {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) (φ : TestFunction B.toOpens ℂ ⊤) :
    TestFunction B.toOpens ℂ ⊤ :=
  match l with
  | [] => φ
  | i :: l => TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1)
      (iteratedDerivativeTest l φ)

private theorem iteratedDerivativeTest_apply {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) (φ : TestFunction B.toOpens ℂ ⊤) :
    (fun x => iteratedDerivativeTest l φ x) = coordinateDerivativeList l (fun x => φ x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [iteratedDerivativeTest, coordinateDerivativeList]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM]
    rw [TestFunction.fderivCLM_apply_of_le _ (by simp)]
    change fderiv ℝ (fun y => iteratedDerivativeTest l φ y) x _ = _
    rw [ih]

private def pairTest {n : ℕ} (B : LocalBall n) (φ : TestFunction B.toOpens ℂ ⊤) :
    BallL2 B →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume.restrict B.carrier) 2 2).flip
    ((φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ)
private theorem pairTest_eq {n : ℕ} (B : LocalBall n) (φ : TestFunction B.toOpens ℂ ⊤)
    (u : BallL2 B) : pairTest B φ u = ∫ x in B.carrier, u x * φ x := by
  rw [pairTest, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).coeFn_toLp]
    with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

private theorem isWeakDerivative_iff_pairTest {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u d : BallL2 B) : IsWeakDerivative B α u d ↔
      ∀ φ : TestFunction B.toOpens ℂ ⊤,
        pairTest B (iteratedDerivativeTest α.directions φ) u = (-1 : ℂ) ^ α.degree * pairTest B φ d := by
  simp only [IsWeakDerivative, pairTest_eq, iteratedDerivativeTest_apply, coordinateDerivative]

theorem weak_derivative_sub {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u₁ u₂ d₁ d₂ : BallL2 B)
    (h₁ : IsWeakDerivative B α u₁ d₁) (h₂ : IsWeakDerivative B α u₂ d₂) :
    IsWeakDerivative B α (u₁ - u₂) (d₁ - d₂) := by
  rw [isWeakDerivative_iff_pairTest] at h₁ h₂ ⊢
  intro φ
  rw [map_sub, map_sub, h₁ φ, h₂ φ, mul_sub]

theorem weak_derivative_smul {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (c : ℂ) (u d : BallL2 B) (h : IsWeakDerivative B α u d) :
    IsWeakDerivative B α (c • u) (c • d) := by
  rw [isWeakDerivative_iff_pairTest] at h ⊢
  intro φ
  simp only [map_smul, smul_eq_mul, h φ, mul_left_comm]

theorem weakDerivative_zero {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k) :
    IsWeakDerivative B α (0 : BallL2 B) 0 := by
  simp [isWeakDerivative_iff_pairTest]

private theorem weakDerivative_isClosed {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k) :
    IsClosed {uv : BallL2 B × BallL2 B | IsWeakDerivative B α uv.1 uv.2} := by
  have heq : {uv : BallL2 B × BallL2 B | IsWeakDerivative B α uv.1 uv.2} =
      ⋂ φ : TestFunction B.toOpens ℂ ⊤,
        {uv | pairTest B (iteratedDerivativeTest α.directions φ) uv.1 =
          (-1 : ℂ) ^ α.degree * pairTest B φ uv.2} := by
    ext uv
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, isWeakDerivative_iff_pairTest]
  rw [heq]
  apply isClosed_iInter
  intro φ
  exact isClosed_eq ((pairTest B _).continuous.comp continuous_fst)
    (continuous_const.mul ((pairTest B φ).continuous.comp continuous_snd))

theorem weakDerivative_of_tendsto {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (us ds : ℕ → BallL2 B) (u d : BallL2 B)
    (hu : Filter.Tendsto us Filter.atTop (𝓝 u))
    (hd : Filter.Tendsto ds Filter.atTop (𝓝 d))
    (hweak : ∀ m, IsWeakDerivative B α (us m) (ds m)) :
    IsWeakDerivative B α u d := by
  exact (weakDerivative_isClosed B α).mem_of_tendsto (hu.prodMk_nhds hd)
    (Filter.Eventually.of_forall hweak)

end DedekindZetaZeroFree.KPContLocalNorm
