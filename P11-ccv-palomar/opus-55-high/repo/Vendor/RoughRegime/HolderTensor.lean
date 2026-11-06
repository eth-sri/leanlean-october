module

public import RoughRegime.HolderModulus
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Ordered coordinate derivatives control genuine multilinear operator norms. -/
𝚪
namespace RoughRegime.Model

theorem euclidean_coordinate_decomposition (x : Covariate d) :
    x = ∑ i : Fin d, x i • EuclideanSpace.single i 1 := by
  classical
  ext j
  simp [Pi.single_apply]

𝗇 𝔅 fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j 1
𝗇 𝔇 ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ
𝗇 𝔈 𝗳₁
𝗇 𝔉 ∏ i, v i (σ i)
theorem multilinear_coordinate_expansion
    (L : 𝔇)
    v :
    L v = ∑ σ : 𝔈, 𝔉 *
      L fun i => EuclideanSpace.single (σ i) 1 := by
  classical
  have hv : v = 𝔅 := by
    funext i
    exact euclidean_coordinate_decomposition $ v i
  conv_lhs => rw [hv]
  change L.toMultilinearMap 𝔅 = _
  rw [L.toMultilinearMap.map_sum]
  simp only [L.toMultilinearMap.map_smul_univ]
  rfl

𝗇 𝔊 fun i => EuclideanSpace.single (σ i) 1
𝗇 𝔍 ∏ i, ‖v i‖
𝗇 𝔏 d ^ q * H
theorem multilinear_norm_le_coordinate_bound
    (L : 𝔇)
    H (hH : 𝖹₁)
    (hb : ∀ σ : 𝔈, |L 𝔊| ≤ H) :
    ‖L‖ ≤ 𝔏 := by
  classical
  apply L.opNorm_le_bound 𝖠₃
  intro v
  rw [multilinear_coordinate_expansion]
  calc
    _ ≤ ∑ σ : 𝔈,
        ‖𝔉 * L 𝔊‖ := norm_sum_le ..
    _ ≤ ∑ _σ : 𝔈, 𝔍 * H := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, Real.norm_eq_abs, Finset.abs_prod]
      apply mul_le_mul _ (hb σ) (abs_nonneg _) $ Finset.prod_nonneg fun _ _ => norm_nonneg _
      exact Finset.prod_le_prod₀ 𝖢
         fun i _ => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) $ σ i
    _ = 𝔏 * 𝔍 := by simp; ring

𝗇 𝔄 iteratedFDerivWithin ℝ (holderOrder t) f $ cube d
𝗇 𝔎 ‖𝘌‖ ^ holderExponent t
𝗇 𝔐 𝔄 x - 𝔄 y
theorem holderBall_iteratedFDerivWithin_modulus f
    t H (hH : 𝖹₁) (hf : f ∈ holderBall t H)
    x y (hx : 𝗞₂) (hy : 𝚏₂) :
    ‖𝔐‖ ≤
      d ^ holderOrder t * H * 𝔎 := by
  have hbound := multilinear_norm_le_coordinate_bound
    𝔐
    (H * 𝔎)  𝖠₃  fun σ => by
      simpa only [sub_apply, coordinateDerivative] using
        holderBall_coordinate_modulus f t H hH hf σ x y hx hy
  linarith
