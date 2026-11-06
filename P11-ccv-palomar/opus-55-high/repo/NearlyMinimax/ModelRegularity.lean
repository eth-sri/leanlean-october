module

public import NearlyMinimax.Model
public import NearlyMinimax.Projection
public import RoughRegime.Macro
public import RoughRegime.Notation

public section

open Set Matrix
𝚳

𝚨

𝗇 𝔇 List.flatMap_eq_nil_iff.mpr 𝗓₂
𝗇 𝔍 𝖾
theorem multiPartial_zero_index (F : 𝙀) :
    multiPartial F 𝔍 = F := by
  simp [multiPartial, 𝔇]

section

variable (x : Covariate d)

theorem euclideanNorm_eq_sqrt_energy :
    euclideanNorm x = Real.sqrt (projectionEnergy x) := by
  simp only [euclideanNorm, projectionEnergy, dotProduct, pow_two]

theorem euclideanNorm_eq_zero_iff :
    euclideanNorm x = 0 ↔ x = 0 := by
  rw [euclideanNorm_eq_sqrt_energy, Real.sqrt_eq_zero $ projectionEnergy_nonneg x ]
  exact dotProduct_self_eq_zero

theorem euclideanNorm_pos_of_ne_zero (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  have hnonneg : 0 ≤ euclideanNorm x := by unfold euclideanNorm; positivity
  have hne : euclideanNorm x ≠ 0 := by
    intro hz
    exact hx $ (euclideanNorm_eq_zero_iff x).mp hz
  positivity

end

𝗇 𝔏 𝘌
𝗇 𝔅 euclideanNorm 𝔏 ^ α
𝗇 𝔎 ⟨x, hx⟩
/-- The model's actual Hölder seminorm gives its pointwise modulus,
using precisely the Euclidean distance in the manuscript. -/
theorem holderSeminorm_pointwise_bound U
    G α H (hH : 𝖹₁)
    (hseminorm : holderSeminorm U G α ≤ ENNReal.ofReal H)
    (x y : Covariate d) (hx : x ∈ U) (hy : y ∈ U) :
    |G x - G y| ≤ H * 𝔅 := by
  by_cases hxy : x = y
  · subst y
    simp
    exact mul_nonneg hH $ Real.rpow_nonneg (Real.sqrt_nonneg _) α
  · have hraw : ENNReal.ofReal
        (|G x - G y| / 𝔅) ≤ holderSeminorm U G α := by
      apply le_iSup_of_le 𝔎
      apply le_iSup_of_le ⟨y, hy⟩
      simp_all
    exact (div_le_iff₀ $ Real.rpow_pos_of_pos (euclideanNorm_pos_of_ne_zero 𝔏 $ sub_ne_zero.mpr hxy ) α ).mp $ (ENNReal.ofReal_le_ofReal_iff hH).mp $ hraw.trans hseminorm

𝗃 𝔐 multiPartial F fun i => (ἀ i).val
𝗇 𝔄 𝔐 γ
𝗃 𝔑 ∑ i, (ἀ i).val
𝗇 𝔈 𝔑 γ
𝗇 𝔉 𝘍₂ ℓ α
𝗇 𝔊 𝘛
/-- Every mixed partial counted in the model norm has the stated
uniform pointwise bound on the extension domain. -/
theorem holderNorm_derivative_bound U
    F ℓ α H (hH : 𝖹₁)
    (hNorm : 𝔉 ≤ ENNReal.ofReal H)
    (γ : 𝔊) (hγ : 𝔈 ≤ ℓ)
    x (hx : x ∈ U) :
    |𝔄 x| ≤ H := by
  have hpoint : ENNReal.ofReal |𝔄 x| ≤
      derivativeSup U 𝔄 := le_iSup (fun z : U => ENNReal.ofReal |𝔄 z|) 𝔎
  have hterm : derivativeSup U 𝔄 ≤
      𝔉 := by
    apply le_trans _ $ le_add_right le_rfl
    have ht := Finset.single_le_sum
      (fun δ _ => (bot_le : 0 ≤
        if 𝔑 δ ≤ ℓ then derivativeSup U 𝔐 δ else 0))
      $ Finset.mem_univ γ
    simp_all
  exact (ENNReal.ofReal_le_ofReal_iff hH).mp $ (hpoint.trans hterm).trans hNorm

/-- The highest-order mixed partials counted by the model norm inherit
the actual Hölder modulus, without replacing the paper's norm. -/
theorem holderNorm_top_derivative_modulus U
    F ℓ α H (hH : 𝖹₁)
    (hNorm : 𝔉 ≤ ENNReal.ofReal H)
    (γ : 𝔊) (hγ : 𝔈 = ℓ)
    x y (hx : x ∈ U) (hy : y ∈ U) :
    |𝔄 x - 𝔄 y| ≤
      H * 𝔅 := by
  apply holderSeminorm_pointwise_bound U _ α H hH _ x y hx hy
  apply le_trans _ hNorm
  apply le_trans _ $ le_add_left le_rfl
  apply le_iSup_of_le γ
  simp_all

/-- At order zero, the model norm is precisely the function supremum
and its Hölder seminorm. -/
theorem holderNorm_order_zero U
    (F : 𝙀) α :
    𝘍₂ 0 α = derivativeSup U F + holderSeminorm U F α := by
  simp [holderNorm, multiPartial, 𝔇]

/-- The paper's actual admissibility norm bounds the regression values
uniformly on the design cube for every smoothness order. -/
theorem admissible_regression_value_bound C
    θ (hθ : 𝙟)
    x (hx : 𝗌) : |θ.regression x| ≤ C.holderBound := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, _, hNorm⟩, _, _, _⟩
  have hb := holderNorm_derivative_bound C.domain F C.order C.alpha C.holderBound
    C.holderBound_pos.le hNorm 𝔍  𝖢₄  x $ C.cube_subset hx
  simpa only [Fin.val_zero, multiPartial_zero_index, hcube x hx] using hb

/-- A cube of side length `h` has Euclidean diameter at most `sqrt(d) h`. -/
theorem euclideanNorm_le_coordinate_radius (x : Covariate d)
    h (hh : 0 ≤ h) (hx : ∀ i, |x i| ≤ h) :
    euclideanNorm x ≤ Real.sqrt d * h := by
  rw [euclideanNorm, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hh, ?_⟩
  rw [mul_pow, Real.sq_sqrt $ Nat.cast_nonneg d ]
  calc
     ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, h ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [sq_abs] using (𝘉 hh).mpr $ hx i
    𝘿 := 𝖢₄
