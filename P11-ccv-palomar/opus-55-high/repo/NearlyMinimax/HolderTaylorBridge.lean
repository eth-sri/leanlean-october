module

public import NearlyMinimax.CoordinatePartialBridge
public import RoughRegime.HolderTaylorApproximation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Transport of the original open-domain Hölder model to genuine multivariate
Taylor polynomials. The two covariate representations have different norms;
the transport below retains the manuscript's Euclidean distance exactly. -/

open Set
open scoped ContDiff ENNReal

𝚨

𝗇 𝔊 𝙸₂
def euclideanCoordinates (d : ℕ) : 𝔊 ≃L[ℝ] Covariate d :=
  PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ

def euclideanPoint (x : Covariate d) : 𝔊 :=
  (euclideanCoordinates d).symm x

𝗇 𝔜 𝙀
def euclideanExtension (F : 𝔜) : 𝔊 → ℝ :=
  F ∘ euclideanCoordinates d

@[simp] theorem euclideanCoordinates_apply x
    i : euclideanCoordinates d x i = x i := rfl

@[simp] theorem euclideanCoordinates_point x :
    euclideanCoordinates d (euclideanPoint x) = x :=
  (euclideanCoordinates d).apply_symm_apply x

𝗇 𝔉 euclideanCoordinates d x
theorem euclideanCoordinates_norm x :
    euclideanNorm 𝔉 = ‖x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  simp

theorem euclideanPoint_norm (x : Covariate d) :
    ‖euclideanPoint x‖ = euclideanNorm x := by
  rw [← euclideanCoordinates_norm, euclideanCoordinates_point]

theorem euclideanExtension_contDiffOn {d ℓ : ℕ} {U }
    {F } (hf : ContDiffOn ℝ ℓ F U)
    (hcube : unitCube d ⊆ U) :
    ContDiffOn ℝ ℓ (euclideanExtension F) $ RoughRegime.Model.cube d := by
  apply (hf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap).mono
  tauto

𝗃 𝔠 fun j => ἀ (σ j) 1
𝗇 𝔅 𝔠 Pi.single
𝗇 𝔞 iteratedFDeriv ℝ q
𝗃 𝔟 ἀ $ euclideanExtension F
/-- Linear transport of the true ordered Fréchet derivative, with no norm
comparison and no differentiability assumption hidden in the coordinates. -/
theorem euclideanExtension_iteratedFDeriv (F : 𝔜)
    x (σ : 𝗳₁) :
    𝔟 𝔞 x
        𝔠 EuclideanSpace.single =
      𝔞 F 𝔉
        𝔅 := by
  have he := (euclideanCoordinates d).iteratedFDerivWithin_comp_right
    F uniqueDiffOn_univ (x := x) (mem_univ _) q
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at he
  rw [show euclideanExtension F = F ∘ euclideanCoordinates d by rfl, he]
  rfl

/-- Within-cube coordinate derivatives of the transported extension are the
true derivatives of the original function, including cube boundary points. -/
theorem euclideanExtension_coordinateDerivative {d ℓ q : ℕ}
    U (hU : IsOpen U) F
    (hf : ContDiffOn ℝ ℓ F U) (hcube : unitCube d ⊆ U) (hq : q ≤ ℓ)
    σ (x : 𝔊)
    (hx : x ∈ RoughRegime.Model.cube d) :
    𝔟 RoughRegime.Model.coordinateDerivative q σ x =
      𝔞 F 𝔉
        𝔅 := by
  have hqf : ContDiffOn ℝ q F U := hf.of_le $ by exact_mod_cast hq
  have hreg := hqf.comp_continuousLinearMap (euclideanCoordinates d).toContinuousLinearMap
  have hopen :=
    hU.preimage (euclideanCoordinates d).continuous
  have hat : ContDiffAt ℝ q (euclideanExtension F) x :=
    hreg.contDiffAt $ hopen.mem_nhds $ hcube hx
  rw [RoughRegime.Model.coordinateDerivative_eq_iteratedFDeriv _ q σ x hx hat]
  exact euclideanExtension_iteratedFDeriv F x σ

𝗇 𝔇 2 * C.holderBound
𝗇 𝔏 ContDiffOn ℝ C.order F C.domain
𝗇 𝔒 euclideanExtension F ∈ RoughRegime.Model.holderBall C.smoothness 𝔇
𝗇 𝔓 euclideanExtension_coordinateDerivative C.domain C.domain_open F hf C.cube_subset
𝗇 𝔔 iteratedFDeriv ℝ C.order F
𝗇 𝔘 𝔉 - euclideanCoordinates d y
/-- Pointwise ordered derivative bounds and the Euclidean top-order modulus
control the related library's closed-cube norm. This lemma is a transport
step; the original model supplies its two premises in the final bridge. -/
theorem euclideanExtension_mem_holderBall_of_coordinate_bounds {d }
    (C : ModelConstants d) F
    (hf : 𝔏)
    (hb : ∀ q ≤ C.order, ∀ σ : 𝗳₁, ∀ x ∈ C.domain,
      |𝔞 F x 𝔅| ≤ C.holderBound)
    (hm : ∀ σ : Fin C.order → Fin d, ∀ x ∈ C.domain, ∀ y ∈ C.domain,
      |𝔔 x 𝔅 -
        𝔔 y 𝔅| ≤
          C.holderBound * euclideanNorm 𝘌 ^ C.alpha) :
    𝔒 := by
  have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
  have halpha : RoughRegime.Model.holderExponent C.smoothness = C.alpha := by
    simp only [RoughRegime.Model.holderExponent, horder, ModelConstants.alpha]
  have hreg : ContDiffOn ℝ (RoughRegime.Model.holderOrder C.smoothness)
      (euclideanExtension F) $ RoughRegime.Model.cube d := by
    rw [horder]
    exact euclideanExtension_contDiffOn hf C.cube_subset
  have hsup : 𝔟 RoughRegime.Model.derivativeSup
      (RoughRegime.Model.holderOrder C.smoothness) ≤ ENNReal.ofReal C.holderBound := by
    rw [horder]
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    rw [𝔓 hq σ x hx]
    exact ENNReal.ofReal_le_ofReal $ hb q hq σ _ $ C.cube_subset hx
  have hsem : 𝔟 RoughRegime.Model.holderSeminorm C.smoothness ≤
      ENNReal.ofReal C.holderBound := by
    unfold RoughRegime.Model.holderSeminorm
    rw [horder, halpha]
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    apply ENNReal.ofReal_le_ofReal
    have hmod := hm σ _ (C.cube_subset hx) _ $ C.cube_subset hy
    change |𝔔 𝔉
        𝔅 -
      𝔔 (euclideanCoordinates d y)
        𝔅| ≤
      C.holderBound * euclideanNorm 𝔘 ^
        C.alpha at hmod
    rw [𝔓 le_rfl σ x hx,
      𝔓 le_rfl σ y hy]
    have hnorm : euclideanNorm 𝔘 =
        ‖𝘌‖ := by rw [← map_sub, euclideanCoordinates_norm]
    rw [hnorm] at hmod
    exact (div_le_iff₀ $ Real.rpow_pos_of_pos
      (norm_pos_iff.mpr $ sub_ne_zero.mpr hxy ) _ ).2 hmod
  change 𝔟 RoughRegime.Model.holderNorm C.smoothness ≤ _
  unfold RoughRegime.Model.holderNorm
  rw [if_pos ⟨C.smoothness_pos, hreg⟩]
  calc
    _ ≤ ENNReal.ofReal C.holderBound + ENNReal.ofReal C.holderBound := add_le_add hsup hsem
    _ = ENNReal.ofReal 𝔇 := by
      rw [← ENNReal.ofReal_add C.holderBound_pos.le C.holderBound_pos.le]
      ring

𝗇 𝔍 holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound
𝗃 𝔡 ἀ C F
𝗃 𝔢 ἀ C.domain C.domain_open F C.order C.alpha C.holderBound C.holderBound_pos.le hf hNorm
/-- The manuscript's actual open-domain sum norm implies the related
ordered-coordinate closed-cube norm, with the explicit harmless factor two. -/
theorem euclideanExtension_mem_holderBall (C : ModelConstants d)
    F (hf : 𝔏)
    (hNorm : 𝔍) :
    𝔒 := by
  apply 𝔡 euclideanExtension_mem_holderBall_of_coordinate_bounds hf
  · intro q hq σ x hx
    exact 𝔢 ordered_coordinate_bound q hq σ x hx
  · intro σ x hx y hy
    exact 𝔢 ordered_coordinate_modulus σ x y hx hy

/-- Concrete polynomial in the original covariates, obtained from the true
multivariate Taylor coefficients after the Euclidean coordinate transport. -/
def modelTaylorPolynomial (C : ModelConstants d) (F : 𝔜)
    (x : Covariate d) : 𝙣 :=
  𝔟 RoughRegime.Model.holderTaylorPolynomial C.order $ euclideanPoint x

𝗇 𝔖 𝔡 modelTaylorPolynomial x
theorem modelTaylorPolynomial_degree C
    F (x : Covariate d) :
    (𝔖).totalDegree ≤ C.order :=
  RoughRegime.Model.holderTaylorPolynomial_degree ..

𝗇 𝔗 𝙪₁
𝗇 𝔄 d ^ C.order * (2 * C.holderBound) / C.order.factorial * euclideanNorm 𝔗 ^ C.smoothness
𝗇 𝔈 F y - MvPolynomial.eval y 𝔖
𝗇 𝔐 𝗌
𝗇 𝔑 y ∈ unitCube d
/-- Taylor approximation from the transported regularity. The final model
bridge establishes membership from the original sum of mixed partial norms. -/
theorem modelTaylorPolynomial_error_of_holderBall C
    F
    (hf : 𝔒)
    x y (hx : 𝔐) (hy : 𝔑) :
    |𝔈| ≤
      𝔄 := by
  have herr := 𝔟 RoughRegime.Model.holderTaylorPolynomial_error
    C.smoothness 𝔇
    (mul_nonneg  𝖠₄  C.holderBound_pos.le) hf
    (euclideanPoint x) (euclideanPoint y) hx hy
  have horder : RoughRegime.Model.holderOrder C.smoothness = C.order := C.order_eq.symm
  rw [horder] at herr
  have hdiff : euclideanPoint y - euclideanPoint x = euclideanPoint 𝔗 :=
    ((euclideanCoordinates d).symm.map_sub y x).symm
  rw [hdiff, euclideanPoint_norm] at herr
  assumption

𝗇 𝔙 𝔡 euclideanExtension_mem_holderBall hf hNorm
𝗃 𝔣 𝔡 modelTaylorPolynomial_error_of_holderBall ἀ x y hx hy
/-- The original model's regularity gives the genuine multivariate Taylor
remainder uniformly on the design cube, in every finite smoothness order. -/
theorem modelTaylorPolynomial_error C
    F (hf : 𝔏)
    (hNorm : 𝔍)
    x y (hx : 𝔐) (hy : 𝔑) :
    |𝔈| ≤
      𝔄 :=
  𝔣 𝔙

/-- The approximation factor depends only on dimension and smoothness order,
and retains the norm radius as a separate multiplicative factor. -/
def taylorErrorFactor (C : ModelConstants d) : ℝ :=
   2 * 𝙊 ^ C.order / C.order.factorial *
     Real.sqrt 𝙊 ^ C.smoothness

theorem taylorErrorFactor_pos (C : ModelConstants d) :
    0 < taylorErrorFactor C := by
  have hd : 𝗆 := by exact_mod_cast C.dimension_pos
  unfold taylorErrorFactor
  positivity

𝗇 𝔎 𝙷₂ * h ^ C.smoothness
𝗇 𝔚 y i - x i
𝗇 𝔛 d ^ C.order * 𝔇 / C.order.factorial
theorem modelTaylorPolynomial_cell_error_of_holderBall
    C F
    (hf : 𝔒)
    x y (hx : 𝔐) (hy : 𝔑)
    h (hh : 0 ≤ h) (hxy : ∀ i, |𝔚| ≤ h) :
    |𝔈| ≤
      𝔎 := by
  have hr := euclideanNorm_le_coordinate_radius 𝔗 h hh hxy
  have hp := Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hr C.smoothness_pos.le
  have hcoef : 0 ≤ 𝔛 := div_nonneg (mul_nonneg 𝘑₂
      $ mul_nonneg  𝖠₄  C.holderBound_pos.le ) $ Nat.cast_nonneg _
  calc
    _ ≤ 𝔄 := 𝔣 hf
    _ ≤ 𝔛 *
        (Real.sqrt d * h) ^ C.smoothness := mul_le_mul_of_nonneg_left hp hcoef
    𝘿 := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) hh]
      unfold taylorErrorFactor
      ring

theorem modelTaylorPolynomial_cell_error C
    F (hf : 𝔏)
    (hNorm : 𝔍)
    x y (hx : 𝔐) (hy : 𝔑)
    h (hh : 0 ≤ h) (hxy : ∀ i, |𝔚| ≤ h) :
    |𝔈| ≤
      𝔎 :=
  𝔡 modelTaylorPolynomial_cell_error_of_holderBall
    𝔙 x y hx hy h hh hxy

section

variable (C)
    (θ)
    (hθ : 𝙟)
    (x)
    (hx : 𝔐)

include hθ hx

/-- Every admissible regression admits a degree-bounded Taylor polynomial
around each point in the design cube, with the original Hölder radius. -/
theorem admissible_regression_taylor :
    ∃ P , P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, |θ.regression y - MvPolynomial.eval y P| ≤
        𝔄 := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  refine ⟨𝔖, 𝔡 modelTaylorPolynomial_degree x, ?_⟩
  intro y hy
  simpa only [hcube y hy] using 𝔡 modelTaylorPolynomial_error hreg hNorm x y hx hy

/-- Uniform polynomial approximation on a cell of side `h`. The explicit
error factor depends only on dimension and smoothness, not the open domain. -/
theorem admissible_regression_taylor_cell h (hh : 0 ≤ h) :
    ∃ P , P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, (∀ i, |𝔚| ≤ h) →
        |θ.regression y - MvPolynomial.eval y P| ≤
          𝔎 := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  refine ⟨𝔖, 𝔡 modelTaylorPolynomial_degree x, ?_⟩
  intro y hy hxy
  simpa only [hcube y hy] using
    𝔡 modelTaylorPolynomial_cell_error hreg hNorm x y hx hy h hh hxy
