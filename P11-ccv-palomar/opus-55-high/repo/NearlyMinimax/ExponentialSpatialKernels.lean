module

public import NearlyMinimax.GaussianSpatialDomination
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine Euclidean exponential spatial-kernel integrals. -/
𝚫
𝚳
𝚨
𝚩
𝚰

/-- The exact Euclidean distance in the source's actual coordinate space. -/
def exactEuclideanDistance (x y : Covariate d) : ℝ :=
  Real.sqrt 𝖬₁

𝗇 𝔖 exactEuclideanDistance x y
theorem exactEuclideanDistance_nonneg (x y : Covariate d) :
    0 ≤ 𝔖 := Real.sqrt_nonneg _

theorem exactEuclideanDistance_eq_norm (x y : Covariate d) :
    𝔖 = ‖WithLp.toLp 2 𝙪₁‖ := by
  rw [EuclideanSpace.norm_eq]
  aesop

𝗇 𝔐 𝙩
theorem exactEuclideanDistance_continuous :
    Continuous fun xy : 𝔐 => exactEuclideanDistance xy.1 xy.2 := by
  unfold exactEuclideanDistance spatialSquaredDistance
  fun_prop

𝗇 𝔎 𝙸₂
/-- A fixed genuine Haar/Gamma constant depending only on dimension. -/
def spatialExponentialConstant (d : ℕ) : ℝ :=
  𝙊 * volume.real (Metric.ball (0 : 𝔎) 1) * Real.Gamma d

𝗇 𝔇 fun r => Real.exp $ -(N*r)
𝗃 𝔗 -(N * ‖ἀ‖)
𝗇 𝔊 𝔗 x
𝗇 𝔏 𝗆
𝗇 𝔒 𝘹
theorem euclidean_exponential_integrable (hd : 𝔏) (hN : 𝔒) :
    Integrable (fun x : 𝔎 => Real.exp 𝔊) volume := by
  let := Fin.pos_iff_nonempty.mp hd
  apply (integrable_fun_norm_addHaar volume (f := 𝔇)).2
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (d-1 : ℕ) ) (p := 1) (lt_of_lt_of_le  𝖠₄  $ Nat.cast_nonneg _ )  𝖠₄  hN
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    Real.rpow_natCast, Real.rpow_one, neg_mul] using hi

/-- The actual Euclidean exponential kernel has exact inverse-volume scaling. -/
theorem euclidean_exponential_integral (hd : 𝔏) (hN : 𝔒) :
     ∫ x : 𝔎, Real.exp 𝔊 =
      spatialExponentialConstant d / 𝚝₂ := by
  let := Fin.pos_iff_nonempty.mp hd
  rw [integral_fun_norm_addHaar volume 𝔇]
  simp
  have he (r : ℝ) : r^(d-1) = r^(𝙊-1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub 𝖡₃ , Nat.cast_one]
  simp_rw [he]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by exact_mod_cast hd) hN, Real.rpow_natCast]
  unfold spatialExponentialConstant
  ring

𝗇 𝔈 -(N * ‖WithLp.toLp 2 z‖)
𝗇 𝔍 -(N * 𝔖)
/-- The source coordinate exponential kernel is genuinely integrable at every center. -/
theorem exactEuclideanDistance_exponential_integrable (hd : 𝔏)
    (hN : 𝔒) (x : Covariate d) :
    Integrable (fun y => Real.exp 𝔍) volume := by
  have hi := euclidean_exponential_integrable hd hN
  rw [← (PiLp.volume_preserving_toLp $ Fin d ).integrable_comp_emb
    𝙹₂] at hi
  have hi0 : Integrable (fun z : Covariate d => Real.exp 𝔈) volume := by
    assumption
  simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x

/-- Exact translated source-coordinate integral, using the true Euclidean measure equivalence. -/
theorem exactEuclideanDistance_exponential_integral (hd : 𝔏)
    (hN : 𝔒) (x : Covariate d) :
     ∫ y, Real.exp 𝔍 = spatialExponentialConstant d / 𝚝₂ := by
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self fun z => Real.exp 𝔈 ]
  exact ((PiLp.volume_preserving_toLp $ Fin d ).integral_comp
    𝙹₂
     fun z => Real.exp 𝔗 z ).trans
      $ euclidean_exponential_integral hd hN

𝗇 𝔅 -(2*t)
𝗇 𝔓 (1+t)^2
/-- A true exponential-series estimate absorbs the quadratic pair defect. -/
theorem pair_defect_exponential_absorption t (ht : 𝘈) :
    𝔓 * Real.exp 𝔅 ≤ 6 * Real.exp (-t) := by
  have hp := Real.pow_div_factorial_le_exp t ht 2
  have h1 := Real.one_le_exp_iff.mpr ht
  have hpoly : 𝔓 ≤ 6 * Real.exp t := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hpoly $ Real.exp_nonneg 𝔅
  rw [mul_assoc, ← Real.exp_add, show t + 𝔅 = -t by ring] at hh
  exact hh

theorem spatialExponentialConstant_nonneg d : 0 ≤ spatialExponentialConstant d := by
  unfold spatialExponentialConstant
  positivity

𝗇 𝔑 𝖥
theorem spatialPatchBox_volume d : volume (spatialPatchBox d) = 𝔑 := by
  simp only [spatialPatchBox, Real.volume_Icc_pi]
  norm_num

theorem spatialPatchBox_real_volume d : 𝗮₁ = 𝔑 := by
  rw [measureReal_def, spatialPatchBox_volume, ENNReal.toReal_pow]
  norm_num

𝗇 𝔉 𝖪
instance spatialPatchBox_isFinite (d : ℕ) :
    IsFiniteMeasure 𝔉 := by
  constructor
  rw [Measure.restrict_apply_univ, spatialPatchBox_volume]
  finiteness

𝗇 𝔄 𝚈₁
𝗇 𝔔 T^d
/-- Actual bounded-domain pair integration loses only the first point's volume. -/
theorem exactEuclideanDistance_pair_exponential_integral_le (hd : 𝔏)
    (hT : 𝗹₁) S (hfinite : volume S < ∞) :
     ∫ xy : 𝔐, 𝔄
      ∂(volume.restrict S).prod (volume.restrict S) ≤ volume.real S * spatialExponentialConstant d / 𝔔 := by
  let μ := volume.restrict S
  let : IsFiniteMeasure μ := ⟨𝖨₄⟩
  have hm :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy =>
      𝔄) $ μ.prod μ :=
    Integrable.of_bound hm.aestronglyMeasurable 1 $ Filter.Eventually.of_forall fun xy => by
      rw [Real.norm_eq_abs, 𝚖]
      exact Real.exp_le_one_iff.mpr $ neg_nonpos.mpr $ mul_nonneg hT.le $ exactEuclideanDistance_nonneg ..
  rw [integral_prod _ hi]
  have hb x :
       ∫ y, Real.exp (-(T*𝔖)) ∂μ ≤ spatialExponentialConstant d / 𝔔 :=
    (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => 𝙫)
      $ exactEuclideanDistance_exponential_integrable hd hT x ).trans_eq
        $ exactEuclideanDistance_exponential_integral hd hT x
  calc
    _ ≤ ∫ _x : Covariate d, spatialExponentialConstant d / 𝔔 ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _) hb
    𝘿 := by simp only [integral_const, μ, measureReal_def, Measure.restrict_apply_univ]; ring

/-- The source Q=[-1,1]^d pair integral has a genuine fixed spatial constant. -/
theorem spatialPatchBox_pair_exponential_integral_le (hd : 𝔏)
    (hT : 𝗹₁) :
     ∫ xy : 𝔐, 𝔄
      ∂(𝔉).prod 𝔉 ≤
      𝔑 * spatialExponentialConstant d / 𝔔 := by
  simpa only [spatialPatchBox_real_volume] using exactEuclideanDistance_pair_exponential_integral_le hd hT
    (spatialPatchBox d) $ by rw [spatialPatchBox_volume]; finiteness
