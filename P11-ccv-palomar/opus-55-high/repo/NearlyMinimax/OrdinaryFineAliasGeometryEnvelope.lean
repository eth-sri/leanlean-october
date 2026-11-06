module

public import NearlyMinimax.OrdinaryFineAliasAggregation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Deterministic response-summed square envelopes for ordinary fine aliases.
They depend only on actual geometric matrix kernels and fixed scalar data,
never on the density/regression/window/coefficient nuisance values. -/
𝚫
𝚨
𝚩
𝚭
𝚬

𝗇 𝔙 𝖧
𝗇 𝔠 shrunkDensityExponent ad bd M
𝗃 𝔤 ἀ^2
def ordinaryFineAliasAmplitudeFactor (n M R q : ℕ) (ad bd c0 C a rho eta : ℝ) : ℝ :=
   (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
    Real.exp (𝔙*𝔠) *
      (ordinaryAliasResponseConstant q C a rho * 𝙒^2 * 𝔤 eta)

𝗇 𝔏 𝙇
def ordinaryFineAliasGeometryKernel {d n F : ℕ} (r : ℕ) (L T : ℝ)
    (U : 𝔏) : ℝ :=
  ∑ S ∈ (Finset.univ : 𝙍).powersetCard r,
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
      𝖹₂)

𝗇 𝔇 ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta
𝗇 𝔡 ordinaryFineAliasGeometryKernel (F := F) r
𝗇 𝔐 𝔡 L (T r) U
𝗇 𝔚 ∑ r ∈ I, 𝔇 * 𝔐
/-- Sum the actual geometric bands before squaring. This is the genuine
triangle/Cauchy envelope for the sum of fine signed-row actions. -/
def ordinaryFineAliasFamilyResponseSquareEnvelope {d n F : ℕ} (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : 𝙜)
    (U : 𝔏) : ℝ :=
  (3 : ℝ)^n *
    𝔤 𝔚

𝗇 𝔛 ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta
𝗇 𝔍 𝔛 L T U
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg I
    M R q ad bd c0 C a rho eta L T (U : 𝔏) :
    0 ≤ 𝔍 := by
  unfold ordinaryFineAliasFamilyResponseSquareEnvelope
  positivity

𝗃 𝔣 ἀ (d := d) (n := n) (F := F)
theorem ordinaryFineAliasGeometryKernel_measurable r
    (hL : 𝚛₂) (hT : 𝖹) :
    Measurable $ 𝔣 ordinaryFineAliasGeometryKernel r L T := Finset.measurable_sum _ fun S _ => Finset.measurable_sum _
     fun gamma _ => Finset.measurable_sum _ fun beta _ =>
      ((integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT gamma beta).measurable.abs).comp
        $ spatialSubsetConfiguration_measurable S

𝗇 𝔄 ordinaryFineAliasFamilyRawAction I (ad+𝔙⁻¹) (bd-𝔙⁻¹) (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y
𝗇 𝔊 𝙈
𝗇 𝔎 𝔙⁻¹
𝗇 𝔞 hI r hr
𝗃 𝔧 ∀ r ∈ I, ἀ ∧ r ≤ R
/-- Actual pointwise square domination for the entire fine family,
separately uniform over each response's nuisance tuple. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_dominates {d n F M R : ℕ}
    (I : Finset ℕ) (ad bd c0 L : ℝ) (T : 𝙜) (haD : 𝖼)
    (hshrink : ad+𝔎 < bd-𝔎)
    (htau : 𝔠 ≤ c0) (hI : 𝔧 𝘗)
    (q : ℕ) (hn : 𝗚) (C a V eta rho : ℝ) (hC : 1 ≤ C) (ha : 𝙆)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔊 → 𝙔)
    (c : 𝔊 → 𝖲)
    (hpD : ∀ y i, p y i ∈ Icc (ad+𝔎) (bd-𝔎))
    (hg : ∀ y i, |g y i| ≤ rho/2) (hw : ∀ y i, |w y i| ≤ 1)
    (hc : ∀ y, ∑ gamma, |c y gamma| ≤ 𝗳)
    (hp : ∀ f : ℝ, |f| ≤ rho → 𝘃) :
     ∑ y : 𝔊,
      𝔤 𝔄 ≤
      𝔍 := by
  let H := 𝔚
  have hb (y : 𝔊) :
      |𝔄| ≤ H := by
    apply (Finset.abs_sum_le_sum_abs _ I).trans
    exact Finset.sum_le_sum fun r hr =>
      ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 (spatialInterpolationLambda d) L (T r)
        haD hshrink htau (𝔞).1 (𝔞).2 q hn C a V eta rho hC ha heta hrho hetarho
        U hU (p y) (g y) (w y) (hpD y) (hg y) (hw y) (c y) (hc y) hp y
  have hsq (y : 𝔊) :
      𝔤 𝔄 ≤ 𝔤 H := by
    simpa only [sq_abs] using (𝘉 $ (abs_nonneg _).trans $ hb y ).mpr $ hb y
  have hs := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hsq y
  aesop

𝗇 𝔅 𝗐
𝗇 𝔈 𝖮₁
𝗇 𝔢 f r U
𝗇 𝔉 (∑ r ∈ I, 𝔢)^2
𝗇 𝔑 𝔤 𝔢
𝗇 𝔒 2*𝔠*M
𝗇 𝔓 N^(4-𝙊)
𝗇 𝔔 𝘫₂
𝗇 𝔖 hLT r hr
𝗇 𝔗 ∫ U, 𝔑 ∂𝔈
𝗇 𝔘 𝔡 𝔅 (T r) U
𝗃 𝔦 ἀ d q R ad bd c0 C a rho
𝗃 𝔜 𝔦 ἀ * eta^4 * Real.exp 𝔒 * 𝔓 * Real.exp 𝔔
𝗇 𝔟 r ∈ I
/-- True integrability and geometric scale for the response-summed family
envelope itself; independent of every nuisance field and chart inverse. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le {d n F M R : ℕ}
    (hd : 𝘚) (I : Finset ℕ) (hI : 𝔧 𝘠₁)
    (ad bd c0 C a rho eta D K N : ℝ) (hbd : 0 ≤ bd)
    (hD : 0 ≤ D) (hK : 𝖭₂) (hc0 : 0 ≤ c0) (hDK : 𝚋₁)
    (hN : 𝘹) (hell : 1 ≤ 𝔅)
    (hH : Real.log 𝘵 ≤ M) (T : 𝙜)
    (hLT : ∀ r ∈ I, 𝔅 ≤ T r) (q : ℕ) :
    Integrable (𝔣 ordinaryFineAliasFamilyResponseSquareEnvelope
      I M R q ad bd c0 C a rho eta 𝔅 T) 𝔈 ∧
     ∫ U, 𝔛 𝔅 T U ∂𝔈 ≤
      𝔜 ordinaryAliasFamilySpatialPrefactor * ordinaryAliasSpatialResponseBase d bd ^n := by
  let f := fun r (U : 𝔏) =>
    𝔇 *
      𝔘
  let B := 𝔜 ordinaryAliasSpatialPrefactor * ordinaryAliasSpatialCountBase d bd ^n
  have hB : 𝙐 := by
    dsimp [B]
    have := 𝔦 ordinaryAliasSpatialPrefactor_nonneg
    unfold ordinaryAliasSpatialCountBase
    positivity
  have hm r (hr : 𝔟) : Measurable $ f r :=
    (ordinaryFineAliasGeometryKernel_measurable r hell $ hell.trans 𝔖 ).const_mul _
  have hk r (hr : 𝔟) := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
    hd (𝔞).1 hell (hell.trans 𝔖) 𝔖
  have hi r (hr : 𝔟) : Integrable (fun U => 𝔑) 𝔈 := by
    have h := (hk r hr).1.const_mul 𝔤 𝔇
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  have hb r (hr : 𝔟) : 𝔗 ≤ B := by
    have h : 𝔗 ≤
        ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a rho eta 𝔅 := by
      have hid : 𝔗 =
          𝔤 𝔇 *
             ∫ U, 𝔤 𝔘
              ∂𝔈 := by
        rw [← integral_const_mul]
        grind
      rw [hid]
      exact (mul_le_mul_of_nonneg_left (hk r hr).2 $ sq_nonneg _ ).trans_eq $ by
        rfl
    exact h.trans $ ordinaryFineAliasSpatialBudget_source_scale_le hd (𝔞).2 hbd hD hK hc0
      hDK hN hell hH q
  have hs : Integrable (fun U => 𝔉) 𝔈 := by
    have h := finite_sum_abs_square_integrable 𝔈 I f hm hi
    have hupper : ∀ U, 𝔉 ≤ (∑ r ∈ I, |𝔢|)^2 := by
      intro U
      have hb := Finset.abs_sum_le_sum_abs (fun r => 𝔢) I
      simpa only [sq_abs] using (𝘉
        $ Finset.sum_nonneg 𝖢 ).mpr hb
    exact h.mono' ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
      $ Filter.Eventually.of_forall fun U => 𝖤₄
  have hcard : 𝔤 I.card ≤ ((R+1 : ℕ) : ℝ)^2 := by
    have hsub : I ⊆ Finset.range (R+1) := fun r hr => Finset.mem_range.mpr 𝖤₄
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast Nat.pow_le_pow_left h 2
  have hsum := (finite_sum_square_integral_le 𝔈 I f B hm hi hb).trans
    $ mul_le_mul_of_nonneg_right hcard hB
  refine ⟨hs.const_mul $ 3^n , ?_⟩
  rw [show ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope
      I M R q ad bd c0 C a rho eta 𝔅 T U ∂𝔈 =
      3^n * ∫ U, 𝔉 ∂𝔈 by
    rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left hsum 𝖠₃ ).trans_eq $ by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase
    ring
