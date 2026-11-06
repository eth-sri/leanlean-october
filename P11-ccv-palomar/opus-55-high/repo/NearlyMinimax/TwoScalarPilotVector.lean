module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PilotFields
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Honest assembly of the two scalar pilot fluctuations into the original
three-coordinate coefficient fluctuation. -/
𝚯
𝚻
𝚨
𝚩
𝛃
𝚰

𝗇 𝔖 a - b
def twoScalarPilotVector (a b : ℝ) : PairVector :=
  𝔖 • pairCoordinateVector 1 - a • pairCoordinateVector 2

𝗇 𝔘 twoScalarPilotVector a b
theorem twoScalarPilotVector_coordinates a b :
    𝔘 = WithLp.toLp 2 ![0, 𝔖, -a] := by
  ext i
  fin_cases i <;> simp [twoScalarPilotVector, pairCoordinateVector]

theorem twoScalarPilotVector_norm_sq a b :
    ‖𝔘‖ ^ 2 = 𝔖 ^ 2 + 𝗅 := by
  rw [EuclideanSpace.real_norm_sq_eq, twoScalarPilotVector_coordinates]
  simp [Fin.sum_univ_succ]

theorem twoScalarPilotVector_norm_sq_le a b :
    ‖𝔘‖ ^ 2 ≤ 3 * 𝗅 + 2 * 𝘺 := by
  rw [twoScalarPilotVector_norm_sq]
  nlinarith only [sq_nonneg 𝗓₁]

theorem twoScalarPilotVector_inner a b v :
    ⟪𝔘, v⟫ = (v 1 - v 2) * a - v 1 * b := by
  rw [twoScalarPilotVector_coordinates]
  simp [PiLp.inner_apply, Fin.sum_univ_succ]
  ring

𝗃 𝔤 ἀ (a x) $ b x
𝗇 𝔄 𝔤 twoScalarPilotVector
𝗇 𝔒 fun x => 𝔄
𝗃 𝔢 ∫ x, ἀ ∂μ
𝗃 𝔣 2 * ἀ x ^ 2
section
𝛒
variable {a b : 𝘄}

theorem twoScalarPilotVector_aestronglyMeasurable
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) :
    AEStronglyMeasurable 𝔒 μ :=
  ((ha.sub hb).smul_const _).sub $ ha.smul_const _

𝗇 𝔏 (ha.integrable_sq.const_mul 3).add $ hb.integrable_sq.const_mul 2
𝗇 𝔙 MemLp a 2 μ
𝗇 𝔚 MemLp b 2 μ
theorem twoScalarPilotVector_memLp (ha : 𝔙) (hb : 𝔚) :
    MemLp 𝔒 2 μ := by
  have hs := twoScalarPilotVector_aestronglyMeasurable ha.aestronglyMeasurable hb.aestronglyMeasurable
  have hi :=
    𝔏
  apply (memLp_two_iff_integrable_sq_norm hs).2
  apply hi.mono' $ hs.norm.pow 2
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, 𝗤]
    exact twoScalarPilotVector_norm_sq_le ..

𝗃 𝔡 ∫ x, ἀ x ∂μ = 0
theorem twoScalarPilotVector_mean_zero [IsFiniteMeasure μ]
    (ha : 𝔙) (hb : 𝔚)
    (hma : 𝔡 a) (hmb : 𝔡 b) :
    𝔢 𝔄 = 0 := by
  have hai := ha.integrable 𝖠₄
  have hbi := hb.integrable 𝖠₄
  have hs1 : Integrable (fun x => (a x - b x) • pairCoordinateVector 1) μ := (hai.sub hbi).smul_const _
  unfold twoScalarPilotVector
  rw [integral_sub hs1 $ hai.smul_const _ ,
    integral_smul_const, integral_smul_const, integral_sub hai hbi, hma, hmb]
  simp

𝗇 𝔑 ∫ x, ‖𝔄‖ ^ 2 ∂μ
𝗃 𝔟 ∫ x, ἀ x ^ 2 ∂μ ≤ E
theorem twoScalarPilotVector_second_le (ha : 𝔙) (hb : 𝔚)
    (hEa : 𝔟 a) (hEb : 𝔟 b) :
    𝔑 ≤ 5 * E := by
  have h := integral_mono (twoScalarPilotVector_memLp ha hb).norm.integrable_sq
    𝔏
     fun x => 𝔤 twoScalarPilotVector_norm_sq_le
  change 𝔑 ≤
     ∫ x, 3 * a x ^ 2 + 𝔣 b ∂μ at h
  rw [integral_add
    (ha.integrable_sq.const_mul 3) $ hb.integrable_sq.const_mul 2 ,
    integral_const_mul, integral_const_mul] at h
  linarith

end

theorem twoScalarPilotVector_measurable {Ω } [MeasurableSpace Ω]
    {a b : 𝘄} (ha : Measurable a) (hb : Measurable b) :
    Measurable 𝔒 :=
  ((ha.sub hb).smul measurable_const).sub $ ha.smul measurable_const

𝗇 𝔇 MemLp v 2 M
theorem pairVector_coordinate_memLp {W } [MeasurableSpace W]
    {M : Measure W} {v : W → PairVector} (hv : 𝔇) i :
    MemLp (fun w => v w i) 2 M := by
  apply hv.mono $ (PiLp.continuous_apply 2 𝚟 i).comp_aestronglyMeasurable hv.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun w => PiLp.norm_apply_le (v w) i

𝗇 𝔛 a x w
𝗇 𝔜 b x w
𝗇 𝔅 PilotFields.test (M := M) (fun x w => twoScalarPilotVector 𝔛 𝔜) v x
𝗇 𝔈 𝚌₂
𝗃 𝔥 ∫ w, ἀ w * 𝔛 ∂M
𝗇 𝔉 𝔥 v
𝗃 𝔦 ∫ w, ἀ w * 𝔜 ∂M
𝗇 𝔊 𝔦 v
𝗇 𝔍 A x - B x
𝗇 𝔎 𝔣 A + 𝔣 B
𝗇 𝔐 c * ∫ w, v w ^ 2 ∂M
𝗃 𝔓 ∫ x, ἀ ^ 2 ∂μ
𝗃 𝔔 ∀ v , 𝔇 → ∀ x, Integrable (fun w => v w * ἀ x w) M
𝗇 𝔗 vA w ^ 2 + vB w ^ 2
𝗃 𝔞 ∀ v , 𝔇 → MemLp (fun x => ἀ) 2 μ
𝗃 𝔠 ∫ w, ἀ ∂M
𝗃 𝔧 ∀ v , 𝔇 → 𝔓 ἀ ≤ 𝔐
/-- A universal scalar covariance estimate for each of the two fields yields
the actual vector covariance estimate, with its dimension-free factor six. -/
theorem twoScalarPilotVector_test_second_le
    {Ω W } [MeasurableSpace Ω] [MeasurableSpace W]
    (μ : Measure Ω) M (a b : Ω → W → ℝ) {c } (hc : 𝗂₁)
    (hinta : 𝔔 a)
    (hintb : 𝔔 b)
    (hLa : 𝔞 𝔉)
    (hLb : 𝔞 𝔊)
    (hEa : 𝔧 𝔉)
    (hEb : 𝔧 𝔊)
    v (hv : 𝔇) :
    𝔓 𝔅 ≤
      6 * c * 𝔠 𝔈 := by
  let vA w := v w 1 - v w 2
  let vB w := v w 1
  have hvA : MemLp vA 2 M := (pairVector_coordinate_memLp hv 1).sub $ pairVector_coordinate_memLp hv 2
  have hvB := pairVector_coordinate_memLp hv 1
  let A x := 𝔥 vA
  let B x := 𝔦 vB
  have hA := hLa vA hvA
  have hB := hLb vB hvB
  have heq x : 𝔅 = 𝔍 := by
    unfold PilotFields.test
    simp_rw [twoScalarPilotVector_inner]
    exact integral_sub (hinta vA hvA x) $ hintb vB hvB x
  have hsq := integral_mono (hA.sub hB).integrable_sq
    ((hA.integrable_sq.const_mul 2).add $ hB.integrable_sq.const_mul 2 )
     fun x => show 𝔍 ^ 2 ≤ 𝔎 by
      nlinarith only [sq_nonneg $ A x + B x ]
  change 𝔓 𝔍 ≤ 𝔢 𝔎 at hsq
  rw [integral_add
    (hA.integrable_sq.const_mul 2) $ hB.integrable_sq.const_mul 2 ,
    integral_const_mul, integral_const_mul] at hsq
  have hweights : 𝔠 𝔗 ≤ 3 * 𝔠 𝔈 := by
    have hp w : 𝔗 ≤ 3 * 𝔈 := by
      have hn : 𝔈 = v w 0 ^ 2 + v w 1 ^ 2 + v w 2 ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Fin.sum_univ_succ, add_assoc]
      nlinarith
    have hh := integral_mono (hvA.integrable_sq.add hvB.integrable_sq)
      (hv.norm.integrable_sq.const_mul 3) hp
    rwa [integral_const_mul] at hh
  rw [integral_add hvA.integrable_sq hvB.integrable_sq] at hweights
  simp_rw [heq]
  have hca := hEa vA hvA
  have hcb := hEb vB hvB
  nlinarith
