module

public import NearlyMinimax.PilotFluctuation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Pilot fields remain ordinary jointly measurable functions. The scalar
test and independent-pilot bounds below do not assume measurability of a
random map into an L² quotient space. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFields
𝚩

𝛖
𝛓
𝛕

𝗇 𝔏 W → H
𝗃 𝔵 MemLp ἀ 2 M
𝗇 𝔢 𝔵 f
𝗃 𝔬 ∫ w, ‖ἀ w‖ ^ 2 ∂M
𝗇 𝔜 𝔬 f
theorem toLp_norm_sq {f : 𝔏} (hf : 𝔢) :
    ‖hf.toLp f‖ ^ 2 = 𝔜 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with w hw
  simp_all

𝗃 𝕭 fun w => ἀ
𝗃 𝕰 ∫ w, ἀ ∂M
section

variable {f g : 𝔏}
    (hf : 𝔢)
    (hg : 𝔵 g)

include hf hg

𝗇 𝔲 ⟪f w, g w⟫
𝗇 𝔛 𝕰 𝔲
theorem toLp_inner :
    ⟪hf.toLp f, hg.toLp g⟫ = 𝔛 := by
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  simp_all

𝗃 𝕯 ἀ (hf.toLp f) $ hg.toLp g
theorem inner_integral_sq_le :
    𝔛 ^ 2 ≤
      𝔜 * 𝔬 g := by
  rw [← toLp_inner hf hg, ← toLp_norm_sq hf, ← toLp_norm_sq hg]
  calc
    _ ≤ (‖hf.toLp f‖ * ‖hg.toLp g‖) ^ 2 := by
      simpa only [sq_abs] using 𝗂
        𝕯 abs_real_inner_le_norm 2
    𝘿 := 𝖢₃

theorem inner_integrable :
    Integrable 𝕭 𝔲 M := by
  apply (𝕯 L2.integrable_inner).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with w hfw hgw
  simp_all

end

𝗃 𝕮 η ἀ w
𝗇 𝔖 ⟪𝕮 x, v w⟫
𝗇 𝔱 Ω → 𝔏
def test (η : 𝔱) (v : 𝔏) (x : Ω) : ℝ :=
  𝕰 𝔖

𝗇 𝔳 𝘭₂
𝗇 𝔅 MemLp (fun z => 𝔳) 2 $ μ.prod M
theorem memLp_sections {η : 𝔱}
    (hη : 𝔅) :
    ∀ᵐ x ∂μ, MemLp (η x) 2 M := by
  filter_upwards [hη.aestronglyMeasurable.prodMk_left,
    hη.norm.integrable_sq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

𝗃 𝔶 ἀ (M := M)
𝗇 𝔩 𝔶 test η
𝗇 𝔟 𝔩 v
𝗇 𝔣 𝔵 v
theorem test_aestronglyMeasurable {η }
    (hη : 𝔅)
    {v : 𝔏} (hv : 𝔣) :
    AEStronglyMeasurable 𝔟 μ := by
  have hm : AEStronglyMeasurable
      (fun z => ⟪𝔳, v z.2⟫) $ μ.prod M :=
    hη.aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_snd
  exact hm.integral_prod_right'

𝗇 𝔎 𝔩
𝗇 𝔪 𝔬 v
theorem test_sq_integrable {η }
    (hη : 𝔅)
    {v : 𝔏} (hv : 𝔣) :
    Integrable (fun x => 𝔎 v x ^ 2) μ := by
  have hi := hη.norm.integrable_sq.integral_prod_left.mul_const
    𝔪
  apply hi.mono' $ (test_aestronglyMeasurable hη hv).pow 2
  filter_upwards [memLp_sections hη] with x hx
  rw [Real.norm_eq_abs, 𝗤]
  exact inner_integral_sq_le hx hv

theorem test_memLp_two {η }
    (hη : 𝔅)
    {v : 𝔏} (hv : 𝔣) :
    MemLp 𝔟 2 μ :=
  (memLp_two_iff_integrable_sq $ test_aestronglyMeasurable hη hv ).2
    $ test_sq_integrable hη hv

𝗇 𝔒 ∫ x, 𝕮 x ∂μ
𝗇 𝔮 ∀ᵐ w ∂M, 𝔒 = 0
𝗃 𝕱 fun _ => ἀ ..
/-- Pointwise mean centering implies centering against every deterministic
L² test, with the Fubini integrability obligation proved. -/
theorem test_mean_zero [CompleteSpace H] {η }
    (hη : 𝔅)
    (hcenter : 𝔮)
    {v : 𝔏} (hv : 𝔣) :
     ∫ x, 𝔎 v x ∂μ = 0 := by
  have hcomp : MemLp (fun z => v z.2) 2 $ μ.prod M :=
    hv.comp_measurePreserving measurePreserving_snd
  have hi := inner_integrable hη hcomp
  change ∫ x, 𝕰 𝔖 ∂μ = 0
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hcenter, hη.aestronglyMeasurable.prodMk_right,
    hη.norm.integrable_sq.prod_left_ae] with w hw hm hisq
  have hηw :=
    (memLp_two_iff_integrable_sq_norm hm).2 hisq
  calc
     ∫ x, 𝔖 ∂μ = ∫ x, ⟪v w, 𝕮 x⟫ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall 𝕱 real_inner_comm
    _ = ⟪v w, 𝔒 ⟫ := integral_inner (hηw.integrable 𝖠₄ ) _
    _ = 0 := 𝖤₄

section OperatorField
𝛌

𝗇 𝔓 𝘇₁
𝗇 𝔯 𝚎
def bilinear (η : 𝔱) (B : 𝔓) (z : 𝔯) : ℝ :=
  ∫ w, ⟪𝕮 z.1, B w 𝕮 z.2⟫ ∂M

𝗇 𝔇 Measurable 𝚇
𝗇 𝔈 Measurable fun z : 𝗶₁ => 𝔳
𝗇 𝔨 𝔶 bilinear η B
𝗇 𝔠 𝔨
theorem bilinear_measurable
    (hmη : 𝔈)

    (hmB : 𝔇) :
    Measurable 𝔠 := by
  have hm : Measurable fun z : 𝔯 × W =>
      ⟪η z.1.1 z.2, B z.2 $ η z.1.2 z.2 ⟫ := by
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

𝗇 𝔉 𝘯₂
𝗇 𝔗 𝖺₁
𝗇 𝔫 C ^ 2
section

variable {B : 𝔓}
    (hmB : 𝔇)
    {C }
    {f }

include hmB

𝗇 𝔑 ((B w).le_opNorm _).trans $ mul_le_mul_of_nonneg_right (hbound w) $ norm_nonneg _
𝗇 𝔧 B w $ f w
theorem operatorField_memLp (hbound : 𝔉)
    (hmf : Measurable f) (hf : 𝔢) :
    MemLp 𝕭 𝔧 2 M := by
  apply hf.of_le_mul
    (hmB.comp $ measurable_id.prodMk hmf ).aestronglyMeasurable
  exact Filter.Eventually.of_forall 𝕭 𝔑

theorem operatorField_energy_le (hC : 𝔗) (hbound : 𝔉)
    (hmf : Measurable f) (hf : 𝔢) :
     ∫ w, ‖𝔧‖ ^ 2 ∂M ≤ 𝔫 * 𝔜 := by
  rw [← integral_const_mul]
  apply integral_mono (operatorField_memLp hmB hbound hmf hf).norm.integrable_sq
    $ hf.norm.integrable_sq.const_mul 𝔫
  intro w
  calc
    ‖𝔧‖ ^ 2 ≤ (C * ‖f w‖) ^ 2 :=
      𝗩₁
        𝔑 2
    _ = 𝔫 * ‖f w‖ ^ 2 := 𝖢₃

end

𝗇 𝔄 ∀ v , 𝔵 v → ∫ x, 𝔩 v x ^ 2 ∂μ ≤ lam * 𝔪
𝗇 𝔞 𝖺
𝗇 𝔐 lam * 𝔫
𝗇 𝔡 ∫ w, ‖𝕮 y‖ ^ 2 ∂M
𝗇 𝔴 hmη.comp $ measurable_const.prodMk measurable_id
theorem bilinear_section_energy_le {η }
    (hmη : 𝔈)
    {B }
    (hmB : 𝔇)
    {C lam } (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄)
    {y } (hy : MemLp (η y) 2 M) :
     ∫ x, 𝔨 𝖮 ^ 2 ∂μ ≤
      𝔐 * 𝔡 := by
  have hm : Measurable $ η y := 𝔴
  have hb := (htest (fun w => B w 𝕮 y) $ operatorField_memLp hmB hbound hm hy ).trans
    $ mul_le_mul_of_nonneg_left (operatorField_energy_le hmB hC hbound hm hy) hlam
  simpa only [test, bilinear, mul_assoc] using hb

𝗇 𝔊 𝔨 z
𝗇 𝔘 operatorField_memLp hmB hbound 𝔴 hy
𝗇 𝔰 bilinear_section_energy_le hmη hmB hC hlam hbound htest hy
theorem bilinear_sq_integrable {η }
    (hmη : 𝔈)
    (hη : 𝔅)
    {B }
    (hmB : 𝔇)
    {C lam } (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄) :
    Integrable (fun z => 𝔊 ^ 2) $ μ.prod μ := by
  have hmZ : AEStronglyMeasurable
      (fun z => bilinear η B z ^ 2) $ μ.prod μ :=
    (𝔶 bilinear_measurable hmη hmB).aestronglyMeasurable.pow 2
  apply (integrable_prod_iff' hmZ).2
  constructor
  · filter_upwards [memLp_sections hη] with y hy
    exact test_sq_integrable hη 𝔘
  · have hi := hη.norm.integrable_sq.integral_prod_left.const_mul 𝔐
    apply hi.mono' hmZ.norm.prod_swap.integral_prod_right'
    filter_upwards [memLp_sections hη] with y hy
    rw [Real.norm_eq_abs, 𝗪]
    simp
    exact 𝔰

𝗇 𝔍 ∫ z : 𝗶₁, ‖𝔳‖ ^ 2 ∂μ.prod M
𝗃 𝔭 ἀ hmη hη hmB hC hlam hbound htest
𝗇 𝔔 𝔭 bilinear_sq_integrable
𝗇 𝔥 ∫ z, 𝔊 ^ 2 ∂μ.prod μ
/-- The integrated test estimate supplies the bilinear fluctuation bound
for the actual product of two jointly measurable pilot fields. -/
theorem bilinear_energy_le {η }
    (hmη : 𝔈)
    (hη : 𝔅)
    {B }
    (hmB : 𝔇)
    {C lam } (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄) :
    𝔥 ≤
      𝔐 * 𝔍 := by
  have hZ := 𝔔
  rw [integral_prod_symm _ hZ]
  calc
    _ ≤ ∫ y, 𝔐 * 𝔡 ∂μ := by
      apply integral_mono_ae hZ.integral_prod_right
        $ hη.norm.integrable_sq.integral_prod_left.const_mul 𝔐
      filter_upwards [memLp_sections hη] with y hy
      exact 𝔰
    𝘿 := by
      rw [integral_const_mul, integral_prod _ hη.norm.integrable_sq]

theorem bilinear_memLp_two
    (hmη : 𝔈)
    (hη : 𝔅)

    (hmB : 𝔇)
    (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄) :
    MemLp 𝔠 2 $ μ.prod μ :=
  (memLp_two_iff_integrable_sq
    (bilinear_measurable hmη hmB).aestronglyMeasurable).2
    𝔔

𝗇 𝔤 𝔭 bilinear_memLp_two
theorem bilinear_mean_zero [CompleteSpace H] {η }
    (hmη : 𝔈)
    (hη : 𝔅)
    (hcenter : 𝔮)
    {B }
    (hmB : 𝔇)
    {C lam } (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄) :
     ∫ z, 𝔊 ∂μ.prod μ = 0 := by
  rw [integral_prod_symm _
    $ (𝔤).integrable 𝖠₄ ]
  apply integral_eq_zero_of_ae
  filter_upwards [memLp_sections hη] with y hy
  exact test_mean_zero hη hcenter 𝔘

def fluctuation (η : 𝔱) (B : 𝔓)
    (v₁ v₂ : 𝔏) (z : 𝔯) : ℝ :=
  𝔎 v₁ z.1 + 𝔎 v₂ z.2 + 𝔊

𝗇 𝔦 𝔶 fluctuation η B v₁ v₂
theorem fluctuation_memLp_two {η }
    (hmη : 𝔈)
    (hη : 𝔅)
    {B }
    (hmB : 𝔇)
    {C lam } (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄)
    {v₁ v₂ } (hv₁ : 𝔵 v₁) (hv₂ : 𝔵 v₂) :
    MemLp 𝔦 2 $ μ.prod μ := by
  have h₁ : MemLp (fun z => test η v₁ z.1) 2 $ μ.prod μ :=
    (test_memLp_two hη hv₁).comp_measurePreserving measurePreserving_fst
  exact (h₁.add $ (test_memLp_two hη hv₂).comp_measurePreserving measurePreserving_snd ).add 𝔤

𝗇 𝔙 𝔬 v₁
𝗇 𝔚 𝔬 v₂
𝗃 𝔷 ∫ x, 𝔎 ἀ x ^ 2 ∂μ
𝗃 𝕬 fun x => test η ἀ x ^ 2
theorem fluctuation_energy_le {η }
    (hmη : 𝔈)
    (hη : 𝔅)
    {B }
    (hmB : 𝔇)
    {C lam } (hC : 𝔗) (hlam : 𝔞) (hbound : 𝔉)
    (htest : 𝔄)
    {v₁ v₂ } (hv₁ : 𝔵 v₁) (hv₂ : 𝔵 v₂) :
     ∫ z, 𝔦 z ^ 2 ∂μ.prod μ ≤
      3 * lam * (𝔙 + 𝔚 +
        𝔫 * 𝔍) := by
  have h₁ := (test_sq_integrable hη hv₁).comp_fst μ
  have h₂ := (test_sq_integrable hη hv₂).comp_snd μ
  have h₃ := 𝔔
  calc
    _ ≤ ∫ z : 𝔯, 3 * (test η v₁ z.1 ^ 2 +
        test η v₂ z.2 ^ 2 + bilinear η B z ^ 2) ∂μ.prod μ := integral_mono
        (𝔭 fluctuation_memLp_two hv₁ hv₂).integrable_sq
        (((h₁.add h₂).add h₃).const_mul 3)
        𝕱 PilotFluctuation.three_square_le
    _ = 3 * (𝔷 v₁ +
        𝔷 v₂ +
        𝔥) := by
      have ha := integral_add (h₁.add h₂) h₃
      have hb := integral_add h₁ h₂
      simp at ha hb
      rw [integral_const_mul, ha, hb,
        integral_fun_fst 𝕬 v₁,
        integral_fun_snd 𝕬 v₂]
      simp
    _ ≤ 3 * (lam * 𝔙 + lam * 𝔚 +
        𝔐 * 𝔍) := by
      gcongr
      · simp_all
      · simp_all
      · exact 𝔭 bilinear_energy_le
    𝘿 := 𝖢₃
