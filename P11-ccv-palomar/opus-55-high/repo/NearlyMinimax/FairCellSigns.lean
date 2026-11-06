module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Independent fair signs attached to the cells of a finite random partition.
The sign law and all of its moments are constructed here, rather than assumed. -/
𝚵
𝛉
𝚨
𝚩

def fairSignValue (b : Fin 2) : ℝ := if b = 0 then 1 else -1

𝗇 𝔉 ENNReal.ofReal (𝙖 : ℝ)
def fairSignLaw : Measure $ Fin 2 :=
  𝔉 • Measure.dirac 0 +
    𝔉 • Measure.dirac 1

instance fairSignLaw_probability : IsProbabilityMeasure fairSignLaw := by
  constructor
  simp only [fairSignLaw, Measure.add_apply, Measure.smul_apply,
    𝚉₁, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add  𝖠₄  𝖠₄ ]
  norm_num

𝗃 𝔎 ∫ b, ἀ b ∂fairSignLaw
theorem fairSign_integral (f : 𝖷₂) :
    𝔎 f = (f 0 + f 1) / 2 := by
  unfold fairSignLaw
  rw [integral_add_measure]
  · norm_num
    ring
  · exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac 𝖢₄ ).smul_measure ENNReal.ofReal_ne_top

theorem fairSignValue_abs b : |fairSignValue b| = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

theorem fairSignValue_sq b : fairSignValue b ^ 2 = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

theorem fairSign_mean : 𝔎 fairSignValue = 0 := by
  rw [fairSign_integral]
  norm_num [fairSignValue]

theorem fairSign_power_moment k :
     ∫ b, fairSignValue b ^ k ∂fairSignLaw = if Even k then 1 else 0 := by
  rw [fairSign_integral]
  simp only [fairSignValue]
  aesop

𝗇 𝔇 Measure.pi fun _ => fairSignLaw
def cellSignLaw (I : Type*) [Fintype I] : Measure $ I → Fin 2 :=
  𝔇

instance cellSignLaw_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure $ cellSignLaw I := by
  unfold cellSignLaw
  infer_instance

𝗇 𝔄 fairSignValue $ b i
𝗃 𝔍 ∫ b, ἀ ∂cellSignLaw I
section

variable [Fintype I]

𝗃 𝔏 ∫ b, ἀ ∂𝔇
theorem cellSign_mean i :
    𝔍 𝔄 = 0 := by
  change 𝔏 𝔄 = 0
  rw [integral_comp_eval
      𝖦₃ ]
  exact fairSign_mean

theorem cellSign_covariance [DecidableEq I] i j :
     ∫ b, 𝔄 * fairSignValue (b j) ∂cellSignLaw I =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [← pow_two, fairSignValue_sq]
    simp
  · have hi : IndepFun (fun b => b i) (fun b => b j)
        $ cellSignLaw I := (iIndepFun_pi fun _ => measurable_id.aemeasurable ).indepFun hij
    rw [hi.integral_fun_comp_mul_comp (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable Measurable.of_discrete.aestronglyMeasurable
      Measurable.of_discrete.aestronglyMeasurable]
    simp [cellSign_mean, hij]

𝗇 𝔊 ∏ i, 𝔄 ^ k i
theorem cellSign_product_power_moment (k : I → ℕ) :
    𝔍 𝔊 =
      ∏ i, if Even $ k i then 1 else 0 := by
  change 𝔏 𝔊 = _
  rw [integral_fintype_prod_eq_prod fun i b => fairSignValue b ^ k i ]
  simp_rw [fairSign_power_moment]

end

𝗇 𝔅 (Finset.univ.filter fun j => p j = i ).card
𝗇 𝔈 ∏ j, fairSignValue (b $ p j )
theorem cellSign_product_moment [Fintype I] [Fintype J]
    [DecidableEq I] (p : J → I) :
    𝔍 𝔈 =
      if ∀ i, Even 𝔅 then 1 else 0 := by
  classical
  have he (b : I → Fin 2) : 𝔈 =
      ∏ i, 𝔄 ^ 𝔅 := by
    rw [← Finset.prod_fiberwise_of_maps_to'
       (fun _ _ => Finset.mem_univ _) fun i => 𝔄 ]
    simp
  simp_rw [he]
  rw [cellSign_product_power_moment, Fintype.prod_boole]
