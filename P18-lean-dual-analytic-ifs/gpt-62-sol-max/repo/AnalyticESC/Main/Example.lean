module

public import AnalyticESC.Main.Criterion
public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# The polynomial example of Section 1.2.2

The system `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` lies in `𝔖_3` for
`ε = 1/100`, has `c_max < 1/5`, `β ≤ 1` and distortions `1/2`-apart at `0`, so Proposition 1.8
shows that it satisfies the SESC.
-/

namespace AnalyticESC

open Set Metric Filter Topology

export Challenge (exampleMaps)

noncomputable abbrev exampleLinear (i : Fin 3) : ℝ := ![4, 4, 2] i
noncomputable abbrev exampleQuadratic (i : Fin 3) : ℝ := ![0, 1, 1] i
noncomputable abbrev exampleTranslation (i : Fin 3) : ℝ := ![0, 0, 29] i

private theorem exampleMaps_eq (i : Fin 3) (z : ℂ) :
    exampleMaps i z = (exampleLinear i * z + exampleQuadratic i * z ^ 2 + exampleTranslation i) / 32 := by
  fin_cases i <;> norm_num [exampleMaps, exampleLinear, exampleQuadratic, exampleTranslation] <;> ring

theorem exampleMaps_ofReal (i : Fin 3) (x : ℝ) :
    exampleMaps i x = ↑((exampleLinear i * x + exampleQuadratic i * x ^ 2 + exampleTranslation i) / 32 : ℝ) := by
  push_cast
  exact exampleMaps_eq ..

private theorem exampleMaps_deriv (i : Fin 3) :
    deriv (exampleMaps i) = fun z => ((exampleLinear i : ℂ) + 2 * exampleQuadratic i * z) / 32 := by
  funext z
  rw [funext (exampleMaps_eq i)]
  have h := (((hasDerivAt_id' z).const_mul (exampleLinear i : ℂ)).add
    ((hasDerivAt_pow 2 z).const_mul (exampleQuadratic i : ℂ))).add_const (exampleTranslation i : ℂ) |>.div_const 32
  refine h.deriv.trans ?_
  ring

private theorem exampleMaps_deriv_deriv (i : Fin 3) (z : ℂ) :
    deriv (deriv (exampleMaps i)) z = 2 * (exampleQuadratic i : ℂ) / 32 := by
  simp [exampleMaps_deriv]

theorem exampleMaps_zero_jet {i : Fin 3} (hi : i ≠ 2) :
    exampleMaps i 0 = 0 ∧ deriv (exampleMaps i) 0 = 1 / 8 := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    norm_num [exampleMaps_eq, exampleMaps_deriv, exampleLinear, exampleQuadratic, exampleTranslation]

private theorem norm_deriv_bounds (i : Fin 3) {z : ℂ} (hz : z ∈ closedNbhd (1 / 100)) :
    deriv (exampleMaps i) z ≠ 0 ∧ ‖deriv (exampleMaps i) z‖ ≤ 19 / 100 := by
  obtain ⟨x, hx, hd⟩ := exists_mem_I_norm_sub_le (by norm_num) hz
  have hre := abs_le.1 ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hnorm := norm_le_norm_sub_add z (x : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] at hnorm
  rw [exampleMaps_deriv]
  constructor
  · intro he
    have := congrArg Complex.re he
    fin_cases i <;> norm_num [exampleLinear, exampleQuadratic, Complex.add_re, Complex.mul_re,
      Complex.div_ofNat_re] at this <;> linarith [hre.1, hx.1]
  · rw [norm_div]
    norm_num
    apply div_le_iff₀ (by norm_num) |>.2
    refine (norm_add_le ..).trans ?_
    rw [norm_mul _ z, norm_mul]
    fin_cases i <;> norm_num <;> grind

theorem exampleMaps_inClass (i : Fin 3) : InClass (1 / 100) (exampleMaps i) := by
  refine Challenge.InClass.of_deriv (by norm_num) ?_ (fun x _ => by rw [exampleMaps_ofReal, Complex.ofReal_im])
    (fun x hx => ?_) (fun _ hz => (norm_deriv_bounds i hz).1)
    (fun _ hz => (norm_deriv_bounds i hz).2.trans_lt (by norm_num))
  · rw [funext (exampleMaps_eq i)]
    fun_prop
  · rw [exampleMaps_ofReal, Complex.ofReal_re]
    fin_cases i <;> norm_num [exampleLinear, exampleQuadratic, exampleTranslation, I] <;>
      constructor <;> nlinarith [hx.1, hx.2, mul_nonneg hx.1 (sub_nonneg.2 hx.2)]

/-- The example as an analytic IFS. -/
noncomputable def exampleIFS : IFS 3 (1 / 100) := ⟨exampleMaps, by norm_num, exampleMaps_inClass⟩

theorem exampleIFS_cmax_lt : exampleIFS.cmax < 1 / 5 := by
  have h : exampleIFS.cmax ≤ 19 / 100 := Real.iSup_le
    (fun i => Real.iSup_le (fun z => (norm_deriv_bounds i z.2).2) (by norm_num)) (by norm_num)
  linarith

private theorem exampleNonlin_ofReal (i : Fin 3) (x : ℝ) : exampleIFS.nonlin i x =
    ((2 * exampleQuadratic i / (exampleLinear i + 2 * exampleQuadratic i * x) : ℝ) : ℂ) := by
  change deriv (deriv (exampleMaps i)) x / deriv (exampleMaps i) x = _
  rw [exampleMaps_deriv_deriv, exampleMaps_deriv, div_div_div_cancel_right₀ (by norm_num)]
  push_cast
  rfl

theorem exampleIFS_beta_le : exampleIFS.beta ≤ 1 := by
  refine Real.iSup_le (fun x => Real.iSup_le (fun i => ?_) zero_le_one) zero_le_one
  rw [exampleNonlin_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hx := x.2.1
  fin_cases i <;> norm_num [abs_div] <;> rw [abs_of_nonneg (by linarith), div_le_one (by linarith)] <;> linarith

private lemma nonlin_zero_table (i : Fin 3) : exampleIFS.nonlin i 0 = ![(0 : ℂ), 1 / 2, 1] i := by
  rw [← Complex.ofReal_zero, exampleNonlin_ofReal]
  fin_cases i <;> norm_num

theorem exampleIFS_nonlin_sep (i j : Fin 3) (hij : i ≠ j) :
    (1 / 2 : ℝ) ≤ ‖exampleIFS.nonlin i 0 - exampleIFS.nonlin j 0‖ := by
  simp_rw [nonlin_zero_table]
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num

/-- The example satisfies the criterion for strong exponential separation. -/
theorem exampleIFS_sesc : exampleIFS.SESC := by
  apply exampleIFS.theorem_2_2
  intro i j hij
  apply exampleIFS.exists_dualProj_ne_of_get?_zero (α := 1/2)
    (fun a b hab => ⟨⟨0, by simp⟩, by simpa using exampleIFS_nonlin_sep a b hab⟩) _ (i := .inf i) (j := .inf j) rfl rfl hij
  rw [div_lt_iff₀ (by linarith [exampleIFS_cmax_lt])]
  nlinarith [exampleIFS_beta_le, exampleIFS.cmax_nonneg, exampleIFS_cmax_lt,
    mul_nonneg (sub_nonneg.2 exampleIFS_beta_le) exampleIFS.cmax_nonneg]

end AnalyticESC
