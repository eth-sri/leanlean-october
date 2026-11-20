module

public import AnalyticESC.Main.Criterion
public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# The polynomial example of Section 1.2.2

The system `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` lies in `𝔖_3` for
a sufficiently small `ε > 0`, has `c_max < 1/5`, `β ≤ 1` and distortions `1/2`-apart at `0`, so Proposition 1.8
shows that it satisfies the SESC.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace Example

noncomputable abbrev a : Fin 3 → ℝ := ![1/8,1/8,1/16]
noncomputable abbrev b : Fin 3 → ℝ := ![0,1/32,1/32]
noncomputable abbrev t : Fin 3 → ℝ := ![0,0,29/32]

lemma poly (i : Fin 3) : exampleMaps i = fun z : ℂ => a i*z + b i*z^2 + t i := by
  fin_cases i <;> norm_num [exampleMaps,a,b,t] <;> ring

lemma real (i : Fin 3) (x : ℝ) : exampleMaps i x = ((a i*x + b i*x^2 + t i : ℝ) : ℂ) := by
  simp [poly]

lemma jet (i : Fin 3) (z : ℂ) : HasDerivAt (exampleMaps i) (a i + 2*b i*z) z := by
  rw [poly]; convert ((((hasDerivAt_id' z).const_mul (a i : ℂ)).add ((hasDerivAt_pow 2 z).const_mul (b i : ℂ))).add_const (t i : ℂ)) using 1; push_cast; ring

lemma derivative (i : Fin 3) : deriv (exampleMaps i) = fun z : ℂ => a i + 2*b i*z := funext fun z => (jet i z).deriv

private lemma slope_range (i : Fin 3) {x : ℝ} (hx : x ∈ I) :
    0 ≤ 2*b i ∧ 2*b i ≤ a i+2*b i*x ∧ a i+2*b i*x ∈ Ioo 0 (1/5) := by
  obtain ⟨l,h⟩ := hx; fin_cases i <;> norm_num <;> grind

end Example
open Example

lemma example_domain : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ Challenge.cmax ε exampleMaps < 1/5 := by
  apply common_class (by norm_num) isOpen_univ (by simp) (fun i z _ => (jet i z).differentiableAt.differentiableWithinAt)
    (fun i x _ => by rw [real]; rfl)
  · intro i x hx; rw [real,Complex.ofReal_re]; obtain ⟨hx,hx'⟩ := hx
    fin_cases i <;> norm_num <;> constructor <;> nlinarith
  · intro i x hx; rw [derivative]; change ‖(a i:ℂ) + 2*b i*x‖ ∈ _; norm_cast; rw [Real.norm_eq_abs]
    have h := (slope_range i hx).2.2; rwa [abs_of_pos h.1]

noncomputable def exampleIFS : IFS 3 := ⟨exampleMaps,example_domain.choose_spec.1,example_domain.choose_spec.2.1⟩
lemma exampleIFS_cmax_lt : exampleIFS.cmax < 1/5 := example_domain.choose_spec.2.2

lemma example_nonlin (i : Fin 3) (x : ℝ) : exampleIFS.nonlin i x = ((2*b i/(a i+2*b i*x) : ℝ) : ℂ) := by
  unfold IFS.nonlin; change deriv (deriv (exampleMaps i)) x / deriv (exampleMaps i) x = _
  simp [derivative]

theorem exampleIFS_beta_le : exampleIFS.beta ≤ 1 := by
  refine ciSup_le fun x => ciSup_le fun i => ?_
  rw [example_nonlin,Complex.norm_real,Real.norm_eq_abs]
  obtain ⟨l,h,e⟩ := slope_range i x.2
  rwa [abs_of_nonneg (div_nonneg l e.1.le),div_le_one e.1]

theorem exampleIFS_nonlin_sep (i j : Fin 3) (hij : i ≠ j) :
    (1 / 2 : ℝ) ≤ ‖exampleIFS.nonlin i 0 - exampleIFS.nonlin j 0‖ := by
  rw [← Complex.ofReal_zero,example_nonlin,example_nonlin,← Complex.ofReal_sub,Complex.norm_real]
  fin_cases i <;> fin_cases j <;> norm_num  at *

/-- The example satisfies the SESC. -/
theorem exampleIFS_sesc : exampleIFS.SESC := by
  have sep : exampleIFS.Spread (1/2) := fun i j hij => ⟨0,exampleIFS_nonlin_sep i j hij⟩
  apply exampleIFS.theorem_1_5; intro v w h
  apply exampleIFS.infinite_criterion sep _ h
  have hc := exampleIFS_cmax_lt
  have hb := exampleIFS_beta_le
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [exampleIFS.cmax_nonneg]

end AnalyticESC
