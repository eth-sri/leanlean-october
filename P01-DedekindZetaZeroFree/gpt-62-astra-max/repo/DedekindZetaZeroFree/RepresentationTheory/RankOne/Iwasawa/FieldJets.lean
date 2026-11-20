module
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.NormalPrincipalCoefficient

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.BottomRowRadialContraction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Matrix.Norms.Operator Classical
namespace DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient (matrix_path_components matrix_bottom_basis_jet matrix_height_squared_basis_jet matrixHeightSquared matrix_height_squared_action gl_bottom_nonzero bottomRowJet)

section

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def bottomDenominator : ℝ :=
  Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

def bottomDenominatorJet (i : Fin 6) : ℝ :=
  ![2 * (Complex.normSq (g 1 0) - Complex.normSq (g 1 1)), 0,
    2 * (g 1 0 * star (g 1 1)).re, -2 * (g 1 0 * star (g 1 1)).im,
    2 * (g 1 0 * star (g 1 1)).re, 2 * (g 1 0 * star (g 1 1)).im] i

def horizontalNumerator : ℂ :=
  g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)

end

section

variable (g : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6)

def horizontalNumeratorJet : ℂ :=
  let h := g * KPSmoothActualFlowData.basisMatrix i
  h 0 0 * star (g 1 0) + g 0 0 * star (h 1 0) +
    (h 0 1 * star (g 1 1) + g 0 1 * star (h 1 1))

def horizontalFieldJet : ℂ :=
  (horizontalNumeratorJet g i * (bottomDenominator g : ℂ) -
    horizontalNumerator g * (bottomDenominatorJet g i : ℂ)) /
      (bottomDenominator g : ℂ)^2

def verticalFieldJet : ℝ :=
  -bottomDenominatorJet g i / bottomDenominator g

 theorem horizontalNumerator_hasDerivAt :
    HasDerivAt (fun t : ℝ => horizontalNumerator
      (g * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)))
      (horizontalNumeratorJet g i) 0 := by
  have h := matrix_path_components g (KPSmoothActualFlowData.basisMatrix i)
  have hd := ((h 0 0).mul (h 1 0).star).add ((h 0 1).mul (h 1 1).star)
  convert hd using 1
  · funext t
    rfl
  · simp only [horizontalNumeratorJet, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]

 theorem bottomDenominator_hasDerivAt :
    HasDerivAt (fun t : ℝ => bottomDenominator
      (g * NormedSpace.exp ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)))
      (bottomDenominatorJet g i) 0 :=
  matrix_bottom_basis_jet g i

end

section

variable (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)

private theorem actual_horizontal_formula :
    (KPArch.action g (0,0)).1 = horizontalNumerator g / (bottomDenominator g : ℂ) := by
  simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
    horizontalNumerator, bottomDenominator, Complex.sq_norm, add_comm]

theorem actual_horizontal_field_hasDerivAt (i : Fin 6) :
    HasDerivAt (fun t : ℝ => (KPArch.action
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)) (0,0)).1)
      (horizontalFieldJet g i) 0 := by
  have hD := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (bottomDenominator_hasDerivAt g i)
  have hN := horizontalNumerator_hasDerivAt g i
  have hn : (bottomDenominator g : ℂ) ≠ 0 := by
    exact_mod_cast gl_bottom_nonzero g
  have h := hN.div hD (by simpa using hn)
  convert h using 1
  · funext t
    exact actual_horizontal_formula _
  · simp only [horizontalFieldJet, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero,
      mul_one, Complex.ofRealCLM_apply, Function.comp_def]

private theorem actual_vertical_formula :
    (KPArch.action g (0,0)).2 = Real.log (matrixHeightSquared g) / 2 := by
  rw [matrix_height_squared_action]
  rw [Real.log_exp]
  ring

theorem actual_vertical_field_hasDerivAt (i : Fin 6) :
    HasDerivAt (fun t : ℝ => (KPArch.action
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)) (0,0)).2)
      (verticalFieldJet g i) 0 := by
  have hn : matrixHeightSquared g ≠ 0 := by
    rw [matrix_height_squared_action]
    exact Real.exp_ne_zero _
  have hd := ((matrix_height_squared_basis_jet g (gl_bottom_nonzero g) i).log (by simpa using hn)).div_const 2
  convert hd using 1
  · funext t
    exact actual_vertical_formula _
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    unfold verticalFieldJet bottomDenominatorJet bottomDenominator
    fin_cases i <;> simp [bottomRowJet] <;> field_simp <;> ring

theorem actual_six_field_hasDerivAt (i : Fin 6) :
    HasDerivAt (fun t : ℝ => KPArch.action
      (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • KPSmoothActualFlowData.basisMatrix i)) (0,0))
      (horizontalFieldJet g i, verticalFieldJet g i) 0 := (actual_horizontal_field_hasDerivAt g i).prodMk (actual_vertical_field_hasDerivAt g i)

end
 alias pgl_action_out := DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient.action_out



end DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets

end
