module
public import OAI.NumberTheory.DirichletL.Reflection.KernelActual
public import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

section
variable (Z : ℝ) (m : ℕ)
include Z m
lemma literal_ramified_log_width :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      (m:ℝ)*Real.logb Z 3 := by
  rw [ramifiedScale,one_mul,Real.logb_pow,completedRamifiedStep,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<3)]
  ring

lemma literal_ramified_width_offset :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      InverseTerminalWidths.ramifiedWidth Z m + 4*Real.logb Z 3 := by
  rw [literal_ramified_log_width]
  unfold InverseTerminalWidths.ramifiedWidth
  ring
end

lemma reflectedExponent_ramified_shift (O₀ H S₀ B₀ za v ell el Td δ : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td =
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell (el-δ) (Td-δ)-2*δ/3 := by
  unfold InverseTerminalWidths.reflectedExponent
  rw [show Td-δ-v-3*ell-(el-δ)=Td-v-3*ell-el by ring]
  ring

theorem literal_reflectedExponent_le_signed (Z : ℝ) (hZ : 1<Z) (m : ℕ)
    (O₀ H S₀ B₀ za v ell Td : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) Td ≤
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (InverseTerminalWidths.ramifiedWidth Z m) (Td-4*Real.logb Z 3) := by
  pm_6587 hδ hZ
  rw [reflectedExponent_ramified_shift O₀ H S₀ B₀ za v ell _ Td (4*Real.logb Z 3),
    literal_ramified_width_offset]
  rw [add_sub_cancel_right]
  linarith

end
end SevenEighths.InverseReflectedPhase

end OAI
