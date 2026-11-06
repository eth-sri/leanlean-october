module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.KernelActual
public import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss


lemma literal_ramified_log_width  Z   m  :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      (m:ℝ)*Real.logb Z 3 := by
  rw [ramifiedScale,one_mul,Real.logb_pow,completedRamifiedStep,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<3)]
  ring

lemma literal_ramified_width_offset  Z   m  :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      InverseTerminalWidths.ramifiedWidth Z m + 4*Real.logb Z 3 := by
  rw [literal_ramified_log_width]
  unfold InverseTerminalWidths.ramifiedWidth
  ring

lemma reflectedExponent_ramified_shift  O₀ H S₀ B₀ za v ell el Td δ  :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td =
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell (el-δ) (Td-δ)-2*δ/3 := by
  grind [InverseTerminalWidths.reflectedExponent]

theorem literal_reflectedExponent_le_signed  Z  (hZ : 1<Z)  m 
     O₀ H S₀ B₀ za v ell Td  :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) Td ≤
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (InverseTerminalWidths.ramifiedWidth Z m) (Td-4*Real.logb Z 3) := by
  have hδ : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hZ (by norm_num))
  rw [reflectedExponent_ramified_shift O₀ H S₀ B₀ za v ell _ Td (4*Real.logb Z 3),
    literal_ramified_width_offset]
  rw [add_sub_cancel_right]
  linarith


end SevenEighths.InverseReflectedPhase

end OAI
