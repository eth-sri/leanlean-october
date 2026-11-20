module
public import MathCollab.Density.Stronger.ShortFixedFamily

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger




theorem shortTaylor_cutoff_error_eventually :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 1 ≤ Real.log T ∧
      3*T^(-1 : ℝ) ≤ 1/(96*Real.log T) := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at ht
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1/288 by norm_num))] with T hT hlog hh
  refine ⟨hT, hlog, ?_⟩
  have hTpos : 0 < T := by linarith
  have hlo : Real.log T < T/288 := (div_lt_iff₀ hTpos).mp hh |>.trans_eq (by ring)
  rw [Real.rpow_neg_one]
  apply (le_div_iff₀ (by positivity : 0 < 96*Real.log T)).mpr
  have he : 3*T⁻¹*(96*Real.log T) = (288*Real.log T)/T := by ring
  rw [he]
  exact (div_le_one hTpos).mpr (by linarith)



end MathCollab.Density.Stronger
