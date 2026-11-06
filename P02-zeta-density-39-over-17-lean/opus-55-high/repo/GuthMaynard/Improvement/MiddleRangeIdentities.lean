module
public import GuthMaynard.Improvement.MiddleRangeScales
import WeylPort.Analytic.RealLaplace

public section
namespace GuthMaynard.Improvement

theorem middle_logs {N T : ℝ} (hn : 0 < N) (ht : 0 < T) :
    Real.log (middleLength N T) = (1/7:ℝ)*Real.log N+(5/7:ℝ)*Real.log T ∧
    Real.log (middleThreshold N T) = (5/7:ℝ)*Real.log N+(1/14:ℝ)*Real.log T ∧
    Real.log (middleMoment N T) = (18/7:ℝ)*Real.log N+(6/7:ℝ)*Real.log T := by
  unfold middleLength middleThreshold middleMoment
  constructor
  pm_4559
  constructor
  pm_4559
  pm_4559

section
variable {N T : ℝ} (hn : 0 < N) (ht : 0 < T)
include N T hn ht
theorem middle_length_threshold_identity :
    N*middleLength N T*(middleThreshold N T)^2 = middleMoment N T := by
  pm_4562
  pm_4560
  pm_4561
  pm_69 hll hlu hlp middle_logs hn ht
  apply Real.log_injOn_pos (by simp_all) hp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul hn.ne' hl.ne',Real.log_pow,hll,hlu,hlp]
  ring

theorem middle_moment_three_halves :
    N^4*T^2/middleLength N T = (middleMoment N T)^((3:ℝ)/2) ∧
      (middleMoment N T)^((3:ℝ)/2) = middleMoment N T*Real.sqrt (middleMoment N T) := by
  pm_4562
  pm_4561
  pm_7857
  constructor
  · apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    rw [Real.log_div (by positivity) hl.ne',Real.log_mul (by positivity) (by positivity),
      Real.log_pow,Real.log_pow,Real.log_rpow hp,hll,hlp]
    ring
  · apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    rw [Real.log_rpow hp,Real.log_mul hp.ne' (by positivity),Real.log_sqrt hp.le]
    ring

theorem middle_length_moment_square :
    N^5*middleLength N T*T = (middleMoment N T)^2 := by
  pm_4562
  pm_4561
  pm_7857
  pm_1592
  rw [Real.log_mul (by positivity) ht.ne',Real.log_mul (by positivity) hl.ne',
    Real.log_pow,Real.log_pow,hll,hlp]
  ring

theorem middle_threshold_square_quotient :
    T*N^4/(middleThreshold N T)^2 = middleMoment N T := by
  pm_4560
  pm_4561
  obtain ⟨_,hlu,hlp⟩ := middle_logs hn ht
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) hp
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul ht.ne' (by positivity),
    Real.log_pow,Real.log_pow,hlu,hlp]
  ring

theorem middle_threshold_fourth_quotient :
    T*N^4/(middleThreshold N T)^4 = N*middleLength N T := by
  pm_4562
  pm_4560
  obtain ⟨hll,hlu,_⟩ := middle_logs hn ht
  pm_1592
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul ht.ne' (by positivity),
    Real.log_mul hn.ne' hl.ne',Real.log_pow,Real.log_pow,hlu,hll]
  ring

theorem middle_cubic_budget
    (hhi : T ≤ N^((5:ℝ)/3)) : N^7*T^3 ≤ (middleMoment N T)^3 := by
  pm_4561
  have hh := Real.log_le_log ht hhi
  rw [Real.log_rpow hn] at hh
  pm_1094
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_pow,(middle_logs hn ht).2.2]
  linarith
end

end GuthMaynard.Improvement
