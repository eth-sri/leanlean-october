module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Exponent
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimit
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Strict upper gap for the homogeneous adjoint exponent -/

 public section

open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Degree two provides the lower bound for the chosen exponent. -/
theorem bellmanAdjointExponent_two_le (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR :=
  (bellmanAdjointExponent_characterization R hR).1.1
    (two_mem_bellmanAdmissibleDegrees R hR)

variable (R : ℝ) (hR : 1 ≤ R)

/-- The excluded endpoint remains excluded after taking the supremum of admissible degrees. -/
theorem bellmanAdjointExponent_lt_three  :
    bellmanAdjointExponent R hR < 3 := by
  have hlu := (bellmanAdjointExponent_characterization R hR).1

  by_contra hlt
  have heq  := le_antisymm (hlu.2 (fun b hb => (admissible_degree_lt_three R hR b hb).le)) (le_of_not_gt hlt)
  have hex (n : ℕ) : ∃ b ∈ bellmanAdmissibleDegrees R,
      3 - 1 / ((n : ℝ) + 1) < b ∧ b ≤ 3 := by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simpa only [heq] using hlu.exists_between (by rw [heq]; linarith)
  choose beta hb hlo hhi using hex
  have hpairs (n : ℕ)  :=
    (mem_bellmanAdmissibleDegrees_iff R (beta n)).mp (hb n)
  choose mu eta hp using hpairs


  obtain ⟨chi, hchi, hc, hs, _, _, _, c, hcp, hcn, k, hk,
    muInf, etaInf, hmInf, heInf, hmv, hev⟩ :=
    homogeneous_pairs_subsequence R hR beta mu eta hp (by
        refine ⟨2, 3, fun n => ⟨?_, hhi n⟩⟩

        have hi : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
        linarith [hlo n])

  have hlim := bellman_vague_limit_pair R 3 hR (fun n => beta (k n))
    (fun n => ENNReal.ofReal (c (k n)) • mu (k n))
    (fun n => ENNReal.ofReal (c (k n)) • eta (k n)) muInf etaInf
    ((show Tendsto beta atTop (𝓝 (3 )) by

        exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by
            simpa using (tendsto_const_nhds (x := (3 : ℝ))).sub
              (tendsto_one_div_add_atTop_nhds_zero_nat )) tendsto_const_nhds
          (fun n => (hlo n).le) hhi).comp hk.tendsto_atTop)
    (fun n => (hp (k n)).smul (c (k n)) (hcp (k n)))
    hmInf heInf hmv hev chi hchi.continuous hc (by
        intro q hq hz
        have hg := (hs hq).1
        rw [hz] at hg
        norm_num [bellmanGauge, bellmanGaugePower] at hg) (fun n => hcn (k n))

  exact (lt_irrefl (3 : ℝ)) (admissible_degree_lt_three R hR 3 ((mem_bellmanAdmissibleDegrees_iff R 3).mpr ⟨muInf, etaInf, hlim.1⟩))

/-- The normalized homogeneous adjoint exponent lies in the source's half-open interval. -/
theorem bellmanAdjointExponent_range  :
    2 ≤ bellmanAdjointExponent R hR ∧ bellmanAdjointExponent R hR < 3 :=
  ⟨bellmanAdjointExponent_two_le R hR, bellmanAdjointExponent_lt_three R hR⟩

end HypoellipticAleksandrov.KineticAleksandrov
