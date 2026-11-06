module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarGrowth
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNativeEquation
import Mathlib.Tactic

/-!
# Continuity of the reflected scalar profile

Joint axis limits and the anisotropic growth bound include both axes and the origin.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology

variable (gamma : ScalarGamma) (Lam : ℝ)

/-- The literal common axis trace is continuous. -/
theorem scalarTrace_continuous  :
    Continuous (scalarTrace gamma Lam) := by
  unfold scalarTrace

  exact continuous_const.mul ((Real.continuous_rpow_const ((mul_pos (by norm_num) gamma.2.1).le)).comp continuous_abs)

variable (hLam : 0 < Lam) (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) = Real.rpow Lam (-gamma.1))

include hLam hmatch
/-- The joint profile is continuous at every nonzero point of the position axis. -/
theorem scalarProfile_continuousAt_axis   (q : XV 1) (hx : q.1 0 = 0) (hv : q.2 0 ≠ 0) :
    ContinuousAt (scalarProfile gamma Lam) q := by
  have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
  let Sp : Set (XV 1) := {z | 0 < z.1 0}
  let Sn : Set (XV 1) := {z | z.1 0 < 0}
  let Sz : Set (XV 1) := {z | z.1 0 = 0}
  have ht : Sp ∪ Sn ∪ Sz = univ := by
    ext z
    simp only [Sp, Sn, Sz, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases lt_trichotomy (z.1 0) 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hq : scalarProfile gamma Lam q = scalarTrace gamma Lam (q.2 0) := by
    simp only [scalarProfile, hx, lt_self_iff_false, ↓reduceIte]
  change Tendsto _ (𝓝 q) _
  rw [hq, ← nhdsWithin_univ q, ← ht, nhdsWithin_union, nhdsWithin_union, tendsto_sup,
    tendsto_sup]
  constructor
  · constructor
    · have he := scalarAnsatz_tendsto_axis (𝓝[Sp] q) gamma Lam hLam hmatch
        (fun z => z.1 0) (fun z => z.2 0) (q.2 0) hv
        (by simpa only [hx] using
          ((hX.tendsto q).mono_left (nhdsWithin_le_nhds (s := Sp))))
        self_mem_nhdsWithin ((hV.tendsto q).mono_left nhdsWithin_le_nhds)
      apply he.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarProfile, show 0 < z.1 0 from hz, ↓reduceIte]
    · have he := scalarAnsatz_tendsto_axis (𝓝[Sn] q) gamma Lam hLam hmatch
        (fun z => -z.1 0) (fun z => -z.2 0) (-q.2 0) (neg_ne_zero.mpr hv)
        (by simpa only [hx, neg_zero] using
          (hX.tendsto q).neg.mono_left (nhdsWithin_le_nhds (s := Sn)))
        (by filter_upwards [self_mem_nhdsWithin] with z hz; exact neg_pos.mpr hz)
        ((hV.tendsto q).neg.mono_left nhdsWithin_le_nhds)
      rw [scalarTrace_neg] at he
      apply he.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarProfile, not_lt.mpr (show z.1 0 < 0 from hz).le,
        show z.1 0 < 0 from hz, ↓reduceIte]
  · have he := ((scalarTrace_continuous gamma Lam).comp hV).tendsto q
      |>.mono_left (nhdsWithin_le_nhds (s := Sz))
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [scalarProfile, show z.1 0 = 0 from hz, lt_self_iff_false, ↓reduceIte,
      Function.comp_def]

/-- The anisotropic growth bound proves continuity at the origin. -/
theorem scalarProfile_continuousAt_zero   : ContinuousAt (scalarProfile gamma Lam) 0 := by
  obtain ⟨K, hK, hb⟩ := scalarProfile_growth gamma Lam hLam hmatch



  have ht := (show Continuous (fun q : XV 1 => K *
      (Real.rpow |q.1 0| gamma.1 + Real.rpow |q.2 0| (3 * gamma.1))) from continuous_const.mul (((Real.continuous_rpow_const gamma.2.1.le).comp (by fun_prop)).add ((Real.continuous_rpow_const (mul_pos (by norm_num) gamma.2.1).le).comp (by fun_prop)))).tendsto (0 )
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, abs_zero, Real.rpow_eq_pow,
    Real.zero_rpow gamma.2.1.ne',
    Real.zero_rpow (mul_pos (by norm_num : (0 : ℝ) < 3) gamma.2.1).ne',
    zero_add, mul_zero] at ht


  simpa only [ContinuousAt, scalarProfile_zero] using ((tendsto_zero_iff_norm_tendsto_zero).mpr ((squeeze_zero (fun _ => abs_nonneg _) hb ht)))

/-- The literal scalar profile is continuous on the entire native carrier. -/
theorem scalarProfile_continuous   : Continuous (scalarProfile gamma Lam) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hx : q.1 0 = 0
  · by_cases hv : q.2 0 = 0
    · have hq : q = 0 := by
        apply Prod.ext <;> funext i
        all_goals have hi : i = 0 := Subsingleton.elim _ _
        all_goals subst i
        · exact hx
        · exact hv
      subst q
      exact scalarProfile_continuousAt_zero gamma Lam hLam hmatch
    · simp_all [scalarProfile_continuousAt_axis]
  · exact (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx).continuousAt

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
