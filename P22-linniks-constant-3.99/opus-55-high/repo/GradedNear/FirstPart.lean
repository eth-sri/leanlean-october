module

public import GradedNear.FirstFactor
public import GradedNear.Basic

/-!
# The first Cauchy–Schwarz factor for the data of the lemma

`𝓛⁻¹ Σ_{1 ≤ n ≤ q^{x_f}} (Λ(n)/n) e^{2 s t_n} f(t_n)² / ω(t_n) ≤ I_B + ε` for all large `q`.
This applies `riemann_upper` to `φ(u) = e^{2su} f(u)² / ω(u)`. `φ` is bounded on `[0, x_f]`
because `ω ≥ c > 0` wherever `f ≠ 0`. It is continuous on `(0, x_f)` away from the
cell endpoints `t_k`; where `ω(u) = 0` we have `f = 0` nearby, so `φ = 0`. Its integral over
`[0, x_f]` is `I_B`, since `f = 0` on `[x_f, ∞)`.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear


open Filter Topology MeasureTheory in
theorem first_factor_bound (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, Λ n / n *
          (Real.exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n))) /
        Real.log q ≤ D.IB + ε := by
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  have hφ v (hv : 0 ≤ v) : |Real.exp (2 * D.s * v) * D.f v ^ 2 / D.omega v| ≤
      Real.exp (2 * D.s * v) * D.f v ^ 2 / c := by
    by_cases hf : D.f v = 0
    · grind
    rw [abs_of_nonneg (div_nonneg (by positivity) (hc.trans_le (hcω v hv hf)).le)]
    exact div_le_div_of_nonneg_left (by positivity) hc (hcω v hv hf)
  have := hD.f_cond.cont.mono (Set.Icc_subset_Ici_self (a := D.xf))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := D.xf)).exists_bound_of_continuousOn
    (f := fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / c) (by fun_prop)
  have hcont u (hu : u ∈ Set.Ioo 0 D.xf) (huP : u ∉ (Finset.range (D.m + 1)).image D.t) :
      ContinuousAt (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / D.omega v) u := by
    have hf : ContinuousAt D.f u := hD.f_cond.cont.continuousAt (Ici_mem_nhds hu.1)
    have hnum : ContinuousAt (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2) u := by fun_prop
    by_cases hωu : D.omega u = 0
    · have hfu : D.f u = 0 := by_contra fun hne => by linarith [hcω u hu.1.le hne]
      show Tendsto ..
      simp [hfu]
      refine squeeze_zero_norm' ?_ (by simpa [hfu] using (hnum.div_const c).tendsto)
      filter_upwards [Ioi_mem_nhds hu.1] with v hv
      exact hφ v hv.le
    have hg : ContinuousAt D.g u := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu.1)
    have hH : ContinuousAt D.sieveH u := tendsto_finsetSum _ fun k hk => by
      simp at hk huP
      exact (continuousOn_const.if (s := {D.t k, D.t (k + 1)}ᶜ)
        (fun x hx => (hx.1 ((frontier_Ico (hD.t_lt k hk)).subset hx.2)).elim)
        continuousOn_const).continuousAt ((Set.toFinite _).isClosed.isOpen_compl.mem_nhds
        (by grind))
    exact hnum.div (by unfold NearData.omega; fun_prop) hωu
  obtain ⟨q₀, hq₀⟩ := riemann_upper (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / D.omega v) D.xf M
    ((Finset.range (D.m + 1)).image D.t) hD.f_cond.pos
    (fun u hu => (hφ u hu.1).trans ((le_abs_self _).trans (hM u hu))) hcont hε
  refine ⟨q₀, fun q hq => (hq₀ q hq).trans_eq ?_⟩
  rw [intervalIntegral.integral_of_le hD.f_cond.pos.le, NearData.IB,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
      fun v hv => ?_]
  simp at hv
  simp [hD.f_cond.vanish v hv.2.le]

end GradedNear
