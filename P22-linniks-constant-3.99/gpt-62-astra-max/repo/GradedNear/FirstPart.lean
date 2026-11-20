module

public import GradedNear.FirstFactor
public import GradedNear.Basic

/-!
# The first Cauchy–Schwarz factor for the data of the lemma

`𝓛⁻¹ Σ_{1 ≤ n ≤ q^{x_f}} (Λ(n)/n) e^{2 s t_n} f(t_n)² / ω(t_n) ≤ I_B + ε` for all large `q`.
This applies `riemann_upper` to `φ(u) = e^{2su} f(u)² / ω(u)`. `φ` is bounded on `[0, x_f]`
because `ω ≥ c > 0` wherever `f ≠ 0`. It is continuous on `(0, x_f)` away from `x_g` and the
cell endpoints `t_k`; the denominator can be clipped below by `c` without changing `φ`. Its integral over
`[0, x_f]` is `I_B`, since `f = 0` on `[x_f, ∞)`.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

open NearData

namespace FirstPart

open Filter Topology MeasureTheory

variable (D : NearData)

/-- The cells are half open, so their indicators are continuous away from the
finite set of endpoints. -/
lemma continuousAt_sieveH (hD : D.Valid) {u : ℝ} (hu : ∀ k ≤ D.m, u ≠ D.t k) :
    ContinuousAt D.sieveH u := by
  apply tendsto_finsetSum; intro k hk
  have hk := Finset.mem_range.mp hk
  have h : u ∉ frontier (Set.Ico (D.t k) (D.t (k+1))) := by
    simp [frontier_Ico (hD.t_lt k hk), hu k hk.le, hu (k+1) hk]
  change ContinuousAt _ u
  convert (continuousOn_const (c := D.h k)).continuousAt_indicator h using 1
  ext; simp [Set.indicator_apply]

end FirstPart

theorem first_factor_bound (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop,
      (∑ n ∈ samples q D.horizon, primeMass n * density D (tn q n)) /
        Real.log q ≤ D.IB + ε := by
  obtain ⟨c, hc, hlb⟩ := hD.omega_lb
  let num u := Real.exp (2 * D.s * u) * D.f u^2
  have hnum : ContinuousOn num (Set.Ici 0) := (by fun_prop : Continuous (fun u => Real.exp (2*D.s*u))).continuousOn.mul
    (hD.f_cond.cont.pow 2)
  have clip u (hu : 0 ≤ u) : density D u = num u / max c (D.omega u) := by
    by_cases h : D.f u = 0 <;> simp_all [num]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hnum.mono (Set.Icc_subset_Ici_self : Set.Icc 0 (D.horizon+2) ⊆ Set.Ici 0))
  refine riemann_upper (fun u => density D u) _ (M/c) ((Finset.range (D.m+1)).image D.t) (hD.f_cond.pos.trans_le (le_max_left ..)) ?_ (fun u hu => by simp [hD.f_cond.vanish u ((le_max_left ..).trans hu)]) ?_ hε
  · intro u hu; rw [clip u hu.1, abs_div, abs_of_pos (hc.trans_le (le_max_left ..))]
    exact div_le_div₀ ((norm_nonneg _).trans (hM u hu)) (hM u hu) hc (le_max_left ..)
  · intro u hu hex
    have hg := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu)
    have hn := hnum.continuousAt (Ici_mem_nhds hu)
    have hH := FirstPart.continuousAt_sieveH D hD fun k hk he => hex
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), he.symm⟩)
    have hω : ContinuousAt D.omega u := by unfold NearData.omega; fun_prop
    apply ContinuousAt.congr (f := fun v => num v / max c (D.omega v)) (by fun_prop (disch := positivity))
    filter_upwards [Ici_mem_nhds hu] with v hv using (clip v hv).symm

end GradedNear
