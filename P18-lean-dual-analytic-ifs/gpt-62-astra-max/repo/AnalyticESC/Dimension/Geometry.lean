module
public import AnalyticESC.Attractor

@[expose] public section
namespace AnalyticESC
open Set Filter Topology MeasureTheory

export Challenge (divide Scale scaleZero logRatio realComp RapaportHyp RapaportMeasureStatement RapaportSetStatement
  IsGibbsMeasure BowenGibbsStatement entropy IsProbVec)

abbrev RatioLimit (mass : ℝ → ℝ) (d : ℝ) := Tendsto (fun r : Scale => logRatio (mass r) r) scaleZero (𝓝 d)
abbrev LocalDim (μ : Measure ℝ) (x : ℝ) := RatioLimit (fun r => μ.real (Metric.closedBall x r))

lemma scale_map : map (fun r : Scale => (r : ℝ)) scaleZero = 𝓝[>] (0 : ℝ) := by
  apply map_comap_of_mem
  filter_upwards [Ioo_mem_nhdsGT (show 0 < 1 from zero_lt_one)] with r hr using ⟨⟨r,hr⟩,rfl⟩

/-- Multiplicative comparisons become bounded additive errors on taking logs. -/
lemma log_bounds {a b v u : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (h : u ∈ Icc (a*v) (b*v)) :
    Real.log u - Real.log v ∈ Icc (Real.log a) (Real.log b) := by
  have hv' := mul_pos ha hv
  have l := Real.log_le_log hv' h.1
  have r := Real.log_le_log (hv'.trans_le h.1) h.2
  rw [Real.log_mul ha.ne' hv.ne'] at l; rw [Real.log_mul hb.ne' hv.ne'] at r; grind

lemma log_gap {a b v u : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (h : u ∈ Icc (a*v) (b*v)) :
    |Real.log u - Real.log v| ≤ |Real.log a| + |Real.log b| := by
  have := log_bounds ha hb hv h; grind

lemma ratio_of_bounded {α : Type*} {p : Filter α} {f g : α → ℝ} {c K : ℝ}
    (hg : Tendsto (fun x => |g x|) p atTop) (h : ∀ᶠ x in p, |f x - c*g x| ≤ K) :
    Tendsto (fun x => f x / g x) p (𝓝 c) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (by simp) ?_ ((tendsto_const_nhds (x := K)).div_atTop hg)
  filter_upwards [h,hg.eventually_gt_atTop 0] with x hx hpos
  rw [Real.norm_eq_abs,div_sub' (abs_pos.mp hpos),mul_comm (g x) c,abs_div]
  bound

abbrev cyl {N n} (v : Block N n) := pref n ⁻¹' {v}

lemma cyl_pref {N} (n : ℕ) (ω : Address N) : cyl (pref n ω) = {y | ∀ j < n, y j = ω j} := by
  ext y; simp [cyl,pref,funext_iff,Fin.forall_iff]

lemma sum_cyl {N n} (ν : Measure (Address N)) [IsFiniteMeasure ν] (S : Finset (Block N n)) :
    ∑ v ∈ S, ν.real (cyl v) = ν.real (pref n ⁻¹' ↑S) :=
  sum_measureReal_preimage_singleton S fun _ _ => (measurableSet_singleton _).preimage (by fun_prop)

lemma sum_bounds {α : Type*} {S : Finset α} {f l u : α → ℝ} (h : ∀ v ∈ S, f v ∈ Icc (l v) (u v)) :
    ∑ v ∈ S, f v ∈ Icc (∑ v ∈ S, l v) (∑ v ∈ S, u v) :=
  ⟨Finset.sum_le_sum fun v hv => (h v hv).1, Finset.sum_le_sum fun v hv => (h v hv).2⟩

namespace IFS
variable {N : ℕ} (Φ : IFS N)

noncomputable abbrev lyapunov := Challenge.lyapunov Φ.f
abbrev IsSelfConformal := Challenge.IsSelfConformal Φ.f
noncomputable abbrev potential := Challenge.potential Φ.f

noncomputable abbrev natural (ν : Measure (Address N)) := ν.map Φ.natProj
noncomputable abbrev weight (w : Letters N) (x : ℝ) := ‖deriv (Φ.comp w) x‖
noncomputable abbrev supDeriv (w : Letters N) := ⨆ x : I, ‖deriv (Φ.comp w) x‖
noncomputable abbrev pressureSum (t : ℝ) (n : ℕ) := ∑ w : Block N n, Φ.supDeriv (List.ofFn w) ^ t

noncomputable abbrev rate (t : ℝ) (n : ℕ) := Real.log (Φ.pressureSum t n) / n
abbrev UniqueRoot (s : ℝ) := ∀ t, Tendsto (Challenge.pressureRatio Φ.f t) atTop (𝓝 0) ↔ t = s

lemma ratio_limit (t : ℝ) : Tendsto (Challenge.pressureRatio Φ.f t) atTop (𝓝 0) ↔ Tendsto (Φ.rate t) atTop (𝓝 0) :=
  tendsto_add_atTop_iff_nat (f := Φ.rate t) 1

lemma weight_pos (w) {x} (hx : x ∈ I) : 0 < Φ.weight w x := norm_pos_iff.mpr
  (Φ.deriv_comp_ne_zero _ (Φ.closedReal hx))

lemma weight_eq (w) {x} (hx : x ∈ I) : Φ.weight w x = |deriv (Φ.R w) x| := by simp [weight,← Φ.R_deriv w hx]

lemma weight_append (u v) {x} (hx : x ∈ I) : Φ.weight (u++v) x = Φ.weight u (Φ.R v x) * Φ.weight v x := by
  rw [weight,Φ.deriv_comp_append u v (Φ.closedReal hx),norm_mul,Φ.comp_ofReal v hx]

lemma weight_cont (w) : ContinuousOn (Φ.weight w) I :=
  ((Φ.analytic_comp w).deriv.continuousOn.comp Complex.continuous_ofReal.continuousOn fun _ => Φ.closedReal).norm

lemma norm_deriv_le_supDeriv (w) {x} (hx : x ∈ I) : Φ.weight w x ≤ Φ.supDeriv w := le_sup isCompact_Icc (Φ.weight_cont w) hx

lemma supDeriv_attained (w) : ∃ x ∈ I, Φ.weight w x = Φ.supDeriv w := by
  obtain ⟨x,hx,e⟩ := isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.mpr zero_le_one) (Φ.weight_cont w)
  rw [image_eq_range] at e; exact ⟨x,hx,e.symm⟩

lemma supDeriv_le (w) : Φ.supDeriv w ≤ Φ.cmax ^ w.length := ciSup_le fun x => (Φ.bounds w (Φ.closedReal x.2)).2
lemma cmin_pow_le_supDeriv (w) : Φ.cmin ^ w.length ≤ Φ.supDeriv w :=
  (Φ.bounds w (Φ.closedReal zero_I)).1.trans
    (Φ.norm_deriv_le_supDeriv w zero_I)

/-- The logarithmic derivative of any composition has Lipschitz constant bounded
uniformly: its derivative is exactly a finite dual projection. -/
lemma distortion [NeZero N] (w) {x y} (hx : x ∈ I) (hy : y ∈ I) :
    |Real.log (Φ.weight w x) - Real.log (Φ.weight w y)| ≤ Φ.amp*|x-y| := by
  have reg := Φ.regular_R w
  have hd z (hz : z ∈ I) := ((reg.1 z hz).deriv.differentiableAt.hasDerivAt.log (reg.2 z hz)).hasDerivWithinAt (s := I)
  rw [Φ.weight_eq w hx,Φ.weight_eq w hy, Real.log_abs, Real.log_abs]
  refine (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd (fun z hz => ?_) hy hx
  have H := Φ.proj_le w.reverse.length (pad 0 w.reverse) (Φ.closedReal hz)
  rwa [Φ.partial_log _ _ (Φ.closedReal hz),block_pad_length,List.reverse_reverse,← Φ.R_logDer w (Φ.real_mem hz),Complex.norm_real] at H

lemma close_prefix {x y : Address N} {n : ℕ} (h : ∀ j < n, x j = y j) :
    |Φ.natProj x - Φ.natProj y| ≤ Φ.cmax ^ n := by
  have e : pref n x = pref n y := by grind
  rw [Φ.natProj_eq_comp_prefix x n,Φ.natProj_eq_comp_prefix y n,block,block,← e]
  simpa using Φ.abs_re_comp_sub_le (.ofFn (pref n x)) (Φ.pi_mem _) (Φ.pi_mem _)

/-- Uniform cylinder mass estimates, valid with the derivative evaluated anywhere on `I`. -/
def Gibbs (s : ℝ) (ν : Measure (Address N)) : Prop :=
  ∃ A > 0, ∃ B > 0, ∀ {n} (v : Block N n) x, x ∈ I →
    ν.real (cyl v) ∈ Icc (A * Φ.weight (.ofFn v) x ^ s) (B * Φ.weight (.ofFn v) x ^ s)

end IFS
end AnalyticESC
