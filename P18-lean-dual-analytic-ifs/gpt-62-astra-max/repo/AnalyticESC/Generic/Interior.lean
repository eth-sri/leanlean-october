module
public import AnalyticESC.Generic.Distance
public import AnalyticESC.Generic.Class
public import AnalyticESC.Dual.Derivatives

@[expose] public section
namespace AnalyticESC.IFS
open Set Metric Filter Topology
variable {N : ℕ} (Φ : IFS N)

noncomputable abbrev vary (d : ℝ → Maps N) (t : ℝ) (i : Fin N) (z : ℂ) := Φ.f i z + t * d t i z

/-- A bounded holomorphic variation of size `O(t)` on a fixed neighbourhood
converges on the interval in all jets. In particular it stays in the class if
it preserves the interval, and converges in the `C²` pseudometric. -/
lemma perturb {d : ℝ → Maps N} {U : Set ℂ} (ho : IsOpen U) (hU : ∀ x ∈ I, (x:ℂ) ∈ U) (hs : U ⊆ Φ.tube)
    (an : ∀ t i, AnalyticOnNhd ℂ (d t i) U) (re : ∀ t i (x : ℝ), (x:ℂ) ∈ U → (d t i x).im = 0)
    (bd : ∀ i, ∃ M, ∀ t > 0, ∀ z ∈ U, ‖d t i z‖ ≤ M) {r} (hr : 0 < r) : ∀ᶠ t in 𝓝[>] (0:ℝ),
    (∀ i, MapsTo (restr (Φ.vary d t i)) I I) → ∃ Ψ : IFS N, dist Φ Ψ < r ∧ Ψ.f = Φ.vary d t := by
  have ha t i : AnalyticOnNhd ℂ (Φ.vary d t i) U := ((Φ.analytic_f i).mono (hs.trans subset_closure)).add (analyticOnNhd_const.mul (an t i))
  have lim i : TendstoUniformlyOn (fun t => Φ.vary d t i) (Φ.f i) (𝓝[>] 0) U := by
    obtain ⟨M,H⟩ := bd i
    rw [Metric.tendstoUniformlyOn_iff]; intro δ hδ
    filter_upwards [self_mem_nhdsWithin,((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const M).eventually_lt_const (by simpa using hδ)] with t ht hh z hz
    change 0 < t at ht
    simpa [dist_eq_norm,vary,norm_mul,abs_of_pos ht] using (mul_le_mul_of_nonneg_left (H _ ht _ hz) ht.le).trans_lt hh
  obtain ⟨u,hu,hh⟩ := exists_between (lt_min (by positivity : 0 < r/3) (lt_min Φ.cmin_pos (half_pos (sub_pos.mpr Φ.cmax_lt_one))))
  obtain ⟨ur,ul,uh⟩ := (lt_min_iff.mp hh).imp_right lt_min_iff.mp
  have jets i (n : Fin 3) := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_image_I).mp
    ((jet_convergence ho (fun t => ha t i) (lim i).tendstoLocallyUniformlyOn n).mono (image_subset_iff.mpr hU))
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun n => Metric.tendstoUniformlyOn_iff.mp (jets i n) u hu] with t h hI
  have err i (n : Fin 3) (x : I) : ‖deriv^[n.val] (Φ.f i) x - deriv^[n.val] (Φ.vary d t i) x‖ ≤ u :=
    by simpa [dist_eq_norm] using (h i n _ (mem_image_of_mem _ x.2)).le
  have reg i x (hx : x ∈ I) : ‖deriv (Φ.vary d t i) x‖ ∈ Ioo 0 ((1+Φ.cmax)/2) := by
    have e := abs_le.mp ((abs_norm_sub_norm_le (deriv (Φ.f i) x) (deriv (Φ.vary d t i) x)).trans (err i 1 ⟨x,hx⟩))
    grind [Φ.cmin_le_norm_deriv i (Φ.closedReal hx),Φ.norm_deriv_le_cmax i (Φ.closedReal hx)]
  obtain ⟨ε,he,cl,-⟩ := common_class ⟨by linarith [Φ.cmax_nonneg],by linarith [Φ.cmax_lt_one]⟩ ho hU
    (fun i => (ha t i).differentiableOn) (fun i x hx => by simp [vary,re t i x hx,show (Φ.f i x).im = 0 from Φ.im_comp_ofReal [i] (hs hx)]) (fun i _ hx => hI i hx) reg
  exact ⟨⟨_,he,cl⟩,(Φ.d2_upper ⟨_,he,cl⟩ hu.le err).trans_lt (by linarith),rfl⟩

/-- Interpolate each image with a freely chosen point of the interval. -/
lemma blend {r : ℝ} (hr : 0 < r) (b : Fin N → I) : ∃ t ∈ Ioo (0:ℝ) 1, ∃ Ψ : IFS N,
    dist Φ Ψ < r ∧ ∀ i (x : ℝ), (Ψ.f i x).re = t*b i + (1-t)*(Φ.f i x).re := by
  let d (_ : ℝ) i (z : ℂ) := b i - Φ.f i z
  have an t i : AnalyticOnNhd ℂ (d t i) Φ.tube := analyticOnNhd_const.sub ((Φ.analytic_f i).mono subset_closure)
  have H := Φ.perturb (isOpen_nbhd _) (fun _ => Φ.real_mem) Subset.rfl an
    (fun _ i x hx => by simp [d,show (Φ.f i x).im = 0 from Φ.im_comp_ofReal [i] hx]) (fun i => ⟨_,fun _ _ z hz =>
      (norm_sub_le _ _).trans (add_le_add_right ((Φ.onBox (Φ.analytic_f i).continuousOn).norm_coe_le_norm ⟨z,subset_closure hz⟩) _)⟩) hr
  obtain ⟨t,H,ht⟩ := (H.and (Ioo_mem_nhdsGT zero_lt_one)).exists
  have e i (x : ℝ) : (Φ.vary d t i x).re = t*b i + (1-t)*(Φ.f i x).re := by simp [vary,d]; ring
  obtain ⟨Ψ,h,hΨ⟩ := H fun i x hx => by rw [restr,e]; exact (convex_Icc 0 1) (b i).2 ((Φ.inClass i).re_mem_I x hx) ht.1.le (sub_nonneg.mpr ht.2.le) (by ring)
  exact ⟨t,ht,Ψ,h,by rwa [hΨ]⟩

def Buffered (a : ℝ) := ∀ i (x : I), (Φ.f i x).re ∈ Icc a (1-a)

lemma interior_near {r : ℝ} (hr : 0 < r) : ∃ Ψ : IFS N, dist Φ Ψ < r ∧ ∃ a > 0, Ψ.Buffered a := by
  obtain ⟨t,ht,Ψ,hd,e⟩ := Φ.blend hr fun _ => ⟨1/2,by norm_num⟩
  refine ⟨Ψ,hd,t/2,half_pos ht.1,fun i x => ?_⟩
  rw [e]; have ⟨hl,hu⟩ := (Φ.inClass i).re_mem_I x x.2
  have ht' := (sub_pos.mpr ht.2).le
  grind [mul_nonneg ht' hl, mul_le_mul_of_nonneg_left hu ht']

end AnalyticESC.IFS
