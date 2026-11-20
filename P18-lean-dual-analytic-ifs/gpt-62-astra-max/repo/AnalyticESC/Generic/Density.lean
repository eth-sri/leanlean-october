module
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Generic.Interior
public import AnalyticESC.Conjugation.Characterisation

@[expose] public section
/-! # Separating two first letters

A regular coordinate for each tail turns the head recursion into equality of
logarithmic derivatives. Identical projections would give proportional slopes
on the interval and hence on a slight enlargement. A critical point in just
one head map rules this out. -/
namespace AnalyticESC.IFS
open Set Filter Topology Metric
variable {N : ℕ} (Φ : IFS N)

private lemma critical_good {i j : Fin N} {p : ℝ} (hp : p ≤ 0)
    (ha : ∀ k, AnalyticOnNhd ℝ (Φ.realMap k) (Icc p 1))
    (hm : ∀ k, MapsTo (Φ.realMap k) (Icc p 1) I)
    (hi : deriv (Φ.realMap i) p = 0) (hj : deriv (Φ.realMap j) p ≠ 0) : Φ ∈ Good i j := by
  rintro ⟨⟨v,w⟩,rfl,rfl,h⟩
  have coord (u : Address N) : ∃ g, Regular g ∧ EqOn (D (g ∘ Φ.realMap (u 0))) (Φ.P u) I := by
    obtain ⟨g,hg,e⟩ := Φ.coord_for (shift 1 u)
    refine ⟨g,hg,fun x hx => ?_⟩
    change D (g ∘ Φ.R [u 0]) x = _
    simp only [Φ.rec_comp hg [u 0] hx,Φ.head_rec u hx,e (Φ.re_comp_mem_I [u 0] hx)]
  obtain ⟨g,hg,eg⟩ := coord w
  obtain ⟨f,hf,ef⟩ := coord v
  obtain ⟨l,hl⟩ := proportional (Φ.regular_comp hg [w 0]) (Φ.regular_comp hf [v 0])
    (fun x hx => (eg hx).trans ((h ⟨x,hx⟩).symm.trans (ef hx).symm))
  have hz : p ∈ Icc p 1 := left_mem_Icc.mpr (by linarith)
  have e := agree_Icc (hg.1.comp (ha _) (hm _)).deriv (analyticOnNhd_const.mul (hf.1.comp (ha _) (hm _)).deriv)
    (Icc_infinite zero_lt_one) (Icc_subset_Icc hp le_rfl) hl hz
  dsimp only at e
  rw [deriv_comp p (hg.1 _ (hm _ hz)).differentiableAt (ha _ _ hz).differentiableAt,
    deriv_comp p (hf.1 _ (hm _ hz)).differentiableAt (ha _ _ hz).differentiableAt,hi] at e
  exact mul_ne_zero (hg.2 _ (hm _ hz)) hj (by simpa using e)

/-- Buffering persists a little to the left of zero. -/
private lemma extend_buffer {a} (ha : 0 < a) (hI : Φ.Buffered a) : ∃ p < (0:ℝ),
    ∀ x ∈ Icc p 1, (x:ℂ) ∈ Φ.tube ∧ ∀ i, (Φ.f i x).re ∈ Icc (a/2) (1-a/2) := by
  have inside i : Ioo (a/2) (1-a/2) ∈ 𝓝 (Φ.realMap i 0) := by
    have h : Φ.realMap i 0 ∈ Icc a (1-a) := hI i 0
    grind [h.1, h.2, Ioo_mem_nhds]
  have near := eventually_all.mpr fun i => ((Φ.regular_R [i]).1 0 zero_I).continuousAt.preimage_mem_nhds (inside i)
  obtain ⟨p,hp,H⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp (nhdsWithin_le_nhds (inter_mem (near_real (isOpen_nbhd _) (Φ.real_mem zero_I)) near))
  refine ⟨p,hp,fun x hx => ?_⟩
  rcases le_total x 0 with h|h
  · obtain ⟨h,e⟩ := H ⟨hx.1,h⟩; exact ⟨h,fun i => Ioo_subset_Icc_self (e i)⟩
  · have hxI : x ∈ I := ⟨h,hx.2⟩
    exact ⟨Φ.real_mem hxI,fun i => Icc_subset_Icc (by linarith) (by linarith) (hI i ⟨x,hxI⟩)⟩

private lemma mark {i j : Fin N} (hij : i ≠ j) {a r : ℝ} (ha : 0 < a) (hI : Φ.Buffered a) (hr : 0 < r) :
    ∃ Ψ : IFS N, dist Φ Ψ < r ∧ Ψ ∈ Good i j := by
  obtain ⟨p,hp,J⟩ := Φ.extend_buffer ha hI
  have hI' : I ⊆ Icc p 1 := Icc_subset_Icc hp.le le_rfl
  have hz := (J p (left_mem_Icc.mpr (hp.le.trans zero_le_one))).1
  let C (k : Fin N) := if k=i then deriv (Φ.realMap k) p else 0
  let d (t : ℝ) k (z : ℂ) := C k * Complex.exp ((p-z)/t)
  have an (t : ℝ) k : AnalyticOnNhd ℂ (d t k) Φ.tube := by apply DifferentiableOn.analyticOnNhd _ (isOpen_nbhd _); unfold d; fun_prop
  have bound t (ht : 0 < t) k z (hz : p ≤ z.re) : ‖d t k z‖ ≤ |C k| := by
    simp only [d,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.div_ofReal_re,Complex.sub_re,Complex.ofReal_re]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) ht.le))
  let U := Φ.tube ∩ {z : ℂ | p < z.re}
  have H := Φ.perturb (U := U) ((isOpen_nbhd _).inter (isOpen_lt continuous_const Complex.continuous_re)) (fun x hx => ⟨Φ.real_mem hx,hp.trans_le hx.1⟩) inter_subset_left
    (fun t k => (an t k).mono inter_subset_left) (fun t k x _ => by simp [d,← Complex.ofReal_sub,← Complex.ofReal_div,← Complex.ofReal_exp])
    (fun k => ⟨_,fun t ht z hz => bound t ht k z hz.2.le⟩) hr
  have small k : ∀ᶠ t in 𝓝[>] (0:ℝ), t * |C k| < a/2 := ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const |C k|).eventually_lt_const (by simpa using half_pos ha)
  obtain ⟨t,H,ht,hs⟩ := (H.and ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin).and (eventually_all.mpr small))).exists
  change 0 < t at ht
  have mem k {x : ℝ} (hx : x ∈ Icc p 1) : (Φ.vary d t k x).re ∈ I := by
    have ⟨l,h⟩ := (J x hx).2 k
    have e := (Complex.abs_re_le_norm (d t k x)).trans (bound t ht k x hx.1)
    have E := abs_le.mp (show |t * (d t k x).re| ≤ a/2 by rw [abs_mul,abs_of_pos ht]; exact (mul_le_mul_of_nonneg_left e ht.le).trans (hs k).le)
    simp only [vary,Complex.add_re,Complex.re_ofReal_mul,mem_Icc]; grind
  obtain ⟨Ψ,hd,e⟩ := H fun k x hx => mem k (hI' hx)
  have av k : AnalyticOnNhd ℝ (Ψ.realMap k) (Icc p 1) := fun x hx => by
    change AnalyticAt ℝ (restr (Ψ.f k)) x; rw [e]; exact (((Φ.analytic_f k _ (subset_closure (J x hx).1))).add (analyticAt_const.mul (an t k _ (J x hx).1))).re_ofReal
  have der k : deriv (Ψ.realMap k) p = deriv (Φ.realMap k) p - C k := by
    have E : Ψ.realMap k = fun x => Φ.realMap k x + t * (C k * Real.exp ((p-x)/t)) := by
      funext x; simp [realMap,e,vary,d,← Complex.ofReal_sub,← Complex.ofReal_div,← Complex.ofReal_exp]
    rw [E]
    have df := (Φ.analytic_f k _ (subset_closure hz)).re_ofReal.differentiableAt.hasDerivAt
    exact (df.add (((((hasDerivAt_id p).const_sub p).div_const t).exp.const_mul (C k)).const_mul t)).congr_deriv (by simp; field_simp; ring) |>.deriv
  refine ⟨Ψ,hd,Ψ.critical_good hp.le av (by intro k x hx; simpa [realMap,e] using mem k hx) (by simp [der,C]) ?_⟩
  rw [der]; simp only [C,ite_eq_right hij.symm,sub_zero]
  intro hn
  exact (Φ.inClass j).deriv_ne_zero _ (subset_closure hz) ((Φ.R_jet [j] 1 hz).symm.trans (by change ((deriv (Φ.realMap j) p:ℝ):ℂ) = 0; simp [hn]))

lemma good_dense {i j : Fin N} (h : i ≠ j) : Dense (Good i j) := Metric.dense_iff.mpr fun Φ r hr => by
  obtain ⟨Γ,d,a,ha,hI⟩ := Φ.interior_near (half_pos hr)
  obtain ⟨Ψ,e,hg⟩ := Γ.mark h ha hI (half_pos hr)
  exact ⟨Ψ,mem_ball'.mpr ((dist_triangle _ Γ _).trans_lt (by linarith)),hg⟩

end AnalyticESC.IFS
