module

public import AnalyticESC.Dual

@[expose] public section

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

noncomputable def hatH (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z

private def singleIFS {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) : IFS 1 ε :=
  ⟨fun _ => f, hε, fun _ => hf⟩

private theorem hatH_eq_dualProj {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) :
    hatH f = (singleIFS hε hf).dualProj (.inf fun _ => 0) := by
  have hc : ∀ n, (singleIFS hε hf).comp (List.replicate n 0) = f^[n] := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, IFS.comp_cons, ih, Function.iterate_succ']; rfl
  funext z; simp only [hatH, IFS.dualProj]
  refine tsum_congr fun k => ?_
  rw [(singleIFS hε hf).dualTerm_of_get?_eq_some (Word.get?_inf _ k)]
  simp only [Word.take_inf, List.ofFn_const, List.reverse_replicate, hc, IFS.nonlin]; rfl

private theorem hatH_eq_add {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) {z : ℂ}
    (hz : z ∈ nbhd ε) :
    hatH f z = deriv (deriv f) z / deriv f z + deriv f z * hatH f (f z) := by
  have hw : (Word.inf fun _ : ℕ => (0 : Fin 1)).prepend [0] = .inf fun _ => 0 := by
    simp only [Word.prepend]; congr 1; funext _; exact Subsingleton.elim _ _
  have h := (singleIFS hε hf).dualProj_prepend [0] (.inf fun _ => 0) (subset_closure hz)
  rw [hw, IFS.dualProj_singleton] at h
  rw [hatH_eq_dualProj hε hf, h]; rfl

private lemma inClass_real_jet {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) {x : ℝ}
    (hx : x ∈ I) :
    f x = ((f x).re : ℂ) ∧ deriv f x = ((deriv f x).re : ℂ) ∧
      deriv (deriv f) x = ((deriv (deriv f) x).re : ℂ) ∧
      HasDerivAt (fun t : ℝ => (f t).re) (deriv f x).re x ∧
      HasDerivAt (fun t : ℝ => (deriv f t).re) (deriv (deriv f) x).re x ∧
      (deriv f x).re ≠ 0 ∧ |(deriv f x).re| < 1 := by
  have hU := isOpen_nbhd (2 * ε)
  have hx2 := ofReal_mem_nbhd (by linarith : 0 < 2 * ε) hx
  have hcl := subset_closure (ofReal_mem_nbhd hε hx)
  have hi1 : ∀ {y : ℝ}, (y : ℂ) ∈ nbhd (2 * ε) → (deriv f y).im = 0 :=
    fun hy => im_deriv_eq_zero hU hf.differentiableOn hf.im_eq_zero hy
  have hd1 : deriv f x = ((deriv f x).re : ℂ) := Complex.ext rfl (by simp [hi1 hx2])
  exact ⟨Complex.ext rfl (by simp [hf.im_eq_zero x hx2]), hd1,
    Complex.ext rfl (by simp [im_deriv_eq_zero hU (hf.differentiableOn.deriv hU) (fun _ => hi1) hx2]),
    hasDerivAt_re_ofReal (hf.differentiableOn.differentiableAt (hU.mem_nhds hx2)),
    hasDerivAt_re_ofReal ((hf.differentiableOn.deriv hU).differentiableAt (hU.mem_nhds hx2)),
    fun h => hf.deriv_ne_zero _ hcl (by rw [hd1, h, Complex.ofReal_zero]),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

theorem existsUnique_fixedPoint {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) :
    ∃! p : ℝ, p ∈ I ∧ f p = p := by
  set F : ℝ → ℝ := fun x => (f x).re - x
  have hderiv : ∀ x ∈ I, HasDerivAt F ((deriv f x).re - 1) x := fun x hx =>
    (inClass_real_jet hε hf hx).2.2.2.1.sub (hasDerivAt_id x)
  have hcont : ContinuousOn F I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hfix : ∀ x ∈ I, f x = x ↔ F x = 0 := fun x hx => by
    rw [(inClass_real_jet hε hf hx).1, Complex.ofReal_inj, sub_eq_zero]
  have hanti : StrictAntiOn F I := strictAntiOn_of_deriv_neg (convex_Icc 0 1) hcont fun x hx => by
    have hxI := interior_subset hx
    rw [(hderiv x hxI).deriv, sub_neg]
    exact (le_abs_self _).trans_lt (inClass_real_jet hε hf hxI).2.2.2.2.2.2
  obtain ⟨p, hp, hFp⟩ : (0 : ℝ) ∈ F '' I := intermediate_value_Icc' zero_le_one hcont
    ⟨by linarith [(hf.re_mem_I 1 ⟨zero_le_one, le_rfl⟩).2],
     by linarith [(hf.re_mem_I 0 ⟨le_rfl, zero_le_one⟩).1]⟩
  exact ⟨p, ⟨hp, (hfix p hp).2 hFp⟩, fun q ⟨hq, hfq⟩ => hanti.injOn hq hp ((hfix q hq).1 hfq ▸ hFp.symm)⟩

private lemma exists_holo_ext {x₀ r : ℝ} (hr : 0 < r) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball (x₀ : ℂ) r))
    (him : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), (h x).im = 0)
    {F : ℝ → ℝ} (hF : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), HasDerivAt F (h x).re x) :
    AnalyticAt ℝ F x₀ ∧ ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (ball (x₀ : ℂ) r) ∧
      ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Ψ x = F x := by
  obtain ⟨Ψ, hΨ0, hΨ⟩ := hh.isExactOn_ball.with_val_at x₀ (F x₀)
  have hΨd : DifferentiableOn ℂ Ψ (ball (x₀ : ℂ) r) := fun z hz => (hΨ z hz).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), HasDerivAt (fun t : ℝ => Ψ t - F t) 0 x := fun x hx => by
    have hm : (x : ℂ) ∈ ball (x₀ : ℂ) r := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have he : h x - ((h x).re : ℂ) = 0 := Complex.ext (by simp) (by simp [him x hx])
    simpa [he] using (hΨ x hm).comp_ofReal.fun_sub (hF x hx).ofReal_comp
  have hx0 : x₀ ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
  have heq : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Ψ x = F x := fun x hx =>
    sub_eq_zero.1 <| (isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun t ht => (hzero t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hzero t ht).deriv) hx hx0).trans (by simp [hΨ0])
  refine ⟨((Complex.reCLM.analyticAt _).comp
    ((hΨd.analyticAt (ball_mem_nhds _ hr)).restrictScalars.comp (Complex.ofRealCLM.analyticAt x₀))).congr ?_,
    Ψ, hΨd, heq⟩
  filter_upwards [Ioo_mem_nhds (by linarith : x₀ - r < x₀) (by linarith : x₀ < x₀ + r)] with x hx
  simp [heq x hx]

private lemma eq_of_hasDerivWithinAt_zero_I {v : ℝ → ℝ}
    (hv : ∀ x ∈ I, HasDerivWithinAt v 0 I x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    v x = v y := by
  have h := constant_of_derivWithin_zero (fun z hz => (hv z hz).differentiableWithinAt) fun z hz =>
    (hv z (Ico_subset_Icc_self hz)).derivWithin (uniqueDiffOn_Icc zero_lt_one z (Ico_subset_Icc_self hz))
  rw [h x hx, h y hy]

lemma exists_koenigs_ode {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) :
    ∃ g : ℝ → ℝ, IsAnalyticCoord g ∧ (∀ x ∈ I, 0 < deriv g x) ∧
      (∀ x ∈ I, deriv (deriv g) x = (hatH f x).re * deriv g x) := by
  have hab : -ε / 2 ≤ 1 + ε / 2 := by linarith
  have hH_diff : DifferentiableOn ℂ (hatH f) (nbhd ε) := by
    rw [hatH_eq_dualProj hε hf]; exact (singleIFS hε hf).differentiableOn_dualProj _
  have hH_im : ∀ {t : ℝ}, (t : ℂ) ∈ nbhd ε → (hatH f t).im = 0 := fun ht => by
    rw [hatH_eq_dualProj hε hf]; exact (singleIFS hε hf).im_dualProj_ofReal _ ht
  have hmem_ab : ∀ t ∈ Icc (-ε / 2) (1 + ε / 2), (t : ℂ) ∈ nbhd ε := fun t ht => by
    refine ball_subset_nbhd (x := max 0 (min 1 t)) ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ ?_
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    cases le_total t 1 <;> cases le_total 0 (min 1 t) <;> simp_all <;> constructor <;> linarith [ht.1, ht.2]
  let u (x : ℝ) : ℝ := (hatH f (projIcc (-ε / 2) (1 + ε / 2) hab x : ℝ)).re
  have huc : Continuous u := Complex.continuous_re.comp <|
    hH_diff.continuousOn.comp_continuous
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc))
      fun x => hmem_ab _ (projIcc _ _ hab x).2
  let U (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, u t
  have hUd : ∀ x, HasDerivAt U (u x) x := fun x => (huc.integral_hasStrictDerivAt 0 x).hasDerivAt
  let G (x : ℝ) : ℝ := Real.exp (U x)
  have hGd : ∀ x, HasDerivAt G (u x * G x) x := fun x => by simpa [G, mul_comm] using (hUd x).exp
  let g (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, G t
  have hgd : ∀ x, HasDerivAt g (G x) x := fun x =>
    ((continuous_iff_continuousAt.2 fun y => (hGd y).continuousAt).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hu_eq : ∀ x₀ ∈ I, ∀ x ∈ Ioo (x₀ - ε / 2) (x₀ + ε / 2), u x = (hatH f x).re := fun x₀ hx₀ x hx => by
    have hm : x ∈ Icc (-ε / 2) (1 + ε / 2) := ⟨by linarith [hx₀.1, hx.1], by linarith [hx₀.2, hx.2]⟩
    simp [u, projIcc_of_mem hab hm]
  have han : AnalyticOnNhd ℝ g I := fun x₀ hx₀ => by
    obtain ⟨_, Ψ₁, hΨ₁d, hΨ₁⟩ := exists_holo_ext (half_pos hε)
      (hH_diff.mono ((ball_subset_ball (half_lt_self hε).le).trans (ball_subset_nbhd hx₀)))
      (fun x hx => hH_im (hmem_ab x ⟨by linarith [hx₀.1, hx.1], by linarith [hx₀.2, hx.2]⟩))
      (fun x hx => hu_eq x₀ hx₀ x hx ▸ hUd x)
    exact (exists_holo_ext (half_pos hε) hΨ₁d.cexp
      (fun x hx => by rw [hΨ₁ x hx, ← Complex.ofReal_exp, Complex.ofReal_im])
      (fun x hx => by rw [hΨ₁ x hx, ← Complex.ofReal_exp, Complex.ofReal_re]; exact hgd x)).1
  have hderiv_g : deriv g = G := funext fun x => (hgd x).deriv
  have hpos : ∀ x ∈ I, 0 < deriv g x := fun x _ => by rw [hderiv_g]; exact Real.exp_pos _
  exact ⟨g, ⟨han, (strictMonoOn_of_deriv_pos (convex_Icc 0 1) han.continuousOn
    fun x hx => hpos x (interior_subset hx)).injOn⟩, hpos,
    fun x hx => by rw [hderiv_g, (hGd x).deriv, hu_eq x hx x ⟨by linarith, by linarith⟩]⟩

lemma conj_of_koenigs_ode {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f)
    {g : ℝ → ℝ} (hga : AnalyticOnNhd ℝ g I) (hgpos : ∀ x ∈ I, 0 < deriv g x)
    (hode : ∀ x ∈ I, deriv (deriv g) x = (hatH f x).re * deriv g x) :
    ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f x).re = lam * g x + t := by
  obtain ⟨p, ⟨hp, hfp⟩, -⟩ := existsUnique_fixedPoint hε hf
  set F : ℝ → ℝ := fun x => (f x).re
  set F₁ : ℝ → ℝ := fun x => (deriv f x).re
  have hGd : ∀ y ∈ I, HasDerivAt (deriv g) ((hatH f y).re * deriv g y) y := fun y hy =>
    hode y hy ▸ (hga y hy).deriv.differentiableAt.hasDerivAt
  have hq : ∀ x ∈ I, HasDerivWithinAt (fun x => deriv g (F x) * F₁ x / deriv g x) 0 I x := fun x hx => by
    obtain ⟨hfr, hf1r, hf2r, hFd, hF₁d, hF₁ne, -⟩ := inClass_real_jet hε hf hx
    have hadd := congrArg Complex.re (hatH_eq_add hε hf (ofReal_mem_nbhd hε hx))
    rw [hf2r, hf1r, hfr, ← Complex.ofReal_div, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul] at hadd
    have hLd : HasDerivAt (fun x => deriv g (F x) * F₁ x) ((hatH f x).re * (deriv g (F x) * F₁ x)) x :=
      (((hGd (F x) (hf.re_mem_I x hx)).comp x hFd).fun_mul hF₁d).congr_deriv
        (by dsimp [Function.comp]; rw [hadd]; field_simp [F₁]; ring)
    convert (hLd.div (hGd x hx) (hgpos x hx).ne').hasDerivWithinAt using 1; ring
  have hFp : F p = p := by dsimp [F]; rw [hfp, Complex.ofReal_re]
  have hLeq : ∀ x ∈ I, deriv g (F x) * F₁ x = F₁ p * deriv g x := fun x hx => by
    have hc := eq_of_hasDerivWithinAt_zero_I hq hx hp
    have := (hgpos x hx).ne'; have := (hgpos p hp).ne'
    rw [hFp] at hc; field_simp at hc; linarith
  have hv : ∀ x ∈ I, HasDerivWithinAt (fun t => g (F t) - F₁ p * g t) 0 I x := fun x hx => by
    have h := ((((hga (F x) (hf.re_mem_I x hx)).differentiableAt.hasDerivAt).comp x
      (inClass_real_jet hε hf hx).2.2.2.1).fun_sub
      (((hga x hx).differentiableAt.hasDerivAt).const_mul (F₁ p))).hasDerivWithinAt (s := I)
    rwa [hLeq x hx, sub_self] at h
  obtain ⟨_, _, _, _, _, h0, h1⟩ := inClass_real_jet hε hf hp
  refine ⟨F₁ p, (1 - F₁ p) * g p, h0, h1, fun x hx => ?_⟩
  have hc := eq_of_hasDerivWithinAt_zero_I hv hx hp
  rw [hFp] at hc; dsimp [F] at hc; linarith

private theorem comp_comm_of_conj {F G g : ℝ → ℝ} (hinj : InjOn g I) (hF : MapsTo F I I)
    (hG : MapsTo G I I) {a b s t : ℝ} (hgF : ∀ x ∈ I, g (F x) = a * g x + s)
    (hgG : ∀ x ∈ I, g (G x) = b * g x + t) {p : ℝ} (hp : p ∈ I) (hFp : F p = p) (hGp : G p = p) :
    ∀ x ∈ I, F (G x) = G (F x) := fun x hx => by
  have hs : g p = a * g p + s := by simpa only [hFp] using hgF p hp
  have ht : g p = b * g p + t := by simpa only [hGp] using hgG p hp
  refine hinj (hF (hG hx)) (hG (hF hx)) ?_
  rw [hgF _ (hG hx), hgG _ (hF hx), hgG x hx, hgF x hx]
  linear_combination (1 - a) * ht - (1 - b) * hs

private theorem periodic_hasDerivAt_unique {u v : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (huv : ∀ y ∈ I, u y = v y) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr huv (huv x hx))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem inClass_comp {w : List (Fin N)} (hw : w ≠ []) : InClass (ε / 4) (Φ.comp w) := by
  have hsub : nbhd (2 * (ε / 4)) ⊆ nbhd ε := nbhd_mono (by linarith [Φ.ε_pos])
  have hcl : closure (nbhd (ε / 4)) ⊆ closure (nbhd ε) := closure_mono (nbhd_mono (by linarith [Φ.ε_pos]))
  exact inClass_of_deriv (by linarith [Φ.ε_pos])
    ((Φ.differentiableOn_comp w).mono hsub)
    (fun _ hx => Φ.im_comp_ofReal w (hsub hx))
    (fun _ hx => Φ.re_comp_mem_I w hx)
    (fun _ hz => Φ.deriv_comp_ne_zero w (hcl hz))
    (fun _ hz => (Φ.norm_deriv_comp_le w (hcl hz)).trans_lt
      (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'))

theorem hatH_comp_eq_dualProj {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) :
    ∀ x ∈ I, hatH (Φ.comp (List.ofFn w)) x = Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) x := by
  intro x hx
  have hw : List.ofFn w ≠ [] := fun h => hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hf := Φ.inClass_comp hw
  have hε4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  set f := Φ.comp (List.ofFn w)
  set c := Φ.cmax ^ m
  have hc0 : 0 ≤ c := pow_nonneg Φ.cmax_nonneg m
  have hc1 : c < 1 := pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one hm.ne'
  obtain ⟨M₁, -, hM₁, -⟩ := (singleIFS hε4 hf).exists_dualProj_bounds
  obtain ⟨M₂, -, hM₂, -⟩ := Φ.exists_dualProj_bounds
  have hsub : nbhd (ε / 4) ⊆ closure (nbhd ε) := (nbhd_mono (by linarith)).trans subset_closure
  have hper : Word.inf (periodic hm (w ∘ Fin.rev)) =
      (Word.inf (periodic hm (w ∘ Fin.rev))).prepend (List.ofFn (w ∘ Fin.rev)) := by
    show _ = Word.inf fun n => if h : n < (List.ofFn _).length then _ else _
    congr 1; funext n; simp only [List.length_ofFn]
    split_ifs with hn
    · simp [periodic, Nat.mod_eq_of_lt hn]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
      simp [periodic, Nat.add_mod_right]
  have hrev_ofFn : List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse :=
    List.ext_getElem (by simp) fun n _ _ => by
      simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_reverse, List.length_ofFn]
      exact congrArg w (Fin.ext (by simp only [Fin.val_rev]; omega))
  have hiter : ∀ n : ℕ, ∀ z ∈ nbhd (ε / 4),
      ‖hatH f z - Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) z‖ ≤ c ^ n * (M₁ + M₂) := by
    intro n; induction n with
    | zero =>
      intro z hz; rw [hatH_eq_dualProj hε4 hf]
      simpa using (norm_sub_le _ _).trans (add_le_add (hM₁ _ z (subset_closure hz)) (hM₂ _ z (hsub hz)))
    | succ n ih =>
      intro z hz
      have hB := Φ.dualProj_prepend (List.ofFn (w ∘ Fin.rev)) (.inf (periodic hm (w ∘ Fin.rev))) (hsub hz)
      rw [← hper, hrev_ofFn, List.reverse_reverse, Φ.dualProj_fin_reverse _ (hsub hz)] at hB
      rw [hatH_eq_add hε4 hf hz, hB, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ', mul_assoc]
      exact mul_le_mul (by simpa [c] using Φ.norm_deriv_comp_le (List.ofFn w) (hsub hz))
        (ih _ (hf.mapsTo _ (subset_closure hz))) (norm_nonneg _) hc0
  have hlim : Tendsto (fun n : ℕ => c ^ n * (M₁ + M₂)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (M₁ + M₂)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim fun n =>
    hiter n _ (ofReal_mem_nbhd hε4 hx)))

private theorem exact_re_comp_mem_attractor (a : List (Fin N)) {x : ℝ}
    (hx : x ∈ Φ.attractor) : (Φ.comp a x).re ∈ Φ.attractor := by
  obtain ⟨w, rfl⟩ := hx; exact ⟨_, (Φ.re_comp_natProj a w).symm⟩

theorem fixedPoint_of_attractor_singleton {p : ℝ} (hp : Φ.attractor = {p}) (k : Fin N) :
    Φ.f k p = p := by
  have hpA : p ∈ Φ.attractor := hp ▸ mem_singleton p
  have h := Φ.exact_re_comp_mem_attractor [k] hpA
  rw [hp] at h
  exact (inClass_real_jet Φ.ε_pos (Φ.inClass k) (Φ.attractor_subset_I hpA)).1.trans
    (congrArg Complex.ofReal h)

theorem attractor_infinite (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    Φ.attractor.Infinite := by
  intro hfin
  let k : Fin N := ⟨0, hN⟩
  let p := Φ.natProj (fun _ => k)
  have hpA : p ∈ Φ.attractor := ⟨_, rfl⟩
  have hpI := Φ.attractor_subset_I hpA
  have hfp : (Φ.comp [k] p).re = p := by simpa [p] using Φ.re_comp_natProj [k] (fun _ => k)
  obtain ⟨q, hqA, hqp⟩ : ∃ q ∈ Φ.attractor, q ≠ p := by
    by_contra! hall
    exact hnd ⟨p, Set.ext fun x => ⟨fun hx => hall x hx, fun hx => hx.symm ▸ hpA⟩⟩
  have hqI := Φ.attractor_subset_I hqA
  let x (n : ℕ) : ℝ := (Φ.comp (List.replicate n k) q).re
  have hx_ne : ∀ n, x n ≠ p := by
    intro n; induction n with
    | zero => simpa [x] using hqp
    | succ n ih =>
      intro he; apply ih
      refine Φ.injOn_re_comp [k] (Φ.re_comp_mem_I _ hqI) hpI ?_
      dsimp only; rw [← Φ.comp_ofReal (List.replicate n k) hqI,
        ← Function.comp_apply (f := Φ.comp [k]), ← Φ.comp_append,
        show [k] ++ List.replicate n k = List.replicate (n + 1) k from rfl]
      exact he.trans hfp.symm
  have hx_lim : Tendsto x atTop (𝓝 p) := by
    have hp_rep : ∀ n, (Φ.comp (List.replicate n k) p).re = p := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.replicate_succ, comp_cons, Function.comp_apply, Φ.comp_ofReal _ hpI, ih]
        exact hfp
    have h0 : Tendsto (fun n => Φ.cmax ^ n * |q - p|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_const |q - p|
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) h0)
    rw [Real.dist_eq]; nth_rw 1 [← hp_rep n]
    simpa [x] using Φ.abs_re_comp_sub_le_mul (List.replicate n k) hqI hpI
  exact ((hfin.sdiff (t := {p})).isClosed.mem_of_tendsto hx_lim
    (Eventually.of_forall fun n => ⟨Φ.exact_re_comp_mem_attractor _ hqA, mem_singleton_iff.not.2 (hx_ne n)⟩)).2
    (mem_singleton p)

private theorem periodic_re_comp_cons (k : Fin N) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    (Φ.comp (k :: w) x).re = Φ.realMaps k (Φ.comp w x).re := by
  show (Φ.f k (Φ.comp w x)).re = (Φ.f k ((Φ.comp w x).re : ℂ)).re; rw [← Φ.comp_ofReal w hx]

theorem tendsto_re_comp_natProj (i : ℕ → Fin N) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {z : ℕ → ℝ} (hz : ∀ n, z n ∈ I) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin (m n) => i k) (z n)).re) atTop
      (𝓝 (Φ.natProj i)) := by
  refine ((Φ.tendsto_natProj i).comp hm).congr_dist (squeeze_zero (fun _ => dist_nonneg)
    (fun n => ?_) ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hm))
  have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin (m n) => i k) ⟨le_rfl, zero_le_one⟩ (hz n)
  rwa [List.length_ofFn, Complex.ofReal_zero, ← Real.dist_eq] at h

theorem deriv_ne_zero_of_conj_of_nonsingleton (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x})
    {g : ℝ → ℝ} (hg : IsAnalyticCoord g) {lam t : Fin N → ℝ}
    (hconj : ∀ k, ∀ x ∈ I, g (Φ.realMaps k x) = lam k * g x + t k) :
    ∀ x ∈ I, deriv g x ≠ 0 := by
  obtain ⟨hga, hinj⟩ := hg
  intro z hz hgz
  set Z := I ∩ deriv g ⁻¹' {0}
  have hZc : IsClosed Z := ContinuousOn.preimage_isClosed_of_isClosed
    (fun x hx => (hga x hx).deriv.continuousAt.continuousWithinAt) isClosed_Icc isClosed_singleton
  have hinv : ∀ k, MapsTo (Φ.realMaps k) Z Z := by
    rintro k x ⟨hx, hx0⟩
    have hFx := (Φ.inClass k).re_mem_I x hx
    obtain ⟨_, _, _, hFd, _, hF1ne, -⟩ := inClass_real_jet Φ.ε_pos (Φ.inClass k) hx
    have hid := periodic_hasDerivAt_unique hx ((hga _ hFx).differentiableAt.hasDerivAt.comp x hFd)
      (((hga x hx).differentiableAt.hasDerivAt.const_mul (lam k)).add_const (t k)) (hconj k)
    refine ⟨hFx, ?_⟩
    simp only [mem_preimage, mem_singleton_iff] at hx0 ⊢
    rw [hx0, mul_zero] at hid
    exact (mul_eq_zero.1 hid).resolve_right hF1ne
  have hinvw : ∀ w : List (Fin N), MapsTo (fun x : ℝ => (Φ.comp w x).re) Z Z := by
    intro w; induction w with
    | nil => intro x hx; simpa using hx
    | cons k w ih => intro x hx; show (Φ.comp (k :: w) x).re ∈ Z; rw [Φ.periodic_re_comp_cons k w hx.1]; exact hinv k (ih hx)
  have hΛ : Φ.attractor ⊆ Z := by
    rintro _ ⟨i, rfl⟩
    exact hZc.mem_of_tendsto (Φ.tendsto_re_comp_natProj i tendsto_id fun _ => hz)
      (Eventually.of_forall fun _ => hinvw _ ⟨hz, hgz⟩)
  obtain ⟨x₀, hx₀, hacc⟩ := ((Φ.attractor_infinite hN hnd).mono hΛ).exists_accPt_of_subset_isCompact
    isCompact_Icc inter_subset_left
  have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun x hx => (hga x hx).deriv) isPreconnected_Icc hx₀
    ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun _ h => h.2)
  exact one_ne_zero (hinj ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
    (eq_of_hasDerivWithinAt_zero_I
      (fun x hx => ((hga x hx).differentiableAt.hasDerivAt.hasDerivWithinAt).congr_deriv (hzero hx))
      ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩))

theorem deriv_deriv_div_deriv_eq_of_fixedPoint {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g I)
    {w : List (Fin N)} (hw : w ≠ []) {a b : ℝ}
    (hconj : ∀ x ∈ I, g (Φ.comp w x).re = a * g x + b) {p : ℝ} (hp : p ∈ I)
    (hfp : Φ.comp w p = p) (hgp : deriv g p ≠ 0) :
    ((deriv (deriv g) p / deriv g p : ℝ) : ℂ) =
      Φ.dualProj (.fin w.reverse) p / (1 - deriv (Φ.comp w) p) := by
  have hε4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  have hf := Φ.inClass_comp hw
  set F : ℝ → ℝ := fun y => (Φ.comp w y).re
  set F₁ : ℝ → ℝ := fun y => (deriv (Φ.comp w) y).re
  set F₂ : ℝ → ℝ := fun y => (deriv (deriv (Φ.comp w)) y).re
  have hgd : ∀ y ∈ I, HasDerivAt g (deriv g y) y := fun y hy => (hg y hy).differentiableAt.hasDerivAt
  have hg₁d : ∀ y ∈ I, HasDerivAt (deriv g) (deriv (deriv g) y) y := fun y hy =>
    (hg y hy).deriv.differentiableAt.hasDerivAt
  have hA : ∀ x ∈ I, deriv g (F x) * F₁ x = a * deriv g x := fun x hx =>
    periodic_hasDerivAt_unique hx ((hgd _ (Φ.re_comp_mem_I w hx)).comp x (inClass_real_jet hε4 hf hx).2.2.2.1)
      (((hgd x hx).const_mul a).add_const b) hconj
  obtain ⟨_, h₁, h₂, hFdp, hF₁dp, hne, hlt⟩ := inClass_real_jet hε4 hf hp
  have hFp : F p = p := by show (Φ.comp w p).re = p; rw [hfp, Complex.ofReal_re]
  have hB : deriv (deriv g) (F p) * F₁ p * F₁ p + deriv g (F p) * F₂ p = a * deriv (deriv g) p :=
    periodic_hasDerivAt_unique hp (((hg₁d _ (Φ.re_comp_mem_I w hp)).comp p hFdp).mul hF₁dp)
      ((hg₁d p hp).const_mul a) hA
  have hF₁p : F₁ p = a := mul_left_cancel₀ hgp (by have h := hA p hp; rw [hFp] at h; linarith)
  rw [Φ.dualProj_fin_reverse w (subset_closure (ofReal_mem_nbhd Φ.ε_pos hp)), h₁, h₂,
    show (F₂ p : ℂ) / (F₁ p : ℂ) / (1 - (F₁ p : ℂ)) = ((F₂ p / F₁ p / (1 - F₁ p) : ℝ) : ℂ) by push_cast; ring]
  congr 1
  rw [hFp, ← hF₁p] at hB
  rw [div_div, div_eq_div_iff hgp (mul_ne_zero hne fun h0 => by linarith [abs_lt.1 hlt])]
  linear_combination -hB

theorem dualProj_eq_of_conjSelfSimilar (hnd : ¬ ∃ x, Φ.attractor = {x})
    (h : ConjSelfSimilar Φ.realMaps) :
    ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  intro i₀ j₀
  have hN : 0 < N := (i₀ 0).pos
  have hε := Φ.ε_pos
  obtain ⟨g, hg, lam, t, hconj⟩ := h
  have hconj' : ∀ k, ∀ x ∈ I, g (Φ.realMaps k x) = lam k * g x + t k := fun k => (hconj k).2.2
  have hg' := Φ.deriv_ne_zero_of_conj_of_nonsingleton hN hnd hg hconj'
  have hccomp : ∀ w : List (Fin N), ∃ a b : ℝ, ∀ x ∈ I, g (Φ.comp w x).re = a * g x + b := by
    intro w; induction w with
    | nil => exact ⟨1, 0, fun x _ => by simp⟩
    | cons k w ih =>
      obtain ⟨a, b, hw⟩ := ih
      exact ⟨lam k * a, lam k * b + t k, fun x hx => by
        rw [Φ.periodic_re_comp_cons k w hx, hconj' k _ (Φ.re_comp_mem_I w hx), hw x hx]; ring⟩
  obtain ⟨M, -, -, hM⟩ := Φ.exists_dualProj_bounds
  have hc : Tendsto (fun n : ℕ => Φ.cmax ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp (tendsto_add_atTop_nat 1)
  have key : ∀ i j : ℕ → Fin N,
      ((deriv (deriv g) (Φ.natProj i) / deriv g (Φ.natProj i) : ℝ) : ℂ) =
        Φ.dualProj (.inf j) (Φ.natProj i) := fun i j => by
    have hπ : Φ.natProj i ∈ I := Φ.attractor_subset_I ⟨i, rfl⟩
    set u : ℕ → List (Fin N) := fun n => List.ofFn fun m : Fin (n + 1) => i m with hu
    set v : ℕ → List (Fin N) := fun n => List.ofFn fun m : Fin (n + 1) => j m with hv
    set k : ℕ → List (Fin N) := fun n => u n ++ (v n).reverse with hk
    have hkne : ∀ n, k n ≠ [] := fun n => by simp [hk, hu]
    choose p hp hfp using fun n => (existsUnique_fixedPoint (by linarith : 0 < ε / 4) (Φ.inClass_comp (hkne n))).exists
    have hpcl : ∀ n, (p n : ℂ) ∈ closure (nbhd ε) := fun n => subset_closure (ofReal_mem_nbhd hε (hp n))
    have hid : ∀ n, ((deriv (deriv g) (p n) / deriv g (p n) : ℝ) : ℂ) =
        Φ.dualProj (.fin (k n).reverse) (p n) / (1 - deriv (Φ.comp (k n)) (p n)) := fun n => by
      obtain ⟨a, b, hab⟩ := hccomp (k n)
      exact Φ.deriv_deriv_div_deriv_eq_of_fixedPoint hg.1 (hkne n) hab (hp n) (hfp n) (hg' _ (hp n))
    have hplim : Tendsto p atTop (𝓝 (Φ.natProj i)) :=
      (Φ.tendsto_re_comp_natProj i (tendsto_add_atTop_nat 1)
        (z := fun n => (Φ.comp (v n).reverse (p n)).re) fun n => Φ.re_comp_mem_I _ (hp n)).congr fun n => by
        show (Φ.comp (u n) ((Φ.comp (v n).reverse (p n)).re : ℂ)).re = p n
        rw [← Φ.comp_ofReal _ (hp n), ← Function.comp_apply (f := Φ.comp (u n)), ← Φ.comp_append]
        show (Φ.comp (k n) (p n)).re = p n; rw [hfp n, Complex.ofReal_re]
    have hL : Tendsto (fun n => ((deriv (deriv g) (p n) / deriv g (p n) : ℝ) : ℂ)) atTop
        (𝓝 ((deriv (deriv g) (Φ.natProj i) / deriv g (Φ.natProj i) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp
        (((hg.1 _ hπ).deriv.deriv.continuousAt.div (hg.1 _ hπ).deriv.continuousAt (hg' _ hπ)).tendsto.comp hplim)
    have hD : Tendsto (fun n => deriv (Φ.comp (k n)) (p n)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (Φ.norm_deriv_comp_le _ (hpcl n)).trans
        (pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le (by simp [hk, hu, hv]))) hc
    have hH₁ : Tendsto (fun n => Φ.dualProj (.fin (k n).reverse) (p n) - Φ.dualProj (.inf j) (p n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => hM _ _ (n + 1) (fun l hl => ?_) _ (hpcl n))
        (by simpa using hc.const_mul (2 * M))
      have hget : (Word.fin (k n).reverse).get? l = some (j l) := by
        simp only [hk, Word.get?_fin, List.reverse_append, List.reverse_reverse]
        rw [List.getElem?_append_left (by simp [hv, hl])]
        show (List.ofFn fun m : Fin (n + 1) => j m)[l]? = some (j l)
        simp only [List.getElem?_ofFn, hl, ↓reduceDIte]
      simp [hget]
    have hH₂ : Tendsto (fun n => Φ.dualProj (.inf j) (p n)) atTop (𝓝 (Φ.dualProj (.inf j) (Φ.natProj i))) :=
      (((Φ.differentiableOn_dualProj _).differentiableAt
        ((isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hπ))).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto _).comp hplim)
    have hR := (hH₁.add hH₂).div ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hD)
      (by rw [sub_zero]; exact one_ne_zero)
    rw [zero_add, sub_zero, div_one] at hR
    exact tendsto_nhds_unique hL ((hR.congr fun n => by simp only [Pi.div_apply, sub_add_cancel]).congr fun n => (hid n).symm)
  intro x hx
  by_contra hne
  refine Φ.attractor_infinite hN hnd ((finite_zeros hε ((Φ.differentiableOn_dualProj (.inf i₀)).sub
    (Φ.differentiableOn_dualProj (.inf j₀))) ⟨x, hx, sub_ne_zero.2 hne⟩).subset ?_)
  rintro _ ⟨i, rfl⟩
  refine ⟨Φ.attractor_subset_I ⟨i, rfl⟩, ?_⟩
  show Φ.dualProj (.inf i₀) (Φ.natProj i) - Φ.dualProj (.inf j₀) (Φ.natProj i) = 0
  rw [← key i i₀, ← key i j₀, sub_self]

private theorem periodic_hatH_f_eq_dualProj_const (k : Fin N) :
    ∀ x ∈ I, hatH (Φ.f k) x = Φ.dualProj (.inf fun _ => k) x := fun x hx => by
  have h := Φ.hatH_comp_eq_dualProj one_pos ![k] x hx
  have hw : periodic one_pos (![k] ∘ Fin.rev) = fun _ => k :=
    funext fun _ => by unfold periodic; exact Matrix.cons_val_fin_one k ![] _
  rwa [hw, show Φ.comp (List.ofFn ![k]) = Φ.f k by simp] at h

private theorem conjSelfSimilar_of_hatH_eq
    (h : ∀ k j : Fin N, ∀ x ∈ I, hatH (Φ.f k) x = hatH (Φ.f j) x) :
    ConjSelfSimilar Φ.realMaps := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun j => j.elim0⟩
  obtain ⟨φ, hco, hpos, hode⟩ := exists_koenigs_ode Φ.ε_pos (Φ.inClass ⟨0, hN⟩)
  choose lam t hc_spec using fun k =>
    conj_of_koenigs_ode Φ.ε_pos (Φ.inClass k) hco.1 hpos fun x hx => by
      rw [h k ⟨0, hN⟩ x hx]; exact hode x hx
  exact ⟨φ, hco, lam, t, hc_spec⟩

theorem conjSelfSimilar_of_dualProj_eq
    (h : ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) :
    ConjSelfSimilar Φ.realMaps :=
  Φ.conjSelfSimilar_of_hatH_eq fun k j x hx => by
    rw [Φ.periodic_hatH_f_eq_dualProj_const k x hx, Φ.periodic_hatH_f_eq_dualProj_const j x hx, h _ _ x hx]

theorem subConjSelfSimilar_iff :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (Φ.comp (List.ofFn i) x).re,
        fun x : ℝ => (Φ.comp (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x := by
  have hne : ∀ {m : ℕ} (w : Fin m → Fin N), 0 < m → List.ofFn w ≠ [] := fun w hm h =>
    hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hrev : ∀ {m : ℕ} (w : Fin m → Fin N), (w ∘ Fin.rev) ∘ Fin.rev = w := fun w => funext fun _ => by simp
  have hrev_ne : ∀ {m : ℕ} {u v : Fin m → Fin N}, u ≠ v → u ∘ Fin.rev ≠ v ∘ Fin.rev :=
    fun {m u v} huv h => huv (by rw [← hrev u, h, hrev])
  have hε4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  constructor
  · rintro ⟨m, i, j, hij, g, ⟨hg, hinj⟩, lam, t, hconj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hij (by subst h; exact Subsingleton.elim _ _)
    have hf₁ := Φ.inClass_comp (hne i hm); have hf₂ := Φ.inClass_comp (hne j hm)
    obtain ⟨p₁, ⟨hp₁, hfp₁⟩, uq₁⟩ := existsUnique_fixedPoint hε4 hf₁
    obtain ⟨p₂, ⟨hp₂, hfp₂⟩, uq₂⟩ := existsUnique_fixedPoint hε4 hf₂
    by_cases hpq : p₁ = p₂
    · subst hpq
      have hcomm := comp_comm_of_conj hinj hf₁.re_mem_I hf₂.re_mem_I (hconj 0).2.2 (hconj 1).2.2 hp₁
        (by rw [hfp₁, Complex.ofReal_re]) (by rw [hfp₂, Complex.ofReal_re])
      have hm' : 0 < m + m := by omega
      set u := List.ofFn (Fin.append i j); set v := List.ofFn (Fin.append j i)
      have hcomp : ∀ (a b : Fin m → Fin N) {y : ℝ}, y ∈ I → Φ.comp (List.ofFn (Fin.append a b)) y =
          ((Φ.comp (List.ofFn a) ((Φ.comp (List.ofFn b) y).re : ℂ)).re : ℂ) := fun a b {y} hy => by
        rw [List.ofFn_fin_append, Φ.comp_append, Function.comp_apply]
        conv_lhs => rw [Φ.comp_ofReal _ hy]
        exact Φ.comp_ofReal _ (Φ.re_comp_mem_I _ hy)
      have hfg : EqOn (Φ.comp u) (Φ.comp v) (nbhd ε) :=
        eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp u) (Φ.differentiableOn_comp v)
          zero_lt_one subset_rfl fun y hy => by rw [hcomp i j hy, hcomp j i hy]; exact congrArg _ (hcomm y hy)
      have hiter : ∀ k : ℕ, EqOn ((Φ.comp u)^[k]) ((Φ.comp v)^[k]) (nbhd ε) := fun k => by
        induction k with
        | zero => exact fun _ _ => rfl
        | succ k ih =>
          intro z hz
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hfg hz]
          exact ih (Φ.mapsTo_comp u hz)
      have hd1 := hfg.deriv (isOpen_nbhd ε); have hd2 := hd1.deriv (isOpen_nbhd ε)
      refine ⟨m + m, hm', Fin.append i j ∘ Fin.rev, Fin.append j i ∘ Fin.rev,
        hrev_ne fun h => hij (funext fun k => by simpa using congrFun h (Fin.castAdd m k)), fun x hx => ?_⟩
      rw [← Φ.hatH_comp_eq_dualProj hm' _ x hx, ← Φ.hatH_comp_eq_dualProj hm' _ x hx]
      have hxε := ofReal_mem_nbhd Φ.ε_pos hx
      refine tsum_congr fun k => ?_
      have h2 := (Φ.mapsTo_comp u).iterate k hxε
      rw [(hiter k).deriv (isOpen_nbhd ε) hxε, ← hiter k hxε, hd1 h2, hd2 h2]
    · let Ψ : IFS 2 (ε / 4) := ⟨![Φ.comp (List.ofFn i), Φ.comp (List.ofFn j)], hε4,
        Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩⟩
      have hnd : ¬ ∃ x, Ψ.attractor = {x} := by
        rintro ⟨x, hx⟩
        have hxI := Ψ.attractor_subset_I (hx ▸ mem_singleton x)
        have hfix := Ψ.fixedPoint_of_attractor_singleton hx
        exact hpq ((uq₁ p₁ ⟨hp₁, hfp₁⟩).trans ((uq₁ x ⟨hxI, by simpa [Ψ] using hfix 0⟩).symm.trans
          (uq₂ x ⟨hxI, by simpa [Ψ] using hfix 1⟩)))
      have hall := Ψ.dualProj_eq_of_conjSelfSimilar hnd ⟨g, ⟨hg, hinj⟩, lam, t,
        Fin.forall_fin_two.2 ⟨by simpa [Ψ, realMaps] using hconj 0, by simpa [Ψ, realMaps] using hconj 1⟩⟩
      refine ⟨m, hm, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, fun x hx => ?_⟩
      rw [← Φ.hatH_comp_eq_dualProj hm _ x hx, ← Φ.hatH_comp_eq_dualProj hm _ x hx]
      have h := hall (fun _ => 0) (fun _ => 1) x hx
      rw [← Ψ.periodic_hatH_f_eq_dualProj_const 0 x hx, ← Ψ.periodic_hatH_f_eq_dualProj_const 1 x hx] at h
      simpa [Ψ] using h
  · rintro ⟨m, hm, i, j, hij, h⟩
    let Ψ : IFS 2 (ε / 4) := ⟨![Φ.comp (List.ofFn (i ∘ Fin.rev)), Φ.comp (List.ofFn (j ∘ Fin.rev))],
      hε4, Fin.forall_fin_two.2 ⟨Φ.inClass_comp (hne _ hm), Φ.inClass_comp (hne _ hm)⟩⟩
    have hc := Ψ.conjSelfSimilar_of_hatH_eq (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2
      ⟨fun _ _ => rfl, fun x hx => by
        dsimp [Ψ]; rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx, hrev, hrev]
        exact h x hx⟩, Fin.forall_fin_two.2 ⟨fun x hx => by
        dsimp [Ψ]; rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx, hrev, hrev]
        exact (h x hx).symm, fun _ _ => rfl⟩⟩)
    obtain ⟨φ, hco, lam, t, hspec⟩ := hc
    exact ⟨m, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, φ, hco, lam, t,
      Fin.forall_fin_two.2 ⟨by simpa [Ψ, realMaps] using hspec 0, by simpa [Ψ, realMaps] using hspec 1⟩⟩

end IFS

end AnalyticESC
