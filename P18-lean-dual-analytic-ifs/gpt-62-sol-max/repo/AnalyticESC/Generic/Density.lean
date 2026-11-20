module

public import AnalyticESC.Generic.Class
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Main.Closeness

@[expose] public section

namespace AnalyticESC.IFS
open Set Metric Filter Topology Continuity

variable {N : ℕ} {ε : ℝ}

/-- An entire near-identity perturbation inserts a simple critical point just outside `I`.
Cauchy's estimate controls the jets. -/
theorem exists_dualSSC_near (Φ : IFS N ε) (hN : 0 < N) {m : ℝ} (hm : 0 < m)
    (hI : ∀ i x, x ∈ I → (Φ.f i x).re ∈ Icc m (1 - m)) {r : ℝ} (hr : 0 < r) :
    ∃ ε' : ℝ, ∃ Ψ : IFS N ε', d2 Φ Ψ < r ∧ Ψ.DualSSC := by
  let _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨s, hs, H⟩ := exists_between (half_pos (lt_min Φ.ε_pos hm))
  have ⟨hsε, hsm⟩ := lt_min_iff.1 (show 2*s < min ε m by linarith)
  have hsub := nbhd_mono hsε.le
  have flip (i : Fin N) {z y : ℂ} (hz : z ∈ nbhd ε) (hy : y ∈ nbhd ε) :
      ‖Φ.f i z - Φ.f i y‖ ≤ ‖z - y‖ := by
    have H := Φ.norm_comp_sub_le [i] (subset_closure hz) (subset_closure hy)
    exact (by simp_all : ‖Φ.f i z - Φ.f i y‖ ≤ Φ.cmax * ‖z-y‖).trans
      (mul_le_of_le_one_left (norm_nonneg _) Φ.cmax_lt_one.le)
  have himage (i : Fin N) {z : ℂ} (hz : z ∈ nbhd (2*s)) : (Φ.f i z).re ∈ I := by
    have hze := hsub hz
    obtain ⟨x, hx, H⟩ := hz
    have H' := (Complex.abs_re_le_norm _).trans ((flip i hze (Φ.real_mem_open hx)).trans H.le)
    grind [Complex.sub_re]
  let ρ := s/4
  have hρ : 0 < ρ := by positivity
  let C (j : Fin 3) : ℝ := j.val.factorial / ρ^j.val
  let M := ∑ j, C j
  have hM : 0 ≤ M := by positivity
  let R := min r (min Φ.cmin (1-Φ.cmax))
  have hR : 0 < R := by dsimp [R]; positivity [Φ.cmin_pos hN, Φ.cmax_lt_one]
  let E := Real.exp 1
  obtain ⟨t, ht, Ht⟩ := exists_between (show 0 < min (s/E) (R/(E*M+1)) by positivity)
  have hsE : t * E < s := (lt_div_iff₀ (Real.exp_pos 1)).1 (lt_min_iff.1 Ht).1
  have hMR : t*E*M < R := by linarith [(lt_div_iff₀ (by positivity)).1 (lt_min_iff.1 Ht).2]
  have ht0 : (t : ℂ) ≠ 0 := by aesop
  let _ : Infinite (Ioo (-s) (min 0 (-s + t))) := (Ioo_infinite (by grind)).to_subtype
  let a := (Fin.valEmbedding (n := N)).trans (Infinite.natEmbedding (Ioo (-s) (min 0 (-s + t))))
  let p (i : Fin N) : ℝ := a i
  have hp i : p i ∈ Ioo (-s) (min 0 (-s + t)) := (a i).2
  have hinj : Function.Injective p := fun _ _ h => a.injective (Subtype.ext h)
  let K := Ioc (-s) 1
  let e (i : Fin N) (z : ℂ) := Complex.exp (((p i : ℂ) - z)/(t:ℂ))
  let l (i : Fin N) (z : ℂ) := z + (t : ℂ) * e i z
  let g i := Φ.f i ∘ l i
  have hIK : I ⊆ K := fun x hx => ⟨by grind, hx.2⟩
  have hpK i : p i ∈ K := ⟨(hp i).1, by grind⟩
  have heReal i (x : ℝ) : e i x = (Real.exp ((p i - x)/t) : ℂ) := by aesop
  have hL i (x : ℝ) : l i x = ((x + t * Real.exp ((p i - x)/t) : ℝ) : ℂ) := by
    aesop
  have hmove i {z : ℂ} (hz : z ∈ nbhd s) : ‖l i z - z‖ ≤ t*E := by
    rw [show l i z - z = (t : ℂ) * e i z by ring, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le]
    simp only [e, Complex.norm_exp, Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((div_le_one ht).2 ?_)) ht.le
    obtain ⟨x, hx, hzx⟩ := hz
    have h := abs_lt.1 ((Complex.abs_re_le_norm _).trans_lt hzx)
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    grind
  have hstep i {z : ℂ} (hz : z ∈ nbhd s) : l i z ∈ nbhd (2*s) := by
    have h := hmove i hz
    obtain ⟨x, hx, hzx⟩ := hz
    exact ⟨x, hx, (norm_sub_le_norm_sub_add_norm_sub (l i z) z (x:ℂ)).trans_lt (by linarith)⟩
  have hK {x : ℝ} (hx : x ∈ K) : (x : ℂ) ∈ nbhd s := by
    refine ⟨max 0 x, by grind, ?_⟩
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    grind
  have hal (i : Fin N) (z : ℂ) : AnalyticAt ℂ (l i) z := by fun_prop
  have hag i {z : ℂ} (hz : z ∈ nbhd s) : AnalyticAt ℂ (g i) z :=
    (Φ.analyticAt_f i (subset_closure (hsub (hstep i hz)))).comp (hal i z)
  have him i {x : ℝ} (hx : (x : ℂ) ∈ nbhd s) : (g i x).im = 0 := by
    have hh := nbhd_subset_two Φ.ε_pos (hsub (hstep i hx))
    rw [hL] at hh
    simpa only [g, Function.comp_apply, hL] using Φ.im_f_ofReal i hh
  have hd i : DifferentiableOn ℂ (g i) (nbhd s) := fun _ hz => (hag i hz).differentiableAt.differentiableWithinAt
  have hsr : nbhd s ⊆ nbhd ε := nbhd_mono (by linarith)
  have hρs : nbhd (2*ρ) ⊆ nbhd s := nbhd_mono (by grind)
  have hjet i (j : Fin 3) {z : ℂ} (hz : z ∈ closedNbhd ρ) :
      ‖iteratedDeriv j (Φ.f i) z - iteratedDeriv j (g i) z‖ ≤ t*E*C j := by
    have hc : closedBall z ρ ⊆ nbhd s := by
      obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hρ.le hz
      intro w hw
      exact ⟨x, hx, (norm_sub_le_norm_sub_add_norm_sub w z (x:ℂ)).trans_lt
        (by have := mem_closedBall_iff_norm.1 hw; dsimp [ρ] at *; linarith)⟩
    have H (w) (hw : w ∈ nbhd s) : ‖Φ.f i w - g i w‖ ≤ t*E := by
      rw [norm_sub_rev]
      exact (flip i (hsub (hstep i hw)) (hsr hw)).trans (hmove i hw)
    have hz' := hc (mem_closedBall_self hρ.le)
    simpa only [iteratedDeriv_sub (Φ.analyticAt_f i (subset_closure (hsr hz'))).contDiffAt
      (hag i hz').contDiffAt, mul_comm (j.val.factorial : ℝ), mul_div_assoc, C] using (cauchy_bound hρ (((Φ.differentiableOn_f i).mono (hsr.trans (nbhd_subset_two Φ.ε_pos))).sub (hd i)) H hc j)
  have hCR : t*E*C 1 < R :=
    (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := C) (fun j _ => by positivity) (Finset.mem_univ 1))
      (by positivity)).trans_lt hMR
  have hcl i : InClass ρ (g i) := by
    have H {z : ℂ} (hz : z ∈ closedNbhd ρ) : 0 < ‖deriv (g i) z‖ ∧ ‖deriv (g i) z‖ < 1 := by
      have h := (abs_norm_sub_norm_le ..).trans (hjet i 1 hz)
      simp only [Fin.val_one, iteratedDeriv_one, abs_le] at h
      have hz' := closure_mono (nbhd_mono (show ρ ≤ ε by grind)) hz
      have hl := Φ.cmin_le_norm_deriv i hz'
      have hu := Φ.norm_deriv_le_cmax i hz'
      grind
    exact Challenge.InClass.of_deriv hρ ((hd i).mono hρs) (fun _ hx => him i (hρs hx))
      (fun _ hx => himage i (hstep i (hK (hIK hx)))) (fun _ hz => norm_pos_iff.1 (H hz).1) (fun _ hz => (H hz).2)
  let Ψ : IFS N ρ := ⟨g, hρ, hcl⟩
  refine ⟨ρ, Ψ, ?_, ?_⟩
  · rw [d2, d2Sys_eq]
    refine Finite.ciSup_lt_iff.2 fun i => ?_
    exact (Finset.sum_le_sum fun j _ => Real.iSup_le
      (fun x : I => hjet i j (ofReal_mem_closure hρ x.2)) (by positivity)).trans_lt
        (by rw [← Finset.mul_sum]; grind)
  have he i (z : ℂ) : HasDerivAt (e i) (e i z * ((-1:ℂ)/t)) z := by
    simpa [e] using (((hasDerivAt_const z (p i : ℂ)).sub (hasDerivAt_id z)).div_const (t : ℂ)).cexp
  have hl i : deriv (l i) = fun z => 1 - e i z := funext fun z => by
    rw [((hasDerivAt_id' z).fun_add ((he i z).const_mul (t : ℂ))).deriv]
    grind
  have hcrit i : deriv (l i) (p i) = 0 := by simp_all
  have hf i j := Φ.analyticAt_f i (subset_closure (hsub (hstep i (hK (hpK j)))))
  have hfne i j := (Φ.inClass i).deriv_ne_zero _ (subset_closure (hsub (hstep i (hK (hpK j)))))
  have hdg i j : deriv (g i) (p j) = deriv (Φ.f i) (l i (p j)) * deriv (l i) (p j) :=
    deriv_comp _ (hf i j).differentiableAt (hal i _).differentiableAt
  have h₁ i : deriv (g i) (p i) = 0 := by simp_all
  have h₂ i : deriv (deriv (g i)) (p i) ≠ 0 := by
    rw [← show iteratedDeriv 2 (g i) (p i) = deriv (deriv (g i)) (p i) by simp [iteratedDeriv_succ], show g i = Φ.f i ∘ l i from rfl,
      iteratedDeriv_comp_two (hf i i).contDiffAt (hal i _).contDiffAt, hcrit]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hl]
    rw [((hasDerivAt_const _ (1 : ℂ)).fun_sub (he i _)).deriv]
    simp [e, hfne, ht0]
  have hne i j (hij : i ≠ j) : deriv (g j) (p i) ≠ 0 := by
    rw [hdg, hl]
    dsimp only
    rw [heReal, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    apply mul_ne_zero (hfne j i)
    rw [ne_eq, Complex.ofReal_eq_zero, sub_eq_zero, eq_comm, Real.exp_eq_one_iff, div_eq_zero_iff, sub_eq_zero]
    tauto
  -- After clearing the first denominators, continuation detects the simple poles.
  intro u v huv
  by_contra! heq
  let S := Complex.ofReal '' K
  have ha i : AnalyticOnNhd ℂ (g i) S := by
    rintro _ ⟨x, hx, rfl⟩
    tauto
  have hmaps i : MapsTo (g i) S (nbhd ρ) := by
    rintro _ ⟨x, hx, rfl⟩
    have he : g i x = ((g i x).re : ℂ) := Complex.ext rfl (him i (hK hx))
    exact he ▸ ofReal_mem_nbhd hρ (himage i (hstep i (hK hx)))
  let B (w : ℕ → Fin N) (z : ℂ) := deriv (deriv (g (w 0))) z +
    deriv (g (w 0)) z ^ 2 * Ψ.dualProj (.inf fun k => w (k + 1)) (g (w 0) z)
  have hB w : AnalyticOnNhd ℂ (B w) S :=
    (ha _).deriv.deriv.add (((ha _).deriv.pow 2).mul
      (((Ψ.differentiableOn_dualProj _).analyticOnNhd (isOpen_nbhd _)).fun_comp (ha _) (hmaps _)))
  have hEq w (x : ℝ) (hx : x ∈ I) : B w x = deriv (g (w 0)) x * Ψ.dualProj (.inf w) x := by
    rw [Ψ.dualProj_inf_head w (ofReal_mem_closure hρ hx), nonlin]
    dsimp [B, Ψ]
    field_simp [(hcl _).deriv_ne_zero _ (ofReal_mem_closure hρ hx)]
  have H := eqOn_of_eqOn_Icc ((hB u).mul (ha (v 0)).deriv) ((hB v).mul (ha (u 0)).deriv)
    ((convex_Ioc ..).isPreconnected.image _ Complex.continuous_ofReal.continuousOn) (zero_lt_one (α := ℝ))
    (fun x hx => ⟨x, hIK hx, rfl⟩) (fun x hx => by grind)
    (mem_image_of_mem Complex.ofReal (hpK (u 0)))
  simp [B, h₁, h₂, hne _ _ huv] at H

end AnalyticESC.IFS
