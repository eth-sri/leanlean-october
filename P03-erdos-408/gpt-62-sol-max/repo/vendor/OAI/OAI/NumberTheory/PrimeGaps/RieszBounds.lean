module

public import OAI.NumberTheory.PrimeGaps.PrincipalGrowth

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Complex Filter Topology

noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna  := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) := norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm  := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  classical
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    exact_mod_cast (show 1 ≤ 4*(n+1) by omega)
  obtain ⟨cp,hcp,hlp⟩ := principal_strip_lower hε hε1
  obtain ⟨cn,hcn,hln⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨Kp,hKp,hbp⟩ := principal_deriv_growth hε hε1
  obtain ⟨Kn,hKn,hbn⟩ := LFunction_deriv_norm_small_power
    (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let c := min cp cn
  let K := max (3*Kp) Kn*3^ε
  have hc : 0<c := lt_min hcp hcn
  have hm : 0<max (3*Kp) Kn := hKn.trans_le (le_max_right _ _)
  have hK : 0<K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0<d := by dsimp [d]; positivity
  have hd1 : d≤1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d≤ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d≤c/2 := by
    have hh := (le_div_iff₀ (show 0<2*K by positivity)).mp
      (show d≤c/(2*K) from min_le_right _ _)
    linarith
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro q _ χ hχp σ t hσ hσ2
  let T := |t|+2
  let Q : ℝ := (q:ℝ)+2
  let X := Q*T
  let P := X^ε
  let A := if χ=1 then T else 1
  have hQ : 1≤Q := by dsimp [Q]; linarith only [Nat.cast_nonneg (α := ℝ) q]
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg t]
  have hTX : T≤X := le_mul_of_one_le_left (zero_le_one.trans hT) hQ
  have hX := hT.trans hTX
  have hT0 : 0<T := zero_lt_one.trans_le hT
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hP := Real.one_le_rpow hX hε.le
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hA : 0<A := by dsimp [A]; split <;> positivity
  have hlow : c*A/P ≤ ‖poleRemovedL χ (σ+I*t)‖ := by
    by_cases hχ : χ=1
    · subst χ
      have hq : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
      subst q
      simp only [A, if_pos rfl]
      refine le_trans ?_ (hlp σ t hσ hσ2)
      change c*T/P ≤ cp*T/T^ε
      gcongr
      · exact min_le_left _ _
      · exact Real.rpow_le_rpow hT0.le hTX hε.le
    · have h := hln q χ hχp hχ σ t hσ hσ2
      change cn*X^(-ε) ≤ _ at h
      rw [Real.rpow_neg hX0.le,←div_eq_mul_inv] at h
      simp only [A,poleRemovedL,hχ,if_false,mul_one]
      exact (div_le_div_of_nonneg_right (min_le_right _ _) hP0.le).trans h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL χ) w‖ ≤ K*A*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    by_cases hχ : χ=1
    · subst χ
      have hq : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
      subst q
      simp only [A, if_pos rfl]
      change _ ≤ K*T*P
      calc
        _ ≤ Kp*(‖w‖+2)*(‖w‖+2)^ε := hbp w hre
        _ ≤ Kp*(3*T)*(3*X)^ε := by
          have h := hnorm.trans (mul_le_mul_of_nonneg_left hTX (by norm_num))
          gcongr
        _ = (3*Kp)*3^ε*T*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; ring
        _ ≤ _ := by dsimp [K]; gcongr; exact le_max_left _ _
    · have h := hbn q χ hχ w (by linarith)
      rw [show 2*(ε/2)=ε by ring] at h
      simp only [poleRemovedL,hχ,if_false,A,mul_one]
      calc
        _ ≤ Kn*(Q*(‖w‖+2))^ε := h
        _ ≤ Kn*(3*X)^ε := by
          have : Q*(‖w‖+2)≤3*X := by calc
            _ ≤ Q*(3*T) := by gcongr
            _ = _ := by dsimp [X]; ring
          gcongr
        _ = Kn*3^ε*P := by rw [Real.mul_rpow (by norm_num) hX0.le, mul_assoc]
        _ ≤ _ := by dsimp [K]; gcongr; exact le_max_right _ _
  have hh := logRiesz_power_bound n hP hA hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable χ).analyticAt w) hbound hlow
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change _ ≤ D*P^(2*n+2)/T^2 at hh
  have he : ε*(2*n+2:ℕ)=1/2 := by dsimp [ε]; push_cast; field_simp; ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  refine hh.trans_eq ?_
  change D*P^(2*n+2)/T^2 = D*Q^(1/2:ℝ)*T^(-(3/2:ℝ))
  rw [hpow, show X=Q*T from rfl, Real.mul_rpow (zero_le_one.trans hQ) hT0.le,
    Real.rpow_neg hT0.le]
  have ht : T^(1/2:ℝ)*T^(3/2:ℝ)=T^2 := by
    rw [←Real.rpow_add hT0,show (1/2:ℝ)+3/2=2 by norm_num,Real.rpow_two]
  field_simp
  rw [← ht]
  ring

end LargePrimeGaps

end OAI
