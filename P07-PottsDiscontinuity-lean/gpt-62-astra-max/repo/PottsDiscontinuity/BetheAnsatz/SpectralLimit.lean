module
public import PottsDiscontinuity.BetheAnsatz.SpectralRow

/-! # Removable pole of the row eigenvalue

At a zero root both constant-word products have a simple pole. After the
common regular factors are removed their relative phase is fixed by the
Bethe equation at zero. Its slope gives precisely the derivative correction.
-/
@[expose] public section
open Finset Complex Classical Filter Topology
namespace PottsDiscontinuity.BetheAnsatz
noncomputable section
variable {n N : ℕ} {c : ℝ}

private lemma row_at_one {u : ℂ} (hu : u ≠ 1) :
    rowL (anisotropy c) 1 u = L c u ∧ rowM (anisotropy c) 1 u = M c u := by
  unfold rowL rowM L M anisotropy; push_cast; grind

lemma regular_row_limit (p : Fin n → ℝ) (hp : ∀ j, z (p j) ≠ 1) :
    Tendsto (fun t => rowScalar N (anisotropy c) (z t) p) (𝓝[≠] 0) (𝓝 (eigenvalueRegular c p)) := by
  have h : ContinuousAt (fun v => rowScalar N (anisotropy c) v p) 1 := by
    unfold rowScalar rowL rowM; fun_prop (disch := grind)
  have hz : Tendsto z (𝓝[≠] 0) (𝓝 1) := by simpa using hasDerivAt_z_zero.continuousAt.continuousWithinAt.tendsto (s := {0}ᶜ)
  simpa only [Function.comp_def,rowScalar,one_pow,one_mul,eigenvalueRegular,(row_at_one (hp _)).1,(row_at_one (hp _)).2] using h.tendsto.comp hz

private lemma phase_add (x y : ℝ) : z (x+y) = z x * z y := by simp [z,mul_add,exp_add]
private lemma phase_sum {ι} (s : Finset ι) (f : ι → ℝ) : z (∑ j ∈ s, f j) = ∏ j ∈ s, z (f j) := by simp [z,mul_sum,exp_sum]
section
variable (N : ℕ) (t : ℝ)

private lemma phase_N : z (N*t) = z t ^ N := by
  simp only [z, ofReal_mul, ofReal_natCast, ← exp_nat_mul]; ring

private lemma derivative_phase : HasDerivAt z (z t * I) t := by
  convert! (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.comp_ofReal) using 1 <;> simp [z]

end

private lemma phase_slope {f : ℝ → ℂ} {d : ℂ} (hf : HasDerivAt f d 0) (h : f 0 = 1) :
    Tendsto (fun t : ℝ => (f t-1)/(t:ℂ)) (𝓝[≠] 0) (𝓝 d) := by
  simpa [h, Complex.real_smul, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero

lemma singular_row_limit (hc : 2 < c) (p : Fin n → ℝ) (a : Fin n) (ha : p a = 0)
    (hp : ∀ j ≠ a, z (p j) ≠ 1) (hBE : BetheEquations N (anisotropy c) p) :
    Tendsto (fun t => rowScalar N (anisotropy c) (z t) p) (𝓝[≠] 0) (𝓝 (eigenvalueZero N c p a)) := by
  let Δ := anisotropy c
  have hΔ : Δ < -1 := anisotropy_lt_neg_one hc
  let s := univ.erase a
  let θ := fun (j : Fin n) t => Bethe.theta Δ t (p j)
  let f := fun t : ℝ => N*t + ∑ j ∈ s, θ j t
  let D := N + ∑ j ∈ s, deriv (θ j) 0
  let P := fun t => (-1 : ℂ)^s.card * z (f t)
  let B := fun t => ∏ j ∈ s, rowM Δ (z t) (z (p j))
  have he (t : ℝ) : z t^N * (∏ j ∈ s, rowL Δ (z t) (z (p j))) = P t * B t := by
    simp_rw [rowL_phase hΔ t]; rw [prod_mul_distrib,prod_neg]
    simp only [P,B,f,θ,phase_add,phase_N,phase_sum]; grind [z]
  have hP : P 0 = 1 := by
    have hb := hBE a
    rw [ha, ← sum_erase_add _ _ (mem_univ a)] at hb
    simp only [ha,Bethe.theta_self,add_zero,ofReal_zero,mul_zero,exp_zero,exp_neg] at hb
    rw [← div_eq_mul_inv, eq_div_iff (exp_ne_zero _), one_mul] at hb
    simp only [P,f,z,θ,s,Finset.card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fin,
      mul_zero,zero_add,Δ,hb,← mul_pow]; norm_num
  have hf : HasDerivAt f D 0 := by
    apply HasDerivAt.add ((hasDerivAt_id' (0:ℝ)).const_mul _ |>.congr_deriv (by ring))
    exact HasDerivAt.fun_sum fun j _ => (Bethe.analyticAt_theta_left hΔ 0 (p j)).differentiableAt.hasDerivAt
  have hd : HasDerivAt P ((D:ℂ)*I) 0 := by
    convert! ((derivative_phase _).scomp 0 hf).const_mul ((-1:ℂ)^s.card) using 1
    rw [Complex.real_smul]; linear_combination -(D:ℂ)*I*hP
  have hz : Tendsto z (𝓝[≠] 0) (𝓝 1) := by simpa using hasDerivAt_z_zero.continuousAt.continuousWithinAt.tendsto (s := {0}ᶜ)
  have hQ : Tendsto (fun t => (P t-1)/(z t-1)) (𝓝[≠] 0) (𝓝 (D:ℂ)) := by
    have h := (phase_slope hd hP).div (phase_slope hasDerivAt_z_zero z_zero) I_ne_zero
    apply (show Tendsto _ _ (𝓝 (D:ℂ)) from by simpa using h).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' := ofReal_ne_zero.mpr ht
    dsimp only [Pi.div_apply]; field_simp
  have hB : Tendsto B (𝓝[≠] 0) (𝓝 (∏ j ∈ s, M c (z (p j)))) := by
    apply tendsto_finsetProd _ fun j hj => ?_
    have hj' := hp j (mem_erase.mp hj).1
    rw [← (row_at_one hj').2]; have h : ContinuousAt (fun v => rowM Δ v (z (p j))) 1 := by
      unfold rowM; fun_prop (disch := exact sub_ne_zero.mpr hj')
    exact h.tendsto.comp hz
  have hlim := (tendsto_const_nhds (x := 2*(Δ:ℂ))).add (((hz.add_const 1).sub_const (2*(Δ:ℂ))).mul hQ) |>.mul hB
  have hdr (j : Fin n) : deriv (fun t => (Bethe.theta (anisotropy c) t (p j) : ℂ)) 0 = ((deriv (θ j) 0 : ℝ) : ℂ) :=
    ((Bethe.analyticAt_theta_left hΔ 0 (p j)).differentiableAt.hasDerivAt.ofReal_comp).deriv
  convert_to Tendsto _ _ (𝓝 ((2*(Δ:ℂ)+((1:ℂ)+1-2*Δ)*D)*(∏ j ∈ s, M c (z (p j)))))
  · congr 2; simp only [eigenvalueZero,hdr]; simp only [D,s,Δ,anisotropy,ofReal_add,ofReal_sub,ofReal_div,ofReal_ofNat,ofReal_pow,ofReal_sum,ofReal_natCast]; ring
  apply hlim.congr'
  filter_upwards [eventually_avoid 1] with t ht
  simp only [rowScalar, ← mul_prod_erase univ _ (mem_univ a), ha, z_zero]
  rw [mul_left_comm, he t]; change _ = rowL Δ (z t) 1 * (P t * B t) + rowM Δ (z t) 1 * B t
  unfold rowL rowM
  field_simp [sub_ne_zero.mpr ht, sub_ne_zero.mpr ht.symm]; ring

end
end PottsDiscontinuity.BetheAnsatz
