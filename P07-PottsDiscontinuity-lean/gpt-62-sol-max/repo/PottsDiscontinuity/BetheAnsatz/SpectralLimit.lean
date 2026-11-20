module

public import PottsDiscontinuity.BetheAnsatz.Regular

/-! At a zero momentum the two constant words have simple poles. Their
residues agree by the zero-root Bethe equation. Taking the derivative of
that common phase gives the corrected eigenvalue, with no wordwise residues. -/

@[expose] public section

namespace PottsDiscontinuity.BetheAnsatz
open Complex Filter Topology Finset Bethe Matrix Classical

private theorem spectral_numerators (Δ s x : ℝ) (hx : z (x-s) ≠ 1) :
    spectralLeft Δ s x * (1-z (x-s)) = z x * scattering Δ x s ∧
    spectralRight Δ s x * (1-z (x-s)) = -(z s * scattering Δ s x) := by
  have he : z x = z s * z (x-s) := by rw [← z_add]; simp
  constructor <;> rw [z_mul_scattering, he] <;>
    simp only [spectralLeft, spectralRight, gapLeft, gapRight, spectralInterior] <;>
    field_simp [sub_ne_zero.mpr hx.symm] <;> ring

private theorem spectralLeft_eq_phase_mul_right {Δ : ℝ} (hΔ : Δ < -1) (s x : ℝ)
    (hx : z (x-s) ≠ 1) :
    spectralLeft Δ s x = -z (theta Δ s x) * spectralRight Δ s x := by
  apply mul_right_cancel₀ (sub_ne_zero.mpr hx.symm)
  grind only [z_ne_zero, spectral_numerators, z, exp_I_theta_eq_scattering]

private noncomputable def spectralAngle {n : ℕ} (Δ : ℝ) (N : ℕ)
    (p : Fin n → ℝ) (J : Finset (Fin n)) (s : ℝ) : ℝ :=
  (N:ℝ)*s + ∑ j ∈ J, theta Δ s (p j)

private noncomputable def spectralPhase {n : ℕ} (Δ : ℝ) (N : ℕ)
    (p : Fin n → ℝ) (J : Finset (Fin n)) (s : ℝ) : ℂ :=
  (-1 : ℂ)^J.card * z (spectralAngle Δ N p J s)

private theorem spectralPhase_eq_product {n : ℕ} (Δ : ℝ) (N : ℕ) (p : Fin n → ℝ)
    (J : Finset (Fin n)) (s : ℝ) :
    spectralPhase Δ N p J s = z s ^ N * (∏ j ∈ J, -z (theta Δ s (p j))) := by
  rw [spectralPhase, spectralAngle, z_add, z_mul_nat]
  rw [show (∏ j ∈ J, -z (theta Δ s (p j))) = ∏ j ∈ J, (-1:ℂ) * z (theta Δ s (p j)) by
    simp, Finset.prod_mul_distrib, Finset.prod_const]
  unfold z
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
  ring

private theorem spectralPhase_zero {N n : ℕ} {Δ : ℝ} (p : Fin n → ℝ) (l : Fin n)
    (hl : p l = 0) (hBE : BetheEquations N Δ p) :
    spectralPhase Δ N p (univ.erase l) 0 = 1 := by
  have he := hBE l
  rw [hl] at he
  have hsum : ∑ j : Fin n, theta Δ 0 (p j) = ∑ j ∈ univ.erase l, theta Δ 0 (p j) := by
    simp [hl, theta_self]
  rw [hsum] at he
  have he' := congrArg Inv.inv he
  have hsgn (r : ℕ) : ((-1:ℂ)^r)⁻¹ = (-1:ℂ)^r := by rw [← inv_pow]; norm_num
  simpa [spectralPhase, spectralAngle, z, mul_inv, hsgn, Complex.exp_neg, mul_comm] using he'.symm

private theorem spectral_eigenvalue_subtracted {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin n → ℝ) (l : Fin n) (hl : p l = 0) (s : ℝ) (hp : ∀ j, z (p j-s) ≠ 1) :
    spectralEigenvalue N c s p =
      ((1+z s-2*(anisotropy c:ℂ)) * ((spectralPhase (anisotropy c) N p (univ.erase l) s - 1) /
        (1-z (-s))) + 2*(anisotropy c:ℂ)*z s) *
          ∏ j ∈ univ.erase l, spectralRight (anisotropy c) s (p j) := by
  let Δ := anisotropy c
  let J := univ.erase l
  have hprod : (∏ j ∈ J, spectralLeft Δ s (p j)) =
      (∏ j ∈ J, -z (theta Δ s (p j))) * ∏ j ∈ J, spectralRight Δ s (p j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => spectralLeft_eq_phase_mul_right (anisotropy_lt_neg_one hc) s (p j) (hp j)
  have hz := hl ▸ hp l
  have hL := (spectral_numerators Δ s 0 hz).1
  have hM := (spectral_numerators Δ s 0 hz).2
  rw [z_mul_scattering] at hL hM
  simp only [zero_sub, z_zero, one_mul, mul_one] at hL hM
  have hd := sub_ne_zero.mpr (by simpa using hz.symm)
  have hden : z s * (1-z (-s)) = z s - 1 := by
    simp [z_neg, mul_sub, mul_inv_cancel₀ (z_ne_zero s)]
  have hreg (E : ℂ) : spectralLeft Δ s 0 * E + spectralRight Δ s 0 =
      (1+z s-2*(Δ:ℂ)) * ((E-1)/(1-z (-s))) + 2*(Δ:ℂ)*z s := by
    apply mul_right_cancel₀ hd
    rw [add_mul, add_mul, mul_right_comm (spectralLeft Δ s 0), hL, hM, mul_assoc (2*(Δ:ℂ)) (z s) (1-z (-s)), hden, mul_assoc (1+z s-2*(Δ:ℂ)), div_mul_cancel₀ _ hd]
    ring
  unfold spectralEigenvalue
  rw [← Finset.mul_prod_erase univ (fun j => spectralLeft Δ s (p j)) (mem_univ l),
    ← Finset.mul_prod_erase univ (fun j => spectralRight Δ s (p j)) (mem_univ l)]
  change _ * (spectralLeft Δ s (p l) * ∏ j ∈ J, spectralLeft Δ s (p j)) +
    (spectralRight Δ s (p l) * ∏ j ∈ J, spectralRight Δ s (p j)) = _
  rw [hl, hprod, ← hreg, spectralPhase_eq_product]
  ring

private theorem hasDerivAt_z_at (x : ℝ) : HasDerivAt z (I * z x) x := by
  convert (hasDerivAt_exp_smul_const (I : ℂ) (x : ℂ)).comp_ofReal using 1
  · ext t
    simp [z, mul_comm, Complex.exp_eq_exp_ℂ]
  · simp [z, mul_comm, Complex.exp_eq_exp_ℂ]

private theorem tendsto_spectral_phase_ratio {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin n → ℝ) (l : Fin n) (hl : p l = 0) (hBE : BetheEquations N Δ p) :
    Tendsto (fun s : ℝ => (spectralPhase Δ N p (univ.erase l) s - 1) / (1-z (-s)))
      (𝓝[≠] (0:ℝ)) (𝓝 ((N:ℂ)+∑ j ∈ univ.erase l, (deriv (fun t => theta Δ t (p j)) 0:ℂ))) := by
  let J := univ.erase l
  let a := (N:ℝ) + ∑ j ∈ J, deriv (fun t => theta Δ t (p j)) 0
  let F := spectralPhase Δ N p J
  have hF0 : F 0 = 1 := spectralPhase_zero p l hl hBE
  have ht (p₀ : ℝ) := (analyticAt_theta_left hΔ 0 p₀).differentiableAt.hasDerivAt
  have hA : HasDerivAt (spectralAngle Δ N p J) a 0 := by
    have h₁ : HasDerivAt (fun s : ℝ => (N:ℝ) * s) (N:ℝ) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul (N:ℝ)
    exact h₁.add (HasDerivAt.fun_sum (u := J) fun j _ => ht (p j))
  have hF : HasDerivAt F (I*(a:ℂ)) 0 := by
    have hh := ((hasDerivAt_z_at _).scomp 0 hA).const_mul ((-1:ℂ)^J.card)
    have he : (-1:ℂ)^J.card * (a • (I*z (spectralAngle Δ N p J 0))) = I*(a:ℂ) := by
      rw [Complex.real_smul]
      have hv : (-1:ℂ)^J.card * z (spectralAngle Δ N p J 0) = 1 := hF0
      linear_combination I*(a:ℂ)*hv
    rw [he] at hh
    exact hh
  have hG : HasDerivAt (fun s : ℝ => 1-z (-s)) I 0 := by
    have hz := (hasDerivAt_z_at (-(0:ℝ))).scomp 0 (hasDerivAt_neg (0:ℝ))
    have hg := (hasDerivAt_const (0:ℝ) (1:ℂ)).sub hz
    change HasDerivAt (fun s : ℝ => 1-z (-s)) _ 0 at hg
    simpa using hg
  have hh := hF.tendsto_slope_zero.div hG.tendsto_slope_zero Complex.I_ne_zero
  have qe : (I * (a:ℂ))/I = ((N:ℂ)+∑ j ∈ J, (deriv (fun t => theta Δ t (p j)) 0:ℂ)) := by
    rw [mul_comm, mul_div_cancel_right₀ _ Complex.I_ne_zero]
    push_cast [a]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (ht (p j)).ofReal_comp.deriv.symm
  rw [qe] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0:ℝ))] with s hs
  have hs0 : (s:ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 from hs)
  simp only [zero_add, hF0, neg_zero, z_zero, sub_self, sub_zero, Complex.real_smul, ofReal_inv]
  exact mul_div_mul_left _ _ (inv_ne_zero hs0)

private theorem continuous_z_fun : Continuous z := by unfold z; fun_prop

private theorem shifted_roots_eventually_regular {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (l : Fin n) (hl : p l = 0)
    (hinj : Function.Injective p) :
    ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ), ∀ j, z (p j-s) ≠ 1 := by
  apply eventually_all.mpr
  intro j
  by_cases hj : j = l
  · subst j
    have hI : Set.Ioo (-Real.pi) Real.pi ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos
    filter_upwards [nhdsWithin_le_nhds hI, self_mem_nhdsWithin] with s hs hs0
    rw [hl, zero_sub]
    exact z_ne_one ⟨by linarith [hs.2], by linarith [hs.1]⟩ (neg_ne_zero.mpr hs0)
  · have hc : ContinuousAt (fun s => z (p j-s)) 0 := (continuous_z_fun.comp (by fun_prop)).continuousAt
    exact (hc.eventually_ne (by simpa using z_ne_one (hp j) (fun h => hj (hinj (h.trans hl.symm))))).filter_mono nhdsWithin_le_nhds

private theorem tendsto_spectralEigenvalue_zeroRoot {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin n → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin n) (hl : p l = 0) (hBE : BetheEquations N (anisotropy c) p) :
    Tendsto (fun s => spectralEigenvalue N c s p) (𝓝[≠] (0:ℝ)) (𝓝 (eigenvalueZero N c p l)) := by
  let Δ := anisotropy c
  let J := univ.erase l
  have hA : Tendsto (fun s => 1+z s-2*(Δ:ℂ)) (𝓝[≠] (0:ℝ)) (𝓝 (1+1-2*(Δ:ℂ))) := by
    have h : ContinuousAt (fun s => 1+z s-2*(Δ:ℂ)) (0:ℝ) := by unfold z; fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun s => 2*(Δ:ℂ)*z s) (𝓝[≠] (0:ℝ)) (𝓝 (2*(Δ:ℂ))) := by
    simpa [mul_comm] using (continuous_z_fun.continuousAt.mul_const (2*(Δ:ℂ))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ))
  have hprod : Tendsto (fun s => ∏ j ∈ J, spectralRight Δ s (p j))
      (𝓝[≠] (0:ℝ)) (𝓝 (∏ j ∈ J, M c (z (p j)))) := by
    apply tendsto_finsetProd
    intro j hj
    have hjl := (Finset.mem_erase.mp hj).1
    have hz := z_ne_one (hp j) (fun h => hjl (hinj (h.trans hl.symm)))
    have hd : (1:ℂ)-z (p j-0) ≠ 0 := by simpa using sub_ne_zero.mpr hz.symm
    have h : ContinuousAt (fun s => spectralRight Δ s (p j)) (0:ℝ) := by
      unfold spectralRight gapRight spectralInterior z
      fun_prop (disch := exact hd)
    simpa [Δ] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := ((hA.mul (tendsto_spectral_phase_ratio (anisotropy_lt_neg_one hc) p l hl hBE)).add hB).mul hprod
  have he : (1+1-2*(Δ:ℂ)) * ((N:ℂ) + ∑ j ∈ J, (deriv (fun t => theta Δ t (p j)) 0:ℂ)) + 2*(Δ:ℂ) =
      2+(c:ℂ)^2*((N:ℂ)-1)+(c:ℂ)^2*∑ j ∈ J, (deriv (fun t => theta Δ t (p j)) 0:ℂ) := by
    generalize ∑ j ∈ J, (deriv (fun t => theta Δ t (p j)) 0:ℂ) = s
    unfold Δ anisotropy
    push_cast
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [shifted_roots_eventually_regular p hp l hl hinj] with s hs
  exact (spectral_eigenvalue_subtracted hc p l hl s hs).symm

private theorem continuous_spectralGapSum {N n : ℕ} (c : ℝ) (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ) :
    Continuous (fun s => spectralGapSum (N := N) c s x p) := by
  have hW (v w y : ℤ) : Continuous (fun s => gapPointWeight (z s ^ 2) (spectralInterior (anisotropy c) s) v w y) := by
    unfold gapPointWeight
    split_ifs <;> (try simp only [spectralInterior, z]) <;> fun_prop
  unfold spectralGapSum weightedGapSum weightedGapWeight planeWave
  fun_prop

/-- The unchanged Bethe wave has the derivative-corrected eigenvalue at a zero root. -/
theorem betheAnsatz_zeroRoot {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n+2) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n+2)) (hl : p l = 0) (hBE : BetheEquations N (anisotropy c) p) :
    (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      eigenvalueZero N c p l • betheVector (anisotropy c) p := by
  apply betheAnsatz_of_gap hc p hBE
  intro x hx hspan
  have hlim := (continuous_spectralGapSum (N := N) c x p).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ))
  have hshift : Tendsto (fun s => waveShift s x) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
    have h : ContinuousAt (fun s => waveShift s x) 0 := by unfold waveShift; fun_prop
    simpa [waveShift] using h.tendsto.mono_left nhdsWithin_le_nhds
  have H := (tendsto_spectralEigenvalue_zeroRoot hc p hp hinj l hl hBE).mul
    (hshift.mul_const (coordinateWave (anisotropy c) p x))
  have H' : Tendsto (fun s => spectralGapSum (N := N) c s x p) (𝓝[≠] (0:ℝ))
      (𝓝 (eigenvalueZero N c p l * coordinateWave (anisotropy c) p x)) := by
    rw [← one_mul (coordinateWave (anisotropy c) p x)]
    apply H.congr'
    filter_upwards [shifted_roots_eventually_regular p hp l hl hinj] with s hs
    exact (spectralGapSum_eq hc s x hx hspan p hs hBE).symm
  exact tendsto_nhds_unique hlim H'

end PottsDiscontinuity.BetheAnsatz
