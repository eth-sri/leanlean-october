module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteBase
public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Corollary 3.4: normalized Bethe wave, base Vandermonde limit, and eigenvalues
-/

@[expose] public section

open Finset Complex Filter Matrix Topology
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

def cor34_pairCount (n : ℕ) : ℕ := ∑ k : Fin n, (Finset.Ioi k).card

noncomputable def cor34_amplitudeFactor (ε x y : ℝ) : ℂ :=
  BetheAnsatz.z x * (1 + ((-ε / 2 : ℝ) : ℂ) * (Complex.exp (-(I * (x : ℂ))) + BetheAnsatz.z y))

noncomputable def cor34_normalizedAmplitude {n : ℕ} (ε : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (Equiv.Perm.sign σ : ℤ) * ∏ k : Fin n, ∏ l ∈ Finset.Ioi k, cor34_amplitudeFactor ε (p (σ k)) (p (σ l))

@[simp] theorem cor34_normalizedAmplitude_zero {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    cor34_normalizedAmplitude 0 p σ =
      (Equiv.Perm.sign σ : ℤ) * ∏ k : Fin n, ∏ _l ∈ Finset.Ioi k, BetheAnsatz.z (p (σ k)) := by
  simp [cor34_normalizedAmplitude, cor34_amplitudeFactor]

theorem cor34_normalizedAmplitude_eq_scaled_amplitude {n : ℕ} (ε : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hε : ε ≠ 0) :
    cor34_normalizedAmplitude ε p σ =
      ((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n * BetheAnsatz.amplitude (1 / ε) p σ := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  have hfactor (x y : ℝ) :
      cor34_amplitudeFactor ε x y = q * (BetheAnsatz.z x * BetheAnsatz.scattering (1 / ε) x y) := by
    have hq : q * ((1 / ε : ℝ) : ℂ) = -(1 / 2 : ℂ) := by dsimp [q]; push_cast; field_simp [hε]
    unfold cor34_amplitudeFactor BetheAnsatz.scattering
    dsimp only [q] at hq ⊢
    linear_combination 2 * BetheAnsatz.z x * hq
  unfold cor34_normalizedAmplitude BetheAnsatz.amplitude cor34_pairCount
  simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  dsimp [q]; ring

def cor34_sourceEvenPositions {n : ℕ} : Fin n → ℤ := fun k => (2 * (k.val + 1) : ℕ)

noncomputable def cor34_normalizedCoordinate {n : ℕ} (ε : ℝ) (p : Fin n → ℝ) (x : Fin n → ℤ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), cor34_normalizedAmplitude ε p σ * BetheAnsatz.planeWave p σ x

theorem cor34_normalizedCoordinate_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (x : Fin n → ℤ) :
    Tendsto (fun ε => cor34_normalizedCoordinate ε (p ε) x) (𝓝 0)
      (𝓝 (cor34_normalizedCoordinate 0 (p 0) x)) := by
  have hAmp (σ : Equiv.Perm (Fin n)) :
      Continuous (fun q : ℝ × (Fin n → ℝ) => cor34_normalizedAmplitude q.1 q.2 σ) :=
    Continuous.mul continuous_const
      (continuous_finsetProd _ fun k _ => continuous_finsetProd _ fun l _ => by
        dsimp [cor34_amplitudeFactor, BetheAnsatz.z]; fun_prop)
  have hc : Continuous (fun q : ℝ × (Fin n → ℝ) => cor34_normalizedCoordinate q.1 q.2 x) :=
    continuous_finsetSum _ fun σ _ =>
      (hAmp σ).mul (by dsimp [BetheAnsatz.planeWave, BetheAnsatz.z]; fun_prop)
  simpa only [Function.comp_def, id_eq] using hc.continuousAt.tendsto.comp (continuousAt_id.tendsto.prodMk_nhds hp)

theorem cor34_normalizedCoordinate_eq_scaled_coordinateWave {n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) (x : Fin n → ℤ) (hε : ε ≠ 0) :
    cor34_normalizedCoordinate ε p x =
      ((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n * BetheAnsatz.coordinateWave (1 / ε) p x := by
  unfold cor34_normalizedCoordinate BetheAnsatz.coordinateWave
  simp_rw [cor34_normalizedAmplitude_eq_scaled_amplitude ε p _ hε, mul_assoc, ← Finset.mul_sum]

noncomputable def cor34_evenCoordinateState {N n : ℕ} (hN : 2 * n ≤ N) : State N n :=
  ⟨Finset.univ.image (fun k : Fin n => (⟨2 * k.val + 1, by omega⟩ : Fin N)), by
    rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))]
    simp⟩

theorem cor34_evenCoordinateState_positions {N n : ℕ} (hN : 2 * n ≤ N) :
    BetheAnsatz.positions (cor34_evenCoordinateState hN) = fun k => ((2 * k.val + 1 : ℕ) : ℤ) := by
  let x := cor34_evenCoordinateState hN
  let f : Fin n → Fin N := fun k => ⟨2 * k.val + 1, by omega⟩
  have horder : f = x.1.orderEmbOfFin x.2 :=
    Finset.orderEmbOfFin_unique x.2 (fun k => Finset.mem_image_of_mem f (Finset.mem_univ k))
      (fun i j hij => show 2 * i.val + 1 < 2 * j.val + 1 by omega)
  funext k; change ((x.1.orderEmbOfFin x.2 k).val : ℤ) = _; rw [← horder]

noncomputable def cor34_halfRoot (m : ℕ) : ℂ := Complex.exp (Real.pi * I / (m : ℂ))

theorem cor34_base_z_eq_halfRoot_zpow {N n : ℕ} (hnN : n < N) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) =
      cor34_halfRoot (N - n) ^ (2 * (j.val : ℤ) + 1 - (n : ℤ)) := by
  have hm : ((N - n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hnN).ne'
  have harg : I * (Bethe.discreteBaseSolution N n j : ℂ) =
      ((2 * (j.val : ℤ) + 1 - (n : ℤ) : ℤ) : ℂ) * (Real.pi * I / ((N - n : ℕ) : ℂ)) := by
    have hp : Bethe.discreteBaseSolution N n j =
        Real.pi * ((2 * (j.val : ℤ) + 1 - (n : ℤ) : ℤ) : ℝ) / ((N - n : ℕ) : ℝ) := by
      dsimp [Bethe.discreteBaseSolution, Bethe.discreteBetheIndex]; push_cast; field_simp [hm]; ring
    rw [hp]; push_cast; field_simp [hm]
  unfold BetheAnsatz.z cor34_halfRoot; rw [harg, Complex.exp_int_mul]

theorem cor34_eventually_normalizedCoordinate_ne_zero {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hn : 2 * n ≤ N) :
    ∀ᶠ ε in 𝓝 0, cor34_normalizedCoordinate ε (p ε) cor34_sourceEvenPositions ≠ 0 := by
  let zf : Fin n → ℂ := fun j => BetheAnsatz.z (Bethe.discreteBaseSolution N n j)
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => zf i ^ (n + j.val + 1)
  have hdet_eq : cor34_normalizedCoordinate 0 (Bethe.discreteBaseSolution N n) cor34_sourceEvenPositions = M.det := by
    rw [Matrix.det_apply']; unfold cor34_normalizedCoordinate
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [cor34_normalizedAmplitude_zero, mul_assoc]; congr 1
    unfold BetheAnsatz.planeWave cor34_sourceEvenPositions
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hz1 : (∏ _l ∈ Finset.Ioi k, zf (σ k)) = zf (σ k) ^ (n - 1 - k.val) := by simp
    have hz2 : Complex.exp (I * (Bethe.discreteBaseSolution N n (σ k) : ℂ) * (((2 * (k.val + 1) : ℕ) : ℤ) : ℂ)) =
        zf (σ k) ^ (2 * (k.val + 1)) := by
      dsimp [zf, BetheAnsatz.z]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hz1, hz2, ← pow_add]; dsimp [M]; congr 1; omega
  have hpS := Bethe.discreteBaseSolution_mem_S_n hN hn
  have hZinj : Function.Injective zf := fun i j hij => by
    have hexp : Complex.exp (I * (Bethe.discreteBaseSolution N n i : ℂ)) =
        Complex.exp (I * (Bethe.discreteBaseSolution N n j : ℂ)) := by simpa [zf, BetheAnsatz.z] using hij
    have hargs := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simpa using (hpS.1 i).1) (by simpa using (hpS.1 i).2.le)
      (by simpa using (hpS.1 j).1) (by simpa using (hpS.1 j).2.le) hexp
    exact hpS.2.1.injective (by simpa using congrArg Complex.im hargs)
  have hMfac : M = Matrix.diagonal (fun i => zf i ^ (n + 1)) * Matrix.vandermonde zf := by
    ext i j; simp [M, Matrix.mul_apply, Matrix.diagonal, Matrix.vandermonde, pow_add, mul_assoc, mul_comm]
  have hne : M.det ≠ 0 := by
    rw [hMfac, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (BetheAnsatz.z_ne_zero _))
      (Matrix.det_vandermonde_ne_zero_iff.mpr hZinj)
  have hlim := cor34_normalizedCoordinate_tendsto hp cor34_sourceEvenPositions
  rw [hp0, hdet_eq] at hlim
  exact hlim.eventually_ne hne

theorem cor34_deriv_theta_at_zero {Δ y : ℝ} (hΔ : Δ < -1) :
    deriv (fun t : ℝ => Bethe.theta Δ t y) 0 =
      -1 + 2 * (1 + Real.cos y - 2 * Δ) / ((1 + Real.cos y - 2 * Δ) ^ 2 + (Real.sin y) ^ 2) := by
  let d : ℝ := 1 + Real.cos y - 2 * Δ
  have hd : 0 < d := by dsimp [d]; linarith [Real.neg_one_le_cos y]
  have hfrac : HasDerivAt (fun t => (Real.sin t - Real.sin y) / (Real.cos t + Real.cos y - 2 * Δ)) (1 / d) 0 := by
    refine (((Real.hasDerivAt_sin 0).sub_const (Real.sin y)).div
      (((Real.hasDerivAt_cos 0).add_const (Real.cos y)).sub_const (2 * Δ))
      (by rw [Real.cos_zero]; exact hd.ne')).congr_deriv ?_
    rw [Real.sin_zero, Real.cos_zero]; change _ / d ^ 2 = 1 / d; field_simp [hd.ne']; ring
  have hth : HasDerivAt (fun t => Bethe.theta Δ t y)
      (-1 + 2 * (1 / (1 + ((Real.sin 0 - Real.sin y) / (Real.cos 0 + Real.cos y - 2 * Δ)) ^ 2) * (1 / d))) 0 := by
    unfold Bethe.theta
    exact (((hasDerivAt_const (0 : ℝ) y).sub (hasDerivAt_id 0)).congr_deriv (by ring)).add
      (((Real.hasDerivAt_arctan _).comp 0 hfrac).const_mul 2)
  rw [hth.deriv, Real.sin_zero, Real.cos_zero]
  have hden : d ^ 2 + Real.sin y ^ 2 ≠ 0 := by positivity
  change -1 + 2 * (1 / (1 + ((0 - Real.sin y) / d) ^ 2) * (1 / d)) = -1 + 2 * d / (d ^ 2 + Real.sin y ^ 2)
  field_simp [hd.ne', hden]; ring

noncomputable def cor34_derivativeCorrection (ε y : ℝ) : ℝ :=
  2 * ε * (ε * (1 + Real.cos y) - 2) / ((ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2)

noncomputable def cor34_normalizedL (ε x : ℝ) : ℂ :=
  ((-ε / 2 : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) * BetheAnsatz.z x / (1 - BetheAnsatz.z x)

noncomputable def cor34_normalizedM (ε x : ℝ) : ℂ :=
  ((-ε / 2 : ℝ) : ℂ) - ((1 - ε : ℝ) : ℂ) / (1 - BetheAnsatz.z x)

noncomputable def cor34_normalizedRegularEigenvalue {n : ℕ} (ε : ℝ) (p : Fin n → ℝ) : ℂ :=
  (∏ j : Fin n, cor34_normalizedL ε (p j)) + ∏ j : Fin n, cor34_normalizedM ε (p j)

noncomputable def cor34_normalizedZeroEigenvalue {N n : ℕ} (ε : ℝ) (p : Fin n → ℝ) (l : Fin n) : ℂ :=
  (((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
      ((N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection ε (p j)))) *
    ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)

theorem cor34_normalizedRegularEigenvalue_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (hz : ∀ j, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((∏ j : Fin n, BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j))) +
            ∏ j : Fin n, (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hpair (j : Fin n) : Tendsto (fun ε => (ε, p ε j)) (𝓝 0) (𝓝 (0, p 0 j)) :=
    continuousAt_id.tendsto.prodMk_nhds ((continuous_apply j).continuousAt.tendsto.comp hp)
  have hL (j : Fin n) : Tendsto (fun ε => cor34_normalizedL ε (p ε j)) (𝓝 0)
      (𝓝 (BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j)))) := by
    have hc : ContinuousAt (fun q : ℝ × ℝ => cor34_normalizedL q.1 q.2) (0, p 0 j) := by
      unfold cor34_normalizedL BetheAnsatz.z
      exact (Continuous.continuousAt (by fun_prop)).add
        ((Continuous.continuousAt (by fun_prop)).div (Continuous.continuousAt (by fun_prop))
          (sub_ne_zero.mpr (hz j).symm))
    simpa [cor34_normalizedL, Function.comp_def] using hc.tendsto.comp (hpair j)
  have hM (j : Fin n) : Tendsto (fun ε => cor34_normalizedM ε (p ε j)) (𝓝 0)
      (𝓝 ((-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
    have hc : ContinuousAt (fun q : ℝ × ℝ => cor34_normalizedM q.1 q.2) (0, p 0 j) := by
      unfold cor34_normalizedM BetheAnsatz.z
      exact (Continuous.continuousAt (by fun_prop)).sub
        ((Continuous.continuousAt (by fun_prop)).div (Continuous.continuousAt (by fun_prop))
          (sub_ne_zero.mpr (hz j).symm))
    simpa [cor34_normalizedM, neg_div, Function.comp_def] using hc.tendsto.comp (hpair j)
  exact (tendsto_finsetProd Finset.univ fun j _ => hL j).add
    (tendsto_finsetProd Finset.univ fun j _ => hM j)

theorem cor34_normalizedZeroEigenvalue_tendsto {N n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (l : Fin n)
    (hz : ∀ j ∈ Finset.univ.erase l, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε) l) (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) *
        ∏ j ∈ Finset.univ.erase l, (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt l.isLt)
  have hpair (j : Fin n) : Tendsto (fun ε => (ε, p ε j)) (𝓝 0) (𝓝 (0, p 0 j)) :=
    continuousAt_id.tendsto.prodMk_nhds ((continuous_apply j).continuousAt.tendsto.comp hp)
  have hcorr (j : Fin n) : Tendsto (fun ε => cor34_derivativeCorrection ε (p ε j)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun q : ℝ × ℝ => cor34_derivativeCorrection q.1 q.2) (0, p 0 j) := by
      unfold cor34_derivativeCorrection
      exact (Continuous.continuousAt (by fun_prop)).div (Continuous.continuousAt (by fun_prop)) (by norm_num)
    simpa [cor34_derivativeCorrection, Function.comp_def] using hc.tendsto.comp (hpair j)
  have hM (j : Fin n) (hj : j ∈ Finset.univ.erase l) : Tendsto (fun ε => cor34_normalizedM ε (p ε j)) (𝓝 0)
      (𝓝 ((-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
    have hc : ContinuousAt (fun q : ℝ × ℝ => cor34_normalizedM q.1 q.2) (0, p 0 j) := by
      unfold cor34_normalizedM BetheAnsatz.z
      exact (Continuous.continuousAt (by fun_prop)).sub
        ((Continuous.continuousAt (by fun_prop)).div (Continuous.continuousAt (by fun_prop))
          (sub_ne_zero.mpr (hz j hj).symm))
    simpa [cor34_normalizedM, neg_div, Function.comp_def] using hc.tendsto.comp (hpair j)
  have hsum : Tendsto (fun ε : ℝ => ((N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection ε (p ε j))))
      (𝓝 0) (𝓝 ((N : ℝ) - n)) := by
    have hs := (tendsto_const_nhds (x := (N : ℝ) - 1)).add (tendsto_finsetSum (Finset.univ.erase l) fun j _ =>
      (tendsto_const_nhds (x := (-1 : ℝ))).add (hcorr j))
    convert hs using 2
    simp [Finset.card_erase_of_mem (Finset.mem_univ l), Nat.cast_sub hn]
  have hpre : Tendsto (fun ε : ℝ => ((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
      (((N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection ε (p ε j)) : ℝ) : ℂ))
      (𝓝 0) (𝓝 ((N : ℂ) - (n : ℂ))) := by
    have hc1 : Continuous (fun ε : ℝ => ((-ε : ℝ) : ℂ)) := by fun_prop
    have hc2 : Continuous (fun ε : ℝ => ((1 - ε : ℝ) : ℂ)) := by fun_prop
    have h1 : Tendsto (fun ε : ℝ => ((-ε : ℝ) : ℂ)) (𝓝 0) (𝓝 0) := by simpa using (hc1.continuousAt (x := 0)).tendsto
    have h2 : Tendsto (fun ε : ℝ => ((1 - ε : ℝ) : ℂ)) (𝓝 0) (𝓝 1) := by simpa using (hc2.continuousAt (x := 0)).tendsto
    simpa [Function.comp_def] using h1.add (h2.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hsum))
  simpa [cor34_normalizedZeroEigenvalue] using hpre.mul (tendsto_finsetProd (Finset.univ.erase l) hM)

theorem cor34_normalizedRegularEigenvalue_scale {n : ℕ} {ε : ℝ} (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
      ((-ε / 2 : ℝ) : ℂ) ^ n * BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ); let c := Real.sqrt (2 - 2 / ε)
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    have hr2 : c ^ 2 = 2 - 2 / ε := Real.sq_sqrt (by linarith [div_neg_of_pos_of_neg two_pos hε])
    dsimp [q]; rw [show ((c : ℝ) : ℂ) ^ 2 = ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hr2]
    exact_mod_cast (show (-ε / 2) * (2 - 2 / ε) = 1 - ε by field_simp [hε.ne]; ring)
  have hL (j : Fin n) : cor34_normalizedL ε (p j) = q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedL BetheAnsatz.L; rw [← hcoeff]; ring
  have hM (j : Fin n) : cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M; rw [← hcoeff]; ring
  unfold cor34_normalizedRegularEigenvalue BetheAnsatz.eigenvalueRegular
  simp_rw [hL, hM, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  dsimp [q, c]; ring

theorem cor34_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    {ε : ℝ} (hInv : 1 / ε < -1) (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
      ((-ε / 2 : ℝ) : ℂ) ^ n * BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt l.isLt
  let qs : ℂ := ((-ε / 2 : ℝ) : ℂ); let c := Real.sqrt (2 - 2 / ε)
  have hr2 : c ^ 2 = 2 - 2 / ε := Real.sq_sqrt (by linarith [div_neg_of_pos_of_neg two_pos hε])
  have hcoeff : qs * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [qs]; rw [show ((c : ℝ) : ℂ) ^ 2 = ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hr2]
    exact_mod_cast (show (-ε / 2) * (2 - 2 / ε) = 1 - ε by field_simp [hε.ne]; ring)
  have hanis : BetheAnsatz.anisotropy c = 1 / ε := by unfold BetheAnsatz.anisotropy; rw [hr2]; ring
  have hderivC (j : Fin n) : deriv (fun t : ℝ => (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 =
      ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ) := by
    have hd : DifferentiableAt ℝ (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 := by
      simpa [hanis] using (Bethe.analyticAt_theta_left hInv 0 (p j)).differentiableAt
    rw [hd.hasDerivAt.ofReal_comp.deriv, hanis, cor34_deriv_theta_at_zero hInv, show 2 * (1 / ε) = 2 / ε by ring]
    congr 1; congr 1
    have hposD : 0 < (1 + Real.cos (p j) - 2 / ε) ^ 2 + Real.sin (p j) ^ 2 := by
      have : 0 < 1 + Real.cos (p j) - 2 / ε := by linarith [Real.neg_one_le_cos (p j), div_neg_of_pos_of_neg two_pos hε]
      positivity
    unfold cor34_derivativeCorrection
    rw [show (ε * (1 + Real.cos (p j)) - 2) ^ 2 + ε ^ 2 * Real.sin (p j) ^ 2 =
      ε ^ 2 * ((1 + Real.cos (p j) - 2 / ε) ^ 2 + Real.sin (p j) ^ 2) by field_simp [hε.ne],
      show 2 * ε * (ε * (1 + Real.cos (p j)) - 2) = ε ^ 2 * (2 * (1 + Real.cos (p j) - 2 / ε)) by field_simp [hε.ne]]
    field_simp [hε.ne, hposD.ne']
  have hM (j : Fin n) : cor34_normalizedM ε (p j) = qs * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M; rw [← hcoeff]; ring
  have hprodM : (∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)) =
      qs ^ (n - 1) * ∏ j ∈ Finset.univ.erase l, BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    simp_rw [hM]; rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
  change cor34_normalizedZeroEigenvalue ε p l = qs ^ n * BetheAnsatz.eigenvalueZero N c p l
  unfold cor34_normalizedZeroEigenvalue BetheAnsatz.eigenvalueZero
  rw [hprodM, Finset.sum_congr rfl fun j _ => hderivC j, Complex.ofReal_sum,
    show qs ^ n = qs * qs ^ (n - 1) by conv_lhs => rw [← Nat.sub_add_cancel hnpos, pow_succ, mul_comm]]
  have htwo : qs * 2 = ((-ε : ℝ) : ℂ) := by dsimp [qs]; push_cast; ring
  linear_combination (-htwo - hcoeff * (((N : ℂ) - 1) + ∑ j ∈ Finset.univ.erase l, ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ))) *
    (qs ^ (n - 1) * ∏ j ∈ Finset.univ.erase l, BetheAnsatz.M c (BetheAnsatz.z (p j)))

end PottsDiscontinuity.SixVertex
