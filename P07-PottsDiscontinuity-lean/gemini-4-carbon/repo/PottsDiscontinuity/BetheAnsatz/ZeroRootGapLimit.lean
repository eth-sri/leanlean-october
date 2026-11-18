module

public import PottsDiscontinuity.BetheAnsatz.Regular

/-!
# The punctured gap-sum identity at a zero root
-/

@[expose] public section

open Finset Complex Classical Topology

namespace PottsDiscontinuity.BetheAnsatz

private theorem prod_L_eq_prod_M_zero {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, L c (z (p j))) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) := by
  let s : Finset (Fin (n + 1)) := univ.erase l
  let θ (j : Fin (n + 1)) := Bethe.theta (anisotropy c) 0 (p j)
  have hsum : (∑ j ∈ s, θ j) = ∑ j, θ j := by
    rw [← Finset.sum_erase_add _ _ (mem_univ l)]; simp [s, θ, hpl, Bethe.theta_self]
  have heq : (1 : ℂ) = (-1 : ℂ) ^ n * Complex.exp (-(I * ((∑ j ∈ s, θ j : ℝ) : ℂ))) := by
    have hh := hBE l; rw [hpl] at hh; simpa [θ, ← hsum] using hh
  have hsgn : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← pow_add, show n + n = 2 * n by omega, pow_mul]; norm_num
  have hsne : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpos : Complex.exp (I * ((∑ j ∈ s, θ j : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by
    rw [← inv_inv (Complex.exp _), ← Complex.exp_neg,
      mul_left_cancel₀ hsne (heq.symm.trans hsgn.symm), ← inv_pow]; norm_num
  have hne0 {j : Fin (n + 1)} (hj : j ∈ s) : p j ≠ 0 := fun h0 =>
    (mem_erase.mp hj).1 (hinj (h0.trans hpl.symm))
  have hMne : ∏ j ∈ s, M c (z (p j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => M_ne_zero hc (z_ne_one (hp j) (hne0 hj))
  have hcalc : (∏ j ∈ s, Complex.exp (I * (θ j : ℂ))) =
      (-1 : ℂ) ^ n * ((∏ j ∈ s, L c (z (p j))) / (∏ j ∈ s, M c (z (p j)))) := by
    calc (∏ j ∈ s, Complex.exp (I * (θ j : ℂ)))
        = ∏ j ∈ s, ((-1 : ℂ) * (L c (z (p j)) / M c (z (p j)))) :=
          Finset.prod_congr rfl fun j hj => by rw [exp_I_theta_zero_eq_neg_L_div_M_of_mem hc (hp j) (hne0 hj)]; ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]; simp [s, Finset.card_erase_of_mem (mem_univ l)]
  have hprod : (∏ j ∈ s, Complex.exp (I * (θ j : ℂ))) = (-1 : ℂ) ^ n := by
    rw [← Complex.exp_sum, show (∑ j ∈ s, I * (θ j : ℂ)) = I * ((∑ j ∈ s, θ j : ℝ) : ℂ) by
      push_cast; rw [← Finset.mul_sum]]; exact hpos
  exact (div_eq_one_iff_eq hMne).mp (mul_left_cancel₀ hsne (by simpa using hcalc.symm.trans hprod))

private theorem hasDerivAt_z_zero' : HasDerivAt z I 0 := by
  convert! (hasDerivAt_exp_smul_const (I : ℂ) (0 : ℂ)).comp_ofReal using 1
  · ext t; simp [z, smul_eq_mul, mul_comm, Complex.exp_eq_exp_ℂ]
  · simp

private theorem eventually_z_ne_one_zero' : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), z t ≠ 1 := by
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos),
    self_mem_nhdsWithin] with t ht ht0 using z_ne_one ht ht0

private theorem tendsto_t_mul_L_zero (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => (t : ℂ) * L c (z t)) (𝓝[≠] (0 : ℝ)) (𝓝 (I * (c : ℂ) ^ 2)) := by
  have hslope : Filter.Tendsto (fun t : ℝ => (1 - z t) / (t : ℂ)) (𝓝[≠] 0) (𝓝 (-I)) :=
    hasDerivAt_z_zero'.tendsto_slope_zero.neg.congr fun t => by simp [div_eq_mul_inv, sub_eq_add_neg]; ring
  have hinv : Filter.Tendsto (fun t : ℝ => (t : ℂ) / (1 - z t)) (𝓝[≠] 0) (𝓝 I) := by
    refine (by simpa using hslope.inv₀ (by simp : (-I : ℂ) ≠ 0) : Filter.Tendsto _ _ (𝓝 I)).congr' ?_
    filter_upwards [eventually_z_ne_one_zero', self_mem_nhdsWithin] with t ht ht0
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have : 1 - z t ≠ 0 := sub_ne_zero.mpr ht.symm
    field_simp
  have hz : Filter.Tendsto z (𝓝[≠] 0) (𝓝 1) := by
    simpa only [z_zero] using hasDerivAt_z_zero'.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have ht0 : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
    continuous_ofReal.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  refine (by simpa [mul_comm] using ht0.add ((tendsto_const_nhds (x := (c : ℂ) ^ 2)).mul (hz.mul hinv)) :
      Filter.Tendsto _ _ (𝓝 (I * (c : ℂ) ^ 2))).congr' ?_
  filter_upwards [eventually_z_ne_one_zero'] with t ht
  have : 1 - z t ≠ 0 := sub_ne_zero.mpr ht.symm
  unfold L; field_simp

private theorem tendsto_t_mul_M_zero (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => (t : ℂ) * M c (z t)) (𝓝[≠] (0 : ℝ)) (𝓝 (-I * (c : ℂ) ^ 2)) := by
  have ht0 : Filter.Tendsto (fun t : ℝ => (2 - (c : ℂ) ^ 2) * (t : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2 - (c : ℂ) ^ 2)).mul
      (continuous_ofReal.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0))
  refine (by simpa using ht0.sub (tendsto_t_mul_L_zero c) : Filter.Tendsto _ _ (𝓝 (-I * (c : ℂ) ^ 2))).congr' ?_
  filter_upwards [eventually_z_ne_one_zero'] with t ht
  linear_combination -(t : ℂ) * L_add_M c ht

private noncomputable def pertP {k : ℕ} (p : Fin k → ℝ) (l : Fin k) (t : ℝ) : Fin k → ℝ :=
  Function.update p l t

private noncomputable def bethePhase (N : ℕ) (Δ : ℝ) {n : ℕ} (q : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (N : ℝ) * q j + ∑ r, Bethe.theta Δ (q j) (q r)

private noncomputable def betheDefect (N : ℕ) (Δ : ℝ) {n : ℕ} (q : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℂ :=
  (-1 : ℂ) ^ n * Complex.exp (I * (bethePhase N Δ q j : ℂ))

private noncomputable def defectSlope (N : ℕ) (Δ : ℝ) {n : ℕ} (p : Fin (n + 1) → ℝ)
    (l j : Fin (n + 1)) : ℝ :=
  if j = l then (N : ℝ) + ∑ r ∈ univ.erase l, deriv (fun t => Bethe.theta Δ t (p r)) 0
  else -deriv (fun t => Bethe.theta Δ t (p j)) 0

private theorem betheDefect_ne_zero (N : ℕ) (Δ : ℝ) {n : ℕ} (q : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    betheDefect N Δ q j ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _)

private theorem betheDefect_eq_one_of_BE {N n : ℕ} {Δ : ℝ} {p : Fin (n + 1) → ℝ}
    (hBE : BetheEquations N Δ p) (j : Fin (n + 1)) :
    betheDefect N Δ p j = 1 := by
  have h := hBE j; simp only [Nat.add_sub_cancel] at h
  unfold betheDefect bethePhase
  rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, mul_add, Complex.exp_add,
    show I * ((N : ℂ) * (p j : ℂ)) = I * (N : ℂ) * (p j : ℂ) by ring, h]
  set S : ℂ := ((∑ k, Bethe.theta Δ (p j) (p k) : ℝ) : ℂ)
  rw [show (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * Complex.exp (-(I * S)) * Complex.exp (I * S)) =
      ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (Complex.exp (-(I * S)) * Complex.exp (I * S)) by ring,
    ← pow_add, show n + n = 2 * n by omega, pow_mul, ← Complex.exp_add]; norm_num

private theorem hasDerivAt_betheDefect {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N Δ p) (j : Fin (n + 1)) :
    HasDerivAt (fun t : ℝ => betheDefect N Δ (pertP p l t) j)
      (I * (defectSlope N Δ p l j : ℂ)) 0 := by
  have hphase : HasDerivAt (fun t : ℝ => bethePhase N Δ (pertP p l t) j) (defectSlope N Δ p l j) 0 := by
    by_cases hjl : j = l
    · subst j
      have heq : (fun t : ℝ => bethePhase N Δ (pertP p l t) l) =
          fun t => (N : ℝ) * t + ∑ r ∈ univ.erase l, Bethe.theta Δ t (p r) := by
        funext t; unfold bethePhase; rw [← Finset.add_sum_erase _ _ (mem_univ l)]
        simp only [pertP, Function.update_self, Bethe.theta_self, zero_add]
        exact congrArg _ (Finset.sum_congr rfl fun r hr => by rw [Function.update_of_ne (mem_erase.mp hr).1])
      rw [heq]; simp only [defectSlope, ↓reduceIte]
      have h1 : HasDerivAt (fun t : ℝ => (N : ℝ) * t) (N : ℝ) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul (N : ℝ)
      exact h1.add (HasDerivAt.fun_sum fun r _ => (Bethe.analyticAt_theta_left hΔ 0 (p r)).differentiableAt.hasDerivAt)
    · have heq : (fun t : ℝ => bethePhase N Δ (pertP p l t) j) =
          fun t => ((N : ℝ) * p j + ∑ r ∈ univ.erase l, Bethe.theta Δ (p j) (p r)) - Bethe.theta Δ t (p j) := by
        funext t; unfold bethePhase; rw [← Finset.add_sum_erase _ _ (mem_univ l)]
        simp only [pertP, Function.update_of_ne hjl, Function.update_self, Bethe.theta_swap Δ (p j) t]
        rw [Finset.sum_congr rfl fun r hr => by rw [Function.update_of_ne (mem_erase.mp hr).1]]; ring
      rw [heq]; simp only [defectSlope, hjl, ↓reduceIte]
      exact ((Bethe.analyticAt_theta_left hΔ 0 (p j)).differentiableAt.hasDerivAt).const_sub _
  have hp0 : pertP p l 0 = p := by unfold pertP; rw [← hpl, Function.update_eq_self]
  refine (((Complex.hasDerivAt_exp _).comp 0 ((hphase.ofReal_comp).const_mul I)).const_mul ((-1 : ℂ) ^ n)).congr_deriv ?_
  change (-1 : ℂ) ^ n * (Complex.exp (I * (bethePhase N Δ (pertP p l 0) j : ℂ)) * _) = _
  rw [← mul_assoc, hp0]; change betheDefect N Δ p j * _ = _
  rw [betheDefect_eq_one_of_BE hBE j, one_mul]

private theorem tendsto_one_sub_defect_div_t {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N Δ p) (j : Fin (n + 1)) :
    Filter.Tendsto (fun t : ℝ => (1 - betheDefect N Δ (pertP p l t) j) / (t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-I * (defectSlope N Δ p l j : ℂ))) := by
  have hd := (hasDerivAt_betheDefect hΔ p l hpl hBE j).tendsto_slope_zero.neg
  have hp0 : pertP p l 0 = p := by unfold pertP; rw [← hpl, Function.update_eq_self]
  rw [← neg_mul] at hd
  exact hd.congr fun t => by rw [zero_add, hp0, betheDefect_eq_one_of_BE hBE j]; simp [div_eq_mul_inv, sub_eq_add_neg]; ring

private theorem tendsto_inv_defect_sub_one_div_t {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N Δ p) (j : Fin (n + 1)) :
    Filter.Tendsto (fun t : ℝ => ((betheDefect N Δ (pertP p l t) j)⁻¹ - 1) / (t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-I * (defectSlope N Δ p l j : ℂ))) := by
  have hp0 : pertP p l 0 = p := by unfold pertP; rw [← hpl, Function.update_eq_self]
  have hcont : Filter.Tendsto (fun t : ℝ => (betheDefect N Δ (pertP p l t) j)⁻¹) (𝓝[≠] 0) (𝓝 1) := by
    have hc := (hasDerivAt_betheDefect hΔ p l hpl hBE j).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    rw [hp0, betheDefect_eq_one_of_BE hBE j] at hc; simpa using hc.inv₀ one_ne_zero
  refine (by simpa using (tendsto_one_sub_defect_div_t hΔ p l hpl hBE j).mul hcont :
      Filter.Tendsto _ _ (𝓝 (-I * (defectSlope N Δ p l j : ℂ)))).congr fun t => ?_
  have hne := betheDefect_ne_zero N Δ (pertP p l t) j; field_simp [hne]

private def stepWord {k : ℕ} (r : Fin (k + 1)) (i : Fin k) : Bool := decide (i.val < r.val)

private theorem stepWord_injective {k : ℕ} : Function.Injective (stepWord (k := k)) := fun r s h => by
  have hcard (u : Fin (k + 1)) : (univ.filter fun i : Fin k => stepWord u i = true).card = u.val := by
    have heq : (univ.filter fun i : Fin k => stepWord u i = true) =
        univ.image (Fin.castLE (Nat.le_of_lt_succ u.isLt)) := by
      ext i; simp only [mem_filter, mem_univ, true_and, stepWord, decide_eq_true_eq, mem_image]
      exact ⟨fun hi => ⟨⟨i.val, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.isLt⟩
    rw [heq, card_image_of_injective _ (Fin.castLE_injective _), card_univ, Fintype.card_fin]
  exact Fin.ext (by rw [← hcard r, ← hcard s, h])

private theorem sum_wordTerms_eq_stepWords {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) (hq : ∀ j, z (q j) ≠ 1) :
    (∑ w : Fin (n + 1) → Bool, ∑ σ, wordTerm (N := N) c x q σ w) =
      ∑ r : Fin (n + 2), ∑ σ, wordTerm (N := N) c x q σ (stepWord r) := by
  rw [(Finset.sum_image (s := univ) (f := fun w => ∑ σ, wordTerm (N := N) c x q σ w) stepWord_injective.injOn).symm]
  refine (Finset.sum_subset (subset_univ _) fun w _ hw => ?_).symm
  by_cases hML : ∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true
  · obtain ⟨a, ha, hb⟩ := hML
    exact sum_wordTerm_eq_zero_of_adjacentML hc x q hq w a ha hb
  · exfalso; apply hw
    have hno : ∀ a : Fin n, ¬ (w a.castSucc = false ∧ w a.succ = true) := fun a hab => hML ⟨a, hab⟩
    have hanti : Antitone (fun i : Fin (n + 1) => if w i then (1 : ℕ) else 0) :=
      Fin.antitone_iff_succ_le.mpr fun a => by
        cases h0 : w a.castSucc <;> cases h1 : w a.succ <;>
          first | decide | exact False.elim (hno a ⟨h0, h1⟩)
    let S := univ.filter fun i : Fin (n + 1) => w i = true
    refine mem_image.mpr ⟨⟨S.card, Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))⟩, mem_univ _, funext fun i => ?_⟩
    unfold stepWord; dsimp
    cases hwi : w i
    · rw [decide_eq_false_iff_not]; intro hlt
      have hsub : S ⊆ univ.image (Fin.castLE (Nat.le_of_lt i.isLt)) := fun j hj => by
        have hwj := (mem_filter.mp hj).2
        have hji : j.val < i.val := by
          by_contra hge; have := hanti (Fin.le_def.mpr (Nat.le_of_not_lt hge)); simp [hwi, hwj] at this
        exact mem_image.mpr ⟨⟨j.val, hji⟩, mem_univ _, rfl⟩
      have hle := card_le_card hsub
      rw [card_image_of_injective _ (Fin.castLE_injective _), card_univ, Fintype.card_fin] at hle; omega
    · rw [decide_eq_true_eq]
      have hsup : univ.image (Fin.castLE (Nat.succ_le_of_lt i.isLt)) ⊆ S := fun j hj => by
        obtain ⟨u, _, rfl⟩ := mem_image.mp hj
        have hle : Fin.castLE (Nat.succ_le_of_lt i.isLt) u ≤ i := Fin.le_def.mpr (Nat.le_of_lt_succ u.isLt)
        have := hanti hle; simp only [hwi, ↓reduceIte] at this
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        cases hwu : w (Fin.castLE (Nat.succ_le_of_lt i.isLt) u) <;> simp [hwu] at this ⊢
      have hle := card_le_card hsup
      rw [card_image_of_injective _ (Fin.castLE_injective _), card_univ, Fintype.card_fin] at hle; omega

private theorem zn_mul_phase_eq_defect (N n : ℕ) (Δ : ℝ) (q : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    (-1 : ℂ) ^ n * Complex.exp (I * ((∑ k, Bethe.theta Δ (q j) (q k) : ℝ) : ℂ)) * z (q j) ^ N =
      betheDefect N Δ q j := by
  have hz : z (q j) ^ N = Complex.exp (I * (((N : ℝ) * q j : ℝ) : ℂ)) := by
    rw [z, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hz, betheDefect, bethePhase, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring

private theorem wordTerm_rotate_defect {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) :
    wordTerm (N := N) c (cyclicSuccessorPositions N x) q (σ * finRotate (n + 1))
      (fun k => w (finRotate (n + 1) k)) =
      betheDefect N (anisotropy c) q (σ 0) * wordTerm (N := N) c x q σ w := by
  let y := wordPositions N x w
  have hp := planeWave_cyclicPredecessorPositions N q σ (cyclicSuccessorPositions N y)
  rw [cyclicPredecessor_successor] at hp
  have hp' : planeWave q (σ * finRotate (n + 1)) (cyclicSuccessorPositions N y) =
      z (q (σ 0)) ^ N * planeWave q σ y := by
    rw [hp, mul_comm (z _ ^ N), mul_assoc, inv_mul_cancel₀ (pow_ne_zero N (z_ne_zero _)), mul_one]
  unfold wordTerm
  rw [wordCoefficient_rotate, amplitude_rotate_phase (anisotropy_lt_neg_one hc) q σ]
  change _ * wordCoefficient c q σ w * planeWave q (σ * finRotate (n + 1))
    (wordPositions N (cyclicSuccessorPositions N x) (fun k => w (finRotate (n + 1) k))) =
    _ * (_ * _ * planeWave q σ y)
  rw [wordPositions_rotate, hp', ← zn_mul_phase_eq_defect]; ring

private theorem sum_wordTerm_true_defect {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) :
    (∑ σ, wordTerm (N := N) c x q σ (fun _ => true)) =
      (∏ j, L c (z (q j))) * ∑ τ, (betheDefect N (anisotropy c) q (τ (Fin.last n)))⁻¹ *
        amplitude (anisotropy c) q τ * planeWave q τ x := by
  have hterm (σ : Equiv.Perm (Fin (n + 1))) :
      wordTerm (N := N) c x q σ (fun _ => true) =
        (∏ j, L c (z (q j))) * ((betheDefect N (anisotropy c) q (σ 0))⁻¹ *
          amplitude (anisotropy c) q (σ * finRotate (n + 1)) * planeWave q (σ * finRotate (n + 1)) x) := by
    have hne := betheDefect_ne_zero N (anisotropy c) q (σ 0)
    have hzn0 : z (q (σ 0)) ^ N ≠ 0 := pow_ne_zero N (z_ne_zero _)
    unfold wordTerm
    rw [wordCoefficient_true, wordPhase_true, planeWave_cyclicPredecessorPositions N q σ x,
      amplitude_rotate_phase (anisotropy_lt_neg_one hc) q σ, ← zn_mul_phase_eq_defect]
    field_simp [hne, hzn0]
  simp_rw [hterm, ← Finset.mul_sum]; congr 1
  have hsymm0 : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (finRotate (n + 1)).symm_apply_eq.mpr (finRotate_last : finRotate (n + 1) (Fin.last n) = 0).symm
  rw [← Equiv.sum_comp (Equiv.mulRight (finRotate (n + 1)))
    (fun τ => (betheDefect N (anisotropy c) q (τ (Fin.last n)))⁻¹ *
      amplitude (anisotropy c) q τ * planeWave q τ x)]
  exact Finset.sum_congr rfl fun σ _ => by rw [← hsymm0]; simp

private theorem sum_stepWord_eq_defect_weighted {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (m + 2) → ℤ) (q : Fin (m + 2) → ℝ) (hq : ∀ j, z (q j) ≠ 1) (r : Fin (m + 1)) :
    (∑ σ, wordTerm (N := N) c x q σ (stepWord r.succ.castSucc)) =
      ∑ σ, (1 - betheDefect N (anisotropy c) q (σ 0)) *
        wordTerm (N := N) c x q σ (stepWord r.succ.castSucc) := by
  let w := stepWord (k := m + 2) r.succ.castSucc
  have h0 : (∑ τ, wordTerm (N := N) c (cyclicSuccessorPositions N x) q τ (fun i => w (finRotate (m + 2) i))) = 0 := by
    refine sum_wordTerm_eq_zero_of_adjacentML hc (cyclicSuccessorPositions N x) q hq
      (fun i => w (finRotate (m + 2) i)) (Fin.last m) ?_ ?_
    · rw [show finRotate (m + 2) (Fin.last m).castSucc = Fin.last (m + 1) by simp]
      simp only [w, stepWord, Fin.val_last, Fin.val_castSucc, Fin.val_succ, decide_eq_false_iff_not]; omega
    · rw [Fin.succ_last, finRotate_last]; simp [w, stepWord]
  rw [← Equiv.sum_comp (Equiv.mulRight (finRotate (m + 2)))
    (fun τ => wordTerm (N := N) c (cyclicSuccessorPositions N x) q τ (fun i => w (finRotate (m + 2) i)))] at h0
  have hrot : (∑ σ, betheDefect N (anisotropy c) q (σ 0) * wordTerm (N := N) c x q σ w) = 0 :=
    (Finset.sum_congr rfl fun σ _ => (wordTerm_rotate_defect (N := N) (n := m + 1) hc x q σ w).symm).trans h0
  change (∑ σ, wordTerm (N := N) c x q σ w) = ∑ σ, (1 - betheDefect N (anisotropy c) q (σ 0)) * wordTerm (N := N) c x q σ w
  simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]; rw [hrot, sub_zero]

private def intSlots (m : ℕ) : Finset (Fin (m + 2)) :=
  ((univ : Finset (Fin (m + 2))).erase 0).erase (Fin.last (m + 1))

private theorem mem_intSlots {m : ℕ} {s : Fin (m + 2)} :
    s ∈ intSlots m ↔ s ≠ 0 ∧ s ≠ Fin.last (m + 1) := by simp [intSlots, and_comm]

private theorem mem_intSlots_val {m : ℕ} {s : Fin (m + 2)} :
    s ∈ intSlots m ↔ 0 < s.val ∧ s.val < m + 1 := by
  rw [mem_intSlots]
  exact ⟨fun ⟨h0, hL⟩ => ⟨Nat.pos_of_ne_zero (Fin.val_ne_of_ne h0),
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ s.isLt) (Fin.val_ne_of_ne hL)⟩,
    fun ⟨h0, hL⟩ => ⟨Fin.ne_of_val_ne (by dsimp; omega), Fin.ne_of_val_ne (by dsimp; omega)⟩⟩

private noncomputable def intFactor {m : ℕ} (c : ℝ) (q : Fin (m + 2) → ℝ)
    (σ : Equiv.Perm (Fin (m + 2))) (r : Fin (m + 1)) (s : Fin (m + 2)) : ℂ :=
  if s.val ≤ r.val then L c (z (q (σ s))) else M c (z (q (σ s)))

private theorem wordCoefficient_stepWord {m : ℕ} (c : ℝ) (q : Fin (m + 2) → ℝ)
    (σ : Equiv.Perm (Fin (m + 2))) (r : Fin (m + 1)) :
    wordCoefficient c q σ (stepWord r.succ.castSucc) =
      (M c (z (q (σ (Fin.last (m + 1))))) * L c (z (q (σ 0))) - 1) *
        ∏ s ∈ intSlots m, intFactor c q σ r s := by
  let w := stepWord (k := m + 2) r.succ.castSucc
  change (∏ i : Fin (m + 2), wordEdgeFactor c q σ w i) = _
  rw [Fin.prod_univ_castSucc, mul_comm]; congr 1
  · simp only [wordEdgeFactor, finRotate_last]
    rw [show w (Fin.last (m + 1)) = false by simp [w, stepWord]; omega,
        show w 0 = true by simp [w, stepWord]]; simp
  · rw [← Finset.mul_prod_erase univ _ (mem_univ r)]
    have hwr : wordEdgeFactor c q σ w r.castSucc = 1 := by
      have hrot : finRotate (m + 2) r.castSucc = r.succ := finRotate_of_lt (n := m + 1) r.isLt
      simp only [wordEdgeFactor, hrot]
      rw [show w r.castSucc = true by simp [w, stepWord], show w r.succ = false by simp [w, stepWord]]; simp
    rw [hwr, one_mul]
    refine Finset.prod_bij'
      (fun a _ => if a.val < r.val then a.succ else a.castSucc)
      (fun s hs => if h : s.val ≤ r.val then ⟨s.val - 1, by have := r.isLt; omega⟩
        else ⟨s.val, (mem_intSlots_val.mp hs).2⟩)
      (fun a ha => by
        have := Fin.val_ne_of_ne (mem_erase.mp ha).1; have := a.isLt; have := r.isLt
        rw [mem_intSlots_val]
        by_cases h : a.val < r.val <;> simp only [h, ↓reduceIte, Fin.val_succ, Fin.val_castSucc] <;> omega)
      (fun s hs => by
        obtain ⟨h1, h2⟩ := mem_intSlots_val.mp hs
        refine mem_erase.mpr ⟨Fin.ne_of_val_ne ?_, mem_univ _⟩
        by_cases h : s.val ≤ r.val <;> simp only [h, ↓reduceDIte] <;> dsimp <;> omega)
      (fun a ha => by
        have := Fin.val_ne_of_ne (mem_erase.mp ha).1; ext
        by_cases h : a.val < r.val
        · simp only [h, ↓reduceIte, Fin.val_succ, show a.val + 1 ≤ r.val by omega, ↓reduceDIte]; omega
        · simp only [h, ↓reduceIte, Fin.val_castSucc, show ¬ a.val ≤ r.val by omega, ↓reduceDIte])
      (fun s hs => by
        obtain ⟨h1, h2⟩ := mem_intSlots_val.mp hs; ext
        by_cases h : s.val ≤ r.val
        · simp only [h, ↓reduceDIte]
          rw [ite_eq_left (by dsimp; omega : (⟨s.val - 1, by omega⟩ : Fin (m + 1)).val < r.val), Fin.val_succ]; dsimp; omega
        · simp only [h, ↓reduceDIte]
          rw [ite_eq_right (by dsimp; omega : ¬ (⟨s.val, h2⟩ : Fin (m + 1)).val < r.val)]; rfl)
      (fun a ha => ?_)
    have hne := Fin.val_ne_of_ne (mem_erase.mp ha).1
    have hrot : finRotate (m + 2) a.castSucc = a.succ := finRotate_of_lt (n := m + 1) a.isLt
    simp only [wordEdgeFactor, hrot, intFactor]
    by_cases h : a.val < r.val
    · have hw1 : w a.castSucc = true := by simp [w, stepWord]; omega
      have hw2 : w a.succ = true := by simp [w, stepWord]; omega
      simp only [h, ↓reduceIte, hw1, hw2, Fin.val_succ]
      rw [ite_eq_left (by omega)]
    · have hw1 : w a.castSucc = false := by simp [w, stepWord]; omega
      have hw2 : w a.succ = false := by simp [w, stepWord]; omega
      simp only [h, ↓reduceIte, hw1, hw2, Bool.false_eq_true, Fin.val_castSucc]
      rw [ite_eq_right (by omega)]

private noncomputable def stepRes {N m : ℕ} (c : ℝ) (x : Fin (m + 2) → ℤ)
    (p : Fin (m + 2) → ℝ) (l : Fin (m + 2)) (r : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 2))) : ℂ :=
  let Δ := anisotropy c
  let w := stepWord (k := m + 2) r.succ.castSucc
  let s := σ.symm l
  if s = 0 then
    (c : ℂ) ^ 2 * (defectSlope N Δ p l l : ℂ) * amplitude Δ p σ *
      M c (z (p (σ (Fin.last (m + 1))))) * (∏ t ∈ intSlots m, intFactor c p σ r t) *
      wordPhase (N := N) x p σ w
  else if s = Fin.last (m + 1) then
    -(c : ℂ) ^ 2 * (defectSlope N Δ p l (σ 0) : ℂ) * amplitude Δ p σ *
      L c (z (p (σ 0))) * (∏ t ∈ intSlots m, intFactor c p σ r t) *
      wordPhase (N := N) x p σ w
  else
    (if s.val ≤ r.val then (1 : ℂ) else -1) * (c : ℂ) ^ 2 *
      (defectSlope N Δ p l (σ 0) : ℂ) * amplitude Δ p σ *
      (M c (z (p (σ (Fin.last (m + 1))))) * L c (z (p (σ 0))) - 1) *
      (∏ t ∈ (intSlots m).erase s, intFactor c p σ r t) *
      wordPhase (N := N) x p σ w

private theorem tendsto_defect_wordTerm {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (m + 2) → ℤ) (p : Fin (m + 2) → ℝ) (l : Fin (m + 2)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (r : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 2))) :
    Filter.Tendsto (fun t : ℝ => (1 - betheDefect N (anisotropy c) (pertP p l t) (σ 0)) *
        wordTerm (N := N) c x (pertP p l t) σ (stepWord r.succ.castSucc))
      (𝓝[≠] (0 : ℝ)) (𝓝 (stepRes (N := N) c x p l r σ)) := by
  let Δ := anisotropy c
  let w := stepWord (k := m + 2) r.succ.castSucc
  have hΔ := anisotropy_lt_neg_one hc
  have hp0 : pertP p l 0 = p := by unfold pertP; rw [← hpl, Function.update_eq_self]
  have hp_cont (k : Fin (m + 2)) : Continuous (fun t : ℝ => pertP p l t k) := by
    unfold pertP; by_cases hk : k = l <;> simp [hk] <;> fun_prop
  have hamp : Filter.Tendsto (fun t : ℝ => amplitude Δ (pertP p l t) σ) (𝓝[≠] 0) (𝓝 (amplitude Δ p σ)) := by
    have hcA : Continuous (fun t : ℝ => amplitude Δ (pertP p l t) σ) := by unfold amplitude scattering z; fun_prop
    have ht := hcA.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    rwa [hp0] at ht
  have hph : Filter.Tendsto (fun t : ℝ => wordPhase (N := N) x (pertP p l t) σ w) (𝓝[≠] 0) (𝓝 (wordPhase (N := N) x p σ w)) := by
    have hcP : Continuous (fun t : ℝ => wordPhase (N := N) x (pertP p l t) σ w) := by unfold wordPhase positionPhase; fun_prop
    have ht := hcP.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    rwa [hp0] at ht
  have hdef := tendsto_one_sub_defect_div_t hΔ p l hpl hBE (σ 0)
  have ht0 : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
    continuous_ofReal.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  let s := σ.symm l
  have hcoeff : Filter.Tendsto (fun t : ℝ => (t : ℂ) * wordCoefficient c (pertP p l t) σ w) (𝓝[≠] 0)
      (𝓝 (if s = 0 then
            I * (c : ℂ) ^ 2 * M c (z (p (σ (Fin.last (m + 1))))) * ∏ u ∈ intSlots m, intFactor c p σ r u
          else if s = Fin.last (m + 1) then
            -I * (c : ℂ) ^ 2 * L c (z (p (σ 0))) * ∏ u ∈ intSlots m, intFactor c p σ r u
          else
            (if s.val ≤ r.val then I * (c : ℂ) ^ 2 else -I * (c : ℂ) ^ 2) *
              (M c (z (p (σ (Fin.last (m + 1))))) * L c (z (p (σ 0))) - 1) *
              ∏ u ∈ (intSlots m).erase s, intFactor c p σ r u)) := by
    simp_rw [w, wordCoefficient_stepWord]
    have sne {i : Fin (m + 2)} (hi : i ≠ s) : σ i ≠ l := fun h => hi (σ.symm_apply_eq.mpr h.symm).symm
    have hint_away (U : Finset (Fin (m + 2))) (hU : s ∉ U) (t : ℝ) :
        (∏ u ∈ U, intFactor c (pertP p l t) σ r u) = ∏ u ∈ U, intFactor c p σ r u :=
      Finset.prod_congr rfl fun u hu => by
        dsimp only [intFactor, pertP]; rw [Function.update_of_ne (sne fun h => hU (h ▸ hu))]
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      have h0l : σ 0 = l := by rw [← hs0]; simp [s]
      have hLne : (Fin.last (m + 1) : Fin (m + 2)) ≠ s := by rw [hs0]; exact Fin.last_pos.ne'
      have hedge : Filter.Tendsto (fun t : ℝ => (t : ℂ) * (M c (z (pertP p l t (σ (Fin.last (m + 1))))) * L c (z (pertP p l t (σ 0))) - 1))
          (𝓝[≠] 0) (𝓝 (I * (c : ℂ) ^ 2 * M c (z (p (σ (Fin.last (m + 1))))))) := by
        refine (by simpa [mul_comm, mul_left_comm] using
          ((tendsto_const_nhds (x := M c (z (p (σ (Fin.last (m + 1))))))).mul (tendsto_t_mul_L_zero c)).sub ht0 :
          Filter.Tendsto _ _ _).congr fun t => ?_
        simp only [pertP, Function.update_of_ne (sne hLne), h0l, Function.update_self]; ring
      exact (hedge.mul tendsto_const_nhds).congr fun t => by
        rw [hint_away _ (fun h => (mem_intSlots.mp h).1 hs0) t, mul_assoc]
    · rw [ite_eq_right hs0]
      by_cases hsL : s = Fin.last (m + 1)
      · rw [ite_eq_left hsL]
        have hLl : σ (Fin.last (m + 1)) = l := by rw [← hsL]; simp [s]
        have hedge : Filter.Tendsto (fun t : ℝ => (t : ℂ) * (M c (z (pertP p l t (σ (Fin.last (m + 1))))) * L c (z (pertP p l t (σ 0))) - 1))
            (𝓝[≠] 0) (𝓝 (-I * (c : ℂ) ^ 2 * L c (z (p (σ 0))))) := by
          refine (by simpa [mul_assoc] using
            ((tendsto_t_mul_M_zero c).mul (tendsto_const_nhds (x := L c (z (p (σ 0)))))).sub ht0 :
            Filter.Tendsto _ _ _).congr fun t => ?_
          simp only [pertP, Function.update_of_ne (sne (Ne.symm hs0)), hLl, Function.update_self]; ring
        exact (hedge.mul tendsto_const_nhds).congr fun t => by
          rw [hint_away _ (fun h => (mem_intSlots.mp h).2 hsL) t, mul_assoc]
      · rw [ite_eq_right hsL]
        have hslim : Filter.Tendsto (fun t : ℝ => (t : ℂ) * intFactor c (pertP p l t) σ r s) (𝓝[≠] 0)
            (𝓝 (if s.val ≤ r.val then I * (c : ℂ) ^ 2 else -I * (c : ℂ) ^ 2)) := by
          unfold intFactor; simp only [show σ s = l by simp [s], pertP, Function.update_self]
          by_cases hsr : s.val ≤ r.val
          · simp only [hsr, ↓reduceIte]; exact tendsto_t_mul_L_zero c
          · simp only [hsr, ↓reduceIte]; exact tendsto_t_mul_M_zero c
        refine ((hslim.mul tendsto_const_nhds).mul tendsto_const_nhds).congr fun t => ?_
        rw [← Finset.mul_prod_erase (intSlots m) _ (mem_intSlots.mpr ⟨hs0, hsL⟩),
          hint_away _ (notMem_erase _ _) t]
        simp only [pertP, Function.update_of_ne (sne (Ne.symm hs0)), Function.update_of_ne (sne (Ne.symm hsL))]; ring
  have hprod := ((hdef.mul hamp).mul hcoeff).mul hph
  have heq_lim : (-I * (defectSlope N Δ p l (σ 0) : ℂ)) * amplitude Δ p σ *
      (if s = 0 then
        I * (c : ℂ) ^ 2 * M c (z (p (σ (Fin.last (m + 1))))) * ∏ u ∈ intSlots m, intFactor c p σ r u
      else if s = Fin.last (m + 1) then
        -I * (c : ℂ) ^ 2 * L c (z (p (σ 0))) * ∏ u ∈ intSlots m, intFactor c p σ r u
      else
        (if s.val ≤ r.val then I * (c : ℂ) ^ 2 else -I * (c : ℂ) ^ 2) *
          (M c (z (p (σ (Fin.last (m + 1))))) * L c (z (p (σ 0))) - 1) *
          ∏ u ∈ (intSlots m).erase s, intFactor c p σ r u) *
      wordPhase (N := N) x p σ w = stepRes (N := N) c x p l r σ := by
    unfold stepRes; dsimp only [Δ, w]
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0, ite_eq_left hs0, show σ 0 = l by rw [← hs0]; simp [s]]; ring_nf; rw [I_sq]; ring
    · by_cases hsL : s = Fin.last (m + 1)
      · rw [ite_eq_right hs0, ite_eq_left hsL, ite_eq_right hs0, ite_eq_left hsL]; ring_nf; rw [I_sq]; ring
      · rw [ite_eq_right hs0, ite_eq_right hsL, ite_eq_right hs0, ite_eq_right hsL]
        by_cases hsr : s.val ≤ r.val <;> [rw [ite_eq_left hsr, ite_eq_left hsr]; rw [ite_eq_right hsr, ite_eq_right hsr]] <;>
          (ring_nf; rw [I_sq]; ring)
  rw [heq_lim] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  unfold wordTerm; dsimp only [Δ, w]; field_simp [htC]

private def moveRight {k : ℕ} : ℕ → ℕ → Equiv.Perm (Fin k)
  | _, 0 => 1
  | i, d + 1 =>
    if h : i + d + 1 < k then
      moveRight i d * Equiv.swap ⟨i + d, by omega⟩ ⟨i + d + 1, h⟩
    else 1

private theorem moveRight_apply_out {k : ℕ} (i d : ℕ) (hi : i + d < k) {t : Fin k}
    (ht : t.val < i ∨ i + d < t.val) : moveRight i d t = t := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hi' : i + d + 1 < k := by omega
    simp only [moveRight, hi', ↓reduceDIte, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by dsimp; omega)) (Fin.ne_of_val_ne (by dsimp; omega))]
    exact ih (by omega) (by omega)

private theorem moveRight_apply_end {k : ℕ} (i d : ℕ) (hi : i + d < k) :
    moveRight i d ⟨i + d, hi⟩ = ⟨i, by omega⟩ := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hi' : i + d + 1 < k := by omega
    rw [show (⟨i + (d + 1), hi⟩ : Fin k) = ⟨i + d + 1, hi'⟩ by ext; dsimp; omega]
    simp only [moveRight, hi', ↓reduceDIte, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    exact ih (by omega)

private theorem moveRight_apply_mid {k : ℕ} (i d : ℕ) (hi : i + d < k) {t : ℕ}
    (ht0 : t + 1 < k) (ht1 : i ≤ t) (ht2 : t < i + d) :
    moveRight i d ⟨t, by omega⟩ = ⟨t + 1, ht0⟩ := by
  induction d with
  | zero => omega
  | succ d ih =>
    have hi' : i + d + 1 < k := by omega
    simp only [moveRight, hi', ↓reduceDIte, Equiv.Perm.mul_apply]
    by_cases htd : t = i + d
    · subst htd; rw [Equiv.swap_apply_left]
      exact moveRight_apply_out i d (by omega) (Or.inr (by dsimp; omega))
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by dsimp; omega)) (Fin.ne_of_val_ne (by dsimp; omega))]
      exact ih (by omega) (by omega)

private theorem amplitude_moveRight {n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (σ : Equiv.Perm (Fin (n + 1))) (i d : ℕ) (hi0 : i < n + 1)
    (hσi : σ ⟨i, hi0⟩ = l) (hi : i + d < n + 1) :
    amplitude (anisotropy c) p (σ * moveRight i d) *
        (∏ t ∈ Finset.range d, if h : i + 1 + t < n + 1 then M c (z (p (σ ⟨i + 1 + t, h⟩))) else 1) =
      amplitude (anisotropy c) p σ *
        (∏ t ∈ Finset.range d, if h : i + 1 + t < n + 1 then L c (z (p (σ ⟨i + 1 + t, h⟩))) else 1) := by
  let fm (t : ℕ) : ℂ := if h : i + 1 + t < n + 1 then M c (z (p (σ ⟨i + 1 + t, h⟩))) else 1
  let fl (t : ℕ) : ℂ := if h : i + 1 + t < n + 1 then L c (z (p (σ ⟨i + 1 + t, h⟩))) else 1
  change amplitude (anisotropy c) p (σ * moveRight i d) * (∏ t ∈ Finset.range d, fm t) =
    amplitude (anisotropy c) p σ * (∏ t ∈ Finset.range d, fl t)
  revert hi
  induction d with
  | zero => intro _; simp [moveRight]
  | succ d ih =>
    intro hi
    have hi' : i + d + 1 < n + 1 := by omega
    let σ' := σ * moveRight i d
    let a : Fin (n + 1) := ⟨i + d, by omega⟩
    let b : Fin (n + 1) := ⟨i + d + 1, hi'⟩
    have hσ'a : σ' a = l := by
      dsimp only [σ', a]; rw [Equiv.Perm.mul_apply, moveRight_apply_end (k := n + 1) i d (by omega), hσi]
    have hσ'b : σ' b = σ b := by
      dsimp only [σ', b]; rw [Equiv.Perm.mul_apply, moveRight_apply_out (k := n + 1) i d (by omega) (Or.inr (by dsimp; omega))]
    have hbne : p (σ b) ≠ 0 := fun h0 => by
      have := congrArg Fin.val (σ.injective (hinj (h0.trans (hpl.symm.trans (congrArg p hσi.symm)))))
      dsimp [b] at this; omega
    have hMne : M c (z (p (σ b))) ≠ 0 := M_ne_zero hc (z_ne_one (hp _) hbne)
    have hswap : amplitude (anisotropy c) p (σ' * Equiv.swap a b) * M c (z (p (σ b))) =
        amplitude (anisotropy c) p σ' * L c (z (p (σ b))) := by
      rw [amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ' (show a.val + 1 = b.val by dsimp [a, b]),
        hσ'a, hσ'b, hpl, exp_I_theta_zero_eq_neg_L_div_M_of_mem hc (hp _) hbne]; field_simp [hMne]
    have hbe : (⟨i + 1 + d, by omega⟩ : Fin (n + 1)) = b := by ext; dsimp [b]; omega
    have hfm_d : fm d = M c (z (p (σ b))) := by dsimp [fm]; rw [dite_eq_left (by omega), hbe]
    have hfl_d : fl d = L c (z (p (σ b))) := by dsimp [fl]; rw [dite_eq_left (by omega), hbe]
    simp only [moveRight, hi', ↓reduceDIte, Finset.prod_range_succ, hfm_d, hfl_d, ← mul_assoc]
    change amplitude (anisotropy c) p (σ' * Equiv.swap a b) * (∏ t ∈ range d, fm t) * M c (z (p (σ b))) =
      amplitude (anisotropy c) p σ * (∏ t ∈ range d, fl t) * L c (z (p (σ b)))
    rw [mul_right_comm, hswap, mul_right_comm, ih (by omega)]

private theorem sum_fiber_mulRight {k : ℕ} (l a b : Fin k) (μ : Equiv.Perm (Fin k)) (hμ : μ b = a)
    (F : Equiv.Perm (Fin k) → ℂ) :
    (∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin k) => τ.symm l = b), F τ) =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin k) => σ.symm l = a), F (σ * μ) := by
  refine (Finset.sum_bij (fun σ _ => σ * μ) (fun σ hσ => ?_) (fun _ _ _ _ h => (Equiv.mulRight μ).injective h)
    (fun τ hτ => ⟨τ * μ⁻¹, ?_, by simp⟩) (fun _ _ => rfl)).symm
  · have h1 : σ a = l := (σ.symm_apply_eq.mp (mem_filter.mp hσ).2).symm
    exact mem_filter.mpr ⟨mem_univ _, (σ * μ).symm_apply_eq.mpr (by simp [hμ, h1])⟩
  · have h1 : τ b = l := (τ.symm_apply_eq.mp (mem_filter.mp hτ).2).symm
    have hinv : μ⁻¹ a = b := Equiv.Perm.inv_eq_iff_eq.mpr hμ.symm
    exact mem_filter.mpr ⟨mem_univ _, (τ * μ⁻¹).symm_apply_eq.mpr (by rw [Equiv.Perm.mul_apply, hinv, h1])⟩

private theorem prod_erase_perm {k : ℕ} (a b : Fin k) (μ : Equiv.Perm (Fin k)) (hμ : μ a = b)
    (f : Fin k → ℂ) :
    (∏ s ∈ (univ : Finset (Fin k)).erase a, f (μ s)) = ∏ t ∈ (univ : Finset (Fin k)).erase b, f t :=
  Finset.prod_bij (fun s _ => μ s)
    (fun s hs => mem_erase.mpr ⟨fun h => (mem_erase.mp hs).1 (μ.injective (h.trans hμ.symm)), mem_univ _⟩)
    (fun _ _ _ _ h => μ.injective h)
    (fun t ht => ⟨μ⁻¹ t, mem_erase.mpr ⟨fun h => (mem_erase.mp ht).1 (by have := congrArg μ h; simpa [hμ] using this), mem_univ _⟩, by simp⟩)
    (fun _ _ => rfl)

private theorem prod_erase2_perm {k : ℕ} (a₁ a₂ b₁ b₂ : Fin k) (μ : Equiv.Perm (Fin k))
    (h₁ : μ a₁ = b₁) (h₂ : μ a₂ = b₂) (f : Fin k → ℂ) :
    (∏ s ∈ ((univ : Finset (Fin k)).erase a₁).erase a₂, f (μ s)) =
      ∏ t ∈ ((univ : Finset (Fin k)).erase b₁).erase b₂, f t :=
  Finset.prod_bij (fun s _ => μ s)
    (fun s hs => mem_erase.mpr ⟨fun h => (mem_erase.mp hs).1 (μ.injective (h.trans h₂.symm)),
      mem_erase.mpr ⟨fun h => (mem_erase.mp (mem_erase.mp hs).2).1 (μ.injective (h.trans h₁.symm)), mem_univ _⟩⟩)
    (fun _ _ _ _ h => μ.injective h)
    (fun t ht => ⟨μ⁻¹ t, mem_erase.mpr ⟨fun h => (mem_erase.mp ht).1 (by have := congrArg μ h; simpa [h₂] using this),
      mem_erase.mpr ⟨fun h => (mem_erase.mp (mem_erase.mp ht).2).1 (by have := congrArg μ h; simpa [h₁] using this), mem_univ _⟩⟩, by simp⟩)
    (fun _ _ => rfl)

private theorem prod_range_shift {m : ℕ} (base d : ℕ) (hbd : base + d < m + 2)
    (S : Finset (Fin (m + 2)))
    (hmem : ∀ u : Fin (m + 2), u ∈ S ↔ base ≤ u.val ∧ u.val < base + d)
    (g : Fin (m + 2) → ℂ) :
    (∏ u ∈ S, g u) = ∏ t ∈ Finset.range d, if h : base + t < m + 2 then g ⟨base + t, h⟩ else 1 :=
  Finset.prod_bij' (fun u _ => u.val - base)
    (fun t ht => ⟨base + t, by have := mem_range.mp ht; omega⟩)
    (fun u hu => by obtain ⟨h1, h2⟩ := (hmem u).mp hu; exact mem_range.mpr (by omega))
    (fun t ht => by have := mem_range.mp ht; exact (hmem _).mpr ⟨by dsimp; omega, by dsimp; omega⟩)
    (fun u hu => by obtain ⟨h1, _⟩ := (hmem u).mp hu; ext; dsimp; omega)
    (fun _ _ => by dsimp; omega)
    (fun u hu => by
      obtain ⟨h1, h2⟩ := (hmem u).mp hu
      rw [dite_eq_left (by omega)]
      exact congrArg g (Fin.ext (by dsimp; omega)).symm)

private theorem sum_stepRes_interior_eq_zero {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (m + 2) → ℤ) (p : Fin (m + 2) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (m + 2)) (hpl : p l = 0) :
    (∑ r : Fin (m + 1), ∑ s ∈ intSlots m,
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = s),
        stepRes (N := N) c x p l r σ) = 0 := by
  let S (r : Fin (m + 1)) (s : Fin (m + 2)) : ℂ :=
    ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = s), stepRes (N := N) c x p l r σ
  let P := (univ ×ˢ univ : Finset (Fin (m + 1) × Fin (m + 1))).filter fun pq => pq.1 < pq.2
  have hpos_sum : (∑ r : Fin (m + 1), ∑ s ∈ (intSlots m).filter (fun s => s.val ≤ r.val), S r s) =
      ∑ pq ∈ P, S pq.2 pq.1.succ := by
    rw [Finset.sum_sigma']
    exact Finset.sum_bij'
      (fun u hu => (⟨u.2.val - 1, by have := (mem_intSlots_val.mp (mem_filter.mp (mem_sigma.mp hu).2).1).2; omega⟩, u.1))
      (fun pq _ => ⟨pq.2, pq.1.succ⟩)
      (fun u hu => by
        obtain ⟨hsI, hle⟩ := mem_filter.mp (mem_sigma.mp hu).2
        have := (mem_intSlots_val.mp hsI).1; have := u.1.isLt
        exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, Fin.lt_def.mpr (by dsimp; omega)⟩)
      (fun pq hpq => by
        have hlt : pq.1.val < pq.2.val := (mem_filter.mp hpq).2; have := pq.2.isLt
        exact mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_intSlots_val.mpr ⟨by simp, by dsimp; omega⟩, by dsimp; omega⟩⟩)
      (fun u hu => by
        have := (mem_intSlots_val.mp (mem_filter.mp (mem_sigma.mp hu).2).1).1
        exact congrArg (Sigma.mk u.1) (Fin.ext (by dsimp; omega)))
      (fun _ _ => by ext <;> simp)
      (fun u hu => by
        have := (mem_intSlots_val.mp (mem_filter.mp (mem_sigma.mp hu).2).1).1
        dsimp; congr 1; ext; dsimp; omega)
  have hneg_sum : (∑ r : Fin (m + 1), ∑ s ∈ (intSlots m).filter (fun s => ¬ s.val ≤ r.val), S r s) =
      ∑ pq ∈ P, S pq.1 pq.2.castSucc := by
    rw [Finset.sum_sigma']
    exact Finset.sum_bij'
      (fun u hu => (u.1, ⟨u.2.val, (mem_intSlots_val.mp (mem_filter.mp (mem_sigma.mp hu).2).1).2⟩))
      (fun pq _ => ⟨pq.1, pq.2.castSucc⟩)
      (fun u hu => by
        have := (mem_filter.mp (mem_sigma.mp hu).2).2
        exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, Fin.lt_def.mpr (by dsimp; omega)⟩)
      (fun pq hpq => by
        have hlt : pq.1.val < pq.2.val := (mem_filter.mp hpq).2; have := pq.2.isLt
        exact mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_intSlots_val.mpr ⟨by dsimp; omega, by dsimp; omega⟩, by dsimp; omega⟩⟩)
      (fun _ _ => by ext <;> rfl) (fun _ _ => by ext <;> rfl) (fun _ _ => rfl)
  have hcancel (pq : Fin (m + 1) × Fin (m + 1)) (hpq : pq ∈ P) :
      S pq.2 pq.1.succ + S pq.1 pq.2.castSucc = 0 := by
    have hlt : pq.1.val < pq.2.val := (mem_filter.mp hpq).2
    have hpq2_lt : pq.2.val < m + 1 := pq.2.isLt
    let i := pq.1.val + 1; let d := pq.2.val - (pq.1.val + 1)
    have hid : i + d = pq.2.val := by dsimp [i, d]; omega
    have hi : i + d < m + 2 := by omega
    let μ := moveRight (k := m + 2) i d
    let sPos : Fin (m + 2) := pq.1.succ; let sNeg : Fin (m + 2) := pq.2.castSucc
    have hsNeg_eq : sNeg = ⟨i + d, hi⟩ := Fin.ext hid.symm
    have hμ_end : μ sNeg = sPos := by rw [hsNeg_eq]; exact moveRight_apply_end i d hi
    change S pq.2 sPos + S pq.1 sNeg = 0
    rw [show S pq.1 sNeg = _ from sum_fiber_mulRight l sPos sNeg μ hμ_end _, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun σ hσ => ?_
    have hσs : σ.symm l = sPos := (mem_filter.mp hσ).2
    have hσP : σ sPos = l := (σ.symm_apply_eq.mp hσs).symm
    have hτs : (σ * μ).symm l = sNeg := (σ * μ).symm_apply_eq.mpr (by simp [hμ_end, hσP])
    have hμ0 : (σ * μ) 0 = σ 0 := by simp [μ, moveRight_apply_out i d hi (t := 0) (Or.inl (by simp [i]))]
    have hμL : (σ * μ) (Fin.last (m + 1)) = σ (Fin.last (m + 1)) := by
      simp [μ, moveRight_apply_out i d hi (Or.inr (by rw [Fin.val_last]; omega))]
    have hph : wordPhase (N := N) x p (σ * μ) (stepWord pq.1.succ.castSucc) =
        wordPhase (N := N) x p σ (stepWord pq.2.succ.castSucc) := by
      unfold wordPhase
      let gPos (u : Fin (m + 2)) := positionPhase (p (σ u))
        (if stepWord pq.2.succ.castSucc u then cyclicPredecessorPositions N x u else x u)
      let gNeg (u : Fin (m + 2)) := positionPhase (p ((σ * μ) u))
        (if stepWord pq.1.succ.castSucc u then cyclicPredecessorPositions N x u else x u)
      change (∏ u, gNeg u) = ∏ u, gPos u
      rw [← Finset.mul_prod_erase univ gNeg (mem_univ sNeg),
        ← Finset.mul_prod_erase univ gPos (mem_univ sPos),
        show gNeg sNeg = 1 by simp [gNeg, hμ_end, hσP, hpl, positionPhase],
        show gPos sPos = 1 by simp [gPos, hσP, hpl, positionPhase], one_mul, one_mul,
        ← prod_erase_perm sNeg sPos μ hμ_end gPos]
      refine Finset.prod_congr rfl fun u hu => ?_
      have hune : u.val ≠ i + d := by rw [hid]; exact Fin.val_ne_of_ne (mem_erase.mp hu).1
      dsimp only [gNeg, gPos]; simp only [Equiv.Perm.mul_apply]
      by_cases h1 : u.val < i
      · rw [moveRight_apply_out i d hi (Or.inl h1),
          show stepWord pq.1.succ.castSucc u = true by simp [stepWord]; dsimp [i] at h1; omega,
          show stepWord pq.2.succ.castSucc u = true by simp [stepWord]; dsimp [i] at h1; omega]
      · by_cases h2 : i + d < u.val
        · rw [moveRight_apply_out i d hi (Or.inr h2),
            show stepWord pq.1.succ.castSucc u = false by simp [stepWord]; omega,
            show stepWord pq.2.succ.castSucc u = false by simp [stepWord]; omega]
        · have hu_lt := u.isLt
          rw [moveRight_apply_mid i d hi (by omega) (by omega) (by omega),
            show stepWord pq.1.succ.castSucc u = false by simp [stepWord]; dsimp [i] at h1; omega,
            show stepWord pq.2.succ.castSucc (⟨u.val + 1, by omega⟩ : Fin (m + 2)) = true by simp [stepWord]; omega,
            ite_eq_right Bool.false_ne_true, ite_eq_left rfl]
          have hsucc : (⟨u.val + 1, by omega⟩ : Fin (m + 2)) = (⟨u.val, by omega⟩ : Fin (m + 1)).succ := rfl
          rw [hsucc, cyclicPredecessorPositions_succ]; rfl
    have hamp_int : amplitude (anisotropy c) p (σ * μ) * (∏ u ∈ (intSlots m).erase sNeg, intFactor c p (σ * μ) pq.1 u) =
        amplitude (anisotropy c) p σ * (∏ u ∈ (intSlots m).erase sPos, intFactor c p σ pq.2 u) := by
      let U_P := (intSlots m).erase sPos; let U_N := (intSlots m).erase sNeg
      have hpart (U : Finset (Fin (m + 2))) (f : Fin (m + 2) → ℂ) :
          (∏ u ∈ U, f u) = (∏ u ∈ U.filter (fun u => u.val < i), f u) *
            ((∏ u ∈ U.filter (fun u => ¬ u.val < i ∧ ¬ pq.2.val < u.val), f u) *
              ∏ u ∈ U.filter (fun u => pq.2.val < u.val), f u) := by
        rw [← Finset.prod_filter_mul_prod_filter_not U (fun u => u.val < i)]; congr 1
        rw [← Finset.prod_filter_mul_prod_filter_not (U.filter (fun u => ¬ u.val < i)) (fun u => pq.2.val < u.val),
          mul_comm, Finset.filter_filter, Finset.filter_filter]
        rw [show U.filter (fun u => ¬ u.val < i ∧ pq.2.val < u.val) = U.filter (fun u => pq.2.val < u.val) by
          ext u; simp only [mem_filter]; exact ⟨fun ⟨hU, _, h2⟩ => ⟨hU, h2⟩, fun ⟨hU, h2⟩ => ⟨hU, by dsimp [i]; omega, h2⟩⟩]
      have hlo_eq : U_P.filter (fun u => u.val < i) = U_N.filter (fun u => u.val < i) := by
        ext u; simp only [U_P, U_N, mem_filter, mem_erase]
        exact ⟨fun ⟨⟨_, huI⟩, h1⟩ => ⟨⟨Fin.ne_of_val_ne (by dsimp [sNeg, i] at h1 ⊢; omega), huI⟩, h1⟩,
          fun ⟨⟨_, huI⟩, h1⟩ => ⟨⟨Fin.ne_of_val_ne (by dsimp [sPos, i] at h1 ⊢; omega), huI⟩, h1⟩⟩
      have hhi_eq : U_P.filter (fun u => pq.2.val < u.val) = U_N.filter (fun u => pq.2.val < u.val) := by
        ext u; simp only [U_P, U_N, mem_filter, mem_erase]
        exact ⟨fun ⟨⟨_, huI⟩, h1⟩ => ⟨⟨Fin.ne_of_val_ne (by dsimp [sNeg] at h1 ⊢; omega), huI⟩, h1⟩,
          fun ⟨⟨_, huI⟩, h1⟩ => ⟨⟨Fin.ne_of_val_ne (by dsimp [sPos] at h1 ⊢; omega), huI⟩, h1⟩⟩
      have hprod_lo : (∏ u ∈ U_N.filter (fun u => u.val < i), intFactor c p (σ * μ) pq.1 u) =
          ∏ u ∈ U_P.filter (fun u => u.val < i), intFactor c p σ pq.2 u := by
        rw [← hlo_eq]; refine Finset.prod_congr rfl fun u hu => ?_
        have h1 := (mem_filter.mp hu).2
        simp only [intFactor, show u.val ≤ pq.1.val by dsimp [i] at h1; omega,
          show u.val ≤ pq.2.val by dsimp [i] at h1; omega, ↓reduceIte, Equiv.Perm.mul_apply]
        rw [moveRight_apply_out i d hi (Or.inl h1)]
      have hprod_hi : (∏ u ∈ U_N.filter (fun u => pq.2.val < u.val), intFactor c p (σ * μ) pq.1 u) =
          ∏ u ∈ U_P.filter (fun u => pq.2.val < u.val), intFactor c p σ pq.2 u := by
        rw [← hhi_eq]; refine Finset.prod_congr rfl fun u hu => ?_
        have h1 := (mem_filter.mp hu).2
        simp only [intFactor, show ¬ u.val ≤ pq.1.val by omega, show ¬ u.val ≤ pq.2.val by omega,
          ↓reduceIte, Equiv.Perm.mul_apply]
        rw [moveRight_apply_out (k := m + 2) i d hi (Or.inr (by omega))]
      have hmidP : (∏ u ∈ U_P.filter (fun u => ¬ u.val < i ∧ ¬ pq.2.val < u.val), intFactor c p σ pq.2 u) =
          ∏ t ∈ Finset.range d, if h : i + 1 + t < m + 2 then L c (z (p (σ ⟨i + 1 + t, h⟩))) else 1 := by
        refine (Finset.prod_congr rfl (g := fun u => L c (z (p (σ u)))) fun u hu => by
          simp only [intFactor, show u.val ≤ pq.2.val by have := (mem_filter.mp hu).2; omega, ↓reduceIte]).trans ?_
        refine prod_range_shift (i + 1) d (by dsimp [i, d] at *; omega) _ (fun u => ?_) _
        have huP : u ∈ U_P ↔ u.val ≠ i ∧ 0 < u.val ∧ u.val < m + 1 := by
          simp only [U_P, mem_erase, mem_intSlots_val]
          exact and_congr_left' ⟨Fin.val_ne_of_ne, fun h => Fin.ne_of_val_ne h⟩
        simp only [mem_filter, huP]; dsimp [i, d] at *; omega
      have hmidN : (∏ u ∈ U_N.filter (fun u => ¬ u.val < i ∧ ¬ pq.2.val < u.val), intFactor c p (σ * μ) pq.1 u) =
          ∏ t ∈ Finset.range d, if h : i + 1 + t < m + 2 then M c (z (p (σ ⟨i + 1 + t, h⟩))) else 1 := by
        rw [prod_range_shift i d hi _ (fun u => by
          have huN : u ∈ U_N ↔ u.val ≠ pq.2.val ∧ 0 < u.val ∧ u.val < m + 1 := by
            simp only [U_N, mem_erase, mem_intSlots_val]
            exact and_congr_left' ⟨Fin.val_ne_of_ne, fun h => Fin.ne_of_val_ne h⟩
          simp only [mem_filter, huN]; dsimp [i, d] at *; omega)]
        refine Finset.prod_congr rfl fun t ht => ?_
        have ht' := mem_range.mp ht
        rw [dite_eq_left (by omega), dite_eq_left (by dsimp [i, d] at *; omega)]
        simp only [intFactor, show ¬ i + t ≤ pq.1.val by dsimp [i]; omega, ↓reduceIte, Equiv.Perm.mul_apply]
        have hm := moveRight_apply_mid (k := m + 2) i d hi (t := i + t) (by dsimp [i, d] at *; omega) (by omega) (by omega)
        exact congrArg (fun v => M c (z (p (σ v)))) (hm.trans (Fin.ext (by dsimp; omega)))
      have ham := amplitude_moveRight hc p hp hinj l hpl σ i d (by omega) hσP hi
      rw [hpart U_N, hpart U_P, hprod_lo, hprod_hi, hmidN, hmidP]
      linear_combination (∏ u ∈ U_P.filter (fun u => u.val < i), intFactor c p σ pq.2 u) *
        (∏ u ∈ U_P.filter (fun u => pq.2.val < u.val), intFactor c p σ pq.2 u) * ham
    have hs1 : stepRes (N := N) c x p l pq.2 σ =
        (c : ℂ) ^ 2 * (defectSlope N (anisotropy c) p l (σ 0) : ℂ) *
          (amplitude (anisotropy c) p σ * ∏ u ∈ (intSlots m).erase sPos, intFactor c p σ pq.2 u) *
          (M c (z (p (σ (Fin.last (m + 1))))) * L c (z (p (σ 0))) - 1) *
          wordPhase (N := N) x p σ (stepWord pq.2.succ.castSucc) := by
      have hs0 : sPos ≠ 0 := Fin.succ_ne_zero _
      have hsL : sPos ≠ Fin.last (m + 1) := Fin.ne_of_val_ne (by dsimp [sPos]; omega)
      unfold stepRes; simp only [hσs, hs0, hsL, show sPos.val ≤ pq.2.val by dsimp [sPos]; omega, ↓reduceIte]; ring
    have hs2 : stepRes (N := N) c x p l pq.1 (σ * μ) =
        -(c : ℂ) ^ 2 * (defectSlope N (anisotropy c) p l (σ 0) : ℂ) *
          (amplitude (anisotropy c) p (σ * μ) * ∏ u ∈ (intSlots m).erase sNeg, intFactor c p (σ * μ) pq.1 u) *
          (M c (z (p (σ (Fin.last (m + 1))))) * L c (z (p (σ 0))) - 1) *
          wordPhase (N := N) x p (σ * μ) (stepWord pq.1.succ.castSucc) := by
      have hs0 : sNeg ≠ 0 := Fin.ne_of_val_ne (by dsimp [sNeg]; omega)
      have hsL : sNeg ≠ Fin.last (m + 1) := (Fin.castSucc_lt_last pq.2).ne
      unfold stepRes; simp only [hτs, hμ0, hμL, hs0, hsL, show ¬ sNeg.val ≤ pq.1.val by dsimp [sNeg]; omega, ↓reduceIte]; ring
    rw [hs1, hs2, hamp_int, hph]; ring
  change (∑ r : Fin (m + 1), ∑ s ∈ intSlots m, S r s) = 0
  simp_rw [(fun r => (Finset.sum_filter_add_sum_filter_not (intSlots m) (fun s => s.val ≤ r.val) (S r)).symm),
    Finset.sum_add_distrib]
  rw [hpos_sum, hneg_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero hcancel

private theorem sum_stepRes_zero_eq {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (m + 2) → ℤ) (p : Fin (m + 2) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (m + 2)) (hpl : p l = 0) (r : Fin (m + 1)) :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = 0),
        stepRes (N := N) c x p l r σ) =
      (c : ℂ) ^ 2 * (defectSlope N (anisotropy c) p l l : ℂ) *
        (∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, M c (z (p j))) *
        ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc),
          amplitude (anisotropy c) p τ * planeWave p τ x := by
  let μ := moveRight (k := m + 2) 0 r.val
  have hrlt : r.val < m + 1 := r.isLt
  have hr : 0 + r.val < m + 2 := by omega
  have hμ_end : μ r.castSucc = 0 := by
    rw [show r.castSucc = ⟨0 + r.val, hr⟩ by ext; simp]; exact moveRight_apply_end 0 r.val hr
  rw [sum_fiber_mulRight l 0 r.castSucc μ hμ_end, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hs0 : σ.symm l = 0 := (mem_filter.mp hσ).2
  have hσ0 : σ 0 = l := (σ.symm_apply_eq.mp hs0).symm
  unfold stepRes; simp only [hs0, ↓reduceIte]
  have hph : wordPhase (N := N) x p σ (stepWord r.succ.castSucc) = planeWave p (σ * μ) x := by
    unfold wordPhase planeWave
    rw [← Finset.mul_prod_erase univ _ (mem_univ (0 : Fin (m + 2))),
      ← Finset.mul_prod_erase univ _ (mem_univ r.castSucc),
      show positionPhase (p (σ 0)) _ = 1 by simp [hσ0, hpl, positionPhase],
      show Complex.exp (I * (p ((σ * μ) r.castSucc) : ℂ) * _) = 1 by simp [hμ_end, hσ0, hpl],
      one_mul, one_mul,
      ← prod_erase_perm 0 r.castSucc μ⁻¹ (Equiv.Perm.inv_eq_iff_eq.mpr hμ_end.symm)]
    refine Finset.prod_congr rfl fun s hs => ?_
    have hspos : 0 < s.val := Nat.pos_of_ne_zero (Fin.val_ne_of_ne (mem_erase.mp hs).1)
    have happ : (σ * μ) (μ⁻¹ s) = σ s := by change σ (μ (μ.symm s)) = σ s; rw [μ.apply_symm_apply]
    rw [happ]; unfold positionPhase
    by_cases hsr : s.val ≤ r.val
    · have hμinv : μ⁻¹ s = ⟨s.val - 1, by omega⟩ := Equiv.Perm.inv_eq_iff_eq.mpr
        ((moveRight_apply_mid (k := m + 2) 0 r.val hr (t := s.val - 1) (by omega) (by omega) (by omega)).trans
          (Fin.ext (by dsimp; omega))).symm
      have hpred : cyclicPredecessorPositions N x s = x ⟨s.val - 1, by omega⟩ := by
        have hsucc : s = (⟨s.val - 1, by omega⟩ : Fin (m + 1)).succ := by ext; dsimp; omega
        conv_lhs => rw [hsucc, cyclicPredecessorPositions_succ]
        rfl
      rw [hμinv, ite_eq_left (by simp [stepWord]; omega), hpred]
    · rw [Equiv.Perm.inv_eq_iff_eq.mpr (moveRight_apply_out 0 r.val hr (Or.inr (by omega))).symm,
        ite_eq_right (by simp [stepWord]; omega)]
  have hprod : amplitude (anisotropy c) p σ * M c (z (p (σ (Fin.last (m + 1))))) *
      (∏ s ∈ intSlots m, intFactor c p σ r s) =
      amplitude (anisotropy c) p (σ * μ) * ∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, M c (z (p j)) := by
    have hsplitB : (∏ s ∈ intSlots m, intFactor c p σ r s) =
        (∏ t ∈ Finset.range r.val, if h : 0 + 1 + t < m + 2 then L c (z (p (σ ⟨0 + 1 + t, h⟩))) else 1) *
          ∏ s ∈ (intSlots m).filter (fun s => ¬ s.val ≤ r.val), M c (z (p (σ s))) := by
      rw [← Finset.prod_filter_mul_prod_filter_not (intSlots m) (fun s => s.val ≤ r.val)]
      congr 1
      · refine (Finset.prod_congr rfl (g := fun s => L c (z (p (σ s)))) fun s hs => by
          simp [intFactor, (mem_filter.mp hs).2]).trans ?_
        exact prod_range_shift (m := m) (0 + 1) r.val (by omega) _ (fun s => by
          simp only [mem_filter, mem_intSlots_val]; omega) _
      · exact Finset.prod_congr rfl fun s hs => by simp [intFactor, (mem_filter.mp hs).2]
    have hallM : (∏ t ∈ Finset.range r.val, if h : 0 + 1 + t < m + 2 then M c (z (p (σ ⟨0 + 1 + t, h⟩))) else 1) *
        (∏ s ∈ (intSlots m).filter (fun s => ¬ s.val ≤ r.val), M c (z (p (σ s)))) *
        M c (z (p (σ (Fin.last (m + 1))))) =
        ∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, M c (z (p j)) := by
      rw [← prod_erase_perm 0 l σ hσ0 (fun j => M c (z (p j))),
        ← Finset.mul_prod_erase ((univ : Finset (Fin (m + 2))).erase 0) _
          (mem_erase.mpr ⟨Fin.last_pos.ne', mem_univ (Fin.last (m + 1))⟩),
        mul_comm (M c (z (p (σ (Fin.last (m + 1)))))),
        show ((univ : Finset (Fin (m + 2))).erase 0).erase (Fin.last (m + 1)) = intSlots m from rfl,
        ← Finset.prod_filter_mul_prod_filter_not (intSlots m) (fun s => s.val ≤ r.val)]
      congr 2; symm
      exact prod_range_shift (m := m) (0 + 1) r.val (by omega) _ (fun s => by
        simp only [mem_filter, mem_intSlots_val]; omega) _
    have ham := amplitude_moveRight hc p hp hinj l hpl σ 0 r.val (by omega) hσ0 hr
    rw [hsplitB, ← hallM]
    linear_combination -(M c (z (p (σ (Fin.last (m + 1))))) *
      ∏ s ∈ (intSlots m).filter (fun s => ¬ s.val ≤ r.val), M c (z (p (σ s)))) * ham
  rw [hph]
  linear_combination (c : ℂ) ^ 2 * (defectSlope N (anisotropy c) p l l : ℂ) * planeWave p (σ * μ) x * hprod

private theorem sum_stepRes_last_eq {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (m + 2) → ℤ) (p : Fin (m + 2) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (m + 2)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p) (r : Fin (m + 1)) :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = Fin.last (m + 1)),
        stepRes (N := N) c x p l r σ) =
      -(c : ℂ) ^ 2 * (∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, M c (z (p j))) *
        ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc),
          (defectSlope N (anisotropy c) p l (τ (Fin.last (m + 1))) : ℂ) *
            amplitude (anisotropy c) p τ * planeWave p τ x := by
  have hrlt : r.val < m + 1 := r.isLt
  let d := m - r.val
  have hrd : r.val + d = m := by dsimp [d]; omega
  have hr : r.val + d < m + 2 := by omega
  let μ := moveRight (k := m + 2) r.val d
  let ν := μ * (finRotate (m + 2)).symm
  have hrot_last : (finRotate (m + 2)).symm (Fin.last (m + 1)) = ⟨m, by omega⟩ :=
    (finRotate (m + 2)).symm_apply_eq.mpr (finRotate_of_lt (n := m + 1) (show m < m + 1 by omega)).symm
  have hrot_zero : (finRotate (m + 2)).symm 0 = Fin.last (m + 1) :=
    (finRotate (m + 2)).symm_apply_eq.mpr (finRotate_last : finRotate (m + 2) (Fin.last (m + 1)) = 0).symm
  have hν_last : ν (Fin.last (m + 1)) = r.castSucc := by
    simp only [ν, Equiv.Perm.mul_apply, hrot_last]
    rw [show (⟨m, by omega⟩ : Fin (m + 2)) = ⟨r.val + d, hr⟩ from Fin.ext hrd.symm]
    exact moveRight_apply_end r.val d hr
  have hν_zero : ν 0 = Fin.last (m + 1) := by
    simp only [ν, Equiv.Perm.mul_apply, hrot_zero]
    exact moveRight_apply_out r.val d hr (Or.inr (by rw [Fin.val_last]; omega))
  rw [sum_fiber_mulRight l r.castSucc (Fin.last (m + 1)) ν hν_last, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  have hτr : τ r.castSucc = l := (τ.symm_apply_eq.mp (mem_filter.mp hτ).2).symm
  let σ := τ * ν; let σ₁ := τ * μ
  have hσσ1 : σ * finRotate (m + 2) = σ₁ := by ext k; simp [σ, σ₁, ν]
  have hsL : σ.symm l = Fin.last (m + 1) := σ.symm_apply_eq.mpr (by simp [σ, hν_last, hτr])
  have hσ0 : σ 0 = τ (Fin.last (m + 1)) := by simp [σ, hν_zero]
  unfold stepRes
  change (if σ.symm l = 0 then _ else if σ.symm l = Fin.last (m + 1) then _ else _) = _
  rw [ite_eq_right (hsL ▸ Fin.last_pos.ne'), ite_eq_left hsL]
  have hrot_int {u : Fin (m + 2)} (hu : u ∈ intSlots m) :
      (finRotate (m + 2)).symm u = ⟨u.val - 1, by have := mem_intSlots_val.mp hu; omega⟩ := by
    obtain ⟨h1, h2⟩ := mem_intSlots_val.mp hu
    exact (finRotate (m + 2)).symm_apply_eq.mpr
      ((finRotate_of_lt (n := m + 1) (show u.val - 1 < m + 1 by omega)).trans (Fin.ext (by dsimp; omega))).symm
  have hph : wordPhase (N := N) x p σ (stepWord r.succ.castSucc) =
      (z (p (σ 0)) ^ N)⁻¹ * planeWave p τ x := by
    unfold wordPhase planeWave
    rw [← Finset.mul_prod_erase univ _ (mem_univ (Fin.last (m + 1))),
      ← Finset.mul_prod_erase univ _ (mem_univ r.castSucc),
      show positionPhase (p (σ (Fin.last (m + 1)))) _ = 1 by
        simp [(σ.symm_apply_eq.mp hsL).symm, hpl, positionPhase],
      show Complex.exp (I * (p (τ r.castSucc) : ℂ) * _) = 1 by simp [hτr, hpl],
      one_mul, one_mul,
      ← Finset.mul_prod_erase ((univ : Finset (Fin (m + 2))).erase (Fin.last (m + 1))) _
        (mem_erase.mpr ⟨Fin.last_pos.ne, mem_univ 0⟩),
      ← Finset.mul_prod_erase ((univ : Finset (Fin (m + 2))).erase r.castSucc) _
        (mem_erase.mpr ⟨(Fin.castSucc_lt_last r).ne', mem_univ (Fin.last (m + 1))⟩)]
    have hz0 : positionPhase (p (σ 0)) (if stepWord r.succ.castSucc 0 then cyclicPredecessorPositions N x 0 else x 0) =
        (z (p (σ 0)) ^ N)⁻¹ * Complex.exp (I * (p (τ (Fin.last (m + 1))) : ℂ) * (x (Fin.last (m + 1)) : ℂ)) := by
      have hzn : (z (p (σ 0)) ^ N)⁻¹ = Complex.exp (-(I * (N : ℂ) * (p (σ 0) : ℂ))) := by
        rw [z, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; ring
      rw [ite_eq_left (by simp [stepWord]), show cyclicPredecessorPositions N x 0 = x (Fin.last (m + 1)) - N by
        unfold cyclicPredecessorPositions; rw [hrot_zero]; simp, positionPhase, hzn, ← hσ0, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hz0, mul_assoc, ← prod_erase2_perm (Fin.last (m + 1)) 0 r.castSucc (Fin.last (m + 1)) ν hν_last hν_zero]
    congr 2
    refine Finset.prod_congr rfl fun s hs => ?_
    have hsI : s ∈ intSlots m := mem_intSlots.mpr ⟨(mem_erase.mp hs).1, (mem_erase.mp (mem_erase.mp hs).2).1⟩
    obtain ⟨hspos, hslt⟩ := mem_intSlots_val.mp hsI
    change positionPhase (p (τ (ν s))) _ = _
    unfold positionPhase
    by_cases hsr : s.val ≤ r.val
    · have hνs : ν s = ⟨s.val - 1, by omega⟩ := by
        simp only [ν, Equiv.Perm.mul_apply, hrot_int hsI]
        exact moveRight_apply_out r.val d hr (Or.inl (by dsimp; omega))
      rw [hνs, ite_eq_left (by simp [stepWord]; omega)]
      unfold cyclicPredecessorPositions
      rw [hrot_int hsI, ite_eq_right (Fin.ne_of_val_ne (by dsimp; omega)), sub_zero]
    · have hνs : ν s = s := by
        simp only [ν, Equiv.Perm.mul_apply, hrot_int hsI]
        exact (moveRight_apply_mid (k := m + 2) r.val d hr (t := s.val - 1) (by omega) (by omega) (by dsimp [d]; omega)).trans
          (Fin.ext (by dsimp; omega))
      rw [hνs, ite_eq_right (by simp [stepWord]; omega)]
  have hamp_rot : amplitude (anisotropy c) p σ * (z (p (σ 0)) ^ N)⁻¹ = amplitude (anisotropy c) p σ₁ := by
    have := amplitude_rotate (anisotropy_lt_neg_one hc) p hBE σ
    rw [hσσ1] at this; rw [this, mul_comm]
  have hprod : amplitude (anisotropy c) p σ₁ * L c (z (p (σ 0))) * (∏ u ∈ intSlots m, intFactor c p σ r u) =
      amplitude (anisotropy c) p τ * ∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, M c (z (p j)) := by
    rw [← prod_L_eq_prod_M_zero (n := m + 1) hc p hp hinj l hpl hBE]
    let mapU (u : Fin (m + 2)) : Fin (m + 2) := if h : u.val ≤ r.val then ⟨u.val - 1, by omega⟩ else u
    have hsplitB : (∏ u ∈ intSlots m, intFactor c p σ r u) =
        (∏ u ∈ (intSlots m).filter (fun u => u.val ≤ r.val), L c (z (p (τ (mapU u))))) *
          ∏ t ∈ Finset.range d, if h : r.val + 1 + t < m + 2 then M c (z (p (τ ⟨r.val + 1 + t, h⟩))) else 1 := by
      rw [← Finset.prod_filter_mul_prod_filter_not (intSlots m) (fun u => u.val ≤ r.val)]
      congr 1
      · refine Finset.prod_congr rfl fun u hu => ?_
        obtain ⟨huI, hle⟩ := mem_filter.mp hu; obtain ⟨h1, _⟩ := mem_intSlots_val.mp huI
        simp only [intFactor, mapU, hle, ↓reduceIte, ↓reduceDIte, σ, ν, Equiv.Perm.mul_apply, hrot_int huI]
        rw [moveRight_apply_out r.val d hr (Or.inl (by dsimp; omega))]
      · rw [prod_range_shift (r.val + 1) d (by dsimp [d]; omega) _ fun u => by
            simp only [mem_filter, mem_intSlots_val]; dsimp [d]; omega]
        refine Finset.prod_congr rfl fun t ht => ?_
        have ht' := mem_range.mp ht
        rw [dite_eq_left (by dsimp [d] at ht'; omega), dite_eq_left (by dsimp [d] at ht'; omega)]
        have huI : (⟨r.val + 1 + t, by dsimp [d] at ht'; omega⟩ : Fin (m + 2)) ∈ intSlots m :=
          mem_intSlots_val.mpr ⟨by dsimp; omega, by dsimp [d] at ht' ⊢; omega⟩
        simp only [intFactor, show ¬ r.val + 1 + t ≤ r.val by omega, ↓reduceIte, σ, ν, Equiv.Perm.mul_apply, hrot_int huI]
        exact congrArg (fun v => M c (z (p (τ v))))
          ((moveRight_apply_mid (k := m + 2) r.val d hr (t := r.val + 1 + t - 1) (by dsimp [d] at ht'; omega) (by omega) (by dsimp [d]; omega)).trans
            (Fin.ext (by dsimp; omega)))
    have hallL : (∏ u ∈ (intSlots m).filter (fun u => u.val ≤ r.val), L c (z (p (τ (mapU u))))) *
        (∏ t ∈ Finset.range d, if h : r.val + 1 + t < m + 2 then L c (z (p (τ ⟨r.val + 1 + t, h⟩))) else 1) *
        L c (z (p (τ (Fin.last (m + 1))))) =
        ∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, L c (z (p j)) := by
      rw [← prod_erase_perm r.castSucc l τ hτr (fun j => L c (z (p j))),
        ← Finset.mul_prod_erase ((univ : Finset (Fin (m + 2))).erase r.castSucc) _
          (mem_erase.mpr ⟨(Fin.castSucc_lt_last r).ne', mem_univ (Fin.last (m + 1))⟩),
        mul_comm (L c (z (p (τ (Fin.last (m + 1))))))]
      congr 1
      have hbij_int : (∏ u ∈ intSlots m, L c (z (p (τ (mapU u))))) =
          ∏ s ∈ ((univ : Finset (Fin (m + 2))).erase r.castSucc).erase (Fin.last (m + 1)), L c (z (p (τ s))) :=
        Finset.prod_bij' (fun u _ => mapU u)
          (fun s _ => if h : s.val < r.val then ⟨s.val + 1, by omega⟩ else s)
          (fun u hu => by
            obtain ⟨h1, h2⟩ := mem_intSlots_val.mp hu
            refine mem_erase.mpr ⟨Fin.ne_of_val_ne ?_, mem_erase.mpr ⟨Fin.ne_of_val_ne ?_, mem_univ _⟩⟩ <;>
              (by_cases h : u.val ≤ r.val <;> simp only [mapU, h, ↓reduceDIte, Fin.val_last, Fin.val_castSucc] <;> dsimp <;> omega))
          (fun s hs => by
            have h1 : s.val ≠ m + 1 := Fin.val_ne_of_ne (mem_erase.mp hs).1
            have h2 : s.val ≠ r.val := Fin.val_ne_of_ne (mem_erase.mp (mem_erase.mp hs).2).1
            have := s.isLt; rw [mem_intSlots_val]
            by_cases h : s.val < r.val
            · rw [dite_eq_left h]; dsimp; omega
            · rw [dite_eq_right h]; omega)
          (fun u hu => by
            obtain ⟨h1, _⟩ := mem_intSlots_val.mp hu
            by_cases h : u.val ≤ r.val
            · simp only [mapU, h, ↓reduceDIte, show u.val - 1 < r.val by omega]; ext; dsimp; omega
            · simp only [mapU, h, ↓reduceDIte, show ¬ u.val < r.val by omega])
          (fun s hs => by
            have h2 : s.val ≠ r.val := Fin.val_ne_of_ne (mem_erase.mp (mem_erase.mp hs).2).1
            by_cases h : s.val < r.val
            · simp only [h, ↓reduceDIte, mapU, show s.val + 1 ≤ r.val by omega]; ext; dsimp
            · simp only [h, ↓reduceDIte, mapU, show ¬ s.val ≤ r.val by omega])
          (fun _ _ => rfl)
      rw [← hbij_int, ← Finset.prod_filter_mul_prod_filter_not (intSlots m) (fun u => u.val ≤ r.val)]
      congr 1; symm
      refine (Finset.prod_congr rfl (g := fun u => L c (z (p (τ u)))) fun u hu => by
        simp [mapU, (mem_filter.mp hu).2]).trans ?_
      exact prod_range_shift (m := m) (r.val + 1) d (by have := r.isLt; dsimp [d]; omega) _ (fun u => by
        simp only [mem_filter, mem_intSlots_val]; dsimp [d]; omega) _
    have ham := amplitude_moveRight hc p hp hinj l hpl τ r.val d (by omega) hτr hr
    rw [hsplitB, hσ0, ← hallL]
    linear_combination (L c (z (p (τ (Fin.last (m + 1))))) *
      ∏ u ∈ (intSlots m).filter (fun u => u.val ≤ r.val), L c (z (p (τ (mapU u))))) * ham
  calc -(c : ℂ) ^ 2 * (defectSlope N (anisotropy c) p l (σ 0) : ℂ) * amplitude (anisotropy c) p σ *
        L c (z (p (σ 0))) * (∏ u ∈ intSlots m, intFactor c p σ r u) * wordPhase (N := N) x p σ (stepWord r.succ.castSucc)
      = -(c : ℂ) ^ 2 * (defectSlope N (anisotropy c) p l (σ 0) : ℂ) *
          (amplitude (anisotropy c) p σ * (z (p (σ 0)) ^ N)⁻¹ * L c (z (p (σ 0))) * ∏ u ∈ intSlots m, intFactor c p σ r u) *
          planeWave p τ x := by rw [hph]; ring
    _ = _ := by rw [hamp_rot, hprod, hσ0]; ring

/-- The limiting fixed-amplitude gap sum agrees with its value at the original
zero-root tuple, by continuity of the gap expression. -/
theorem fixedAmplitudeGapSum_zero_eq_eigenvalueZero {N m : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (m + 2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (m + 1)) - x 0 < (N : ℤ))
    (p : Fin (m + 2) → ℝ) (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∑ σ : Equiv.Perm (Fin (m + 2)),
      amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ) =
      eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := by
  let Δ := anisotropy c
  have hΔ := anisotropy_lt_neg_one hc
  have hp0 : pertP p l 0 = p := by unfold pertP; rw [← hpl, Function.update_eq_self]
  have hp_cont (k : Fin (m + 2)) : Continuous (fun t : ℝ => pertP p l t k) := by
    unfold pertP; by_cases hk : k = l <;> simp [hk] <;> fun_prop
  have hG_cont : Filter.Tendsto (fun t : ℝ => ∑ σ : Equiv.Perm (Fin (m + 2)),
      amplitude Δ (pertP p l t) σ * cyclicGapSum c N x (pertP p l t) σ)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∑ σ, amplitude Δ p σ * cyclicGapSum c N x p σ)) := by
    have hcG : Continuous (fun t : ℝ => ∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude Δ (pertP p l t) σ * cyclicGapSum c N x (pertP p l t) σ) := by
      unfold amplitude scattering cyclicGapSum distinctGapTuples gapTuples gapWeight planeWave z; fun_prop
    have ht := hcG.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    rwa [hp0] at ht
  have hzne : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ∀ k, z (pertP p l t k) ≠ 1 := by
    filter_upwards [eventually_z_ne_one_zero'] with t ht k
    by_cases hkl : k = l
    · subst k; simpa [pertP] using ht
    · simp only [pertP, Function.update_of_ne hkl]
      exact z_ne_one (hp k) fun hk0 => hkl (hinj (hk0.trans hpl.symm))
  let PM : ℂ := ∏ j ∈ (univ : Finset (Fin (m + 2))).erase l, M c (z (p j))
  have hconst_lim : Filter.Tendsto (fun t : ℝ =>
      (∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord 0)) +
        ∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord (Fin.last (m + 2))))
      (𝓝[≠] 0)
      (𝓝 (PM * ∑ τ, amplitude Δ p τ * planeWave p τ x *
        ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ)))) := by
    have heq : (fun t : ℝ =>
        (∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord 0)) +
          ∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord (Fin.last (m + 2)))) =ᶠ[𝓝[≠] 0]
        fun t => PM * ∑ τ, amplitude Δ (pertP p l t) τ * planeWave (pertP p l t) τ x *
          ((2 - (c : ℂ) ^ 2) + ((t : ℂ) * L c (z t)) *
            (((betheDefect N Δ (pertP p l t) (τ (Fin.last (m + 1))))⁻¹ - 1) / (t : ℂ))) := by
      filter_upwards [eventually_z_ne_one_zero', self_mem_nhdsWithin] with t hzt ht0
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
      rw [show stepWord (k := m + 2) 0 = fun _ => false from funext fun _ => by simp [stepWord],
        show stepWord (k := m + 2) (Fin.last (m + 2)) = fun _ => true from funext fun _ => by simp [stepWord],
        sum_wordTerm_false, sum_wordTerm_true_defect (n := m + 1) hc x (pertP p l t), coordinateWave]
      have hpM : (∏ j, M c (z (pertP p l t j))) = M c (z t) * PM := by
        rw [← Finset.mul_prod_erase univ _ (mem_univ l)]; simp only [pertP, Function.update_self]
        exact congrArg _ (Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1])
      have hpL : (∏ j, L c (z (pertP p l t j))) = L c (z t) * PM := by
        rw [← Finset.mul_prod_erase univ _ (mem_univ l)]; simp only [pertP, Function.update_self]; dsimp only [PM]
        rw [← prod_L_eq_prod_M_zero (n := m + 1) hc p hp hinj l hpl hBE]
        exact congrArg _ (Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1])
      rw [hpM, hpL, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set B := (betheDefect N Δ (pertP p l t) (τ (Fin.last (m + 1))))⁻¹
      rw [show ((t : ℂ) * L c (z t)) * ((B - 1) / (t : ℂ)) = L c (z t) * (B - 1) by field_simp [htC]]
      linear_combination PM * amplitude Δ (pertP p l t) τ * planeWave (pertP p l t) τ x * L_add_M c hzt
    refine (tendsto_const_nhds.mul (tendsto_finsetSum univ fun τ _ => ?_)).congr' heq.symm
    have hcA : Continuous (fun t : ℝ => amplitude Δ (pertP p l t) τ * planeWave (pertP p l t) τ x) := by
      unfold amplitude scattering planeWave z; fun_prop
    have hA : Filter.Tendsto (fun t : ℝ => amplitude Δ (pertP p l t) τ * planeWave (pertP p l t) τ x)
        (𝓝[≠] 0) (𝓝 (amplitude Δ p τ * planeWave p τ x)) := by
      have ht := hcA.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
      rwa [hp0] at ht
    have hB := (tendsto_const_nhds (x := 2 - (c : ℂ) ^ 2)).add
      ((tendsto_t_mul_L_zero c).mul (tendsto_inv_defect_sub_one_div_t hΔ p l hpl hBE (τ (Fin.last (m + 1)))))
    rw [show (2 - (c : ℂ) ^ 2) + (I * (c : ℂ) ^ 2) * (-I * (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ)) =
        (2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ) by
      ring_nf; rw [I_sq]; ring] at hB
    exact hA.mul hB
  have hmid_lim : Filter.Tendsto (fun t : ℝ =>
      ∑ r : Fin (m + 1), ∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord r.succ.castSucc))
      (𝓝[≠] 0) (𝓝 (∑ r : Fin (m + 1), ∑ σ, stepRes (N := N) c x p l r σ)) :=
    (tendsto_finsetSum univ fun r _ => tendsto_finsetSum univ fun σ _ =>
      tendsto_defect_wordTerm hc x p l hpl hBE r σ).congr' <| by
        filter_upwards [hzne] with t ht
        exact Finset.sum_congr rfl fun r _ => (sum_stepWord_eq_defect_weighted hc x (pertP p l t) ht r).symm
  have htot_eq : (fun t : ℝ => ∑ σ, amplitude Δ (pertP p l t) σ * cyclicGapSum c N x (pertP p l t) σ) =ᶠ[𝓝[≠] 0]
      fun t => ((∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord 0)) +
          ∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord (Fin.last (m + 2)))) +
        ∑ r : Fin (m + 1), ∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord r.succ.castSucc) := by
    filter_upwards [hzne] with t ht
    calc (∑ σ, amplitude Δ (pertP p l t) σ * cyclicGapSum c N x (pertP p l t) σ)
        = ∑ w : Fin (m + 2) → Bool, ∑ σ, wordTerm (N := N) c x (pertP p l t) σ w := by
          simp_rw [cyclicGapSum_eq_sum_words c x (pertP p l t) _ hx hspan ht, Finset.mul_sum]
          rw [Finset.sum_comm]; simp_rw [← mul_assoc]; rfl
      _ = ∑ k : Fin (m + 3), ∑ σ, wordTerm (N := N) c x (pertP p l t) σ (stepWord k) :=
          sum_wordTerms_eq_stepWords (n := m + 1) hc x (pertP p l t) ht
      _ = _ := by rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ, Fin.castSucc_zero]; ring
  rw [tendsto_nhds_unique hG_cont ((hconst_lim.add hmid_lim).congr' htot_eq.symm)]
  have hpart_σ (r : Fin (m + 1)) : (∑ σ, stepRes (N := N) c x p l r σ) =
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = 0), stepRes (N := N) c x p l r σ) +
      (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = Fin.last (m + 1)), stepRes (N := N) c x p l r σ) +
      ∑ s ∈ intSlots m, ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l = s),
        stepRes (N := N) c x p l r σ := by
    rw [(Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := fun σ : Equiv.Perm (Fin (m + 2)) => σ.symm l)
        (fun _ _ => mem_univ _) (fun σ => stepRes (N := N) c x p l r σ)).symm,
      ← Finset.sum_erase_add univ _ (mem_univ (0 : Fin (m + 2))),
      ← Finset.sum_erase_add ((univ : Finset (Fin (m + 2))).erase 0) _
        (mem_erase.mpr ⟨Fin.last_pos.ne', mem_univ (Fin.last (m + 1))⟩)]
    dsimp only [intSlots]; ring
  simp_rw [hpart_σ, Finset.sum_add_distrib]
  rw [sum_stepRes_interior_eq_zero hc x p hp hinj l hpl, add_zero]
  simp_rw [sum_stepRes_zero_eq hc x p hp hinj l hpl, sum_stepRes_last_eq hc x p hp hinj l hpl hBE, ← Finset.mul_sum]
  have hpart_τ (f : Equiv.Perm (Fin (m + 2)) → ℂ) :
      (∑ τ, f τ) = (∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = Fin.last (m + 1)), f τ) +
        ∑ r : Fin (m + 1), ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc), f τ := by
    rw [(Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l)
      (fun _ _ => mem_univ _) f).symm, Fin.sum_univ_castSucc, add_comm]
  have heig : PM * ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l l : ℂ)) = eigenvalueZero N c p l := by
    unfold eigenvalueZero defectSlope; dsimp only [PM, Δ]; rw [ite_eq_left rfl]
    push_cast
    rw [Finset.sum_congr rfl fun r _ =>
      (((Bethe.analyticAt_theta_left hΔ 0 (p r)).differentiableAt.hasDerivAt).ofReal_comp).deriv.symm]; ring
  unfold coordinateWave
  rw [hpart_τ (fun τ => amplitude Δ p τ * planeWave p τ x *
      ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ))),
    hpart_τ (fun τ => amplitude Δ p τ * planeWave p τ x), ← heig]
  have hlast_fiber : (∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = Fin.last (m + 1)),
      amplitude Δ p τ * planeWave p τ x *
        ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ))) =
      ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l l : ℂ)) *
        ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = Fin.last (m + 1)),
          amplitude Δ p τ * planeWave p τ x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [(τ.symm_apply_eq.mp (mem_filter.mp hτ).2).symm]; ring
  rw [hlast_fiber, mul_add, mul_add]
  have hsum_r : PM * (∑ r : Fin (m + 1), ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc),
      amplitude Δ p τ * planeWave p τ x *
        ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ))) +
      ((c : ℂ) ^ 2 * (defectSlope N Δ p l l : ℂ) * PM *
        ∑ r : Fin (m + 1), ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc),
          amplitude Δ p τ * planeWave p τ x) +
      (-(c : ℂ) ^ 2 * PM *
        ∑ r : Fin (m + 1), ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc),
          (defectSlope N Δ p l (τ (Fin.last (m + 1))) : ℂ) * amplitude Δ p τ * planeWave p τ x) =
      PM * ((2 - (c : ℂ) ^ 2) + (c : ℂ) ^ 2 * (defectSlope N Δ p l l : ℂ)) *
        ∑ r : Fin (m + 1), ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin (m + 2)) => τ.symm l = r.castSucc),
          amplitude Δ p τ * planeWave p τ x := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun τ _ => by ring
  dsimp only [PM, Δ] at hsum_r ⊢
  linear_combination hsum_r

end PottsDiscontinuity.BetheAnsatz
