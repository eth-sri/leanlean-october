module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.GoodPrimeSeries

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private alias initial_boundary_Q_gt_one := GoodPrimeSeries.good_series_Q_gt_one
private alias initial_boundary_Ctk_bound := GoodPrimeSeries.good_series_Ctk_bound
private alias initial_boundary_vartheta_norm := GoodPrimeSeries.good_series_vartheta_norm
private alias initial_boundary_qPower_norm := GoodPrimeSeries.good_series_qPower_norm
private alias initial_boundary_term_bound := GoodPrimeSeries.good_series_term_bound

theorem good_euler_series_summable_initial_boundary (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j : Fin 6) (θ : {θ : ℂ // ‖θ‖ = 1})
    (ξ w z : ℂ) (hξ : 4 ≤ ξ.re) (hw : 4 ≤ w.re) (hz : 2 ≤ z.re) :
    Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 ξ w z‖) := by
  let a := ‖gammaTwo C p‖ * Real.exp ((1/2 - ξ.re) * Real.log (Q p))
  let b := Real.exp ((2 - 3*ξ.re) * Real.log (Q p))
  let c := Real.exp ((1-w.re) * Real.log (Q p))
  let d := Real.exp ((-6*z.re) * Real.log (Q p))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := (Real.exp_pos _).le
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hlog : 0 < Real.log (Q p) := Real.log_pos (initial_boundary_Q_gt_one p)
  have sb : Summable (fun l : ℕ => b^l) := by
    apply summable_geometric_of_lt_one hb
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) hlog
  have sc : Summable (fun k : ℕ => c^k) := by
    apply summable_geometric_of_lt_one hc
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) hlog
  have sd : Summable (fun m : ℕ => d^m) := by
    apply summable_geometric_of_lt_one hd
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) hlog
  have sa : Summable (fun e : Fin 2 => a^e.val) := (hasSum_fintype _).summable
  have scd := sc.mul_of_nonneg sd (fun _ => pow_nonneg hc _) (fun _ => pow_nonneg hd _)
  have sbcd := sb.mul_of_nonneg scd (fun _ => pow_nonneg hb _) (by intro i; exact mul_nonneg (pow_nonneg hc _) (pow_nonneg hd _))
  have sall := sa.mul_of_nonneg sbcd (fun _ => pow_nonneg ha _) (by intro i; exact mul_nonneg (pow_nonneg hb _) (mul_nonneg (pow_nonneg hc _) (pow_nonneg hd _)))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) sall
  simpa only [a, b, c, d, mul_assoc] using
    initial_boundary_term_bound C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 ξ w z

open CanonicalLocalGaussTable CanonicalGaussInversePower

private alias tau_period := GoodPrimeSeries.good_strict_tau_period
private alias shell_six_kzero := GoodPrimeSeries.good_strict_shell_six_kzero
private alias shell_six_kone := GoodPrimeSeries.good_strict_shell_six_kone
private alias shell_one_kzero := GoodPrimeSeries.good_strict_shell_one_kzero
private alias shell_one_kone := GoodPrimeSeries.good_strict_shell_one_kone
private alias shell_odd_zero := GoodPrimeSeries.good_strict_shell_odd_zero
private alias qp_add := GoodPrimeSeries.good_strict_qp_add
private alias qp_nat_mul := GoodPrimeSeries.good_strict_qp_nat_mul
private alias qp_nat := GoodPrimeSeries.good_strict_qp_nat
private alias weight_even := GoodPrimeSeries.good_strict_weight_even
private alias geom_tail := GoodPrimeSeries.good_strict_geom_tail
private alias geom_strict_tail := GoodPrimeSeries.good_strict_geom_strict_tail
private alias even_shell_sum_zero := GoodPrimeSeries.good_strict_even_shell_sum_zero
private alias even_shell_sum_one := GoodPrimeSeries.good_strict_even_shell_sum_one
private alias BQV := GoodPrimeSeries.good_strict_BQV
private alias Htau := GoodPrimeSeries.good_strict_Htau
private alias even_shell_sum_origin := GoodPrimeSeries.good_strict_even_shell_sum_origin
private lemma boundary_norms (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (ξ w z : ℂ) (hξ : 4 ≤ ξ.re) (hw : 4 ≤ w.re) (hz : 2 ≤ z.re) :
    ‖qPower p (-6*z)‖ < 1 ∧ ‖θ.val*qPower p (-w)‖ < 1 ∧
    ‖vartheta C p^6*qPower p (4-6*ξ)*qPower p (-6*z)‖ < 1 := by
  have hQ : 1 < Q p := by
    change 1 < (Ideal.absNorm p.val.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.val
  have hn (s : ℂ) : ‖qPower p s‖ = Real.exp (s.re*Real.log (Q p)) := by
    simp [qPower, Complex.norm_exp]
  have hv : ‖vartheta C p‖ = 1 := Circle.norm_coe _
  have hlog := Real.log_pos hQ
  constructor
  · rw [hn]; apply Real.exp_lt_one_iff.mpr
    apply mul_neg_of_neg_of_pos _ hlog; simp; linarith
  constructor
  · rw [norm_mul, θ.property, one_mul, hn]; apply Real.exp_lt_one_iff.mpr
    apply mul_neg_of_neg_of_pos _ hlog; simp; linarith
  · simp only [norm_mul, norm_pow, hv, one_pow, one_mul, hn, ← Real.exp_add]
    apply Real.exp_lt_one_iff.mpr
    simp; nlinarith
private lemma ib_evaluation (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (θ : {θ : ℂ // ‖θ‖ = 1})
    (hθ : θ.val = chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (ξ w z : ℂ) (hξ : 4 ≤ ξ.re) (hw : 4 ≤ w.re) (hz : 2 ≤ z.re) :
    let V := qPower p (-6*z)
    let W := θ.val*qPower p (-w)
    let D := η p.val.asIdeal*star θ.val*qPower p (-ξ)
    let E := vartheta C p^6*qPower p (4-6*ξ)*V
    f C p 0 θ ξ w z = 1/(1-V)+W/(1-W)+
      E/(1-E)*((1-(Q p : ℂ)⁻¹)/(1-V)+W)-
      D/(1-E)*(1+((Q p : ℂ)-1)*W*V/(1-V)) := by
  let V := qPower p (-6*z)
  let W := θ.val*qPower p (-w)
  let D := η p.val.asIdeal*star θ.val*qPower p (-ξ)
  let E := vartheta C p^6*qPower p (4-6*ξ)*V
  let B := vartheta C p^6*qPower p (-2-6*ξ)
  let H := gammaTwo C p*vartheta C p*θ.val⁻¹*qPower p (-1/2-ξ)
  change f C p 0 θ ξ w z = 1/(1-V)+W/(1-W)+
    E/(1-E)*((1-(Q p : ℂ)⁻¹)/(1-V)+W)-D/(1-E)*(1+((Q p : ℂ)-1)*W*V/(1-V))
  obtain ⟨hV,hW,hE⟩ := boundary_norms C p θ ξ w z hξ hw hz
  change ‖V‖ < 1 at hV
  change ‖W‖ < 1 at hW
  change ‖E‖ < 1 at hE
  have hθ6 : θ.val^6=1 := by rw [hθ]; exact chi_unit_sixth p _ hu
  have sall := (good_euler_series_summable_initial_boundary C p 0 θ ξ w z hξ hw hz).of_norm
  let L (e : Fin 2) (l : ℕ) := ∑' i : ℕ × ℕ, seriesTerm C p 0 θ e l i.1 i.2 ξ w z
  have sL (e : Fin 2) : Summable (L e) := (sall.prod_factor e).prod
  have hprod (e : Fin 2) (l : ℕ) : L e l = ∑' k : ℕ, ∑' m : ℕ, seriesTerm C p 0 θ e l k m ξ w z :=
    ((sall.prod_factor e).prod_factor l).tsum_prod
  have hodd (e : Fin 2) (d : ℕ) : L e (2*d+1)=0 := by
    rw [hprod]
    have ht (k m : ℕ) : seriesTerm C p 0 θ e (2*d+1) k m ξ w z = 0 := by
      unfold seriesTerm
      simp only [Fin.val_zero, zero_add, shell_odd_zero C p e d k m, mul_zero, zero_mul]
    simp_rw [ht, tsum_zero]
  have hi : Function.Injective (fun d : ℕ => 2*d) := by intro a b h; dsimp at h; omega
  have heven (e : Fin 2) : (∑' l, L e l) = ∑' d, L e (2*d) := by
    symm; apply hi.tsum_eq
    intro l hl
    change L e l ≠ 0 at hl
    have hmod : l % 2 = 0 := by
      by_contra hn
      have heq : l=2*(l/2)+1 := by omega
      rw [heq, hodd] at hl
      exact hl rfl
    exact ⟨l/2, by dsimp; omega⟩
  have h0 (d : ℕ) (hd : 0 < d) : L 0 (2*d) = E^d*((1-(Q p : ℂ)⁻¹)/(1-V)+W) := by
    rw [hprod]
    simp_rw [weight_even C p θ hθ6]
    simp only [Fin.val_zero, pow_zero, one_mul, zero_add]
    rw [even_shell_sum_zero C p B W V hV d hd]
    rw [show B*(Q p : ℂ)^6*V = E from BQV C p ξ z]
  have h00 : L 0 0 = 1/(1-V)+W/(1-W) := by
    rw [show (0 : ℕ) = 2*0 by omega, hprod]
    simp_rw [weight_even C p θ hθ6]
    simp only [Fin.val_zero, pow_zero, one_mul, mul_zero, zero_add]
    exact even_shell_sum_origin C p W V hW hV
  have h1 (d : ℕ) : L 1 (2*d) = -D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V)) := by
    rw [hprod]
    simp_rw [weight_even C p θ hθ6]
    simp only [Fin.val_one, pow_one]
    simp only [show 1+6*d=6*d+1 by omega]
    rw [even_shell_sum_one C p H B W V hV d]
    rw [show B*(Q p : ℂ)^6*V = E from BQV C p ξ z,
      show H*tau C p 1 = -D from Htau C p θ ξ]
  have s0 : Summable (fun d : ℕ => L 0 (2*d)) := (sL 0).comp_injective hi
  unfold f
  rw [sall.tsum_prod, tsum_fintype, Fin.sum_univ_two]
  rw [(sall.prod_factor 0).tsum_prod, (sall.prod_factor 1).tsum_prod]
  change (∑' l, L 0 l)+(∑' l, L 1 l)=_
  rw [heven 0, heven 1, s0.tsum_eq_zero_add, h00]
  have h0' (d : ℕ) := h0 (d+1) (by omega)
  simp_rw [h0', h1]
  have sE := summable_geometric_of_norm_lt_one hE
  have sEp : Summable (fun d : ℕ => E^(d+1)) := by simpa only [pow_succ] using sE.mul_right E
  have sg := (sE.mul_left D).mul_right (1+((Q p : ℂ)-1)*W*V/(1-V))
  have sp := sEp.mul_right ((1-(Q p : ℂ)⁻¹)/(1-V)+W)
  have hg : (∑' d : ℕ, -D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V))) =
      -(∑' d : ℕ, D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V))) := by
    simp only [neg_mul, tsum_neg]
  rw [hg]
  rw [show (1/(1-V)+W/(1-W)+(∑' d : ℕ, E^(d+1)*((1-(Q p : ℂ)⁻¹)/(1-V)+W)))+
      -(∑' d : ℕ, D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V))) =
      1/(1-V)+W/(1-W)+((∑' d : ℕ, E^(d+1)*((1-(Q p : ℂ)⁻¹)/(1-V)+W))-
        (∑' d : ℕ, D*E^d*(1+((Q p : ℂ)-1)*W*V/(1-V)))) by ring]
  rw [← sp.tsum_sub sg, good_euler_geometric_shell_sum V W D E (Q p : ℂ) hE]
  ring

theorem good_euler_series_initial_boundary (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (u : A.R)
    (hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (θ : {θ : ℂ // ‖θ‖ = 1})
    (hθ : θ.val = chi (σ := σ) p
      (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) u))
    (ξ w z : ℂ) (hξ : 4 ≤ ξ.re) (hw : 4 ≤ w.re) (hz : 2 ≤ z.re) :
    let V := qPower p (-6 * z)
    let W := θ.val * qPower p (-w)
    let D := η p.val.asIdeal * star θ.val * qPower p (-ξ)
    let E := vartheta C p ^ 6 * qPower p (4 - 6 * ξ) * V
    f C p 0 θ ξ w z =
      1 / (1 - V) + W / (1 - W) +
        E / (1 - E) * ((1 - (Q p : ℂ)⁻¹) / (1 - V) + W) -
        D / (1 - E) * (1 + ((Q p : ℂ) - 1) * W * V / (1 - V)) := by
  dsimp only
  exact ib_evaluation C p u hu θ hθ ξ w z hξ hw hz

end DedekindZetaZeroFree.LocalFiniteSums

end
