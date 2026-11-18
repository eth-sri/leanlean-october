module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsDerivatives
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsJets
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarReduction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarEquations
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
open Set Filter Asymptotics
open scoped Topology

/-- Multiplication by a real power adds its exponent to an existing remainder bound. -/
theorem rpow_mul_isBigO (f : ℝ → ℝ) (p r : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => z ^ (p + r)) := by
  apply ((isBigO_refl (fun z : ℝ => z ^ p) atTop).mul h).congr' EventuallyEq.rfl _
  filter_upwards [Ioi_mem_atTop 0] with z hz
  exact (Real.rpow_add hz p r).symm

/-- A version with an explicitly identified sum of exponents. -/
theorem rpow_mul_isBigO_of_add_eq (f : ℝ → ℝ) (p r e : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) (he : p + r = e) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => Real.rpow z e) := by
  simp only [Real.rpow_eq_pow, ← he]
  exact rpow_mul_isBigO f p r h

/-- The transformed remainder is a power times the positive integral remainder. -/
theorem UNr_remainder_eq_power (a : NegThird) (N : ℕ) (z : ℝ) (hz : 0 < z) :
    UNr a z - uExpansion a.1 (2 / 3) N z =
      z ^ (1 / 3 : ℝ) *
        (UIr ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩ (4 / 3) z -
          uExpansion (a.1 + 1 / 3) (4 / 3) N z) := by
  rw [mul_sub, uExpansion_transform a N z hz]
  rfl

/-- The first derivative remainder has one additional inverse power. -/
theorem UNr_expansion_deriv (a : NegThird) (N : ℕ) :
    IsBigO atTop (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  let f : ℝ → ℝ := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z
  have h0 : IsBigO atTop f (fun z => z ^ (-c.1 - (N : ℝ))) := by
    simpa using UIr_expansion c (4 / 3) N
  have h1 : IsBigO atTop (deriv f) (fun z => z ^ (-c.1 - (N : ℝ) - 1)) := by
    simpa using UIr_expansion_deriv c (4 / 3) N
  have ha := (rpow_mul_isBigO f (1 / 3 - 1) (-c.1 - (N : ℝ)) h0).const_mul_left (1 / 3 : ℝ)
  have ha' : IsBigO atTop (fun z => (1 / 3 : ℝ) * (z ^ (1 / 3 - 1 : ℝ) * f z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
    apply ha.congr' EventuallyEq.rfl _
    filter_upwards with z
    rw [Real.rpow_eq_pow]
    congr 1
    ring
  have hb' : IsBigO atTop (fun z => z ^ (1 / 3 : ℝ) * deriv f z)
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
    apply (rpow_mul_isBigO (deriv f) (1 / 3) (-c.1 - (N : ℝ) - 1) h1).congr' EventuallyEq.rfl _
    filter_upwards with z
    rw [Real.rpow_eq_pow]
    congr 1
    dsimp only [c]
    ring
  apply (ha'.add hb').congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop 0] with z hz
  have heq : (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact UNr_remainder_eq_power a N w hw
  have hd := ((hasDerivAt_power_mul f (1 / 3) z hz ((hasDerivAt_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt)).congr_of_eventuallyEq heq).deriv
  exact (by convert hd.symm using 1; ring)

/-- The second derivative remainder has two additional inverse powers. -/
theorem UNr_expansion_deriv2 (a : NegThird) (N : ℕ) :
    IsBigO atTop (deriv (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z)))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 2)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  let f : ℝ → ℝ := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z
  have h0 : IsBigO atTop f (fun z => z ^ (-c.1 - (N : ℝ))) := by
    simpa using UIr_expansion c (4 / 3) N
  have h1 : IsBigO atTop (deriv f) (fun z => z ^ (-c.1 - (N : ℝ) - 1)) := by
    simpa using UIr_expansion_deriv c (4 / 3) N
  have h2 : IsBigO atTop (deriv (deriv f)) (fun z => z ^ (-c.1 - (N : ℝ) - 2)) := by
    simpa using UIr_expansion_deriv2 c (4 / 3) N
  have ha := (rpow_mul_isBigO_of_add_eq f (1 / 3 - 2) (-c.1 - (N : ℝ))
    (-a.1 - (N : ℝ) - 2) h0 (by dsimp only [c]; ring)).const_mul_left
      ((1 / 3 : ℝ) * (1 / 3 - 1))
  have hb := (rpow_mul_isBigO_of_add_eq (deriv f) (1 / 3 - 1) (-c.1 - (N : ℝ) - 1)
    (-a.1 - (N : ℝ) - 2) h1 (by dsimp only [c]; ring)).const_mul_left (2 * (1 / 3 : ℝ))
  apply ((ha.add hb).add (rpow_mul_isBigO_of_add_eq (deriv (deriv f)) (1 / 3) (-c.1 - (N : ℝ) - 2) (-a.1 - (N : ℝ) - 2) h2 (by dsimp only [c]; ring))).congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop 0] with z hz
  have heq : (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact UNr_remainder_eq_power a N w hw
  have hf : ∀ w ∈ Ioi 0, HasDerivAt f (deriv f w) w := by
    intro w hw
    exact (hasDerivAt_UIr_remainder c (4 / 3) N w hw).differentiableAt.hasDerivAt
  have hf' := (hasDerivAt_deriv_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt
  have hder := heq.deriv.deriv_eq
  rw [(deriv_deriv_power_mul f (1 / 3) z hz hf hf')] at hder
  exact (by convert hder.symm using 1; ring)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter Asymptotics Set
open scoped Topology ContDiff


/-- Exact rescaling of the positive scalar tail's power. -/
theorem scalar_tail_power (s D p : ℝ) (hs : 0 < s) (hD : 0 < D) :
    Real.rpow (s ^ 3 / D) p = Real.rpow D (-p) * Real.rpow s (3 * p) := by
  simp
  rw [Real.div_rpow (pow_nonneg hs.le _) hD.le,
    ← Real.rpow_natCast s 3, ← Real.rpow_mul hs.le, Real.rpow_neg hD.le]
  norm_num
  ring

/-- Positive cubic rescaling sends the positive scalar ray to positive infinity. -/
theorem tendsto_scalar_tail_argument (D : ℝ) (hD : 0 < D) :
    Tendsto (fun s : ℝ => s ^ 3 / D) atTop atTop := by
  exact (tendsto_pow_atTop (by decide : 3 ≠ 0)).atTop_div_const hD

/-- Pull back a power remainder by the positive cubic change of variable. -/
theorem isBigO_comp_scalar_tail (e : ℝ → ℝ) (p D : ℝ) (hD : 0 < D)
    (he : IsBigO atTop e (fun z => Real.rpow z p)) :
    IsBigO atTop (fun s => e (s ^ 3 / D)) (fun s => Real.rpow s (3 * p)) := by
  obtain ⟨C, hb⟩ := isBigO_iff.mp he
  refine isBigO_iff.mpr ⟨C * Real.rpow D (-p), ?_⟩
  filter_upwards [(tendsto_scalar_tail_argument D hD).eventually hb,
    eventually_gt_atTop 0] with s hs hs0
  rw [scalar_tail_power s D p hs0 hD] at hs
  simp only [Real.rpow_eq_pow] at hs ⊢
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_pos_of_pos hD (-p)).le] at hs
  simpa only [mul_assoc] using hs

/-- The positive piece has the source leading coefficient and cubic-order remainder. -/
theorem Fplus_asymptotic (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atTop
      (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
  have hD : 0 < 9 * Lam := mul_pos (by norm_num) hLam
  obtain ⟨C, hb⟩ := isBigO_iff.mp (Kummer.UNr_expansion gamma.negative 1)
  refine isBigO_iff.mpr ⟨C * Real.rpow (9 * Lam) (1 - gamma.1), ?_⟩
  filter_upwards [((tendsto_scalar_tail_argument (9 * Lam) hD).eventually hb), eventually_gt_atTop 0] with s hs hs0
  have hm : Kummer.uExpansion (-gamma.1) (2 / 3) 1 (s ^ 3 / (9 * Lam)) =
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1) := by
    simp [Kummer.uExpansion, Finset.sum_range_one, Kummer.poch_zero, Nat.factorial_zero, Nat.cast_one, one_div, inv_one, Real.rpow_eq_pow]
    simpa using scalar_tail_power s (9 * Lam) gamma.1 hs0 hD
  have hp : Real.rpow (s ^ 3 / (9 * Lam)) (gamma.1 - 1) =
      Real.rpow (9 * Lam) (1 - gamma.1) * Real.rpow s (3 * gamma.1 - 3) := by
    rw [scalar_tail_power s (9 * Lam) (gamma.1 - 1) hs0 hD]
    rw [show -(gamma.1 - 1) = 1 - gamma.1 by ring,
      show 3 * (gamma.1 - 1) = 3 * gamma.1 - 3 by ring]
  norm_num only [Nat.cast_one] at hs
  simp only [ScalarGamma.negative, neg_neg, hm, hp, norm_mul] at hs
  simp only [Real.rpow_eq_pow] at hs ⊢
  rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hD (1 - gamma.1)).le,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hs0 (3 * gamma.1 - 3)).le] at hs
  simpa only [Fplus, Real.rpow_eq_pow, ScalarGamma.negative,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hs0 (3 * gamma.1 - 3)).le,
    mul_assoc] using hs


private theorem positive_gamma_product_ratio (t u : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 < u) (hu1 : u < 1) :
    Real.Gamma t * Real.Gamma (1 - t) /
      (Real.Gamma u * Real.Gamma (1 - u)) =
        Real.sin (Real.pi * u) / Real.sin (Real.pi * t) := by
  have htpi : Real.pi * t < Real.pi := by nlinarith only [ht1, Real.pi_pos]
  have hupi : Real.pi * u < Real.pi := by nlinarith only [hu1, Real.pi_pos]
  rw [Real.Gamma_mul_Gamma_one_sub, Real.Gamma_mul_Gamma_one_sub]
  field_simp



section

open Filter Asymptotics

/-- The first truncation of the literal M expansion is its leading power. -/
theorem mExpansion_one (a b X : ℝ) : Kummer.mExpansion a b 1 X =
    Real.Gamma b / Real.Gamma (b - a) * Real.rpow X (-a) := by
  simp [Kummer.mExpansion, Finset.sum_range_one, Kummer.poch_zero, Nat.factorial_zero, Nat.cast_one]

/-- The leading powers of the two M terms have the source joint coefficient. -/
theorem scalar_negative_leading (gamma : ScalarGamma) (Lam s : ℝ)
    (hLam : 0 < Lam) (hs : 0 < s) :
    gammaA gamma.1 * Kummer.mExpansion (-gamma.1) (2 / 3) 1 (s ^ 3 / 9) -
      gammaB gamma.1 * s / Real.rpow (9 * Lam) (1 / 3) *
        Kummer.mExpansion (1 / 3 - gamma.1) (4 / 3) 1 (s ^ 3 / 9) =
    Real.rpow 9 (-gamma.1) *
      (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
        Real.rpow s (3 * gamma.1)   := by
  have gammaB_leading_ratio :
      gammaB gamma.1 * Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1) =
      Qgamma gamma.1 := by
    have hgn := Real.Gamma_add_one (neg_ne_zero.mpr gamma.2.1.ne')
    have hgp := Real.Gamma_add_one gamma.2.1.ne'
    have h13 := Real.Gamma_add_one (by norm_num : (1 / 3 : ℝ) ≠ 0)
    have hn13 := Real.Gamma_add_one (by norm_num : (-(1 / 3) : ℝ) ≠ 0)
    have h := positive_gamma_product_ratio (1 / 3) gamma.1
      (by norm_num) (by norm_num) gamma.2.1 (by linarith only [gamma.2.2])
    have hden' : Real.Gamma (1 - gamma.1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith only [gamma.2.2])).ne'
    have hneg : Real.Gamma (-gamma.1) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hgn
      have he : -gamma.1 + 1 = 1 - gamma.1 := by ring
      rw [he] at hgn
      exact hden' hgn
    norm_num at h13 hn13
    rw [show -gamma.1 + 1 = 1 - gamma.1 by ring] at hgn
    rw [show gamma.1 + 1 = 1 + gamma.1 by ring] at hgp
    have he : gammaB gamma.1 * Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1) =
        Real.Gamma (1 / 3) * Real.Gamma (2 / 3) /
          (Real.Gamma gamma.1 * Real.Gamma (1 - gamma.1)) := by
      unfold gammaB
      rw [h13, hgp, hgn, hn13]
      field_simp
    norm_num only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
    rw [he, h, show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
      Real.sin_pi_div_three, Qgamma]
    ring
  have gammaA_leading_ratio :
      gammaA gamma.1 * Real.Gamma (2 / 3) / Real.Gamma (2 / 3 + gamma.1) =
      Pgamma gamma.1 := by
    have hu : 0 < 1 / 3 - gamma.1 := by linarith only [gamma.2.2]
    have hu1 : 1 / 3 - gamma.1 < 1 := by linarith only [gamma.2.1]
    have h := positive_gamma_product_ratio (1 / 3) (1 / 3 - gamma.1)
      (by norm_num) (by norm_num) hu hu1
    norm_num only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
    rw [show 1 - (1 / 3 - gamma.1) = 2 / 3 + gamma.1 by ring] at h
    have hs : Real.sin (Real.pi * (1 / 3 - gamma.1)) /
        Real.sin (Real.pi * (1 / 3)) = Pgamma gamma.1 := by
      rw [show Real.pi * (1 / 3 - gamma.1) = Real.pi / 3 - Real.pi * gamma.1 by ring,
        show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
        Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three, Pgamma]
      field_simp
    rw [← hs, ← h]
    unfold gammaA
    ring
  rw [mExpansion_one, mExpansion_one]
  rw [show (2 / 3 : ℝ) - -gamma.1 = 2 / 3 + gamma.1 by ring,
    show (4 / 3 : ℝ) - (1 / 3 - gamma.1) = 1 + gamma.1 by ring,
    neg_neg, show -(1 / 3 - gamma.1) = gamma.1 - 1 / 3 by ring,
    scalar_tail_power s 9 gamma.1 hs (by norm_num),
    scalar_tail_power s 9 (gamma.1 - 1 / 3) hs (by norm_num)]
  simp only [Real.rpow_eq_pow]
  have hpow : (9 : ℝ) ^ (-(gamma.1 - 1 / 3)) =
      9 ^ (1 / 3 : ℝ) * 9 ^ (-gamma.1) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 9)]
    congr 1
    ring
  have hsprod : s * s ^ (3 * (gamma.1 - 1 / 3)) = s ^ (3 * gamma.1) := by
    rw [mul_comm s, ← Real.rpow_add_one hs.ne']
    congr 1
    ring
  have hroot : (9 * Lam) ^ (1 / 3 : ℝ) = 9 ^ (1 / 3 : ℝ) * Lam ^ (1 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) hLam.le
  rw [hpow, hroot, Real.rpow_neg hLam.le]
  have h9 : (9 : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hL : Lam ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hLam _).ne'
  have he : gammaA gamma.1 *
      (Real.Gamma (2 / 3) / Real.Gamma (2 / 3 + gamma.1)) = Pgamma gamma.1 := by
    simpa only [mul_div_assoc] using gammaA_leading_ratio
  have he' : gammaB gamma.1 *
      (Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1)) = Qgamma gamma.1 := by
    simpa only [mul_div_assoc] using gammaB_leading_ratio
  calc
    _ = (gammaA gamma.1 * (Real.Gamma (2 / 3) / Real.Gamma (2 / 3 + gamma.1))) *
          9 ^ (-gamma.1) * s ^ (3 * gamma.1) -
        (gammaB gamma.1 * (Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1))) *
          9 ^ (-gamma.1) / Lam ^ (1 / 3 : ℝ) *
            (s * s ^ (3 * (gamma.1 - 1 / 3))) := by field_simp
    _ = _ := by rw [he, he', hsprod]; ring

section MExpansion

variable (hm : ∀ (a : ℝ) (b : Kummer.Pos), -1 < a → a < b.1 → ∀ N : ℕ,
  IsBigO atTop (fun X => Kummer.M a b (-X) - Kummer.mExpansion a b.1 N X)
    (fun X => Real.rpow X (-a - (N : ℝ))))

include hm


/-- The full negative-ray remainder has the exact source coefficient and order. -/
theorem Fminus_negative_ray_asymptotic_of_M_expansion (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) :
    IsBigO atTop
      (fun s => Fminus gamma Lam (-s) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow s (3 * gamma.1))
      (fun s => Real.rpow s (3 * gamma.1 - 3))  := by
  have scalar_M_remainders_of_M_expansion :
      IsBigO atTop
      (fun s => Kummer.M (-gamma.1) Kummer.b23 (-(s ^ 3 / 9)) -
        Kummer.mExpansion (-gamma.1) (2 / 3) 1 (s ^ 3 / 9))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) ∧
    IsBigO atTop
      (fun s => s * (Kummer.M (1 / 3 - gamma.1) Kummer.b43 (-(s ^ 3 / 9)) -
        Kummer.mExpansion (1 / 3 - gamma.1) (4 / 3) 1 (s ^ 3 / 9)))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
    have ha1 : -1 < -gamma.1 := by linarith only [gamma.2.2]
    have hb1 : -gamma.1 < Kummer.b23.1 := by
      dsimp only [Kummer.b23]
      linarith only [gamma.2.1]
    have ha2 : -1 < 1 / 3 - gamma.1 := by linarith only [gamma.2.2]
    have hb2 : 1 / 3 - gamma.1 < Kummer.b43.1 := by
      dsimp only [Kummer.b43]
      linarith only [gamma.2.1]
    have hm1 := hm (-gamma.1) Kummer.b23 ha1 hb1 1
    have hm2 := hm (1 / 3 - gamma.1) Kummer.b43 ha2 hb2 1
    simp [Nat.cast_one, Kummer.b23] at hm1
    simp only [Nat.cast_one, Kummer.b43] at hm2
    rw [show -(1 / 3 - gamma.1) - 1 = gamma.1 - 4 / 3 by ring] at hm2
    have h1 := isBigO_comp_scalar_tail _ (gamma.1 - 1) 9 (by norm_num) hm1
    have h2 := isBigO_comp_scalar_tail _ (gamma.1 - 4 / 3) 9 (by norm_num) hm2
    have hi : IsBigO atTop (fun s : ℝ => s) (fun s => Real.rpow s 1) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_one] using (isBigO_refl (fun s : ℝ => s) atTop)
    have hprod := hi.mul h2
    have he : (fun s : ℝ => Real.rpow s 1 * Real.rpow s (3 * (gamma.1 - 4 / 3)))
        =ᶠ[atTop] fun s => Real.rpow s (3 * gamma.1 - 3) := by
      filter_upwards [eventually_gt_atTop 0] with s hs
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hs]
      congr 1
      ring
    constructor
    · convert h1 using 1
      congr 1
      funext s
      congr 1
      ring
    · exact hprod.congr' (EventuallyEq.refl _ _) he
  obtain ⟨h1, h2⟩ := scalar_M_remainders_of_M_expansion
  have h := (h1.const_mul_left (gammaA gamma.1)).sub
    (h2.const_mul_left (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)))
  apply h.congr' _ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [← scalar_negative_leading gamma Lam s hLam hs]
  unfold Fminus
  rw [show (-s) ^ 3 / 9 = -(s ^ 3 / 9) by ring]
  ring

end MExpansion

/-- Matching selects exactly the positive piece's leading coefficient. -/
theorem scalar_matching_trace_coefficient (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    Real.rpow 9 (-gamma.1) *
      (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) =
        Real.rpow (9 * Lam) (-gamma.1) := by
  rw [hmatch]
  simp only [Real.rpow_eq_pow]
  exact (Real.mul_rpow (by norm_num) hLam.le).symm

end


/-- Exact first and second derivatives of a constant linear combination on the positive ray. -/
theorem scalar_linear_combination_derivatives (f g : ℝ → ℝ) (c d s : ℝ)
    (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hg : ContDiffOn ℝ 2 g (Ioi 0)) (hs : 0 < s) :
    deriv (fun t => c * f t + d * g t) s = c * deriv f s + d * deriv g s ∧
    deriv (deriv (fun t => c * f t + d * g t)) s =
      c * deriv (deriv f) s + d * deriv (deriv g) s := by
  have he (t : ℝ) (ht : 0 < t) : HasDerivAt (fun w => c * f w + d * g w)
      (c * deriv f t + d * deriv g t) t := by
    have hdf := (hf.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by norm_num)
    have hdg := (hg.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by norm_num)
    simpa only [Pi.add_def] using (hdf.hasDerivAt.const_mul c).add
      (hdg.hasDerivAt.const_mul d)
  refine ⟨(he s hs).deriv, ?_⟩
  have heq : deriv (fun t => c * f t + d * g t) =ᶠ[𝓝 s]
      fun t => c * deriv f t + d * deriv g t := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (he t ht).deriv
  have hdf := ((hf.contDiffAt (isOpen_Ioi.mem_nhds hs)).derivWithin
    (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hdg := ((hg.contDiffAt (isOpen_Ioi.mem_nhds hs)).derivWithin
    (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hd := (hdf.hasDerivAt.const_mul c).add (hdg.hasDerivAt.const_mul d)
  simp only [Pi.add_def] at hd
  exact (hd.congr_of_eventuallyEq heq).deriv

/-- Differentiating a signed linear prefactor preserves the predicted remainder orders. -/
theorem scalar_linear_remainder_derivatives (f : ℝ → ℝ) (p : ℝ)
    (hf : ContDiffOn ℝ 2 f (Ioi 0))
    (h0 : IsBigO atTop f (fun s => Real.rpow s p))
    (h1 : IsBigO atTop (deriv f) (fun s => Real.rpow s (p - 1)))
    (h2 : IsBigO atTop (deriv (deriv f)) (fun s => Real.rpow s (p - 2))) :
    IsBigO atTop (deriv (fun s => s * f s)) (fun s => Real.rpow s p) ∧
    IsBigO atTop (deriv (deriv (fun s => s * f s)))
      (fun s => Real.rpow s (p - 1)) := by
  have hb1 := Kummer.rpow_mul_isBigO_of_add_eq (deriv f) 1 (p - 1) p
    (by simpa only [Real.rpow_eq_pow] using h1) (by ring)
  have hb2 := Kummer.rpow_mul_isBigO_of_add_eq (deriv (deriv f)) 1 (p - 2) (p - 1)
    (by simpa only [Real.rpow_eq_pow] using h2) (by ring)
  have he (s : ℝ) (hs : 0 < s) : deriv (fun t => t * f t) s = f s + s * deriv f s := by
    have hd := (hf.contDiffAt (isOpen_Ioi.mem_nhds hs)).differentiableAt (by norm_num)
    simpa [Pi.mul_def] using ((hasDerivAt_id s).mul hd.hasDerivAt).deriv
  constructor
  · have hb0 : IsBigO atTop f (fun s => s ^ p) := by
      simpa only [Real.rpow_eq_pow] using h0
    apply (hb0.add hb1).congr' _ (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [he s hs]
    simp only [Real.rpow_one]
  · have hb1' : IsBigO atTop (deriv f) (fun s => s ^ (p - 1)) := by
      simpa only [Real.rpow_eq_pow] using h1
    apply ((hb1'.const_mul_left 2).add hb2).congr' _
      (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hc := hf.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hd := hc.differentiableAt (by norm_num)
    have hd' := (hc.derivWithin (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have heq : deriv (fun t => t * f t) =ᶠ[𝓝 s] fun t => f t + t * deriv f t := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact he t ht
    have hder := hd.hasDerivAt.add ((hasDerivAt_id s).mul hd'.hasDerivAt)
    simp [Pi.add_def, Pi.mul_def] at hder
    rw [(hder.congr_of_eventuallyEq heq).deriv]
    simp only [Real.rpow_one]
    ring

/-- First and second derivative remainder estimates after the cubic substitution. -/
theorem scalarCubic_remainder_derivatives (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hf : ContDiffOn ℝ 2 f (Ioi 0))
    (h1 : IsBigO atTop (deriv f) (fun z => Real.rpow z (p - 1)))
    (h2 : IsBigO atTop (deriv (deriv f)) (fun z => Real.rpow z (p - 2))) :
    IsBigO atTop (deriv (fun s => f (scalarCubic a s)))
      (fun s => Real.rpow s (3 * p - 1)) ∧
    IsBigO atTop (deriv (deriv (fun s => f (scalarCubic a s))))
      (fun s => Real.rpow s (3 * p - 2)) := by
  have hD : 0 < 9 * a := mul_pos (by norm_num) ha
  have hb1 := isBigO_comp_scalar_tail (deriv f) (p - 1) (9 * a) hD h1
  have hb2 := isBigO_comp_scalar_tail (deriv (deriv f)) (p - 2) (9 * a) hD h2
  have hfirst := (Kummer.rpow_mul_isBigO_of_add_eq _ 2 (3 * (p - 1))
    (3 * p - 1) (by simpa only [Real.rpow_eq_pow] using hb1) (by ring)).const_mul_left
      ((3 * a)⁻¹)
  have hsecond := (Kummer.rpow_mul_isBigO_of_add_eq _ 4 (3 * (p - 2))
    (3 * p - 2) (by simpa only [Real.rpow_eq_pow] using hb2) (by ring)).const_mul_left
      ((3 * a)⁻¹ ^ 2)
  have hsecond' := (Kummer.rpow_mul_isBigO_of_add_eq _ 1 (3 * (p - 1))
    (3 * p - 2) (by simpa only [Real.rpow_eq_pow] using hb1) (by ring)).const_mul_left
      (2 / (3 * a))
  constructor
  · apply hfirst.congr' _ (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hz : 0 < scalarCubic a s := div_pos (pow_pos hs _) hD
    have hc := hf.contDiffAt (isOpen_Ioi.mem_nhds hz)
    rw [deriv_comp_scalarCubic f a s (hc.differentiableAt (by norm_num))]
    simp only [Real.rpow_ofNat, scalarCubic]
    ring
  · apply (hsecond.add hsecond').congr' _ (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hz : 0 < scalarCubic a s := div_pos (pow_pos hs _) hD
    rw [deriv2_comp_scalarCubic f a s (hf.contDiffAt (isOpen_Ioi.mem_nhds hz))]
    simp only [Real.rpow_ofNat, Real.rpow_one, scalarCubic]
    ring

/-- The positive scalar remainder has the exact first two differentiated source orders. -/
theorem Fplus_tail_derivatives (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atTop
      (deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop
      (deriv (deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
  let f : ℝ → ℝ := fun z => Kummer.UNr gamma.negative z -
    Kummer.uExpansion (-gamma.1) (2 / 3) 1 z
  have he : ∀ z : ℝ, Kummer.uExpansion (-gamma.1) (2 / 3) 1 z =
      Real.rpow z gamma.1 := by
    intro z
    simp [Kummer.uExpansion, Finset.sum_range_one, Kummer.poch_zero, Nat.factorial_zero, Nat.cast_one, one_div, inv_one, Real.rpow_eq_pow]
  have hf : ContDiffOn ℝ 2 f (Ioi 0) := by
    have hpow : ContDiffOn ℝ 2 (fun z : ℝ => Real.rpow z gamma.1) (Ioi 0) := by
      simp only [Real.rpow_eq_pow]
      exact contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)
    have hu : ContDiffOn ℝ 2 (Kummer.UNr gamma.negative) (Ioi 0) :=
      (Kummer.contDiffOn_UNr gamma.negative).of_le (by norm_num)
    have hfe : f = fun z => Kummer.UNr gamma.negative z - Real.rpow z gamma.1 := by
      funext z
      dsimp only [f]
      rw [he]
    rw [hfe]
    exact hu.sub hpow
  have h1 : IsBigO atTop (deriv f) (fun z => Real.rpow z (gamma.1 - 2)) := by
    simpa [f, ScalarGamma.negative, Nat.cast_one, show gamma.1 - 1 - 1 = gamma.1 - 2 by ring] using
      Kummer.UNr_expansion_deriv gamma.negative 1
  have h2 : IsBigO atTop (deriv (deriv f)) (fun z => Real.rpow z (gamma.1 - 3)) := by
    simpa [f, ScalarGamma.negative, Nat.cast_one, show gamma.1 - 1 - 2 = gamma.1 - 3 by ring] using
      Kummer.UNr_expansion_deriv2 gamma.negative 1
  have hb := scalarCubic_remainder_derivatives f (gamma.1 - 1) Lam hLam hf
    (by simpa only [show gamma.1 - 1 - 1 = gamma.1 - 2 by ring] using h1)
    (by simpa only [show gamma.1 - 1 - 2 = gamma.1 - 3 by ring] using h2)
  have hloc (s : ℝ) (hs : 0 < s) : (fun t => f (scalarCubic Lam t)) =ᶠ[𝓝 s]
      fun t => Fplus gamma Lam t -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    dsimp only [f, scalarCubic, Fplus]
    rw [he, scalar_tail_power t (9 * Lam) gamma.1 ht (mul_pos (by norm_num) hLam)]
  have hloc' : deriv (fun s => f (scalarCubic Lam s)) =ᶠ[atTop]
      deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (hloc s hs).deriv_eq
  have hloc'' : deriv (deriv (fun s => f (scalarCubic Lam s))) =ᶠ[atTop]
      deriv (deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (hloc s hs).deriv.deriv_eq
  constructor
  · convert hb.1.congr' hloc' EventuallyEq.rfl using 1
    funext s
    congr 1
    ring
  · convert hb.2.congr' hloc'' EventuallyEq.rfl using 1
    funext s
    congr 1
    ring



/-- Two simultaneous sign changes preserve the second scalar derivative. -/
theorem scalar_deriv2_comp_neg (f : ℝ → ℝ) (s : ℝ) :
    deriv (deriv (fun t => f (-t))) s = deriv (deriv f) (-s) := by
  have he : deriv (fun t => f (-t)) = -(fun t => deriv f (-t)) := by
    funext t
    simp [deriv_comp_neg]
  rw [he, deriv.neg, deriv_comp_neg, neg_neg]

/-- The actual first-truncation remainder in the negative-ray M formula. -/
def scalarMRemainder (a : ℝ) (b : Kummer.Pos) (z : ℝ) : ℝ :=
  Kummer.M a b (-z) - Kummer.mExpansion a b.1 1 z

/-- The first-truncation remainder is smooth on the positive argument ray. -/
theorem contDiffOn_scalarMRemainder (a : ℝ) (b : Kummer.Pos) :
    ContDiffOn ℝ 2 (scalarMRemainder a b) (Ioi 0) := by
  have hm : ContDiff ℝ 2 (fun z : ℝ => Kummer.M a b (-z)) :=
    (Kummer.analyticOnNhd_M a b).contDiff.comp contDiff_neg
  have he : scalarMRemainder a b = fun z => Kummer.M a b (-z) -
      (Real.Gamma b.1 / Real.Gamma (b.1 - a)) * Real.rpow z (-a) := by
    funext z
    unfold scalarMRemainder
    rw [mExpansion_one]
  rw [he]
  have hp : ContDiffOn ℝ 2 (fun z : ℝ => Real.rpow z (-a)) (Ioi 0) := by
    simp only [Real.rpow_eq_pow]
    exact contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)
  exact hm.contDiffOn.sub (contDiffOn_const.mul hp)

section MJet

variable (hmjet : ∀ (a : ℝ) (b : Kummer.Pos), -1 < a → a < b.1 →
  ∀ N j : ℕ, j ≤ 2 →
    IsBigO atTop (Kummer.jet j (fun X => Kummer.M a b (-X) - Kummer.mExpansion a b.1 N X))
      (fun X => Real.rpow X (-a - (N : ℝ) - (j : ℝ))))

include hmjet



/-- The two differentiated negative-ray scalar remainders, with the full source coefficient. -/
theorem Fminus_negative_ray_tail_derivatives_of_M_jets (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) :
    IsBigO atTop
      (deriv (fun s => Fminus gamma Lam (-s) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop
      (deriv (deriv (fun s => Fminus gamma Lam (-s) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow s (3 * gamma.1))))
      (fun s => Real.rpow s (3 * gamma.1 - 5))   := by
  have scalar_M_tail_derivatives_of_M_jets (a : ℝ) (b : Kummer.Pos) (ha : -1 < a) (hab : a < b.1) :
      IsBigO atTop (fun s => scalarMRemainder a b (scalarCubic 1 s))
      (fun s => Real.rpow s (-3 * a - 3)) ∧
    IsBigO atTop (deriv (fun s => scalarMRemainder a b (scalarCubic 1 s)))
      (fun s => Real.rpow s (-3 * a - 4)) ∧
    IsBigO atTop (deriv (deriv (fun s => scalarMRemainder a b (scalarCubic 1 s))))
      (fun s => Real.rpow s (-3 * a - 5)) := by
    have h0 : IsBigO atTop (scalarMRemainder a b) (fun z => Real.rpow z (-a - 1)) := by
      unfold scalarMRemainder
      simpa [Kummer.jet, Function.iterate_zero_apply, Nat.cast_one, Nat.cast_zero] using hmjet a b ha hab 1 0 (by norm_num)
    have h1 : IsBigO atTop (deriv (scalarMRemainder a b))
        (fun z => Real.rpow z (-a - 1 - 1)) := by
      unfold scalarMRemainder
      simpa only [Kummer.jet, Function.iterate_one, Nat.cast_one] using
        hmjet a b ha hab 1 1 (by norm_num)
    have h2 : IsBigO atTop (deriv (deriv (scalarMRemainder a b)))
        (fun z => Real.rpow z (-a - 1 - 2)) := by
      unfold scalarMRemainder
      simpa only [Kummer.jet, Function.iterate_succ_apply, Function.iterate_zero_apply,
        Nat.cast_one, Nat.cast_ofNat] using hmjet a b ha hab 1 2 (by norm_num)
    have h := scalarCubic_remainder_derivatives (scalarMRemainder a b) (-a - 1) 1
      zero_lt_one (contDiffOn_scalarMRemainder a b) h1 h2
    have hb0 := isBigO_comp_scalar_tail (scalarMRemainder a b) (-a - 1) 9 (by norm_num) h0
    refine ⟨?_, ?_, ?_⟩
    · convert hb0 using 1
      · simp [scalarCubic]
      · funext s
        congr 1
        ring
    · convert h.1 using 1
      funext s
      congr 1
      ring
    · convert h.2 using 1
      funext s
      congr 1
      ring
  have scalar_second_M_tail_derivatives_of_M_jets :
      IsBigO atTop
      (deriv (fun s => s * scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop
      (deriv (deriv (fun s => s *
        scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
    have ha : -1 < 1 / 3 - gamma.1 := by linarith only [gamma.2.2]
    have hab : 1 / 3 - gamma.1 < Kummer.b43.1 := by
      dsimp only [Kummer.b43]
      linarith only [gamma.2.1]
    obtain ⟨h0, h1, h2⟩ := scalar_M_tail_derivatives_of_M_jets
      (1 / 3 - gamma.1) Kummer.b43 ha hab
    have hf : ContDiffOn ℝ 2
        (fun s => scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s))
        (Ioi 0) := by
      apply (contDiffOn_scalarMRemainder _ _).comp
        ((contDiff_scalarCubic 1).of_le (by norm_num)).contDiffOn
      intro s hs
      exact div_pos (pow_pos hs 3) (by norm_num)
    have he0 : -3 * (1 / 3 - gamma.1) - 3 = 3 * gamma.1 - 4 := by ring
    have he1 : -3 * (1 / 3 - gamma.1) - 4 = (3 * gamma.1 - 4) - 1 := by ring
    have he2 : -3 * (1 / 3 - gamma.1) - 5 = (3 * gamma.1 - 4) - 2 := by ring
    rw [he0] at h0
    rw [he1] at h1
    rw [he2] at h2
    have hb := scalar_linear_remainder_derivatives _ (3 * gamma.1 - 4) hf h0 h1 h2
    simpa only [show 3 * gamma.1 - 4 - 1 = 3 * gamma.1 - 5 by ring] using hb
  let f : ℝ → ℝ := fun s => scalarMRemainder (-gamma.1) Kummer.b23 (scalarCubic 1 s)
  let g : ℝ → ℝ := fun s => s *
    scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s)
  let c := gammaA gamma.1
  let d := -(gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3))
  have ha : -1 < -gamma.1 := by linarith only [gamma.2.2]
  have hab : -gamma.1 < Kummer.b23.1 := by
    dsimp only [Kummer.b23]
    linarith only [gamma.2.1]
  have hfirst := scalar_M_tail_derivatives_of_M_jets (-gamma.1) Kummer.b23 ha hab
  have hsecond := scalar_second_M_tail_derivatives_of_M_jets
  have hf : ContDiffOn ℝ 2 f (Ioi 0) := by
    apply (contDiffOn_scalarMRemainder _ _).comp
      ((contDiff_scalarCubic 1).of_le (by norm_num)).contDiffOn
    intro s hs
    exact div_pos (pow_pos hs 3) (by norm_num)
  have hg : ContDiffOn ℝ 2 g (Ioi 0) := by
    apply contDiffOn_id.mul
    apply (contDiffOn_scalarMRemainder _ _).comp
      ((contDiff_scalarCubic 1).of_le (by norm_num)).contDiffOn
    intro s hs
    exact div_pos (pow_pos hs 3) (by norm_num)
  have hf1 : IsBigO atTop (deriv f) (fun s => Real.rpow s (3 * gamma.1 - 4)) := by
    simpa only [f, show -3 * -gamma.1 - 4 = 3 * gamma.1 - 4 by ring] using hfirst.2.1
  have hf2 : IsBigO atTop (deriv (deriv f)) (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
    simpa only [f, show -3 * -gamma.1 - 5 = 3 * gamma.1 - 5 by ring] using hfirst.2.2
  have hg1 := hsecond.1
  have hg2 := hsecond.2
  have hloc (s : ℝ) (hs : 0 < s) : (fun t => c * f t + d * g t) =ᶠ[𝓝 s]
      fun t => Fminus gamma Lam (-t) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow t (3 * gamma.1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    rw [← scalar_negative_leading gamma Lam t hLam ht]
    dsimp only [f, g, c, d, scalarMRemainder, scalarCubic, Fminus]
    simp [Kummer.b23, Kummer.b43]
    rw [show (-t) ^ 3 / 9 = -(t ^ 3 / 9) by ring]
    ring
  constructor
  · apply ((hf1.const_mul_left c).add (hg1.const_mul_left d)).congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [← (scalar_linear_combination_derivatives f g c d s hf hg hs).1]
    exact (hloc s hs).deriv_eq
  · apply ((hf2.const_mul_left c).add (hg2.const_mul_left d)).congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [← (scalar_linear_combination_derivatives f g c d s hf hg hs).2]
    exact (hloc s hs).deriv.deriv_eq

end MJet

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

