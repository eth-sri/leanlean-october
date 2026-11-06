module

public import Mathlib

/-! # A finite left Riemann estimate from a derivative modulus -/

@[expose] public section

open Set


namespace PottsDiscontinuity.Bethe

theorem fin_sum_consecutive_sub {k : ℕ} (f : Fin (k + 1) → ℝ) :
     ∑ j : Fin k, (f j.succ - f j.castSucc)  = f (Fin.last k) - f 0 := by
  
  
  rw [Finset.sum_sub_distrib]
  linarith only [ Fin.sum_univ_succ f ,  Fin.sum_univ_castSucc f ]

/-- A mesh bound and a Lipschitz derivative give a quantitative left Riemann
estimate, without asymptotic notation. -/
theorem finite_left_riemann_error {k : ℕ} (q : Fin (k + 1) → ℝ)
    (hq : StrictMono q) (f g : ℝ → ℝ) {a b L d : ℝ}
    (hbox : ∀ j, q j ∈ Icc a b) (hL : 0 ≤ L)
    (hmesh : ∀ j : Fin k, q j.succ - q j.castSucc ≤ d)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g x - g y| ≤ L * |x-y|) :
    |(∑ j : Fin k, (q j.succ - q j.castSucc) * g (q j.castSucc)) -
      (f (q (Fin.last k)) - f (q 0))| ≤ L * d * (q (Fin.last k) - q 0) := by
  have hlocal (j : Fin k) :
      |(q j.succ - q j.castSucc) * g (q j.castSucc) -
        (f (q j.succ) - f (q j.castSucc))| ≤
          L * d * (q j.succ - q j.castSucc) := by
    have hlt : q j.castSucc < q j.succ := by
                                            bound
    have hsub : Icc (q j.castSucc) (q j.succ) ⊆ Icc a b :=
      by
        grind
    obtain ⟨ξ, hξ, hm⟩ := exists_hasDerivAt_eq_slope f g hlt
      (fun x hx => (hderiv x (hsub hx)).continuousAt.continuousWithinAt)
       fun x hx => hderiv x (hsub ⟨hx.1.le, hx.2.le⟩) 
    have hξbox := hsub ⟨hξ.1.le, hξ.2.le⟩
    have hl := hLip (q j.castSucc) (hbox _) ξ hξbox
    have hdist : |q j.castSucc - ξ| ≤ q j.succ - q j.castSucc := by
      grind
    have hl'  :=
      hl.trans ((mul_le_mul_of_nonneg_left hdist hL).trans
        (mul_le_mul_of_nonneg_left (hmesh j) hL))
    have hm' : (q j.succ - q j.castSucc) * g ξ =
        f (q j.succ) - f (q j.castSucc) := by
      grind
    rw [← hm', ← mul_sub, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
    calc
      _ ≤ (q j.succ - q j.castSucc) * (L * d) :=
        mul_le_mul_of_nonneg_left hl' (sub_nonneg.mpr hlt.le)
      _ = _ := by ring
  rw [← fin_sum_consecutive_sub  fun j => f (q j) , ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin k, |(q j.succ - q j.castSucc) * g (q j.castSucc) -
        (f (q j.succ) - f (q j.castSucc))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin k, L * d * (q j.succ - q j.castSucc) :=
      Finset.sum_le_sum fun j _ => hlocal j
    _ = _ := by rw [← Finset.mul_sum, fin_sum_consecutive_sub q]

end PottsDiscontinuity.Bethe
