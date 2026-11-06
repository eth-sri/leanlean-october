module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.PrimitiveTripleGcd
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                         

noncomputable section
namespace TaoTrudgianYang2025

theorem primitive_linear_triple_gcd_fiber_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {a b c : ℤ} {g : ℕ} {V α β : ℝ}
    (hcoeff : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : 0 < c)
    (hg : 0 < g) (hgc : (g:ℤ) ∣ c) (hV : 0 < V) (hαβ : α ≤ β)
    (hgcd : ∀ p ∈ S, Int.gcd p.1 p.2.1 = g)
    (hden : ∀ p ∈ S, V ≤ (p.2.1:ℝ) ∧ (p.2.1:ℝ) ≤ 2*V)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, a*p.1+b*p.2.1+c*p.2.2 = 0)
    (hratio : ∀ p ∈ S, α ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ β) :
    (S.card:ℝ) ≤ 1+4*V^2*(β-α)/((c:ℝ)*g) := by
  classical
  pm_2552 hgz g hg
  pm_4473 hgr g hg
  pm_4473 hcr c hc
  let f : ℤ × ℤ × ℤ → ℤ × ℤ := fun p => (p.1/g,p.2.1/g)
  let W := S.image f
  have hdu : ∀ p ∈ S, (g:ℤ) ∣ p.1 := by
    pm_8252 Int.gcd_dvd_left
  have hdv : ∀ p ∈ S, (g:ℤ) ∣ p.2.1 := by
    pm_8252 Int.gcd_dvd_right
  have huc : ∀ p ∈ S, (((f p).1:ℤ):ℝ) = (p.1:ℝ)/g := by
    pm_7680 hdu
  have hvc : ∀ p ∈ S, (((f p).2:ℤ):ℝ) = (p.2.1:ℝ)/g := by
    pm_7680 hdv
  have hinj : Set.InjOn f S := by
    intro p hp q hq he
    have heu : p.1 = q.1 := by
      have hh := congrArg (fun t : ℤ × ℤ => t.1*(g:ℤ)) he
      pm_6606 hdu
    have hev : p.2.1 = q.2.1 := by
      have hh := congrArg (fun t : ℤ × ℤ => t.2*(g:ℤ)) he
      pm_6606 hdv
    have hew : p.2.2 = q.2.2 := by
      pm_268 hp' hline p hp hq' q hq
      rw [heu,hev] at hp'
      nlinarith
    exact Prod.ext heu (Prod.ext hev hew)
  have hm : 0 < c/(g:ℤ) := Int.ediv_pos_of_pos_of_dvd hc hgz.le hgc
  have hmod := primitive_coefficients_of_modulus_dvd hcoeff (Int.ediv_dvd_of_dvd hgc)
  have hWden : ∀ p ∈ W, V/(g:ℝ) ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ 2*(V/g) := by
    pm_2551
    rw [hvc q hq]
    constructor
    · exact div_le_div_of_nonneg_right (hden q hq).1 hgr.le
    · simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hden q hq).2 hgr.le
  have hWprim : ∀ p ∈ W, Nat.Coprime p.1.natAbs p.2.natAbs := by
    pm_2551
    change Int.gcd (q.1/(g:ℤ)) (q.2.1/(g:ℤ)) = 1
    rw [← hgcd q hq]
    exact Int.gcd_ediv_gcd_ediv_gcd (by rw [hgcd q hq]; exact hg)
  have hWcong : ∀ p ∈ W, (c/(g:ℤ)) ∣ a*p.1+b*p.2 := by
    pm_2551
    have hv : 0 < q.2.1 := by exact_mod_cast hV.trans_le (hden q hq).1
    have hh := primitive_linear_triple_normalized_congruence hv (hprim q hq) (hline q hq)
    simpa only [hgcd q hq,f] using hh
  have hWratio : ∀ p ∈ W, α ≤ (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 ≤ β := by
    pm_2551
    rw [huc q hq,hvc q hq,div_div_div_cancel_right₀ hgr.ne']
    exact hratio q hq
  have hb := primitive_congruence_card_le W hmod hm (div_pos hV hgr) hαβ
    hWden hWprim hWcong hWratio
  have hcard : W.card = S.card := Finset.card_image_of_injOn hinj
  have hmc : ((c/(g:ℤ):ℤ):ℝ) = (c:ℝ)/g := by
    apply (eq_div_iff hgr.ne').mpr
    exact_mod_cast Int.ediv_mul_cancel hgc
  rw [hcard,hmc] at hb
  calc
    (S.card:ℝ) ≤ 1+4*(V/(g:ℝ))^2*(β-α)/((c:ℝ)/g) := hb
    _ = 1+4*V^2*(β-α)/((c:ℝ)*g) := by field_simp

end TaoTrudgianYang2025
