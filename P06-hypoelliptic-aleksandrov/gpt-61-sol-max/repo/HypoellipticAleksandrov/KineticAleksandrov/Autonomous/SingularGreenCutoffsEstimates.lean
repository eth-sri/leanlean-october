module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLeibniz
import Mathlib.Tactic

/-! # Pointwise quantitative bounds on the genuine cutoff product error

These lemmas isolate the spatial and velocity derivative scales and require no
coefficient derivatives. They are estimates on cutoffs, not a singular Green function.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous


/-- Bound the three product-error terms from scalar cutoff and barrier bounds. -/
theorem cutoff_error_abs_le (a Lam v chi psi dx dv dvv phi phiv DX DV DVV B0 B1 : ℝ)
    (ha : 0 ≤ a) (haL : a ≤ Lam) (hc : |chi| ≤ 1) (hp : |psi| ≤ 1)
    (hx : |dx| ≤ DX) (hv : |dv| ≤ DV) (hvv : |dvv| ≤ DVV)
    (hb : |phi| ≤ B0) (hbv : |phiv| ≤ B1) :
    |v*dx*psi*phi+a*chi*dvv*phi+2*a*chi*dv*phiv| ≤
      |v| *DX*B0+Lam*DVV*B0+2*Lam*DV*B1 := by
  have hDX := (abs_nonneg dx).trans hx
  have hDV := (abs_nonneg dv).trans hv
  have hDVV := (abs_nonneg dvv).trans hvv


  have hLam := ha.trans haL
  have ha' : |a| ≤ Lam := by rwa [abs_of_nonneg ha]
  have h₁ : |v*dx*psi*phi| ≤ |v| *DX*B0 := by
    simp only [abs_mul]
    calc
      _ ≤ |v| *DX*1*B0 := by gcongr
      _ = _ := by ring
  have h₂ : |a*chi*dvv*phi| ≤ Lam*DVV*B0 := by
    simp only [abs_mul]
    calc
      _ ≤ Lam*1*DVV*B0 := by gcongr
      _ = _ := by ring
  have h₃ : |2*a*chi*dv*phiv| ≤ 2*Lam*DV*B1 := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2*Lam*1*DV*B1 := by gcongr
      _ = _ := by ring
  have hsum := (abs_add_le (v*dx*psi*phi+a*chi*dvv*phi) (2*a*chi*dv*phiv)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  linarith only [hsum, h₁, h₂, h₃]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
