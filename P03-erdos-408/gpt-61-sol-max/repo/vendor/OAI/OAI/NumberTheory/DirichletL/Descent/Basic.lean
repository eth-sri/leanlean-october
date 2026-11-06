module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

def MarkedMargins (m r z c : ℝ)  :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c

def CanonicalMargins (F M Q z c : ℝ)  :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

def decrease (ell A t g theta V : ℝ)  := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ)  :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ)  :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

section
variable {F M Q Q' z c ell A t g theta V j Fc kappa lambda count delta eta : ℝ} (h : CanonicalMargins F M Q z c) {d : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) {tau pi eps : ℝ}

include h hA ht hV hj hgt hQ in
theorem child_margins_sharp  
     
           
     
      :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

include h hA ht hV hj hgt hdelta heta hQ in
theorem child_margins  
     
           
         
      :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

include hA ht hgt in
theorem child_row_decrease  
         
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith

theorem step_energy_exponent  
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

end

def initialF (r z G P delta : ℝ)  := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ)  :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

section
variable {m r z G P delta eta tau Q c₁ c₂ : ℝ} (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂) (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)

include h₁ h₂ hG hP hQ in
theorem initial_margins_sharp  
       
          :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

include h₁ h₂ hG hP hQ in
theorem initial_margins  
       
         
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

end

end SevenEighths.InverseMoment

end OAI
