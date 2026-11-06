module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneous

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

def denominator (x : ℝ)  := 3-17*x/9

def primeWeight (x : ℝ)  := (2-8*x/9)*(1-x)

def crossing (x t : ℝ)  := ((2-8*x/9)*t-5*x/9)/denominator x

def inverseExponent (δ x r : ℝ)  := 1-δ*(x+(1-x)*r)

def plainExponent (δ x t r : ℝ)  := 1-δ*(4*x/9+(2-8*x/9)*(t-r))

def shortExponent (δ x t : ℝ)  := 1-δ+δ*primeWeight x/denominator x*(3/2-t)

def longExponent (δ t : ℝ)  := 1-δ+(5/6-δ)*(t-1)

section
variable {δ x t r q m Δ γ κ ν : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2)

lemma denominator_lower   (hx : x≤1/2) : 37/18≤denominator x := by
  unfold denominator
  linarith

theorem crossing_bounds   (hx : 0≤x) (hx' : x≤1/2)
    (ht : 1≤t) (ht' : t≤3/2) :
    23/37≤crossing x t ∧ crossing x t≤1 ∧
      1/3≤t-crossing x t ∧ t-crossing x t≤1/2 := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤2-8*x/9 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0≤1-x := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t-crossing x t=((1-x)*t+5*x/9)/denominator x := by
    grind [crossing, denominator]
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

lemma inverse_at_crossing  δ x t  (hd : denominator x≠0) :
    inverseExponent δ x (crossing x t)=shortExponent δ x t := by
  unfold inverseExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma plain_at_crossing  δ x t  (hd : denominator x≠0) :
    plainExponent δ x t (crossing x t)=shortExponent δ x t := by
  unfold plainExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

include hδ _hx hx' in
theorem selected_short_bound         :
    (r≤crossing x t → plainExponent δ x t r≤shortExponent δ x t) ∧
      (crossing x t≤r → inverseExponent δ x r≤shortExponent δ x t) := by
  have hd : denominator x≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hx'))
  constructor
  · intro hr
    rw [←plain_at_crossing δ x t hd]
    unfold plainExponent
    bound
  · intro hr
    rw [←inverse_at_crossing δ x t hd]
    unfold inverseExponent
    bound

include hδ _hx hx' in
lemma short_ge_base        
    (ht : t≤3/2) : 1-δ≤shortExponent δ x t := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤primeWeight x := mul_nonneg (by linarith) (by linarith)
  unfold shortExponent
  exact (by bound)

theorem capacity_loss   (_hq : 0≤q) (hq' : q≤1/2)
    (hm : 1/3-γ≤m) (hm' : m≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hγ : 0≤γ) :
    2*q*(1-2*m)*(2/9-1/(9/2+12*Δ))≤Δ/4+2*γ := by
  
  have hden : (16 : ℝ)≤(9/2)*(9/2+12*Δ) := by nlinarith
  have hqmul : q*(1-2*m)≤(1/2)*(1/3+2*γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0≤24*Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔ' (show 0≤24*γ by positivity)
  have he : 2*q*(1-2*m)*(2/9-1/(9/2+12*Δ)) =
      24*q*(1-2*m)*Δ/((9/2)*(9/2+12*Δ)) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ (show 0<(9/2)*(9/2+12*Δ) by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_left hden (show 0≤Δ/4+2*γ by positivity)
  nlinarith

theorem plain_capacity_comparison  {δ x Δ t r m γ} 
    (hδ : 0≤δ) (hδ' : δ≤1) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hm : 1/3-γ≤m) (hm' : m≤1/2)
    (hγ : 0≤γ) (hlength : t-r-γ≤m) :
    1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)≤plainExponent δ x t r+Δ/4+4*γ := by
  have hq : 0≤δ*x := mul_nonneg hδ hx
  have hq' : δ*x≤1/2 := (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss hq hq' hm hm' hΔ hΔ' hγ
  have hc : 0≤δ*(2-8*x/9) := mul_nonneg hδ (by linarith)
  have hc' : δ*(2-8*x/9)≤2 := by
    
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  grind [plainExponent]

include hδ in
lemma inverse_zero_capacity    
    (hcap : (1-r)/2≤ν) : 1-δ*r≤1-δ+2*δ*ν := by
  have hh := mul_le_mul_of_nonneg_left hcap hδ
  nlinarith

include hδ in
lemma plain_zero_capacity     (hκ : 0<κ)
    (hκ' : κ≤1) (hν : 0≤ν) (hcap : (1-2*m)/(6*κ)≤ν) :
    1-2*δ*m≤1-δ+6*δ*ν := by
  have hh := (div_le_iff₀ (show 0<6*κ by positivity)).mp hcap
  have hk := mul_le_mul_of_nonneg_right hκ' hν
  have hm : 1-2*m≤6*ν := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hm hδ
  nlinarith

end

lemma long_count_bound  {δ r t γ}  (hδ : δ≤5/6) (_hγ : 0≤γ)
    (hr : r≤t+γ) :
    1-5/6+(5/6-δ)*r≤longExponent δ t+(5/6-δ)*γ := by
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤5/6-δ by linarith)
  unfold longExponent
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
