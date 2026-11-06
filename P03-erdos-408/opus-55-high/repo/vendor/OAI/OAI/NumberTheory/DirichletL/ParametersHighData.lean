module

public import OAI.NumberTheory.DirichletL.ParametersCentralBudget

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0<t
  t_delta : t<Δ/4
  t_small : t≤1/100000000
  slots_pos : 0<N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=1/6
  slots_bounds : ∀j,0<ell j ∧ (7/8)*rmin≤ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0<rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε<rmin*t
  e_pos : 0<e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0<cost
  eps_pos : 0<eps
  eps_small : eps≤1
  sigma_pos : 0<sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  count_budget : 159*ε+t+t+7*t≤1/32
  central_budget : (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640
  geometric_budget : sigma+8*e+t/8≤63/800
  principal_budget : sigma+t/8≤17/48000
  window_budget : sigma+e≤(7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma≤7/1200
  high_saving : sigma+t/8+t/8≤t
  height_choice : ∀J : ℝ,0≤J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t

end SevenEighths.Parameters

end

end OAI
