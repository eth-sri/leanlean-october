module

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalCaps

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseMoment
noncomputable section

theorem canonical_reflection_parameters (L c η : ℝ)
    (hL : 0≤L) (hc : 0<c) (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/100000) :
    ∃ ε ρ κ δ π : ℝ,0<ε ∧ 0<ρ ∧ 0<κ ∧ 0<δ ∧
      0≤δ+(7*L+1) ∧ η≤c/1000 ∧ δ+η≤c/1000 ∧ π≤c/1000 ∧
      ε*(L+L+2*(δ+(7*L+1)+η))+η/2≤π ∧ κ+ρ*L≤c/16 := by
  let ε := c/(100000*(L+1))
  let ρ := c/(64*(L+1))
  let κ := c/64
  refine ⟨ε,ρ,κ,η,c/1000,by positivity,by positivity,
    by positivity,hη,by positivity,by linarith,by linarith,le_refl _,?_,?_⟩
  · have hep : 0≤ε := by positivity
    have hed : ε*(L+1)=c/100000 := by dsimp [ε];field_simp
    nlinarith
  · have hrp : 0≤ρ := by positivity
    have hrd : ρ*(L+1)=c/64 := by dsimp [ρ];field_simp
    grind

lemma canonical_reflected_target_positive (F M Q z margin c O : ℝ)
    (h : CanonicalMargins F M Q z margin) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0<c) (hm : c/2≤margin) (hO : O≤M) :
    0<F-3*c/16-O/2 := by
  obtain ⟨hfirst,hsecond⟩ := h
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
