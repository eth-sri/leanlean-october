module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure

@[expose] public section

namespace OAI



open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialProfileBounds
open InverseInitialProfile InverseMoment FourierBridge

section
variable (W : ℝ→ℂ) (B : ℝ) (hW : ∀x,‖W x‖≤B) (a b c cmax θ x : ℝ) (ha : 0<a) (hc : 1≤c)

theorem clipped_norm   :‖clippedSource W c θ x‖=‖W (c*x)‖:=by
  simp only [clippedSource,norm_mul,logPhase_norm,one_mul]

include hW in
theorem clipped_bound     :
    ‖clippedSource W c θ x‖≤B:=by rw [clipped_norm];exact hW _

include ha hc in
theorem clipped_support     (hcm:c≤cmax)
    (hW:Function.support W⊆Set.Icc a b):
    Function.support (clippedSource W c θ)⊆Set.Icc (a/cmax) b:=by
  intro x hx
  have hn:W (c*x)≠0:=(mul_ne_zero_iff.mp hx).2
  have hs:=hW hn
  have hcp:0<c:=zero_lt_one.trans_le hc
  have hxpos:0<x:=pos_of_mul_pos_right (ha.trans_le hs.1) hcp.le
  constructor
  · apply (div_le_iff₀ (hcp.trans_le hcm)).mpr
    exact hs.1.trans (by nlinarith)
  · have hxc:x≤c*x:=le_mul_of_one_le_left hxpos.le hc
    exact hxc.trans hs.2

include ha hc in
theorem clipped_support_upper     
    (hW:Function.support W⊆Set.Icc a b):Function.support (clippedSource W c θ)⊆Set.Iic b:=
  fun _ hx=>(clipped_support W a b c c θ ha hc le_rfl hW hx).2

theorem childLogTest_eq_clipped   :childLogTest W θ=clippedSource W 1 θ:=by
  grind [childLogTest, clippedSource]

end

end SevenEighths.InverseInitialProfileBounds



end OAI
