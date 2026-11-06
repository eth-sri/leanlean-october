module
public import OAI.NumberTheory.DirichletL.Moments.PlainWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalKernel

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWindowPair
open CenteredMomentPlainWindowEnergy CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge

theorem paired_integrals {κ:Type*}(rows:Finset κ)(f g:κ→ℝ→ℂ)
    (hf:∀z∈rows,Integrable (f z))(hg:∀z∈rows,Integrable (g z))
    (a b:ℝ→ℝ)(ha:Integrable a)(hb:Integrable b)
    (_ha0:∀u,0≤a u)(_hb0:∀v,0≤b v)(E:ℝ)(_hE:0≤E)
    (hpair:∀u v,∑z∈rows,‖f z u‖*‖g z v‖≤E*a u*b v):
    (∑z∈rows,‖∫u,f z u‖*‖∫v,g z v‖)≤E*(∫u,a u)*(∫v,b v):=by
  have hinner (u:ℝ):
      (∑z∈rows,‖f z u‖*‖∫v,g z v‖)≤E*a u*(∫v,b v):=by
    calc
      _≤∑z∈rows,‖f z u‖*(∫v,‖g z v‖):=
        Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm _) (norm_nonneg _))
      _=∫v,∑z∈rows,‖f z u‖*‖g z v‖:=by
        rw [integral_finsetSum _ (fun z hz=>(hg z hz).norm.const_mul _)]
        simp only [integral_const_mul]
      _≤∫v,E*a u*b v:=integral_mono
        (integrable_finsetSum rows (fun z hz=>(hg z hz).norm.const_mul _))
        (hb.const_mul _) (fun v=>hpair u v)
      _=E*a u*(∫v,b v):=integral_const_mul _ _
  calc
    _≤∑z∈rows,(∫u,‖f z u‖)*‖∫v,g z v‖:=
      Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm _) (norm_nonneg _))
    _=∫u,∑z∈rows,‖f z u‖*‖∫v,g z v‖:=by
      rw [integral_finsetSum _ (fun z hz=>(hf z hz).norm.mul_const _)]
      simp only [integral_mul_const]
    _≤∫u,E*a u*(∫v,b v):=integral_mono
      (integrable_finsetSum rows (fun z hz=>(hf z hz).norm.mul_const _))
      ((ha.const_mul E).mul_const _) hinner
    _=E*(∫u,a u)*(∫v,b v):=by rw [integral_mul_const,integral_const_mul]
