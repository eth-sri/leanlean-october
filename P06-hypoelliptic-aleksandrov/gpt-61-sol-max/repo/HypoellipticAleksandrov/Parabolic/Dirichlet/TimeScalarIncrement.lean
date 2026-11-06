module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import PDEFoundation.Sobolev.OneDimensional.Primitive
import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy

open private HypoellipticAleksandrov.Parabolic.Dirichlet.exists_strict_test_collar from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy


/-!
# Reverse-time scalar increment testing

This module converts a continuous scalar increment identity on the literal
reverse-time interval into its compactly supported distributional identity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set








private theorem reverseTime_Ioc_integral_eq_volume_Icc_integral
    {T a b s t : ℝ} {q : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 ) T)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ r in Ioc s t, q r ∂reverseTimeVolume T) = ∫ r in Icc s t, q r := by

  change (∫ r, q r ∂(volume.restrict (Ioo (0 : ℝ) T)).restrict (Ioc s t)) = _
  rw [Measure.restrict_restrict_of_subset (by
      intro r hr
      exact ⟨lt_of_lt_of_le (hK hs).1 (mem_Ioc.mp hr).1.le,
        lt_of_le_of_lt (mem_Ioc.mp hr).2 (hK ht).2⟩), ← integral_Icc_eq_integral_Ioc]

private def intervalPrimitive (a : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in a..t, q r

private theorem intervalPrimitive_eq_setIntegral_Icc
    {a t : ℝ} (hat : a ≤ t) (q : ℝ → ℝ) :
    intervalPrimitive a q t = ∫ r in Icc a t, q r := by
  rw [intervalPrimitive, intervalIntegral.integral_of_le hat,
    ← integral_Icc_eq_integral_Ioc]

variable {a b : ℝ}

private theorem continuousOn_intervalPrimitive
     {q : ℝ → ℝ} (hab : a ≤ b)
    (hq : IntegrableOn q (Icc a b) ) :
    ContinuousOn (intervalPrimitive a q) (Icc a b) := (PDE.continuousOn_intervalPrimitive hab hq)








variable {a b : ℝ}

private theorem intervalPrimitive_scalar_weak_identity_Icc
     {q : ℝ → ℝ}
    (hq : IntegrableOn q (Icc a b) ) {psi : ℝ → ℝ}
    (hpsi : ContDiff ℝ 1 psi) (hsupp : tsupport psi ⊆ Ioo a b) :
    ∫ t in Icc a b, intervalPrimitive a q t * deriv psi t =
      -∫ t in Icc a b, q t * psi t := (PDE.intervalPrimitive_scalar_weak_identity_Icc hq hpsi hsupp)


private theorem integral_mul_deriv_eq_neg_integral_of_increment
     {e q : ℝ → ℝ}
    (hab : a ≤ b) (hq : IntegrableOn q (Icc a b) )
    (he : ContinuousOn e (Icc a b))
    (hinc : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      e t - e s = ∫ r in Icc s t, q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, e t * deriv eta t) =
      -(∫ t in Icc a b, q t * eta t) := by
  let sharedTerm_9c37e021b2 := (∫ t in Icc a b, (intervalPrimitive a q t + e a) * deriv eta t)



  have heFormula : ∀ t ∈ Icc a b, e t = intervalPrimitive a q t + e a := by
    intro t ht
    have h := hinc a t ⟨le_rfl, hab⟩ ht ht.1
    calc
      e t = (∫ r in Icc a t, q r) + e a := by linarith
      _ = intervalPrimitive a q t + e a := by
        rw [intervalPrimitive_eq_setIntegral_Icc ht.1]
  have hleft : (∫ t in Icc a b, e t * deriv eta t) =
      sharedTerm_9c37e021b2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change e t * deriv eta t = _
    rw [heFormula t ht]
  rw [hleft]
  calc
    (sharedTerm_9c37e021b2) =
        ∫ t in Icc a b, intervalPrimitive a q t * deriv eta t + e a * deriv eta t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      ring
    _ = (∫ t in Icc a b, intervalPrimitive a q t * deriv eta t) +
        ∫ t in Icc a b, e a * deriv eta t := by
      rw [integral_add]
      · exact ((continuousOn_intervalPrimitive hab hq).mul
          (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
      · simpa only using ((heta.continuous_deriv (by simp)).integrableOn_Icc).const_mul (e a)
    _ = -(∫ t in Icc a b, q t * eta t) := by
      rw [intervalPrimitive_scalar_weak_identity_Icc hq heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_eq_sub' eta rfl
            (fun t _ => heta.differentiable (by norm_num) t)
            (heta.continuous_deriv (by norm_num)).continuousOn]
        have ha : eta a = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1
        have hb : eta b = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2
        rw [ha, hb]
        ring
      rw [integral_const_mul, htail]
      ring

/-- A reverse-time scalar increment identity yields its compactly supported
distributional testing identity on the literal restricted time measure. -/
theorem integral_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_increment
    (T : ℝ) (hT : 0 < T)
    (q e : ℝ → ℝ)
    (hq : MeasureTheory.Integrable q (reverseTimeVolume T))
    (he : ContinuousOn e (Set.Icc 0 T))
    (hinc : ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
      e t - e s = ∫ r in Set.Ioc s t, q r ∂reverseTimeVolume T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, e t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, q t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.exists_strict_test_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩

  have heIcc  := he.mono (by
    intro t ht
    exact ⟨(hK ht).1.le, (hK ht).2.le⟩)

  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  exact integral_mul_deriv_eq_neg_integral_of_increment hab.le (by
      change Integrable q (volume.restrict (Ioo (0 ) T)) at hq
      simpa only [Measure.restrict_restrict_of_subset hK, IntegrableOn] using
        hq.restrict (s := Icc a b)) heIcc (by
      intro s t hs ht hst
      rw [hinc s t
        ⟨(hK hs).1.le, (hK hs).2.le⟩
        ⟨(hK ht).1.le, (hK ht).2.le⟩ hst]
      exact reverseTime_Ioc_integral_eq_volume_Icc_integral hK hs ht)
    (eta.contDiff.of_le (by norm_num)) heta

end HypoellipticAleksandrov.Parabolic.Dirichlet
