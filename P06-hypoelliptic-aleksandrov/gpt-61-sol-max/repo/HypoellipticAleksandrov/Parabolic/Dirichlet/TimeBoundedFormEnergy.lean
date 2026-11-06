module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarIncrement
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertIntegrationByParts

/-!
# Reverse-time energy testing by a bounded pivot factorization

This module turns a bounded spatial factorization of the scalar `L²` pivot
into the corresponding reverse-time scalar energy testing identity.
-/

 public section

open MeasureTheory Set
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable (hΩ : IsOpen Ω)

private theorem pivot_symmetric_of_factorization


    (A S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hfactor : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y))) :
    ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y) := (fun x y =>
  Trans.trans
    (Trans.trans (Trans.trans (hfactor x y) (real_inner_comm ((valueCLM hΩ) (A y)) ((valueCLM hΩ) (A x))))
      (Eq.symm (hfactor y x)))
    (real_inner_comm ((valueCLM hΩ) (S x)) ((valueCLM hΩ) y)))

variable (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) (Su : ReverseTimeL2V hΩ T)

private theorem ae_pivot_factorization_rate

      (Sg : ReverseTimeL2VStar hΩ T)
    (hSu : Su =ᵐ[reverseTimeVolume T] fun r => S (u r))
    (hSg : Sg =ᵐ[reverseTimeVolume T]
      fun r => h10HilbertGraphDualPrecompose hΩ S (g r)) :
    (fun r => (g r) (Su r) + (Sg r) (u r)) =ᵐ[reverseTimeVolume T]
      fun r => 2 * (g r) (S (u r)) := by
  filter_upwards [hSu, hSg] with r hrSu hrSg
  rw [hrSu, hrSg]
  change (g r) (S (u r)) + (g r) (S (u r)) = 2 * (g r) (S (u r))
  ring

private theorem integrable_pivot_factorization_rate


    (hSu : Su =ᵐ[reverseTimeVolume T] fun r => S (u r)) :
    Integrable (fun r => 2 * (g r) (S (u r))) (reverseTimeVolume T) := by
  refine ((integrable_reverseTimeDualPairing hΩ T
    Su g).const_mul 2).congr ?_
  filter_upwards [hSu] with r hrSu
  rw [hrSu]

variable {T : ℝ} (U V : C(↥(Icc 0 T), PDE.ScalarLp Ω (2 )))

private theorem continuousOn_pivot_factorization_cross_energy
      :
    ContinuousOn
      (fun t => if ht : t ∈ Icc 0 T then
        inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0)
      (Icc 0 T) := by
  letI : InnerProductSpace ℝ (PDE.ScalarLp Ω (2 )) := L2.innerProductSpace
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Icc 0 T).domRestrict (fun t => if ht : t ∈ Icc 0 T then
      inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0) =
      fun t => inner ℝ (U t) (V t) := by
    funext t
    simp only [Set.domRestrict_apply, dif_pos t.2]
  rw [heq]

  exact continuous_inner.comp (U.continuous.prodMk V.continuous)

private theorem pivot_factorization_cross_energy_increment

    (rate q : ℝ → ℝ)
    (hinc : ∀ s t : ℝ, ∀ hs : s ∈ Icc 0 T, ∀ ht : t ∈ Icc 0 T, s ≤ t →
      inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) -
          inner ℝ (U ⟨s, hs⟩) (V ⟨s, hs⟩) =
        ∫ r in Ioc s t, rate r ∂reverseTimeVolume T)
    (hrate : rate =ᵐ[reverseTimeVolume T] q)
    (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (if ht : t ∈ Icc 0 T then
      inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0) -
      (if hs : s ∈ Icc 0 T then
        inner ℝ (U ⟨s, hs⟩) (V ⟨s, hs⟩) else 0) =
      ∫ r in Ioc s t, q r ∂reverseTimeVolume T := by
  rw [dif_pos ht, dif_pos hs]
  exact (hinc s t hs ht hst).trans
    (integral_congr_ae (ae_restrict_of_ae hrate))

private theorem ae_pivot_factorization_cross_energy_eq_norm_sq

    (hΩ : IsOpen Ω) (T : ℝ)
    (A S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hfactor : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y)))
    (u Su : ReverseTimeL2V hΩ T)
    (U V : C(↥(Icc 0 T), PDE.ScalarLp Ω (2 )))
    (hU : ReverseTimeHilbertRepresentativeAgrees hΩ T u U)
    (hV : ReverseTimeHilbertRepresentativeAgrees hΩ T Su V)
    (hSu : Su =ᵐ[reverseTimeVolume T] fun t => S (u t)) :
    (fun t => if ht : t ∈ Icc 0 T then
      inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0) =ᵐ[reverseTimeVolume T]
      fun t => ‖valueCLM hΩ (A (u t))‖ ^ 2 := by

  filter_upwards [(ae_restrict_mem measurableSet_Ioo), hU, hV, hSu] with
    t ht hUagree hVagree hSu

  rw [dif_pos (⟨le_of_lt ht.1, le_of_lt ht.2⟩), hUagree ht, hVagree ht, hSu, hfactor]
  exact real_inner_self_eq_norm_sq _

set_option linter.unusedVariables false in
section
variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (A S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) (hfactor : ∀ x y : H10HilbertGraph hΩ, inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) = inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y))) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hfactor hderiv
/-- A bounded spatial pivot factorization has a continuous closed-time
energy representative for the value norm of its left factor. -/
theorem exists_continuous_value_norm_sq_energy_increment_of_pivot_factorization
     :
    ∃ e : ℝ → ℝ,
      MeasureTheory.Integrable
        (fun r => 2 * (g r) (S (u r))) (reverseTimeVolume T) ∧
      ContinuousOn e (Set.Icc 0 T) ∧
      e =ᵐ[reverseTimeVolume T]
        (fun t => ‖valueCLM hΩ (A (u t))‖ ^ 2) ∧
      ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
        s ≤ t →
          e t - e s =
            ∫ r in Set.Ioc s t,
              2 * (g r) (S (u r)) ∂reverseTimeVolume T := by

  let Su := S.compLpL (2 ) (reverseTimeVolume T) u
  let Sg := (h10HilbertGraphDualPrecompose hΩ S).compLpL
    (2 ) (reverseTimeVolume T) g
  let hSu := hderiv.comp_of_pivot_symmetric S (pivot_symmetric_of_factorization hΩ A S hfactor)
  let U := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let V := reverseTimeHilbertRepresentative hΩ T hT Su Sg hSu

  let e  := fun t => if ht : t ∈ Icc 0 T then
    inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0
  have hSuAgree : Su =ᵐ[reverseTimeVolume T] fun t => S (u t) :=
    ContinuousLinearMap.coeFn_compLpL S u








  have heq  := ae_pivot_factorization_cross_energy_eq_norm_sq hΩ T A S hfactor u Su U V
      ((reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1) ((reverseTimeHilbertRepresentative_spec hΩ T hT Su Sg hSu).1) hSuAgree
  exact ⟨e, (integrable_pivot_factorization_rate hΩ T u g S Su hSuAgree), (continuousOn_pivot_factorization_cross_energy U V), heq, (by
      intro s t hs ht hst
      exact pivot_factorization_cross_energy_increment U V
        (fun r => (g r) (Su r) + (Sg r) (u r)) (fun t => 2 * (g t) (S (u t))) (by
            intro s t hs ht hst
            exact reverseTimeHilbertRepresentative_inner_increment hΩ T hT u g hderiv Su Sg
              hSu s t hs ht hst) (ae_pivot_factorization_rate hΩ T u g S Su Sg hSuAgree (ContinuousLinearMap.coeFn_compLpL (h10HilbertGraphDualPrecompose hΩ S) g)) s t hs ht hst)⟩

/-- A bounded spatial pivot factorization yields the reverse-time scalar energy
testing identity for the value-level `L²` norm of its left factor. -/
theorem
    integral_value_norm_sq_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_pivot_factorization

    (eta : ReverseTimeScalarTest T) :
    (∫ t,
      ‖valueCLM hΩ (A (u t))‖ ^ 2 * eta.deriv t
        ∂reverseTimeVolume T) =
      -(∫ t,
        (2 * (g t) (S (u t))) * eta t
          ∂reverseTimeVolume T) := by
  obtain ⟨e, hq, he, heq, hinc⟩ :=
    exists_continuous_value_norm_sq_energy_increment_of_pivot_factorization
      hΩ T hT A S hfactor u g hderiv
  have hscalar := integral_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_increment
    T hT (fun t => 2 * (g t) (S (u t))) e hq he hinc eta
  calc
    (∫ t, ‖valueCLM hΩ (A (u t))‖ ^ 2 * eta.deriv t ∂reverseTimeVolume T) =
        ∫ t, e t * eta.deriv t ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards [heq] with t ht
      rw [ht]
    _ = -(∫ t, (2 * (g t) (S (u t))) * eta t
        ∂reverseTimeVolume T) := hscalar
end


end HypoellipticAleksandrov.Parabolic.Dirichlet
