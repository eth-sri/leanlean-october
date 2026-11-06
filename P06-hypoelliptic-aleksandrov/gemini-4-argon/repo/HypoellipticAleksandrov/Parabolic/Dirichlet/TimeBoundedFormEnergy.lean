module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarIncrement
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertIntegrationByParts
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces

/-!
# Reverse-time energy testing by a bounded pivot factorization

This module turns a bounded spatial factorization of the scalar `L²` pivot
into the corresponding reverse-time scalar energy testing identity.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem pivot_factorization_cross_energy_increment
    {d } {Ω : Set (PDE.Vec d)} {T : ℝ}
    (U V : C(↥(Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
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
    {d } {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (A S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hfactor : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y)))
    (u Su : ReverseTimeL2V hΩ T)
    (U V : C(↥(Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hU : ReverseTimeHilbertRepresentativeAgrees hΩ T u U)
    (hV : ReverseTimeHilbertRepresentativeAgrees hΩ T Su V)
    (hSu : Su =ᵐ[reverseTimeVolume T] fun t => S (u t)) :
    (fun t => if ht : t ∈ Icc 0 T then
      inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0) =ᵐ[reverseTimeVolume T]
      fun t => ‖valueCLM hΩ (A (u t))‖ ^ 2 := by
  have hIoo : ∀ᵐ t ∂reverseTimeVolume T, t ∈ Ioo 0 T :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hIoo, hU, hV, hSu] with
    t ht hUagree hVagree hSu
  have htIcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  rw [dif_pos htIcc, hUagree ht, hVagree ht, hSu, hfactor]
  exact real_inner_self_eq_norm_sq _

set_option linter.unusedVariables false in
/- A bounded spatial pivot factorization has a continuous closed-time
energy representative for the value norm of its left factor. -/
theorem exists_continuous_value_norm_sq_energy_increment_of_pivot_factorization
    {d } {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (A S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hfactor : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y)))
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
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
  let hSsymm : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y) := by
    intro x y
    calc
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
          inner ℝ (valueCLM hΩ (A x)) (valueCLM hΩ (A y)) := hfactor x y
      _ = inner ℝ (valueCLM hΩ (A y)) (valueCLM hΩ (A x)) := real_inner_comm _ _
      _ = inner ℝ (valueCLM hΩ y) (valueCLM hΩ (S x)) := (hfactor y x).symm
      _ = inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y) := real_inner_comm _ _
  let Su := S.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u
  let Sg := (h10HilbertGraphDualPrecompose hΩ S).compLpL
    (2 : ℝ≥0∞) (reverseTimeVolume T) g
  let hSu := hderiv.comp_of_pivot_symmetric S hSsymm
  let U := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let V := reverseTimeHilbertRepresentative hΩ T hT Su Sg hSu
  let q : ℝ → ℝ := fun t => 2 * (g t) (S (u t))
  let e : ℝ → ℝ := fun t => if ht : t ∈ Icc 0 T then
    inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0
  have hSuAgree : Su =ᵐ[reverseTimeVolume T] fun t => S (u t) :=
    ContinuousLinearMap.coeFn_compLpL S u
  have hSgAgree :=
    ContinuousLinearMap.coeFn_compLpL (h10HilbertGraphDualPrecompose hΩ S) g
  have hrate : (fun r => (g r) (Su r) + (Sg r) (u r)) =ᵐ[
      reverseTimeVolume T] q := by
    filter_upwards [hSuAgree, hSgAgree] with r hrSu hrSg
    rw [hrSu, hrSg]
    change (g r) (S (u r)) + (g r) (S (u r)) = 2 * (g r) (S (u r))
    ring
  have hq : Integrable q (reverseTimeVolume T) := by
    refine ((integrable_reverseTimeDualPairing hΩ T
      Su g).const_mul 2).congr ?_
    filter_upwards [hSuAgree] with r hrSu
    rw [hrSu]
  have he : ContinuousOn e (Icc 0 T) := by
    letI : InnerProductSpace ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) := L2.innerProductSpace
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Icc 0 T).domRestrict (fun t => if ht : t ∈ Icc 0 T then
        inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) else 0) =
        fun t => inner ℝ (U t) (V t) := by
      funext t
      simp only [Set.domRestrict_apply, dif_pos t.2]
    rw [heq]
    have hinner : Continuous (fun p : PDE.ScalarLp Ω (2 : ℝ≥0∞) ×
        PDE.ScalarLp Ω (2 : ℝ≥0∞) => inner ℝ p.1 p.2) := continuous_inner
    exact hinner.comp (U.continuous.prodMk V.continuous)
  have hcross : ∀ s t : ℝ, ∀ hs : s ∈ Icc 0 T, ∀ ht : t ∈ Icc 0 T, s ≤ t →
      inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) -
          inner ℝ (U ⟨s, hs⟩) (V ⟨s, hs⟩) =
        ∫ r in Ioc s t, ((g r) (Su r) + (Sg r) (u r)) ∂reverseTimeVolume T := by
    intro s t hs ht hst
    let hsum := hderiv.add hSu
    let U := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
    let V := reverseTimeHilbertRepresentative hΩ T hT Su Sg hSu
    let W := reverseTimeHilbertRepresentative hΩ T hT (u + Su) (g + Sg) hsum
    have hW : W = U + V := by
      obtain ⟨hW, _⟩ :=
        reverseTimeHilbertRepresentative_spec hΩ T hT (u + Su) (g + Sg) hsum
      have _h_inl_7 : ReverseTimeHilbertRepresentativeAgrees hΩ T (u + Su) (reverseTimeHilbertRepresentative hΩ T hT u g hderiv + reverseTimeHilbertRepresentative hΩ T hT Su Sg hSu) := by
        obtain ⟨hU, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv
        obtain ⟨hV, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT Su Sg hSu
        filter_upwards [hU, hV, Lp.coeFn_add u Su] with tau hU hV huv
        intro htau
        let htIcc : tau ∈ Icc 0 T := ⟨le_of_lt htau.1, le_of_lt htau.2⟩
        calc
          (reverseTimeHilbertRepresentative hΩ T hT u g hderiv +
              reverseTimeHilbertRepresentative hΩ T hT Su Sg hSu) ⟨tau, htIcc⟩ =
              reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨tau, htIcc⟩ +
                reverseTimeHilbertRepresentative hΩ T hT Su Sg hSu ⟨tau, htIcc⟩ := rfl
          _ = valueCLM hΩ (u tau) + valueCLM hΩ (Su tau) := by rw [hU htau, hV htau]
          _ = valueCLM hΩ (u tau + Su tau) := ((valueCLM hΩ).map_add _ _).symm
          _ = valueCLM hΩ ((u + Su) tau) := by
            rw [huv]
            rfl
      exact ReverseTimeHilbertRepresentativeAgrees.unique hW hT
        _h_inl_7
    have hU := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).2 s t hs ht hst
    have hV := (reverseTimeHilbertRepresentative_spec hΩ T hT Su Sg hSu).2 s t hs ht hst
    have hWenergy :=
      (reverseTimeHilbertRepresentative_spec hΩ T hT (u + Su) (g + Sg) hsum).2
        s t hs ht hst
    change inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) -
        inner ℝ (U ⟨s, hs⟩) (V ⟨s, hs⟩) = _
    change ‖U ⟨t, ht⟩‖ ^ 2 - ‖U ⟨s, hs⟩‖ ^ 2 = _ at hU
    change ‖V ⟨t, ht⟩‖ ^ 2 - ‖V ⟨s, hs⟩‖ ^ 2 = _ at hV
    change ‖W ⟨t, ht⟩‖ ^ 2 - ‖W ⟨s, hs⟩‖ ^ 2 = _ at hWenergy
    rw [hW] at hWenergy
    change ‖U ⟨t, ht⟩ + V ⟨t, ht⟩‖ ^ 2 -
        ‖U ⟨s, hs⟩ + V ⟨s, hs⟩‖ ^ 2 = _ at hWenergy
    have _h_inl_9 : ∫ r in Ioc s t, ((g + Sg) r) ((u + Su) r) ∂reverseTimeVolume T =
        (∫ r in Ioc s t, (g r) (u r) ∂reverseTimeVolume T) +
          (∫ r in Ioc s t, (g r) (Su r) ∂reverseTimeVolume T) +
            (∫ r in Ioc s t, (Sg r) (u r) ∂reverseTimeVolume T) +
              (∫ r in Ioc s t, (Sg r) (Su r) ∂reverseTimeVolume T) := by
        have hgu := integrable_reverseTimeDualPairing hΩ T u g
        have hgv := integrable_reverseTimeDualPairing hΩ T Su g
        have hku := integrable_reverseTimeDualPairing hΩ T u Sg
        have hkv := integrable_reverseTimeDualPairing hΩ T Su Sg
        have hguIoc : Integrable (fun r => (g r) (u r))
            ((reverseTimeVolume T).restrict (Ioc s t)) := hgu.restrict
        have hgvIoc : Integrable (fun r => (g r) (Su r))
            ((reverseTimeVolume T).restrict (Ioc s t)) := hgv.restrict
        have hkuIoc : Integrable (fun r => (Sg r) (u r))
            ((reverseTimeVolume T).restrict (Ioc s t)) := hku.restrict
        have hkvIoc : Integrable (fun r => (Sg r) (Su r))
            ((reverseTimeVolume T).restrict (Ioc s t)) := hkv.restrict
        have _h_inl_8 : (fun r => ((g + Sg) r) ((u + Su) r)) =ᵐ[reverseTimeVolume T] (fun r => (g r) (u r) + (g r) (Su r) + (Sg r) (u r) + (Sg r) (Su r)) := by
          filter_upwards [Lp.coeFn_add g Sg, Lp.coeFn_add u Su] with r hgk huv
          rw [hgk, huv]
          change (g r + Sg r) (u r + Su r) = _
          change (g r) (u r + Su r) + (Sg r) (u r + Su r) = _
          have hgadd : (g r) (u r + Su r) = (g r) (u r) + (g r) (Su r) :=
            (g r).map_add _ _
          have hkadd : (Sg r) (u r + Su r) = (Sg r) (u r) + (Sg r) (Su r) :=
            (Sg r).map_add _ _
          calc
            (g r) (u r + Su r) + (Sg r) (u r + Su r) =
                ((g r) (u r) + (g r) (Su r)) + ((Sg r) (u r) + (Sg r) (Su r)) :=
              congrArg₂ (· + ·) hgadd hkadd
            _ = _ := by ring
        rw [integral_congr_ae (ae_restrict_of_ae
          _h_inl_8)]
        have hguv :
            (∫ r in Ioc s t, (g r) (u r) + (g r) (Su r) ∂reverseTimeVolume T) =
              (∫ r in Ioc s t, (g r) (u r) ∂reverseTimeVolume T) +
                (∫ r in Ioc s t, (g r) (Su r) ∂reverseTimeVolume T) :=
          integral_add hguIoc hgvIoc
        have hkuv :
            (∫ r in Ioc s t, (Sg r) (u r) + (Sg r) (Su r) ∂reverseTimeVolume T) =
              (∫ r in Ioc s t, (Sg r) (u r) ∂reverseTimeVolume T) +
                (∫ r in Ioc s t, (Sg r) (Su r) ∂reverseTimeVolume T) :=
          integral_add hkuIoc hkvIoc
        have hfour :
            (∫ r in Ioc s t, ((g r) (u r) + (g r) (Su r)) +
                ((Sg r) (u r) + (Sg r) (Su r)) ∂reverseTimeVolume T) =
              (∫ r in Ioc s t, (g r) (u r) + (g r) (Su r) ∂reverseTimeVolume T) +
                (∫ r in Ioc s t, (Sg r) (u r) + (Sg r) (Su r) ∂reverseTimeVolume T) :=
          integral_add (hguIoc.add hgvIoc) (hkuIoc.add hkvIoc)
        calc
          ∫ r in Ioc s t, (g r) (u r) + (g r) (Su r) + (Sg r) (u r) + (Sg r) (Su r)
              ∂reverseTimeVolume T =
              ∫ r in Ioc s t, ((g r) (u r) + (g r) (Su r)) + ((Sg r) (u r) + (Sg r) (Su r))
                ∂reverseTimeVolume T := by
            apply integral_congr_ae
            filter_upwards [] with r
            ring
          _ = _ := by
            rw [hfour, hguv, hkuv]
            ring




    rw [_h_inl_9] at hWenergy
    rw [norm_add_sq_real, norm_add_sq_real] at hWenergy
    have hgvIoc : Integrable (fun r => (g r) (Su r))
        ((reverseTimeVolume T).restrict (Ioc s t)) :=
      (integrable_reverseTimeDualPairing hΩ T Su g).restrict
    have hkuIoc : Integrable (fun r => (Sg r) (u r))
        ((reverseTimeVolume T).restrict (Ioc s t)) :=
      (integrable_reverseTimeDualPairing hΩ T u Sg).restrict
    rw [integral_add hgvIoc hkuIoc]
    have hcross :
        2 * (inner ℝ (U ⟨t, ht⟩) (V ⟨t, ht⟩) -
          inner ℝ (U ⟨s, hs⟩) (V ⟨s, hs⟩)) =
        2 * ((∫ r in Ioc s t, (g r) (Su r) ∂reverseTimeVolume T) +
          (∫ r in Ioc s t, (Sg r) (u r) ∂reverseTimeVolume T)) := by
      linarith
    linarith
  have hinc : ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
      e t - e s = ∫ r in Ioc s t, q r ∂reverseTimeVolume T := by
    intro s t hs ht hst
    exact pivot_factorization_cross_energy_increment U V
      (fun r => (g r) (Su r) + (Sg r) (u r)) q hcross hrate s t hs ht hst
  have hUagree := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hVagree := (reverseTimeHilbertRepresentative_spec hΩ T hT Su Sg hSu).1
  have heq : e =ᵐ[reverseTimeVolume T]
      fun t => ‖valueCLM hΩ (A (u t))‖ ^ 2 := by
    exact ae_pivot_factorization_cross_energy_eq_norm_sq hΩ T A S hfactor u Su U V
      hUagree hVagree hSuAgree
  exact ⟨e, hq, he, heq, hinc⟩

/- A bounded spatial pivot factorization yields the reverse-time scalar energy
testing identity for the value-level `L²` norm of its left factor. -/
end HypoellipticAleksandrov.Parabolic.Dirichlet
