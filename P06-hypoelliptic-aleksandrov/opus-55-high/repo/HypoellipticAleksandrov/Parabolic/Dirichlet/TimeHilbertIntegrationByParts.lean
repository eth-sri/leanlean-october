module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces

/-!
# Reverse-time Hilbert integration by parts

This module polarizes the one-curve reverse-time Hilbert energy
increment for canonical continuous representatives.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace


namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T)

private theorem reverseTimeHilbertRepresentative_add_agrees
     (g : ReverseTimeL2VStar hΩ T)
    (hu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : ReverseTimeL2V hΩ T) (k : ReverseTimeL2VStar hΩ T)
    (hv : HasGelfandWeakTimeDerivative hΩ T hT v k) :
    ReverseTimeHilbertRepresentativeAgrees hΩ T (u + v)
      (reverseTimeHilbertRepresentative hΩ T hT u g hu +
        reverseTimeHilbertRepresentative hΩ T hT v k hv) := by
  obtain ⟨hU, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT u g hu
  obtain ⟨hV, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT v k hv
  filter_upwards [hU, hV, Lp.coeFn_add u v] with tau hU hV huv
  aesop

private theorem reverseTimeHilbertRepresentative_add_eq
     (g : ReverseTimeL2VStar hΩ T)
    (hu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : ReverseTimeL2V hΩ T) (k : ReverseTimeL2VStar hΩ T)
    (hv : HasGelfandWeakTimeDerivative hΩ T hT v k)
    (hsum : HasGelfandWeakTimeDerivative hΩ T hT (u + v) (g + k)) :
    reverseTimeHilbertRepresentative hΩ T hT (u + v) (g + k) hsum =
      reverseTimeHilbertRepresentative hΩ T hT u g hu +
        reverseTimeHilbertRepresentative hΩ T hT v k hv := by
  obtain ⟨hW, _⟩ :=
    reverseTimeHilbertRepresentative_spec hΩ T hT (u + v) (g + k) hsum
  exact ReverseTimeHilbertRepresentativeAgrees.unique hW hT
    (reverseTimeHilbertRepresentative_add_agrees hΩ T hT u g hu v k hv)

private theorem reverseTimeDualPairing_add_ae
    
    (u v : ReverseTimeL2V hΩ T) (g k : ReverseTimeL2VStar hΩ T) :
    (fun r => ((g + k) r) ((u + v) r)) =ᵐ[reverseTimeVolume T]
      (fun r => (g r) (u r) + (g r) (v r) + (k r) (u r) + (k r) (v r)) := by
  filter_upwards [Lp.coeFn_add g k, Lp.coeFn_add u v] with r hgk huv
  rw [hgk, huv]
  have hgadd : (g r) (u r + v r) = (g r) _ + (g r) _ :=
    (g r).map_add _ _
  have hkadd : (k r) (u r + v r) = (k r) _ + (k r) _ :=
    (k r).map_add _ _
  calc
    (g r) _ + (k r) _ =
        ((g r) _ + (g r) _) + ((k r) _ + (k r) _) :=
      congrArg₂ _ hgadd hkadd
    _ = _ := by ring

private theorem integral_sum_reverseTimeDualPairings_Ioc
    
    (u v : ReverseTimeL2V hΩ T) (g k : ReverseTimeL2VStar hΩ T)
    (s t : ℝ) :
    ∫ r in Ioc s t, ((g + k) r) ((u + v) r) ∂reverseTimeVolume T =
      (∫ r in Ioc s t, (g r) (u r) ∂reverseTimeVolume T) +
        (∫ r in Ioc s t, (g r) (v r) ∂reverseTimeVolume T) +
          (∫ r in Ioc s t, (k r) (u r) ∂reverseTimeVolume T) +
            (∫ r in Ioc s t, (k r) (v r) ∂reverseTimeVolume T) := by
  have hgu := integrable_reverseTimeDualPairing hΩ T u g
  have hgv := integrable_reverseTimeDualPairing hΩ T v g
  have hku := integrable_reverseTimeDualPairing hΩ T u k
  have hkv := integrable_reverseTimeDualPairing hΩ T v k
  have hguIoc : Integrable _
      ((reverseTimeVolume T).restrict (Ioc s t)) := hgu.restrict
  have hgvIoc : Integrable _
      ((reverseTimeVolume T).restrict (Ioc s t)) := hgv.restrict
  have hkuIoc : Integrable _
      ((reverseTimeVolume T).restrict (Ioc s t)) := hku.restrict
  have hkvIoc : Integrable _
      ((reverseTimeVolume T).restrict (Ioc s t)) := hkv.restrict
  rw [integral_congr_ae (ae_restrict_of_ae
    (reverseTimeDualPairing_add_ae hΩ T u v g k))]
  have hguv :
      (∫ r in Ioc s t, (g r) _ + (g r) _ ∂reverseTimeVolume T) =
        (∫ r in Ioc s t, (g r) _ ∂reverseTimeVolume T) +
          (∫ r in Ioc s t, (g r) _ ∂reverseTimeVolume T) :=
    integral_add hguIoc hgvIoc
  have hkuv :
      (∫ r in Ioc s t, (k r) _ + (k r) _ ∂reverseTimeVolume T) =
        (∫ r in Ioc s t, (k r) _ ∂reverseTimeVolume T) +
          (∫ r in Ioc s t, (k r) _ ∂reverseTimeVolume T) :=
    integral_add hkuIoc hkvIoc
  have hfour :
      (∫ r in Ioc s t, ((g r) _ + (g r) _) +
          ((k r) _ + (k r) _) ∂reverseTimeVolume T) =
        (∫ r in Ioc s t, (g r) _ + (g r) _ ∂reverseTimeVolume T) +
          (∫ r in Ioc s t, (k r) _ + (k r) _ ∂reverseTimeVolume T) :=
    integral_add (hguIoc.add hgvIoc) (hkuIoc.add hkvIoc)
  calc
    ∫ r in Ioc s t, (g r) _ + (g r) _ + (k r) _ + (k r) _
        ∂reverseTimeVolume T =
        ∫ r in Ioc s t, ((g r) _ + (g r) (v r)) + ((k r) _ + (k r) (v r))
          ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards [] with r
      ring
    _ = _ := by
      rw [hfour, hguv, hkuv]
      ring

/-- Reverse-time Hilbert integration by parts for the canonical continuous
spatial-`L²` representatives of two Gelfand weak-derivative curves. Raw
Bochner representatives are not evaluated at closed-time endpoints. -/
theorem reverseTimeHilbertRepresentative_inner_increment
     (g : ReverseTimeL2VStar hΩ T)
    (hu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : ReverseTimeL2V hΩ T) (k : ReverseTimeL2VStar hΩ T)
    (hv : HasGelfandWeakTimeDerivative hΩ T hT v k)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    inner ℝ
        (reverseTimeHilbertRepresentative hΩ T hT u g hu ⟨t, ht⟩)
        (reverseTimeHilbertRepresentative hΩ T hT v k hv ⟨t, ht⟩) -
      inner ℝ
        (reverseTimeHilbertRepresentative hΩ T hT u g hu ⟨s, hs⟩)
        (reverseTimeHilbertRepresentative hΩ T hT v k hv ⟨s, hs⟩) =
      ∫ r in Set.Ioc s t,
        ((g r) (v r) + (k r) (u r)) ∂reverseTimeVolume T := by
  let hsum := hu.add hv
  let U := reverseTimeHilbertRepresentative hΩ T hT u g hu
  let V := reverseTimeHilbertRepresentative hΩ T hT v k hv
  let W := reverseTimeHilbertRepresentative hΩ T hT _ _ hsum
  have hW : W = U + V :=
    reverseTimeHilbertRepresentative_add_eq hΩ T hT u g hu v k hv hsum
  have hU := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hu).2 s t hs ht hst
  have hV := (reverseTimeHilbertRepresentative_spec hΩ T hT v k hv).2 s t hs ht hst
  have hWenergy :=
    (reverseTimeHilbertRepresentative_spec hΩ T hT _ _ hsum).2
      s t hs ht hst
  change ‖W _‖ ^ 2 - ‖W _‖ ^ 2 = _ at hWenergy
  rw [hW] at hWenergy
  change ‖U _ + V _‖ ^ 2 -
      ‖U _ + V _‖ ^ 2 = _ at hWenergy
  rw [integral_sum_reverseTimeDualPairings_Ioc, norm_add_sq_real, norm_add_sq_real] at hWenergy
  have hgvIoc : Integrable _
      ((reverseTimeVolume T).restrict (Ioc s t)) :=
    (integrable_reverseTimeDualPairing hΩ T v g).restrict
  have hkuIoc : Integrable _
      ((reverseTimeVolume T).restrict (Ioc s t)) :=
    (integrable_reverseTimeDualPairing hΩ T u k).restrict
  rw [integral_add hgvIoc hkuIoc]
  linarith

end HypoellipticAleksandrov.Parabolic.Dirichlet
