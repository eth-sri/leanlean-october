module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerSequence
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Comparison

/-! # The source's second limit from reflected inner cylinders to the original closure -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

variable {d : ℕ}

/-- Every backward kinetic boundary is nonempty, including all grazing conventions. -/
theorem borel_kineticBoundary_nonempty  (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    (kineticBoundary P₀ R).Nonempty := by
  have hn := (comparison_exitBoundary_nonempty (kineticReflection P₀) R hR).image
    kineticReflection
  rw [kineticReflection_image_exitBoundary,kineticReflection_involutive P₀] at hn
  exact hn

/-- Inner estimates exhaust the original closure with the same constant and either source norm. -/
theorem borel_boundary_limit  (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ)
    (localised : Bool) (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (u f : HypoellipticAleksandrov.KineticScalarField d)
    (hcont : ContinuousOn u (closure (backwardCylinder P₀ R)))
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R)))
    (hinner : ∀ n, ∀ P ∈ closure (backwardCylinder
        (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary
        (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)) +
      C₀ * (borelInnerRadius R hR n) ^ alpha *
        (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder
            (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)))).toReal) :
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal := by
  let sharedTerm_ce2fc16e35 := ((fun P => max (u P) 0))
  let Q := backwardCylinder P₀ R
  let Qn := fun n => backwardCylinder (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
  let F := borelSource localised u f
  let M := sSup (sharedTerm_ce2fc16e35 '' kineticBoundary P₀ R)
  let N := (eLpNorm F (ENNReal.ofReal p) (volume.restrict Q)).toReal
  have hQ := isOpen_backwardCylinder P₀ R hR
  have hQn n : IsOpen (Qn n) := isOpen_backwardCylinder _ _ (borelInnerRadius_pos R hR n)
  have hKn n : closure (Qn n) ⊆ Q := by
    have h := closure_reflected_innerCylinder_subset P₀ R hR _
      (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
    rw [kineticReflection_image_innerCylinder] at h
    exact h
  have hQnQ n : Qn n ⊆ Q := subset_closure.trans (hKn n)
  have hFp : MemLp F (ENNReal.ofReal p) (volume.restrict Q) :=
    borelSource_memLp hQ localised u f (hcont.mono subset_closure) hLp
  have hcover : ∀ᵐ P ∂(volume.restrict Q), ∀ᶠ n in atTop, P ∈ Qn n := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
    exact borel_inner_exhaustion P₀ R hR P hP
  have htF := borel_indicator_norm_tendsto (lt_of_lt_of_le zero_lt_one hp) F hFp
    (Filter.Eventually.of_forall (borelSource_nonneg localised u f)) Qn
    (fun n => (hQn n).measurableSet) hcover
  have heq n : eLpNorm ((Qn n).indicator F) (ENNReal.ofReal p) (volume.restrict Q) =
      eLpNorm F (ENNReal.ofReal p) (volume.restrict (Qn n)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hQn n).measurableSet,
      Measure.restrict_restrict (hQn n).measurableSet,inter_eq_left.mpr (hQnQ n)]
  have htN : Tendsto (fun n => (eLpNorm F (ENNReal.ofReal p)
      (volume.restrict (Qn n))).toReal) atTop (𝓝 N) := by
    simpa only [heq] using htF
  have htR := (Real.continuousAt_rpow_const R alpha (Or.inl hR.ne')).tendsto.comp
    (borelInnerRadius_tendsto R hR)
  have htCoeff := ((tendsto_const_nhds (x := C₀)).mul htR).mul htN
  have hinterior : ∀ P ∈ Q, u P ≤ M + C₀ * R ^ alpha * N := by
    intro P hP
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨η,hη,hboundary⟩ := comparison_kinetic_boundary_approx P₀ R hR u hcont hε
    have hsmall := (tendsto_order.mp (borelInnerDelta_tendsto R)).2 η hη
    have hm := borel_inner_exhaustion P₀ R hR P hP
    have hb : ∀ᶠ n in atTop, u P ≤ M + ε + C₀ * (borelInnerRadius R hR n) ^ alpha *
        (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Qn n))).toReal := by
      filter_upwards [hsmall,hm] with n hn hPn
      have hs : sSup (sharedTerm_ce2fc16e35 '' kineticBoundary
          (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)) ≤ M + ε := by
        apply csSup_le ((borel_kineticBoundary_nonempty _ _
          (borelInnerRadius_pos R hR n)).image sharedTerm_ce2fc16e35)
        rintro _ ⟨Z,hZ,rfl⟩
        exact hboundary _ _
          _ hn Z hZ
      have hi := hinner n P (subset_closure hPn)
      linarith only [hi,hs]
    have hu : u P ≤ M + ε + C₀ * R ^ alpha * N :=
      ge_of_tendsto ((tendsto_const_nhds (x := M + ε)).add htCoeff) hb
    linarith only [hu]
  exact le_on_closure hinterior hcont continuousOn_const

end HypoellipticAleksandrov.KineticAleksandrov
