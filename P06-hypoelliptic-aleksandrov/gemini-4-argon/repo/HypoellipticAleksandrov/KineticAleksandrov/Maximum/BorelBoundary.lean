module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerSequence
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Comparison
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflectedRetraction
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderUniform

/-! # The source's second limit from reflected inner cylinders to the original closure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/- Every backward kinetic boundary is nonempty, including all grazing conventions. -/
theorem borel_kineticBoundary_nonempty {d } (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    (kineticBoundary P₀ R).Nonempty := by
  have hn := (comparison_exitBoundary_nonempty (kineticReflection P₀) R hR).image
    kineticReflection
  rw [kineticReflection_image_exitBoundary,kineticReflection_involutive P₀] at hn
  exact hn

/- Inner estimates exhaust the original closure with the same constant and either source norm. -/
theorem borel_boundary_limit {d : ℕ} (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ)
    (localised : Bool) (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (u f : KineticPoint d → ℝ)
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
  let Q := backwardCylinder P₀ R
  let Qn := fun n => backwardCylinder (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
  let F := borelSource localised u f
  let M := sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R)
  let N := (eLpNorm F (ENNReal.ofReal p) (volume.restrict Q)).toReal
  have hQ := isOpen_backwardCylinder P₀ R hR
  have hQn n : IsOpen (Qn n) := isOpen_backwardCylinder _ _ (borelInnerRadius_pos R hR n)
  have hKn n : closure (Qn n) ⊆ Q := by
    have h := closure_reflected_innerCylinder_subset P₀ R hR (borelInnerDelta R n)
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
    obtain ⟨η,hη,hboundary⟩ : ∃ η : ℝ, 0 < η ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2),
      δ < η → ∀ P ∈ kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R),
        max (u P) 0 ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + ε := by
      have hS : kineticBoundary P₀ R ⊆ closure (backwardCylinder P₀ R) := fun _ h => h.1
      have hcompact : IsCompact (closure (backwardCylinder P₀ R)) := by
        have h := (isCompact_closure_forwardCylinder (kineticReflection P₀) R hR).image
          (continuous_kineticReflection d)
        rw [kineticReflection_image_closure, kineticReflection_image_forwardCylinder,
          kineticReflection_involutive P₀] at h
        exact h
      obtain ⟨r,hr,hbound⟩ := boundary_value_le_of_close_map hcompact hcont hS hε
      obtain ⟨η,hη,hclose⟩ := reflectedInnerRetraction_uniformly_to_identity P₀ R hR r hr
      refine ⟨η,hη,?_⟩
      intro δ hδ0 hδlt hδη P hP
      have _h_xinl_0 : reflectedInnerRetraction P₀ R hR δ hδ0 hδlt '' kineticBoundary P₀ R =
      kineticBoundary
        ⟨P₀.time - δ, P₀.position - δ • P₀.velocity, P₀.velocity⟩
        (innerRatio R hR δ hδ0 hδlt * R) := by
          change (kineticReflection ∘ (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt ∘
            kineticReflection)) '' _ = _
          simp only [Function.comp_def]
          rw [← image_image kineticReflection
            (fun P => innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt
              (kineticReflection P)),
            ← image_image (innerRetraction (kineticReflection P₀) R hR δ hδ0 hδlt)
              kineticReflection, kineticReflection_image_kineticBoundary P₀ R hR,
            innerRetraction_image_exitBoundary,kineticReflection_image_innerExitBoundary]

        /- Reflection preserves the existing product-metric distance, used only topologically. -/
      rw [← _h_xinl_0] at hP
      obtain ⟨x,hx,rfl⟩ := hP
      apply hbound (reflectedInnerRetraction P₀ R hR δ hδ0 hδlt) ?_ ?_ x hx
      · intro y hy
        have hi := closure_reflected_innerCylinder_subset P₀ R hR δ hδ0 hδlt
        apply subset_closure (hi ?_)
        rw [kineticReflection_image_innerCylinder P₀ R hR δ hδ0 hδlt]
        rw [← reflectedInnerRetraction_image_closure P₀ R hR δ hδ0 hδlt]
        exact mem_image_of_mem _ (hS hy)
      · exact fun y hy => hclose δ hδ0 hδlt hδη y (hS hy)
    have hsmall := (tendsto_order.mp (borelInnerDelta_tendsto R)).2 η hη
    have hm := borel_inner_exhaustion P₀ R hR P hP
    have hb : ∀ᶠ n in atTop, u P ≤ M + ε + C₀ * (borelInnerRadius R hR n) ^ alpha *
        (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Qn n))).toReal := by
      filter_upwards [hsmall,hm] with n hn hPn
      have hs : sSup ((fun P => max (u P) 0) '' kineticBoundary
          (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)) ≤ M + ε := by
        apply csSup_le ((borel_kineticBoundary_nonempty _ _
          (borelInnerRadius_pos R hR n)).image (fun P => max (u P) 0))
        rintro _ ⟨Z,hZ,rfl⟩
        exact hboundary (borelInnerDelta R n) (borelInnerDelta_valid R hR n).1
          (borelInnerDelta_valid R hR n).2 hn Z hZ
      have hi := hinner n P (subset_closure hPn)
      linarith only [hi,hs]
    have hu : u P ≤ M + ε + C₀ * R ^ alpha * N :=
      ge_of_tendsto ((tendsto_const_nhds (x := M + ε)).add htCoeff) hb
    linarith only [hu]
  exact le_on_closure hinterior hcont continuousOn_const

end HypoellipticAleksandrov.KineticAleksandrov
