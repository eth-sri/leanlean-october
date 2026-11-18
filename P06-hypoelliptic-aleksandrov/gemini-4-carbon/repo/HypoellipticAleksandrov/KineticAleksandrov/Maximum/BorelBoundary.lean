module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Comparison

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter MeasureTheory
open scoped Topology

/-- A valid inner error scale for every natural index, starting at zero. -/
def borelInnerDelta (R : ℝ) (n : ℕ) : ℝ := R ^ 2 / (4 * ((n : ℝ) + 1))

/-- Every scale is positive and below half the original time depth. -/
theorem borelInnerDelta_valid (R : ℝ) (hR : 0 < R) (n : ℕ) :
    0 < borelInnerDelta R n ∧ borelInnerDelta R n < R ^ 2 / 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < 4 * ((n : ℝ) + 1) := by positivity
  have hR2 := sq_pos_of_pos hR
  refine ⟨div_pos hR2 hd,?_⟩
  rw [borelInnerDelta,div_lt_iff₀ hd]
  nlinarith only [hn,hR2]

/-- The scale tends to zero with the centre and original radius fixed. -/
theorem borelInnerDelta_tendsto (R : ℝ) :
    Tendsto (borelInnerDelta R) atTop (𝓝 0) := by
  have heq : borelInnerDelta R = fun (n : ℕ) => R ^ 2 / 4 * (1 / ((n : ℝ) + 1)) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [borelInnerDelta]
    field_simp
  rw [heq]
  convert! tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R ^ 2 / 4) using 1
  simp

/-- Radius of the concrete reflected inner cylinder. -/
def borelInnerRadius (R : ℝ) (hR : 0 < R) (n : ℕ) : ℝ :=
  innerRatio R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2 * R

/-- Positivity holds at every index, without discarding the first cylinder. -/
theorem borelInnerRadius_pos (R : ℝ) (hR : 0 < R) (n : ℕ) :
    0 < borelInnerRadius R hR n :=
  mul_pos (innerRatio_spec R hR _ (borelInnerDelta_valid R hR n).1
    (borelInnerDelta_valid R hR n).2).1 hR


/-- The source shifted backward centre for the concrete sequence. -/
def borelInnerCentre {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (n : ℕ) : KineticPoint d :=
  ⟨P₀.time - borelInnerDelta R n,
    P₀.position - borelInnerDelta R n • P₀.velocity,P₀.velocity⟩

/-- Every backward interior point eventually lies in the shifted inner cylinders. -/
theorem borel_inner_exhaustion {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (P : KineticPoint d) (hP : P ∈ backwardCylinder P₀ R) :
    ∀ᶠ n in atTop, P ∈ backwardCylinder (borelInnerCentre P₀ R n) (borelInnerRadius R hR n) := by
  have hP' : kineticReflection P ∈ forwardCylinder (kineticReflection P₀) R hR := by
    rw [← kineticReflection_image_backwardCylinder P₀ R hR]
    exact mem_image_of_mem _ hP
  obtain ⟨η,hη,hmem⟩ := innerCylinder_exhaustion (kineticReflection P₀) R hR
    (kineticReflection P) hP'
  filter_upwards [((tendsto_order.mp (borelInnerDelta_tendsto R)).2 η hη)] with n hn
  change P ∈ backwardCylinder
    ⟨P₀.time - borelInnerDelta R n,P₀.position - borelInnerDelta R n • P₀.velocity,
      P₀.velocity⟩ (borelInnerRadius R hR n)
  unfold borelInnerRadius
  rw [← kineticReflection_image_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2]
  exact ⟨kineticReflection P,(hmem (borelInnerDelta R n) (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2 hn),kineticReflection_involutive P⟩



/-- Inner estimates exhaust the original closure with the same constant and either source norm. -/
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
        (volume.restrict (backwardCylinder P₀ R))).toReal   := by
  have borel_kineticBoundary_nonempty (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
      (kineticBoundary P₀ R).Nonempty := by
    have hn := (comparison_exitBoundary_nonempty (kineticReflection P₀) R hR).image
      kineticReflection
    rwa [kineticReflection_image_exitBoundary,kineticReflection_involutive P₀] at hn
  have borelInnerRadius_tendsto :
      Tendsto (borelInnerRadius R hR) atTop (𝓝 R) := by
    have ht' : Tendsto (fun n => 1 - 2 * borelInnerDelta R n / R ^ 2)
        atTop (𝓝 1) := by simpa using ((tendsto_const_nhds (x := 1)).sub (((borelInnerDelta_tendsto R).const_mul 2).div_const (R ^ 2)))
    have hs := (Real.continuous_sqrt.tendsto 1).comp ht'
    change Tendsto (fun n => Real.sqrt (1 - 2 * borelInnerDelta R n / R ^ 2) * R)
      atTop (𝓝 R)
    simpa using hs.mul_const R
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
    rwa [kineticReflection_image_innerCylinder] at h
  have hQnQ n : Qn n ⊆ Q := subset_closure.trans (hKn n)
  have hFp : MemLp F (ENNReal.ofReal p) (volume.restrict Q) :=
    borelSource_memLp hQ localised u f (hcont.mono subset_closure) hLp
  have hcover : ∀ᵐ P ∂(volume.restrict Q), ∀ᶠ n in atTop, P ∈ Qn n := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
    exact borel_inner_exhaustion P₀ R hR P hP
  have heq n : eLpNorm ((Qn n).indicator F) (ENNReal.ofReal p) (volume.restrict Q) =
      eLpNorm F (ENNReal.ofReal p) (volume.restrict (Qn n)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hQn n).measurableSet,
      Measure.restrict_restrict (hQn n).measurableSet,inter_eq_left.mpr (hQnQ n)]
  have htN : Tendsto (fun n => (eLpNorm F (ENNReal.ofReal p)
      (volume.restrict (Qn n))).toReal) atTop (𝓝 N) := by
    simpa only [heq] using (borel_indicator_norm_tendsto (lt_of_lt_of_le zero_lt_one hp) F hFp (Filter.Eventually.of_forall (borelSource_nonneg localised u f)) Qn (fun n => (hQn n).measurableSet) hcover)
  have htR := (Real.continuousAt_rpow_const R alpha (Or.inl hR.ne')).tendsto.comp
    (borelInnerRadius_tendsto)
  have htCoeff := ((tendsto_const_nhds (x := C₀)).mul htR).mul htN
  have hinterior : ∀ P ∈ Q, u P ≤ M + C₀ * R ^ alpha * N := by
    intro P hP
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨η,hη,hboundary⟩ := comparison_kinetic_boundary_approx P₀ R hR u hcont hε
    have hb : ∀ᶠ n in atTop, u P ≤ M + ε + C₀ * (borelInnerRadius R hR n) ^ alpha *
        (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Qn n))).toReal := by
      filter_upwards [((tendsto_order.mp (borelInnerDelta_tendsto R)).2 η hη),(borel_inner_exhaustion P₀ R hR P hP)] with n hn hPn
      have hs : sSup ((fun P => max (u P) 0) '' kineticBoundary
          (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)) ≤ M + ε := by
        apply csSup_le ((borel_kineticBoundary_nonempty _ _
          (borelInnerRadius_pos R hR n)).image (fun P => max (u P) 0))
        rintro _ ⟨Z,hZ,rfl⟩
        exact hboundary (borelInnerDelta R n) (borelInnerDelta_valid R hR n).1
          (borelInnerDelta_valid R hR n).2 hn Z hZ
      linarith only [(hinner n P (subset_closure hPn)),hs]
    linarith only [(ge_of_tendsto ((tendsto_const_nhds).add htCoeff) hb)]
  exact le_on_closure hinterior hcont continuousOn_const

end HypoellipticAleksandrov.KineticAleksandrov

