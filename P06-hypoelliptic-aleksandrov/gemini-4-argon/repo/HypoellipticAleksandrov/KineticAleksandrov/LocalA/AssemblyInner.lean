module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothLocalStatement
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsReflection
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelDerivativeLimit
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelHolderLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectors
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
import Mathlib.Topology.UniformSpace.UniformConvergence
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Transfer of the joint estimate on a fixed compact interior cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Filter Metric Holder
open scoped Topology Matrix.Norms.Elementwise
open SectionTwo TheoremA
open HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov
open scoped MatrixOrder ContDiff

/- The data-dependent part of the authorized smooth joint estimate. -/
def SmoothEstimateFor {d : ℕ} (lam Lam : ℝ) (C_m : ℕ → ℝ) (C α : ℝ) : Prop :=
  ∀ A : CoefficientField d, IsSmoothCoefficient A → IsSymmetricCoefficient A →
    HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
  ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R → ∀ u : KineticPoint d → ℝ,
    ContinuousOn u (closure (backwardCylinder P₀ R)) →
    IsKineticC112On u (backwardCylinder P₀ R) →
    (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
    (∀ P ∈ backwardCylinder P₀ R,
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
    (∀ m, 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
      R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
        C_m m * Holder.oscillationOn u (backwardCylinder P₀ R)) ∧
    (∀ P ∈ backwardCylinder P₀ (R / 2), ∀ Q ∈ backwardCylinder P₀ (R / 2),
      |u P - u Q| ≤ C * Holder.oscillationOn u (backwardCylinder P₀ R) *
        (kineticIncrement P₀ P Q / R) ^ α)

/- Correctors recover smoothness and quantitative estimates on a fixed inner cylinder. -/
theorem borel_inner_joint_estimates
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d } (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (C_m : ℕ → ℝ) (hCm : ∀ m, 0 ≤ C_m m) (C α : ℝ)
    (hest : SmoothEstimateFor (d := d) lam Lam C_m C α)
    (A : CoefficientField d) (hA : IsBorelCoefficient A)
    (hs : IsSymmetricCoefficient A) (hlo : HasLowerEllipticityAE lam A)
    (hhi : HasUpperEllipticityAE Lam A)
    (P₀ : KineticPoint d) (R ) (hR : 0 < R)
    (u : KineticPoint d → ℝ) (hu : IsKineticC112On u (backwardCylinder P₀ R))
    (he : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0)
    (P₁ : KineticPoint d) (r : ℝ) (hr : 0 < r)
    (hKD : closure (backwardCylinder P₁ r) ⊆ backwardCylinder P₀ R) :
    (∀ P ∈ backwardCylinder P₁ (3 * r / 4),
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position ∧
      ∀ m, 1 ≤ m → r ^ (3 * m) *
        ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
          C_m m * Holder.oscillationOn u (backwardCylinder P₁ r)) ∧
    (∀ P ∈ backwardCylinder P₁ (r / 2), ∀ Q ∈ backwardCylinder P₁ (r / 2),
      |u P - u Q| ≤ C * Holder.oscillationOn u (backwardCylinder P₁ r) *
        (kineticIncrement P₁ P Q / r) ^ α) := by
  let E := backwardCylinder P₁ r
  have hK := isCompact_closure_backwardCylinder P₁ r hr
  have huc := hu.continuousOn.mono hKD
  obtain ⟨B, w, O, hO, hKO, hB, hw, hew, ht⟩ : ∃ (B : ℕ → CoefficientField d) (w : ℕ → KineticPoint d → ℝ)
      (O : Set (KineticPoint d)), IsOpen O ∧ (closure E) ⊆ O ∧
      (∀ j, IsSmoothCoefficient (B j) ∧ IsSymmetricCoefficient (B j) ∧
        HasLowerEllipticityAE lam (B j) ∧ HasUpperEllipticityAE Lam (B j)) ∧
      (∀ j, IsKineticC112On (w j) O) ∧
      (∀ j, ∀ P ∈ O, backwardOperatorOfTimeVelocityCoefficient (B j) (w j) P = 0) ∧
      TendstoUniformlyOn w u atTop (closure E) := by
    let L := (closure E)
    let Z := kineticReflection P₀
    let D := forwardCylinder Z R hR
    have hmap : MapsTo (kineticReflection (d := d)) D (backwardCylinder P₀ R) := by
      intro P hP
      have hi := kineticReflection_image_backwardCylinder P₀ R hR
      dsimp only [D, Z] at hP
      rw [← hi] at hP
      rcases hP with ⟨Q, hQ, rfl⟩
      simpa only [kineticReflection_involutive Q] using hQ
    have hreg := comparison_regular_mono (isKineticC112On_kineticReflection u _ hu) hmap
    have hμ := (measurePreserving_kineticReflection d).quasiMeasurePreserving.restrict hmap
    have he' : ∀ᵐ P ∂volume.restrict D,
        forwardKineticOperator (ofTimeVelocityCoefficient (kineticReflectedCoefficient A))
          (u ∘ kineticReflection) P = 0 := by
      filter_upwards [hμ.ae he] with P hP
      rw [reflectedKineticOperator_reflection, hP, neg_zero]
    have hKL : kineticReflection '' L ⊆ D := by
      dsimp only [D, Z]
      rw [← kineticReflection_image_backwardCylinder P₀ R hR]
      exact image_mono hKD
    have _h_xinl_0 : IsBorelCoefficient (kineticReflectedCoefficient A) := by
        exact (
      hA.comp ((continuous_fst.neg.prodMk continuous_snd).measurable)
      )
    obtain ⟨B, W, V, hV, hKV, _, hB, hW, heW, ht⟩ :=
      exists_borel_homogeneous_correctors hH hLE hd lam Lam hlam hLam
        (kineticReflectedCoefficient A) _h_xinl_0
        (isSymmetricCoefficient_kineticReflectedCoefficient A hs)
        (ellipticityAE_kineticReflectedCoefficient A lam Lam hlo hhi).1
        (ellipticityAE_kineticReflectedCoefficient A lam Lam hlo hhi).2 Z R hR
        (u ∘ kineticReflection) hreg he' (kineticReflection '' L)
        (hK.image (continuous_kineticReflection d)) hKL
    let O := kineticReflection ⁻¹' V
    have hO : IsOpen O := hV.preimage (continuous_kineticReflection d)
    have hWs j := isKineticC112On_of_contDiffOn hV
      (boundary_physical_smooth_to_native (hW j))
    have hBs j : IsSmoothCoefficient (B j) := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro k
      exact (hB j).2.2.1 i k |>.comp
        (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := (0 : PDE.Vec d)))))
    refine ⟨fun j => kineticReflectedCoefficient (B j), fun j => W j ∘ kineticReflection,
      O, hO, fun P hP => hKV (mem_image_of_mem _ hP), ?_, ?_, ?_, ?_⟩
    · intro j
      have hlo' : HasLowerEllipticityAE lam (B j) :=
        Eventually.of_forall (fun x => (hB j).2.2.2.2.1 x.1 x.2)
      have hhi' : HasUpperEllipticityAE Lam (B j) :=
        Eventually.of_forall (fun x => (hB j).2.2.2.2.2 x.1 x.2)
      exact ⟨isSmoothCoefficient_kineticReflectedCoefficient _ (hBs j),
        isSymmetricCoefficient_kineticReflectedCoefficient _ (hB j).2.2.2.1,
        (ellipticityAE_kineticReflectedCoefficient _ lam Lam hlo' hhi').1,
        (ellipticityAE_kineticReflectedCoefficient _ lam Lam hlo' hhi').2⟩
    · intro j
      exact isKineticC112On_kineticReflection _ _ (hWs j)
    · intro j P hP
      have hh := reflectedKineticOperator_reflection (kineticReflectedCoefficient (B j))
        (W j ∘ kineticReflection) (kineticReflection P)
      have hc : kineticReflectedCoefficient (kineticReflectedCoefficient (B j)) = B j := by
        funext s v
        simp only [kineticReflectedCoefficient, neg_neg]
      have hw : (W j ∘ kineticReflection) ∘ kineticReflection = W j := by
        funext Q
        simp only [Function.comp_apply, kineticReflection_involutive Q]
      rw [hc, hw, kineticReflection_involutive P, heW j _ hP] at hh
      linarith
    · have hh := ht.comp (kineticReflection (d := d))
      have hsubset : L ⊆ kineticReflection ⁻¹' (kineticReflection '' L) :=
        fun _ h => mem_image_of_mem _ h
      have hu' : (u ∘ kineticReflection) ∘ kineticReflection = u := by
        funext P
        simp only [Function.comp_apply, kineticReflection_involutive P]
      simpa only [hu'] using hh.mono hsubset
  have hEO := subset_closure.trans hKO
  have heQ j : ∀ᵐ P ∂volume.restrict E,
      backwardOperatorOfTimeVelocityCoefficient (B j) (w j) P = 0 := by
    filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₁ r hr).measurableSet]
      with P hP
    exact hew j P (hEO hP)
  have hestj j := hest (B j) (hB j).1 (hB j).2.1 (hB j).2.2.1 (hB j).2.2.2
    P₁ r hr (w j) ((hw j).continuousOn.mono hKO)
    (comparison_regular_mono (hw j) hEO)
    (heQ j)
  have hne : E.Nonempty := backwardCylinder_nonempty P₁ hr
  have hab : BddAbove (u '' E) := (hK.bddAbove_image huc).mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := (hK.bddBelow_image huc).mono (image_mono subset_closure)
  have hos : Tendsto (fun j => Holder.oscillationOn (w j) E) atTop (𝓝 (Holder.oscillationOn u E)) := by
    have ht := (ht.mono subset_closure)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp ht) (ε / 3) (by positivity)] with j hj
    have he : ∀ P ∈ E, |w j P - u P| ≤ ε / 3 := by
      intro P hP
      simpa only [Real.dist_eq, abs_sub_comm] using (hj P hP).le
    have hwa : BddAbove (w j '' E) := by
      refine ⟨sSup (u '' E) + ε / 3, ?_⟩
      rintro _ ⟨P, hP, rfl⟩
      have h := (abs_le.mp (he P hP)).2
      have h' := le_csSup hab (mem_image_of_mem u hP)
      linarith
    have hwb : BddBelow (w j '' E) := by
      refine ⟨sInf (u '' E) - ε / 3, ?_⟩
      rintro _ ⟨P, hP, rfl⟩
      have h := (abs_le.mp (he P hP)).1
      have h' := csInf_le hbb (mem_image_of_mem u hP)
      linarith
    have h1 := corrector_oscillation_le hne hab hbb he
    have h2 := corrector_oscillation_le (u := w j) (w := u) hne hwa hwb
      (fun P hP => by rw [abs_sub_comm]; exact he P hP)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hos0 := Holder.oscillationOn_nonneg hne hab hbb
  have h34 : backwardCylinder P₁ (3 * r / 4) ⊆ E :=
    Holder.backwardCylinder_radius_mono P₁ (by positivity) (by linarith)
  have h12 : backwardCylinder P₁ (r / 2) ⊆ E :=
    Holder.backwardCylinder_radius_mono P₁ (by positivity) (by linarith)
  refine ⟨?_, ?_⟩
  · intro P hP
    let s := fun x : PDE.Vec d => (⟨P.time, x, P.velocity⟩ : KineticPoint d)
    have hsc : Continuous s := KineticPoint.continuous_mk continuous_const continuous_id
      continuous_const
    have hpre := (isOpen_backwardCylinder P₁ (3 * r / 4) (by positivity)).preimage hsc
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hpre.mem_nhds hP)
    have hsq : closedBall P.position ρ ⊆ s ⁻¹' closure E :=
      fun x hx => subset_closure (h34 (hball hx))
    have hfs j x hx := (hestj j).1 (s x) (h34 (hball hx))
    have hconv := (ht.comp s).mono hsq
    have hcont :=
      huc.comp hsc.continuousOn hsq
    let b := fun m => C_m m / r ^ (3 * m)
    have hb m : 0 ≤ b m := div_nonneg (hCm m) (pow_pos hr _).le
    have hbounds : ∀ j m, 1 ≤ m → ∀ x ∈ closedBall P.position ρ,
        ‖iteratedFDeriv ℝ m (physicalPositionSlice (w j) P) x‖ ≤
          b m * Holder.oscillationOn (w j) E := by
      intro j m hm x hx
      have hh := (hestj j).2.1 m hm (s x) (hball hx)
      have hp : 0 < r ^ (3 * m) := pow_pos hr _
      change r ^ (3 * m) * ‖iteratedFDeriv ℝ m
        (physicalPositionSlice (w j) P) x‖ ≤ C_m m * Holder.oscillationOn (w j) E at hh
      have hh' : ‖iteratedFDeriv ℝ m (physicalPositionSlice (w j) P) x‖ ≤
          (C_m m * Holder.oscillationOn (w j) E) / r ^ (3 * m) :=
        (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
      convert hh' using 1; dsimp only [b]; ring
    obtain ⟨hsp, hbd⟩ := corrector_derivative_estimates
      (fun j => physicalPositionSlice (w j) P) (physicalPositionSlice u P)
      P.position ρ hρ hfs hconv hcont b hb
      (fun j => Holder.oscillationOn (w j) E) (Holder.oscillationOn u E) hos0 hos hbounds
    refine ⟨hsp, fun m hm => ?_⟩
    have hh := hbd m hm
    have hp : 0 < r ^ (3 * m) := pow_pos hr _
    have hh' := mul_le_mul_of_nonneg_left hh hp.le
    convert hh' using 1
    dsimp only [b, E]
    field_simp
  · apply corrector_holder_limit ((ht.mono subset_closure).mono h12) hos P₁
    intro j P hP Q hQ
    exact (hestj j).2.2 P hP Q hQ

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
