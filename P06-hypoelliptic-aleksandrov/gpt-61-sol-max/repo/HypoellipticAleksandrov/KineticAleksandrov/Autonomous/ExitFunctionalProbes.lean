module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalProbe
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.Ring
public import PDEFoundation.Calculus.RegularityOrder




/-! # Smooth ambient exit probes and their actual compact kinetic sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped CompactlySupported

/-- The physical coordinate homeomorphism associated to the native Euclidean packing. -/
def reconstructionPhysicalHomeomorph : EvolutionVec 1 ≃ₜ Point :=
  (evolutionHomeomorph 1).trans (sectionTwoHomeomorph 1)

/-- The inverse map packs physical velocity before physical position. -/
@[simp] theorem reconstructionPhysicalHomeomorph_symm_apply (p : Point) :
    reconstructionPhysicalHomeomorph.symm p = packPoint p.time p.velocity p.position := rfl

/-- Ambient smooth compact scalar functions form the exit probe vector space. -/
def exitProbeSubmodule : Submodule ℝ (EvolutionVec 1 → ℝ) where
  carrier := {f | ContDiff ℝ PDE.smoothOrder f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun _c _f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

variable (f : exitProbeSubmodule)

/-- The physical test supplied by an ambient exit probe. -/
def exitProbePhysical  : Point → ℝ :=
  f.1 ∘ reconstructionPhysicalHomeomorph.symm

/-- A physical probe is globally continuous and compactly supported. -/
theorem exitProbePhysical_continuous_compact  :
    Continuous (exitProbePhysical f) ∧ HasCompactSupport (exitProbePhysical f) :=
  ⟨f.2.1.continuous.comp reconstructionPhysicalHomeomorph.symm.continuous,
    f.2.2.comp_homeomorph reconstructionPhysicalHomeomorph.symm⟩

private theorem probe_native_smooth  :
    ContDiff ℝ PDE.smoothOrder (exitProbePhysical f ∘ evolutionHomeomorph 1) := by
  have h := f.2.1.comp ((evolutionProdCLE 1).symm.contDiff.comp
    ((contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)).comp
      (evolutionProdCLE 1).contDiff))
  assumption

/-- Smooth ambient probes supply genuine global physical C112 tests. -/
theorem exitProbePhysical_isKineticC112On  (D : Set Point)
    (hD : IsOpen D) : IsKineticC112On (exitProbePhysical f) D :=
  isKineticC112On_of_contDiffOn hD (probe_native_smooth f).contDiffOn

private theorem probe_derivative_smooth {f : EvolutionVec 1 → ℝ}
    (hf : ContDiff ℝ PDE.smoothOrder f) (v : EvolutionVec 1) :
    ContDiff ℝ PDE.smoothOrder (fun x => fderiv ℝ f x v) :=
  (hf.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (f : exitProbeSubmodule)

private theorem probe_operator_formula  :
    transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1 =
      fun x => fderiv ℝ f.1 x basisT +
        A.a (transportedCoord 1 x 0) (diffusedCoord 1 x 0) *
          fderiv ℝ (fun y => fderiv ℝ f.1 y (basisV (0 ))) x (basisV (0 )) +
        diffusedCoord 1 x 0 * fderiv ℝ f.1 x (basisZ (0 )) := by
  ext <;> simp_all [transportedOperator, evolutionCoefficient, identityDrift] <;> ring

/-- The actual packed kinetic operator of a smooth compact probe is smooth and compact. -/
theorem exitProbe_operator_smooth_compact  :
    ContDiff ℝ PDE.smoothOrder (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1) ∧
    HasCompactSupport (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1) := by
  let sharedTerm_74dee2ac18 := ((basisV (0 : Fin 1)))
  have ht := probe_derivative_smooth f.2.1 basisT
  have hv := probe_derivative_smooth f.2.1 sharedTerm_74dee2ac18
  have hz := probe_derivative_smooth f.2.1 (basisZ (0 ))
  have hh := probe_derivative_smooth hv sharedTerm_74dee2ac18
  have hvc : HasCompactSupport (fun x => fderiv ℝ f.1 x sharedTerm_74dee2ac18) :=
    f.2.2.fderiv_apply ℝ _
  have hhc := hvc.fderiv_apply ℝ sharedTerm_74dee2ac18
  have haa : ContDiff ℝ PDE.smoothOrder (fun x =>
      A.a (transportedCoord 1 x 0) (diffusedCoord 1 x 0)) :=
    A.smooth.comp (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (transportedCoord 1).contDiff).prodMk
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (diffusedCoord 1).contDiff))
  rw [probe_operator_formula A f]
  constructor
  · simpa only [Function.comp_def] using! (ht.add (haa.mul hh)).add
      (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (diffusedCoord 1).contDiff).mul hz)
  · exact ((f.2.2.fderiv_apply ℝ basisT).add hhc.mul_left).add
      (f.2.2.fderiv_apply ℝ (basisZ (0 ))).mul_left

/-- The scalar physical operator is exactly the packed probe operator under the fixed map. -/
theorem exitProbePhysical_operator  (p : Point) :
    forwardScalarOperator A.a (exitProbePhysical f) p =
      transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1
        (reconstructionPhysicalHomeomorph.symm p) := by
  let x := reconstructionPhysicalHomeomorph.symm p
  have heq : (exitProbePhysical f ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1 = f.1 := by
    funext y
    exact congrArg f.1 (reconstructionPhysicalHomeomorph.symm_apply_apply y)
  have hs : ContDiffAt ℝ 2 ((exitProbePhysical f ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x := by
    rw [heq]
    exact (f.2.1.of_le (by simp)).contDiffAt
  have hop := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hs
  rw [heq, reconstruction_scalar_operator_swap] at hop
  have hx : sectionTwoPoint (evolutionHomeomorph 1 x) = p :=
    reconstructionPhysicalHomeomorph.apply_symm_apply p
  rw [hx] at hop
  exact hop.symm

/-- A compact probe and its actual kinetic operator satisfy the bounded source hypotheses. -/
theorem exitProbePhysical_bounded_source  :
    ∃ M : ℝ, ∀ p, |exitProbePhysical f p| ≤ M ∧
      |forwardScalarOperator A.a (exitProbePhysical f) p| ≤ M := by
  obtain ⟨B, hB⟩ := f.2.2.exists_bound_of_continuous f.2.1.continuous
  obtain ⟨C, hC⟩ := (exitProbe_operator_smooth_compact A f).2.exists_bound_of_continuous
    (exitProbe_operator_smooth_compact A f).1.continuous
  refine ⟨max B C, fun p => ⟨(hB _).trans (le_max_left _ _), ?_⟩⟩
  rw [exitProbePhysical_operator A f p]
  exact (hC _).trans (le_max_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
