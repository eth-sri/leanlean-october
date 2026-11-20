module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.KernelDefinitions
public import DedekindZetaZeroFree.Moments.Probes.PoissonOrbitFormula
public import DedekindZetaZeroFree.Adeles.Characters.TraceConductor

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

section

variable (P : PrincipalData A σ η hS) (N : MellinNormalizationData A σ η hS P)

def poissonNormalization :
    PoissonNormalizedRow.Normalization A σ η hS P where
  localMeasure := N.finiteMeasure
  localHaar := N.finiteHaar
  localNormalization := N.localNormalization
  traceConductor := by
    have hc := PrincipalProbeConstruction.canonical_trace_conductor A
    intro v y
    simpa only [N.sameFiniteTrace] using hc v y
  containsDifferent := N.containsDifferent
  sameMeasure := by
    rw [N.sameAdditiveMeasure]
    rfl

include N in
theorem finiteTrace_nontrivial : ∀ v, P.finiteTrace v ≠ 1 := by
  intro v h
  obtain ⟨x, hx⟩ := PoissonS.ScaleShift.traceConductor_nontrivial
    F A.Sf P.finiteTrace (poissonNormalization P N).traceConductor v
  exact hx (by rw [h]; rfl)

end

theorem probe_eq_orbit_sum (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : Function.LeftInverse (ProbeOrbitNormSum.orbitMk A) ρ)
    (X Y Z : {x : ℝ // 0 < x}) :
    Summable (fun i : ProbePoissonOrbitFormula.Index A =>
      ‖ProbePoissonOrbitFormula.term A σ η hS P ρ X.val Y.val Z.val i‖) ∧
    principalProbe A σ η hS P X Y Z =
      ∑' i : ProbePoissonOrbitFormula.Index A,
        ProbePoissonOrbitFormula.term A σ η hS P ρ X.val Y.val Z.val i := by
  have h := ProbePoissonOrbitFormula.exact_orbit_formula A σ η hS P
    (poissonNormalization P N) (finiteTrace_nontrivial P N) N.disintegration
    ρ hρ X.val Y.val Z.val X.property Y.property Z.property
  exact ⟨h.1, h.2⟩

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
