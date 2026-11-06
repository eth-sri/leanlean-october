module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import PDEFoundation.Ambient.Basic

/-! # Canonical spectral measurability for fields continuous off the origin -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- Ramp functional calculus is continuous on a set supporting a Hermitian field. -/
theorem continuousOn_spectralRamp {X : Type*} [TopologicalSpace X] {d }
    (M : X → PDE.Mat d) (S ) (hM : ContinuousOn M S)
    (hherm : ∀ x ∈ S, (M x).IsHermitian) (n : ℕ) :
    ContinuousOn (fun x => cfc (positiveSpectralRamp n) (M x)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
  exact continuous_spectralRamp (fun x : S => M x) hM (fun x => hherm x x.property) n

/- Continuous positive-part calculus is continuous on any Hermitian field domain. -/
theorem continuousOn_positiveSpectralMass {X : Type*} [TopologicalSpace X] {d }
    (M : X → PDE.Mat d) (S ) (hM : ContinuousOn M S)
    (hherm : ∀ x ∈ S, (M x).IsHermitian) :
    ContinuousOn (fun x => positiveSpectralMass (M x)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
  exact continuous_positiveSpectralMass (fun x : S => M x) hM (fun x => hherm x x.property)

/- Positive spectral projections of punctured continuous Hermitian fields are measurable. -/
theorem measurable_positiveSpectralProjection_punctured {d }
    (M : PDE.Vec d × PDE.Vec d → PDE.Mat d) (hM : ContinuousOn M ({0}ᶜ))
    (hherm : ∀ q, (M q).IsHermitian) :
    Measurable (fun q => positiveSpectralProjection (M q)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_of_continuousOn_compl_singleton 0
      (continuousOn_spectralRamp M _ hM (fun q _ => hherm q) n))
  apply tendsto_pi_nhds.mpr
  intro q
  have heq : (fun n : ℕ => cfc (positiveSpectralRamp n) (M q)) =ᶠ[atTop]
      (fun _ => positiveSpectralProjection (M q)) := by
    let M := (M q)
    have hM := (hherm q)
    have hh : ∀ᶠ n : ℕ in atTop, ∀ i : Fin d,
        positiveSpectralRamp n (hM.eigenvalues i) =
          positiveSpectralIndicator (hM.eigenvalues i) :=
      eventually_all.mpr fun i => positiveSpectralRamp_eventually (hM.eigenvalues i)
    filter_upwards [hh] with n hn
    apply cfc_congr
    intro t ht
    rw [hM.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    exact hn i
  exact tendsto_const_nhds.congr' heq.symm

/- Entries of the canonical trace solver are measurable for punctured continuous data. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
