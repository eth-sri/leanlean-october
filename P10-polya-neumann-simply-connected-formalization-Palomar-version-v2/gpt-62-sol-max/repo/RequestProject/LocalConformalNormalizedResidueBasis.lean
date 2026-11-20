module

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalHerglotzDensity
public import RequestProject.TraceReparamReverse

/-!
The true normalized Neumann pole in a basis indexed by the multiplicity
of the original physical Neumann sequence.  The physical L2 normalization
absorbs the shifted H1 factor E+1.  Actual arclength reparametrization
identifies its compatibility conditions with the original physical loads.
This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric
open scoped InnerProductSpace ComplexConjugate

/-- The multiplicity is taken from the original physical Neumann
sequence; its finiteness and its equality to the true kernel dimension
are proved below. -/
def originalNeumannMultiplicity (Ω : Set ℂ) (E : ℝ) : ℕ :=
  {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard.toNat

theorem originalNeumannMultiplicity_eq_finrank {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    originalNeumannMultiplicity Ω E = Module.finrank ℂ (h1ResonantSpace Ω E) := by
  unfold originalNeumannMultiplicity
  rw [← h1ResonantSpace_multiplicity_eq hb hL hE]
  exact ENat.toNat_coe _

/-- A genuine orthonormal H1 basis, with exactly the multiplicity
specified by the original variational Neumann spectrum. -/
def originalNeumannResonanceH1Basis {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    OrthonormalBasis (Fin (originalNeumannMultiplicity Ω E)) ℂ (h1ResonantSpace Ω E) := by
  letI : FiniteDimensional ℂ (h1ResonantSpace Ω E) := finiteDimensional_h1ResonantSpace hb hL E
  exact (stdOrthonormalBasis ℂ (h1ResonantSpace Ω E)).reindex
    (finCongr (originalNeumannMultiplicity_eq_finrank hb hL hE).symm)

/-- The physical eigenfunction lifted to the actual H1 graph space,
normalized in the original L2 space. -/
def originalNeumannResonanceH1Mode {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : NeumannH1 Ω :=
  (Real.sqrt (E + 1) : ℂ) • (originalNeumannResonanceH1Basis hb hL hE j : NeumannH1 Ω)

/-- The normalized boundary vector is the true half trace of the
original L2-normalized physical eigenfunction. -/
def normalizedNeumannResonanceMode {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z)
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : L2Z :=
  Q (originalNeumannResonanceH1Mode hb hL hE j)

theorem normalizedNeumannResonanceMode_eq_scaled {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z)
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) :
    normalizedNeumannResonanceMode Q hb hL hE j =
      (Real.sqrt (E + 1) : ℂ) • Q (originalNeumannResonanceH1Basis hb hL hE j) := by
  simp only [normalizedNeumannResonanceMode, originalNeumannResonanceH1Mode, map_smul]

theorem normalizedNeumannResidue_eq_original_basis {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    normalizedNeumannResidue Q E = ∑ j : Fin (originalNeumannMultiplicity Ω E),
      InnerProductSpace.rankOne ℂ (normalizedNeumannResonanceMode Q hb hL hE j)
        (normalizedNeumannResonanceMode Q hb hL hE j) := by
  simpa only [normalizedNeumannResonanceMode_eq_scaled] using
    normalizedNeumannResidue_eq_sum_rankOne Q hE (originalNeumannResonanceH1Basis hb hL hE)

section ActualCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

end ActualCoordinates

end PolyaNeumann

end
