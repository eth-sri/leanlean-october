module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalRegularObservation
public import RequestProject.Reconstruction
public import RequestProject.TraceReparam

/-!
The true normalized Neumann pole in a basis indexed by the multiplicity
of the original physical Neumann sequence.  The physical L2 normalization
absorbs the shifted H1 factor E+1.  Actual arclength reparametrization
identifies its compatibility conditions with the original physical loads.
This module is part of the verified dependency chain.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric

/-- The multiplicity is taken from the original physical Neumann
sequence; its finiteness and its equality to the true kernel dimension
are proved below. -/
def originalNeumannMultiplicity Ω E  :=
  {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard.toNat

theorem originalNeumannMultiplicity_eq_finrank 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)  (hE : 0 ≤ E) :
    originalNeumannMultiplicity Ω E = Module.finrank ℂ (h1ResonantSpace Ω E) := by
  unfold originalNeumannMultiplicity
  rw [← h1ResonantSpace_multiplicity_eq hb hL hE]
  exact ENat.toNat_coe _

/-- A genuine orthonormal H1 basis, with exactly the multiplicity
specified by the original variational Neumann spectrum. -/
def originalNeumannResonanceH1Basis {Ω : PlanarSet} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    OrthonormalBasis (Fin (originalNeumannMultiplicity Ω E)) ℂ (h1ResonantSpace Ω E) := by
  letI  := finiteDimensional_h1ResonantSpace hb hL E
  exact (stdOrthonormalBasis ℂ (h1ResonantSpace Ω E)).reindex
    (finCongr (originalNeumannMultiplicity_eq_finrank hb hL hE).symm)

/-- The physical eigenfunction lifted to the actual H1 graph space,
normalized in the original L2 space. -/
def originalNeumannResonanceH1Mode {Ω : PlanarSet} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : NeumannH1 Ω :=
  (Real.sqrt (E + 1) : ℂ) • (originalNeumannResonanceH1Basis hb hL hE j : NeumannH1 Ω)

/-- The normalized boundary vector is the true half trace of the
original L2-normalized physical eigenfunction. -/
def normalizedNeumannResonanceMode {Ω : PlanarSet} (Q : NeumannH1 Ω →L[ℂ] L2Z)
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : L2Z :=
  Q (originalNeumannResonanceH1Mode hb hL hE j)

section
variable {Ω : PlanarSet} (Q : NeumannH1 Ω →L[ℂ] L2Z)
include Ω Q

section
variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
include hb hL E hE

theorem normalizedNeumannResonanceMode_eq_scaled
    (j : Fin (originalNeumannMultiplicity Ω E)) :
    normalizedNeumannResonanceMode Q hb hL hE j =
      (Real.sqrt (E + 1) : ℂ) • Q (originalNeumannResonanceH1Basis hb hL hE j) := by
  simp only [normalizedNeumannResonanceMode, originalNeumannResonanceH1Mode, map_smul]

theorem normalizedNeumannResidue_eq_original_basis :
    normalizedNeumannResidue Q E = ∑ j : Fin (originalNeumannMultiplicity Ω E),
      InnerProductSpace.rankOne ℂ (normalizedNeumannResonanceMode Q hb hL hE j)
        (normalizedNeumannResonanceMode Q hb hL hE j) := by
  simpa only [normalizedNeumannResonanceMode_eq_scaled] using
    normalizedNeumannResidue_eq_sum_rankOne Q hE (originalNeumannResonanceH1Basis hb hL hE)

end


end



end PolyaNeumann

end
