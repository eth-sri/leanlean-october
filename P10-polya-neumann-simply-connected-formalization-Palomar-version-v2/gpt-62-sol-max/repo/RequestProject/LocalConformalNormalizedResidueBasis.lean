module

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalRegularObservation
public import RequestProject.NeumannResonanceDimension

/-! A factorization of the Neumann pole needs only a bound on its rank.
Extend a basis factorization of the genuine form kernel by zero modes. -/

@[expose] public section

noncomputable section
namespace PolyaNeumann

open Set
open scoped InnerProductSpace

/-- Variational multiplicity at the reference energy. -/
def originalNeumannMultiplicity (Ω : Set ℂ) (E : ℝ) : ℕ :=
  {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard.toNat

/-- The Neumann residue has a Gram representation of length at most the
multiplicity in the variational sequence. -/
theorem normalizedNeumannResidue_factorization {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    ∃ w : Fin (originalNeumannMultiplicity Ω E) → L2Z,
      normalizedNeumannResidue Q E = ∑ j, InnerProductSpace.rankOne ℂ (w j) (w j) := by
  let H := h1ResonantSpace Ω E
  letI := finiteDimensional_h1ResonantSpace hb hL E
  let b := stdOrthonormalBasis ℂ H
  let u := fun j => (Real.sqrt (E + 1) : ℂ) • Q (b j)
  have hfin : {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.Finite := by
    refine (finite_setOf_neumannEigenvalue_lt hb hL (E := ENNReal.ofReal (E + 1))
      ENNReal.ofReal_ne_top).subset fun j hj => ?_
    change neumannEigenvalue Ω j = _ at hj
    rw [mem_setOf_eq, hj, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  have hd : Module.finrank ℂ H ≤ originalNeumannMultiplicity Ω E := by
    simpa [originalNeumannMultiplicity, H] using ENat.toNat_le_toNat
      (h1ResonantSpace_multiplicity_le hb hL hE) hfin.encard_lt_top.ne
  let f := Fin.castLEEmb hd
  let w := Function.extend f u 0
  have hw (j : Fin (Module.finrank ℂ H)) : w (f j) = u j := f.injective.extend_apply _ _ _
  refine ⟨w, (normalizedNeumannResidue_eq_sum_rankOne Q hE b).trans ?_⟩
  change (∑ j, InnerProductSpace.rankOne ℂ (u j) (u j)) = _
  calc
    _ = ∑ j ∈ Finset.univ.map f, InnerProductSpace.rankOne ℂ (w j) (w j) := by
      simp [hw]
    _ = _ := Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
      have hj' : ¬ ∃ i, f i = j := by simpa using hj
      simp [w, Function.extend_apply' _ _ _ hj']

end PolyaNeumann
end
