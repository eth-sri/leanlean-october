module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import RequestProject.CutPhase
public import RequestProject.BasePoint

/-!
# Cayley rank bounds under unitary conjugation and change of base point

Finite orthonormal eigenvector families can be transported by a linear isometric
equivalence. Consequently their Cayley rank bound is unchanged by unitary
conjugation. For a periodic Lipschitz boundary curve, this applies to the
monodromies obtained by starting its transport at different parameters.
-/

@[expose] public section

noncomputable section

open Set
open scoped Real

namespace PolyaNeumann

section Intertwining

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- An isometric intertwiner preserves the bound on finite orthonormal families
of eigenvectors above a Cayley threshold. -/
theorem cayleyRankBound_iff_of_intertwining (e : H ≃ₗᵢ[ℂ] G)
    U V
    (hUV : ∀ x, V (e x) = e (U x)) A m :
    CayleyRankBound U A m ↔ CayleyRankBound V A m := by
  constructor
  · intro hU n v t hv ht hEig hA
    refine hU n (fun k => e.symm (v k)) t
      (hv.comp_linearIsometryEquiv e.symm) ht ?_ hA
    intro k
    apply e.injective
    calc
      _ = _ := by
        simpa using
          (hUV (e.symm (v k))).symm
      _ = _ := hEig k
      _ = _ := by
        simp
  · intro hV n v t hv ht hEig hA
    refine hV n (fun k => e (v k)) t
      (hv.comp_linearIsometryEquiv e) ht ?_ hA
    intro k
    rw [hUV, hEig k, LinearIsometryEquiv.map_smul]

end Intertwining

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugating an operator by a unitary preserves its Cayley rank bound. -/
theorem cayleyRankBound_unitary_conj_iff U Q
    (hQ : Q ∈ unitary (H →L[ℂ] H)) (A : ℝ) m :
    CayleyRankBound U A m ↔
      CayleyRankBound (Q * U * ContinuousLinearMap.adjoint Q) A m := by
  let e := Unitary.linearIsometryEquiv ⟨Q, hQ⟩
  refine cayleyRankBound_iff_of_intertwining e U
    (Q * U * ContinuousLinearMap.adjoint Q) ?_ A m
  intro x
  change Q (U (ContinuousLinearMap.adjoint Q (Q x))) = Q (U x)
  rw [show ContinuousLinearMap.adjoint Q (Q x) = x by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : H →L[ℂ] H => T x) (show ContinuousLinearMap.adjoint Q * Q = 1 by
        simpa [ContinuousLinearMap.star_eq_adjoint] using
          Unitary.star_mul_self_of_mem hQ)]

end Unitary

/-- Transfer a Cayley rank estimate established at a chosen starting point back
to the original parameterization. -/
theorem cayleyRankBound_of_rebased_transport  
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * π)) 
     (hW : IsTransport γ E W)
     (ht : t ∈ Icc 0 (2 * π)) 
    (hW' : IsTransport (fun θ => γ (θ + t)) E W')  
    (h : CayleyRankBound (monodromy W') A m) :
    CayleyRankBound (monodromy W) A m :=
  (show CayleyRankBound (monodromy W) A m ↔ CayleyRankBound (monodromy W') A m by
    rw [monodromy_basepoint hK hper hW ht hW']
    exact cayleyRankBound_unitary_conj_iff (monodromy W) (W t) (by
      obtain ⟨h1, h2⟩ := volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
        (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 t ht
      exact Unitary.mem_iff.mpr ⟨h1, h2⟩) A m).mpr h

end PolyaNeumann

end
