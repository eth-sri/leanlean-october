module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import RequestProject.CutPhase
public import RequestProject.BasePoint
public import RequestProject.PlanarNotation

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
    (U : H →L[ℂ] H) (V : G →L[ℂ] G)
    (hUV : ∀ x, V (e x) = e (U x)) (A : ℝ) (m : ℕ) :
    CayleyRankBound U A m ↔ CayleyRankBound V A m := by
  constructor
  · intro hU n v t hv ht hEig hA
    refine hU n (fun k => e.symm (v k)) t
      (hv.comp_linearIsometryEquiv e.symm) ht ?_ hA
    intro k
    apply e.injective
    calc
      _ = V (v k) := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (hUV (e.symm (v k))).symm
      _ = _ := hEig k
      _ = _ := by
        simp
  · intro hV n v t hv ht hEig hA
    refine hV n (fun k => e (v k)) t
      (hv.comp_linearIsometryEquiv e) ht ?_ hA
    simp [*]

end Intertwining

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugating an operator by a unitary preserves its Cayley rank bound. -/
theorem cayleyRankBound_unitary_conj_iff (U Q : H →L[ℂ] H)
    (hQ : Q ∈ unitary (H →L[ℂ] H)) (A : ℝ) (m : ℕ) :
    CayleyRankBound U A m ↔
      CayleyRankBound (Q * U * ContinuousLinearMap.adjoint Q) A m := by
  
  let e  := Unitary.linearIsometryEquiv (⟨Q, hQ⟩)
  refine cayleyRankBound_iff_of_intertwining e U
    (Q * U * ContinuousLinearMap.adjoint Q) ?_ A m
  intro x
  have hQQ : ContinuousLinearMap.adjoint Q * Q = 1 := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      Unitary.star_mul_self_of_mem hQ
  have hQQx : ContinuousLinearMap.adjoint Q (Q x) = x := by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
      congrArg (fun T : H →L[ℂ] H => T x) hQQ
  change Q (U (ContinuousLinearMap.adjoint Q (Q x))) = Q (U x)
  rw [hQQx]

end Unitary

/-- A cyclic change of the parameter's starting point preserves the Cayley rank
bound of the boundary monodromy, with the same threshold and rank. -/
theorem cayleyRankBound_monodromy_basepoint_iff {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ anglePeriod) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    {t : ℝ} (ht : t ∈ angleInterval) {W' : TransportPath}
    (hW' : IsTransport (fun θ => γ (θ + t)) E W') (A : ℝ) (m : ℕ) :
    CayleyRankBound (monodromy W) A m ↔ CayleyRankBound (monodromy W') A m := by
  
  rw [monodromy_basepoint hK hper hW ht hW']
  refine cayleyRankBound_unitary_conj_iff (monodromy W) (W t) ?_ A m
  obtain ⟨h1, h2⟩ := volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 t ht
  solve_by_elim

/-- Transfer a Cayley rank estimate established at a chosen starting point back
to the original parameterization. -/
theorem cayleyRankBound_of_rebased_transport {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ anglePeriod) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    {t : ℝ} (ht : t ∈ angleInterval) {W' : TransportPath}
    (hW' : IsTransport (fun θ => γ (θ + t)) E W') {A : ℝ} {m : ℕ}
    (h : CayleyRankBound (monodromy W') A m) :
    CayleyRankBound (monodromy W) A m :=
  (cayleyRankBound_monodromy_basepoint_iff hK hper hW ht hW' A m).mpr h

end PolyaNeumann

end
