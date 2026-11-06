module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalExtension

/-! # The unique positive contraction functional on the full closed ball trace -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set SectionTwo Evolution TheoremA Parabolic
open scoped CompactlySupported

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

variable (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) (f : boundaryProbeSubmodule d)

/-- Smooth probe values obey the boundary supremum contraction. -/
theorem boundaryProbeValueLinear_bound  (c : ℝ)
    (_hc : 0 ≤ c) (hbd : ∀ Q, |boundaryProbeCcLinear P.1.time T.1 v₀ R f Q| ≤ c) :
    |boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T f| ≤ c := by
  have hp : P.1 ∈ localClosedStrip P.1.time T.1 v₀ R :=
    ⟨le_rfl, T.2.le, subset_closure P.2⟩
  have hu := ballBoundarySolution_le_of_trace hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 _ (boundaryProbePhysical_regular f).1
    (boundaryProbePhysical_regular f).2.2 c
    (fun Q hQ => (le_abs_self _).trans (hbd ⟨Q, hQ⟩)) P.1 hp
  have hn := ballBoundarySolution_le_of_trace hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 _ (boundaryProbePhysical_regular _).1
    (boundaryProbePhysical_regular (-f)).2.2 c (fun Q hQ => by
      exact (neg_le_abs _).trans (hbd ⟨Q, hQ⟩)) P.1 hp
  have heq := (boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T).map_neg f
  change boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T _ ≤ c at hn
  rw [heq] at hn
  exact abs_le.mpr ⟨neg_le.mp hn, hu⟩

/-- Nonnegative trace data have nonnegative actual homogeneous values. -/
theorem boundaryProbeValueLinear_nonneg 
    (hbd : ∀ Q, 0 ≤ boundaryProbeCcLinear P.1.time T.1 v₀ R f Q) :
    0 ≤ boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T f := by
  have hp : P.1 ∈ localClosedStrip P.1.time T.1 v₀ R :=
    ⟨le_rfl, T.2.le, subset_closure P.2⟩
  have hn := ballBoundarySolution_le_of_trace hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 _ (boundaryProbePhysical_regular _).1
    (boundaryProbePhysical_regular (-f)).2.2 0 (fun Q hQ => by
      exact neg_nonpos.mpr (hbd ⟨Q, hQ⟩)) P.1 hp
  have heq := (boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T).map_neg f
  change boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T _ ≤ 0 at hn
  simp_all

/-- Existence and uniqueness of the positive contraction extending the actual probe values. -/
theorem existsUnique_ballBoundaryFunctional  :
    ∃! ℓ : C_c(localTrace P.1.time T.1 v₀ R, ℝ) →ₚ[ℝ] ℝ,
      (∀ (f : C_c(localTrace P.1.time T.1 v₀ R, ℝ)) (c : ℝ), 0 ≤ c →
        (∀ Q, |f Q| ≤ c) → |ℓ f| ≤ c) ∧
      ∀ f : boundaryProbeSubmodule d, ℓ (boundaryProbeCcLinear P.1.time T.1 v₀ R f) =
        boundaryProbeValueLinear hH hLE hd hlam hLam B hB v₀ hR P T f := by
  obtain ⟨ℓ, hbd, hagree⟩ := exists_positive_extension_of_dense
    _
    _
    (boundaryProbeValueLinear_bound hH hLE hd hlam hLam B hB v₀ hR P T)
    (boundaryProbeValueLinear_nonneg hH hLE hd hlam hLam B hB v₀ hR P T)
    (boundaryProbeCc_sq P.1.time T.1 v₀ R) (boundaryProbeCc_dense P.1.time T.1 v₀ R)
  refine ⟨ℓ, ⟨hbd, hagree⟩, fun k hk => ?_⟩
  have hlin : k.toLinearMap = ℓ.toLinearMap := eq_of_bounded_of_dense
    (boundaryProbeCcLinear P.1.time T.1 v₀ R) k.toLinearMap ℓ.toLinearMap hk.1 hbd
    (fun f => (hk.2 f).trans (hagree f).symm) (boundaryProbeCc_dense P.1.time T.1 v₀ R)
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
