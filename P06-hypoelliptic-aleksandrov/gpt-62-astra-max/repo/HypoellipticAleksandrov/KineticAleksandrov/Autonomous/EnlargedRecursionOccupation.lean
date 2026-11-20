module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFullSpace

/-! # Domination of finite enlarged active occupations by full-space evolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (c : Clock) (P : Point) (J : Interval) (T : ℝ) (hT : 0 < T)
include hT

/-- Every killed strip occupation is dominated by the full-space physical occupation. -/
theorem enlarged_stripGreen_le_fullspace
    (hv : P.velocity 0 ∈ H.carrier) :
    stripGreen hlam hLam A H (P.time + T)
      ⟨P, WithTop.coe_lt_coe.mpr (by linarith), hv⟩ ≤
      enlargedFullSpaceOccupation hlam hLam A P T := by
  let e : StripPole H ((P.time + T : ℝ)) :=
    ⟨P, WithTop.coe_lt_coe.mpr (by linarith), hv⟩
  let E := fullSpaceEvolution hlam hLam A
  apply Measure.le_iff.mpr
  intro B hB
  let F : Point → ℝ≥0∞ := B.indicator 1
  have hF : Measurable F := measurable_one.indicator hB
  rw [← lintegral_indicator_one hB, ← lintegral_indicator_one hB]
  change (∫⁻ p, F p ∂stripGreen hlam hLam A H (P.time + T) e) ≤
    ∫⁻ p, F p ∂enlargedFullSpaceOccupation hlam hLam A P T
  rw [stripGreen_lintegral hlam hLam A H (P.time + T) e F hF,
    enlargedFullSpaceOccupation_elapsed_lintegral hlam hLam A P T hT F hF]
  have hh : stripHorizon ((P.time + T : ℝ)) P.time = ENNReal.ofReal T := by
    simp [stripHorizon]
  let p := stripPoleState H ((P.time + T : ℝ)) e
  change (∫⁻ t, ∫⁻ w, F (elapsedPhysicalPoint P.time (t, w))
    ∂((stripEvolution hlam hLam A H).2).master (elapsedQuery P.time p t)
    ∂elapsedVolume (stripHorizon ((P.time + T : ℝ)) P.time)) ≤
      ∫⁻ t : ElapsedTime (ENNReal.ofReal T),
        ∫⁻ z, F (enlargedTerminalPoint (P.time + t.1) z)
          ∂kernelXV E (Real.toNNReal t.1) (P.position 0, P.velocity 0)
          ∂elapsedVolume (ENNReal.ofReal T)
  rw [hh]
  apply lintegral_mono
  intro t
  have hm := (strip_kernel_le_fullspace hlam hLam A E (fullSpaceEvolution_spec hlam hLam A) H (stripEvolution hlam hLam A H) (stripEvolution_spec hlam hLam A H)) (elapsedQuery P.time (stripPoleState H (P.time + T) e) t)
  have hi := lintegral_mono' hm (f := fun w => F ⟨P.time + t.1, w.2, w.1⟩) le_rfl
  have hq : largeQueryOfSmall (strip_subset_fullspace H)
      (elapsedQuery P.time (stripPoleState H (P.time + T) e) t) =
      wholeSpaceQuery P.time (P.time + t.1) (by linarith [t.2.1]) P.velocity P.position := rfl
  exact hi.trans_eq (enlargedFullSpace_native_elapsed_lintegral
    hlam hLam A P t.1 t.2.1.le F hF)

/-- Every finite enlarged active sum is dominated by the actual full-space occupation. -/
theorem enlarged_active_occupation_le_fullspace
    (P : Point) (hv : P.velocity 0 ∈ J.carrier) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      enlargedActivePiece hlam hLam A c J P.time (P.time + T) P n) ≤
        enlargedFullSpaceOccupation hlam hLam A P T := by
  classical
  have h := (enlarged_piece_domination hlam hLam A c J P.time (P.time + T) P ⟨le_rfl, by linarith, hv⟩ N).2
  apply (h.trans Measure.restrict_le_self).trans
  have hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion (P.time + T) :=
    ⟨by linarith, by simpa [Interval.toFiniteUnion_carrier] using hv⟩
  change (if h : P ∈ enlargedVisitPoleSet J.toFiniteUnion (P.time + T) then
    finiteUnionGreen hlam hLam A J.toFiniteUnion (P.time + T)
      (enlargedVisitPole _ _ ⟨P, h⟩) else 0) ≤ _
  rw [dite_eq_left hp]
  apply enlarged_stripGreen_le_fullspace <;> assumption

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
