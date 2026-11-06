module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierFactors
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierIntegral

/-! # Fourier composition through the genuine later exit operator -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The genuine restart Fourier measure is the killed Fourier projection composed with
actual later exits, with the exact unit centering phase. -/
theorem ballExitRestart_fourier_apply
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1}) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (hE : MeasurableSet E) :
    exitFourier ((ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H).map
      (exitCoordinates P.1 v₀)) ξ E =
      exitFourierStepPhase P.1 H.1 v₀ ξ *
        ∫ᵛ v, ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR
          H.1 T.1 H.2.2 ξ E v
          ∂[ContinuousLinearMap.mul ℝ ℂ;
            fourierProjection (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
              (ballEvolutionQuery P ⟨H.1, H.2.1⟩) ξ] := by
  let K := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
  let q := ballEvolutionQuery P ⟨H.1, H.2.1⟩
  let f := ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR H.1 T.1 H.2.2 ξ E
  have hfm := measurable_ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR
    H.1 T.1 H.2.2 ξ E hE
  have hfb : ∃ C : ℝ, ∀ v, ‖f v‖ ≤ C := ⟨1, fun v =>
    norm_ballLaterExitFourierTest_le_one hH hLE hd hlam hLam B hB v₀ hR
      H.1 T.1 H.2.2 ξ E v⟩
  rw [exitFourier_map_exitCoordinates_apply _ P.1 v₀ ξ E hE,
    ballExitRestart_integral_complex hH hLE hd hlam hLam B hB v₀ hR P T H
      _ (measurable_exitFourierTest _ _ _ hE)
      ⟨1, norm_exitFourierTest_le_one _ _ _ _⟩,
    fourierProjection_integral_complex K q ξ _ (fourierProjection_spec K q ξ) f hfm hfb]
  change _ = exitFourierStepPhase P.1 H.1 v₀ ξ *
    ∫ w, f w.1 * fourierPhase ξ P.1.position w
      ∂K.master (evolutionQueryOfState _ _
        P.1.time H.1 H.2.1.le _)
  rw [master_integral_eq_fiber K (PDE.isOpen_euclideanBall v₀ R).measurableSet
    P.1.time H.1 H.2.1.le _
    (fun w => f w.1 * fourierPhase ξ P.1.position w)
    ((hfm.comp measurable_fst).mul (continuous_fourierPhase ξ _).measurable),
    ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  let W := (ballStateStart H.1 w).1
  have heq : (fun Q => exitFourierTest P.1 v₀ ξ E Q) =
      fun Q => exitFourierStepPhase P.1 H.1 v₀ ξ *
        fourierPhase ξ P.1.position w.1 * exitFourierTest W v₀ ξ E Q :=
    funext (fun Q => exitFourierTest_factor P.1 W Q v₀ ξ E)
  rw [heq]
  dsimp only
  rw [integral_const_mul, ← exitFourier_map_exitCoordinates_apply _ W v₀ ξ E hE]
  have hfvalid := ballLaterExitFourierTest_valid hH hLE hd hlam hLam B hB v₀ hR
    H.1 T.1 H.2.2 ξ E ⟨w.1.1, w.2.1⟩
  rw [ballLaterExitFourier_eq_state] at hfvalid
  dsimp only [f]
  rw [hfvalid]
  dsimp only [ballExit]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
