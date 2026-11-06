
import proofs.HordijkSteelThreshold.SourceTerminalRAF




namespace HordijkSteelThreshold

open Classical RAF.Polymer RAF.Concrete

theorem raf_escape_or_seed {M R : Type*} [Fintype R] [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (ω : R → M → Prop) (length : M → ℕ) (K : ℕ)
    (hraf : ∃ S, IsRevRAF Q (fun x r => ω r x) S) :
    (∃ x, (∃ k, x ∈ revClosureAt Q (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ) k) ∧
      K < length x) ∨ ∃ x r, length x ≤ K ∧ RevSeedReaction Q r ∧ ω r x := by
  obtain ⟨S, hne, hfg, hcat⟩ := hraf
  obtain ⟨r, hr, hseed⟩ := (show ∃ r ∈ S, RevSeedReaction Q r from by
                             grind [RevFoodGenerated, RevSeedReaction, ← RAF.Concrete.revClosureAt_eq_food_of_no_seed])
  obtain ⟨x, k, hx, hxr⟩ := hcat r hr
  have hS : S ⊆ RAFEmergenceApprox.Generic.catalystActive ω Finset.univ := by
    grind [RevReflexivelyAutocatalytic, RAFEmergenceApprox.Generic.catalystActive, RAFEmergenceApprox.Generic.catalystPoolOpen]
  have hx' := revClosureAt_mono_reactions Q hS k hx
  grind


open MeasureTheory unitInterval

theorem ambient_coordinate_probability (n : ℕ) (lambda : ℝ) (z : AmbientCoord n) :
    ambientPiMeasure n lambda {ω | ω z} = toNNReal (catalysisP n lambda) := by
  
  have he := congrArg (fun μ : Measure Prop => μ {True}) (Measure.infinitePi_map_eval (fun _ : AmbientCoord n =>
                                                           ambientCoordLaw (catalysisP n lambda)) z)
  rw [Measure.map_apply (measurable_pi_apply z) (MeasurableSet.singleton True)] at he
  simpa [ambientPiMeasure, ambientCoordLaw] using he

def boundedSeedCatalystEvent (n K : ℕ) : Set (AmbientCoord n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ r : Reaction n,
    molLength x ≤ K ∧ RevSeedReaction (binaryPolymerCRS n 2) r ∧ ω (x,r)}

end HordijkSteelThreshold
