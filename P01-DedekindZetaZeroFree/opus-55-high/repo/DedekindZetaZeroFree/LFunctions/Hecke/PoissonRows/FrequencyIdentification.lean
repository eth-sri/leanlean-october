module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Identification

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawFrequencyPublicBridge

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.PrincipalMellinComparison
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev Freq (D : FixedData S η) : Type := PrincipalMellinComparison.Frequency D.recipe

abbrev principal (D : FixedData S η) : Freq D := principalFrequency D.recipe

abbrev Raw (D : FixedData S η) : Type :=
  AllRowEuler.InitialSeparation.RawFrequency D.recipe.A

abbrev delSet {D : FixedData S η} (U : Raw D) : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows.rawDeletionSet U

theorem context_correction (D : FixedData S η) :
    D.recipe.probe.correction = D.context.correction := rfl

def Row.toFreq {D : FixedData S η} (r : D.Row) : Freq D :=
  ⟨⟨r.u, r.isRep.choose⟩, r.isRep.choose_spec⟩

@[simp] theorem Row.toFreq_val {D : FixedData S η} (r : D.Row) : (Row.toFreq r).val.val = r.u :=
  rfl

structure Bridge (D : FixedData S η) (U : Freq D → Raw D)
    (P M : Freq D → Detector.PrimitiveFrequencyCharacter F) (plus minus : Freq D → ℂ → ℂ) :
    Prop where
  raw_u : ∀ u, (U u).u = u.val.val
  finite : ∀ u, (delSet (U u)).Finite
  plus_coeff : ∀ (u : Freq D) (I : D.recipe.A.Exterior),
    AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ (U u) I =
      Detector.deletedPrimitiveIdealCoefficient F (P u) (delSet (U u)) I.val
  minus_coeff : ∀ (u : Freq D) (I : D.recipe.A.Exterior),
    AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target (U u) I =
      Detector.deletedPrimitiveIdealCoefficient F (M u) (delSet (U u)) I.val
  plus_nonprincipal : ∀ u, u ≠ principal D → ¬ (P u).character.IsPrincipal
  minus_nonprincipal : ∀ u, u ≠ principal D → ¬ (M u).character.IsPrincipal
  plus_diff : ∀ u, u ≠ principal D → DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re}
  minus_diff : ∀ u, u ≠ principal D → DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re}
  plus_series : ∀ (u : Freq D) (s : ℂ), 1 < s.re →
    plus u s = AllRowEuler.InitialSeparation.plusL D.recipe.σ (U u) s
  minus_series : ∀ (u : Freq D) (s : ℂ), 1 < s.re →
    minus u s = AllRowEuler.InitialSeparation.minusL D.recipe.σ D.recipe.target (U u) s

namespace Bridge

variable {D : FixedData S η} {U : Freq D → Raw D}
  {P M : Freq D → Detector.PrimitiveFrequencyCharacter F} {plus minus : Freq D → ℂ → ℂ}

theorem quotient_right_eq (h : Bridge D U P M plus minus) (u : Freq D) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries D.recipe u ξ w z =
      (D.recipe.L (6 * z) * plus u w *
        AllRowEuler.InitialSeparation.correctionProduct D.context (U u) ξ w z) / minus u ξ :=
  NonprincipalContinuation.Corridor.initial_continuation_agreement D.recipe D.context U plus minus
    (context_correction D) h.raw_u h.plus_series h.minus_series u ξ w z hξ hw hz

theorem plus_conductor_bound (h : Bridge D U P M plus minus) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Freq D,
      1 + (Ideal.absNorm (P u).conductor : ℝ) ≤ C * frequencyNorm D.recipe u :=
  NonprincipalContinuation.RightBound.ConductorEstimate.raw_plus_inducer_conductor_bound
    D.recipe U h.raw_u P h.plus_coeff

theorem plus_eq_hecke_mul_mask (h : Bridge D U P M plus minus) (u : Freq D)
    (hu : u ≠ principal D) (w : ℂ) (hw : 0 < w.re) :
    plus u w = (RowHeckeBridge.hecke D.recipe.A (P u) (h.plus_nonprincipal u hu)).L w *
      Detector.finiteEulerDeletionMask F (delSet (U u))
        (fun v => (P u).character v.asIdeal) w :=
  NonprincipalContinuation.RightBound.ConductorEstimate.deleted_exterior_continuation_eq
    D.recipe.A (P u) (RowHeckeBridge.hecke D.recipe.A (P u) (h.plus_nonprincipal u hu))
    (delSet (U u)) (h.finite u) Set.subset_union_left
    (AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ (U u)) (h.plus_coeff u)
    (plus u) (h.plus_diff u hu) (h.plus_series u) w hw

theorem minus_eq_hecke_mul_mask (h : Bridge D U P M plus minus) (u : Freq D)
    (hu : u ≠ principal D) (w : ℂ) (hw : 0 < w.re) :
    minus u w = (RowHeckeBridge.hecke D.recipe.A (M u) (h.minus_nonprincipal u hu)).L w *
      Detector.finiteEulerDeletionMask F (delSet (U u))
        (fun v => (M u).character v.asIdeal) w :=
  NonprincipalContinuation.RightBound.ConductorEstimate.deleted_exterior_continuation_eq
    D.recipe.A (M u) (RowHeckeBridge.hecke D.recipe.A (M u) (h.minus_nonprincipal u hu))
    (delSet (U u)) (h.finite u) Set.subset_union_left
    (AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target (U u))
    (h.minus_coeff u) (minus u) (h.minus_diff u hu) (h.minus_series u) w hw

end Bridge

end

end DedekindZetaZeroFree.Quantitative.RawFrequencyPublicBridge
