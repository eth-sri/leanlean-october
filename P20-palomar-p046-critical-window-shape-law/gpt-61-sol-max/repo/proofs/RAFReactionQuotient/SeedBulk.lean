
import proofs.HordijkSteelThreshold.FixedPoolReactionLaw
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
import proofs.RAFReactionQuotient.History
import proofs.RAFReactionQuotient.Fibres
import proofs.HordijkSteelThreshold.WordEffectiveClosure




namespace RAFReactionQuotient

section
open Classical MeasureTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

def fieldOR (π : R → J) (ω : R → Prop) (j : J) : Prop :=
  ∃ r, π r = j ∧ ω r

variable (π : R → J) (p : I) (j : J)

noncomputable def fibreParameter   :=
  σ (σ p ^ (Finset.univ.filter fun r => π r = j).card)



/-- The complete quotient ensemble is a product law with its actual fibre
probabilities. Singleton and double fibres need not have the same parameter. -/
theorem fieldOR_map [Fintype J] (π : R → J) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) =
      Measure.pi (fun j => ambientCoordLaw (fibreParameter π p j)) := by
  let F := fun j => {r // π r = j}
  let S := MeasurableEquiv.piCongrLeft (fun _ : (j : J) × F j => Prop) (Equiv.sigmaFiberEquiv π).symm
  let C := MeasurableEquiv.piCurry (fun j (_ : F j) => Prop)
  have hcol (j : J) : (Measure.infinitePi fun _ : F j => ambientCoordLaw p).map (fun v => ∃ r, v r) =
      ambientCoordLaw (fibreParameter π p j) := by
    simpa [RAFEmergenceApprox.Generic.colLaw, Measure.infinitePi_eq_pi,
      fibreParameter, fixedPoolParameter,F,Fintype.card_subtype] using
      pool_column_map (X := F j) p Finset.univ

  calc
    _ = (((RAFEmergenceApprox.Generic.colLaw R p).map S).map C).map
        fun v j => ∃ r, v j r := by
      rw [Measure.map_map (measurable_of_finite _) C.measurable,
        Measure.map_map (measurable_of_finite _) S.measurable]
      congr 1
      funext ω j
      simp [S, C, Sigma.curry, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, fieldOR, F]
    _ = _ := by
      rw [RAFEmergenceApprox.Generic.colLaw, ← Measure.infinitePi_eq_pi,
        Measure.infinitePi_map_piCongrLeft
          (fun _ : (j : J) × F j => ambientCoordLaw p) (Equiv.sigmaFiberEquiv π).symm,
        Measure.infinitePi_map_piCurry (fun j _ => ambientCoordLaw p),
        Measure.infinitePi_map_pi _ fun _ => measurable_of_finite _]
      simp_rw [hcol]
      exact Measure.infinitePi_eq_pi _
end

open Classical unitInterval

noncomputable def halfParameter (a : I) : I := ⟨a/2, by grind⟩

open MeasureTheory HordijkSteelThreshold
open RAF.Polymer OverlapCorrectedRAF.Source

noncomputable def quotientStaticMeasure (n : ℕ) (a : I) :=
  Measure.pi fun _ : RepositoryChannel n => ambientCoordLaw a

variable {n : ℕ}

noncomputable def quotientOpen  (ω : RepositoryChannel n → Prop)  := Finset.univ.filter ω

theorem quotientOpen_OR  (ω : Reaction n → Prop) :
    quotientOpen (fieldOR splitToQuotient ω) =
      (staticOpenReactions ω).image splitToQuotient := by
  ext j
  simp [quotientOpen,fieldOR,staticOpenReactions,and_comm]

theorem quotientClosure_OR {n L : ℕ} (ω : _) :
    quotientClosure n L (quotientOpen (fieldOR splitToQuotient ω)) =
      temporaryReactionClosure L (staticOpenReactions ω) := by
  rw [quotientOpen_OR]
  ext x
  simp [split_closure_eq_quotient]

theorem quotient_mass_failure_antitone (n L m : ℕ) :
    Antitone (fun ω : _ =>
      MassDeficit m (quotientClosure n L (quotientOpen ω))) := by
  intro x y hxy hy

  exact lt_of_le_of_lt (Nat.mul_le_mul_left m (Finset.card_le_card (quotientClosure_mono n L (Finset.monotone_filter_right _ fun j _ => @hxy j)))) hy

end RAFReactionQuotient
