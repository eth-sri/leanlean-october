
import proofs.RAFReactionQuotient.FiniteApproximation
import proofs.HordijkSteelThreshold.PeelingHistory
import proofs.RAFEmergenceApprox.GenericHistory
import proofs.HordijkSteelThreshold.PeelingHistory
import proofs.HordijkSteelThreshold.BoundedRAFProbability
import proofs.HordijkSteelThreshold.FixedPoolReactionLaw
import proofs.RAFReactionQuotient.SeedApproximation
import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock




namespace RAFReactionQuotient

open OverlapCorrectedRAF.Source RAFCriticalWindowQuantitative


theorem fullClosure_eq_quotient {n L : ℕ} (A : Finset (RepositoryChannel n)) :
    fullClosure (repositoryCRS n L) A = quotientClosure n L A := by
  ext x
  simp
  exact (closureAt_exists_iff _ _ (closure_stable_at_card _ _) x).symm



open unitInterval HordijkSteelThreshold
open RAF.Polymer

variable (n : ℕ) (p : I) (C : Finset (Molecule n))

theorem quotient_pool_statistic 
    (stat : _ → Prop) :
    quotientCatalyticLaw n p {ω | stat (RAFEmergenceApprox.Generic.catalystActive ω C)} =
      quotientStaticMeasure n (fixedPoolParameter p C.card) {q | stat (quotientOpen q)} :=
  catalystPool_statistic (fun _ : RepositoryChannel n => p) C stat


open Classical MeasureTheory
open RAF.Concrete

def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}


noncomputable def quotientRAFProbability   :=
  quotientCatalyticLaw n p (quotientRAFEvent n)



theorem quotient_coordinate_probability  (j : RepositoryChannel n) (x : Molecule n) :
    quotientCatalyticLaw n p {ω | ω j x} = toNNReal p := by
  have h := (measurePreserving_eval (fun _ : Molecule n => ambientCoordLaw p) x).comp
    (measurePreserving_eval (fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p) j)
  simpa [ambientCoordLaw,quotientCatalyticLaw,RAFEmergenceApprox.Generic.law] using h.measure_preimage (MeasurableSet.singleton True).nullMeasurableSet

def quotientBoundedSeed (n K : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ j : RepositoryChannel n,
    molLength x ≤ K ∧ RevSeedReaction (repositoryCRS n 2) j ∧ ω j x}

variable (n K : ℕ) (p : I)

theorem quotient_bounded_seed_le  :
    quotientCatalyticLaw n p (quotientBoundedSeed n K) ≤
      Fintype.card (Molecule K)*34*toNNReal p := by
  let J := ↥(binaryFood n K) × ↥(repositorySeedChannels n 2)
  let E : J → Set (RepositoryChannel n → Molecule n → Prop) := fun j => {ω | ω j.2.val j.1.val}
  have he : quotientBoundedSeed n K = ⋃ j : J, E j := by
    ext ω
    simp [J, E, quotientBoundedSeed, binaryFood, repositorySeedChannels]
  rw [he]
  calc
    _ ≤ ∑ j : J, quotientCatalyticLaw n p (E j) := measure_iUnion_fintype_le _ _
    _ = Fintype.card J*toNNReal p := by
      simp [E, quotient_coordinate_probability]
    _ ≤ _ := by
      apply mul_le_mul_left
      
      exact_mod_cast by

                       rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_coe]
                       exact Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (by
                         rw [repositorySeedChannels, ← Fintype.card_subtype]
                         exact Fintype.card_le_of_injective repositorySeedChannelToGateway
                           (by
                             intro r s hrs
                             have h := congrArg Subtype.val hrs
                             dsimp only [repositorySeedChannelToGateway] at h
                             grind [lowerMolecule_injective_on]))

theorem quotient_raf_upper  :
    quotientRAFProbability n p ≤
      quotientStaticMeasure _ (fixedPoolParameter p (Fintype.card (Molecule n)))
        (quotientEscapeEvent 2 K) + Fintype.card (Molecule (K+2))*34*toNNReal p := by
  let E : Set (RepositoryChannel n → Molecule n → Prop) := {ω | ∃ x ∈
    quotientClosure n 2 (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x}
  have hs : quotientRAFEvent n ⊆ E ∪ quotientBoundedSeed n (K+2) := by
    intro ω hraf
    simpa [E, quotientBoundedSeed] using (raf_escape_or_seed (repositoryCRS n 2) ω molLength (K+2) hraf)
  have hb := (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add_right (quotient_bounded_seed_le n (K+2) p) _))
  apply hb.trans
  apply add_le_add_left
  
  rw [quotient_pool_statistic n p Finset.univ
    fun A => ∃ x ∈ quotientClosure n 2 A, K+2 < molLength x, quotient_escape_measure_eq]
  exact quotient_capped_escape_le n K _

end RAFReactionQuotient
