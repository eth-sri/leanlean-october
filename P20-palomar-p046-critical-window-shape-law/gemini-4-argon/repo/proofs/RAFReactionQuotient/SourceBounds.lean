module

public import proofs.RAFReactionQuotient.PoolLaw
public import proofs.RAFReactionQuotient.SeedApproximation
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability (n : ℕ) (p : I) : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)

theorem quotient_near_full_lower (n m : ℕ) (p q : I) (hm : 0 < m)
    (hk : 6 < nearFullPoolSize n m)
    (hq : q ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    quotientStaticMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(quotientClosure n 2 (quotientOpen ω)).card} ≤ quotientRAFProbability n p := by
  let k := nearFullPoolSize n m
  have h1 : quotientStaticMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(quotientClosure n 2 (quotientOpen ω)).card} ≤
      quotientStaticMeasure n q {ω | k ≤ (quotientClosure n 2 (quotientOpen ω)).card} :=
    measure_mono fun ω (hω : (m-1)*_ ≤ _) => by
      have := Nat.mul_le_mul_left (m-1) (Nat.div_mul_le_self (Fintype.card (Molecule n)) m)
      dsimp [k, nearFullPoolSize]; nlinarith
  have h2 := product_increasing_mono (fun _ => q) (fun _ => fixedPoolParameter p k) (fun _ => hq)
    (fun ω => k ≤ (quotientClosure n 2 (quotientOpen ω)).card) fun x y hxy hx =>
      hx.trans <| Finset.card_le_card <| quotientClosure_mono n 2 fun j hj =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy j (Finset.mem_filter.mp hj).2⟩
  have hbar : quotientStaticMeasure n (fixedPoolParameter p (finiteInitialSegment (Molecule n) k).card)
      {q | k ≤ (quotientClosure n 2 (quotientOpen q)).card} ≤ quotientRAFProbability n p :=
    (mass_ge_static p (quotientClosure n 2) (quotientClosure_mono n 2) k (Fintype.card (RepositoryChannel n))).trans
      (measure_mono fun ω hω => quotient_terminal_hasRAF ω (hk.trans_le hω))
  rw [card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)] at hbar
  exact h1.trans (h2.trans hbar)

theorem quotient_coordinate_probability (n : ℕ) (p : I) (j : RepositoryChannel n) (x : Molecule n) :
    quotientCatalyticLaw n p {ω | ω j x} = (toNNReal p : ENNReal) := by
  have hj := congrArg (fun μ : Measure (Molecule n → Prop) => μ {v | v x})
    (measurePreserving_eval (fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p) j).map_eq
  have hx := congrArg (fun μ : Measure Prop => μ {True})
    (measurePreserving_eval (fun _ : Molecule n => ambientCoordLaw p) x).map_eq
  rw [Measure.map_apply (measurable_pi_apply _) (Set.toFinite _).measurableSet] at hj
  rw [Measure.map_apply (measurable_pi_apply _) (.singleton _)] at hx
  exact hj.trans (by simpa [RAFEmergenceApprox.Generic.colLaw, ambientCoordLaw] using hx)

def quotientBoundedSeed (n K : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ j : RepositoryChannel n,
    molLength x ≤ K ∧ RevSeedReaction (repositoryCRS n 2) j ∧ ω j x}

theorem quotient_bounded_seed_le (n K : ℕ) (p : I) :
    quotientCatalyticLaw n p (quotientBoundedSeed n K) ≤
      (Fintype.card (Molecule K) : ENNReal)*34*(toNNReal p : ENNReal) := by
  let J := ↥(binaryFood n K) × ↥(repositorySeedChannels n 2)
  rw [show quotientBoundedSeed n K = ⋃ j : J, {ω | ω j.2.1 j.1.1} by
    ext ω; simp [quotientBoundedSeed, J, binaryFood, repositorySeedChannels]]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  simp only [quotient_coordinate_probability, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  gcongr
  exact_mod_cast (Fintype.card_prod _ _).trans_le
    (by simpa using Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (repositorySeedChannels_card_le_34 n))

theorem quotient_raf_upper (n K : ℕ) (p : I) :
    quotientRAFProbability n p ≤
      quotientStaticMeasure (2*(K+2)) (fixedPoolParameter p (Fintype.card (Molecule n)))
        (quotientEscapeEvent 2 K) + (Fintype.card (Molecule (K+2)) : ENNReal)*34*(toNNReal p : ENNReal) := by
  let E : Set (RepositoryChannel n → Molecule n → Prop) := {ω | ∃ x ∈
    quotientClosure n 2 (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x}
  have hs : quotientRAFEvent n ⊆ E ∪ quotientBoundedSeed n (K+2) := fun ω ⟨S, hS⟩ => by
    by_cases he : ω ∈ E
    · exact Or.inl he
    · obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated _ S hS.1 hS.2.1
      obtain ⟨x, k, hx, hcat⟩ := hS.2.2 r hr
      exact Or.inr ⟨x, r, Nat.le_of_not_gt fun hl => he ⟨x,
        quotientClosure_mono n 2 (quotient_raf_subset_peeling ω hS 0) ((mem_quotientClosure S x).mpr ⟨k, hx⟩), hl⟩,
        hseed, hcat⟩
  refine (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add ?_ (quotient_bounded_seed_le n (K+2) p)))
  change quotientCatalyticLaw n p {ω | ∃ x ∈ quotientClosure n 2
    (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x} ≤ _
  rw [quotientCatalyticLaw, pool_statistic p (Finset.univ : Finset (Molecule n))
    (fun A => ∃ x ∈ quotientClosure n 2 A, K+2 < molLength x), Finset.card_univ, quotient_escape_measure_eq]
  exact quotient_capped_escape_le n K _

end RAFReactionQuotient
