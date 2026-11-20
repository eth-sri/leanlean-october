module

public import QPBT.Observables.WinImplications.AnticommutingObs

/-!
# The phase-signed commutation relation of the point observables

This module assembles the commuting and anticommuting halves into Equation
`eq:pts-obs-commutation` of `lem:qld-win-implications-obs`: on average over a
uniformly random tuple the two point observables commute up to the sign
`(-1)^gamma(omega)`, with error the square root of the test error.

## References

The declarations formalize the first assertion of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyTwisted : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## The unconditional bound on a difference of reflections -/

/-- The product of two isometries is an isometry. Formalization-only support
for `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`. -/
theorem mul_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Op ι} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  grind only

/-- Both sides of the twisted commutation relation are unit vectors, so their
distance is bounded by two for every tuple. This is the unconditional bound
used when the error parameter exceeds one; the statement is generic in the two
tensor factors and the state. Paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem norm_twistedCommutator_sq_le_four {P : AdmissibleParams}
    {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : PauliTuple P → Op ιL) (χ : EuclideanSpace ℂ (ιL × ιR))
    (hχ : ‖χ‖ = 1) (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1)
    (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
          ω.phase •
            heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2 ≤ 4 := by
  have norm_mul (A B : Op ιL) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
      ‖applyOperatorToState (heteroKron (A * B) (1 : Op ιR)) χ‖ = 1 :=
    (MagicSquareRigidity.norm_applyOperatorToState_of_isometry
      (heteroKron_left_isometry _ (mul_conjTranspose_mul_self hA hB)) χ).trans hχ
  rw [MagicSquareRigidity.applyOperatorToState_sub_op, applyOperatorToState_smul_op]
  calc
    _ ≤ (_ + _) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    _ = 4 := by
      rw [norm_smul, show ‖ω.phase‖ = 1 from norm_phaseSign _, one_mul,
        norm_mul _ _ (hOX ω) (hOZ ω), norm_mul _ _ (hOZ ω) (hOX ω)]
      norm_num

/-! ## Splitting the uniform average -/

/-- A gated uniform average is bounded by the corresponding conditional
average. Formalization-only support for the case split of
`eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`. -/
theorem avgOver_gated_le {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (p : X → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).Nonempty)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {K : ℝ}
    (hK : avgOver (Distribution.uniformOnFinset (Finset.univ.filter p)) f ≤ K) :
    avgOver (uniformDistribution X) (fun x => if p x then f x else 0) ≤ K := by
  rw [← cardRatio_mul_avgOver_filter p hp f]
  have hA : 0 ≤ avgOver
      (Distribution.uniformOnFinset (Finset.univ.filter p)) f :=
    avgOver_nonneg _ _ hf
  have hratio : ((Finset.univ.filter p).card : ℝ) / Fintype.card X ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast Finset.card_le_univ _
  nlinarith

/-- The commuting event is nonempty. Paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`, blueprint
`ch14_qpbt_observables.tex:159-194`. -/
theorem commuting_filter_nonempty (P : AdmissibleParams) :
    (Finset.univ.filter (@IsCommuting P)).Nonempty := by
  refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simp [IsCommuting, gammaValue, fixedBinTrace, binTrace, dotProduct]

/-- The anticommuting event is nonempty. Paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`, blueprint
`ch14_qpbt_observables.tex:159-194`. -/
theorem anticommuting_filter_nonempty (P : AdmissibleParams) :
    (Finset.univ.filter (@IsAnticommuting P)).Nonempty := by
  by_contra h
  have hempty :=
    Finset.not_nonempty_iff_eq_empty.mp h
  have hprob := anticommTupleDist_isProbability P
  unfold anticommTupleDist Distribution.IsProbability
    Distribution.totalWeight at hprob
  rw [hempty] at hprob
  simp at hprob

/-- Splitting a uniform average over the commuting and anticommuting events.
Formalization-only support for `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`. -/
theorem avgOver_uniform_split_le (P : AdmissibleParams)
    (f : PauliTuple P → ℝ) (hf : ∀ ω, 0 ≤ f ω) {Kc Ka : ℝ}
    (hc : avgOver (commTupleDist P) f ≤ Kc)
    (ha : avgOver (anticommTupleDist P) f ≤ Ka) :
    avgOver (uniformDistribution (PauliTuple P)) f ≤ Kc + Ka := by
  classical
  have hsplit : avgOver (uniformDistribution (PauliTuple P)) f =
      avgOver (uniformDistribution (PauliTuple P))
          (fun ω => if IsCommuting ω then f ω else 0) +
        avgOver (uniformDistribution (PauliTuple P))
          (fun ω => if IsAnticommuting ω then f ω else 0) := by
    rw [← avgOver_add]
    refine avgOver_congr _ _ _ ?_
    intro ω
    by_cases h : IsCommuting ω
    · have hna : ¬ IsAnticommuting ω := by
        simp only [IsAnticommuting, not_not]
        exact h
      simp [h, hna]
    · have hna : IsAnticommuting ω := by
        assumption
      simp [h, hna]
  rw [hsplit]
  exact add_le_add
    (avgOver_gated_le (@IsCommuting P) (commuting_filter_nonempty P) f hf hc)
    (avgOver_gated_le (@IsAnticommuting P) (anticommuting_filter_nonempty P) f
      hf ha)

/-! ## The twisted commutation relation -/

/-- Assembling the commuting and anticommuting halves into the phase-signed
commutation relation. This is Equation `eq:pts-obs-commutation`, stated
generically in the two tensor factors and the state so that both orientations
of `lem:qld-win-implications-obs` use it. Paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem twisted_commutation_of_halves {P : AdmissibleParams} {ιL ιR : Type}
    [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : PauliTuple P → Op ιL) (χ : EuclideanSpace ℂ (ιL × ιR))
    (hχ : ‖χ‖ = 1) (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1)
    (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1) {ε Cc Ca : ℝ}
    (hε : 0 ≤ ε) (hCc : 0 ≤ Cc) (hCa : 0 ≤ Ca)
    (hcomm : avgOver (commTupleDist P) (fun ω =>
      ‖applyOperatorToState (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤
        Cc * (ε + Real.sqrt ε))
    (hanti : avgOver (anticommTupleDist P) (fun ω =>
      ‖applyOperatorToState (heteroKron (OX ω * OZ ω) (1 : Op ιR) +
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤ Ca * ε) :
    opDistSq (uniformDistribution (PauliTuple P))
      (fun ω => heteroKron (OX ω * OZ ω) (1 : Op ιR))
      (fun ω => ω.phase •
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ ≤
      (2 * Cc + Ca + 4) * Real.sqrt ε := by
  classical
  rw [opDistSq_eq_avgOver]
  set f : PauliTuple P → ℝ := fun ω =>
    ‖applyOperatorToState (heteroKron (OX ω * OZ ω) (1 : Op ιR) -
      ω.phase •
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2 with hfdef
  have hfnn : ∀ ω, 0 ≤ f ω := by
    intro ω
    rw [hfdef]
    positivity
  have hsq := Real.sqrt_nonneg ε
  have hcbound : avgOver (commTupleDist P) f ≤ Cc * (ε + Real.sqrt ε) := by
    refine le_trans (le_of_eq ?_) hcomm
    refine avgOver_congr_on_support _ _ _ ?_
    intro ω hω
    have hIs : IsCommuting ω := by
      rw [commTupleDist, Distribution.uniformOnFinset_support,
        Finset.mem_filter] at hω
      exact hω.2
    have hph : ω.phase = 1 := by
      simp [PauliTuple.phase, show ω.phaseBit = 0 from hIs, phaseSign]
    simp only [hfdef]
    rw [hph, one_smul]
  have habound : avgOver (anticommTupleDist P) f ≤ Ca * ε := by
    refine le_trans (le_of_eq ?_) hanti
    refine avgOver_congr_on_support _ _ _ ?_
    intro ω hω
    have hIs : IsAnticommuting ω := by
      rw [anticommTupleDist, Distribution.uniformOnFinset_support,
        Finset.mem_filter] at hω
      exact hω.2
    have hone := (zmod_two_eq_zero_or_one ω.phaseBit).resolve_left hIs
    have hph : ω.phase = -1 := by simp [PauliTuple.phase, hone, phaseSign]
    simp only [hfdef]
    rw [hph, neg_one_smul, sub_neg_eq_add]
  have hmain :=
    avgOver_uniform_split_le P f hfnn hcbound habound
  have htriv : avgOver (uniformDistribution (PauliTuple P)) f ≤ 4 := by
    refine le_trans (avgOver_mono _ _ (fun _ => (4 : ℝ)) ?_) ?_
    · intro ω
      rw [hfdef]
      exact norm_twistedCommutator_sq_le_four OX OZ χ hχ hOX hOZ ω
    · exact le_of_eq (avgOver_const_of_isProbability _
        (uniformDistribution_isProbability (PauliTuple P)) 4)
  by_cases hle : ε ≤ 1
  · have hsle : Real.sqrt ε ≤ 1 := by nlinarith [Real.sq_sqrt hε]
    have hεsq : ε ≤ Real.sqrt ε := by nlinarith [Real.sq_sqrt hε]
    have h1 : Cc * (ε + Real.sqrt ε) + Ca * ε ≤
        (2 * Cc + Ca) * Real.sqrt ε := by
      nlinarith [mul_le_mul_of_nonneg_left hεsq hCc,
        mul_le_mul_of_nonneg_left hεsq hCa]
    have h2 : (2 * Cc + Ca) * Real.sqrt ε ≤
        (2 * Cc + Ca + 4) * Real.sqrt ε := by nlinarith [hsq]
    linarith
  · have hgt := not_le.mp hle
    have hone : (1 : ℝ) ≤ Real.sqrt ε := by
      nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε]
    have h3 : (4 : ℝ) ≤ (2 * Cc + Ca + 4) * Real.sqrt ε := by
      nlinarith [hone, hCc, hCa]
    linarith

/-! ## The commuting half on Alice's factor -/

abbrev commutingObsConstant : ℝ :=
  1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
    1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))

abbrev twistedCommutationConstant : ℝ :=
  2 * commutingObsConstant + anticommutingObsConstant + 4

/-- The point observables of Alice approximately commute on commuting tuples.
This auxiliary estimate is the commuting part of `lem:qld-win-implications-obs`
in the standard tensor order.

The error is `C * (ε + √ε)` rather than `C * ε` because Equation `eq:lc-11` is
closed by the transitivity estimate for the consistency relation `≃`, which is
not additive. The detour through the Pair/W families passes through a squared
state-dependent distance and a Cauchy--Schwarz step, so its two `O(ε)` defects
contribute `O(√ε)`, while the defect of the step used directly contributes
`O(ε)`. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:311-341`,
blueprint `lem:qld-point-obs-commuting-estimate`. -/
theorem point_obs_commutator_comm_le_alice_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointProductAt .alice .X ω) (1 : Op S.toStrategy.ιB) -
            heteroKron (S.pointProductAt .alice .Z ω) (1 : Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤
        commutingObsConstant *
            (ε + Real.sqrt ε) := by
  classical
  have hcard : (1 : ℝ) ≤ (Fintype.card PauliEdge : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  set K : ℝ := 4 * (Fintype.card PauliEdge : ℝ) with hKdef
  have hK : (0 : ℝ) ≤ K := by rw [hKdef]; linarith
  intro P ε S hε
  have hsq := Real.sqrt_nonneg ε
  have hmain := point_obs_commutator_comm_le_explicit
    (ιL := S.toStrategy.ιA) (ιR := S.toStrategy.ιB)
    (S.pointTraceAt .alice .X)
    (S.pointTraceAt .alice .Z)
    (S.pairWAt .alice .X)
    (S.pairWAt .alice .Z)
    (S.pairWAt .bob .X)
    (S.pairWAt .bob .Z)
    (S.pairAt .bob)
    (S.pointObsAt .alice .X)
    (S.pointObsAt .alice .Z)
    S.toStrategy.ψ S.toStrategy.ψ_norm (by positivity)
    (fun ω => SandwichProduct.postprocess_isProjective _ (S.isProjective.2 _) _)
    (fun ω => pointObs_eq_one_sub_two_smul S .alice .X ω.2.2.1 ω.1)
    (fun ω => pointObs_eq_one_sub_two_smul S .alice .Z ω.2.2.2 ω.2.1)
    (win_comm_cons_explicit P ε S hε .X) (win_comm_cons_explicit P ε S hε .Z)
    (pairW_self_consistency_comm_le S .X) (pairW_self_consistency_comm_le S .Z)
    (win_comm_explicit P ε S hε .X) (win_comm_explicit P ε S hε .Z)
  refine le_trans hmain ?_
  have hKsplit : Real.sqrt (2 * (Fintype.card PauliEdge : ℝ) * ε +
      2 * (Fintype.card PauliEdge : ℝ) * ε) =
      Real.sqrt K * Real.sqrt ε := by
    rw [show 2 * (Fintype.card PauliEdge : ℝ) * ε +
        2 * (Fintype.card PauliEdge : ℝ) * ε = K * ε by
      rw [hKdef]; ring]
    exact Real.sqrt_mul hK ε
  rw [hKsplit]
  unfold commutingObsConstant
  nlinarith [Real.sqrt_nonneg K, hε, hsq]

/-- The strategy observables satisfy the phase-signed commutation relation on
Alice's factor. This is Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_twisted_commutation_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron
          (S.pointProductAt .alice .X ω) 1)
        (fun ω => ω.phase •
          heteroKron
            (S.pointProductAt .alice .Z ω) 1)
        S.toStrategy.ψ ≤
          twistedCommutationConstant *
            Real.sqrt ε := by
  classical
  intro P ε S hε
  exact twisted_commutation_of_halves
    (S.pointObsAt .alice .X)
    (S.pointObsAt .alice .Z)
    S.toStrategy.ψ S.toStrategy.ψ_norm
    (fun ω => pointObs_conjTranspose_mul_self S .alice .X _ _)
    (fun ω => pointObs_conjTranspose_mul_self S .alice .Z _ _)
    hε (by positivity) (by positivity)
    (point_obs_commutator_comm_le_alice_explicit P ε S hε)
    (point_obs_anticommutator_anticomm_le_explicit P ε S hε)

end WinImplications

end

end MIPStarRE.QPBT
