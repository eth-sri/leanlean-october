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
          phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
            heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2 ≤ 4 := by
  have h1 : ‖applyOperatorToState
      (heteroKron (OX ω * OZ ω) 1) χ‖ = 1 := by
    rw [MagicSquareRigidity.norm_applyOperatorToState_of_isometry (heteroKron_left_isometry (ιB := ιR)
      (MagicSquareRigidity.isometry_mul_isometry (hOX ω) (hOZ ω)))]
    exact hχ
  have h2 : ‖applyOperatorToState
      (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        heteroKron (OZ ω * OX ω) 1) χ‖ = 1 := by
    rw [applyOperatorToState_smul_op, norm_smul, norm_phaseSign,
      MagicSquareRigidity.norm_applyOperatorToState_of_isometry (heteroKron_left_isometry (ιB := ιR)
        (MagicSquareRigidity.isometry_mul_isometry (hOZ ω) (hOX ω))), hχ, one_mul]
  have hsub : ‖applyOperatorToState
      (heteroKron (OX ω * OZ ω) 1 -
        phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron (OZ ω * OX ω) 1) χ‖ ≤ 2 := by
    rw [DistanceCalculus.applyOperatorToState_sub_op]
    refine LE.le.trans_eq (norm_sub_le _ _) ?_
    simp [*]; norm_num
  nlinarith [hsub, norm_nonneg (applyOperatorToState
    (heteroKron (OX ω * OZ ω) 1 -
      phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        heteroKron (OZ ω * OX ω) 1) χ)]

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

section

variable (P : AdmissibleParams)

/-- Splitting a uniform average over the commuting and anticommuting events.
Formalization-only support for `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-362`. -/
theorem avgOver_uniform_split_le
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
    apply avgOver_congr
    intro ω
    by_cases h : IsCommuting ω
    · have hna : ¬ IsAnticommuting ω := by
        simp [IsAnticommuting]
        exact h
      simp_all
    · have hna : IsAnticommuting ω := by
        exact h
      simp_all
  rw [hsplit]
  exact add_le_add
    (avgOver_gated_le _ ((by
                                          refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
                                          simp [IsCommuting, gammaValue, fixedBinTrace, dotProduct])) f hf hc)
    (avgOver_gated_le _ ((by
                           by_contra h
                           have hprob := anticommTupleDist_isProbability P
                           unfold anticommTupleDist Distribution.IsProbability
                             Distribution.totalWeight at hprob
                           rw [(Finset.not_nonempty_iff_eq_empty.mp h)] at hprob
                           simp at hprob)) f
      hf ha)

end

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
      (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ ≤
      (2 * Cc + Ca + 4) * Real.sqrt ε := by
  classical
  rw [opDistSq_eq_avgOver]
  set f : PauliTuple P → ℝ := fun ω =>
    ‖applyOperatorToState (heteroKron (OX ω * OZ ω) 1 -
      phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        heteroKron (OZ ω * OX ω) 1) χ‖ ^ 2 with hfdef
  have hsq := Real.sqrt_nonneg ε
  have hcbound : avgOver (commTupleDist P) f ≤ Cc * (ε + Real.sqrt ε) := by
    refine le_trans (le_of_eq ?_) hcomm
    apply avgOver_congr_on_support
    intro ω hω
    have hIs : IsCommuting ω := by
      rw [commTupleDist, Distribution.uniformOnFinset_support,
        Finset.mem_filter] at hω
      exact hω.2
    have hph : phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1 := by
      rw [hIs]
      simp [phaseSign]
    simp [*]
  have habound : avgOver (anticommTupleDist P) f ≤ Ca * ε := by
    refine le_trans (le_of_eq ?_) hanti
    apply avgOver_congr_on_support
    intro ω hω
    have hone : gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 1 := by
      have h := (by
        rw [anticommTupleDist, Distribution.uniformOnFinset_support,
          Finset.mem_filter] at hω
        exact hω.2)
      rw [IsAnticommuting] at h
      revert h
      generalize gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = t
      revert t
      decide
    have hph : phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = -1 := by
      rw [hone]
      simp [phaseSign]
    simp only [hfdef]
    simp [hph]
  have hmain :=
    avgOver_uniform_split_le P f (by
      bound) hcbound habound
  have htriv : avgOver (uniformDistribution (PauliTuple P)) f ≤ 4 := by
    refine le_trans (avgOver_mono _ _ (fun _ => 4) ?_) ?_
    · solve_by_elim [norm_twistedCommutator_sq_le_four]
    · exact le_of_eq (avgOver_const_of_isProbability _
        (uniformDistribution_isProbability (PauliTuple P)) 4)
  by_cases hle : ε ≤ 1
  · have hεsq : ε ≤ Real.sqrt ε := by nlinarith [Real.sq_sqrt hε]
    have h1 : Cc * (ε + Real.sqrt ε) + Ca * ε ≤
        (2 * Cc + Ca) * Real.sqrt ε := by
      nlinarith [mul_le_mul_of_nonneg_left hεsq hCc,
        mul_le_mul_of_nonneg_left hεsq hCa]
    linarith
  · have hone : 1 ≤ Real.sqrt ε := by
      nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε]
    have h3 : 4 ≤ (2 * Cc + Ca + 4) * Real.sqrt ε := by
      nlinarith [hone, hCc, hCa]
    linarith

/-! ## The commuting half on Alice's factor -/

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
          (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
              S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιB) -
            heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤
        (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
          1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) *
            (ε + Real.sqrt ε) := by
  classical
  set K : ℝ := 4 * (Fintype.card PauliEdge) with hKdef
  intro P ε S hε
  refine le_trans (point_obs_commutator_comm_le_explicit
    (fun ω => S.pointTraceMeas .alice .X ω.1 ω.2.2.1)
    (fun ω => S.pointTraceMeas .alice .Z ω.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairMeas .bob ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pointObs .alice .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .alice .Z ω.2.2.2 ω.2.1)
    S.toStrategy.ψ S.toStrategy.ψ_norm (by positivity)
    (fun ω => SandwichProduct.postprocess_isProjective _ (S.isProjective.2 _) _)
    (fun ω => pointObs_eq_one_sub_two_smul S .alice .X ω.2.2.1 ω.1)
    (fun ω => pointObs_eq_one_sub_two_smul S .alice .Z ω.2.2.2 ω.2.1)
    (win_comm_cons_explicit P ε S hε .X) (win_comm_cons_explicit P ε S hε .Z)
    (pairW_self_consistency_comm_le S .X) (pairW_self_consistency_comm_le S .Z)
    (win_comm_explicit P ε S hε .X) (win_comm_explicit P ε S hε .Z)) ?_
  have hKsplit : Real.sqrt (2 * (Fintype.card PauliEdge) * ε +
      2 * (Fintype.card PauliEdge) * ε) =
      Real.sqrt K * Real.sqrt ε := by
    rw [show 2 * (Fintype.card PauliEdge) * ε +
        2 * (Fintype.card PauliEdge) * ε = K * ε by
      ring]
    exact Real.sqrt_mul (by rw [hKdef]; linarith) ε
  nlinarith [Real.sqrt_nonneg K, hε, (Real.sqrt_nonneg ε)]

/-- The strategy observables satisfy the phase-signed commutation relation on
Alice's factor. This is Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_twisted_commutation_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron
          (S.pointObs .alice .X ω.2.2.1 ω.1 *
            S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1)
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron
            (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) 1)
        S.toStrategy.ψ ≤
          (2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  classical
  intro P ε S hε
  exact twisted_commutation_of_halves
    _
    (fun ω => S.pointObs .alice .Z ω.2.2.2 ω.2.1)
    S.toStrategy.ψ S.toStrategy.ψ_norm
    (fun ω => pointObs_conjTranspose_mul_self S .alice .X ω.2.2.1 ω.1)
    (fun ω => pointObs_conjTranspose_mul_self S .alice .Z ω.2.2.2 ω.2.1)
    hε (by positivity) (by positivity)
    (point_obs_commutator_comm_le_alice_explicit P ε S hε)
    (point_obs_anticommutator_anticomm_le_explicit P ε S hε)

end WinImplications

end

end MIPStarRE.QPBT
