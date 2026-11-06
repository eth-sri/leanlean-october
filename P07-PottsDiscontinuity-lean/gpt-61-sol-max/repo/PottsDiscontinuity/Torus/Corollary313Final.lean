module
public import Mathlib

public import PottsDiscontinuity.Torus.Corollary313
public import PottsDiscontinuity.TorusTopology.NonzeroWindingTurning
public import PottsDiscontinuity.TorusTopology.ZeroWindingTurning

/-!
# Final torus random-cluster / six-vertex identities

The homological turning classifications proved in `TorusTopology/ZeroWindingTurning.lean`
and `TorusTopology/NonzeroWindingTurning.lean` discharge the explicit intermediate
premises used by `OrientedLoopWeight` and `Corollary313`. This module exposes the
Lemma 3.10 weight identity and all three parts of Corollary 3.13 without those
intermediate premises.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M)
include hN hM

private theorem turnPremises_of_turning_classification
     (i : Fin N) (j : Fin M)
    (A : RCConfig N M) :
    ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A := by
                                                                                    solve_by_elim [_root_.And.intro, _root_.PottsDiscontinuity.TorusTopology.loopRotationNumber_eq_pm_one_of_zero_winding, _root_.PottsDiscontinuity.TorusTopology.loopRotationNumber_eq_zero_of_nonzero_winding]

section

variable (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (i : Fin N) (j : Fin M)
include hq

/-- Corollary 3.13(i): the corrected random-cluster partition sum equals the
six-vertex partition function at `c = sqrt (2 + sqrt q)`. -/
theorem corollary_313_i_final
      :
     ∑ A : RCConfig N M, torusCorrectedRCWeight hN hM i j q A  =
      torusNormalization q N M *
        Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
                                                       solve_by_elim [_root_.PottsDiscontinuity.Torus.corollary_313_i, _root_.PottsDiscontinuity.Torus.turnPremises_of_turning_classification]

/-- Corollary 3.13(ii): the `U = 1` corrected random-cluster sector is bounded
by four times the one-defect six-vertex sector. -/
theorem corollary_313_ii_final
      :
     ∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
      torusCorrectedRCWeight hN hM i j q A.val  ≤
      4 * torusNormalization q N M *
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
                                                          solve_by_elim [_root_.PottsDiscontinuity.Torus.corollary_313_ii, _root_.PottsDiscontinuity.Torus.turnPremises_of_turning_classification]

/-- Corollary 3.13(iii): every `r`-defect six-vertex sector is bounded by the
corrected random-cluster sector with vertical winding at least `r`. -/
theorem corollary_313_iii_final
      (r : ℕ) :
    torusNormalization q N M *
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val := by
                                                      solve_by_elim [_root_.PottsDiscontinuity.Torus.corollary_313_iii, _root_.PottsDiscontinuity.Torus.turnPremises_of_turning_classification]

end

end

end PottsDiscontinuity.Torus
