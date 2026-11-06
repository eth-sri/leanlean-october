module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Edge.NormOsc

public import Erdos821.P3Clean.LiteralClean

/-! Signed clean coefficients after the exact small normalization. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem restrictBig_join {M : ℕ} (a : SmallLabels P M) (b : P.BigLabels M) :
    P.restrictBig (joinLabels a b) = b := by funext g; exact joinLabels_big a b g

section
variable (A : Model F P J m)

theorem rawEdgeWeight_empty_join   (n : ℕ) (ν : Pattern P J F.ell m)
    (a c : SmallLabels P (J + F.ell)) (b d : P.BigLabels (J + F.ell))
    (v : SmallLabels P J) (u : P.BigAux J) (s t : PendingState P) :
    rawEdgeWeight A n 1 ν (joinLabels v u)
      (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2)
      (emptyTransfer (s.1, joinLabels a b, s.2)) =
      (smallAuxMass v * ν.bigAuxMass u) * tiltedFreshMass F n ν d *
        smallTargetFactor (P := P) F * smallDamping F J s.1 * smallDamping F J t.1 := by
  simp only [rawEdgeWeight, emptyTransfer, auxMass_join, freshBigFactor_empty,
    Finset.card_empty, Nat.cast_zero, neg_zero, zpow_zero, Finset.prod_const_one,
    one_pow, mul_one]

def smallSignedCoefficient (A : Model F P J m) (forward : Bool) (d : SmallLabels P J)  :=
  if forward then imaginaryPower (prefixPrimeProduct J d) A.zeta
  else star (imaginaryPower (prefixPrimeProduct J d) A.zeta)

def bigSignedCoefficient (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J)  :=
  if forward then ν.coefficient a b u * imaginaryPower (ν.DBig a u) A.zeta
  else star (ν.coefficient b a u * imaginaryPower (ν.DBig a u) A.zeta)

theorem imaginaryPower_norm  n   zeta  : ‖imaginaryPower n zeta‖ = 1 := by solve_by_elim [_root_.Erdos821.P3Edge.norm_imaginaryPower]

theorem smallSignedCoefficient_norm    forward  (d : SmallLabels P J) :
    ‖smallSignedCoefficient A forward d‖ = 1 := by
  unfold smallSignedCoefficient
  split_ifs <;> simp only [norm_star, imaginaryPower_norm]

theorem rawCleanCoefficient_join   (n : ℕ) (theta : ℝ) (forward : Bool)
    (ν : Pattern P J F.ell m) (a c : SmallLabels P (J + F.ell))
    (b d : P.BigLabels (J + F.ell)) (v : SmallLabels P J) (u : P.BigAux J)
    (s t : PendingState P) (hV : ∀ g : P.SmallGroup, 0 ≤ P.V g.val) :
    (smallMarkMass P (J + F.ell) : ℂ) *
      rawCleanCoefficient A n theta forward ν (joinLabels v u)
        (s.1, joinLabels a b, s.2) (t.1, joinLabels c d, t.2) =
      (smallAuxMass v : ℂ) *
        (star (physicalSmallCoefficient F P J s.1) * physicalSmallCoefficient F P J t.1) *
        (ν.bigAuxMass u * tiltedFreshMass F n ν d : ℝ) *
        smallSignedCoefficient A forward (smallArrayPrefix J F.ell a) *
        bigSignedCoefficient A ν forward b d u *
        phase (theta * (bigStep A ν forward (smallArrayPrefix J F.ell a) b u : ℝ)) := by
  have hu : (fun g : P.BigGroup => joinLabels v u g.val) = u := by
    funext g
    exact joinLabels_big v u g
  simp only [rawCleanCoefficient, rawEdgeWeight_empty_join, restrictBig_join, hu,
    D_join, edgeDelta_join]
  rw [imaginaryPower_mul _ _ (prefixPrimeProduct_pos J (smallArrayPrefix J F.ell a))
    (DBig_pos ν b u) A.zeta, physicalSmallCoefficient_joint F P J s.1 t.1 hV]
  simp only [smallSignedCoefficient, bigSignedCoefficient]
  split_ifs <;> simp only [star_mul, Complex.ofReal_mul] <;> ring

end


end Erdos821.P3Clean
