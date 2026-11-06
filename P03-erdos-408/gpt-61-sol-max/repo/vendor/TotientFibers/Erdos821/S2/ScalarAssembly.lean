module

public import Erdos821.S2.GroupWeights

/-! Literal inverse-edge factors and factorial-normalized ghost factors. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

def ghostFactorial (S : LifespanAssignment P n)  :=
  ∏ i : Fin (n + 1), ∏ g : P.BigGroup, ((Q.ghostBirthPrimes S i g).card.factorial : ℝ)

def smallEdgeDamping (y : P.SmallResidues) (i : Fin n)  :=
  smallDamping (P := P) F J (translateSmallResidues (Q.offset i.castSucc) y) *
    smallDamping (P := P) F J (translateSmallResidues (Q.offset i.succ) y)

def scalarPathPrefactor (y : P.SmallResidues)  :=
  (Fintype.card P.SmallResidues : ℝ)⁻¹ * P.markMass (J + F.ell) *
    (∏ i : Fin n, edgeSymmetryFactor P (J + F.ell) *
      (A.pattern (Q.pattern i)).auxMass (Q.free i) *
      (A.pattern (Q.pattern i)).physicalTargetMass) *
    ∏ i : Fin n, Q.smallEdgeDamping y i

theorem reconstructedRawWeight_one  S 
     y   i  :
    Q.reconstructedRawWeight S y 1 i =
      (A.pattern (Q.pattern i)).auxMass (Q.free i) *
        (∏ g : P.BigGroup, Q.freshBigGroupFactor S i g *
          (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) *
        smallTargetFactor (P := P) F * Q.smallEdgeDamping y i := by
  dsimp only [reconstructedRawWeight, rawEdgeWeight, permuteActive, stateAfter,
    stateBefore, reconstructedTransferChoice, freshBigFactor, freshBigGroupFactor,
    target, smallEdgeDamping]
  simp only [one_pow, mul_one, Finset.prod_mul_distrib]
  ring

theorem ghost_weight_factorial_product (hGhost : SpanGhostWeightTask)
     S   hS 
    (hV : ∀ g, P.V g ≠ 0)  y  :
    (∏ i : Fin (n + 1), ghostChoiceWeight F n 1 i (Q.reconstructedGhostChoice S hS y i)) *
        Q.ghostFactorial S =
      ∏ i : Fin (n + 1), ∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p := by
  unfold ghostFactorial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact hGhost F P J m n A Q S hV hS y i

theorem reconstructedScalarWeight_factorial (hGhost : SpanGhostWeightTask)
    (hMark : SpanMarkWeightTask)  S 
    (hQ : Q.Valid)  hS 
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0)  y  (hy : Q.SmallCompatible y) :
    Q.reconstructedScalarWeight S hS y 1 * Q.ghostFactorial S =
      Q.scalarPathPrefactor y *
        ∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanWeight g p (S g p) := by
  have hG := Q.ghost_weight_factorial_product hGhost S hS hV y
  have hM := Q.all_big_group_weights hMark S hQ hS hk (fun g => hV g.val)
  have hStart := Q.reconstructed_initial_mass S y hy
  unfold reconstructedScalarWeight
  rw [hStart]
  simp_rw [Q.reconstructedRawWeight_one S y]
  have he :
      (Fintype.card P.SmallResidues : ℝ)⁻¹ *
        (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
        (∏ g : P.BigGroup, Q.initialBigGroupFactor g) *
        (∏ i : Fin (n + 1), ghostChoiceWeight F n 1 i (Q.reconstructedGhostChoice S hS y i)) *
        (∏ i : Fin n, edgeSymmetryFactor P (J + F.ell) *
          ((A.pattern (Q.pattern i)).auxMass (Q.free i) *
            (∏ g : P.BigGroup, Q.freshBigGroupFactor S i g *
              (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) *
            smallTargetFactor (P := P) F * Q.smallEdgeDamping y i)) * Q.ghostFactorial S =
      (Fintype.card P.SmallResidues : ℝ)⁻¹ *
        (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
        (∏ i : Fin n, edgeSymmetryFactor P (J + F.ell) *
          (A.pattern (Q.pattern i)).auxMass (Q.free i) * smallTargetFactor (P := P) F *
          Q.smallEdgeDamping y i) *
        ((∏ g : P.BigGroup, Q.initialBigGroupFactor g) *
          (∏ i : Fin n, ∏ g : P.BigGroup, Q.freshBigGroupFactor S i g *
            (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) *
          ((∏ i : Fin (n + 1), ghostChoiceWeight F n 1 i (Q.reconstructedGhostChoice S hS y i)) *
            Q.ghostFactorial S)) := by
    simp only [Finset.prod_mul_distrib]
    ac_rfl
  dsimp only [initialBigGroupFactor] at he hM
  rw [he, hG, hM]
  unfold scalarPathPrefactor
  rw [markMass_split]
  simp_rw [physicalTargetMass_split]
  simp only [Finset.prod_mul_distrib]
  ac_rfl


end ResiduePath
end Erdos821.S2Core
