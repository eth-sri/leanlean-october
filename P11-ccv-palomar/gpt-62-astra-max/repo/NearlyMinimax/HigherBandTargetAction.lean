module

public import NearlyMinimax.HighSourceRawDecomposition
public import NearlyMinimax.HigherBandOmissions


@[expose] public section

/-! Actual target-count evaluation and physical sum of the selected
higher signed rows. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {d n : ℕ} (ad bd lam ell N mu : ℝ) (D M q : ℕ) (C : ℝ) (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (U : DesignSample d n) (p : Fin n → ℝ) (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ)

def higherBandPhysicalFirstAction
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
        (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) q C i.2 U p c Φ else 0
  else higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
    (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) q C i.2 U p c Φ

include hell hnu hFine in
theorem higherBandFamilyFirstAction_eq_physical :
    (∑ i : HigherBandFamilyIndex d D M q ad bd C lam ell N mu,
      higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) q C i.val.2 U p c Φ) =
      ∑ i, higherBandPhysicalFirstAction ad bd lam ell N mu D M q C U p c Φ i := by
  let F := fun (i : Fin (D-2) × Bool)
      e =>
    highPacketObservable ad bd (m := (higherBandFamilyGuardDegree M i)) (r := (higherBandFamilyTarget i)) (D := D) (q := q) C c
      (fun ζ z eps => ∏ j, localDensityReset ad bd z eps p
        (fun j l => higherBandCarrierFactor lam i.2 ζ l (U j)) j) Φ e
  exact higherBandFamily_signedIntegral_sum_eq_physical ad bd C lam ell N mu hell hnu hFine F

end

section
variable {d n m D : ℕ} (lam L T : ℝ) (fine : Bool) (U : DesignSample d n)

theorem integrated_cardinal_matrix_fin_cast (h : m = n) (lam T : ℝ)
    (U : DesignSample d n) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (U ∘ finCongr h) β β' = integratedCardinalMatrix lam T U β β' := by
  subst n
  rfl

theorem integrated_cardinal_matrix_full_subset (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (spatialSubsetConfiguration Finset.univ U) β β' =
      integratedCardinalMatrix lam T U β β' := by
  let S : Finset (Fin n) := Finset.univ
  let h : S.card = n := by simp [S]
  let e  := (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm
  let v : S ≃ Fin n := ⟨Subtype.val, (fun j => ⟨j, Finset.mem_univ j⟩),
    (by intro j; rfl), (by intro j; rfl)⟩
  let τ  := ((finCongr h).symm.trans e).trans v
  have hc : spatialSubsetConfiguration S U = (U ∘ τ) ∘ finCongr h := rfl
  rw [hc, integrated_cardinal_matrix_fin_cast h]
  exact integrated_cardinal_matrix_perm ..

theorem higherBandActualMatrix_full_subset :
    (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration Finset.univ U) : HighFrameIndex d D → _ → ℝ) =
      higherBandActualMatrix lam L T fine U := by
  funext β β'
  cases fine <;> simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
    globalCardinalBandMatrix, integrated_cardinal_matrix_full_subset]

end

theorem higherBandFirstAction_target_count {d n : ℕ} {ad bd lam L T : ℝ}
    (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hL : 0 < L) (hT : 1 ≤ T)
    (m D q : ℕ) (hn : 2 ≤ n) (hD : 1 ≤ D) (hnD : n ≤ D) (hnm : n ≤ m)
    (C : ℝ) (fine : Bool) {U : DesignSample d n} (hU : ∀ i j, |U i j| ≤ 2)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    higherBandFirstAction ad bd lam L T n m q C fine U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (higherBandActualMatrix lam L T fine U) c Φ := by
  rw [higherBandFirstAction_actual_count_expansion ha hab hlam hL hT n m D q hn hD hnD
    C fine hU hp c Φ, densityCountCoefficient_exact ad bd ha hab m n n (by omega) le_rfl hnm]
  simp [ite_true, (by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))), Finset.sum_singleton, one_mul, higherBandActualMatrix_full_subset]

end NearlyMinimax
