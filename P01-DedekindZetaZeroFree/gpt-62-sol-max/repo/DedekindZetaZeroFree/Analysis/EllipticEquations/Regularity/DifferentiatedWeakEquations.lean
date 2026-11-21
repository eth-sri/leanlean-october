module

public import DedekindZetaZeroFree.Analysis.Sobolev.Restriction.BallNormMonotonicity
public import DedekindZetaZeroFree.Analysis.EllipticEquations.Regularity.MultiIndexCommutatorPairing

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

open MeasureTheory KPContLocalNorm
namespace Raw
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

def SmoothNearClosedBall {n : ℕ} {outer : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients outer cρ Cρ κ Λ) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧
    Metric.closedBall outer.center outer.radius ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) D.density U ∧
    ∀ i j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => D.matrix x i j) U

def BoundedCoefficientDerivatives {n : ℕ} {outer : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (k : ℕ) (L : ℝ) : Prop :=
  ∀ α : MultiIndex n k, ∀ x ∈ outer.carrier,
    ‖coordinateDerivative α (fun y => (D.density y : ℂ)) x‖ ≤ L ∧
    ∀ i j : Fin n,
      ‖coordinateDerivative α
        (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x‖ ≤ L

def WeakIntegerEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (r : ℕ) (M C : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ M →
    ∀ (u : IntegerSobolev outer 1) (h : IntegerSobolev outer r),
      WeakEquation D z u (value h) →
      ∃ v : IntegerSobolev inner (r + 2),
        Represents v (fun x => value u x) ∧
        v.sobolevNorm ≤ C * (‖value u‖ + h.sobolevNorm)

end Raw

def restrictCoefficients {n : ℕ} {inner outer : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hsub : inner.carrier ⊆ outer.carrier)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ) :
    KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients inner cρ Cρ κ Λ where
  density := D.density
  matrix := D.matrix
  density_smooth := D.density_smooth.mono hsub
  matrix_smooth i j := (D.matrix_smooth i j).mono hsub
  density_bounds x hx := D.density_bounds x (hsub hx)
  symmetric x hx := D.symmetric x (hsub hx)
  ellipticity x hx := D.ellipticity x (hsub hx)
  upper_bound x hx := D.upper_bound x (hsub hx)

open KPContLocalEnergy
open KPContLocalEnergy.SobolevEnergyEstimates.Raw hiding gradient value

theorem restrictWeakEquation {n : ℕ} {inner outer : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (hsub : inner.carrier ⊆ outer.carrier)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ)
    (z : ℂ) (u : IntegerSobolev outer 1) (h : BallL2 outer)
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u h) :
    WeakEquation (restrictCoefficients hsub D) z (restrictSobolev hsub u) (restrictBallL2 hsub h) := by
  intro φ
  let ψ : TestFunction outer.toOpens ℂ ⊤ :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hsub⟩
  have heqOuter := heq ψ
  have hgrad : ∀ᵐ x ∂volume.restrict inner.carrier,
      ∀ j, gradient (restrictSobolev hsub u) j x = gradient u j x := by
    apply ae_all_iff.mpr
    intro j
    exact restrictBallL2_ae hsub _
  have hv := restrictSobolev_represents hsub u
  have hh := restrictBallL2_ae hsub h
  change (∫ x in inner.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient (restrictSobolev hsub u) j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in inner.carrier, (D.density x : ℂ) * value (restrictSobolev hsub u) x * star (φ x)) =
        ∫ x in inner.carrier, (D.density x : ℂ) * restrictBallL2 hsub h x * star (φ x)
  have hi : (∫ x in inner.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient (restrictSobolev hsub u) j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      ∫ x in outer.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x) := by
    trans ∫ x in inner.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)
    · apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      simp only [hx]
    · symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
      intro x hx
      have hz : ∀ i, coordinateDerivativeList [i] (fun y => φ y) x = 0 := by
        intro i
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact hx.2 (φ.tsupport_subset (coordinateDerivativeList_tsupport_subset [i] _ hm))
      simp [hz]
  have h0 (f : BallL2 outer) :
      (∫ x in inner.carrier, (D.density x : ℂ) * restrictBallL2 hsub f x * star (φ x)) =
      ∫ x in outer.carrier, (D.density x : ℂ) * f x * star (φ x) := by
    trans ∫ x in inner.carrier, (D.density x : ℂ) * f x * star (φ x)
    · apply integral_congr_ae
      filter_upwards [restrictBallL2_ae hsub f] with x hx
      rw [hx]
    · symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
      intro x hx
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx.2 (φ.tsupport_subset hm))
      simp [hz]
  rw [hi, h0 h]
  change (∫ x in outer.carrier, _) - z * (∫ x in inner.carrier,
    (D.density x : ℂ) * restrictBallL2 hsub (value u) x * star (φ x)) = _
  rw [h0 (value u)]
  exact heqOuter

theorem restrict_weak_equation {n : ℕ} {inner outer : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (hsub : inner.carrier ⊆ outer.carrier)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ)
    (z : ℂ) (u : IntegerSobolev outer 1) (h : BallL2 outer)
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u h) :
    ∃ (v : IntegerSobolev inner 1) (g : BallL2 inner),
      (∀ α : MultiIndex n 1, ∀ᵐ x ∂volume.restrict inner.carrier,
        v.derivatives α x = u.derivatives α x) ∧
      (∀ᵐ x ∂volume.restrict inner.carrier, g x = h x) ∧
      v.sobolevNorm ≤ u.sobolevNorm ∧ ‖g‖ ≤ ‖h‖ ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation (restrictCoefficients hsub D) z v g := by
  refine ⟨restrictSobolev hsub u, restrictBallL2 hsub h,
    (fun α => restrictBallL2_ae hsub _), restrictBallL2_ae hsub h,
    sobolevNorm_restrictSobolev_le hsub u, norm_restrictBallL2_le hsub h,
    restrictWeakEquation hsub D z u h heq⟩

export WeakJets.Raw (Counts counts indexOfCounts jet coefficientJet unitCount multiChoose
  commutatorSource list_smooth derivativeTest jet_weak_derivative)
open WeakJets.Raw (counts_first counts_zero)

theorem shifted_jet_sobolev {n r : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B (r + 1)) (α : MultiIndex n r) :
    ∃ w : IntegerSobolev B 1, ∀ δ : MultiIndex n 1,
      w.derivatives δ = jet u (counts α + counts δ) := by
  have hab (δ : MultiIndex n 1) : (∑ i, (counts α + counts δ) i) ≤ r + 1 := by
    simpa only [Pi.add_apply, Finset.sum_add_distrib, counts] using
      Nat.add_le_add α.property δ.property
  have ha : (∑ i, counts α i) ≤ r + 1 := α.property.trans (Nat.le_succ r)
  have hz : counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n 1) = 0 := rfl
  refine ⟨⟨fun δ => jet u (counts α + counts δ), ?_⟩, fun _ => rfl⟩
  intro δ
  change IsWeakDerivative B δ (jet u (counts α + counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n 1))) _
  rw [hz, add_zero]
  exact jet_weak_derivative u α δ ha (hab δ)

theorem differentiated_weak_equation_of_jet_pairing {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B (r + 1)) (h : IntegerSobolev B r)
    (α : MultiIndex n r)
    (hg : MemLp (commutatorSource D z u h α) 2 (volume.restrict B.carrier))
    (hpair : ∀ φ : TestFunction B.toOpens ℂ ⊤,
      (∫ x in B.carrier, (D.density x : ℂ) *
        ∑ i, ∑ j, (D.matrix x i j : ℂ) * jet u (counts α + unitCount j) x *
          star (coordinateDerivativeList [i] (fun y => φ y) x)) -
        z * (∫ x in B.carrier, (D.density x : ℂ) * jet u (counts α) x * star (φ x)) =
      ∫ x in B.carrier, (D.density x : ℂ) * commutatorSource D z u h α x * star (φ x)) :
    ∃ w : IntegerSobolev B 1,
      (∀ δ : MultiIndex n 1, ∀ᵐ x ∂volume.restrict B.carrier,
        w.derivatives δ x = jet u (counts α + counts δ) x) ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z w
        (hg.toLp (commutatorSource D z u h α)) := by
  obtain ⟨w, hw⟩ := shifted_jet_sobolev u α
  refine ⟨w, fun δ => Filter.Eventually.of_forall (fun x => congrArg (fun f : BallL2 B => f x) (hw δ)), ?_⟩
  intro φ
  have hgrad (j : Fin n) : KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient w j =
      jet u (counts α + unitCount j) := by
    simpa only [KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient, counts_first] using
      hw (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)
  have hvalue : KPContLocalEnergy.SobolevEnergyEstimates.Raw.value w = jet u (counts α) := by
    simpa only [KPContLocalEnergy.SobolevEnergyEstimates.Raw.value, counts_zero, add_zero] using
      hw (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n 1)
  change (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient w j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.value w x * star (φ x)) = _
  simp only [hgrad, hvalue]
  rw [hpair φ]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem differentiated_weak_equation {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (z : ℂ)
    (u₁ : IntegerSobolev B 1) (u : IntegerSobolev B (r + 1))
    (h : IntegerSobolev B r)
    (hu : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u
      (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x))
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u₁
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h))
    (α : MultiIndex n r)
    (hg : MemLp (commutatorSource D z u h α) 2 (volume.restrict B.carrier)) :
    ∃ w : IntegerSobolev B 1,
      (∀ δ : MultiIndex n 1, ∀ᵐ x ∂volume.restrict B.carrier,
        w.derivatives δ x = jet u (counts α + counts δ) x) ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z w
        (hg.toLp (commutatorSource D z u h α)) := by
  exact differentiated_weak_equation_of_jet_pairing D z u h α hg
    (WeakJets.Raw.differentiated_pairing (WeakJets.Raw.weak_product_rule B)
      (WeakJets.Raw.weak_product_rule B) D hcρ z u₁ u h hu heq α)

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

end
