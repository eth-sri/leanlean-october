module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.ScalarMultiplication

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.TestPairings

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

open MeasureTheory KPContLocalNorm

theorem finite_jet_bound_of_sobolev_representative {n : ℕ}
    (A C : LocalBall n) (hAC : KPContLocalCubeEmbedding.closedCarrier A ⊆ C.carrier)
    (m : ℕ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (w : IntegerSobolev C (m + n)) (g : Space n → ℂ),
      ContDiffOn ℝ (⊤ : ℕ∞) g C.carrier →
      (g =ᵐ[volume.restrict C.carrier]
        (fun x => w.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n (m + n)) x)) →
      ∀ α : MultiIndex n m, ∀ x ∈ KPContLocalCubeEmbedding.closedCarrier A,
        ‖coordinateDerivative α g x‖ ≤ E * w.sobolevNorm := by
  obtain ⟨E, hE, hbound⟩ :=
    KPLocalCubeSobolevJets.finite_order_representative_interior_jet_bound A C hAC m
  refine ⟨E, hE, ?_⟩
  intro w g hg hgw α x hx
  obtain ⟨j, hj, hjbound⟩ := hbound w g (hg.of_le (by simp)) hgw
  letI : CompactSpace (KPContLocalCubeEmbedding.closedCarrier A) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall A.center A.radius)
  rw [← hj α ⟨x, hx⟩]
  exact (ContinuousMap.norm_coe_le_norm (j α) ⟨x, hx⟩).trans
    ((norm_le_pi_norm j α).trans hjbound)

theorem hilbert_difference_small {H : Type*} [NormedAddCommGroup H]
    (O : Set ℂ) (v : ℂ → H) (hv : ContinuousOn v O)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ O, dist z z₀ < δ → ‖v z - v z₀‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.mp (hv z₀ hz₀) ε hε
  exact ⟨δ, hδ, fun z hz hdist => by simpa [dist_eq_norm] using h hz hdist⟩

def subtractSobolev {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) : IntegerSobolev B k where
  derivatives α := u.derivatives α - v.derivatives α
  weak_derivatives α := weak_derivative_sub B α _ _ _ _
    (u.weak_derivatives α) (v.weak_derivatives α)

def scaleSobolev {n k : ℕ} {B : LocalBall n}
    (c : ℂ) (u : IntegerSobolev B k) : IntegerSobolev B k where
  derivatives α := c • u.derivatives α
  weak_derivatives α := weak_derivative_smul B α c _ _ (u.weak_derivatives α)

theorem scaleSobolev_norm {n k : ℕ} {B : LocalBall n}
    (c : ℂ) (u : IntegerSobolev B k) :
    (scaleSobolev c u).sobolevNorm = ‖c‖ * u.sobolevNorm := by
  unfold IntegerSobolev.sobolevNorm IntegerSobolev.normSq
  simp only [scaleSobolev, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_norm]

theorem subtractSobolev_norm_le {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) :
    (subtractSobolev u v).sobolevNorm ≤ 2 * (u.sobolevNorm + v.sobolevNorm) := by
  have hu : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hv : 0 ≤ v.sobolevNorm := Real.sqrt_nonneg _
  have hsq : (subtractSobolev u v).sobolevNorm ^ 2 ≤
      2 * (u.sobolevNorm ^ 2 + v.sobolevNorm ^ 2) := by
    rw [IntegerSobolev.sobolevNorm_sq, IntegerSobolev.sobolevNorm_sq,
      IntegerSobolev.sobolevNorm_sq]
    unfold IntegerSobolev.normSq
    simp only [subtractSobolev]
    calc
      _ ≤ ∑ α : MultiIndex n k, 2 * (‖u.derivatives α‖ ^ 2 + ‖v.derivatives α‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro α _
        have h := norm_sub_le (u.derivatives α) (v.derivatives α)
        have hnn := norm_nonneg (u.derivatives α - v.derivatives α)
        nlinarith [norm_nonneg (u.derivatives α), norm_nonneg (v.derivatives α),
          sq_nonneg (‖u.derivatives α‖ - ‖v.derivatives α‖)]
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hnn : 0 ≤ (subtractSobolev u v).sobolevNorm := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hu hv]

theorem subtractSobolev_represents {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) (f g : Space n → ℂ)
    (hu : (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] f)
    (hv : (fun x => v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] g) :
    (fun x => (subtractSobolev u v).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] (fun x => f x - g x) := by
  filter_upwards [hu, hv, Lp.coeFn_sub
    (u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))
    (v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))] with x hx hy hsub
  change (u.derivatives _ - v.derivatives _) x = _
  simpa only [Pi.sub_apply, hx, hy] using hsub

theorem scaleSobolev_represents {n k : ℕ} {B : LocalBall n}
    (c : ℂ) (u : IntegerSobolev B k) (f : Space n → ℂ)
    (hu : (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] f) :
    (fun x => (scaleSobolev c u).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] (fun x => c * f x) := by
  filter_upwards [hu, Lp.coeFn_smul c
    (u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))] with x hx hsmul
  change (c • u.derivatives _) x = _
  simpa only [Pi.smul_apply, smul_eq_mul, hx] using hsmul

def addSobolev {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) : IntegerSobolev B k :=
  subtractSobolev u (scaleSobolev (-1) v)

theorem addSobolev_norm_le {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) :
    (addSobolev u v).sobolevNorm ≤ 2 * (u.sobolevNorm + v.sobolevNorm) := by
  simpa only [addSobolev, scaleSobolev_norm, norm_neg, norm_one, one_mul] using
    subtractSobolev_norm_le u (scaleSobolev (-1) v)

theorem addSobolev_represents {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) (f g : Space n → ℂ)
    (hu : (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] f)
    (hv : (fun x => v.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] g) :
    (fun x => (addSobolev u v).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
      =ᵐ[volume.restrict B.carrier] (fun x => f x + g x) := by
  change (fun x => (subtractSobolev u (scaleSobolev (-1) v)).derivatives
      (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x)
    =ᵐ[volume.restrict B.carrier] (fun x => f x + g x)
  simpa only [neg_one_mul, sub_neg_eq_add] using
    subtractSobolev_represents u (scaleSobolev (-1) v) f (fun x => (-1 : ℂ) * g x)
      hu (scaleSobolev_represents (-1) v g hv)

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

end
