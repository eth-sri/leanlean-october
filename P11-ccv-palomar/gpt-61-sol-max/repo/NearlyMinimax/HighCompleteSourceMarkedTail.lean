module

public import NearlyMinimax.HighCompleteSourceSpatialTail

@[expose] public section

/-! Large-count factorial energy of the genuine canonical complete source
in the original periodic-frame field. All source field guards are derived;
the fixed tail constant precedes degree, count, history and spatial grid. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem crude_raw_square_energy_pointwise {d n } Chi η B
    (hChi : 0 ≤ Chi) (hB : 0 ≤ B)
    R
    (hcap : ∀ x y, |R x y| ≤ Chi^n*η^2*(B+1)) (x : Fin n → Covariate d) :
    selectedRawSquareEnergy R x ≤ (3*Chi^2)^n*η^4*(B+1)^2 := by
  have hp (y) : R x y ^ 2 ≤ Chi^(2*n)*η^4*(B+1)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Chi^n*η^2*(B+1))).mpr (hcap x y)
    simp only [sq_abs] at hh
    convert hh using 1 <;> (try rw [mul_pow,mul_pow,←pow_mul]) <;> ring
  have he : selectedRawSquareEnergy R x = ∑ y : Fin n → Fin 3, R x y ^ 2 := by
    unfold selectedRawSquareEnergy
    apply Finset.sum_congr (by ext y; simp)
    intro y _
    rfl
  calc
    _ = ∑ y : Fin n → Fin 3, R x y ^ 2 := he
    _ ≤ ∑ _y : Fin n → Fin 3, Chi^(2*n)*η^4*(B+1)^2 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = (3*Chi^2)^n*η^4*(B+1)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat, nsmul_eq_mul, mul_pow, ←pow_mul]
      ring

section Marked
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]

def highUnionSourceMarkedNumerator C (R : HighUnionRowData d k D I E)
    n a V η j
    h
    x y  :=
  highMarkedSampleNumerator n (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η
    (highUnionSourceDensity C R h) (highUnionSourceResetDensity C R j h)
    (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    ((highUnionSourceState C R h).2 j) x y

end Marked

end NearlyMinimax
