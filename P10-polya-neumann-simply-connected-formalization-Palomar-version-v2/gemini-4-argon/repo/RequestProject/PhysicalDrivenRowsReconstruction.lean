module

public import RequestProject.PhysicalDrivenL2Reconstruction
public import RequestProject.PhysicalVolterraNormalization

/-!
# All genuine driven rows from the same original boundary input

The absolutely convergent factorial inverse applies at every row index.
The actual primitive recurrence then reconstructs each row from the same
zeroth gauge, at the original fixed real energy.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set

theorem factorialGauge_inverse_at z d
    {C a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ n, ‖d n‖ ≤ C * a ^ n) k :
    (∑' j : ℕ, z ^ j / (j.factorial : ℂ) * factorialGauge z d (j + k)) = d k := by
  have hshift n : ‖d (n + k)‖ ≤ C * a ^ k * a ^ n := by
    refine (hd (n + k)).trans_eq ?_
    rw [pow_add]
    ring
  simpa [factorialGauge, Nat.add_assoc] using factorialGauge_inverse z (fun n => d (n + k)) (C := C * a ^ k) (a := a) ha hshift

theorem physicalDrivenGauge_inverse_at
    γ E y θ k :
    (∑' j : ℕ, physicalDrivenCentered γ θ ^ j / (j.factorial : ℂ) *
      physicalDrivenGauge γ E y (j + k) θ) = physicalDrivenScaledRow E y k θ := by
  simpa [factorialGauge, physicalDrivenGauge, physicalDrivenGaugeTerm, physicalDrivenPower] using factorialGauge_inverse_at (physicalDrivenCentered γ θ) (fun n => physicalDrivenScaledRow E y n θ) (C := 2 * ‖y θ‖) (a := ‖physicalDrivenQ E‖) (norm_nonneg _) (fun n => (norm_physicalDrivenScaledRow_le E y n θ).trans_eq (by ring)) k

theorem volterraPrimitiveIterate_iterate a h j k :
    volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j =
      volterraPrimitiveIterate a h (j + k) := by
  induction j with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    rw [show j + 1 + k = j + k + 1 by omega]
    funext θ
    change (∫ s in 0..θ,
      a s * volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j s) =
      ∫ s in 0..θ, a s * volterraPrimitiveIterate a h (j + k) s
    rw [ih]

/-- Every scaled physical row is the actual Vekua boundary series of the
corresponding true primitive of the original zeroth gauge. -/
theorem physicalDrivenScaledRow_eq_volterraVekua_of_intervalIntegrable
      (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
     (hE : 0 ≤ E)  (hW : IsTransport γ E W)
    g (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    k  (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenScaledRow E (physicalDrivenVector W g) k θ =
      (-(E : ℂ) / 4) ^ k *
        (∑' j : ℕ, physicalVekuaCoeff (E : ℂ) j * physicalDrivenCentered γ θ ^ j *
          volterraPrimitiveIterate (fun s => star (deriv γ s))
            (volterraPrimitiveIterate (fun s => star (deriv γ s))
              (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) k) j θ) := by
  rw [← physicalDrivenGauge_inverse_at γ E (physicalDrivenVector W g) θ k,
    ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable
    hK hγ hW g hg (j + k) hθ,
    physicalDrivenQ_sq hE, volterraPrimitiveIterate_iterate, physicalVekuaCoeff, pow_add]
  simp only [starRingEnd_apply]
  ring

end PolyaNeumann

end
