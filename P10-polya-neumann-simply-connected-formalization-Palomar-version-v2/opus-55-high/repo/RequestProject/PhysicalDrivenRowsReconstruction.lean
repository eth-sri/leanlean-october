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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set

theorem factorialGauge_inverse_at (z : ℂ) (d : ℕ → ℂ)
    {C a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ n, ‖d n‖ ≤ C * a ^ n) (k : ℕ) :
    (∑' j : ℕ, z ^ j / j.factorial * factorialGauge z d (j + k)) = d k := by
  have hshift (n : ℕ) : ‖d (n + k)‖ ≤ (C * a ^ k) * a ^ n := by
    refine (hd (n + k)).trans_eq ?_
    ring
  simpa only [factorialGauge, Nat.add_assoc, zero_add] using factorialGauge_inverse z (fun n => d (n + k))
      ha hshift

theorem physicalDrivenGauge_inverse_at
    (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (θ : ℝ) (k : ℕ) :
    (∑' j : ℕ, physicalDrivenCentered γ θ ^ j / j.factorial *
      physicalDrivenGauge γ E y (j + k) θ) = physicalDrivenScaledRow E y k θ := by
  have h := factorialGauge_inverse_at (physicalDrivenCentered γ θ)
    (fun n => physicalDrivenScaledRow E y n θ)
    (C := 2 * ‖y θ‖)  (norm_nonneg _)
    (fun n => (norm_physicalDrivenScaledRow_le E y n θ).trans_eq (by ring)) k
  assumption

theorem volterraPrimitiveIterate_iterate (a h : ℝ → ℂ) (j k : ℕ) :
    volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j =
      volterraPrimitiveIterate a h (j + k) := by
  induction j with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega]
    funext θ
    change (∫ s in 0..θ,
      a s * volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j s) =
      ∫ s in 0..θ, a s * volterraPrimitiveIterate a h (j + k) s
    simp_all

/-- Every scaled physical row is the actual Vekua boundary series of the
corresponding true primitive of the original zeroth gauge. -/
theorem physicalDrivenScaledRow_eq_volterraVekua_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (k : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenScaledRow E (physicalDrivenVector W g) k θ =
      (-E / 4) ^ k *
        (∑' j : ℕ, physicalVekuaCoeff E j * physicalDrivenCentered γ θ ^ j *
          volterraPrimitiveIterate (fun s => star (deriv γ s))
            (volterraPrimitiveIterate (fun s => star (deriv γ s))
              (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) k) j θ) := by
  rw [← physicalDrivenGauge_inverse_at γ E (physicalDrivenVector W g) θ k,
    ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [physicalDrivenGauge_eq_volterraPrimitiveIterate_of_intervalIntegrable
    hK hγ hW g hg (j + k) hθ,
    physicalDrivenQ_sq hE, volterraPrimitiveIterate_iterate, physicalVekuaCoeff]
  simp 
  ring

end PolyaNeumann

end
