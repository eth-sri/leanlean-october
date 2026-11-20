module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ClassicalLink
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ChainGeometry

/-! # Chaining the local comparison

The attenuation at each step is at most one, so the additive error grows at most
linearly in the number of links. Taking the source bound to be zero gives Harnack.
-/
@[expose] public section
namespace HypoellipticAleksandrov.Parabolic
open Set KrylovEstimate

theorem unit_harnack_with_source
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam) (Lam : ℝ) (hLL : lam ≤ Lam) :
    let U := parabolicInterior 1 (0 : PDE.Vec N)
    ∃ h E : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 ≤ E ∧
      ∀ (B : CoefficientField N) (u : TimeVelocity N → ℝ) (M : ℝ), 0 ≤ M →
        IsContinuousCoefficientOn B U → HasLowerEllipticityOn lam B U →
        HasUpperEllipticityOn Lam B U → IsScalarC12On u U → IsNonnegativeOn u U →
        (∀ z ∈ U, |residual (coefficientAt B) u z| ≤ M) →
        ∀ P ∈ Ioo (1/4 : ℝ) (1/2) ×ˢ PDE.euclideanBall (0 : PDE.Vec N) (1/2),
          ∀ P' ∈ Ioo (3/4 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) (1/2),
            h * u P ≤ u P' + E * M := by
  intro U
  obtain ⟨h, E, hh, hh1, hE, link⟩ := exists_classical_harnack_link N hN lam hlam Lam hLL
  let m := 256 * N
  refine ⟨h^m, m*E, pow_pos hh _, pow_le_one₀ hh.le hh1, by positivity, ?_⟩
  intro B u M hM hc hlo hhi hu hn hf P hP P' hP'
  let dt := (P'.1-P.1)/(m : ℝ)
  let r := Real.sqrt dt
  let t (k : ℕ) := P.1 + k*dt
  let v (k : ℕ) := P.2 + ((k : ℝ)/m) • (P'.2-P.2)
  obtain ⟨hr1, hr, hstart, hend, htstep, hboxes, hvstep⟩ :=
    unitCylinder_harnack_link_geometry N hN P P' hP hP'
  have chain (k : ℕ) (hk : k ≤ m) : h^k*u P ≤ u (t k, v k) + k*E*M := by
    induction k with
    | zero => simpa [show (t 0, v 0) = P from hstart]
    | succ k ih =>
      have hkm := Nat.lt_of_succ_le hk
      have hl := link B u M hM hc hlo hhi hu hn hf (t k) (v k) r hr hr1 (hboxes k hkm) _ (hvstep k hkm)
      rw [show t k+r^2 = t (k+1) from (htstep k hkm).symm] at hl
      have h₁ := mul_le_mul_of_nonneg_left (ih hkm.le) hh.le
      have h₂ := mul_le_of_le_one_left (show 0 ≤ (k : ℝ)*E*M by positivity) hh1
      rw [pow_succ, Nat.cast_succ]
      linarith
  simpa only [show (t m, v m) = P' from hend] using chain m le_rfl

end HypoellipticAleksandrov.Parabolic
