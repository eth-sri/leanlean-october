module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusEstimates
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrier

/-! # The anisotropic modulus of the zero-extended homogeneous barrier -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set BarrierRegularization

/-- The source's selected witness and its modulus are chosen before any coefficient field.
Thus both constants and the witness have only the source parameter dependencies. -/
theorem exists_bellman_barrier_with_modulus (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simp_all) - 2 < alpha)
    (ha1 : alpha < 1) :
    ∃ phi : (ℝ × ℝ) → ℝ, ∃ c C : ℝ,
      IsBellmanHomogeneous alpha phi ∧ 0 < c ∧ 0 ≤ C ∧
      (∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
        c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q) ∧
      ∀ z w : ℝ × ℝ,
        |bellmanOriginExtension phi z - bellmanOriginExtension phi w| ≤
          C * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha) := by
  obtain ⟨hlo, _, hb⟩ := exists_bellman_barrier lam Lam hlam hLam
  obtain ⟨phi, c, hhom, hc, hbound⟩ := hb alpha ha ha1
  have ha0 : 0 < alpha := lt_of_le_of_lt (sub_nonneg.mpr hlo) ha
  obtain ⟨C, hC, hmod⟩ := barrier_coordinate_modulus hhom ha0 ha1
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
