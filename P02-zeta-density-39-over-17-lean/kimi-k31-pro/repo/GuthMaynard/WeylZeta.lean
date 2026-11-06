module
public import GuthMaynard.WeylExplicit
public import GuthMaynard.NativeSource.GuthMaynard.WeylZeta
public import ModuleExport

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

export_module GuthMaynard.NativeSource.GuthMaynard.WeylZeta from GuthMaynard.NativeMoment

/-- The actual critical-line Dirichlet block on `[A, A + N)`. -/
noncomputable def criticalLineWeylBlock (Y : Real) (A N : Nat) : Complex :=
  ∑ n ∈ Finset.range N,
    (1 / Real.sqrt (A + n) : Real) •
      unitaryPhase (logarithmicPhase (Y ^ 3) (A + n))

theorem criticalLineTerm_eq_cpow (Y : Real) (m : Nat) (hm : 0 < m) :
    (1 / Real.sqrt m : Real) • unitaryPhase (logarithmicPhase (Y ^ 3) m) =
      (m : Complex) ^ (-((1 / 2 : Complex) + (Y ^ 3 : Complex) * I)) := by
  have hw : (1 / Real.sqrt m : Real) =
      (m : Real) ^ (-(1 / 2 : Real)) := by
    rw [Real.sqrt_eq_rpow, one_div, Real.rpow_neg (Nat.cast_nonneg m)]
  rw [Complex.real_smul, unitaryPhase_logarithmicPhase_eq_cpow _ _ hm, hw]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]
  simp only [Complex.ofReal_natCast]
  rw [← Complex.cpow_add _ _ (by exact_mod_cast Nat.ne_of_gt hm)]
  congr 2
  push_cast
  ring

theorem criticalLineWeylBlock_eq_cpow
    (Y : Real) (A N : Nat) (hA : 0 < A) :
    criticalLineWeylBlock Y A N =
      ∑ n ∈ Finset.range N,
        (A + n : Complex) ^ (-((1 / 2 : Complex) + (Y ^ 3 : Complex) * I)) := by
  unfold criticalLineWeylBlock
  apply Finset.sum_congr rfl
  intro n _hn
  simpa only [Nat.cast_add] using criticalLineTerm_eq_cpow Y (A + n) (by omega)

/-- Abel summation transfers the uniform prefix Weyl estimate to the genuine
`n^(-1/2-it)` critical-line weight. -/
theorem norm_criticalLineWeylBlock_le
    (Y : Real) (A N : Nat) (hY : 1 <= Y) (hA : 0 < A) (hN : 0 < N)
    (hYA : Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) (hNA : N <= A) :
    ‖criticalLineWeylBlock Y A N‖ <= 30 * Real.sqrt Y := by
  let f : Nat -> Real := fun n => 1 / Real.sqrt (A + n)
  let g : Nat -> Complex := fun n =>
    unitaryPhase (logarithmicPhase (Y ^ 3) (A + n))
  have hweighted := norm_weighted_sum_le_of_antitone f g N
    (30 * Real.sqrt ((A : Real) * Y)) hN
    (fun i _hi => by dsimp only [f]; positivity)
    (fun i _hi => by
      dsimp only [f]
      apply one_div_le_one_div_of_le
      · positivity
      · apply Real.sqrt_le_sqrt
        exact_mod_cast (show A + i <= A + (i + 1) by omega))
    (fun j hj => by
      dsimp only [g]
      rw [← logarithmicSum_eq_sum_range]
      exact logarithmic_weyl_exponent_pair_prefix Y A j hY hA hYA hAY
        (hj.trans hNA))
  change ‖criticalLineWeylBlock Y A N‖ <= _
  rw [show criticalLineWeylBlock Y A N = ∑ n ∈ Finset.range N, f n • g n by rfl]
  have hbase : Real.sqrt ((A : Real) * Y) =
      Real.sqrt A * Real.sqrt Y := by
    rw [Real.sqrt_mul (Nat.cast_nonneg A)]
  have hsqrtA : 0 < Real.sqrt (A : Real) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hA)
  have hsimplify : f 0 * (30 * Real.sqrt ((A : Real) * Y)) =
      30 * Real.sqrt Y := by
    dsimp only [f]
    simp only [Nat.cast_zero, add_zero]
    rw [hbase]
    field_simp [hsqrtA.ne']
  rw [hsimplify] at hweighted
  exact hweighted

end RiemannZeta.GuthMaynard
