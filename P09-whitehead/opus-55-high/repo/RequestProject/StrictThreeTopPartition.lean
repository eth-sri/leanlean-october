import RequestProject.QCubeThreeComponentRecovery


/-! Exact finite decomposition of a strict three-chain by its actual top cubes. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem strictThreeChain_top_partition (y : StrictOrdTet (QCube A) →₀ ℤ) :
    y = ∑ c ∈ y.support.image (·.1.2.2.2),
      y.filter (·.1.2.2.2 = c) := by
  classical
  ext t
  simp [Finsupp.finset_sum_apply]
  by_cases ht : y t = 0
  · simp [Finsupp.filter_apply, ht]
  · rw [Finset.sum_eq_single t.1.2.2.2]
    · simp
    · intro c _ hne
      simp [hne.symm]
    grind
