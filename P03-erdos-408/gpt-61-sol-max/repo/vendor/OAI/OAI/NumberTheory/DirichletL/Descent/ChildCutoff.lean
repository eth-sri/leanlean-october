module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.PoissonTails

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section


def childFrequencyBall (a : ActualEisensteinCubic.O) (R : ℝ)  :=
  (secondFrequencyCutoff (‖eisEmbedding a‖^2) R).filter
    (fun k => ‖eisEmbedding (a*k)‖^2 ≤ R)

section
variable (a : ActualEisensteinCubic.O) (ha : a ≠ 0) (R : ℝ)
include a ha R

section
variable (k : ActualEisensteinCubic.O)
include k

lemma mem_childFrequencyBall         :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma outside_childFrequencyBall        
    (hk : k ∉ childFrequencyBall a R) : R < ‖eisEmbedding (a*k)‖^2 :=
  lt_of_not_ge fun h => hk ((OAI.SevenEighths.InverseMoment.mem_childFrequencyBall a ha R k).mpr h)

def nonzeroChildFrequencyBall (a : ActualEisensteinCubic.O) (R : ℝ)  :=
  (childFrequencyBall a R).erase 0

lemma mem_nonzeroChildFrequencyBall         :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

end

lemma nonzeroChildFrequencyBall_empty       (hR : R < 1) :
    nonzeroChildFrequencyBall a R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hm := (mem_nonzeroChildFrequencyBall a ha R k).mp hk
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm
  exact (not_le_of_gt hR) ((EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq
    (a*k) (mul_ne_zero ha hk0)).trans hm.2)

end

end
end SevenEighths.InverseMoment

end OAI
