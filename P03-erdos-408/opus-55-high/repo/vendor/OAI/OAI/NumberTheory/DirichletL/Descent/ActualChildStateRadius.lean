module

public import OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseMoment
open InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)

def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta

def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)

theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1<Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hr := actual_second_row_radius_one p (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) (by grind) (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa)

end SevenEighths.InverseMoment
end

end OAI
