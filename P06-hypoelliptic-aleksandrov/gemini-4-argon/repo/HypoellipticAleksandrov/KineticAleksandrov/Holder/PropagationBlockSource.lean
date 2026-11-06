module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSign
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic

/-! # Vanishing localized source for the one-block Gaussian comparison -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/- The globally smooth glued Gaussian is smooth near every set. -/
theorem gaussianBarrier_isSmoothNear {d lam h}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v } (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (E : Set (KineticPoint d)) :
    IsSmoothNear (gaussianBarrier lam Lam H h L ell tminus sblock x v) E := by
  refine ⟨univ, isOpen_univ, subset_univ E, ?_⟩
  exact (contDiff_raw_gaussianBarrier hlam hh Lam H L ell tminus sblock hx hv).contDiffOn

/- Initial-strip comparison and the multiplied sign annihilate the localized source. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
