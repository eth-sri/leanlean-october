module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierPiece

/-!
# Collar comparison across the pieces of a piecewise `C¹` curve

The curve `γ` is continuous and piecewise `C¹`.  Choose a partition `a = t₀ < ⋯ < t_{N+1} = τ`
whose pieces carry `C¹` regularity, and apply `collar_piece` successively from the top piece
downwards; the top-face data of each piece is supplied by the piece above it.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {a a' b b' : ℝ}

/-- Monotonicity of the closed moving slab in its time interval. -/
theorem movingClosedSlab_mono  (ha : a ≤ a') (hb : b' ≤ b) :
    movingClosedSlab Ω γ a' b' ⊆ movingClosedSlab Ω γ a b :=
  fun _ hp => ⟨ha.trans hp.1, hp.2.1.trans hb, hp.2.2⟩

/-- Monotonicity of the active moving slab in its time interval. -/
theorem movingActiveSlab_mono  (ha : a ≤ a') (hb : b' ≤ b) :
    movingActiveSlab Ω γ a' b' ⊆ movingActiveSlab Ω γ a b :=
  fun _ hp => ⟨ha.trans hp.1, hp.2.1.trans_le hb, hp.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
