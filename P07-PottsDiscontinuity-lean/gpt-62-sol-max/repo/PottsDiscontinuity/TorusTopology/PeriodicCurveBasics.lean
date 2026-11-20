module

public import PottsDiscontinuity.TorusTopology.PeriodicMidpointLift

/-! Simplicity of the complete periodic lift, rather than only its first period. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops TorusRC
open PottsDiscontinuity.SixVertex
variable {N M : ℕ}

lemma periodic_translation_decompose (f : ℕ → ℤ × ℤ) (L : ℕ) (D : ℤ × ℤ)
    (h : ∀ n, f (n+L) = f n+D) (n : ℕ) :
    f n = f (n%L) + (n/L) • D := by
  have hh (a k : ℕ) : f (a+k*L) = f a + k • D := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul,← Nat.add_assoc,h,ih,add_nsmul]
      abel
  conv_lhs => rw [← Nat.mod_add_div n L]
  rw [Nat.mul_comm L,hh]

section

variable
  (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s)
    (d : DirectedDart ω)

/-- Nonzero winding makes the entire infinite midpoint lift injective. -/
theorem loopMidpointPosition_injective_of_nonzero_winding (i : Fin N) (j : Fin M)
    (hw : loopVertical ω s h j (directedLoopOf ω s h d) ≠ 0 ∨
      loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d) ≠ 0) :
    Function.Injective (loopMidpointPosition ω s h d) := by
  let L := loopPeriod ω s h d
  let D := ((loopDeckDisplacement ω s h d i j).1+(loopDeckDisplacement ω s h d i j).2,
    (loopDeckDisplacement ω s h d i j).2-(loopDeckDisplacement ω s h d i j).1)
  have hD : D ≠ (0,0) := (rotated_loopDeckDisplacement_ne_zero_iff ω s h d i j).mpr hw
  have hL : 0 < L := loopPeriod_pos ω s h d
  have hper := loopMidpointPosition_add_period ω s h d i j
  intro a b he
  obtain ⟨hz,hp⟩ := loopMidpointPosition_eq_implies_lift_port_eq ω s h d a b he
  have horbit : (directedStep ω s h)^[a] d = (directedStep ω s h)^[b] d := by
    apply Subtype.ext
    apply Prod.ext
    · simp [← loopLiftPosition_projection, hz]
    · exact hp
  have hmod : a%L = b%L := by
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (Nat.mod_lt a hL) (Nat.mod_lt b hL)).mp
    simp_all
  rw [periodic_translation_decompose _ L D hper a,
    periodic_translation_decompose _ L D hper b,hmod] at he
  have hdiv : a/L = b/L := Int.ofNat.inj (smul_left_injective ℤ hD (by
    change ((a / L : ℕ) : ℤ) • D = ((b / L : ℕ) : ℤ) • D
    simpa only [natCast_zsmul] using add_left_cancel he))
  have ha := Nat.mod_add_div a L
  have hb := Nat.mod_add_div b L
  rw [hmod,hdiv] at ha
  exact ha.symm.trans hb

end

end PottsDiscontinuity.TorusTopology
