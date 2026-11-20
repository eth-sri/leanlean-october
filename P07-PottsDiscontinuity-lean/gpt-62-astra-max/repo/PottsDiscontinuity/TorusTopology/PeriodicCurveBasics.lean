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

variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (d : DirectedDart ω)

/-- Equality of geometric midpoints identifies both the original lifted vertex
and its oriented port. The reverse-oriented edge is excluded by the arrow field. -/
lemma loopMidpointPosition_eq_implies_lift_port_eq (a b : ℕ)
    (he : loopMidpointPosition h d a = loopMidpointPosition h d b) :
    loopLiftPosition h d a = loopLiftPosition h d b ∧
      ((directedStep h)^[a] d).val.2 = ((directedStep h)^[b] d).val.2 := by
  rcases (rotatedMidpoint_eq_iff _ _ _ _).mp he with hh | ⟨hz,hp⟩
  · exact hh
  · let e := (directedStep h)^[a] d
    let f := (directedStep h)^[b] d
    have hpz := loopLiftPosition_projection (ω := ω) (s := s) h d a
    have hpf := loopLiftPosition_projection (ω := ω) (s := s) h d b
    have hstep := loopLiftPosition_step_projection (hNp := (Fin.pos d.val.1.1)) (hMp := (Fin.pos d.val.1.2))
      s (d := e.val) (z := (loopLiftPosition h d a)) (congrArg Prod.fst hpz) (congrArg Prod.snd hpz)
    have hinc : (horizontalIncrement e.val,verticalIncrement e.val) = portVector e.val.2 := by
      rcases e with ⟨⟨v,p⟩,he⟩
      cases p <;> rfl
    have hvertex : f.val.1 = (edgeReverse e.val).1 := by
      rw [← hpf,hz,← hinc]
      exact hstep
    have heq : f.val = edgeReverse e.val := by
      apply Prod.ext hvertex
      change f.val.2 = oppositePort e.val.2 at hp
      rw [hp]
      rcases e with ⟨⟨v,p⟩,he⟩
      cases p <;> rfl
    have hout := f.property
    simp_all [heq, dartOut_edgeReverse, e.property]

/-- Nonzero winding makes the entire infinite midpoint lift injective. -/
theorem loopMidpointPosition_injective_of_nonzero_winding (i : Fin N) (j : Fin M)
    (hw : loopVertical j (directedLoopOf h d) ≠ 0 ∨
      loopSum (horizontalCross i) (directedLoopOf h d) ≠ 0) :
    Function.Injective (loopMidpointPosition h d) := by
  let L := loopPeriod h d
  let D := ((loopDeckDisplacement h d i j).1+(loopDeckDisplacement h d i j).2,
    (loopDeckDisplacement h d i j).2-(loopDeckDisplacement h d i j).1)
  have hD := (rotated_loopDeckDisplacement_ne_zero_iff ω s h d i j).mpr hw
  have hL := loopPeriod_pos h d
  have hper := loopMidpointPosition_add_period ω s h d i j
  intro a b he
  obtain ⟨hz,hp⟩ := loopMidpointPosition_eq_implies_lift_port_eq ω s h d a b he
  have horbit : (directedStep h)^[a] d = (directedStep h)^[b] d := by
    apply Subtype.ext
    apply Prod.ext
    · rw [← loopLiftPosition_projection,← loopLiftPosition_projection,hz]
    · exact hp
  have hmod : a%L = b%L := by
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (Nat.mod_lt a hL) (Nat.mod_lt b hL)).mp
    simpa only [L,Function.iterate_mod_minimalPeriod_eq] using horbit
  rw [periodic_translation_decompose _ L D hper a,
    periodic_translation_decompose _ L D hper b,hmod] at he
  have hsmul := add_left_cancel he
  have hdiv : a/L = b/L := by
    have hx := congrArg Prod.fst hsmul
    have hy := congrArg Prod.snd hsmul
    change (a/L : ℕ) • D.1 = (b/L : ℕ) • D.1 at hx
    change (a/L : ℕ) • D.2 = (b/L : ℕ) • D.2 at hy
    simp only [nsmul_eq_mul] at hx hy
    have hcoord : D.1 ≠ 0 ∨ D.2 ≠ 0 := by
      by_contra hn
      simp only [not_or,ne_eq,not_not] at hn
      exact hD (Prod.ext hn.1 hn.2)
    rcases hcoord with hx0 | hy0
    · exact_mod_cast (mul_right_cancel₀ hx0 hx)
    · exact_mod_cast (mul_right_cancel₀ hy0 hy)
  have ha := Nat.mod_add_div a L
  have hb := Nat.mod_add_div b L
  simp_all [hmod, hdiv]

end PottsDiscontinuity.TorusTopology
