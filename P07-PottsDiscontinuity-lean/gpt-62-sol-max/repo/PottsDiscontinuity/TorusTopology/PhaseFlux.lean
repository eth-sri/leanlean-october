module

public import PottsDiscontinuity.TorusTopology.WindingPhase
public import PottsDiscontinuity.Torus.DiamondSeamWinding

/-! Conserved seam flux splits equally among the modular phases. Each phase
of a chain winding b times has nonzero flux; this retains integer multiplicity. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus
open scoped Classical
variable {N M b : ℕ}
noncomputable section

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

/-- The seam edges starting at the given phase. -/
abbrev SeamPhase (g : FaceVertex N M true → ZMod b) (k : ZMod b) (e : OpenDiamondEdge A) : Prop :=
  e.val.2.val = 0 ∧ g (faceEndpoint hN hM true e.val false) = k

/-- Signed flux through selected seam endpoints. -/
def phaseFluxOn (g : FaceVertex N M true → ZMod b) (k : ZMod b)
    (X : FaceVertex N M true → Prop) (side : Bool) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  ∑ e with SeamPhase hN hM A g k e ∧ X (faceEndpoint hN hM true e.val side), f e

abbrev phaseFlux (g : FaceVertex N M true → ZMod b) (k : ZMod b) (f : OpenDiamondEdge A → ℚ) :=
  phaseFluxOn hN hM A g k (fun _ => True) false f

/-- A vertex predicate preserved off the seam selects equal arriving and departing fluxes. -/
theorem phaseFlux_conservation
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b) (hg : IsWindingPhase hN hM A c g)
    (f : diamondCycleSpace hN hM A) (hs : SupportedOnDiamondCluster hN hM A c f)
    (X : FaceVertex N M true → Prop)
    (hX : ∀ e : OpenDiamondEdge A, e.val.2.val ≠ 0 →
      (X (faceEndpoint hN hM true e.val true) ↔ X (faceEndpoint hN hM true e.val false)))
    (k : ZMod b) :
    phaseFluxOn hN hM A g (k + 1) X true f.val = phaseFluxOn hN hM A g k X false f.val := by
  let P (u : FaceVertex N M true) : ℚ := if g u = k ∧ X u then 1 else 0
  have hp := diamondBoundary_pairing hN hM A P f.val
  rw [f.property] at hp
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hp
  have hterm (e : OpenDiamondEdge A) :
      diamondCoboundary hN hM A P e * f.val e =
        (if SeamPhase hN hM A g (k + 1) e ∧ X (faceEndpoint hN hM true e.val true) then f.val e else 0) -
        (if SeamPhase hN hM A g k e ∧ X (faceEndpoint hN hM true e.val false) then f.val e else 0) := by
    by_cases hc : diamondEdgeCluster hN hM A e = c
    · have he := hg e hc
      by_cases hy : e.val.2.val = 0
      · simp only [hy, ite_true] at he
        have heq : g (faceEndpoint hN hM true e.val true) = k ↔
            g (faceEndpoint hN hM true e.val false) = k + 1 := by
          constructor <;> intro h <;> first | linear_combination h - he | linear_combination h + he
        simp [P, heq, sub_mul, SeamPhase, hy]
      · have heq := sub_eq_zero.mp (by simpa [hy] using he)
        simp [P, heq, hX e hy, SeamPhase, hy]
    · simp [hs e hc]
  apply sub_eq_zero.mp
  simpa only [hterm, phaseFluxOn, Finset.sum_filter, Finset.sum_sub_distrib] using hp.symm

/-- There are b equal phase fluxes; a total winding b makes each equal -1. -/
theorem phaseFlux_eq_neg_one (hb : 0 < b)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : IsWindingPhase hN hM A c g)
    (f : diamondCycleSpace hN hM A) (hs : SupportedOnDiamondCluster hN hM A c f)
    (hw : diamondWindingY A f.val = (b : ℚ)) (k : ZMod b) :
    phaseFlux hN hM A g k f.val = -1 := by
  let : NeZero b := ⟨hb.ne'⟩
  have hn (n : ℕ) : phaseFlux hN hM A g (n : ZMod b) f.val = phaseFlux hN hM A g 0 f.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ← ih]
      simpa [phaseFluxOn] using
              phaseFlux_conservation hN hM A c g hg f hs (fun _ => True) (by simp) (n : ZMod b)
  have hall (t : ZMod b) : phaseFlux hN hM A g t f.val = phaseFlux hN hM A g 0 f.val := by
    rw [← ZMod.natCast_zmod_val t]
    exact hn t.val
  have htotal : (∑ t : ZMod b, phaseFlux hN hM A g t f.val) = -diamondWindingY A f.val := by
    simp only [phaseFlux, phaseFluxOn, and_true, SeamPhase, ← Finset.filter_filter]
    rw [Finset.sum_fiberwise]
    simp only [diamondWindingY, diamondSeamCrossY, Finset.sum_filter, ite_mul, neg_one_mul, zero_mul]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => by split <;> simp_all
  simp_rw [hall] at htotal
  rw [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,hw] at htotal
  have h0 : phaseFlux hN hM A g 0 f.val = -1 := by
    have hbq : (b : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hbq
    simpa using htotal
  rw [hall,h0]

end

end
end PottsDiscontinuity.TorusTopology
