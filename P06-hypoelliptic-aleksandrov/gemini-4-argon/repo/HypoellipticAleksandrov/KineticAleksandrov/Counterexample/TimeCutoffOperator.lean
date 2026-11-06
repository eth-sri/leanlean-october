module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffDifference

/-! # The actual backward operator of the cutoff profile -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory HypoellipticAleksandrov.Parabolic

/-- The native spatial slice of the barrier is smooth at every finite order. -/
theorem contDiff_nativeBarrier (d : ℕ) (mu R t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : XV d => barrier mu R ⟨t, q.1, q.2⟩) := by
  simpa only [barrier] using!
    (contDiff_const (c := Real.exp (-mu * t))).mul ((contDiff_const (c := (2 : ℝ))).sub
      ((PDE.contDiff_vecNormSq.comp contDiff_snd).div_const (R ^ 2)))

/-- The cutoff's time derivative differentiates only the explicit exponential barrier. -/
theorem timeCutoffProfile_timeDerivative {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R) P =
      -deriv timeCutoffTheta (selectedFlatProfile h r (P.position, P.velocity) -
        barrier mu R P) * kineticTimeDerivative (barrier mu R) P := by
  have hb := (((hasDerivAt_id P.time).const_mul (-mu)).exp).mul_const
    (2 - PDE.vecNormSq P.velocity / R ^ 2)
  have hi := hb.const_sub (selectedFlatProfile h r (P.position, P.velocity))
  have ht : DifferentiableAt ℝ timeCutoffTheta
      (selectedFlatProfile h r (P.position, P.velocity) - barrier mu R P) :=
    (contDiff_timeCutoffTheta.differentiable (by simp)).differentiableAt
  have he := ht.hasDerivAt.comp P.time hi
  change HasDerivAt
    (fun s => timeCutoffProfile (profileFunction h) alpha r mu R
      ⟨s, P.position, P.velocity⟩) _ P.time at he
  change deriv (fun s => timeCutoffProfile (profileFunction h) alpha r mu R
    ⟨s, P.position, P.velocity⟩) P.time = _
  rw [he.deriv, barrier_timeDerivative]
  simp only [selectedFlatProfile, barrier, id_eq, mul_one]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
