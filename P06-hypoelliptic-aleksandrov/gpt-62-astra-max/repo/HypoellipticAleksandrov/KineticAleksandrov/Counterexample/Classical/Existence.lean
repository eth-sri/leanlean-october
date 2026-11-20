module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.ScalarLift
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSolver

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

theorem classicalProfile_exists {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (ha : 0 < α) (ha1 : α < 1) :
    Nonempty (ClassicalProfile d α) := by
  by_cases he : d = 1
  · subst d; exact (Angular.exists_model ha ha1).elim Angular.Model.profile
  obtain ⟨C, σ, R, lam, Lam, A, hC, hσ, hR, hlam, hord, hm, hb, heq⟩ :=
    exists_geometricProfile_elliptic_solver d (by omega) α ha ha1
  have hR' : 0 < R := by linarith
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  refine ⟨⟨lam,Lam,A,geometricProfile α C σ R,hlam,hord,hm,hb,
    geometricProfile_smooth_off_origin _ _ _ _ hσ hR', geometricProfile_pos _ _ _ _ hC.le hσ hR',
    geometricProfile_homogeneous _ _ _ _, ?_⟩⟩
  have hx : ∀ᵐ q ∂(volume : Measure (XV d)), q.1 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0 : PDE.Vec d))
  filter_upwards [hx] with q hx
  have hq : q ≠ 0 := fun e => hx (congrArg Prod.fst e)
  exact sub_nonneg.mpr (heq q hq).le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
