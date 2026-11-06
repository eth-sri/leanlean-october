module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Oscillation and Hölder estimates under corrected uniform limits

These are sequence lemmas for the Borel passage. They do not assert existence of
correctors or the source-facing local regularity theorem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter
open scoped Topology

/- A uniform error increases oscillation by at most twice that error. -/
theorem corrector_oscillation_le {d : ℕ} {u w : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty)
    (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E))
    {ε } (he : ∀ P ∈ E, |w P - u P| ≤ ε) :
    Holder.oscillationOn w E ≤ Holder.oscillationOn u E + 2 * ε := by
  have hhi : ∀ P ∈ E, w P ≤ sSup (u '' E) + ε := by
    intro P hP
    have hp := (abs_le.mp (he P hP)).2
    have hs := le_csSup hab (mem_image_of_mem u hP)
    linarith
  have hlo : ∀ P ∈ E, sInf (u '' E) - ε ≤ w P := by
    intro P hP
    have hp := (abs_le.mp (he P hP)).1
    have hs := csInf_le hbb (mem_image_of_mem u hP)
    linarith
  have ho := Holder.oscillationOn_le hne hlo hhi
  dsimp only [Holder.oscillationOn] at ho ⊢
  linarith

/- Oscillation is continuous under uniform convergence on a nonempty bounded range. -/
theorem corrector_holder_limit {d : ℕ} {E : Set (KineticPoint d)}
    {u : KineticPoint d → ℝ} {u_j : ℕ → KineticPoint d → ℝ}
    (hu : TendstoUniformlyOn u_j u atTop E)
    {M_j : ℕ → ℝ} {M C α R : ℝ} (hM : Tendsto M_j atTop (𝓝 M))
    (P₀ : KineticPoint d)
    (hb : ∀ j, ∀ P ∈ E, ∀ Q ∈ E,
      |u_j j P - u_j j Q| ≤ C * M_j j * (kineticIncrement P₀ P Q / R) ^ α) :
    ∀ P ∈ E, ∀ Q ∈ E,
      |u P - u Q| ≤ C * M * (kineticIncrement P₀ P Q / R) ^ α := by
  intro P hP Q hQ
  have hl := ((hu.tendsto_at hP).sub (hu.tendsto_at hQ)).abs
  exact le_of_tendsto_of_tendsto hl ((hM.const_mul C).mul_const ((kineticIncrement P₀ P Q / R) ^ α)) (Eventually.of_forall fun j => hb j P hP Q hQ)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
