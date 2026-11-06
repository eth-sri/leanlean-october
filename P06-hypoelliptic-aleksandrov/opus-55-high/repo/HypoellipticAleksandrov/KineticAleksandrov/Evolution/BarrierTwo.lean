module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierChain
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound

/-!
# (A.1): the lateral and terminal barriers

For a viscous classical terminal solution `u_ε` on the moving ball `B_{r₀}` with smooth
compactly supported terminal datum `F`:

* `|u_ε| ≤ ‖F‖ min {1, w(d)/w(d_*)}`, where `d = r₀ - |y - γ(σ) - c|` is the distance to the
  lateral boundary;
* `|u_ε - F| ≤ (τ - σ) M_F` for `τ - σ ≤ d_*/(1 + L_γ)`.

The proof compares `u_ε` with the constant `‖F‖`, the collar supersolution
`‖F‖ w(d)/w(d_*)` (on each smooth piece of `γ`, `collar_chain`), and the terminal barriers
`F ± (τ - σ) M_F`.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

variable {κ : ℝ} {n : ℕ}

/-- In the collar, the terminal datum vanishes (the support of `F` is at distance at least
`2 d_*` from the terminal boundary). -/
theorem terminalDatum_eq_zero_of_collar  {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * dstar ≤ r₀ - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    {p : KineticPoint n} (hpt : p.time = τ) (hS : (r₀ - dstar) ^ 2 ≤ centreSq c γ p) :
    F (p.position, p.velocity) = 0 := by
  by_contra hne
  have hmem : (p.position, p.velocity) ∈ tsupport F :=
    subset_tsupport _ (Function.mem_support.mpr hne)
  have h1 := hsupp _ hmem
  have h2 : r₀ - dstar ≤ PDE.vecEuclideanNorm (p.position - (γ τ + c)) := by
    have h3 : (r₀ - dstar) ^ 2 ≤ PDE.vecNormSq (p.position - (γ τ + c)) := by
      aesop
    calc r₀ - dstar = Real.sqrt _ := (Real.sqrt_sq (by linarith)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h3
  linarith

/-- The profile `w` is strictly increasing. -/
theorem barrierW_strictMono  (hκ : 0 < κ) {s t : ℝ} (h : s < t) :
    barrierW κ s < barrierW κ t := by
  have : Real.exp (-κ * t) < Real.exp (-κ * s) := Real.exp_lt_exp.mpr (by nlinarith)
  exact div_lt_div_of_pos_right (by linarith) hκ

/-- Order reflection for the profile `w`. -/
theorem le_of_barrierW_le  (hκ : 0 < κ) {s t : ℝ} (h : barrierW κ s ≤ barrierW κ t) :
    s ≤ t := by
  by_contra hst
  exact absurd (barrierW_strictMono hκ (not_le.mp hst)) (not_lt.mpr h)

/-- The `σ`-independent extension `F(y, z)` of a smooth terminal datum is slice regular. -/
theorem isSliceRegularAt_terminalDatum  {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (p : KineticPoint n) :
    IsSliceRegularAt (fun q : KineticPoint n => F (q.position, q.velocity)) p := by
  have h2 : ContDiff ℝ 2 _ :=
    hF.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨?_, ?_, ?_⟩
  · simp
  · fun_prop
  fun_prop

end HypoellipticAleksandrov.KineticAleksandrov
