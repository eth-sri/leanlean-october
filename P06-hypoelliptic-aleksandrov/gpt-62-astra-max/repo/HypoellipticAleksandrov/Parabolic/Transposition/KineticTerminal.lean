module
public import HypoellipticAleksandrov.Parabolic.Transposition.TerminalBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluing
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound
import Mathlib

/-! # Kinetic Dirichlet solvability by transposition

On each finite slab solve the sum-of-squares equation subject to the time and lateral
envelopes. The smooth solution extends continuously to its boundary values by squeezing;
an earlier-time collar puts the artificial lower face in the interior. Comparison on
overlapping slabs then gives a single bounded solution on the entire past cylinder.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity KineticAleksandrov KineticAleksandrov.Evolution Set Filter
open scoped ContDiff Topology MatrixOrder
variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {T : ℝ}
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {lam Lam m Lb : ℝ}

private theorem finite_solutions (hn : 0 < n) (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (hm : 0 < m) (hcoerc : HasUnitDirectionDriftCoercivity m b)
    {F : BoundedBorel (EvolutionAmbientState n)} (hF : IsSmoothCompactTerminalDatum Ω γ T F) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a, a < T → ∃ u, IsClassicalViscousFiniteSolution Ω γ B b 0 a T F u ∧
      ∀ p ∈ movingClosedSlab Ω γ a T, |u p| ≤ D := by
  have oΩ := isOpen_of_isAdmissibleEvolutionDomain hΩ
  obtain ⟨X,hspan,op⟩ := kinetic_fields ⊤ hlam hB hell hb hm hcoerc
  obtain ⟨H,hs,hterm,hlat⟩ := terminal_lift oΩ hγ.1 hF
  obtain ⟨C,f,M,hC,cm,hfT,hf⟩ := time_barrier op H hs T
  obtain ⟨A,hA⟩ := hs.exists_bound_of_continuous H.prop.continuous
  have D0 := add_nonneg ((norm_nonneg _).trans (hA 0)) hC
  refine ⟨A+C,D0,?_⟩
  intro a ha
  let U : Domain (n+n) := ⟨(split n) ⁻¹' evolutionFiniteInteriorRaw Ω γ (a-1) T, (isOpen_evolutionFiniteInteriorRaw oΩ hγ.1 ..).preimage (split n).continuous⟩
  have mem (z : Plane n) : z ∈ U ↔ a-1 < (world n z).time ∧ (world n z).time < T ∧ (world n z).position ∈ movingDomain Ω γ (world n z).time := Iff.rfl
  have active (z) (hz : z ∈ U) : world n z ∈ movingActiveSlab Ω γ (a-1) T := ⟨((mem z).mp hz).1.le,((mem z).mp hz).2⟩
  have time (z) (hz : z ∈ U) := hf z (active z hz).2.1.le
  obtain ⟨g,hg,hg0,hgz,happrox⟩ := lateral_barrier (b := b) hn hΩ hγ (show a-1 < T by linarith) hlam hC hell
  obtain ⟨J,eq,out,bound⟩ := harmonic_lift (U := U) H X (fun x _ => hspan x trivial) f
    (g ∘ world n) (hg.comp (world n).continuous) cm (fun z hz => (time z hz).1) (fun z hz => (time z hz).2.2.1)
    (fun z hz => (time z hz).2.2.2) (fun z hz => hg0 _ (active z hz)) (by
      intro ε hε; obtain ⟨G,hG,hop⟩ := happrox ε hε
      refine ⟨⟨G ∘ world n,hG⟩,fun z hz => ?_⟩
      obtain ⟨h1,h2,h3⟩ := hop (world n z) (active z hz)
      exact ⟨h1,(op G z (hG.contDiffAt.of_le (by simp))).le.trans (h2.trans (neg_le_neg (time z hz).2.1)),h3⟩)
  let u := J.val ∘ (world n).symm
  have comp : u ∘ world n = J.val := funext fun z => congrArg J.val ((world n).symm_apply_apply z)
  have ub (p) : |u p| ≤ A+C := by
    let z := (world n).symm p
    change |J.val z| ≤ _
    by_cases hz : z ∈ U
    · have he := (bound z hz).trans (min_le_left ..) |>.trans (time z hz).2.2.2.2.1
      have hh := abs_add_le (J.val z - H.val z) (H.val z)
      rw [sub_add_cancel] at hh; exact hh.trans ((add_le_add he (hA z)).trans_eq (add_comm ..))
    · exact (out hz) ▸ (hA z).trans (le_add_of_nonneg_right hC)
  have memp (p : KineticPoint n) : (world n).symm p ∈ U ↔ a-1 < p.time ∧ p.time < T ∧ p.position ∈ movingDomain Ω γ p.time := by rw [mem,Homeomorph.apply_symm_apply]
  refine ⟨u,⟨⟨A+C,D0,fun p _ => ub p⟩,?_,?_,?_,?_,?_⟩,fun p _ => ub p⟩
  · intro p hp
    let z := (world n).symm p
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp (g := J.val) (f := (world n).symm) ?_ (world n).symm.continuous.continuousAt
    change ContinuousAt J.val z
    by_cases hT : p.time = T
    · apply continuousAt_boundary H.prop.continuous f.prop.continuous _ out fun y hy => (bound y hy).trans (min_le_left ..)
      exact hfT z (by rw [show world n z = p from (world n).apply_symm_apply p]; exact hT)
    by_cases hpos : p.position ∈ movingDomain Ω γ p.time
    · exact (smooth_local J).continuousOn.continuousAt (U.isOpen.mem_nhds ((memp p).mpr ⟨by linarith [hp.1],lt_of_le_of_ne hp.2.1 hT,hpos⟩))
    · apply continuousAt_boundary H.prop.continuous (hg.comp (world n).continuous) _ out fun y hy => (bound y hy).trans (min_le_right ..)
      change g (world n ((world n).symm p)) = 0
      rw [Homeomorph.apply_symm_apply]; apply hgz; rw [(isOpen_movingDomain oΩ p.time).frontier_eq]; exact ⟨hp.2.2,hpos⟩
  · change ContDiffOn ℝ ∞ (J.val ∘ (split n).symm) _
    apply (smooth_local J).comp (split n).symm.contDiff.contDiffOn
    intro q hq; change split n ((split n).symm q) ∈ evolutionFiniteInteriorRaw Ω γ (a-1) T
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact ⟨by linarith [hq.1],hq.2⟩
  · intro p hp hpa
    have hz := (memp p).mpr ⟨by linarith,hp.2⟩
    have hJ := (smooth_local J).contDiffAt (U.isOpen.mem_nhds hz)
    have he := op u ((world n).symm p) (comp ▸ hJ.of_le (by simp))
    simpa only [viscousTransportedOperator,zero_mul,add_zero,comp,Homeomorph.apply_symm_apply] using he.symm.trans (comp ▸ eq _ hz)
  · intro p hp; apply (out (x := (world n).symm p) (fun hz => ((memp p).mp hz).2.1.ne hp.1)).trans
    have hh := hterm ((world n).symm p) (by rw [Homeomorph.apply_symm_apply]; exact hp.1)
    change H.val _ = F ((world n ((world n).symm p)).position,(world n ((world n).symm p)).velocity) at hh
    simpa only [Homeomorph.apply_symm_apply] using hh
  · intro p _ hfr; rw [(isOpen_movingDomain oΩ p.time).frontier_eq] at hfr
    apply (out (x := (world n).symm p) (fun hz => hfr.2 ((memp p).mp hz).2.2)).trans
    apply hlat; rw [Homeomorph.apply_symm_apply]; exact hfr.2

/-- Classical kinetic terminal solutions, with the sup-norm estimate and uniqueness. -/
theorem solve_kinetic_terminal (hn : 0 < n) (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hlam : 0 < lam) (hell : HasEverywhereLoewnerBounds lam Lam B) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (hm : 0 < m) (hcoerc : HasUnitDirectionDriftCoercivity m b) (hlip : HasEuclideanLipschitzDrift Lb b)
    {F : BoundedBorel (EvolutionAmbientState n)} (hF : IsSmoothCompactTerminalDatum Ω γ T F) :
    ∃ u, IsClassicalTerminalSolution Ω γ B b T F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) → ∀ p ∈ evolutionPastClosedCylinder Ω γ T, |u p| ≤ C) ∧
      (∀ v, IsClassicalTerminalSolution Ω γ B b T F v → EqOn v u (evolutionPastClosedCylinder Ω γ T)) := by
  obtain ⟨D,hD,hu⟩ := finite_solutions hn hΩ hγ hlam hell hB hb hm hcoerc hF
  have ho := isOpen_of_isAdmissibleEvolutionDomain hΩ
  obtain ⟨u,hu,_,uniq⟩ := exists_viscous_terminalSolution_of_finiteSlabs ho hγ.1 hlam hell hlip (le_refl 0) zero_le_one T F D hD hu
  have iff (v) : IsClassicalViscousTerminalSolution Ω γ B b 0 T F v ↔ IsClassicalTerminalSolution Ω γ B b T F v := by
    simp [IsClassicalViscousTerminalSolution,IsClassicalTerminalSolution,viscousTransportedOperator]
  exact ⟨u,(iff _).1 hu,fun _ _ h => classical_abs_le_const ho hγ.1 hlam hell hlip (le_refl 0) zero_le_one hu h,fun v hv => uniq v ((iff v).2 hv)⟩

end HypoellipticAleksandrov.Parabolic.Transposition
