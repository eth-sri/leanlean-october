module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsScaling
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public noncomputable section

section



namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set SectionTwo Evolution Occupation
variable {d : ℕ}

/-- Full kinetic integration by parts, with all jets discharged by interior smoothness. -/
theorem integral_transportedAdjoint_contDiffOn_two {U : Set (EvolutionVec d)} (hU : IsOpen U)
    {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (ψ : EvolutionVec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * transportedAdjoint B b ψ x) =
      ∫ x in U, transportedOperator B b u x * ψ x := by
  let D (v : EvolutionVec d) (f : EvolutionVec d → ℝ) (x : EvolutionVec d) :=
    fderiv ℝ f x v
  have hd : ∀ v, ContDiffOn ℝ 1 (D v u) U :=
    fun v => (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hdd : ∀ v w, ContDiffOn ℝ 0 (D w (D v u)) U :=
    fun v w => ((hd v).fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hline : ∀ v x, x ∈ U → HasLineDerivAt ℝ u (D v u x) x v := by
    intro v x hx
    exact ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      ).hasFDerivAt.hasLineDerivAt v
  have hline2 : ∀ v w x, x ∈ U →
      HasLineDerivAt ℝ (D v u) (D w (D v u) x) x w := by
    intro v w x hx
    exact (((hd v).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      ).hasFDerivAt.hasLineDerivAt w
  have key := integral_regularizedAdjoint_of_jets B b 0 hB hb u (D basisT u)
    (fun i => D (basisV i) u) (fun i => D (basisZ i) u)
    (fun i j => D (basisV j) (D (basisV i) u))
    (fun i => D (basisZ i) (D (basisZ i) u))
    hu.continuousOn (hd basisT).continuousOn
    (fun i => (hd (basisV i)).continuousOn) (fun i => (hd (basisZ i)).continuousOn)
    (fun i j => (hdd (basisV i) (basisV j)).continuousOn)
    (fun i => (hdd (basisZ i) (basisZ i)).continuousOn)
    (hline basisT) (fun i => hline (basisV i)) (fun i => hline (basisZ i))
    (fun i j => hline2 (basisV i) (basisV j))
    (fun i => hline2 (basisZ i) (basisZ i)) ψ hψ hc hs
  simp [regularizedAdjoint] at key
  refine key.trans (setIntegral_congr_fun hU.measurableSet fun x _ => ?_)
  congr 1
  dsimp only [D, transportedOperator]
  congr 1
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrFun (congrFun (hBs (timeCoord d x) (diffusedCoord d x)
    (transportedCoord d x)) i) j

/-- The literal scalar kinetic operator of a C² function is continuous. -/
theorem continuous_transportedOperator_c2 {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {f : EvolutionVec 1 → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f) := by
  have hd (v : EvolutionVec 1) : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    contDiffOn_univ.mp
      ((hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by norm_num)).clm_apply contDiffOn_const)
  have hdd (v w : EvolutionVec 1) :
      Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) :=
    (contDiffOn_univ.mp
      (((hd v).contDiffOn.fderiv_of_isOpen isOpen_univ (by norm_num)).clm_apply
        contDiffOn_const) : ContDiff ℝ 0 _).continuous
  unfold transportedOperator
  refine ((hd basisT).continuous.add ?_).add ?_
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((evolutionCoefficient_smooth A) i j).comp
      (evolutionProdCLE 1).contDiff).continuous.mul (hdd (basisV j) (basisV i))
  · apply continuous_finsetSum
    intro i _
    exact (((contDiff_pi.mp (identityDrift_smooth 1)) i).comp
      (diffusedCoord 1).contDiff).continuous.mul (hd (basisZ i)).continuous

/-- Outside a test's closed support all terms of its actual operator vanish. -/
theorem transportedOperator_eq_zero_of_notMem_tsupport {f : EvolutionVec 1 → ℝ}
    {x : EvolutionVec 1} (hx : x ∉ tsupport f) (B : FullKineticCoefficient 1)
    (b : PDE.Vec 1 → PDE.Vec 1) : transportedOperator B b f x = 0 := by
  have hn : x ∉ tsupport (fun y => fderiv ℝ f y (basisV 0)) :=
    fun h => hx (tsupport_fderiv_apply_subset ℝ (basisV 0) h)
  simp [transportedOperator, Fin.sum_univ_one, (fderiv_of_notMem_tsupport ℝ hx), (fderiv_of_notMem_tsupport ℝ hn), zero_apply]


end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}


/-- The zero extension is continuous at terminal points for every bounded signed source. -/
theorem continuousAt_duhamelPotential_terminal (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ p, |g p| ≤ M) (T : ℝ) (p : KineticPoint d) (hp : p.time = T) :
    ContinuousAt (duhamelPotential K T g) p  := by
  have tendsto_duhamelPotential_terminal :
      Tendsto (duhamelPotential K T g) (𝓝 p) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    have hbound : Continuous (fun q : KineticPoint d => |T - q.time| * M) :=
      (continuous_const.sub continuous_time).abs.mul continuous_const
    have hzero : Tendsto (fun q => |T - q.time| * M) (𝓝 p) (𝓝 0) := by
      simpa [hp] using (hbound.continuousAt (x := p)).tendsto
    apply squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) hzero
    rw [Real.norm_eq_abs]
    exact abs_duhamelPotential_le_abs_time K g M hM hgb q T
  rw [ContinuousAt, duhamelPotential_eq_zero_of_terminal_le K T g p hp.ge]
  exact tendsto_duhamelPotential_terminal

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory


end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

end

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory Filter
open scoped Topology ENNReal



/-- Compact C² spatial tests obey the actual full-space Green identity.
Size and operator bounds are derived, and no Green identity is assumed. -/
theorem fullspace_green_spatial_compact_c2
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (p : Point) (hp : p.time < T) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) (fun q => F (q.position, q.velocity)) q)) p =
      F (p.position, p.velocity) - ∫ x, F x ∂E.2.master
        (wholeSpaceQuery p.time T hp.le p.position p.velocity)  := by
  have fullspace_green_terminal_c2 (f : Point → ℝ) (hf : ContDiff ℝ 2 (f ∘ evolutionHomeomorph 1)) (Cf : ℝ) (M : ℝ) (hM : 0 ≤ M) (hfb : ∀ p, |f p| ≤ Cf) (hLf : ∀ p, |transportedForwardOperator (evolutionCoefficient A.a)
      (identityDrift 1) f p| ≤ M) (hF : UniformContinuous F) (hFt : ∀ p, p.time = T → f p = F (p.position, p.velocity)) :
      duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) f q)) p =
      f p - ∫ x, F x ∂E.2.master
        (wholeSpaceQuery p.time T hp.le p.position p.velocity) := by
    have fullspace_green_terminal_error_smooth_datum (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (δ : ℝ) (hFt : ∀ p, p.time = T → |f p - F (p.position, p.velocity)| ≤ δ) (p : Point) (hp : p.time < T) :
        |duhamelPotential E.2 T
        ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
          (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
            (identityDrift 1) f q)) p -
        (f p - ∫ x, F x ∂E.2.master
          (wholeSpaceQuery p.time T hp.le p.position p.velocity))| ≤ δ := by
      have fullspace_green_terminal_error (u : Point → ℝ) (g : Point → ℝ) (hu : ContDiffOn ℝ 2 (u ∘ evolutionHomeomorph 1)
          (evolutionHomeomorph 1 ⁻¹'
            evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T)) (huc : ContinuousOn u
          (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T)) (hg : Measurable g) (Cu : ℝ) (hub : ∀ p, p.time ≤ T → |u p| ≤ Cu) (hgb : ∀ p, |g p| ≤ M) (hgz : ∀ p, T ≤ p.time → g p = 0) (δ : ℝ) (hut : ∀ p, p.time = T → |u p| ≤ δ) (hop : ∀ p, p.time < T →
          transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) u p = -g p) (p₀ : Point) (hp₀ : p₀.time < T) :
          |duhamelPotential E.2 T g p₀ - u p₀| ≤ δ := by
        have c2_isWeakTransportedSolution {U : Set (EvolutionVec 1)} (hU : IsOpen U) {u : EvolutionVec 1 → ℝ} (hu : ContDiffOn ℝ 2 u U) :
            IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u
            (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) u) := by
          refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
          intro ψ hψ hc hs
          exact integral_transportedAdjoint_contDiffOn_two hU (evolutionCoefficient_smooth A)
            (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hu ψ hψ hc hs
        let D := evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T
        let U := evolutionHomeomorph 1 ⁻¹' D
        let W := duhamelPotential E.2 T g
        let v := fun p => W p - u p
        have hD : IsOpen D := isOpen_duhamelCylinder
          (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
          continuous_const T
        have hU := hD.preimage (evolutionHomeomorph 1).continuous
        have hw :=
          (isWeakTransportedSolution_comp_iff _ _ _ _ _).2 (duhamel_bounded_isKineticWeakTransportedSolution autonomousWholeDomain_admissible autonomousWholeDomain_measurable continuous_const (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) g hg M hM hgb T)
        have huw := c2_isWeakTransportedSolution hU hu
        have hue : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
            (u ∘ evolutionHomeomorph 1) ((fun p => -g p) ∘ evolutionHomeomorph 1) := by
          refine ⟨huw.1, ?_⟩
          intro ψ hψ hc hs
          rw [huw.2 ψ hψ hc hs]
          apply setIntegral_congr_fun hU.measurableSet
          intro x hx
          have he := transportedOperator_comp (B := evolutionCoefficient A.a)
            (b := identityDrift 1) ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) (x := x)
          dsimp only [Function.comp_apply]
          rw [he, hop _ hx.1]
        have hvw := weak_same_source_sub A hw hue
        have hWc :=
          continuousOn_duhamelPotential_bounded_signed hH autonomousWholeDomain_admissible
            autonomousWholeDomain_measurable continuous_const (evolutionCoefficient A.a)
            (identityDrift 1) E.1 E.2 hE (evolutionCoefficient_smooth A)
            (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1)
            lam Lam 1 hlam one_pos (evolutionCoefficient_bounds A) (identityDrift_bounds 1).2
            T g hg M hM hgb (by
              intro p hp
              apply hgz p
              by_contra hn
              apply hp
              exact ⟨lt_of_not_ge hn, by
                change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
                rw [movingDomain_wholeSpace]; trivial⟩)
        have hvc := hWc.sub (huc.mono (fun _ hp => ⟨hp.1.le, subset_closure hp.2⟩))
        have hvs : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ evolutionHomeomorph 1) U :=
          homogeneous_weak_contDiffOn hH hlam A hU hvw
            (hvc.comp (evolutionHomeomorph 1).continuous.continuousOn (fun _ hx => hx))
        have hvr (p : Point) (hp : p ∈ D) : IsSliceRegularAt v p :=
          reconstruction_slice_regular_of_contDiffOn hD hvs p hp
        have hvop (p : Point) (hp : p ∈ D) :
            transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) v p = 0 := by
          have hx : (evolutionHomeomorph 1).symm p ∈ U := by
            simpa [U, Homeomorph.apply_symm_apply] using hp
          have he := (duhamel_operator_eq_of_smooth_weak hU (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hvs continuousOn_const hvw) _ hx
          rw [transportedOperator_comp ((hvs.contDiffAt (hU.mem_nhds hx)).of_le (by simp))] at he
          simpa using he
        have hclosed : ContinuousOn v
            (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T) := by
          intro p hp
          by_cases ht : p.time = T
          · exact ((continuousAt_duhamelPotential_terminal E.2 g M hM hgb T p ht).continuousWithinAt.sub
              (huc p hp))
          · apply (hvc p ⟨lt_of_le_of_ne hp.1 ht, ?_⟩).continuousAt
              (hD.mem_nhds ⟨lt_of_le_of_ne hp.1 ht, ?_⟩) |>.continuousWithinAt
            all_goals
              change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
              rw [movingDomain_wholeSpace]; trivial
        have hvterm (p : Point) (ht : p.time = T) : |v p| ≤ δ := by
          dsimp [v, W]
          rw [duhamelPotential_eq_zero_of_terminal_le E.2 T g p ht.ge, zero_sub, abs_neg]
          exact hut p ht
        have hbound (p : Point) (hp : p ∈ movingClosedSlab autonomousWholeDomain
            (fun _ => 0) p₀.time T) : |v p| ≤ (T - p₀.time) * M + Cu := by
          have hh := abs_duhamelPotential_le_abs_time E.2 g M hM hgb p T
          dsimp [v, W]
          calc
            |duhamelPotential E.2 T g p - u p| ≤
                |duhamelPotential E.2 T g p| + |u p| := abs_sub _ _
            _ ≤ |T - p.time| * M + Cu := add_le_add hh (hub p hp.2.1)
            _ ≤ (T - p₀.time) * M + Cu := by
              rw [abs_of_nonneg (sub_nonneg.mpr hp.2.1)]
              exact add_le_add (mul_le_mul_of_nonneg_right (by linarith [hp.1]) hM) le_rfl
        have hcmp (f : Point → ℝ) (hfc : ContinuousOn f
            (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T))
            (hfr : ∀ p ∈ D, IsSliceRegularAt f p)
            (hfo : ∀ p ∈ D, transportedForwardOperator (evolutionCoefficient A.a)
              (identityDrift 1) f p = 0)
            (hft : ∀ p, p.time = T → f p ≤ δ)
            (hfb : ∀ p ∈ movingClosedSlab autonomousWholeDomain (fun _ => 0) p₀.time T,
              |f p| ≤ (T - p₀.time) * M + Cu) : f p₀ ≤ δ := by
          have hh := growth_comparison
            (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
            continuous_const hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
            (le_refl 0) zero_le_one (a := p₀.time) (T := T) (u := fun p => f p - δ)
            ⟨_, fun p hp => sub_le_sub_right ((le_abs_self _).trans (hfb p hp)) δ⟩
            ((hfc.sub continuousOn_const).mono (fun _ hp => ⟨hp.2.1, hp.2.2⟩))
            (fun p hp => (hfr p ⟨hp.2.1, hp.2.2⟩).sub (IsSliceRegularAt.const δ p))
            (fun p hp => by
              rw [viscousTransportedOperator_sub (hfr p ⟨hp.2.1, hp.2.2⟩)
                (IsSliceRegularAt.const δ p), viscousTransportedOperator_const,
                viscousTransportedOperator_zero, hfo p ⟨hp.2.1, hp.2.2⟩]
              norm_num)
            (fun p _ ht => sub_nonpos.mpr (hft p ht))
            (fun p _ hf => by
              change p.position ∈ frontier (movingDomain (wholeSpace 1) (fun _ => 0) p.time) at hf
              rw [movingDomain_wholeSpace, frontier_univ] at hf
              exact False.elim hf)
          apply sub_nonpos.mp
          exact hh p₀ ⟨le_rfl, hp₀.le, by
            change p₀.position ∈ closure (movingDomain (wholeSpace 1) (fun _ => 0) p₀.time)
            rw [movingDomain_wholeSpace, closure_univ]; trivial⟩
        have h2 := hcmp (fun p => -v p) hclosed.neg (fun p hp => (hvr p hp).neg)
          (fun p hp => by
            have hh := viscousTransportedOperator_const_mul
              (B := evolutionCoefficient A.a) (b := identityDrift 1) (ε := 0) (-1) (hvr p hp)
            rw [viscousTransportedOperator_zero, viscousTransportedOperator_zero,
              hvop p hp, mul_zero] at hh
            simpa using hh)
          (fun p ht => (neg_le_abs _).trans (hvterm p ht))
          (fun p hp => by rw [abs_neg]; exact hbound p hp)
        exact abs_le.mpr ⟨by linarith only [h2], (hcmp v hclosed hvr hvop (fun p ht => (le_abs_self _).trans (hvterm p ht)) hbound)⟩
      obtain ⟨u, hu, hr⟩ := fullspace_bounded_smooth_solution hH hlam hLam A E hE T F hF
      let D := evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T
      let g := D.indicator (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
        (identityDrift 1) f q)
      have hD : IsOpen D := isOpen_duhamelCylinder
        (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
        continuous_const T
      have hus : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
          (evolutionHomeomorph 1 ⁻¹' D) := by
        apply contDiffOn_comp_evolutionHomeomorph_iff.mpr
        rw [← evolutionPastInteriorRaw_eq_image]
        exact hu.2.2.1
      have hfc : Continuous f := by
        have he : f = (f ∘ evolutionHomeomorph 1) ∘ (evolutionHomeomorph 1).symm := by
          funext q; simp
        rw [he]
        exact hf.continuous.comp (evolutionHomeomorph 1).symm.continuous
      have hL : Continuous (fun q => transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) f q) := by
        have hc := (continuous_transportedOperator_c2 A hf).comp
          (evolutionHomeomorph 1).symm.continuous
        convert hc using 1
        funext q
        rw [Function.comp_apply,
          transportedOperator_comp hf.contDiffAt, Homeomorph.apply_symm_apply]
      have hgb (q : Point) : |g q| ≤ M := by
        by_cases hq : q ∈ D
        · simpa only [g, indicator_of_mem hq, abs_neg] using hLf q
        · simp [g, indicator_of_notMem hq]; exact hM
      obtain ⟨Cu, -, hCu⟩ := hu.1
      have hwhole (q : Point) :
          q.position ∈ closure (movingDomain autonomousWholeDomain (fun _ => 0) q.time) := by
        change q.position ∈ closure (movingDomain (wholeSpace 1) (fun _ => 0) q.time)
        rw [movingDomain_wholeSpace, closure_univ]; trivial
      have hreg (q : Point) (hq : q ∈ D) : IsSliceRegularAt f q :=
        IsSliceRegularAt.of_contDiffAt (by
          have hh := hf.contDiffAt.comp (q.time, q.position, q.velocity)
            (evolutionProdCLE 1).symm.contDiff.contDiffAt
          have he : (fun x => (f ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm x)) =
              rawLift f := by
            funext x
            simp [evolutionHomeomorph, rawLift, KineticPoint.homeomorphProd,
              KineticPoint.isometryEquivProd, KineticPoint.equivProd]
            rfl
          change ContDiffAt ℝ 2
            (fun x => (f ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm x))
            (q.time, q.position, q.velocity) at hh
          rwa [he] at hh)
      have hureg (q : Point) (hq : q ∈ D) : IsSliceRegularAt u q :=
        reconstruction_slice_regular_of_contDiffOn hD hus q hq
      have hgreen := fullspace_green_terminal_error (fun q => f q - u q) g
        (hf.contDiffOn.sub (hus.of_le (by simp))) (hfc.continuousOn.sub hu.2.1) (hL.neg.measurable.indicator hD.measurableSet) (Cf + Cu)
        (fun q hq => (abs_sub _ _).trans
          (add_le_add (hfb q) (hCu q ⟨hq, hwhole q⟩))) hgb
        (fun q hq => indicator_of_notMem (by intro hh; exact (not_lt_of_ge hq) hh.1) _)
        δ (fun q hq => by
          rw [hu.2.2.2.2.1 q ⟨hq, by simpa only [hq] using hwhole q⟩]
          exact hFt q hq)
        (fun q hq => by
          have hqd : q ∈ D := ⟨hq, by
            change q.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) q.time
            rw [movingDomain_wholeSpace]; trivial⟩
          rw [← viscousTransportedOperator_zero,
            viscousTransportedOperator_sub (hreg q hqd) (hureg q hqd),
            viscousTransportedOperator_zero, viscousTransportedOperator_zero,
            hu.2.2.2.1 q hqd, sub_zero]
          dsimp only [g]
          rw [indicator_of_mem hqd, neg_neg]) p hp
      have hrepr := hr (wholeSpaceQuery p.time T hp.le p.position p.velocity) rfl
      change u p = _ at hrepr
      rw [hrepr] at hgreen
      exact hgreen
    let ε := fun n : ℕ => 1 / ((n : ℝ) + 1)
    have hεp (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
    have hε1 (n : ℕ) : ε n ≤ 1 := by
      dsimp [ε]
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    choose G hGs hGa using fun n => hF.exists_contDiff_dist_le (hεp n)
    obtain ⟨C, hC, hCb⟩ := F.exists_bound
    have hGb (n : ℕ) (x : EvolutionAmbientState 1) : |G n x| ≤ C + 1 := by
      have hh := hGa n x
      rw [Real.dist_eq] at hh
      calc
        |G n x| ≤ |G n x - F x| + |F x| := by
          simpa using abs_add_le (G n x - F x) (F x)
        _ ≤ ε n + C := add_le_add hh.le (hCb x)
        _ ≤ C + 1 := by linarith only [hε1 n]
    let Fn (n : ℕ) : BoundedBorel (EvolutionAmbientState 1) :=
      ⟨G n, (hGs n).continuous.measurable,
        ⟨C + 1, by linarith only [hC], hGb n⟩⟩
    let μ := E.2.master (wholeSpaceQuery p.time T hp.le p.position p.velocity)
    have : IsFiniteMeasure μ := ⟨(E.2.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
    have hGl (x : EvolutionAmbientState 1) : Tendsto (fun n => G n x) atTop (𝓝 (F x)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hεlim
      rw [Real.norm_eq_abs]
      simpa only [Real.dist_eq] using (hGa n x).le
    have hIl : Tendsto (fun n => ∫ x, Fn n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => C + 1)
        (fun n => (Fn n).measurable.aestronglyMeasurable) (integrable_const _)
      · intro n
        exact Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]; exact hGb n x)
      · exact Eventually.of_forall hGl
    have herr (n : ℕ) : |(duhamelPotential E.2 T ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator (fun q => -transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f q)) p) - (f p - ∫ x, Fn n x ∂μ)| ≤ ε n := by
      apply fullspace_green_terminal_error_smooth_datum (Fn n) (hGs n) (ε n) ?_ p hp
      intro q hq
      rw [hFt q hq, abs_sub_comm]
      exact (hGa n _).le
    have hh :=
      le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub
        (tendsto_const_nhds.sub hIl)).abs) hεlim herr
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  let f := fun q : Point => F (q.position, q.velocity)
  let π := fun x => (diffusedCoord 1 x, transportedCoord 1 x)
  let fraw := fun x => F (π x)
  have hπ : Continuous π :=
    (diffusedCoord 1).continuous.prodMk (transportedCoord 1).continuous
  have hfraw := hF.comp
    ((diffusedCoord 1).contDiff.prodMk (transportedCoord 1).contDiff)
  have hfeq : f ∘ evolutionHomeomorph 1 = fraw := by
    funext x
    simp [f, fraw, π, evolutionHomeomorph, KineticPoint.homeomorphProd,
      KineticPoint.isometryEquivProd, KineticPoint.equivProd]
    rfl
  let H := fun x : EvolutionAmbientState 1 =>
    transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f ⟨0, x.1, x.2⟩
  let x0 := fun x => (evolutionProdCLE 1).symm (0, x)
  have hx0 : Continuous x0 :=
    (evolutionProdCLE 1).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hHeq : H = (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) fraw)
      ∘ x0 := by
    funext x
    have hh := transportedOperator_comp (B := evolutionCoefficient A.a)
      (b := identityDrift 1) (u := f) (x := x0 x) (by rw [hfeq]; exact hfraw.contDiffAt)
    rw [hfeq] at hh
    have hx : evolutionHomeomorph 1 (x0 x) = ⟨0, x.1, x.2⟩ := by
      simp [x0, evolutionHomeomorph, KineticPoint.homeomorphProd,
        KineticPoint.isometryEquivProd, KineticPoint.equivProd]
      rfl
    rw [hx] at hh
    exact hh.symm
  have hHc : Continuous H := by
    rw [hHeq]
    exact (continuous_transportedOperator_c2 A hfraw).comp hx0
  have hHk : HasCompactSupport H := by
    apply hc.of_isClosed_subset (isClosed_tsupport H)
    apply closure_minimal ?_ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    have hnx : x0 x ∉ tsupport fraw := by
      intro hh
      have hhit := tsupport_comp_subset_preimage F hπ hh
      apply hn
      change π (x0 x) ∈ tsupport F at hhit
      have hpx : π (x0 x) = x := by
        have hh := (evolutionProdCLE 1).apply_symm_apply (0, x)
        exact congrArg Prod.snd hh
      rwa [hpx] at hhit
    exact hx (by rw [hHeq]; exact (transportedOperator_eq_zero_of_notMem_tsupport hnx (evolutionCoefficient A.a) (identityDrift 1)))
  have hstation (q : Point) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f q =
        H (q.position, q.velocity) := by
    have ht (z : Point) : kineticTimeDerivative f z = 0 := by
      change deriv (fun _ : ℝ => F (z.position, z.velocity)) z.time = 0
      exact deriv_const z.time (F (z.position, z.velocity))
    dsimp only [H]
    rw [transportedForwardOperator_apply, transportedForwardOperator_apply, ht, ht]
    rfl
  obtain ⟨M, hMb⟩ := hHc.bounded_above_of_compact_support hHk
  obtain ⟨C, -, hCb⟩ := F.exists_bound
  exact fullspace_green_terminal_c2 f
    (by rw [hfeq]; exact hfraw) C (max M 0) (le_max_right _ _) (fun q => hCb _)
    (fun q => by
      rw [hstation]
      simpa using (hMb (q.position, q.velocity)).trans
        (le_max_left M 0)) (hc.uniformContinuous_of_continuous hF.continuous)
    (fun _ _ => rfl)


/-- The physical position-velocity order is the swapped native scalar order. -/
def physicalStateCLE : EvolutionAmbientState 1 ≃L[ℝ] Z :=
  (PDE.scalarToVecOneContinuousLinearEquiv.symm.prodCongr
    PDE.scalarToVecOneContinuousLinearEquiv.symm).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

/-- The physical scalar spatial generator, with the source sign and coordinate convention. -/
def physicalSpatialOperator (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (z : Z) : ℝ :=
  z.2 * deriv (fun X => f (X, z.2)) z.1 +
    a z.1 z.2 * deriv (deriv (fun v => f (z.1, v))) z.2

/-- The physical spatial generator agrees with the established physical operator. -/
theorem physicalSpatialOperator_eq_forward (a : ℝ → ℝ → ℝ) (f : Z → ℝ)
    (p : Point) :
    physicalSpatialOperator a f (p.position 0, p.velocity 0) =
      forwardScalarOperator a (fun q => f (q.position 0, q.velocity 0)) p := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar,
    kineticVelocityHessian_scalar]
  have ht : kineticTimeDerivative (fun q : Point => f (q.position 0, q.velocity 0)) p = 0 := by
    change deriv (fun _ : ℝ => f (p.position 0, p.velocity 0)) p.time = 0
    exact deriv_const _ _
  rw [ht]
  dsimp only [physicalSpatialOperator]
  ring

/-- Native compact spatial tests have exactly the physical generator after coordinate exchange. -/
theorem physicalSpatialOperator_eq_native (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (fun q => f (nativeToXV (q.position, q.velocity))) p =
      physicalSpatialOperator a f (p.velocity 0, p.position 0) := by
  exact (terminalPhysicalPoint_operator a
    (fun q => f (q.position 0, q.velocity 0)) p).trans
      (physicalSpatialOperator_eq_forward a f (terminalPhysicalPoint p)).symm

/-- A physical compact C² spatial test gives a native bounded Borel terminal datum. -/
def physicalCompactDatum (f : Z → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    BoundedBorel (EvolutionAmbientState 1) := by
  let C := (hf.bounded_above_of_compact_support hc).choose
  have hb := (hf.bounded_above_of_compact_support hc).choose_spec
  refine ⟨f ∘ nativeToXV, hf.measurable.comp nativeToXV_measurable,
    max C 0, le_max_right _ _, fun x => ?_⟩
  have hh : |f (nativeToXV x)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hb (nativeToXV x)
  exact hh.trans (le_max_left _ _)

/-- Compact physical C² tests retain native joint regularity. -/
theorem physicalCompactDatum_contDiff (f : Z → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ContDiff ℝ 2 (physicalCompactDatum f hf.continuous hc) := by
  have he : (physicalCompactDatum f hf.continuous hc : EvolutionAmbientState 1 → ℝ) =
      f ∘ physicalStateCLE := rfl
  rw [he]
  exact hf.comp physicalStateCLE.contDiff

/-- Compact physical support remains compact under the native coordinate equivalence. -/
theorem physicalCompactDatum_hasCompactSupport (f : Z → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) : HasCompactSupport (physicalCompactDatum f hf hc) := by
  have he : (physicalCompactDatum f hf hc : EvolutionAmbientState 1 → ℝ) =
      f ∘ physicalStateCLE.toHomeomorph := rfl
  rw [he]
  exact hc.comp_homeomorph physicalStateCLE.toHomeomorph







/-- An integrable stationary test has the actual occupation measure as its Duhamel integral. -/
theorem duhamelPotential_physical_occupation (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (g : Z → ℝ) (hg : Measurable g)
    (hgi : Integrable g (physicalOccupationMeasure E z T)) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => g (nativeToXV (q.position, q.velocity))))
      ⟨0, fun _ => z.2, fun _ => z.1⟩ =
      ∫ w, g w ∂physicalOccupationMeasure E z T  := by
  have duhamelPotential_physical :
      duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => g (nativeToXV (q.position, q.velocity))))
      ⟨0, fun _ => z.2, fun _ => z.1⟩ =
      ∫ t in Ioc 0 T, ∫ w, g w ∂kernelXV E (Real.toNNReal t) z := by
    have duhamelIntegrand_physical {s : ℝ} (hs : 0 < s) (hsT : s < T) :
        duhamelIntegrand E.2
        ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
          (fun q => g (nativeToXV (q.position, q.velocity))))
        ⟨0, fun _ => z.2, fun _ => z.1⟩ s =
        ∫ w, g w ∂kernelXV E (Real.toNNReal s) z := by
      rw [duhamelIntegrand, dite_eq_left ⟨hs.le, by simp [movingDomain, autonomousWholeDomain,
        PDE.translateSet]⟩, duhamelSourceIntegral]
      rw [kernelXV, integral_map nativeToXV_measurable.aemeasurable hg.aestronglyMeasurable]
      have hq : (⟨(0, (s, ((fun _ : Fin 1 => z.2), (fun _ : Fin 1 => z.1)))),
          hs.le, by simp [movingDomain, autonomousWholeDomain, PDE.translateSet], by trivial⟩ :
            EvolutionQuery autonomousWholeDomain (fun _ => 0)) =
          wholeQuery (Real.toNNReal s) z := by
        apply Subtype.ext
        simp only [wholeQuery, wholeSpaceQuery, Real.coe_toNNReal s hs.le]
      rw [← hq]
      apply integral_congr_ae
      filter_upwards with w
      rw [indicator_of_mem]
      exact ⟨hsT, by simp [movingDomain, autonomousWholeDomain, PDE.translateSet]⟩
    unfold duhamelPotential
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [volume.ae_ne T] with t ht hmem
    exact duhamelIntegrand_physical hmem.1 (lt_of_le_of_ne hmem.2 ht)
  rw [duhamelPotential_physical,
    ← physicalOccupationMeasure_integral E z T g hgi]


/-- A fixed unit inner radius and two-unit outer radius cutoff. -/
def barrierCutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The same scalar cutoff is used on the two different kinetic scales. -/
def barrierCutoff : ℝ → ℝ := barrierCutoffBump

/-- The cutoff takes values in the source unit interval. -/
theorem barrierCutoff_bounds (x : ℝ) : 0 ≤ barrierCutoff x ∧ barrierCutoff x ≤ 1 :=
  ⟨barrierCutoffBump.nonneg, barrierCutoffBump.le_one⟩

/-- The fixed cutoff is C∞. -/
theorem barrierCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) barrierCutoff :=
  barrierCutoffBump.contDiff

/-- The cutoff and both actual derivatives vanish outside its outer interval. -/
theorem barrierCutoff_zero_jets {x : ℝ} (hx : 2 < |x|) :
    barrierCutoff x = 0 ∧ deriv barrierCutoff x = 0 ∧
      deriv (deriv barrierCutoff) x = 0 := by
  have hn : x ∉ tsupport barrierCutoff := by
    rw [barrierCutoff, barrierCutoffBump.tsupport_eq]
    simpa [Metric.mem_closedBall, Real.dist_eq, not_le, barrierCutoffBump] using hx
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩

/-- The two scalar derivative bounds are fixed before any coefficient or spatial scale. -/
theorem barrierCutoff_derivative_bounds : ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
    (∀ x, |deriv barrierCutoff x| ≤ D1) ∧
    (∀ x, |deriv (deriv barrierCutoff) x| ≤ D2) := by
  obtain ⟨_, D1, D2, _, hD1, hD2, _, h1, h2⟩ := barrier_kernel_uniform_bounds
    barrierCutoff (barrierCutoff_contDiff.of_le (by simp)) barrierCutoffBump.hasCompactSupport
  exact ⟨D1, D2, hD1, hD2, h1, h2⟩

/-- The physical rectangular cutoff, centered at the barrier's position singularity. -/
def barrierRectCutoff (Y R : ℝ) (z : ℝ × ℝ) : ℝ :=
  barrierCutoff ((z.1 - Y) / R ^ 3) * barrierCutoff (z.2 / R)

/-- The rectangular cutoff remains between zero and one. -/
theorem barrierRectCutoff_bounds (Y R : ℝ) (z : ℝ × ℝ) :
    0 ≤ barrierRectCutoff Y R z ∧ barrierRectCutoff Y R z ≤ 1 := by
  exact ⟨mul_nonneg (barrierCutoff_bounds _).1 (barrierCutoff_bounds _).1,
    (mul_le_mul (barrierCutoff_bounds _).2 (barrierCutoff_bounds _).2
      (barrierCutoff_bounds _).1 zero_le_one).trans_eq (one_mul _)⟩

/-- The literal rectangular cutoff is continuous on the physical plane. -/
theorem barrierRectCutoff_continuous (Y R : ℝ) : Continuous (barrierRectCutoff Y R) :=
  (barrierCutoff_contDiff.continuous.comp
    ((continuous_fst.sub continuous_const).div_const _)).mul
      (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))








/-- Literal position, second velocity and cross velocity errors of the rectangular cutoff. -/
def barrierRectError (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (Y R : ℝ) (z : Z) : ℝ :=
  z.2 * (deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3) *
    barrierCutoff (z.2 / R) * f z +
  a z.1 z.2 * barrierCutoff ((z.1 - Y) / R ^ 3) *
    (deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2) * f z +
  2 * a z.1 z.2 * barrierCutoff ((z.1 - Y) / R ^ 3) *
    (deriv barrierCutoff (z.2 / R) / R) * deriv (fun v => f (z.1, v)) z.2

/-- Centering the position cutoff changes no derivative scale. -/
theorem barrier_position_cutoff_deriv (Y R x : ℝ) :
    deriv (fun X => barrierCutoff ((X - Y) / R ^ 3)) x =
      deriv barrierCutoff ((x - Y) / R ^ 3) / R ^ 3 := by
  have hx := ((hasDerivAt_id x).sub_const Y).div_const (R ^ 3)
  simpa [one_div, div_eq_mul_inv, Function.comp_def] using (((barrierCutoff_contDiff.differentiable (by simp) ((x - Y) / R ^ 3)).hasDerivAt).comp x hx).deriv



/-- The literal scalar cutoff equals one throughout its inner unit interval. -/
theorem barrierCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : barrierCutoff x = 1 := by
  apply barrierCutoffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, barrierCutoffBump] using hx

/-- At every physical point, the expanding kinetic cutoff is eventually exactly one. -/
theorem barrierRectCutoff_eventually_one (Y : ℝ) (z : Z) :
    ∀ᶠ n : ℕ in atTop, barrierRectCutoff Y ((n : ℝ) + 1) z = 1 := by
  have hn : ∀ᶠ n : ℕ in atTop, max |z.1 - Y| |z.2| ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hn] with n hn
  have hR : 1 ≤ (n : ℝ) + 1 := by
    have hn0 : 0 ≤ n := by positivity
    linarith only [hn0]
  have hR0 : 0 < (n : ℝ) + 1 := by positivity
  have hcube : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 3 := by
    nlinarith only [(mul_nonneg hR0.le (show 0 ≤ ((n : ℝ) + 1) ^ 2 - 1 by nlinarith [hR]))]
  have hx : |z.1 - Y| ≤ ((n : ℝ) + 1) ^ 3 :=
    (le_max_left _ _).trans (hn.trans ((by linarith : (n : ℝ) ≤ n + 1).trans hcube))
  have hv : |z.2| ≤ (n : ℝ) + 1 :=
    (le_max_right _ _).trans (hn.trans (by linarith))
  have hx' : |(z.1 - Y) / ((n : ℝ) + 1) ^ 3| ≤ 1 := by
    rw [abs_div, abs_of_pos (pow_pos hR0 3), div_le_iff₀ (pow_pos hR0 3), one_mul]
    exact hx
  have hv' : |z.2 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0, one_mul]
    exact hv
  simp [barrierRectCutoff, barrierCutoff_eq_one hx', barrierCutoff_eq_one hv']

/-- Actual integrable endpoint tests converge under the expanding kinetic cutoff. -/
theorem barrierRectCutoff_integral_tendsto (mu : Measure Z) (f : Z → ℝ)
    (hf : Measurable f) (hi : Integrable f mu) (Y : ℝ) :
    Tendsto (fun n : ℕ => ∫ z, barrierRectCutoff Y ((n : ℝ) + 1) z * f z ∂mu)
      atTop (𝓝 (∫ z, f z ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => |f z|)
  · intro n
    have hc : Continuous (barrierRectCutoff Y ((n : ℝ) + 1)) := by
      exact (barrierCutoff_contDiff.continuous.comp
        ((continuous_fst.sub continuous_const).div_const _)).mul
          (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))
    exact (hc.measurable.mul hf).aestronglyMeasurable
  · exact hi.abs
  · intro n
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (barrierRectCutoff_bounds _ _ _).1]
    simpa using mul_le_mul_of_nonneg_right
      (barrierRectCutoff_bounds Y ((n : ℝ) + 1) z).2 (abs_nonneg (f z))
  · filter_upwards with z
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [barrierRectCutoff_eventually_one Y z] with n hn
    simp [hn]

/-- Extended Fatou passes quantitative finite bounds without removing singular atoms. -/
theorem singular_fatou_of_real_bounds {W : Type*} [MeasurableSpace W]
    (mu : Measure W) (f : ℕ → W → ENNReal) (F : W → ENNReal)
    (hm : ∀ n, Measurable (f n))
    (hp : ∀ w, Tendsto (fun n => f n w) atTop (𝓝 (F w)))
    (b : ℕ → ℝ) (B : ℝ) (hb : Tendsto b atTop (𝓝 B))
    (hi : ∀ n, (∫⁻ w, f n w ∂mu) ≤ ENNReal.ofReal (b n)) :
    (∫⁻ w, F w ∂mu) ≤ ENNReal.ofReal B := by
  have he : (fun w => liminf (fun n => f n w) atTop) = F :=
    funext (fun w => (hp w).liminf_eq)
  rw [← he]
  apply (lintegral_liminf_le hm).trans
  apply (liminf_le_liminf (Eventually.of_forall hi)).trans_eq
  exact ((ENNReal.continuous_ofReal.tendsto B).comp hb).liminf_eq


/-- Derived compact Green bounds have a vanishing, explicit inverse-radius error.
The premises describe the actual test and its generator, and no Green identity is assumed. -/
theorem barrier_cutoff_green_bounds
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (alpha D Bv : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ D) (hBv : 0 ≤ Bv)
    (hm : ∀ z w : Z, |f z - f w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha))
    (hbv : ∀ z : Z, |deriv (fun v => f (z.1, v)) z.2| ≤ Bv)
    (c : ℝ) (hc : 0 < c) (w : Z → ℝ) (hw : Measurable w) (hwn : ∀ q, 0 ≤ w q)
    (hbound : ∀ q, c * w q ≤ physicalSpatialOperator A.a f q)
    (Y : ℝ) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫⁻ q, ENNReal.ofReal (c * (barrierRectCutoff Y R q * w q))
        ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, barrierRectCutoff Y R q * f q ∂kernelXV E T z) -
        barrierRectCutoff Y R z * f z + C * (T : ℝ) / R)          := by
  have physicalSpatialOperator_continuous_compact (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
      Continuous (physicalSpatialOperator A.a f) ∧
      HasCompactSupport (physicalSpatialOperator A.a f) := by
    have compact_spatial_generator (F : EvolutionAmbientState 1 → ℝ) (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) :
        Continuous (fun x : EvolutionAmbientState 1 =>
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
          (fun q => F (q.position, q.velocity)) ⟨0, x.1, x.2⟩) ∧
      HasCompactSupport (fun x : EvolutionAmbientState 1 =>
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
          (fun q => F (q.position, q.velocity)) ⟨0, x.1, x.2⟩) := by
      let f := fun q : Point => F (q.position, q.velocity)
      let π := fun x : EvolutionVec 1 => (diffusedCoord 1 x, transportedCoord 1 x)
      let fraw := fun x : EvolutionVec 1 => F (π x)
      have hπ : Continuous π :=
        (diffusedCoord 1).continuous.prodMk (transportedCoord 1).continuous
      have hfraw := hF.comp
        ((diffusedCoord 1).contDiff.prodMk (transportedCoord 1).contDiff)
      have hfeq : f ∘ evolutionHomeomorph 1 = fraw := by
        funext x
        simp [f, fraw, π, evolutionHomeomorph, KineticPoint.homeomorphProd,
          KineticPoint.isometryEquivProd, KineticPoint.equivProd]
        rfl
      let H := fun x : EvolutionAmbientState 1 =>
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f ⟨0, x.1, x.2⟩
      let x0 := fun x : EvolutionAmbientState 1 => (evolutionProdCLE 1).symm (0, x)
      have hx0 : Continuous x0 :=
        (evolutionProdCLE 1).symm.continuous.comp (continuous_const.prodMk continuous_id)
      have hHeq : H = (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) fraw)
          ∘ x0 := by
        funext x
        have hh := transportedOperator_comp (B := evolutionCoefficient A.a)
          (b := identityDrift 1) (u := f) (x := x0 x) (by rw [hfeq]; exact hfraw.contDiffAt)
        rw [hfeq] at hh
        have hx : evolutionHomeomorph 1 (x0 x) = ⟨0, x.1, x.2⟩ := by
          simp [x0, evolutionHomeomorph, KineticPoint.homeomorphProd,
            KineticPoint.isometryEquivProd, KineticPoint.equivProd]
          rfl
        rw [hx] at hh
        exact hh.symm
      have hHc : Continuous H := by
        rw [hHeq]
        exact (continuous_transportedOperator_c2 A hfraw).comp hx0
      have hHk : HasCompactSupport H := by
        apply hc.of_isClosed_subset (isClosed_tsupport H)
        apply closure_minimal ?_ (isClosed_tsupport F)
        intro x hx
        by_contra hn
        have hnx : x0 x ∉ tsupport fraw := by
          intro hh
          have hhit := tsupport_comp_subset_preimage F hπ hh
          apply hn
          change π (x0 x) ∈ tsupport F at hhit
          have hpx : π (x0 x) = x := by
            have hh := (evolutionProdCLE 1).apply_symm_apply (0, x)
            exact congrArg Prod.snd hh
          rwa [hpx] at hhit
        exact hx (by rw [hHeq]; exact (transportedOperator_eq_zero_of_notMem_tsupport hnx (evolutionCoefficient A.a) (identityDrift 1)))
      exact ⟨hHc, hHk⟩
    let F := physicalCompactDatum f hf.continuous hc
    have hh := compact_spatial_generator F
      (physicalCompactDatum_contDiff f hf hc) (physicalCompactDatum_hasCompactSupport f _ hc)
    have he : physicalSpatialOperator A.a f = (fun x : EvolutionAmbientState 1 => transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) (fun q => F (q.position, q.velocity)) ⟨0, x.1, x.2⟩) ∘ physicalStateCLE.symm := by
      funext q
      exact (physicalSpatialOperator_eq_native A.a f
        ⟨0, fun _ => q.2, fun _ => q.1⟩).symm
    rw [he]
    exact ⟨hh.1.comp physicalStateCLE.symm.continuous,
      hh.2.comp_homeomorph physicalStateCLE.symm.toHomeomorph⟩
  have barrier_rectangle_velocity_power {R : ℝ} {v : ℝ} (hR : 1 ≤ R) (hv : |v| ≤ 2 * R) :
      |v| ^ alpha ≤ 2 * R := by
    exact (Real.rpow_le_rpow (abs_nonneg v) hv ha).trans
      (Real.rpow_le_self_of_one_le (by linarith only [hR]) ha1)
  have barrier_rectangle_position_power {R : ℝ} {x : ℝ} (hR : 1 ≤ R) (hx : |x| ≤ 2 * R ^ 3) :
      |x| ^ (alpha / 3) ≤ 2 * R := by
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    have hbase : 1 ≤ 2 * R := by linarith only [hR]
    have hx3 : |x| ≤ (2 * R) ^ 3 := hx.trans (by nlinarith only [hR0, pow_nonneg hR0 3])
    have he : ((2 * R) ^ 3) ^ (alpha / 3) = (2 * R) ^ alpha := by
      rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ 2 * R)]
      congr 1
      ring
    exact ((Real.rpow_le_rpow (abs_nonneg x) hx3 (by linarith)).trans_eq he).trans
      (Real.rpow_le_self_of_one_le hbase ha1)
  have physicalSpatialOperator_occupation_integrable (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
      Integrable (physicalSpatialOperator A.a f) (physicalOccupationMeasure E z T) := by
    obtain ⟨hL, hcL⟩ := physicalSpatialOperator_continuous_compact f hf hc
    obtain ⟨C, hb⟩ := hL.bounded_above_of_compact_support hcL
    apply (integrable_const C).mono' hL.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall hb
  have barrierRectError_quantitative (a : ℝ → ℝ → ℝ) (D1 : ℝ) (D2 : ℝ) (R : ℝ) (hLam : 0 ≤ Lam) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hm : ∀ z w : Z, |f z - f w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)) (hbv : ∀ z : Z, |deriv (fun v => f (z.1, v)) z.2| ≤ Bv) (hb1 : ∀ x, |deriv barrierCutoff x| ≤ D1) (hb2 : ∀ x, |deriv (deriv barrierCutoff) x| ≤ D2) (hR : 1 ≤ R) (z : Z) (haz : 0 ≤ a z.1 z.2) (haL : a z.1 z.2 ≤ Lam) :
      |barrierRectError a f Y R z| ≤
      ((2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) + 2 * Lam * D1 * Bv) / R := by
    have barrierRectError_zero_outside (hz : 2 < |(z.1 - Y) / R ^ 3| ∨ 2 < |z.2 / R|) :
        barrierRectError a f Y R z = 0 := by
      rcases hz with hx | hv
      · obtain ⟨h0, h1, _⟩ := barrierCutoff_zero_jets hx
        simp [barrierRectError, h0, h1]
      · obtain ⟨h0, h1, h2⟩ := barrierCutoff_zero_jets hv
        simp [barrierRectError, h0, h1, h2]
    have barrier_rectangle_growth (hm : ∀ z w : ℝ × ℝ, |f z - f w| ≤
        D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)) (hx : |z.1 - Y| ≤ 2 * R ^ 3) (hv : |z.2| ≤ 2 * R) :
        |f z| ≤ (|f (Y, 0)| + 4 * D) * R := by
      have hh := hm z (Y, 0)
      simp at hh
      have hbound : |f z - f (Y, 0)| ≤ D * (4 * R) :=
        hh.trans (mul_le_mul_of_nonneg_left (by linarith only [(barrier_rectangle_position_power hR hx), (barrier_rectangle_velocity_power hR hv)]) hD)
      have hcenter : |f (Y, 0)| ≤ |f (Y, 0)| * R := by
        simpa using mul_le_mul_of_nonneg_left hR (abs_nonneg (f (Y, 0)))
      have htriangle : |f z| ≤ |f z - f (Y, 0)| + |f (Y, 0)| := by
        convert abs_add_le (f z - f (Y, 0)) (f (Y, 0)) using 1; ring
      nlinarith only [htriangle, hbound, hcenter]
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hC : 0 ≤ (2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) +
        2 * Lam * D1 * Bv := by positivity
    by_cases hx : |(z.1 - Y) / R ^ 3| ≤ 2
    swap
    · rw [barrierRectError_zero_outside (Or.inl (lt_of_not_ge hx)), abs_zero]
      exact div_nonneg hC hR0.le
    by_cases hv : |z.2 / R| ≤ 2
    swap
    · rw [barrierRectError_zero_outside (Or.inr (lt_of_not_ge hv)), abs_zero]
      exact div_nonneg hC hR0.le
    have hxp : |z.1 - Y| ≤ 2 * R ^ 3 := (div_le_iff₀ (pow_pos hR0 3)).mp
      (by simpa only [abs_div, abs_of_pos (pow_pos hR0 3)] using hx)
    have hvp : |z.2| ≤ 2 * R := (div_le_iff₀ hR0).mp
      (by simpa only [abs_div, abs_of_pos hR0] using hv)
    let B := |f (Y, 0)| + 4 * D
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hχ (x : ℝ) : |barrierCutoff x| ≤ 1 := by
      rw [abs_of_nonneg (barrierCutoff_bounds x).1]
      exact (barrierCutoff_bounds x).2
    have hdx : |deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3| ≤ D1 / R ^ 3 := by
      rw [abs_div, abs_of_pos (pow_pos hR0 3)]
      exact div_le_div_of_nonneg_right (hb1 _) (pow_nonneg hR0.le 3)
    have hdv : |deriv barrierCutoff (z.2 / R) / R| ≤ D1 / R := by
      rw [abs_div, abs_of_pos hR0]
      exact div_le_div_of_nonneg_right (hb1 _) hR0.le
    have hdvv : |deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2| ≤ D2 / R ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos hR0 2)]
      exact div_le_div_of_nonneg_right (hb2 _) (pow_nonneg hR0.le 2)
    have hh := cutoff_error_abs_le (a z.1 z.2) Lam z.2
      (barrierCutoff ((z.1 - Y) / R ^ 3)) (barrierCutoff (z.2 / R))
      (deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3)
      (deriv barrierCutoff (z.2 / R) / R) (deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2)
      (f z) (deriv (fun v => f (z.1, v)) z.2) (D1 / R ^ 3) (D1 / R) (D2 / R ^ 2)
      (B * R) Bv haz haL (hχ _) (hχ _) hdx hdv hdvv (barrier_rectangle_growth hm hxp hvp) (hbv z)
    apply hh.trans
    calc
      _ ≤ (2 * R) * (D1 / R ^ 3) * (B * R) + Lam * (D2 / R ^ 2) * (B * R) +
          2 * Lam * (D1 / R) * Bv := by gcongr
      _ = _ := by dsimp only [B]; field_simp
  have barrierRectError_eq_operator (a : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 < R) (z : Z) :
      physicalSpatialOperator a (fun w => barrierRectCutoff Y R w * f w) z =
      barrierRectCutoff Y R z * physicalSpatialOperator a f z + barrierRectError a f Y R z := by
    let chi := fun X => barrierCutoff ((X - Y) / R ^ 3)
    let psi := scaledScalarCutoff barrierCutoff R
    let Phi := fun p : Point => f (p.position 0, p.velocity 0)
    let p : Point := ⟨0, fun _ => z.1, fun _ => z.2⟩
    have hc : ContDiff ℝ 2 barrierCutoff := barrierCutoff_contDiff.of_le (by simp)
    have hchi : ContDiff ℝ 2 chi := hc.comp ((contDiff_id.sub contDiff_const).div_const _)
    have hpsi : ContDiff ℝ 2 psi := scaledScalarCutoff_contDiff _ hc _
    have ht : DifferentiableAt ℝ (fun t => Phi ⟨t, p.position, p.velocity⟩) p.time := by
      change DifferentiableAt ℝ (fun _ : ℝ => f z) 0
      exact differentiableAt_const _
    have hx : DifferentiableAt ℝ (fun X => Phi ⟨p.time, fun _ => X, p.velocity⟩)
        (p.position 0) := by
      have hs : ContDiff ℝ 2 (fun X : ℝ => f (X, z.2)) :=
        hf.comp (contDiff_id.prodMk contDiff_const)
      exact hs.differentiable (by norm_num) z.1
    have hv : ContDiff ℝ 2 (fun v => Phi ⟨p.time, p.position, fun _ => v⟩) :=
      hf.comp (contDiff_const.prodMk contDiff_id)
    have hh := spatialCutoffTest_operator a chi psi hchi hpsi Phi p ht hx hv
    have he : spatialCutoffTest chi psi Phi =
        fun q : Point => (fun w => barrierRectCutoff Y R w * f w)
          (q.position 0, q.velocity 0) := rfl
    rw [he, ← physicalSpatialOperator_eq_forward a
      (fun w => barrierRectCutoff Y R w * f w) p] at hh
    change physicalSpatialOperator a (fun w => barrierRectCutoff Y R w * f w) z = _ at hh
    rw [← physicalSpatialOperator_eq_forward a f p, kineticVelocityGradient_scalar] at hh
    dsimp only [chi] at hh
    rw [barrier_position_cutoff_deriv, scaledScalarCutoff_second_deriv _ hc hR.ne',
      scaledScalarCutoff_deriv _ hc] at hh
    simpa [psi, Phi, p, barrierRectCutoff, barrierRectError, scaledScalarCutoff, add_assoc] using hh
  have fullspace_physical_green_compact_c2 (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
      (∫ w, physicalSpatialOperator A.a f w ∂physicalOccupationMeasure E z T) =
      (∫ w, f w ∂kernelXV E T z) - f z := open Parabolic SectionTwo Evolution in by
    let F := physicalCompactDatum f hf.continuous hc
    have hh := fullspace_green_spatial_compact_c2 hH hlam hLam A E hE T F
      (physicalCompactDatum_contDiff f hf hc) (physicalCompactDatum_hasCompactSupport f _ hc)
      ⟨0, fun _ => z.2, fun _ => z.1⟩ hT
    have hL := physicalSpatialOperator_continuous_compact f hf hc
    have heSource :
        ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
          (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
            (identityDrift 1) (fun q => F (q.position, q.velocity)) q)) =
        ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
          (fun q => -physicalSpatialOperator A.a f (nativeToXV (q.position, q.velocity)))) := by
      congr 1
      funext q
      exact congrArg Neg.neg (physicalSpatialOperator_eq_native A.a f q)
    rw [heSource, duhamelPotential_physical_occupation E z T
      (fun w => -physicalSpatialOperator A.a f w) hL.1.measurable.neg (physicalSpatialOperator_occupation_integrable f hf hc).neg,
      integral_neg] at hh
    have heTerminal := integral_map nativeToXV_measurable.aemeasurable
      (hf.continuous.measurable.aestronglyMeasurable (μ := kernelXV E T z))
    change (∫ w, f w ∂kernelXV E T z) =
      ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery T z) at heTerminal
    change -(∫ w, physicalSpatialOperator A.a f w ∂physicalOccupationMeasure E z T) =
      f z - ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery T z) at hh
    rw [← heTerminal] at hh
    linarith only [hh]
  have barrierRectCutoff_contDiff (R : ℝ) :
      ContDiff ℝ 2 (fun z => barrierRectCutoff Y R z * f z) := by
    have hc : ContDiff ℝ 2 barrierCutoff := barrierCutoff_contDiff.of_le (by simp)
    exact ((hc.comp ((contDiff_fst.sub contDiff_const).div_const (R ^ 3))).mul
      (hc.comp (contDiff_snd.div_const R))).mul hf
  have barrierRectCutoff_hasCompactSupport (R : ℝ) (hR : 0 < R) :
      HasCompactSupport (fun z => barrierRectCutoff Y R z * f z) := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_Icc (a := Y - 2 * R ^ 3) (b := Y + 2 * R ^ 3)).prod
        (isCompact_Icc (a := -(2 * R)) (b := 2 * R)))
    intro z hz
    by_contra hn
    have hlarge : 2 < |(z.1 - Y) / R ^ 3| ∨ 2 < |z.2 / R| := by
      by_contra hh
      push Not at hh
      apply hn
      have hx := (div_le_iff₀ (pow_pos hR 3)).mp
        (by simpa only [abs_div, abs_of_pos (pow_pos hR 3)] using hh.1)
      have hv := (div_le_iff₀ hR).mp
        (by simpa only [abs_div, abs_of_pos hR] using hh.2)
      have hxb := abs_le.mp hx
      exact ⟨⟨by linarith only [hxb.1], by linarith only [hxb.2]⟩, (abs_le.mp hv)⟩
    apply hz
    rcases hlarge with hx | hv
    · simp [barrierRectCutoff, (barrierCutoff_zero_jets hx).1]
    · simp [barrierRectCutoff, (barrierCutoff_zero_jets hv).1]
  obtain ⟨D1, D2, hD1, hD2, hb1, hb2⟩ := barrierCutoff_derivative_bounds
  let C := (2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) + 2 * Lam * D1 * Bv
  have hL : 0 ≤ Lam := hlam.le.trans hLam
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun R hR => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let F := fun q : Z => barrierRectCutoff Y R q * f q
  let G := fun q : Z => c * (barrierRectCutoff Y R q * w q)
  let mu := physicalOccupationMeasure E z T
  have hFc := barrierRectCutoff_contDiff R
  have hFs := barrierRectCutoff_hasCompactSupport R hR0
  have hFL := physicalSpatialOperator_continuous_compact F hFc hFs
  have hFi := physicalSpatialOperator_occupation_integrable F hFc hFs
  have hcut : Continuous (barrierRectCutoff Y R) := by
    exact (barrierCutoff_contDiff.continuous.comp
      ((continuous_fst.sub continuous_const).div_const _)).mul
        (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))
  have hGm : Measurable G := (hcut.measurable.mul hw).const_mul c
  have hGn (q : Z) : 0 ≤ G q :=
    mul_nonneg hc.le (mul_nonneg (barrierRectCutoff_bounds _ _ _).1 (hwn q))
  have hGb (q : Z) : G q ≤ physicalSpatialOperator A.a F q + C / R := by
    have hlift := mul_le_mul_of_nonneg_left (hbound q) (barrierRectCutoff_bounds Y R q).1
    have heG : G q = barrierRectCutoff Y R q * (c * w q) := by dsimp only [G]; ring
    rw [← heG] at hlift
    have he := (neg_le_abs (barrierRectError A.a f Y R q)).trans (barrierRectError_quantitative A.a D1 D2 R hL hD1 hD2 hm hbv hb1 hb2 hR q (hlam.le.trans (A.bounds _ _).1) (A.bounds _ _).2)
    change G q ≤ physicalSpatialOperator A.a F q + C / R
    linarith only [(barrierRectError_eq_operator A.a R hR0 q), hlift, he]
  obtain ⟨K, hbK⟩ := hFL.1.bounded_above_of_compact_support hFL.2
  have hGi : Integrable G mu := by
    apply (integrable_const (K + C / R)).mono' hGm.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (hGn q)]
    have hLb : physicalSpatialOperator A.a F q ≤ K :=
      (le_abs_self _).trans (by simpa using hbK q)
    exact (hGb q).trans (add_le_add hLb le_rfl)
  have hi := integral_mono hGi (hFi.add (integrable_const (C / R))) hGb
  change (∫ q, G q ∂physicalOccupationMeasure E z T) ≤
    ∫ q, physicalSpatialOperator A.a F q + C / R ∂physicalOccupationMeasure E z T at hi
  rw [integral_add hFi (integrable_const (C / R)), integral_const,
    smul_eq_mul, measureReal_def, physicalOccupationMeasure_mass_eq hlam A E hE,
    ENNReal.toReal_ofReal hT.le] at hi
  rw [fullspace_physical_green_compact_c2 F hFc hFs] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hGn)]
  apply ENNReal.ofReal_le_ofReal
  exact hi.trans_eq (by dsimp only [F]; ring)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

