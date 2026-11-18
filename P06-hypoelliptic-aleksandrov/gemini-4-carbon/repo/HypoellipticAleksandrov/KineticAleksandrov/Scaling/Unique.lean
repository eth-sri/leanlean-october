module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Cylinders
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Pushforward
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling
section

open MeasureTheory Set
open HypoellipticAleksandrov

namespace KineticAffineScaling

variable {d : ℕ} (Φ : KineticAffineScaling d)

/-! ### Transport of quantifiers and regularity -/

theorem forall_mem_iff {S S' : Set (KineticPoint d)} (hS : ∀ p, p ∈ S' ↔ Φ.point p ∈ S)
    {f : KineticPoint d → Prop} : (∀ p ∈ S', f (Φ.point p)) ↔ ∀ p ∈ S, f p := by
  constructor
  · intro h p hp
    have hmem := (hS _).2 (by rwa [Φ.point_pointInv])
    simpa only [Φ.point_pointInv] using h _ hmem
  · intro h p hp
    exact h _ ((hS p).1 hp)

theorem continuousOn_iff {S S' : Set (KineticPoint d)} (hS : ∀ p, p ∈ S' ↔ Φ.point p ∈ S)
    {u : KineticPoint d → ℝ} :
    ContinuousOn (fun p => u (Φ.point p)) S' ↔ ContinuousOn u S := by
  constructor
  · intro h
    have hmaps : Set.MapsTo Φ.pointInv S S' := fun p hp =>
      (hS _).2 (by rwa [Φ.point_pointInv])
    have := h.comp Φ.continuous_pointInv.continuousOn hmaps
    refine this.congr ?_
    intro p _
    simp [Φ.point_pointInv]
  · intro h
    exact h.comp Φ.continuous_point.continuousOn (fun p hp => (hS p).1 hp)

theorem contDiffOn_raw_iff {S S' : Set (ℝ × (PDE.Vec d × PDE.Vec d))}
    (hS : ∀ q, q ∈ S' ↔ Φ.raw q ∈ S) {g : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => g (Φ.raw q)) S' ↔ ContDiffOn ℝ (⊤ : ℕ∞) g S := by
  constructor
  · intro h
    have hmaps : Set.MapsTo Φ.rawInv S S' := fun q hq =>
      (hS _).2 (by rwa [Φ.raw_rawInv])
    have := h.comp Φ.contDiff_rawInv.contDiffOn hmaps
    refine this.congr ?_
    intro q _
    simp [Φ.raw_rawInv]
  · intro h
    exact h.comp Φ.contDiff_raw.contDiffOn (fun q hq => (hS q).1 hq)

variable {Ω Ω' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}

/-- **Classical solutions are transported by the change of variables.**  If the moving
domains correspond, `Ω` is open, `γ` is continuous, and the terminal data correspond
(`F' = F ∘ Φ_τ`), then `u ∘ Φ` is a classical terminal solution for the rescaled data
(`B̂`, `b̂`, `Ω'`, `γ'`, `τ`, `F'`) exactly when `u` is one for `(B, b, Ω, γ, σ₀ + a τ, F)`. -/
theorem isClassicalTerminalSolution_comp_point_iff
    (h : Φ.MapsDomain Ω γ Ω' γ') (hΩ : IsOpen Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (τ : ℝ)
    (F F' : BoundedBorel (EvolutionAmbientState d))
    (hF : ∀ x, F' x = F (Φ.ambientEquiv τ x)) (u : KineticPoint d → ℝ) :
    IsClassicalTerminalSolution Ω' γ' (Φ.coefficient B) (Φ.drift b) τ F'
        (fun p => u (Φ.point p)) ↔
      IsClassicalTerminalSolution Ω γ B b (Φ.time τ) F u := by
  -- the individual clause transports
  have c1 : (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ evolutionPastClosedCylinder Ω' γ' τ,
        |u (Φ.point p)| ≤ C) ↔
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ evolutionPastClosedCylinder Ω γ (Φ.time τ), |u p| ≤ C) := by
    refine exists_congr fun C => and_congr_right fun _ => ?_
    exact Φ.forall_mem_iff (f := fun q => |u q| ≤ C) (h.mem_closedCylinder_iff τ)
  have c2 : ContinuousOn (fun p => u (Φ.point p)) (evolutionPastClosedCylinder Ω' γ' τ) ↔
      ContinuousOn u (evolutionPastClosedCylinder Ω γ (Φ.time τ)) :=
    Φ.continuousOn_iff (h.mem_closedCylinder_iff τ)
  have c3 :=
    Φ.contDiffOn_raw_iff (g := rawLift u) (h.mem_interiorRaw_iff τ)
  have hnhds : ∀ p : KineticPoint d, p ∈ evolutionPastOpenCylinder Ω' γ' τ →
      evolutionPastInteriorRaw Ω γ (Φ.time τ) ∈
        nhds (rawPoint (Φ.point p)) := by
    intro p hp
    refine (isOpen_evolutionPastInteriorRaw hΩ hγ (Φ.time τ)).mem_nhds ?_
    have := (h.mem_openCylinder_iff τ p).1 hp
    exact this
  have c4 : ContDiffOn ℝ (⊤ : ℕ∞) (rawLift u) (evolutionPastInteriorRaw Ω γ (Φ.time τ)) →
      ((∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
        transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p = 0)
        ↔ ∀ p ∈ evolutionPastOpenCylinder Ω γ (Φ.time τ),
          transportedForwardOperator B b u p = 0) := by
    intro hsm
    have hop : ∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
        transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p =
          Φ.a * transportedForwardOperator B b u (Φ.point p) := by
      intro p hp
      refine transportedForwardOperator_comp_point Φ B b ?_
      exact (hsm.contDiffAt (hnhds p hp)).of_le (by norm_cast)
    have key : (∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
        transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p = 0)
        ↔ ∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
          transportedForwardOperator B b u (Φ.point p) = 0 := by
      refine forall_congr' fun p => forall_congr' fun hp => ?_
      rw [hop p hp]
      exact mul_eq_zero.trans (or_iff_right Φ.a_pos.ne')
    rw [key]
    exact Φ.forall_mem_iff (f := fun q => transportedForwardOperator B b u q = 0)
      (h.mem_openCylinder_iff τ)
  have c5 : (∀ p ∈ evolutionTerminalClosure Ω' γ' τ, u (Φ.point p) = F' (p.position, p.velocity))
      ↔ ∀ p ∈ evolutionTerminalClosure Ω γ (Φ.time τ), u p = F (p.position, p.velocity) := by
    have hFp : ∀ p ∈ evolutionTerminalClosure Ω' γ' τ,
        F' (p.position, p.velocity) = F ((Φ.point p).position, (Φ.point p).velocity) := by
      intro p hp
      rw [hF]
      simp only [ambientEquiv_apply, point_position, point_velocity, hp.1]
    rw [forall_congr' fun p => forall_congr' fun hp => by rw [hFp p hp]]
    exact Φ.forall_mem_iff
      (f := fun q => u q = F (q.position, q.velocity)) (h.mem_terminalClosure_iff τ)
  have c6 :=
    Φ.forall_mem_iff (f := fun q => u q = 0) (h.mem_lateralFrontier_iff τ)
  unfold IsClassicalTerminalSolution
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hsm := c3.1 h3
    exact ⟨c1.1 h1, c2.1 h2, hsm, (c4 hsm).1 h4, c5.1 h5, c6.1 h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨c1.2 h1, c2.2 h2, c3.2 h3, (c4 h3).2 h4, c5.2 h5, c6.2 h6⟩

end KineticAffineScaling

end
section

open MeasureTheory ProbabilityTheory Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo (boundedBorel_integrable)
open scoped ENNReal

/-- The terminal operator family obtained by integrating bounded Borel data against the
fibre kernels of `K`. -/
def fiberOperator {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) : TerminalOperatorFamily Ω γ :=
  fun σ τ hστ =>
    { toFun := fun f =>
        ⟨fun p => ∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p,
          ⟨(StronglyMeasurable.integral_kernel (κ := K.fiberKernel hΩ σ τ hστ)
              f.measurable.stronglyMeasurable).measurable, by
            obtain ⟨C, hC, hb⟩ := f.exists_bound
            refine ⟨C, hC, fun p => ?_⟩
            have : IsFiniteMeasure (K.fiberKernel hΩ σ τ hστ p) :=
              ⟨(K.fiberKernel_mass_le_one hΩ σ τ hστ p).trans_lt ENNReal.one_lt_top⟩
            have h1 := norm_integral_le_of_norm_le_const (μ := K.fiberKernel hΩ σ τ hστ p)
              (f := f) (C := C) (Filter.Eventually.of_forall fun x => by
                simpa only [Real.norm_eq_abs] using hb x)
            have h2 : (K.fiberKernel hΩ σ τ hστ p).real univ ≤ 1 := by
              rw [measureReal_def]
              simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
                (K.fiberKernel_mass_le_one hΩ σ τ hστ p)
            calc |∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p|
                = ‖∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p‖ := (Real.norm_eq_abs _).symm
              _ ≤ C * (K.fiberKernel hΩ σ τ hστ p).real univ := h1
              _ ≤ C * 1 := by gcongr
              _ = C := mul_one C⟩⟩
      map_add' := by
        intro f g
        apply BoundedBorel.ext
        intro p
        have : IsFiniteMeasure (K.fiberKernel hΩ σ τ hστ p) :=
          ⟨(K.fiberKernel_mass_le_one hΩ σ τ hστ p).trans_lt ENNReal.one_lt_top⟩
        exact integral_add (boundedBorel_integrable f _) (boundedBorel_integrable g _)
      map_smul' := by
        intro c f
        apply BoundedBorel.ext
        intro p
        exact integral_smul c f }

theorem fiberOperator_apply {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionState Ω γ τ)) (p : EvolutionState Ω γ σ) :
    fiberOperator K hΩ σ τ hστ f p = ∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p := rfl

namespace KineticAffineScaling

variable {d : ℕ} {Φ : KineticAffineScaling d} {Ω Ω' : Set (PDE.Vec d)}
  {γ γ' : ℝ → PDE.Vec d}

theorem contDiff_ambientSymm (Φ : KineticAffineScaling d) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionAmbientState d => (Φ.ambientEquiv τ).symm x) := by
  simp
  unfold positionInv transportInv
  fun_prop




/-- **Realization transport.**  If `(S, K)` realizes the terminal evolution for the data
`(Ω, γ, B, b)` (`Ω` open, `γ` continuous), then `(Ŝ, K̂)` realizes it for the rescaled data
`(Ω', γ', Φ.coefficient B, Φ.drift b)`. -/
theorem realizes_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ') (hΩo : IsOpen Ω)
    (hγ : Continuous γ) (hΩ' : MeasurableSet Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ hΩo.measurableSet B b S K) :
    SectionTwo.RealizesTerminalEvolution Ω' γ' hΩ' (Φ.coefficient B) (Φ.drift b)
      (fiberOperator (pushKernel h K) hΩ') (pushKernel h K)    := by
  have integral_fiberKernel_pushKernel (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω') (τ τ' : ℝ) (hττ' : τ ≤ τ') (p : EvolutionState Ω' γ' τ) (f : EvolutionState Ω' γ' τ' → ℝ) :
      ∫ q, f q ∂(pushKernel h K).fiberKernel hΩ' τ τ' hττ' p =
      ∫ q, f ((stateEquiv h τ').symm q)
        ∂K.fiberKernel hΩ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ') (stateEquiv h τ p) := by
    rw [fiberKernel_pushKernel h K hΩ hΩ' τ τ' hττ' p, integral_map_equiv]
  have fiberKernel_pushKernel_eq_conj (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω') (τ τ' : ℝ) (hττ' : τ ≤ τ') :
      (pushKernel h K).fiberKernel hΩ' τ τ' hττ' =
      kernelConj (stateEquiv h τ) (stateEquiv h τ')
        (K.fiberKernel hΩ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ')) := by
    ext p : 1
    rw [kernelConj_apply]
    exact fiberKernel_pushKernel h K hΩ hΩ' τ τ' hττ' p
  have exists_datum_of_hat (τ : ℝ) (F' : BoundedBorel (EvolutionAmbientState d)) (hF' : IsSmoothCompactTerminalDatum Ω' γ' τ F') :
      ∃ F : BoundedBorel (EvolutionAmbientState d),
      IsSmoothCompactTerminalDatum Ω γ (Φ.time τ) F ∧
        ∀ x, F' x = F (Φ.ambientEquiv τ x) := by
    refine ⟨F'.pullback (Φ.ambientEquiv τ).symm (Φ.ambientEquiv τ).symm.measurable, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact hF'.1.comp (Φ.contDiff_ambientSymm τ)
      · exact hF'.2.1.comp_homeomorph (Φ.ambientHomeo τ).symm
      · intro x hx
        have hx' := hF'.2.2 (tsupport_comp_subset_preimage (F' : EvolutionAmbientState d → ℝ) (Φ.ambientHomeo τ).symm.continuous hx)
        have := (h.stateSet_mem_iff τ _).1 hx'
        simpa [Φ.position_positionInv, Φ.transport_transportInv] using this
    · intro x
      simp only [BoundedBorel.pullback_apply, MeasurableEquiv.symm_apply_apply]
  refine ⟨?_, fun σ τ hστ p f => rfl, ?_, ?_⟩
  · intro τ F' hF'
    obtain ⟨F, hF, hFF'⟩ := exists_datum_of_hat τ F' hF'
    obtain ⟨u, hu, hup, huniq⟩ := hreal.1 (Φ.time τ) F hF
    refine ⟨fun p => u (Φ.point p), ?_, ?_, ?_⟩
    · exact (Φ.isClassicalTerminalSolution_comp_point_iff h hΩo hγ B b τ F F' hFF' u).2 hu
    · intro σ hστ p
      have hlhs : u (Φ.point ⟨σ, p.1.1, p.1.2⟩) =
          u ⟨Φ.time σ, (stateEquiv h σ p).1.1, (stateEquiv h σ p).1.2⟩ := rfl
      beta_reduce
      rw [hlhs, hup (Φ.time σ) (Φ.time_le_iff.2 hστ) (stateEquiv h σ p),
        hreal.2.1 (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.2 hστ) (stateEquiv h σ p),
        fiberOperator_apply, integral_fiberKernel_pushKernel hΩo.measurableSet hΩ' σ τ hστ p]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      change F q.1 = F' ((Φ.ambientEquiv τ).symm q.1)
      rw [hFF', MeasurableEquiv.apply_symm_apply]
    · intro v' hv'
      have hv : IsClassicalTerminalSolution Ω γ B b (Φ.time τ) F
          (fun p => v' (Φ.pointInv p)) := by
        rw [← Φ.isClassicalTerminalSolution_comp_point_iff h hΩo hγ B b τ F F' hFF'
          (fun p => v' (Φ.pointInv p))]
        have : (fun p => (fun p => v' (Φ.pointInv p)) (Φ.point p)) = v' := by
          funext p
          simp only [Φ.pointInv_point]
        rw [this]
        exact hv'
      intro p hp
      simpa only [Φ.pointInv_point] using (huniq _ hv ((h.mem_closedCylinder_iff τ p).1 hp))
  · intro σ
    rw [fiberKernel_pushKernel_eq_conj hΩo.measurableSet hΩ']
    rw [hreal.2.2.1 (Φ.time σ), kernelConj_id (stateEquiv h σ)]
  · intro σ r τ hσr hrτ
    rw [fiberKernel_pushKernel_eq_conj hΩo.measurableSet hΩ' σ τ (hσr.trans hrτ),
      fiberKernel_pushKernel_eq_conj hΩo.measurableSet hΩ' r τ hrτ,
      fiberKernel_pushKernel_eq_conj hΩo.measurableSet hΩ' σ r hσr,
      hreal.2.2.2 (Φ.time σ) (Φ.time r) (Φ.time τ) (Φ.time_le_iff.2 hσr)
        (Φ.time_le_iff.2 hrτ),
      kernelConj_comp (stateEquiv h σ) (stateEquiv h r) (stateEquiv h τ)]

end KineticAffineScaling

end

open MeasureTheory Set
open HypoellipticAleksandrov

namespace KineticAffineScaling

variable {d : ℕ} {Φ : KineticAffineScaling d} {Ω Ω' : Set (PDE.Vec d)}
  {γ γ' : ℝ → PDE.Vec d}

/-- **Kernel transport.**  If `(S, K)` realizes the terminal evolution for `(Ω, γ, B, b)`
and `(S', K')` realizes it for the rescaled data `(Ω', γ', Φ.coefficient B, Φ.drift b)`, then
`K'` is the pushforward of `K` and `S'` is integration against it. -/
theorem realizes_unique_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ')
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hΩ' : IsAdmissibleEvolutionDomain Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    {S' : TerminalOperatorFamily Ω' γ'} {K' : MovingFiberKernel Ω' γ'}
    (hreal' : SectionTwo.RealizesTerminalEvolution Ω' γ'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') (Φ.coefficient B) (Φ.drift b) S' K') :
    K' = pushKernel h K ∧
      S' = fiberOperator (pushKernel h K) (measurableSet_of_isAdmissibleEvolutionDomain hΩ') := by
  obtain ⟨hS, hK⟩ := SectionTwo.terminalEvolution_unique Ω' γ' hΩ' (Φ.coefficient B)
    (Φ.drift b) S' _ K' _ hreal' (realizes_pushKernel h (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 (measurableSet_of_isAdmissibleEvolutionDomain hΩ') hreal)
  exact ⟨hK, hS⟩

/-- The master kernel of any realization of the rescaled problem, in the pushforward form
`K̂'.master q' = (K.master (Φ q')).map (Φ_{τ'})⁻¹`. -/
theorem realizes_master_eq_map (h : Φ.MapsDomain Ω γ Ω' γ')
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hΩ' : IsAdmissibleEvolutionDomain Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    {S' : TerminalOperatorFamily Ω' γ'} {K' : MovingFiberKernel Ω' γ'}
    (hreal' : SectionTwo.RealizesTerminalEvolution Ω' γ'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') (Φ.coefficient B) (Φ.drift b) S' K')
    (q : EvolutionQuery Ω' γ') :
    K'.master q = (K.master (queryMap h q)).map (Φ.ambientEquiv q.1.2.1).symm := by
  rw [(realizes_unique_pushKernel h hΩ hγ hΩ' hreal hreal').1]
  exact pushKernel_master_apply h K q

end KineticAffineScaling

/-! ### Case W -/

/-- The whole space with the stationary curve is mapped to itself by every scaling. -/
theorem KineticAffineScaling.mapsDomain_wholeSpace {d : ℕ} (Φ : KineticAffineScaling d) :
    Φ.MapsDomain (Set.univ : Set (PDE.Vec d)) (fun _ => 0) Set.univ (fun _ => 0) := by
  intro τ
  have h : ∀ σ : ℝ, movingDomain (Set.univ : Set (PDE.Vec d)) (fun _ => 0) σ =
      Set.univ := SectionTwo.movingDomain_wholeSpace d
  rw [h, h, preimage_univ]

end HypoellipticAleksandrov.KineticAleksandrov.Scaling

