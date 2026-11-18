module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceLimit
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution Occupation
open scoped Topology
variable {d : ℕ}


/-- Passing the kinetic cutoff identity to the limit retains the terminal source term. -/
theorem kinetic_slice_weak_identity {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (EvolutionVec d)} (hD : IsOpen D) {V u : EvolutionVec d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, transportedOperator B b V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u)
    (C : ℝ) (hC0 : 0 ≤ C) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D)
    (m₀ : EvolutionAmbientState d → ℝ)
    (hlim : ∀ w, Tendsto (fun t => u (packQ d (t, w)) * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (m₀ w))) :
    (∫ q : ℝ × EvolutionAmbientState d,
      {q : ℝ × EvolutionAmbientState d | q.1 < r}.indicator
        (fun q => u (packQ d q) * transportedAdjoint B b ψ (packQ d q)) q) +
      ∫ w, m₀ w = 0  := by
  have kinetic_slice_cutoff_identity {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, timeCoord d x < r → x ∈ D) (h : ℝ) (hh : 0 < h) :
      (∫ x, u x * (layerStep ((r - timeCoord d x) / h) * transportedAdjoint B b ψ x)) +
      ∫ x, u x * (h⁻¹ * layerKernel ((r - timeCoord d x) / h) * ψ x) = 0 := by
    set Ladj := transportedAdjoint B b with hLadj
    have hU := hD
    have hχ := contDiff_sliceCutoff r h
    let φ : EvolutionVec d → ℝ := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x
    have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp (Evolution.timeCoord d).contDiff).mul hψ
    have hφc : HasCompactSupport φ := hc.mul_left
    have hφsub : tsupport φ ⊆ D := by
      intro x hx
      have h1 := tsupport_mul_subset_right hx
      have h2 : tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} := by
        apply closure_minimal
        · intro y hy
          exact (lt_of_sliceCutoff_ne_zero hh (left_ne_zero_of_mul hy)).le
        · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const
      exact hψD x h1 (by have := h2 hx; simp only [mem_ofPred_eq] at this; linarith)
    have key := integral_transportedAdjoint_contDiffOn hD hB hBs hb hV φ hφs hφc hφsub
    have hR : (∫ x in D, transportedOperator B b V x * φ x) = 0 := by
      rw [setIntegral_congr_fun hU.measurableSet (g := fun _ => 0)]
      · simp
      · intro x hx
        simp [hVeq _ hx]
    rw [hR] at key
    have hL : (∫ x in D, V x * Ladj φ x) = ∫ x, u x * Ladj φ x := by
      rw [setIntegral_congr_fun hU.measurableSet]
      · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have : x ∉ tsupport φ := fun h' => hx (hφsub h')
        rw [hLadj, transportedAdjoint_eq_zero_of_notMem_tsupport φ this, mul_zero]
      · intro x hx
        simp only [huV _ hx]
    rw [hL] at key
    have hexp : ∀ x, Ladj φ x = sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x +
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x := by
      intro x
      simp only [hLadj, φ]
      rw [transportedAdjoint_cutoff_mul hB hχ hψ x, deriv_sliceCutoff]
      ring
    simp_rw [hexp, mul_add] at key
    have hLc := (contDiff_transportedAdjoint hB hb hψ).continuous
    have hLcs : HasCompactSupport (Ladj ψ) := hasCompactSupport_transportedAdjoint hc
    have hmeasu := hum
    have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u x‖ ≤ C :=
      Eventually.of_forall fun x => by simpa using hub x
    have i1 : Integrable (fun x => u x * (sliceCutoff r h (Evolution.timeCoord d x) *
        Ladj ψ x)) := by
      have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
        ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul hLc
          ).integrable_of_hasCompactSupport hLcs.mul_left
      exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
    have i2 : Integrable (fun x => u x * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h)
        * ψ x)) := by
      have hk : Continuous (fun x =>
          h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
        (continuous_const.mul (continuous_layerKernel.comp
          ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
      have : Integrable (fun x =>
          h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
        hk.integrable_of_hasCompactSupport hc.mul_left
      exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
    exact (integral_add i1 i2).symm.trans key
  refine layer_slice_identity (volume : Measure (EvolutionAmbientState d)) r
    (fun q => u (packQ d q)) (fun q => ψ (packQ d q))
    (fun q => transportedAdjoint B b ψ (packQ d q))
    (hum.comp continuous_packQ.measurable) C hC0 (fun q => hub _)
    (hψ.continuous.comp continuous_packQ) (hasCompactSupport_comp_packQ hc)
    (((contDiff_transportedAdjoint hB hb hψ).continuous).comp continuous_packQ) (hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint (B := B) (b := b) hc)) ?_ m₀ hlim
  intro h hh
  have h1 := kinetic_slice_cutoff_identity
    hψ hc r hψD h hh
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h1
  simp only [timeCoord_packQ] at h1
  rw [← h1]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  · refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring

section
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The kinetic past cylinder is open for an open base domain and continuous motion. -/
theorem isOpen_duhamelCylinder (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (evolutionPastOpenCylinder Ω γ T) := by
  convert (isOpen_lt continuous_time (continuous_const)).inter (hΩ.preimage (continuous_position.sub (hγ.comp continuous_time))) using 1
  ext p
  simp only [evolutionPastOpenCylinder, mem_ofPred_eq, mem_inter_iff]
  change (_ ∧ _ ∈ PDE.translateSet (γ p.time) Ω) ↔ _
  rw [PDE.mem_translateSet_iff_sub_mem]
  rfl

/-- The source integrand tends to its terminal datum at every interior terminal state. -/
theorem duhamelSlice_leftLimit (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    (r : ℝ) (w : EvolutionAmbientState d)
    (hw : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastOpenCylinder Ω γ T) :
    Tendsto (fun t => duhamelIntegrand K g ⟨t, w.1, w.2⟩ r)
      (𝓝[<] r) (𝓝 (g ⟨r, w.1, w.2⟩)) := by
  obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal g hg hc hs T hU r
  have hmapc : Continuous (fun t => (KineticPoint.mk t w.1 w.2)) :=
    KineticPoint.continuous_mk continuous_id continuous_const continuous_const
  have hcl : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastClosedCylinder Ω γ r :=
    ⟨le_rfl, subset_closure hw.2⟩
  have hev : ∀ᶠ t in 𝓝[<] r,
      (KineticPoint.mk t w.1 w.2) ∈ evolutionPastClosedCylinder Ω γ r := by
    have hn := hmapc.continuousAt.eventually ((isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).mem_nhds hw)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht2
    exact ⟨le_of_lt ht2, subset_closure ht.2⟩
  have h1 := (hV.2.1 _ hcl).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨(hmapc.tendsto r).mono_left nhdsWithin_le_nhds, hev⟩)
  have ht := hV.2.2.2.2.1 ⟨r, w.1, w.2⟩ ⟨rfl, hcl.2⟩
  change V ⟨r, w.1, w.2⟩ = g ⟨r, w.1, w.2⟩ at ht
  rw [ht] at h1
  refine h1.congr' ?_
  filter_upwards [hev] with t ht
  exact (duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe _ ht).symm

/-- The slice times a compact test has the precise terminal limit, also outside the test support. -/
theorem duhamelSlice_terminalLimit (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (C : ℝ)
    (hub : ∀ p r, |duhamelIntegrand K g p r| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : Continuous ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T)
    (r : ℝ) (w : EvolutionAmbientState d) :
    Tendsto (fun t => duhamelIntegrand K g ⟨t, w.1, w.2⟩ r * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (g ⟨r, w.1, w.2⟩ * ψ (packQ d (r, w)))) := by
  have hψt : Tendsto (fun t => ψ (packQ d (t, w))) (𝓝[<] r)
      (𝓝 (ψ (packQ d (r, w)))) :=
    ((hψ.comp (continuous_packQ.comp (continuous_id.prodMk continuous_const))).tendsto r
      ).mono_left nhdsWithin_le_nhds
  by_cases h0 : ψ (packQ d (r, w)) = 0
  · rw [h0, mul_zero]
    have hb : Tendsto (fun t => C * |ψ (packQ d (t, w))|) (𝓝[<] r) (𝓝 0) := by
      simpa [h0] using hψt.abs.const_mul C
    refine squeeze_zero_norm (fun t => ?_) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hub _ _) (abs_nonneg _)
  · have hw := hψs (subset_closure h0)
    have hp : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastOpenCylinder Ω γ T := by
      simpa [evolutionHomeomorph_apply, packQ, timeCoord_packPoint, diffusedCoord_packPoint, transportedCoord_packPoint] using hw
    exact (duhamelSlice_leftLimit hΩa hΩ hγ B b S K hreal g hg hc hs T hU r w hp).mul hψt

end
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Packing the product coordinates agrees with the existing kinetic coordinate homeomorphism. -/
@[simp] theorem duhamel_homeomorph_packQ (q : ℝ × EvolutionAmbientState d) :
    evolutionHomeomorph d (packQ d q) = ⟨q.1, q.2.1, q.2.2⟩ := by
  simp only [evolutionHomeomorph_apply, packQ, timeCoord_packPoint,
    diffusedCoord_packPoint, transportedCoord_packPoint]



/-- The kinetic source potential satisfies the exact full adjoint distributional identity. -/
theorem duhamel_weak_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :
    (∫ x, duhamelPotential K T g (evolutionHomeomorph d x) * transportedAdjoint B b ψ x) =
      -∫ x, g (evolutionHomeomorph d x) * ψ x  := by
  have duhamelPotential_eq_integral_Ioi (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (p : KineticPoint d) :
      duhamelPotential K T g p = ∫ r in Ioi p.time, duhamelIntegrand K g p r := by
    have duhamelIntegrand_eq_zero_of_ge {r : ℝ} (hr : T ≤ r) :
        duhamelIntegrand K g p r = 0 := by
      unfold duhamelIntegrand
      split
      · unfold duhamelSourceIntegral
        have hz : ∀ w : EvolutionAmbientState d, g ⟨r, w.1, w.2⟩ = 0 := by
          intro w
          apply image_eq_zero_of_notMem_tsupport
          intro h
          exact absurd (hU h).1 (not_lt.2 hr)
        simp only [hz, integral_zero]
      · rfl
    unfold duhamelPotential
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self (fun r hr => ?_)
    exact duhamelIntegrand_eq_zero_of_ge (not_lt.1 fun h => hr.2 ⟨hr.1, h.le⟩)
  obtain ⟨a, b₀, -, hab⟩ := exists_time_window_of_hasCompactSupport g hgc
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  have hC0 := (hgn ⟨0, 0, 0⟩).trans (hgb _)
  have hmeas := measurable_duhamelIntegrand K hΩ hγ g hg.measurable
  have hub : ∀ p r, |duhamelIntegrand K g p r| ≤ C := fun p r => by
    rw [abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
    exact duhamelIntegrand_le K g hgn C hC0 hgb p r
  let Λ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q =>
    transportedAdjoint B b ψ (packQ d q)
  let Ψ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => ψ (packQ d q)
  have hΛc : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛs : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨc : Continuous Ψ := hψ.continuous.comp continuous_packQ
  have hΨs : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
  have per : ∀ r : ℝ, (∫ q : ℝ × (PDE.Vec d × PDE.Vec d),
      {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r * Λ q) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, g ⟨r, w.1, w.2⟩ * Ψ (r, w) = 0 := by
    intro r
    obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal
      g hg hgc hgs T hgU r
    let D := evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ r
    have hD := (isOpen_duhamelCylinder
      (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ r).preimage (evolutionHomeomorph d).continuous
    have hVsm :=
      hV.2.2.1.comp (evolutionProdCLE d).contDiff.contDiffOn (fun x hx => hx)
    have hVeq : ∀ x ∈ D, transportedOperator B b (V ∘ evolutionHomeomorph d) x = 0 := by
      intro x hx
      rw [transportedOperator_comp ((hVsm.contDiffAt (hD.mem_nhds hx)).of_le (by simp))]
      exact hV.2.2.2.1 _ hx
    have huV : ∀ x ∈ D, duhamelIntegrand K g (evolutionHomeomorph d x) r =
        (V ∘ evolutionHomeomorph d) x := fun x hx =>
      duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe _
        ⟨hx.1.le, subset_closure hx.2⟩
    have hm : Measurable (fun x => duhamelIntegrand K g (evolutionHomeomorph d x) r) :=
      hmeas.comp ((evolutionHomeomorph d).continuous.measurable.prodMk measurable_const)
    simpa using (kinetic_slice_weak_identity hB hBs hb hD hVsm hVeq huV hm C hC0 (fun x => hub _ r) hψ hc r (fun x hx hxr => ⟨hxr, (hψs hx).2⟩) (fun w => g ⟨r, w.1, w.2⟩ * ψ (packQ d (r, w))) (by simpa using (duhamelSlice_terminalLimit hΩa hΩ hγ B b S K hreal g hg hgc hgs T hgU C hub hψ.continuous hψs r)))
  -- Fubini in the source time `r` and the packed coordinates `q`.
  let F1 : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) → ℝ := fun z =>
    {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1}.indicator
      (fun z => duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1 * Λ z.2) z
  have hS : MeasurableSet {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} :=
    measurableSet_lt (measurable_snd.fst) measurable_fst
  have hGm : Measurable (fun z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) =>
      duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1 * Λ z.2) :=
    (hmeas.comp (((KineticPoint.measurable_equivProd_symm d).comp measurable_snd).prodMk
      measurable_fst)).mul (hΛc.measurable.comp measurable_snd)
  have hF1m : Measurable F1 := hGm.indicator hS
  have hbnd : Integrable (fun z =>
      (Icc a b₀).indicator (fun _ => C) z.1 * ‖Λ z.2‖)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by simp))) (hΛc.integrable_of_hasCompactSupport hΛs).norm
  have hF1int : Integrable F1
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))) := by
    refine hbnd.mono' hF1m.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    have hnn : 0 ≤ (Icc a b₀).indicator (fun _ => C) z.1 * ‖Λ z.2‖ :=
      mul_nonneg (indicator_nonneg (fun _ _ => hC0) _) (norm_nonneg _)
    by_cases hz : z.2.1 < z.1
    · have hF : F1 z = duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1 * Λ z.2 :=
        indicator_of_mem (show z ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
      rw [hF, norm_mul, Real.norm_eq_abs]
      by_cases hr : z.1 ∈ Icc a b₀
      · rw [indicator_of_mem hr]
        exact mul_le_mul_of_nonneg_right (hub _ _) (norm_nonneg _)
      · rw [duhamelIntegrand_eq_zero_of_time_not_mem K g a b₀ hab _ _ hr]
        simpa using hnn
    · have hF : F1 z = 0 :=
        indicator_of_notMem
          (show z ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
      rw [hF, norm_zero]
      exact hnn
  let F2 : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => g ⟨q.1, q.2.1, q.2.2⟩ * Ψ q
  have hF2c : Continuous F2 :=
    (hg.comp (KineticPoint.homeomorphProd d).symm.continuous).mul hΨc
  have hF2int : Integrable F2
      ((volume : Measure ℝ).prod (volume : Measure (PDE.Vec d × PDE.Vec d))) :=
    hF2c.integrable_of_hasCompactSupport hΨs.mul_left
  have hAint : Integrable (fun r => ∫ q, F1 (r, q)) :=
    hF1int.integral_prod_left
  have hMint : Integrable (fun r => ∫ w, F2 (r, w)) :=
    hF2int.integral_prod_left
  have hsum : (∫ r, ∫ q, F1 (r, q)) + ∫ r, ∫ w, F2 (r, w) = 0 := by
    rw [← integral_add hAint hMint]
    have : (fun r => (∫ q, F1 (r, q)) + ∫ w, F2 (r, w)) = fun _ => 0 := funext per
    rw [this, integral_zero]
  have hA : (∫ r, ∫ q, F1 (r, q)) =
      ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
        duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ := by
    rw [← integral_prod F1 hF1int, integral_prod_symm F1 hF1int]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have hfun : (fun r => F1 (r, q)) = (Ioi q.1).indicator
        (fun r => Λ q * duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r) := by
      funext r
      by_cases hr : q.1 < r
      · rw [indicator_of_mem (show r ∈ Ioi q.1 from hr)]
        exact (indicator_of_mem (show (r, q) ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
          z.2.1 < z.1} from hr) _).trans (mul_comm _ _)
      · rw [indicator_of_notMem (show r ∉ Ioi q.1 from hr)]
        exact indicator_of_notMem (show (r, q) ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
          z.2.1 < z.1} from hr) _
    have hq : ∫ r, F1 (r, q) = Λ q * ∫ r in Ioi q.1,
        duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r := by
      change ∫ r, (fun r => F1 (r, q)) r = _
      rw [hfun, integral_indicator measurableSet_Ioi, integral_const_mul]
    show (∫ r, F1 (r, q)) = Λ q * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
    rw [hq, duhamelPotential_eq_integral_Ioi hgU ⟨q.1, q.2.1, q.2.2⟩]
  have hM : (∫ r, ∫ w, F2 (r, w)) = ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), F2 q :=
    (integral_prod F2 hF2int).symm
  rw [hA, hM] at hsum
  have e1 : (∫ x, duhamelPotential K T g (evolutionHomeomorph d x) *
      transportedAdjoint B b ψ x) =
      ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
        duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ := by
    rw [integral_evolution_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [duhamel_homeomorph_packQ, Λ]
    ring
  have e2 : (∫ x, g (evolutionHomeomorph d x) * ψ x) = ∫ q, F2 q := by
    rw [integral_evolution_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [duhamel_homeomorph_packQ, F2, Ψ]
  rw [e1, e2]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

