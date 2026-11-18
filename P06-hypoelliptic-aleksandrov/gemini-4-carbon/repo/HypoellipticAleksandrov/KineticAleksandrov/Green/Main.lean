module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.Gluing
public import HypoellipticAleksandrov.KineticAleksandrov.Green.LogIntegration

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green
open MeasureTheory Set HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal


/-- The literal inclusion of the finite-horizon carrier into the infinite-horizon one. -/
def horizonInclusion (d : ℕ) (S : ℝ≥0∞) :
    ElapsedTime S × EvolutionAmbientState d → GreenCarrier d :=
  fun q => (elapsedInclusion le_top q.1, q.2)

lemma measurableEmbedding_elapsedInclusion {T S : ℝ≥0∞} (hTS : T ≤ S) :
    MeasurableEmbedding (elapsedInclusion hTS) := by
  have hT : MeasurableEmbedding (Subtype.val : ElapsedTime T → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime T)
  refine ⟨?_, measurable_elapsedInclusion hTS, ?_⟩
  · intro a b hab
    exact Subtype.ext (by simpa [elapsedInclusion] using congrArg Subtype.val hab)
  · intro B hB
    have : elapsedInclusion hTS '' B = (Subtype.val : ElapsedTime S → ℝ) ⁻¹'
        ((Subtype.val : ElapsedTime T → ℝ) '' B) := by
      ext τ
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, hσ, rfl⟩
      · rintro ⟨σ, hσ, h⟩
        exact ⟨σ, hσ, Subtype.ext h⟩
    rw [this]
    exact measurable_subtype_coe (hT.measurableSet_image.2 hB)


/-- Density transport along a measurable embedding. -/
lemma eq_withDensity_of_map_eq_emb {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {f : X → Z} (hf : MeasurableEmbedding f) {ν Γ' : Measure X} {G' : Z → ℝ≥0∞}
    (h : Γ'.map f = (ν.map f).withDensity G') :
    Γ' = ν.withDensity (fun x => G' (f x)) := by
  ext B hB
  have h1 : Γ' B = (Γ'.map f) (f '' B) := by
    rw [hf.map_apply, Set.preimage_image_eq _ hf.injective]
  rw [h1, h, withDensity_apply _ (hf.measurableSet_image.2 hB), withDensity_apply _ hB]
  exact ((MeasurePreserving.mk hf.measurable rfl).setLIntegral_comp_emb hf G' B).symm

/-- Lebesgue measure on the finite carrier pushes forward to the time-restricted one. -/
lemma map_horizonInclusion_lebesgue (d : ℕ) (S : ℝ≥0∞) :
    ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).map
        (horizonInclusion d S) =
      (greenLebesgue d).restrict {p | ENNReal.ofReal p.1.1 < S} := by
  have h1 := Measure.map_prod_map (elapsedVolume S) (volume : Measure (EvolutionAmbientState d))
    (measurable_elapsedInclusion (le_top : S ≤ ⊤)) measurable_id
  rw [Measure.map_id, elapsedInclusion_map] at h1
  have h2 := Measure.prod_restrict (μ := elapsedVolume ⊤)
    (ν := (volume : Measure (EvolutionAmbientState d))) {τ : ElapsedTime ⊤ | ENNReal.ofReal τ.1 < S}
    univ
  rw [Measure.restrict_univ, Set.prod_univ] at h2
  have h3 : (greenLebesgue d).restrict {p | ENNReal.ofReal p.1.1 < S} =
      ((elapsedVolume ⊤).restrict {τ : ElapsedTime ⊤ | ENNReal.ofReal τ.1 < S}).prod
        (volume : Measure (EvolutionAmbientState d)) := h2.symm
  rw [h3]
  exact h1.symm



/-- The exponent `δ_q = 1 - 2d(q-1)`. -/
def greenDelta (d : ℕ) (q : ℝ) : ℝ := 1 - 2 * (d : ℝ) * (q - 1)

/-- The constant `C_{d,λ,Λ,q}` of Theorem 2.4: `(C_q / (δ_q log 2))^{1/q}`, with `C_q` the
constant of Proposition 5.3. -/
def greenConstant (d : ℕ) (q : ℝ) (C : ℝ → ℝ≥0) : ℝ≥0 :=
  (((slabConstant d q C : ℝ≥0∞) * (ENNReal.ofReal (Real.log 2))⁻¹ *
    ENNReal.ofReal (1 / greenDelta d q)) ^ (1 / q)).toNNReal


/-- The final `ℝ≥0∞` arithmetic: `(c₁ · M^q · (log 2)⁻¹ · S^δ/δ)^{1/q} = C_g · M · S^{δ/q}`. -/
lemma green_arith (a : ℝ≥0) (M : ℝ≥0∞) {S δ q : ℝ} (hS : 0 < S) (hδ : 0 < δ) (hq : 1 < q) :
    ((a : ℝ≥0∞) * M ^ q * (ENNReal.ofReal (Real.log 2))⁻¹ * ENNReal.ofReal (S ^ δ / δ)) ^
        (1 / q) =
      ((a : ℝ≥0∞) * (ENNReal.ofReal (Real.log 2))⁻¹ * ENNReal.ofReal (1 / δ)) ^ (1 / q) * M *
        ENNReal.ofReal (S ^ (δ / q)) := by
  have hq0 : 0 < q := by linarith
  have h1q : 0 ≤ 1 / q := by positivity
  have hS1 : 0 ≤ S ^ δ := (Real.rpow_pos_of_pos hS _).le
  have e1 : ENNReal.ofReal (S ^ δ / δ) = ENNReal.ofReal (1 / δ) * ENNReal.ofReal (S ^ δ) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have e2 : ENNReal.ofReal (S ^ (δ / q)) = ENNReal.ofReal (S ^ δ) ^ (1 / q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hS1 h1q, ← Real.rpow_mul hS.le]
    congr 2
    ring
  have e3 : (M ^ q) ^ (1 / q) = M := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  calc ((a : ℝ≥0∞) * M ^ q * (ENNReal.ofReal (Real.log 2))⁻¹ * ENNReal.ofReal (S ^ δ / δ)) ^
        (1 / q)
      = (((a : ℝ≥0∞) * (ENNReal.ofReal (Real.log 2))⁻¹ * ENNReal.ofReal (1 / δ)) * M ^ q *
          ENNReal.ofReal (S ^ δ)) ^ (1 / q) := by
        rw [e1]; congr 1; ring
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1q, ENNReal.mul_rpow_of_nonneg _ _ h1q, e3, e2]

/-- **Conditional Theorem 2.4 (case W).**  Let `μ` be a finite measure of mass `M = μ univ` and
suppose the infinite-horizon Green measure `Γ_μ^∞` has the outputs `SlabFourierBounds` of
Lemma 5.1 on every slab `(T,2T)`, `T > 0`.  Then for every `S > 0` and
`1 < q < 1 + 1/(2d)` the finite-horizon Green measure `Γ_μ^S` has a Lebesgue density `G` on
`(0,S) × ℝ^d × ℝ^d` with `‖G‖_{L^q} ≤ C M S^{(1-2d(q-1))/q}`, `C = greenConstant d q C_γ`.

The only premise besides the two Green measures ((2.6)) is `hbounds`, which
Lemma 5.1 must discharge. -/
theorem green_density_of_slab_marginals {d : ℕ} (C : ℝ → ℝ≥0) (c : ℝ)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    (hbounds : ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ)
    {q S : ℝ} (hq : 1 < q) (hqd : q < 1 + 1 / (2 * (d : ℝ))) (hS : 0 < S)
    (ΓS : Measure (ElapsedTime (ENNReal.ofReal S) × EvolutionAmbientState d))
    (hΓS : IsGreenMeasure K σ₀ (ENNReal.ofReal S) μ ΓS) :
    ∃ G : ElapsedTime (ENNReal.ofReal S) × EvolutionAmbientState d → ℝ≥0∞, Measurable G ∧
      ΓS = ((elapsedVolume (ENNReal.ofReal S)).prod
        (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) ((elapsedVolume (ENNReal.ofReal S)).prod
        (volume : Measure (EvolutionAmbientState d))) ≤
        (greenConstant d q C : ℝ≥0∞) * μ univ *
          ENNReal.ofReal (S ^ (greenDelta d q / q))   := by
  have greenDelta_pos :
      0 < greenDelta d q := by
    have hd : 0 < (d : ℝ) := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hqd; linarith
      · exact_mod_cast h
    unfold greenDelta
    have h1 : q - 1 < 1 / (2 * (d : ℝ)) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  have measurableEmbedding_horizonInclusion (S : ℝ≥0∞) : MeasurableEmbedding (horizonInclusion d S) :=
    (measurableEmbedding_elapsedInclusion (le_top : S ≤ ⊤)).prodMap MeasurableEmbedding.id
  have hδ := greenDelta_pos
  have hd : 0 < (d : ℝ) := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hqd; linarith
    · exact_mod_cast h
  have hqd' : q < 1 + 1 / (d : ℝ) := by
    have : 1 / (2 * (d : ℝ)) ≤ 1 / (d : ℝ) :=
      one_div_le_one_div_of_le hd (by linarith)
    linarith
  have hq0 : 0 < q := by linarith
  -- local densities on every slab (conditional Proposition 5.3)
  have hloc : ∀ T : ℝ, ∃ G : GreenCarrier d → ℝ≥0∞, 0 < T →
      (Measurable G ∧
        Γ.restrict (slabSet T) = ((greenLebesgue d).restrict (slabSet T)).withDensity G ∧
        ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue d ≤
          (slabConstant d q C : ℝ≥0∞) * μ univ ^ q *
            ENNReal.ofReal (T ^ (1 - 2 * (d : ℝ) * (q - 1)))) := by
    intro T
    by_cases hT : 0 < T
    · obtain ⟨G, h1, h2, h3⟩ :=
        slab_density_of_fourier_marginals C c K σ₀ μ Γ hΓ hq hqd' hT (hbounds T hT)
      exact ⟨G, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose Gl hGl using hloc
  -- gluing
  obtain ⟨G, hGm, hΓG, hGae⟩ := exists_global_density K σ₀ μ Γ hΓ Gl
    (fun T hT => (hGl T hT).1) (fun T hT => (hGl T hT).2.1)
  -- logarithmic integration
  set M := μ univ with hM
  set Kq : ℝ≥0∞ := (slabConstant d q C : ℝ≥0∞) * M ^ q with hKq
  have hν_slab : ∀ T : ℝ, 0 < T →
      ((greenLebesgue d).withDensity (fun p => G p ^ q)) (slabSet T) ≤
        Kq * ENNReal.ofReal (T ^ greenDelta d q) := by
    intro T hT
    rw [withDensity_apply _ (measurableSet_slabSet T)]
    calc ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue d
        = ∫⁻ p in slabSet T, Gl T p ^ q ∂greenLebesgue d := by
          refine lintegral_congr_ae ?_
          filter_upwards [hGae T hT] with p hp
          rw [hp]
      _ ≤ _ := (hGl T hT).2.2
  have hint : ENNReal.ofReal (Real.log 2) *
      ((greenLebesgue d).withDensity (fun p => G p ^ q)) {p : GreenCarrier d | p.1.1 < S} ≤
        Kq * ENNReal.ofReal (S ^ greenDelta d q / greenDelta d q) := by
    refine (log_mul_measure_le ((greenLebesgue d).withDensity (fun p => G p ^ q)) (h := fun p => p.1.1) (measurable_subtype_coe.comp measurable_fst) (fun p => p.1.2.1) S).trans ?_
    rw [← lintegral_inv_mul_rpow hS hδ Kq]
    refine setLIntegral_mono' measurableSet_Ioc fun T hT => ?_
    exact mul_le_mul_right (hν_slab T hT.1) _
  -- restriction to the horizon `S`
  have hR : MeasurableSet {p : GreenCarrier d | ENNReal.ofReal p.1.1 < ENNReal.ofReal S} :=
    (ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp measurable_fst))
      measurableSet_Iio
  have hRset : {p : GreenCarrier d | ENNReal.ofReal p.1.1 < ENNReal.ofReal S} =
      {p : GreenCarrier d | p.1.1 < S} := by
    ext p
    simp [ENNReal.ofReal_lt_ofReal_iff hS]
  have hemb := measurableEmbedding_horizonInclusion (ENNReal.ofReal S)
  have hden : ΓS = ((elapsedVolume (ENNReal.ofReal S)).prod
      (volume : Measure (EvolutionAmbientState d))).withDensity
        (fun x => G (horizonInclusion d (ENNReal.ofReal S) x)) := by
    refine eq_withDensity_of_map_eq_emb hemb ?_
    rw [map_horizonInclusion_lebesgue, ← restrict_withDensity hR, ← hΓG]
    exact greenMeasure_horizonRestriction K σ₀ (ENNReal.ofReal S) ⊤ le_top μ ΓS Γ hΓS hΓ
  have hlint : ∫⁻ x, (G (horizonInclusion d (ENNReal.ofReal S) x)) ^ q
      ∂((elapsedVolume (ENNReal.ofReal S)).prod (volume : Measure (EvolutionAmbientState d))) =
        ((greenLebesgue d).withDensity (fun p => G p ^ q)) {p : GreenCarrier d | p.1.1 < S} := by
    rw [← hRset, withDensity_apply _ hR, ← map_horizonInclusion_lebesgue d (ENNReal.ofReal S),
      hemb.lintegral_map]
  refine ⟨fun x => G (horizonInclusion d (ENNReal.ofReal S) x), hGm.comp hemb.measurable,
    hden, ?_⟩
  have hmeasGS : Measurable (fun x => G (horizonInclusion d (ENNReal.ofReal S) x)) :=
    hGm.comp hemb.measurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal ((ENNReal.ofReal_pos.2 hq0).ne') ENNReal.ofReal_ne_top
    hmeasGS.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  simp only [enorm_eq_self]
  rw [hlint]
  have hL0 := (ENNReal.ofReal_pos.2 (Real.log_pos one_lt_two)).ne'
  have hν := (ENNReal.mul_le_iff_le_inv hL0 ENNReal.ofReal_ne_top).1 hint
  have h1q : 0 ≤ 1 / q := by positivity
  have hcg : (greenConstant d q C : ℝ≥0∞) =
      ((slabConstant d q C : ℝ≥0∞) * (ENNReal.ofReal (Real.log 2))⁻¹ *
        ENNReal.ofReal (1 / greenDelta d q)) ^ (1 / q) := by
    unfold greenConstant
    refine ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg h1q ?_)
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.inv_ne_top.2 hL0)) ENNReal.ofReal_ne_top
  rw [hcg, ← green_arith (slabConstant d q C) M hS hδ hq]
  refine (ENNReal.rpow_le_rpow hν h1q).trans (le_of_eq ?_)
  congr 1
  rw [hKq]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Green

