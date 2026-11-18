module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ViscosityWeakLimit
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter Topology MeasureTheory HypoellipticAleksandrov Set Evolution
open scoped NNReal ENNReal Topology MatrixOrder

/-- A bounded sequence in a separable real Hilbert space has a weakly convergent
subsequence. -/
theorem exists_hilbert_weak_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (v : ℕ → H) (R : ℝ) (hv : ∀ j, ‖v j‖ ≤ R) :
    ∃ (u : H) (ν : ℕ → ℕ), StrictMono ν ∧
      ∀ w : H, Tendsto (fun j => inner ℝ (v (ν j)) w)
        atTop (nhds (inner ℝ u w)) := by
  let f : ℕ → WeakDual ℝ H := fun j =>
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) (v j))
  have hf : ∀ j, f j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
    intro j
    change dist ((InnerProductSpace.toDual ℝ H) (v j)) 0 ≤ R
    simpa using hv j
  obtain ⟨g, _, ν, hν, hg⟩ := (WeakDual.isSeqCompact_closedBall
    (𝕜 := ℝ) (E := H) 0 R) hf
  refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual g), ν, hν, ?_⟩
  intro w
  simpa using! ((WeakDual.eval_continuous w).continuousAt.tendsto.comp hg)


private theorem integral_mul_toLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

private theorem pairing_lipschitz {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {C : ℝ≥0}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ x ∂μ, |f x| ≤ C) :
    LipschitzWith C (fun ψ : Lp ℝ 1 μ => ∫ x, f x * ψ x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro ψ φ
  have hψ : Integrable (fun x => f x * ψ x) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp ψ)).bdd_mul hf hb
  have hφ : Integrable (fun x => f x * φ x) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp φ)).bdd_mul hf hb
  rw [dist_eq_norm, ← integral_sub hψ hφ, dist_eq_norm, L1.norm_eq_integral_norm,
    ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono_ae
  · exact (hψ.sub hφ).norm
  · exact ((memLp_one_iff_integrable.mp (Lp.memLp (ψ - φ))).norm).const_mul _
  filter_upwards [hb, Lp.coeFn_sub ψ φ] with x hx he
  rw [he, Pi.sub_apply, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem extend_integral_tests {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    (v : ℕ → α → ℝ) (u : α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u μ) (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (ht : ∀ ψ : α → ℝ, MemLp ψ 2 μ →
      Tendsto (fun j => ∫ x, v j x * ψ x ∂μ) atTop (nhds (∫ x, u x * ψ x ∂μ))) :
    ∀ ψ : α → ℝ, Integrable ψ μ →
      Tendsto (fun j => ∫ x, v j x * ψ x ∂μ) atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
  let K : ℝ≥0 := ⟨C, hC⟩
  let F (j : ℕ) (ψ : Lp ℝ 1 μ) := ∫ x, v j x * ψ x ∂μ
  let G (ψ : Lp ℝ 1 μ) := ∫ x, u x * ψ x ∂μ
  have hF : ∀ j, LipschitzWith K (F j) := fun j => pairing_lipschitz (hv j) (hb j)
  have hG : LipschitzWith K G := pairing_lipschitz hu hub
  have hclosed : IsClosed {ψ : Lp ℝ 1 μ | Tendsto (fun j => F j ψ) atTop (nhds (G ψ))} :=
    (LipschitzWith.uniformEquicontinuous F K hF).equicontinuous.isClosed_setOfPred_tendsto
      hG.continuous
  have hall : ∀ ψ : Lp ℝ 1 μ, Tendsto (fun j => F j ψ) atTop (nhds (G ψ)) := by
    intro ψ
    refine (Lp.simpleFunc.denseRange (μ := μ) (by simp)).induction_on
      (p := fun φ => Tendsto (fun j => F j φ) atTop (nhds (G φ))) ψ hclosed ?_
    intro f
    let φ : Lp ℝ 1 μ := f
    let s := Lp.simpleFunc.toSimpleFunc f
    have hs : MemLp s 2 μ := s.memLp_of_finite_measure_preimage 2
      (fun _ _ => measure_lt_top _ _)
    have he := Lp.simpleFunc.toSimpleFunc_eq_toFun f
    have hvEq : ∀ j, (∫ x, v j x * s x ∂μ) = F j φ := by
      intro j
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    have huEq : (∫ x, u x * s x ∂μ) = G φ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    simpa only [hvEq, huEq] using ht s hs
  intro ψ hψ
  let φ := (memLp_one_iff_integrable.mpr hψ).toLp ψ
  have he : ⇑φ =ᵐ[μ] ψ := MemLp.coeFn_toLp _
  have hvEq : ∀ j, F j φ = ∫ x, v j x * ψ x ∂μ := by
    intro j
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have huEq : G φ = ∫ x, u x * ψ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  simpa only [hvEq, huEq] using hall φ

/-- Uniformly bounded measurable functions on a finite separable measure space
have a subsequence converging against every integrable test. -/
theorem exists_finite_bounded_weak_subsequence
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [MeasureTheory.IsSeparable μ]
    (v : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C) :
    ∃ (u : α → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧ AEStronglyMeasurable u μ ∧
      (∀ᵐ x ∂μ, |u x| ≤ C) ∧
      ∀ ψ : α → ℝ, Integrable ψ μ →
        Tendsto (fun j => ∫ x, v (ν j) x * ψ x ∂μ)
          atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
  have : Fact (2 ≠ ∞) := ⟨by norm_num⟩
  let hm (j : ℕ) : MemLp (v j) 2 μ := MemLp.of_bound (hv j) C (hb j)
  let V (j : ℕ) : Lp ℝ 2 μ := (hm j).toLp (v j)
  let R : ℝ := ‖(memLp_const C : MemLp (fun _ => C) 2 μ).toLp (fun _ => C)‖
  have hV : ∀ j, ‖V j‖ ≤ R := by
    intro j
    change ‖(hm j).toLp (v j)‖ ≤ R
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hm j).coeFn_toLp, (memLp_const C
      : MemLp (fun _ => C) 2 μ).coeFn_toLp, hb j] with x hx hy hb'
    simpa only [hx, hy, Real.norm_eq_abs, abs_of_nonneg hC] using hb'
  obtain ⟨u, ν, hν, ht⟩ := exists_hilbert_weak_subsequence V R hV
  have htest : ∀ ψ : α → ℝ, MemLp ψ 2 μ →
      Tendsto (fun j => ∫ x, v (ν j) x * ψ x ∂μ)
        atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
    intro ψ hψ
    have h := ht (hψ.toLp ψ)
    have hu : inner ℝ u (hψ.toLp ψ) = ∫ x, u x * ψ x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with x hx
      simp only [hx, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]
    simpa only [V, integral_mul_toLp, hu] using h
  have hui := (Lp.memLp u).integrable (by norm_num)
  have hset (s : Set α) (hs : MeasurableSet s) :
      Tendsto (fun j => ∫ x in s, v (ν j) x ∂μ)
        atTop (nhds (∫ x in s, u x ∂μ)) := by
    simpa [← Set.indicator_mul_right, integral_indicator hs] using (htest (s.indicator (fun _ => 1)) ((memLp_const 1).indicator hs))
  have hupper : ∀ᵐ x ∂μ, u x ≤ C := by
    apply ae_le_of_forall_setIntegral_le hui (integrable_const C)
    intro s hs _
    apply le_of_tendsto (hset s hs)
    filter_upwards with j
    apply integral_mono_ae
    · exact ((hm (ν j)).integrable (by norm_num)).integrableOn
    · exact integrable_const C
    exact (ae_restrict_of_ae (hb (ν j))).mono fun x hx => (le_abs_self _).trans hx
  have hlower : ∀ᵐ x ∂μ, -C ≤ u x := by
    apply ae_le_of_forall_setIntegral_le (integrable_const (-C)) hui
    intro s hs _
    apply ge_of_tendsto (hset s hs)
    filter_upwards with j
    apply integral_mono_ae
    · exact integrable_const (-C)
    · exact ((hm (ν j)).integrable (by norm_num)).integrableOn
    exact (ae_restrict_of_ae (hb (ν j))).mono fun x hx => (abs_le.mp hx).1
  have hub : ∀ᵐ x ∂μ, |u x| ≤ C := by
    filter_upwards [hlower, hupper] with x hx hy
    exact abs_le.mpr ⟨hx, hy⟩
  exact ⟨u, ν, hν, Lp.aestronglyMeasurable u, hub,
    extend_integral_tests (fun j => v (ν j)) u C hC (fun j => hv (ν j))
      (fun j => hb (ν j)) (Lp.aestronglyMeasurable u) hub htest⟩


/-- Uniformly bounded measurable functions for a sigma-finite measure on a
countably generated measurable space have a subsequence converging against all L1 tests. -/
theorem exists_sigmaFinite_bounded_weak_subsequence
    {α : Type*} [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α]
    (μ : Measure α) [SigmaFinite μ]
    (v : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C) :
    ∃ (u : α → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧ AEStronglyMeasurable u μ ∧
      (∀ᵐ x ∂μ, |u x| ≤ C) ∧
      ∀ ψ : α → ℝ, Integrable ψ μ →
        Tendsto (fun j => ∫ x, v (ν j) x * ψ x ∂μ)
          atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
  obtain ⟨ρ, hρ, hμρ, hρμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  let : IsFiniteMeasure ρ := hρ
  obtain ⟨u, ν, hν, hu, hub, ht⟩ := exists_finite_bounded_weak_subsequence ρ v C hC
    (fun j => (hv j).mono_ac hρμ) (fun j => hρμ.ae_le (hb j))
  refine ⟨u, ν, hν, hu.mono_ac hμρ, hμρ.ae_le hub, ?_⟩
  intro ψ hψ
  have hmeasure : ρ.withDensity (μ.rnDeriv ρ) = μ := by
    have h := Measure.rnDeriv_add_singularPart μ ρ
    simpa [Measure.singularPart_eq_zero_of_ac hμρ] using h
  let Ψ (x : α) := (μ.rnDeriv ρ x).toReal * ψ x
  have hΨ : Integrable Ψ ρ := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (Measure.measurable_rnDeriv μ ρ) (Measure.rnDeriv_lt_top μ ρ)).mp
      (hmeasure.symm ▸ hψ)
    simpa using h
  have he (f : α → ℝ) : (∫ x, f x * ψ x ∂μ) = ∫ x, f x * Ψ x ∂ρ := by
    rw [← hmeasure, integral_withDensity_eq_integral_toReal_smul
      (Measure.measurable_rnDeriv μ ρ) (Measure.rnDeriv_lt_top μ ρ)]
    congr 1
    funext x
    simp
    ring
  simpa only [← he] using ht Ψ hΨ



private theorem weak_limit_le_on_finite_set {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (v : ℕ → α → ℝ) (u : α → ℝ) (C a : ℝ)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u μ) (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (hlim : ∀ ψ : α → ℝ, Integrable ψ μ →
      Tendsto (fun j => ∫ x, v j x * ψ x ∂μ) atTop (𝓝 (∫ x, u x * ψ x ∂μ)))
    (E : Set α) (hE : MeasurableSet E) (hEf : μ E < ⊤)
    (hle : ∀ j, ∀ x ∈ E, v j x ≤ a) :
    ∀ᵐ x ∂μ.restrict E, u x ≤ a := by
  let : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hEf⟩
  have hui : Integrable u (μ.restrict E) := by
    apply (integrable_const C).mono hu.restrict
    filter_upwards [ae_restrict_of_ae hub] with x hx
    simpa [abs_of_nonneg ((abs_nonneg _).trans hx)] using hx
  refine ae_le_of_forall_setIntegral_le hui (integrable_const a) ?_
  intro S hS _
  have hSE := hS.inter hE
  have hSEf : μ (S ∩ E) ≠ ⊤ := ne_of_lt ((measure_mono inter_subset_right).trans_lt hEf)
  let ψ : α → ℝ := (S ∩ E).indicator (fun _ => 1)
  have hψ : Integrable ψ μ := (integrable_indicator_iff hSE).2 (integrableOn_const hSEf)
  have hid (f : α → ℝ) : (∫ x, f x * ψ x ∂μ) = ∫ x in S ∩ E, f x ∂μ := by
    have heq : (fun x => f x * ψ x) = (S ∩ E).indicator f := by
      funext x
      by_cases hx : x ∈ S ∩ E <;> simp [ψ, hx]
    rw [heq, integral_indicator hSE]
  have ht := hlim ψ hψ
  simp only [hid] at ht
  have hineq : ∀ j, (∫ x in S ∩ E, v j x ∂μ) ≤ ∫ x in S ∩ E, a ∂μ := by
    intro j
    have hi : IntegrableOn (v j) (S ∩ E) μ := by
      apply (show Integrable (fun _ => C) (μ.restrict (S ∩ E)) from
        integrableOn_const hSEf).mono (hv j).restrict
      filter_upwards [ae_restrict_of_ae (hb j)] with x hx
      simpa [abs_of_nonneg ((abs_nonneg _).trans hx)] using hx
    apply integral_mono_ae hi (integrableOn_const hSEf)
    filter_upwards [ae_restrict_mem hSE] with x hx
    exact hle j x hx.2
  simpa only [Measure.restrict_restrict hS] using (le_of_tendsto ht (Filter.Eventually.of_forall hineq))

/-- The existing kinetic volume assigns positive mass to every nonempty open set. -/
instance kineticVolume_isOpenPosMeasure (n : ℕ) :
    Measure.IsOpenPosMeasure (volume : Measure (KineticPoint n)) := by
  change Measure.IsOpenPosMeasure
    (Measure.map (KineticPoint.equivProd n).symm volume)
  exact (KineticPoint.homeomorphProd n).symm.continuous.isOpenPosMeasure_map
    (KineticPoint.equivProd n).symm.surjective

/-- A smooth representative inherits every uniform upper bound on an open subregion. -/
theorem bounded_weak_limit_le_on_open {n : ℕ}
    (U W : Set (KineticPoint n)) (hW : IsOpen W) (hWU : W ⊆ U)
    (v : ℕ → KineticPoint n → ℝ) (u V : KineticPoint n → ℝ) (C a : ℝ)
    (hv : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U))
    (hb : ∀ j, ∀ᵐ x ∂volume.restrict U, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u (volume.restrict U))
    (hub : ∀ᵐ x ∂volume.restrict U, |u x| ≤ C)
    (hlim : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ x in U, v j x * ψ x) atTop (𝓝 (∫ x in U, u x * ψ x)))
    (hV : ContinuousOn V U) (hrep : u =ᵐ[volume.restrict U] V)
    (hle : ∀ j, ∀ x ∈ W, v j x ≤ a) : ∀ x ∈ W, V x ≤ a := by
  intro x hx
  obtain ⟨E, hEx, hEf⟩ := (volume : Measure (KineticPoint n)).finiteAt_nhds x
  obtain ⟨O, hOE, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hEx (hW.mem_nhds hx))
  have hOU : O ⊆ U := (fun p hp => hWU (hOE hp).2)
  have hOW : O ⊆ W := fun p hp => (hOE hp).2
  have hOf : (volume.restrict U) O < ⊤ := by
    rw [Measure.restrict_apply hO.measurableSet, inter_eq_left.mpr hOU]
    exact (measure_mono (fun p hp => (hOE hp).1)).trans_lt hEf
  have hrestrict : (volume.restrict U).restrict O = volume.restrict O := by
    rw [Measure.restrict_restrict hO.measurableSet, inter_eq_left.mpr hOU]
  have hleV : ∀ᵐ p ∂volume.restrict O, V p ≤ a := by
    rw [← hrestrict]
    filter_upwards [(weak_limit_le_on_finite_set (volume.restrict U) v u C a hv hb hu hub hlim O hO.measurableSet hOf (fun j p hp => hle j p (hOW hp))), ae_restrict_of_ae hrep] with p hp he
    rwa [← he]
  have hae : V =ᵐ[volume.restrict O] fun p => min (V p) a := by
    filter_upwards [hleV] with p hp
    exact (min_eq_left hp).symm
  have hcV := hV.mono hOU
  rw [(Measure.eqOn_open_of_ae_eq hae hO hcV (hcV.inf continuousOn_const)) hxO]
  exact min_le_right _ _

/-- Uniform local absolute trace bounds pass to the continuous weak-limit representative. -/
theorem bounded_weak_limit_abs_sub_le_on_open {n : ℕ}
    (U W : Set (KineticPoint n)) (hW : IsOpen W) (hWU : W ⊆ U)
    (v : ℕ → KineticPoint n → ℝ) (u V : KineticPoint n → ℝ) (C a η : ℝ)
    (hv : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U))
    (hb : ∀ j, ∀ᵐ x ∂volume.restrict U, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u (volume.restrict U))
    (hub : ∀ᵐ x ∂volume.restrict U, |u x| ≤ C)
    (hlim : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ x in U, v j x * ψ x) atTop (𝓝 (∫ x in U, u x * ψ x)))
    (hV : ContinuousOn V U) (hrep : u =ᵐ[volume.restrict U] V)
    (hbound : ∀ j, ∀ x ∈ W, |v j x - a| ≤ η) :
    ∀ x ∈ W, |V x - a| ≤ η := by
  have hupp := bounded_weak_limit_le_on_open U W hW hWU v u V C (a + η)
    hv hb hu hub hlim hV hrep (fun j x hx => by
      have h := (abs_le.mp (hbound j x hx)).2
      linarith)
  have hlimneg : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ x in U, (-v j x) * ψ x)
        atTop (𝓝 (∫ x in U, (-u x) * ψ x)) := by
    intro ψ hψ
    simpa only [neg_mul, integral_neg] using (hlim ψ hψ).neg
  intro x hx
  exact abs_le.mpr ⟨by linarith [(bounded_weak_limit_le_on_open U W hW hWU (fun j x => -v j x) (fun x => -u x) (fun x => -V x) C (η - a) (fun j => (hv j).neg) (fun j => by simpa only [abs_neg] using hb j) hu.neg (by simpa only [abs_neg] using hub) hlimneg hV.neg (by filter_upwards [hrep] with x hx; simp only [hx]) (fun j x hx => by have h := (abs_le.mp (hbound j x hx)).1; linarith)) x hx], by linarith [hupp x hx]⟩


/-- A smooth representative of the zero-source weak equation satisfies the equation
pointwise in the original kinetic coordinates. -/
theorem transportedForwardOperator_eq_zero_of_smooth_weak {n : ℕ}
    {B : FullKineticCoefficient n} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b : PDE.Vec n → PDE.Vec n}
    (hb : IsSmoothDrift b) {U : Set (KineticPoint n)} (hU : IsOpen U)
    {u V : KineticPoint n → ℝ}
    (hu : IsKineticWeakTransportedSolution B b U u (fun _ => 0))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U)) (hrep : u =ᵐ[volume.restrict U] V) :
    ∀ p ∈ U, transportedForwardOperator B b V p = 0 := by
  have hw : IsKineticWeakTransportedSolution B b U V (fun _ => 0) := by
    refine ⟨(locallyIntegrableOn_congr hrep).mp hu.1, ?_⟩
    intro ψ hψ hc hs
    have he := hu.2 ψ hψ hc hs
    rw [← he]
    apply integral_congr_ae
    filter_upwards [hrep] with p hp
    rw [hp]
  have hP := (evolutionHomeomorph n).continuous.isOpen_preimage U hU
  have hreg : IsWeakRegularizedSolution B b 0 (evolutionHomeomorph n ⁻¹' U)
      (V ∘ evolutionHomeomorph n) (fun _ => 0) := by
    simpa [IsWeakRegularizedSolution, IsWeakTransportedSolution, IsDistributionalSolution, regularizedAdjoint, transportedAdjoint, Function.comp_def] using ((isWeakTransportedSolution_comp_iff B b U V (fun _ => 0)).mpr hw)
  intro p hpin
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by simpa [x] using hpin
  have heq := (regularizedOperator_eq_zero_of_smooth_weak hP hB hBs hb 0 hV hreg) x hx
  rw [regularizedOperator_comp 0 ((hV.contDiffAt (hP.mem_nhds hx)).of_le (by simp)),
    zero_mul, add_zero] at heq
  simpa [x] using heq

/-- Interior compactness retains all integrable tests as well as a smooth representative.
Boundary extension is handled separately by uniform trace estimates. -/
theorem exists_smooth_viscosity_sequence_limit
    (hH : HormanderHypoellipticityStatement)
    (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) (C : ℝ) (hC : 0 ≤ C)
    (v : ℕ → KineticPoint n → ℝ)
    (hv : ∀ j : ℕ, IsClassicalViscousTerminalSolution Ω γ B b (1 / ((j : ℝ) + 1)) τ F (v j))
    (hb : ∀ j, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |v j p| ≤ C) :
    ∃ (u V : KineticPoint n → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧
      AEStronglyMeasurable u (volume.restrict (evolutionPastOpenCylinder Ω γ τ)) ∧
      (∀ᵐ p ∂volume.restrict (evolutionPastOpenCylinder Ω γ τ), |u p| ≤ C) ∧
      (∀ ψ : KineticPoint n → ℝ,
        IntegrableOn ψ (evolutionPastOpenCylinder Ω γ τ) volume →
        Tendsto (fun j => ∫ p in evolutionPastOpenCylinder Ω γ τ, v (ν j) p * ψ p)
          atTop (𝓝 (∫ p in evolutionPastOpenCylinder Ω γ τ, u p * ψ p))) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
        (evolutionHomeomorph n ⁻¹' evolutionPastOpenCylinder Ω γ τ) ∧
      u =ᵐ[volume.restrict (evolutionPastOpenCylinder Ω γ τ)] V ∧
      (∀ p ∈ evolutionPastOpenCylinder Ω γ τ, |V p| ≤ C) ∧
      (∀ p ∈ evolutionPastOpenCylinder Ω γ τ, transportedForwardOperator B b V p = 0) := by
  let : SecondCountableTopology (KineticPoint n) :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
  let U := evolutionPastOpenCylinder Ω γ τ
  have hU := isOpen_evolutionPastOpenCylinder
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 τ
  have hUS : U ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
  have hva : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U) := fun j =>
    (((hv j).2.1.mono hUS).aestronglyMeasurable hU.measurableSet)
  have hba : ∀ j, ∀ᵐ p ∂volume.restrict U, |v j p| ≤ C := fun j => by
    filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
    exact hb j p (hUS hp)
  obtain ⟨u, ν, hν, hua, hub, hlim⟩ := exists_sigmaFinite_bounded_weak_subsequence
    (volume.restrict U) v C hC hva hba
  have hε : Tendsto (fun j => 1 / ((ν j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hν.tendsto_atTop
  have hw := weak_transport_equation_of_vanishing_viscosity n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
    hb_lipschitz hb_coercive τ (fun j => 1 / ((ν j : ℝ) + 1))
    (fun j => by positivity) hε (fun j => v (ν j)) u C hC
    (fun j => classical_viscous_terminalSolution_isWeak
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hB_smooth hB_symm hb_smooth (hv (ν j)))
    (fun j => hba (ν j)) hua hub hlim
  obtain ⟨V, hV, hrep⟩ := exists_smooth_kinetic_representative hH hlam hB_smooth hB_ell
    hb_smooth hm hb_coercive U hU u hw
  have hc : ContinuousOn V U := by
    have hc := hV.continuousOn.comp (evolutionHomeomorph n).symm.continuous.continuousOn
      (fun p hp => by simpa using hp)
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hc
  refine ⟨u, V, ν, hν, hua, hub, hlim, hV, hrep, ?_, ?_⟩
  · have hh := bounded_weak_limit_abs_sub_le_on_open U U hU Subset.rfl
      (fun j => v (ν j)) u V C 0 C (fun j => hva (ν j)) (fun j => hba (ν j))
      hua hub hlim hc hrep (fun j p hp => by simpa using hb (ν j) p (hUS hp))
    simpa using hh
  · exact transportedForwardOperator_eq_zero_of_smooth_weak hB_smooth hB_symm
      hb_smooth hU hw hV hrep

end HypoellipticAleksandrov.KineticAleksandrov

