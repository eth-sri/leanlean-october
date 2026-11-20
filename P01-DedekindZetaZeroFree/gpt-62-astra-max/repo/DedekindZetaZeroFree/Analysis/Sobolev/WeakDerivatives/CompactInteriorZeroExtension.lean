module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData
public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactInteriorCutoffs

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology

section

variable {n r : ℕ}

theorem weakFirst_zero_on_open {Ω W : Opens (E n)}
    {f : E n → V r} {g : Fin n → E n → V r}
    (hfg : WeakFirst Ω f g) (hWΩ : (W : Set (E n)) ⊆ (Ω : Set (E n)))
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (W : Set (E n)) → f x = 0) :
    ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (W : Set (E n)) → g j x = 0 := by
  intro j
  have hcomp : ∀ a : Fin r, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (W : Set (E n)) → (g j x) a = 0 := by
    intro a
    refine W.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
       ?_ ?_
    · rw [locallyIntegrableOn_iff W.isOpen.isLocallyClosed]
      intro k hkW hkc
      have hkΩ := hkW.trans hWΩ
      haveI : IsFiniteMeasure (volume.restrict k) :=
        isFiniteMeasure_restrict.2 hkc.measure_ne_top
      show Integrable (fun x => (g j x) a)
        ((volume.restrict Ω).restrict k)
      rw [Measure.restrict_restrict hkc.measurableSet, Set.inter_eq_left.mpr hkΩ]
      simpa using ((EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp (((hfg.derivative_locallyL2 j).2 k hkc hkΩ).integrable (by norm_num)))
    · intro g0 hg0 hg0c hg0s
      have hsupp : tsupport (fun x => (g0 x : ℂ)) = tsupport g0 := by
        unfold tsupport
        congr 1
        ext x
        simp
      let ψ : TestFunction Ω ℂ ⊤ :=
        ⟨fun x => (g0 x : ℂ), (Complex.ofRealCLM.contDiff.comp hg0), by change IsCompact _; rw [hsupp]; exact hg0c,
          fun x hx => hWΩ (hg0s (hsupp ▸ hx))⟩
      have hw := hfg.weak_identity j ψ a
      have hleft : (∫ x in (Ω : Set (E n)),
          (f x) a * coordinatePartial j (fun y => ψ y) x) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hf] with x hx
        by_cases hxW : x ∈ W
        · rw [hx hxW]
          simp
        · have hxnot' := (fun hh => hxW (hg0s (hsupp ▸ hh)))
          have hfd : fderiv ℝ (fun y => ψ y) x = 0 :=
            fderiv_of_notMem_tsupport (𝕜 := ℝ) hxnot'
          rw [coordinatePartial, hfd]
          simp
      rw [hleft, zero_eq_neg] at hw
      have hgoal : (∫ x, g0 x • (g j x) a ∂(volume.restrict Ω)) =
          ∫ x in Ω, (g j x) a * ψ x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show ψ x = (g0 x : ℂ) from rfl, Complex.real_smul, mul_comm]
      rw [hgoal]
      exact hw
  filter_upwards [Filter.eventually_all.mpr hcomp] with x hx
  intro hxW
  ext a
  exact hx a hxW

theorem weakFirst_zero_off_compact {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (E n)))
    (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → g j x = 0 := by
  let W : Opens (E n) := ⟨(Ω : Set (E n)) \ K, Ω.isOpen.sdiff hK.isClosed⟩
  have hWΩ : (W : Set (E n)) ⊆ (Ω : Set (E n)) := fun _ hx => hx.1
  exact weakFirst_zero_on_open hfg hWΩ hf

def compactZeroExtension (K : Set (E n)) (f : E n → V r) :
    E n → V r :=
  K.indicator f

end

section

variable {n r : ℕ} {Ω : Opens (E n)} {K : Set (E n)} {f : E n → V r}

private theorem compactZeroExtension_memLp (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set (E n))) (hf : LocallyL2 Ω f) :
    MemLp (compactZeroExtension K f) 2 volume :=
  (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2 (hf.2 K hK hKΩ)

private theorem compactZeroExtension_ae_eq
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    compactZeroExtension K f =ᵐ[volume.restrict (Ω : Set (E n))] f := by
  filter_upwards [hf, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  by_cases hxK : x ∈ K
  · simp [compactZeroExtension, hxK]
  · simp [compactZeroExtension, hxK, hx ⟨hxΩ, hxK⟩]

end

variable {n r : ℕ} {Ω : Opens (E n)} {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (E n))) (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)), x ∈ (Ω : Set (E n)) \ K → f x = 0)

include hK hKΩ hfg hf in
theorem compactZeroExtension_properties :
    let F := compactZeroExtension K f
    let G := fun j => compactZeroExtension K (g j)
    MemLp F 2 volume ∧
    (∀ j, MemLp (G j) 2 volume) ∧
    Integrable F volume ∧
    (∀ j, Integrable (G j) volume) ∧
    (∀ x, x ∉ K → F x = 0) ∧
    (∀ j x, x ∉ K → G j x = 0) ∧
    tsupport F ⊆ K ∧
    (∀ j, tsupport (G j) ⊆ K) ∧
    F =ᵐ[volume.restrict (Ω : Set (E n))] f ∧
    (∀ j, G j =ᵐ[volume.restrict (Ω : Set (E n))] g j) := by
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hFmem :=
    compactZeroExtension_memLp hK hKΩ hfg.section_locallyL2
  have hGmem := fun j =>
    compactZeroExtension_memLp hK hKΩ (hfg.derivative_locallyL2 j)
  have hGint := fun j =>
    (integrableOn_iff_integrable_of_support_subset
      Set.support_indicator_subset).mp
      (((hGmem j).mono_measure Measure.restrict_le_self).integrable (by norm_num))
  exact ⟨hFmem, hGmem, ((integrableOn_iff_integrable_of_support_subset
    Set.support_indicator_subset).mp
    ((hFmem.mono_measure Measure.restrict_le_self).integrable (by norm_num))), hGint, (fun x hx =>
    Set.indicator_of_notMem hx f), (fun j x hx =>
    Set.indicator_of_notMem hx (g j)), (closure_minimal Set.support_indicator_subset hK.isClosed), (fun j =>
    closure_minimal Set.support_indicator_subset hK.isClosed), (compactZeroExtension_ae_eq hf), (fun j => compactZeroExtension_ae_eq (weakFirst_zero_off_compact hK hKΩ hfg hf j))⟩

include hK hKΩ hfg hf in
theorem compactZeroExtension_weak_identity
    (ψ : E n → ℂ) (hψ : ContDiff ℝ ∞ ψ) (j : Fin n) (a : Fin r) :
    Integrable (fun x => (compactZeroExtension K f x) a * coordinatePartial j ψ x)
      volume ∧
    Integrable (fun x => (compactZeroExtension K (g j) x) a * ψ x) volume ∧
    (∫ x, (compactZeroExtension K f x) a * coordinatePartial j ψ x) =
      -(∫ x, (compactZeroExtension K (g j) x) a * ψ x) := by
  obtain ⟨η, N, hNopen, hKN, hNΩ, hηsm, hηc, hηts, _hη01, hηN, _hηder, _⟩ :=
    exists_smooth_cutoff (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt) Ω K Ω.isOpen hK hKΩ
  let ηc := fun x => (η x : ℂ)
  have hηc_ts : tsupport ηc = tsupport η := by
    unfold tsupport ηc
    congr 1
    ext x
    simp
  have hΨ_sm := (Complex.ofRealCLM.contDiff.comp hηsm).mul hψ
  have hηc_c : HasCompactSupport ηc := hηc.comp_left (g := Complex.ofRealCLM) (by simp)
  have hΨ_c : HasCompactSupport (fun x => ηc x * ψ x) :=
    hηc_c.of_isClosed_subset isClosed_closure (closure_mono fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      exact fun h => hx (by rw [h, zero_mul]))
  have hΨ_ts : tsupport (fun x => ηc x * ψ x) ⊆ (Ω : Set (E n)) := by
    refine (tsupport_mul_subset_left (f := ηc) (g := ψ)).trans ?_
    rw [hηc_ts]
    exact hηts
  let Ψ : TestFunction Ω ℂ ⊤ :=
    ⟨fun x => ηc x * ψ x, hΨ_sm, hΨ_c, hΨ_ts⟩
  have hΨeq : ∀ y, Ψ y = (η y : ℂ) * ψ y := fun y => rfl
  have hcont : Continuous (coordinatePartial j ψ) := by
    exact (hψ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)

  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨Cψ, hCψ⟩ := hK.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hsuppF : Function.support
      (fun x => (compactZeroExtension K f x) a * coordinatePartial j ψ x) ⊆ K := by
    intro x hx
    by_contra hxK
    refine hx ?_
    have h0 : (compactZeroExtension K f x) a = 0 := by
      rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
    show (compactZeroExtension K f x) a * coordinatePartial j ψ x = 0
    rw [h0, zero_mul]
  have hsuppG : Function.support
      (fun x => (compactZeroExtension K (g j) x) a * ψ x) ⊆ K := by
    intro x hx
    by_contra hxK
    refine hx ?_
    have h0 : (compactZeroExtension K (g j) x) a = 0 := by
      rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
    show (compactZeroExtension K (g j) x) a * ψ x = 0
    rw [h0, zero_mul]
  have hintF : Integrable (fun x => (compactZeroExtension K f x) a * coordinatePartial j ψ x)
      volume := by
    refine (integrableOn_iff_integrable_of_support_subset hsuppF).mp ?_
    exact (((EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp
      (((compactZeroExtension_memLp hK hKΩ hfg.section_locallyL2).mono_measure Measure.restrict_le_self).integrable (by norm_num))).mul_bdd
        hcont.aestronglyMeasurable (by
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          exact hC x hx))
  have hintG : Integrable (fun x => (compactZeroExtension K (g j) x) a * ψ x) volume := by
    refine (integrableOn_iff_integrable_of_support_subset hsuppG).mp ?_
    exact (((EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp
      (((compactZeroExtension_memLp hK hKΩ (hfg.derivative_locallyL2 j)).mono_measure Measure.restrict_le_self).integrable (by norm_num))).mul_bdd
        hψ.continuous.aestronglyMeasurable (by
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          exact hCψ x hx))

  have hstep1 : (∫ x in Ω, (f x) a * coordinatePartial j (fun y => Ψ y) x)
      = ∫ x in Ω,
        (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x := by
    apply integral_congr_ae
    filter_upwards [(compactZeroExtension_ae_eq hf)] with x hx
    rw [hx]
  have hstep2 : (∫ x in Ω,
        (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x)
      = ∫ x, (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [compactZeroExtension, Set.indicator_of_notMem (fun h => hx (hKΩ h))]
    simp
  have hR1 : (∫ x in Ω, (g j x) a * Ψ x)
      = ∫ x in Ω, (compactZeroExtension K (g j) x) a * Ψ x := by
    apply integral_congr_ae
    filter_upwards [(compactZeroExtension_ae_eq (weakFirst_zero_off_compact hK hKΩ hfg hf j))] with x hx
    rw [hx]
  have hR2 : (∫ x in Ω, (compactZeroExtension K (g j) x) a * Ψ x)
      = ∫ x, (compactZeroExtension K (g j) x) a * Ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [compactZeroExtension, Set.indicator_of_notMem (fun h => hx (hKΩ h))]
    simp
  have hfinalF : (∫ x, (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x)
      = ∫ x, (compactZeroExtension K f x) a * coordinatePartial j ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxK : x ∈ K
    · have hev : (fun y => Ψ y) =ᶠ[𝓝 x] ψ := by
        filter_upwards [(fun x hx => hNopen.mem_nhds (hKN hx)) x hxK] with y hy
        rw [hΨeq y, hηN y hy]
        simp
      have hfd : coordinatePartial j (fun y => Ψ y) x = coordinatePartial j ψ x := by
        simp only [coordinatePartial]
        rw [hev.fderiv_eq]
      rw [hfd]
    · rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
  have hfinalG : (∫ x, (compactZeroExtension K (g j) x) a * Ψ x)
      = ∫ x, (compactZeroExtension K (g j) x) a * ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxK : x ∈ K
    · rw [hΨeq x, hηN x (hKN hxK)]
      simp
    · rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
  refine ⟨hintF, hintG, ?_⟩
  rw [← hfinalF, ← hfinalG]
  exact by
    rw [← hstep2, ← hstep1, ← hR2, ← hR1]
    exact (hfg.weak_identity j Ψ a)

include hK hKΩ hfg hf in
theorem compactZeroExtension_weakFirst :
    WeakFirst (⊤ : Opens (E n)) (compactZeroExtension K f)
      (fun j => compactZeroExtension K (g j)) := by
  obtain ⟨hFmem, hGmem, -, -, -, -, -, -, -, -⟩ :=
    compactZeroExtension_properties hK hKΩ hfg hf
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by simpa using hFmem.aestronglyMeasurable,
      fun L _ _ => hFmem.mono_measure Measure.restrict_le_self⟩
  · intro j
    exact ⟨by simpa using (hGmem j).aestronglyMeasurable,
      fun L _ _ => (hGmem j).mono_measure Measure.restrict_le_self⟩
  · intro j ψ a
    simpa using (compactZeroExtension_weak_identity hK hKΩ hfg hf (fun y => ψ y) ψ.contDiff' j a).2.2

end DedekindZetaZeroFree.KPCompactInteriorH1

end
