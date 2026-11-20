module

public import RequestProject.ReconDensity
public import RequestProject.Rellich
public import RequestProject.WeakCompact

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
set_option maxHeartbeats 1200000
noncomputable section
namespace PolyaNeumann

/-! To pass the upper eigenvalue bound to the original domain, only lower
semicontinuity is needed. Pull back the trial functions for compactness,
then use their zero extensions for the limiting weak-gradient identity. -/

theorem exists_common_subseq {ι : Type*} [Fintype ι] (P : ι → (ℕ → ℕ) → Prop)
    (hmono : ∀ i (θ θ' : ℕ → ℕ), P i θ → StrictMono θ' → P i (θ ∘ θ'))
    (hex : ∀ i (θ : ℕ → ℕ), StrictMono θ → ∃ θ' : ℕ → ℕ, StrictMono θ' ∧ P i (θ ∘ θ')) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i, P i θ := by
  classical
  suffices h : ∀ s : Finset ι, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ s, P i θ by
    obtain ⟨θ, hθ, hP⟩ := h Finset.univ
    grind
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a s ha ih =>
    obtain ⟨θ, hθ, hP⟩ := ih
    obtain ⟨θ', hθ', hP'⟩ := hex a θ hθ
    refine ⟨θ ∘ θ', hθ.comp hθ', fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    all_goals tauto

/-- Weak lower semicontinuity of the norm. -/
lemma weak_lsc_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x : ℕ → H} {y : H}
    (hx : ∀ z, Tendsto (fun n => inner ℂ z (x n)) atTop (𝓝 (inner ℂ z y))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ‖y‖ ^ 2 - ε ≤ ‖x n‖ ^ 2 := by
  intro ε hε
  have h := (Complex.continuous_re.tendsto _).comp (hx y)
  have hyy : (inner ℂ y y : ℂ).re = ‖y‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hyy] at h
  filter_upwards [h.eventually (lt_mem_nhds (show ‖y‖ ^ 2 - ε / 2 < ‖y‖ ^ 2 by linarith))]
    with n hn
  have h1 := re_inner_le_norm (𝕜 := ℂ) y (x n)
  simp   at hn
  have h2 : (inner ℂ y (x n)).re = RCLike.re (inner ℂ y (x n)) := rfl
  nlinarith [sq_nonneg (‖y‖ - ‖x n‖)]

lemma norm_sq_sum_orthonormal' {D : Set ℂ} {k : ℕ} {e : Fin k → L2 D}
    (h : Orthonormal ℂ e) (a : Fin k → ℂ) : ‖∑ r, a r • e r‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, h.inner_sum]
  simp only [Complex.conj_mul']
  norm_cast

lemma ofReal_sum_norm_sq {D : Set ℂ} (g : Fin 2 → L2 D) :
    ENNReal.ofReal (∑ i, ‖g i‖ ^ 2) = ∑ i, (‖g i‖₊ : ENNReal) ^ 2 := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg ‖g i‖]
  aesop

private lemma exists_orthonormal_lt {D : Set ℂ} (j : ℕ) {E : ℝ}
    (h : neumannEigenvalue D j < ENNReal.ofReal E) :
    ∃ e : Fin (j + 1) → L2 D, Orthonormal ℂ e ∧ ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy D (∑ r, a r • e r) ≤ ENNReal.ofReal (E * ∑ r, ‖a r‖ ^ 2) := by
  obtain ⟨S, hS, hsup⟩ := iInf_lt_iff.mp (show (⨅ S : Submodule ℂ (L2 D),
    ⨅ _ : Module.finrank ℂ S = j + 1, ⨆ (u : L2 D) (_ : u ∈ S) (_ : u ≠ 0),
      rayleigh D u) < _ from h) |>.imp fun S => iInf_lt_iff.mp
  letI := Module.finite_of_finrank_eq_succ hS
  let b := (stdOrthonormalBasis ℂ S).reindex (finCongr hS)
  let e : Fin (j + 1) → L2 D := fun r => b r
  have he := orthonormal_iff_ite.mpr (orthonormal_iff_ite.mp b.orthonormal)
  refine ⟨e, he, fun a => ?_⟩
  let v := ∑ r, a r • e r
  change neumannEnergy D v ≤ _
  by_cases hv : v = 0
  · rw [hv]
    exact (iInf₂_le 0 isWeakGradient_zero).trans (by simp)
  have hvS : v ∈ S := S.sum_mem fun r _ => S.smul_mem _ (b r).2
  have hr := (le_iSup₂_of_le v hvS (le_iSup (fun _ : v ≠ 0 => rayleigh D v) hv)).trans hsup.le
  have hne : (‖v‖₊ : ENNReal) ^ 2 ≠ 0 := by simpa using hv
  rw [rayleigh, ENNReal.div_le_iff hne (by simp)] at hr
  rwa [ENNReal.ofReal_mul' (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← norm_sq_sum_orthonormal' he, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm_eq_enorm] 

theorem neumannEigenvalue_le_of_orthonormal {Ω : Set ℂ} (j : ℕ) (u : Fin (j + 1) → L2 Ω)
    (hu : Orthonormal ℂ u) (lam : ENNReal)
    (h : ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2)) :
    neumannEigenvalue Ω j ≤ lam := by
  have hS : Module.finrank ℂ (Submodule.span ℂ (Set.range u)) = j + 1 := by
    rw [finrank_span_eq_card hu.linearIndependent]; simp
  unfold neumannEigenvalue
  refine (iInf₂_le (Submodule.span ℂ (Set.range u)) hS).trans
    (iSup₂_le fun v hv => iSup_le fun hv0 => ?_)
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have hn : ‖∑ r, a r • u r‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, hu.inner_sum]
    simp only [Complex.conj_mul']
    norm_cast
  have e1 : (‖∑ r, a r • u r‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (∑ r, ‖a r‖ ^ 2) := by
    rw [← hn, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
  have hne : (‖∑ r, a r • u r‖₊ : ENNReal) ^ 2 ≠ 0 := by simpa using hv0
  unfold rayleigh
  rw [ENNReal.div_le_iff hne (by simp), e1]
  tauto


private def zeroExt {D Ω : Set ℂ} (hD : MeasurableSet D) (h : D ⊆ Ω) : L2 D →ₗᵢ[ℂ] L2 Ω where
  toFun v := ((memLp_extZero hD v).restrict Ω).toLp _
  map_add' v w := by
    apply Lp.ext
    filter_upwards [((memLp_extZero hD (v+w)).restrict Ω).coeFn_toLp,
      ((memLp_extZero hD v).restrict Ω).coeFn_toLp, ((memLp_extZero hD w).restrict Ω).coeFn_toLp,
      Lp.coeFn_add (((memLp_extZero hD v).restrict Ω).toLp _)
        (((memLp_extZero hD w).restrict Ω).toLp _),
      (ae_restrict_iff' hD).mp (Lp.coeFn_add v w) |> ae_restrict_of_ae] with x h1 h2 h3 h4 h5
    by_cases hx : x ∈ D <;> simp_all [extZero]
  map_smul' a v := by
    apply Lp.ext
    filter_upwards [((memLp_extZero hD (a • v)).restrict Ω).coeFn_toLp,
      ((memLp_extZero hD v).restrict Ω).coeFn_toLp,
      Lp.coeFn_smul a (((memLp_extZero hD v).restrict Ω).toLp _),
      (ae_restrict_iff' hD).mp (Lp.coeFn_smul a v) |> ae_restrict_of_ae] with x h1 h2 h3 h4
    by_cases hx : x ∈ D <;> simp_all [extZero]
  norm_map' v := by
    change ‖((memLp_extZero hD v).restrict Ω).toLp _‖ = ‖v‖
    rw [Lp.norm_toLp, extZero, eLpNorm_indicator_eq_eLpNorm_restrict hD,
      Measure.restrict_restrict hD, inter_eq_left.mpr h, Lp.norm_def]

private lemma zeroExt_ae {D Ω : Set ℂ} (hD : MeasurableSet D) (h : D ⊆ Ω) (v : L2 D) :
    (zeroExt hD h v : ℂ → ℂ) =ᵐ[volume.restrict Ω] extZero D v :=
  ((memLp_extZero hD v).restrict Ω).coeFn_toLp

section
variable {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (hΩ : IsOpen Ω)
local notation "D" n => A.map n '' Ω

private lemma isOpen_dom (hΩ : IsOpen Ω) (n : ℕ) : IsOpen (D n) := (A.map n).isOpenMap _ hΩ

private def pull (n : ℕ) (v : L2 (D n)) : L2 Ω :=
  bilipPull (A.lipschitzWith_symm n).lipschitzOnWith v

private def bzExtend (n : ℕ) : L2 (D n) →ₗᵢ[ℂ] L2 Ω :=
  zeroExt (isOpen_dom A hΩ n).measurableSet (A.subset n)

private lemma pull_ae (n : ℕ) (v : L2 (D n)) :
    (pull A n v : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => v (A.map n x) :=
  bilipPull_ae _ _

private lemma pull_norm (n : ℕ) (v : L2 (D n)) : ‖pull A n v‖ ≤ A.lip * ‖v‖ := by
  have h := eLpNorm_comp_bilip_le (Ω := Ω) (f := A.map n) (A.lipschitzWith_symm n).lipschitzOnWith (v : ℂ → ℂ)
  change eLpNorm (fun x => v (A.map n x)) _ _ ≤ _ at h
  rw [← eLpNorm_congr_ae (pull_ae A n v), ← Lp.enorm_def, ← Lp.enorm_def] at h
  simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top enorm_ne_top) h

include hΩ in
private lemma pull_gradient (n : ℕ) {v : L2 (D n)} {G : Fin 2 → L2 (D n)}
    (hG : IsWeakGradient (D n) v G) :
    ∃ g : Fin 2 → L2 Ω, IsWeakGradient Ω (pull A n v) g ∧
      ∀ i, ‖g i‖ ≤ (A.lip : ℝ) ^ 2 * (‖G 0‖ + ‖G 1‖) := by
  obtain ⟨g, hg, hga⟩ := exists_isWeakGradient_comp_bilip rfl hΩ
    (A.lipschitzWith n).lipschitzOnWith (A.lipschitzWith_symm n).lipschitzOnWith hG (pull_ae A n v)
  refine ⟨g, hg, fun i => ?_⟩
  let u := pull A n (G 0)
  let w := pull A n (G 1)
  let N := (fun x => ‖u x‖) + (fun x => ‖w x‖)
  have hb : eLpNorm (g i : ℂ → ℂ) 2 (volume.restrict Ω) ≤
      (A.lip : ENNReal) * (‖u‖ₑ + ‖w‖ₑ) := by
    calc
      _ ≤ ENNReal.ofReal (A.lip : ℝ) * eLpNorm N 2 (volume.restrict Ω) := by
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.aestronglyMeasurable _)
        filter_upwards [hga i, pull_ae A n (G 0), pull_ae A n (G 1)] with x hx hu hw
        change u x = _ at hu
        change w x = _ at hw
        rw [hx]
        simpa [N, Pi.add_apply, Real.norm_eq_abs, hu, hw, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
          using norm_chainGrad_le A n (fun j => (G j : ℂ → ℂ)) i x
      _ ≤ _ := by
        rw [ENNReal.ofReal_coe_nnreal]
        gcongr
        rw [Lp.enorm_def, Lp.enorm_def, ← eLpNorm_norm _ (Lp.aestronglyMeasurable u),
          ← eLpNorm_norm _ (Lp.aestronglyMeasurable w)]
        exact eLpNorm_add_le (by norm_num)
  have hbound : ‖g i‖ ≤ (A.lip : ℝ) * (‖u‖ + ‖w‖) := by
    rw [← Lp.enorm_def] at hb
    simpa [ENNReal.toReal_mul, ENNReal.toReal_add enorm_ne_top enorm_ne_top] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.mpr
        ⟨enorm_ne_top, enorm_ne_top⟩)) hb
  calc ‖g i‖ ≤ (A.lip : ℝ) * (‖u‖ + ‖w‖) := hbound
    _ ≤ (A.lip : ℝ) * ((A.lip : ℝ) * ‖G 0‖ + (A.lip : ℝ) * ‖G 1‖) := by
      gcongr <;> apply pull_norm
    _ = _ := by ring

private lemma off_collar_mem {n : ℕ} {x : ℂ} (hx : x ∈ Ω) (h : x ∉ A.collar n) : x ∈ D n :=
  ⟨x, hx, A.eq_self n x h⟩

lemma BallZarnescuApprox.eventually_subset_dom {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ Ω) :
    ∀ᶠ n in atTop, K ⊆ D n := by
  have hcover : K ⊆ ⋃ n, (A.collar n)ᶜ := fun x hx => by
    obtain ⟨n, hn⟩ := (A.collar_shrink x (hsub hx)).exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover _ (fun n => (A.collar_closed n).isOpen_compl) hcover
  refine eventually_atTop.mpr ⟨s.sup id, fun n hn x hx => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hiS, hxi⟩ := mem_iUnion.mp hi
  exact off_collar_mem A (hsub hx) fun h => hxi (A.collar_antitone ((Finset.le_sup hiS).trans hn) h)

lemma BallZarnescuApprox.tendsto_volume :
    Tendsto (fun n => volume (D n)) atTop (𝓝 (volume Ω)) := by
  let C := fun n => Ω \ A.collar n
  have hmono : Monotone C := fun _ _ h => diff_subset_diff_right (A.collar_antitone h)
  have hU : (⋃ n, C n) = Ω := by
    refine iUnion_subset (fun _ => diff_subset) |>.antisymm fun x hx => ?_
    obtain ⟨n, hn⟩ := (A.collar_shrink x hx).exists
    exact mem_iUnion.mpr ⟨n, hx, hn⟩
  have h := tendsto_measure_iUnion_atTop (μ := volume) hmono
  rw [hU] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun n => measure_mono fun x hx => off_collar_mem A hx.left hx.right) fun n => measure_mono (A.subset n)

/-! Strong convergence is not changed by replacing pulled-back functions by
zero extensions, since the maps are uniformly bi-Lipschitz and the collars shrink. -/
private lemma extend_tendsto {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop)
    (v : ∀ n, L2 (D (ψ n))) (U : L2 Ω)
    (hU : Tendsto (fun n => pull A (ψ n) (v n)) atTop (𝓝 U)) :
    Tendsto (fun n => bzExtend A hΩ (ψ n) (v n)) atTop (𝓝 U) := by
  let u := fun n => pull A (ψ n) (v n)
  have hb : ∀ n,
      ‖bzExtend A hΩ (ψ n) (v n) - U‖ₑ ≤
        A.lip * (‖u n - U‖ₑ + eLpNorm (fun x => U (A.map (ψ n) x) - U x) 2 (volume.restrict Ω)) +
          eLpNorm ((A.collar (ψ n)).indicator (U : ℂ → ℂ)) 2 (volume.restrict Ω) := by
    intro n
    let k := ψ n
    let d := D k
    have hd := (isOpen_dom A hΩ k).measurableSet
    let F := fun x => v n x - U x
    let H := fun x => F (A.map k x)
    rw [Lp.enorm_def]
    calc eLpNorm _ 2 (volume.restrict Ω) =
        eLpNorm (d.indicator F + dᶜ.indicator (-(U : ℂ → ℂ))) 2 (volume.restrict Ω) := by
          apply eLpNorm_congr_ae
          filter_upwards [zeroExt_ae hd (A.subset k) (v n), Lp.coeFn_sub (bzExtend A hΩ k (v n)) U]
            with x hx hy
          change ((bzExtend A hΩ k (v n) - U : L2 Ω) : ℂ → ℂ) x = _
          rw [hy]
          simp only [Pi.sub_apply]
          change bzExtend A hΩ k (v n) x = extZero d (v n) x at hx
          rw [hx]
          by_cases hm : x ∈ d <;> simp [extZero, F, hm]
      _ ≤ eLpNorm F 2 (volume.restrict d) + eLpNorm (dᶜ.indicator (-(U : ℂ → ℂ))) 2 (volume.restrict Ω) := by
        have hs : eLpNorm (d.indicator F) 2 (volume.restrict Ω) = eLpNorm F 2 (volume.restrict d) := by
          rw [eLpNorm_indicator_eq_eLpNorm_restrict (show MeasurableSet d from hd),
            Measure.restrict_restrict_of_subset (show d ⊆ Ω from A.subset k)]
        rw [← hs]
        exact eLpNorm_add_le (by norm_num)
      _ ≤ A.lip * eLpNorm H 2 (volume.restrict Ω) +
          eLpNorm ((A.collar k).indicator (U : ℂ → ℂ)) 2 (volume.restrict Ω) := by
        apply add_le_add
        · have e : (A.map k).symm '' d = Ω := (A.map k).toEquiv.symm_image_image _
          have hh := eLpNorm_comp_bilip_le (Ω := d) (f := (A.map k).symm)
            ((A.lipschitzWith k).lipschitzOnWith) H
          rwa [e, show H ∘ (A.map k).symm = F by funext x; simp [H]] at hh
        · apply eLpNorm_mono_ae ((Lp.memLp U).neg.indicator hd.compl).aestronglyMeasurable
          filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
          have hxc : x ∉ d → x ∈ A.collar k := by
            contrapose!; exact off_collar_mem A hx
          change ‖dᶜ.indicator (-(U : ℂ → ℂ)) x‖ ≤ _
          by_cases hxd : x ∈ d
          · rw [indicator_of_notMem (by simpa using hxd), norm_zero]
            exact norm_nonneg _
          · rw [indicator_of_mem hxd, indicator_of_mem (hxc hxd), Pi.neg_apply, norm_neg]
      _ ≤ _ := by
        gcongr
        have hH : H =ᵐ[volume.restrict Ω] fun x =>
            (u n - U) x - (U (A.map k x) - U x) := by
          filter_upwards [pull_ae A k (v n), Lp.coeFn_sub (u n) U] with x hx hy
          change u n x = _ at hx
          change H x = ((u n - U : L2 Ω) : ℂ → ℂ) x - _
          rw [hy, Pi.sub_apply, hx]
          dsimp [H]
          ring
        rw [eLpNorm_congr_ae hH, Lp.enorm_def]
        exact eLpNorm_sub_le (by norm_num)
  rw [tendsto_iff_enorm_sub_tendsto_zero]
  have h₁ := (tendsto_iff_enorm_sub_tendsto_zero.mp hU).add
    ((tendsto_comp_map A hΩ U).comp hψ)
  have h₂ := (tendsto_eLpNorm_indicator_collar A hΩ.measurableSet (Lp.memLp U)).comp hψ
  simp  [add_zero] at h₁
  have hlim := (ENNReal.Tendsto.const_mul (a := (A.lip : ENNReal)) h₁ (Or.inr ENNReal.coe_ne_top)).add h₂
  simp  [mul_zero, add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

end

private lemma zeroExt_integral_mul {D Ω : Set ℂ} (hD : MeasurableSet D) (h : D ⊆ Ω)
    (v : L2 D) (φ : ℂ → ℂ) :
    ∫ x in Ω, zeroExt hD h v x * φ x = ∫ x in D, v x * φ x := by
  calc
    _ = ∫ x in D, v x * φ x ∂(volume.restrict Ω) := by
      rw [← integral_indicator hD]
      apply integral_congr_ae
      filter_upwards [zeroExt_ae hD h v] with x hx
      rw [hx]
      by_cases hm : x ∈ D <;> simp [hm, extZero]
    _ = _ := by rw [Measure.restrict_restrict_of_subset h]

private lemma trial_gradients {D : Set ℂ} (hD : IsOpen D) (j : ℕ) {E : ℝ} (hE : 0 < E)
    (h : neumannEigenvalue D j < ENNReal.ofReal E) :
    ∃ (e : Fin (j + 1) → L2 D) (G : Fin (j + 1) → Fin 2 → L2 D), Orthonormal ℂ e ∧
      (∀ r, IsWeakGradient D (e r) (G r)) ∧ ∀ a : Fin (j + 1) → ℂ,
      ∑ i, ‖∑ r, a r • G r i‖ ^ 2 ≤ E * ∑ r, ‖a r‖ ^ 2 := by
  obtain ⟨e, he, hq⟩ := exists_orthonormal_lt j h
  have hqf : ∀ r, neumannEnergy D (e r) < ⊤ := fun r => by
    have ht := (hq (Pi.single r 1)).trans_lt ENNReal.ofReal_lt_top
    simpa using ht
  have hex : ∀ r, ∃ g, IsWeakGradient D (e r) g := by
    intro r
    obtain ⟨g, hg⟩ := iInf_lt_iff.mp (hqf r)
    aesop
  choose G hG using hex
  refine ⟨e, G, he, hG, fun a => ?_⟩
  have h := hq a
  rw [neumannEnergy_eq_of_isWeakGradient hD (IsWeakGradient.sum _ _ _ fun r _ => (hG r).smul (a r)),
    ← ofReal_sum_norm_sq] at h
  simpa only [Finset.sum_apply, Pi.smul_apply] using
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Only a lower semicontinuity statement is required: a common upper
bound on the approximating eigenvalues is also an upper bound on the limit. -/
theorem BallZarnescuApprox.neumannEigenvalue_le_of_eventually_lt
    {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (j : ℕ) {E : ℝ} (hE : 0 < E)
    (h : ∀ᶠ n in atTop, neumannEigenvalue (A.map n '' Ω) j < ENNReal.ofReal E) :
    neumannEigenvalue Ω j ≤ ENNReal.ofReal E := by
  classical
  let hΩ := hL.1.1
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let κ := fun n : ℕ => n + N
  let D := fun n => A.map (κ n) '' Ω
  have hκ := tendsto_add_atTop_nat N
  have hD (n : ℕ) : IsOpen (D n) := isOpen_dom A hΩ _
  choose v G hv hG hq using fun n => trial_gradients (hD n) j hE (hN (κ n) (by lia))
  let u := fun n r => pull A (κ n) (v n r)
  choose g hg hgb using fun n r => pull_gradient A hΩ (κ n) (hG n r)
  have hG_bound n r i : ‖G n r i‖ ≤ Real.sqrt E := by
    have hs := hq n (Pi.single r 1)
    have ht : ∑ k, ‖G n r k‖ ^ 2 ≤ E := by
      simpa [Pi.single_apply, apply_ite] using hs
    exact Real.le_sqrt_of_sq_le ((Finset.single_le_sum (fun k _ => sq_nonneg ‖G n r k‖)
      (Finset.mem_univ i)).trans ht)
  let C := max (A.lip : ℝ) ((A.lip : ℝ) ^ 2 * (Real.sqrt E + Real.sqrt E))
  obtain ⟨θ, hθ, hU⟩ := exists_common_subseq
    (fun r φ => ∃ U, Tendsto (fun n => u (φ n) r) atTop (𝓝 U))
    (fun _ _ _ ⟨U, hU⟩ ht => ⟨U, hU.comp ht.tendsto_atTop⟩)
    (fun r φ hφ => by
      obtain ⟨ψ, hψ, U, hU⟩ := rellich_compact hb hL (fun n => u (φ n) r)
        (fun n => g (φ n) r) (fun n => hg (φ n) r) C
        (fun n => le_trans (pull_norm A _ _) (by
          rw [(hv (φ n)).norm_eq_one r, mul_one]; exact le_max_left _ _))
        (fun n i => (hgb (φ n) r i).trans ((by gcongr <;> exact hG_bound _ _ _ :
          (A.lip : ℝ) ^ 2 * (‖G (φ n) r 0‖ + ‖G (φ n) r 1‖) ≤ _).trans (le_max_right _ _)))
      exact ⟨ψ, hψ, U, hU⟩)
  choose U hU using hU
  let ψ := κ ∘ θ
  have hψ := hκ.comp hθ.tendsto_atTop
  have hU' (r : Fin (j + 1)) :=
    extend_tendsto A hΩ hψ _ _ (hU r)
  refine neumannEigenvalue_le_of_orthonormal j U ?_ _ (fun a => ?_)
  · refine orthonormal_iff_ite.mpr fun r s => tendsto_nhds_unique ((hU' r).inner (hU' s)) ?_
    simp only [LinearIsometry.inner_map_map, fun n => orthonormal_iff_ite.mp (hv (θ n)) r s]
    exact tendsto_const_nhds
  let z n := ∑ r, a r • v (θ n) r
  let f (n : ℕ) := ∑ r, a r • G (θ n) r
  let B := E * ∑ r, ‖a r‖ ^ 2
  have hzG n : IsWeakGradient (D (θ n)) (z n) (f n) := by
    exact IsWeakGradient.sum Finset.univ _ _ fun r _ => (hG (θ n) r).smul (a r)
  have hz : Tendsto (fun n => bzExtend A hΩ (ψ n) (z n)) atTop (𝓝 (∑ r, a r • U r)) := by
    simp  [z, map_sum, map_smul]
    exact tendsto_finset_sum _ fun r _ => tendsto_const_nhds.smul (hU' r)
  let F (n : ℕ) (i : Fin 2) := bzExtend A hΩ (ψ n) (f n i)
  have hF n : ∑ i, ‖F n i‖ ^ 2 ≤ B := by
    simpa only [F, LinearIsometry.norm_map, f, Finset.sum_apply, Pi.smul_apply] using hq (θ n) a
  have hFb n i := Real.le_sqrt_of_sq_le
    ((Finset.single_le_sum (fun k _ => sq_nonneg ‖F n k‖) (Finset.mem_univ i)).trans (hF n))
  obtain ⟨η, hη, hΓ⟩ := exists_common_subseq
    (fun i φ => ∃ Y, ∀ x, Tendsto (fun n => inner ℂ x (F (φ n) i)) atTop (𝓝 (inner ℂ x Y)))
    (fun _ _ _ ⟨Y, hY⟩ ht => ⟨Y, fun x => (hY x).comp ht.tendsto_atTop⟩)
    (fun i φ _ => exists_weak_subseq (fun n => F (φ n) i) (Real.sqrt B) (fun n => hFb (φ n) i))
  choose Γ hΓ using hΓ
  have hlim : IsWeakGradient Ω (∑ r, a r • U r) Γ := by
    refine isWeakGradient_of_eventually_tendsto (fun φ hφ i => ?_) (hz.comp hη.tendsto_atTop) hΓ
    filter_upwards [(hψ.comp hη.tendsto_atTop).eventually
      (A.eventually_subset_dom hφ.2.1.isCompact hφ.2.2)] with n hn
    change ∫ x in Ω, bzExtend A hΩ (ψ (η n)) (z (η n)) x * fderiv ℝ φ x (coordDir i) =
      -∫ x in Ω, F (η n) i x * φ x
    simp  [F, bzExtend, zeroExt_integral_mul]
    exact hzG (η n) φ ⟨hφ.1, hφ.2.1, hn⟩ i
  have hbound : ∑ i, ‖Γ i‖ ^ 2 ≤ B := by
    by_contra! hB
    simp  [Fin.sum_univ_two] at hB hF
    let ε := (‖Γ 0‖ ^ 2 + ‖Γ 1‖ ^ 2 - B) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨n, h0, h1⟩ := ((weak_lsc_norm_sq (hΓ 0) ε hε).and
      (weak_lsc_norm_sq (hΓ 1) ε hε)).exists
    dsimp [ε] at h0 h1
    linarith [hF (η n)]
  rw [← ENNReal.ofReal_mul hE.le, neumannEnergy_eq_of_isWeakGradient hΩ hlim, ← ofReal_sum_norm_sq]
  gcongr

end PolyaNeumann
end
