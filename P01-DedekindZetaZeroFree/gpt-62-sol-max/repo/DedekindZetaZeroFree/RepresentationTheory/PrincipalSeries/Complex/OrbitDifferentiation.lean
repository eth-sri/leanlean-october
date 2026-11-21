module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicPropagation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace RaisingTopology
private theorem joint_spatial_jets {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
      iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) := by
  induction n with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hF
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => F (p.1, x))) p.2) := (ih.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv
        contDiff_snd (by simp)
    fun_prop

namespace SmoothQuotient
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
noncomputable def partialT (F : ℝ × E → V) (p : ℝ × E) : V :=
  fderiv ℝ (fun t => F (t,p.2)) p.1 1
lemma partialT_smooth (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (partialT F) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
      fderiv ℝ (fun t => F (t,p.2)) p.1) :=
    (hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv contDiff_fst (by simp)
  exact h.clm_apply contDiff_const
lemma partialT_deriv (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : E) :
    HasDerivAt (fun s => F (s,x)) (partialT F (t,x)) t := ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt
noncomputable def extSlope (F : ℝ × E → V) (p : ℝ × E) : V :=
  ∫ s : ℝ in 0..1, partialT F (s * p.1, p.2)
lemma extSlope_continuous (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (extSlope F) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (partialT_smooth F hF).continuous.comp
    ((continuous_snd.mul continuous_fst.fst).prodMk continuous_fst.snd)
lemma extSlope_zero (F : ℝ × E → V) (x : E) :
    extSlope F (0,x) = partialT F (0,x) := by
  simp [extSlope, intervalIntegral.integral_const]
lemma extSlope_ne (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (ht : t ≠ 0) (x : E) :
    extSlope F (t,x) = t⁻¹ • (F (t,x) - F (0,x)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (f := fun s : ℝ => F (s*t,x))
    (f' := fun s : ℝ => t • partialT F (s*t,x))
    (fun s _ => by simpa [Function.comp_def] using
      (partialT_deriv F hF (s*t) x).scomp s ((hasDerivAt_id s).mul_const t))
    (((partialT_smooth F hF).continuous.comp
      ((continuous_id.mul continuous_const).prodMk continuous_const)).const_smul t |>.intervalIntegrable 0 1)
  simp only [one_mul, zero_mul, intervalIntegral.integral_smul_const] at h
  change extSlope F (t,x) = _
  rw [← h, intervalIntegral.integral_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rfl
lemma slope_locally_uniform (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] :
    TendstoLocallyUniformlyOn (fun t x => t⁻¹ • (F (t,x) - F (0,x)))
      (fun x => partialT F (0,x)) (𝓝[≠] (0:ℝ)) Set.univ := by
  let G : ℝ → C(E,V) := fun t => ⟨fun x => extSlope F (t,x),
    (extSlope_continuous F hF).comp (continuous_const.prodMk continuous_id)⟩
  have hG : Continuous G := ContinuousMap.continuous_of_continuous_uncurry G
    (extSlope_continuous F hF)
  have h : TendstoLocallyUniformlyOn (fun t x => (G t) x) (G 0) (𝓝[≠] (0:ℝ)) Set.univ :=
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      ((hG.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)).tendstoLocallyUniformlyOn
  have heq : (fun t x => (G t) x) =ᶠ[𝓝[≠] (0:ℝ)]
      (fun t x => t⁻¹ • (F (t,x) - F (0,x))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    funext x
    exact extSlope_ne F hF t ht x
  have h' := h.congr_inseparable (heq.mono (fun t ht x _ => Inseparable.of_eq (congrFun ht x)))
  simpa only [G, ContinuousMap.coe_mk, extSlope_zero] using h'
lemma slice_smooth (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => F (t,x)) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

lemma jets_partialT (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => partialT F (0,x)) =
      (fun x => partialT (fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) (0,x)) := by
  induction n with
  | zero =>
    funext x
    let L := (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hd := L.hasFDerivAt.comp_hasDerivAt 0 (partialT_deriv F hF 0 x)
    simpa [L, partialT, iteratedFDeriv_zero_eq_comp, Function.comp_def] using hd.deriv.symm
  | succ n ih =>
    let J : ℝ × E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V :=
      fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    have hJ := joint_spatial_jets F hF n
    let K : ℝ × E → E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V :=
      fun p => fderiv ℝ (fun x => J (p.1,x)) p.2
    have hK : ContDiff ℝ (⊤ : ℕ∞) K :=
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv contDiff_snd (by simp)
    have hlimK := slope_locally_uniform K hK
    have hlimJ := slope_locally_uniform J hJ
    have hd (x : E) : HasFDerivAt (fun x => partialT J (0,x)) (partialT K (0,x)) x := by
      apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hlimK
        (fun t x _ => ?_) (fun x _ => hlimJ.tendsto_at (Set.mem_univ x)) (Set.mem_univ x)
      exact (((slice_smooth J hJ t).differentiable (by simp) x).hasFDerivAt.sub
        ((slice_smooth J hJ 0).differentiable (by simp) x).hasFDerivAt).const_smul t⁻¹
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm
      (fderiv ℝ (fun x => partialT J (0,x)) x) = _
    rw [(hd x).fderiv]
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have ht := L.hasFDerivAt.comp_hasDerivAt 0 (partialT_deriv K hK 0 x)
    change L (partialT K (0,x)) = deriv (fun t => L (K (t,x))) 0
    exact ht.deriv.symm
lemma quotient_jets_uniform (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] (n : ℕ) (S : Set E) (hS : IsCompact S) :
    TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ n
      (fun x => t⁻¹ • (F (t,x) - F (0,x))) x)
      (iteratedFDeriv ℝ n (fun x => partialT F (0,x))) (𝓝[≠] (0:ℝ)) S := by
  have h := slope_locally_uniform (fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2)
    (joint_spatial_jets F hF n)
  rw [jets_partialT F hF n]
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
  apply (h.mono (Set.subset_univ S)).congr
  intro t x _
  dsimp only
  symm
  rw [iteratedFDeriv_const_smul_apply' (((slice_smooth F hF t).sub
    (slice_smooth F hF 0)).of_le (by simp)).contDiffAt,
    fun_iteratedFDeriv_sub_apply ((slice_smooth F hF t).of_le (by simp)).contDiffAt
      ((slice_smooth F hF 0).of_le (by simp)).contDiffAt]

lemma sup_jet_error_tendsto (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] (n : ℕ) (S : Set E) (hS : IsCompact S) (hne : S.Nonempty) :
    Tendsto (fun t => sSup ((fun x => ‖iteratedFDeriv ℝ n
      (fun x => t⁻¹ • (F (t,x) - F (0,x)) - partialT F (0,x)) x‖) '' S))
      (𝓝[≠] (0:ℝ)) (𝓝 (0:ℝ)) := by
  let Q := fun t x => t⁻¹ • (F (t,x) - F (0,x))
  let P := fun x => partialT F (0,x)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := slice_smooth (partialT F) (partialT_smooth F hF) 0
  have hQ (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Q t) :=
    ((slice_smooth F hF t).sub (slice_smooth F hF 0)).const_smul _
  have hj := quotient_jets_uniform F hF n S hS
  have heq (t : ℝ) (x : E) : iteratedFDeriv ℝ n (fun x => Q t x - P x) x =
      iteratedFDeriv ℝ n (Q t) x - iteratedFDeriv ℝ n P x :=
    iteratedFDeriv_sub_apply ((hQ t).of_le (by simp)).contDiffAt
      (hP.of_le (by simp)).contDiffAt
  have hb (t : ℝ) : BddAbove ((fun x => ‖iteratedFDeriv ℝ n (fun x => Q t x - P x) x‖) '' S) :=
    (hS.image (((hQ t).sub hP).continuous_iteratedFDeriv (by simp)).norm).bddAbove
  apply tendsto_order.2
  constructor
  · intro a ha
    apply Filter.Eventually.of_forall
    intro t
    apply lt_of_lt_of_le ha
    obtain ⟨x,hx⟩ := hne
    exact le_trans (norm_nonneg _) (le_csSup (hb t) ⟨x,hx,rfl⟩)
  · intro b hb'
    have hε : 0 < b / 2 := by linarith
    have hu := (Metric.tendstoUniformlyOn_iff.mp hj) (b / 2) hε
    filter_upwards [hu] with t ht
    apply lt_of_le_of_lt (csSup_le (hne.image _) ?_) (by linarith : b/2 < b)
    rintro _ ⟨x,hx,rfl⟩
    change ‖iteratedFDeriv ℝ n (fun x => Q t x - P x) x‖ ≤ b / 2
    rw [heq]
    exact le_of_lt (by simpa [dist_eq_norm, norm_sub_rev, Q, P] using ht x hx)
end SmoothQuotient
end RaisingTopology

end DedekindZetaZeroFree.KPCplxHarmonicPropagation

section

namespace DedekindZetaZeroFree.KPCplxLoweringOrbitDifferentiation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxHarmonicPropagation.RaisingTopology
open scoped Topology Matrix.Norms.Elementwise

private lemma matrixFunction_coe (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  unfold matrixFunction
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Units.ext
  rfl

lemma contDiff_upperUnipotent :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => (upperUnipotent x : Matrix (Fin 2) (Fin 2) ℂ)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => !![1, x; 0, 1])
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | exact contDiff_const | exact contDiff_id

lemma contDiff_weyl_upperUnipotent :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℂ => (weyl * upperUnipotent x : Matrix (Fin 2) (Fin 2) ℂ)) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : ℂ => (weyl : Matrix (Fin 2) (Fin 2) ℂ) *
      (upperUnipotent x : Matrix (Fin 2) (Fin 2) ℂ))
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro l _
  exact contDiff_const.mul (contDiff_pi.mp (contDiff_pi.mp contDiff_upperUnipotent l) j)

lemma contDiff_lowerUnipotent :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => (lowerUnipotent x : Matrix (Fin 2) (Fin 2) ℂ)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => !![1, 0; x, 1])
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | exact contDiff_const | exact contDiff_id

lemma smoothOrbit_curve (s : ℝ) (f : PrincipalSeries s)
    (q : ℂ → ComplexGL2)
    (hq : ContDiff ℝ (⊤ : ℕ∞) (fun x => (q x : Matrix (Fin 2) (Fin 2) ℂ)))
    (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ => f (q p.2 * γ p.1)) := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℂ => (q p.2 * γ p.1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ =>
      (q p.2 : Matrix (Fin 2) (Fin 2) ℂ) * (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    apply ContDiff.sum
    intro l _
    exact (contDiff_pi.mp (contDiff_pi.mp (hq.comp contDiff_snd) i) l).mul
      (contDiff_pi.mp (contDiff_pi.mp (hγ.comp contDiff_fst) l) j)
  have h := hf.comp_contDiff hm (fun p => by
    change (q p.2 * γ p.1 : ComplexGL2).val.det ≠ 0
    exact (Matrix.GeneralLinearGroup.det (q p.2 * γ p.1)).ne_zero)
  simpa only [Function.comp_def, ← Matrix.GeneralLinearGroup.coe_mul, matrixFunction_coe] using h

noncomputable def orbitDerivativeSection (s : ℝ) (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (f : PrincipalSeries s) : PrincipalSeries s :=
  ⟨fun g => deriv (fun t : ℝ => f (g * γ t)) 0, by
    refine ⟨?_, ?_, ?_⟩
    · intro a d b g
      show deriv (fun t : ℝ => f (upperTriangular a d b * g * γ t)) 0 =
        (inductionWeight s a d : ℂ) * deriv (fun t : ℝ => f (g * γ t)) 0
      have hfun : (fun t : ℝ => f (upperTriangular a d b * g * γ t)) =
          (fun t : ℝ => (inductionWeight s a d : ℂ) * f (g * γ t)) := by
        funext t
        rw [mul_assoc]
        exact f.property.1 a d b (g * γ t)
      rw [hfun, deriv_const_mul_field]
    · have hs := smoothOrbit_curve s f (fun x => weyl * upperUnipotent x)
        contDiff_weyl_upperUnipotent γ hγ
      have hd := SmoothQuotient.slice_smooth
        (SmoothQuotient.partialT (fun p : ℝ × ℂ => f ((weyl * upperUnipotent p.2) * γ p.1)))
        (SmoothQuotient.partialT_smooth _ hs) 0
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℂ => deriv (fun t : ℝ => f ((weyl * upperUnipotent x) * γ t)) 0)
      simpa only [SmoothQuotient.partialT, fderiv_apply_one_eq_deriv] using hd
    · have hs := smoothOrbit_curve s f lowerUnipotent contDiff_lowerUnipotent γ hγ
      have hd := SmoothQuotient.slice_smooth
        (SmoothQuotient.partialT (fun p : ℝ × ℂ => f (lowerUnipotent p.2 * γ p.1)))
        (SmoothQuotient.partialT_smooth _ hs) 0
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℂ => deriv (fun t : ℝ => f (lowerUnipotent x * γ t)) 0)
      simpa only [SmoothQuotient.partialT, fderiv_apply_one_eq_deriv] using hd⟩

private lemma contDiff_orbit_scalar (s : ℝ) (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (f : PrincipalSeries s) (g : ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (g * γ t)) := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (g * γ t : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (γ t : Matrix (Fin 2) (Fin 2) ℂ))
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    apply ContDiff.sum
    intro l _
    exact contDiff_const.mul (contDiff_pi.mp (contDiff_pi.mp hγ l) j)
  have h := hf.comp_contDiff hm (fun t => by
    change (g * γ t : ComplexGL2).val.det ≠ 0
    exact (Matrix.GeneralLinearGroup.det (g * γ t)).ne_zero)
  simpa only [Function.comp_def, ← Matrix.GeneralLinearGroup.coe_mul, matrixFunction_coe] using h

private lemma orbitDerivativeSection_hasDerivAt (s : ℝ) (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (f : PrincipalSeries s) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => f (g * γ t)) (orbitDerivativeSection s γ hγ f g) 0 :=
  (contDiff_orbit_scalar s γ hγ f g).differentiable (by simp) 0 |>.hasDerivAt

set_option maxHeartbeats 1500000 in
theorem orbit_quotient_seminorm_tendsto (s : ℝ) (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (hzero : γ 0 = 1) (u D : PrincipalSeries s)
    (hd : ∀ g : ComplexGL2, HasDerivAt (fun t : ℝ => u (g * γ t)) (D g) 0) (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => chartSeminorm s n ((t : ℂ)⁻¹ • (rightTranslate s (γ t) u - u) - D))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let F : ℝ × ℂ → ℂ := fun p => u (weyl * upperUnipotent p.2 * γ p.1)
  let H : ℝ × ℂ → ℂ := fun p => u (lowerUnipotent p.2 * γ p.1)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    smoothOrbit_curve s u (fun x => weyl * upperUnipotent x) contDiff_weyl_upperUnipotent γ hγ
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    smoothOrbit_curve s u lowerUnipotent contDiff_lowerUnipotent γ hγ
  have hPF : (fun x => SmoothQuotient.partialT F (0, x)) = openCoordinate D := by
    funext x
    exact (SmoothQuotient.partialT_deriv F hF 0 x).unique (hd (weyl * upperUnipotent x))
  have hPH : (fun x => SmoothQuotient.partialT H (0, x)) = infinityCoordinate D := by
    funext x
    exact (SmoothQuotient.partialT_deriv H hH 0 x).unique (hd (lowerUnipotent x))
  have hzero' : ∀ x, F (0, x) = openCoordinate u x ∧ H (0, x) = infinityCoordinate u x := by
    intro x
    simp [F, H, hzero, openCoordinate, infinityCoordinate]
  have hS : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : ℂ) 1).Nonempty := ⟨0, by simp⟩
  have hf := SmoothQuotient.sup_jet_error_tendsto F hF n _ hS hne
  have hh := SmoothQuotient.sup_jet_error_tendsto H hH n _ hS hne
  simp only [show ∀ x, SmoothQuotient.partialT F (0, x) = openCoordinate D x
    from fun x => congrFun hPF x] at hf
  simp only [show ∀ x, SmoothQuotient.partialT H (0, x) = infinityCoordinate D x
    from fun x => congrFun hPH x] at hh
  have heF (t : ℝ) :
      openCoordinate ((t : ℂ)⁻¹ • (rightTranslate s (γ t) u - u) - D) =
      fun x => t⁻¹ • (F (t, x) - F (0, x)) - openCoordinate D x := by
    funext x
    simp only [openCoordinate, Submodule.coe_sub, Submodule.coe_smul_of_tower, Pi.sub_apply,
      Pi.smul_apply]
    rw [(hzero' x).1]
    simp [F, rightTranslate, openCoordinate, Complex.real_smul, Complex.ofReal_inv]
  have heH (t : ℝ) :
      infinityCoordinate ((t : ℂ)⁻¹ • (rightTranslate s (γ t) u - u) - D) =
      fun x => t⁻¹ • (H (t, x) - H (0, x)) - infinityCoordinate D x := by
    funext x
    simp only [infinityCoordinate, Submodule.coe_sub, Submodule.coe_smul_of_tower, Pi.sub_apply,
      Pi.smul_apply]
    rw [(hzero' x).2]
    simp [H, rightTranslate, infinityCoordinate, Complex.real_smul, Complex.ofReal_inv]
  change Filter.Tendsto (fun t => max (sSup ((fun x => ‖iteratedFDeriv ℝ n (openCoordinate _) x‖)
    '' Metric.closedBall (0 : ℂ) 1)) (sSup ((fun x => ‖iteratedFDeriv ℝ n (infinityCoordinate _) x‖)
    '' Metric.closedBall (0 : ℂ) 1))) _ _
  simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, heF, heH]
  convert hf.max hh using 1 <;> simp

theorem orbit_quotient_tendsto (s : ℝ) (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (hzero : γ 0 = 1) (u D : PrincipalSeries s)
    (hd : ∀ g : ComplexGL2, HasDerivAt (fun t : ℝ => u (g * γ t)) (D g) 0) :
    Filter.Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (rightTranslate s (γ t) u - u))
      (𝓝[≠] (0 : ℝ)) (𝓝 D) := by
  rw [(show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).tendsto_nhds]
  intro n ε hε
  exact (tendsto_order.mp (orbit_quotient_seminorm_tendsto s γ hγ hzero u D hd n)).2 ε hε

theorem smooth_matrix_orbit_derivative (s : ℝ) (γ : ℝ → ComplexGL2)
    (hγ : ContDiff ℝ (⊤ : ℕ∞)
      (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)))
    (hzero : γ 0 = 1) (f : PrincipalSeries s) :
    ∃ D : PrincipalSeries s,
      Filter.Tendsto
        (fun t : ℝ => (t : ℂ)⁻¹ • (rightTranslate s (γ t) f - f))
        (𝓝[≠] (0 : ℝ)) (𝓝 D) ∧
      ∀ g : ComplexGL2,
        HasDerivAt (fun t : ℝ => f (g * γ t)) (D g) 0 := by
  refine ⟨orbitDerivativeSection s γ hγ f, ?_, ?_⟩
  · exact orbit_quotient_tendsto s γ hγ hzero f (orbitDerivativeSection s γ hγ f)
      (orbitDerivativeSection_hasDerivAt s γ hγ f)
  · exact orbitDerivativeSection_hasDerivAt s γ hγ f

end DedekindZetaZeroFree.KPCplxLoweringOrbitDifferentiation

end
