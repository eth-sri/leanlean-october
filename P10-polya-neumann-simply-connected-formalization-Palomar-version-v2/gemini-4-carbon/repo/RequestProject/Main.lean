module

public import RequestProject.Poincare
public import RequestProject.Finite
public import RequestProject.Transport
public import RequestProject.Unitarity
public import RequestProject.CurveContinuity
public import RequestProject.Area
public import RequestProject.Driven
public import RequestProject.Phase
public import RequestProject.Transmutation
public import RequestProject.CutCorrection
public import RequestProject.Reparam
public import RequestProject.Observation
public import RequestProject.BasePoint
public import RequestProject.PeriodicForm
public import RequestProject.Coercivity
public import RequestProject.FiniteRankCompletion
public import RequestProject.RankBound
public import RequestProject.Approximation
public import RequestProject.ArcLength
public import RequestProject.NeumannEigenspace
public import RequestProject.MonodromyCompact
public import RequestProject.PhaseCount
public import RequestProject.PhaseInduction
public import RequestProject.TraceBound
public import RequestProject.SmallEnergy
public import RequestProject.CutTrace
public import RequestProject.ExteriorConnected
public import RequestProject.Pullback
public import RequestProject.FixedSpace
public import RequestProject.HerglotzForm
public import RequestProject.BoundaryConnected
public import RequestProject.BallZarnescu
public import RequestProject.Reconstruction
public import RequestProject.HerglotzAdmissible
public import RequestProject.NeumannMultiplicity
public import RequestProject.RiemannMappingSmoothCollar
public import RequestProject.LocalConformalHerglotzBoundaryTransfer

@[expose] public section

open scoped Real ComplexConjugate
open MeasureTheory Filter Topology Set Metric

noncomputable section

namespace PolyaNeumann

private lemma eig_ne_top {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (j : ℕ) :
    neumannEigenvalue Ω j ≠ ⊤ :=
  (neumannEigenvalue_lt_top_of_isOpen hL.1.1 hL.1.2.nonempty j).ne

private theorem exists_boundaryParam {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ γ : ℝ → ℂ, IsBoundaryParam Ω γ := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him⟩ := exists_jordanParam_of_isPreconnected_frontier hb hL
    (isPreconnected_frontier_of_simplyConnected hb hL hsc)
  obtain ⟨σ, hσ, hin, hout⟩ := windingNumber_pm_one_of_jordan hb hL hK hper hinj him
    (isConnected_compl_closure_of_frontier hb hL
      (him ▸ isPreconnected_Icc.image γ hK.continuous.continuousOn))
  have harea : |∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ θ| = 2 * (volume Ω).toReal := by
    rw [integral_signedAreaDensity_of_winding hL.1.1 hb hK him σ hin hout, abs_mul, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg]
    rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨γ1, ⟨K1, hK1⟩, hper1, hinj1, him1, hc, harea1, -⟩ :=
    exists_constSpeed_reparam hK hper hinj
  rcases (abs_eq (by positivity)).mp harea with hpos | hneg
  · exact ⟨γ1, ⟨⟨K1, hK1⟩, hper1, hinj1, him1.trans him, hc,
      show ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ1 θ = _ from harea1.trans hpos⟩⟩
  · obtain ⟨c, hc0, hspeed⟩ := hc
    obtain ⟨γ2, hK2, hper2, hinj2, him2, hspeed2, harea2⟩ :=
      exists_reverse_param hK1 hper1 hinj1 hspeed
    exact ⟨γ2, ⟨⟨K1, hK2⟩, hper2, hinj2, him2.trans (him1.trans him), ⟨c, hc0, hspeed2⟩,
      show ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ2 θ = _ by
        rw [harea2, harea1, hneg, neg_neg]⟩⟩

private theorem monodromy_ne_one {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (hW : IsTransport γ E W) : monodromy W ≠ 1 := by
  intro h
  obtain ⟨T, hT⟩ := fixedSpace_to_neumannEigenspace_of_reconstruction hγ hE hW
    (neumann_reconstruction_of_compatible hb hL hγ hE)
  haveI := finiteDimensional_neumannEigenspace hb hL E
  have hV : W (2 * π) = 1 := by
    have h2 := congrArg ContinuousLinearMap.adjoint h
    rw [monodromy, ContinuousLinearMap.adjoint_adjoint] at h2
    rw [h2, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  have htop : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) = ⊤ := by
    rw [hV, sub_self]; exact LinearMap.ker_zero
  haveI : FiniteDimensional ℂ Ell2 := by
    haveI := Module.Finite.of_injective T hT
    rw [htop] at this
    exact LinearEquiv.finiteDimensional Submodule.topEquiv
  have horth : Orthonormal ℂ basisVec := orthonormal_iff_ite.mpr fun i j => by
    by_cases hij : i = j <;> simp [basisVec, lp.inner_single_left, lp.single_apply, hij]
  haveI := horth.linearIndependent.finite
  exact _root_.not_finite ℕ

private lemma count_lhs_eq_ofReal {Ω : Set ℂ} (hvol : volume Ω ≠ ⊤) {E : ℝ} (hE : 0 ≤ E)
    (U : Ell2 →L[ℂ] Ell2) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖U - 1‖ / (2 * π)) =
      ENNReal.ofReal ((volume Ω).toReal * E / (4 * π) + ‖U - 1‖ / (2 * π)) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol]

private theorem uniform_cayley_rank_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E₀ : ℝ) (hE₀ : 0 < E₀) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = m) :
    ∃ A a : ℝ, 0 < a ∧ ∀ E, 0 < E → |E - E₀| < a →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      CayleyRankBound (monodromyAt γ E) A m := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  choose Ws hWs using fun E => transport_exists_of_lipschitz γ hKγ E
  have hU : monodromy (Ws E₀) ≠ 1 :=
    monodromy_ne_one hb hS.isLipschitzDomain hγ E₀ hE₀ (Ws E₀) (hWs E₀)
  obtain ⟨t, ht, hcut⟩ : ∃ t ∈ Icc 0 (2 * π),
      ∀ Wt, IsTransport (fun θ => γ (θ + t)) E₀ Wt → cutC (Wt (2 * π)) (basisVec 0) ≠ 0 := by
    obtain ⟨c₀, hc₀, hspeed⟩ := hγ.const_speed
    have hγ' : ∀ᵐ θ, deriv γ θ ≠ 0 :=
      hspeed.mono fun θ hθ h0 => hc₀.ne (by simpa [h0] using hθ)
    have hV : Ws E₀ (2 * π) ≠ 1 := fun h1 =>
      hU (by simp [monodromy, h1, ← ContinuousLinearMap.star_eq_adjoint])
    obtain ⟨t, ht, hct⟩ : ∃ t ∈ Icc 0 (2 * π),
        cutC (Ws E₀ t * Ws E₀ (2 * π) * ContinuousLinearMap.adjoint (Ws E₀ t)) (basisVec 0) ≠ 0 := by
      by_contra hall
      push_neg at hall
      refine hV (ContinuousLinearMap.ext fun v => sub_eq_zero.mp ?_)
      refine observation_injective hKγ hγ' hE₀ (hWs E₀) (Ws E₀ (2 * π) v - v) fun θ hθ => ?_
      have hu := (Unitary.mem_iff.mp (transport_mem_unitary hKγ (hWs E₀) hθ)).1
      rw [ContinuousLinearMap.star_eq_adjoint] at hu
      have hfix : ContinuousLinearMap.adjoint (Ws E₀ (2 * π))
          (ContinuousLinearMap.adjoint (Ws E₀ θ) (basisVec 0)) =
          ContinuousLinearMap.adjoint (Ws E₀ θ) (basisVec 0) := by
        have h2 := congrArg (ContinuousLinearMap.adjoint (Ws E₀ θ)) (sub_eq_zero.mp (hall θ hθ))
        simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
          ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at h2
        have h3 : ∀ x, ContinuousLinearMap.adjoint (Ws E₀ θ) (Ws E₀ θ x) = x := fun x => by
          simpa using congrArg (fun T : Ell2 →L[ℂ] Ell2 => T x) hu
        rwa [h3] at h2
      rw [← ContinuousLinearMap.adjoint_inner_left, inner_sub_right,
        ← ContinuousLinearMap.adjoint_inner_left, hfix, sub_self]
    exact ⟨t, ht, fun Wt hWt => (transport_basepoint hKγ hγ.periodic (hWs E₀) ht hWt).symm ▸ hct⟩
  let γt : ℝ → ℂ := fun θ => γ (θ + t)
  have hγt : IsBoundaryParam Ω γt := hγ.shift t
  obtain ⟨R, C, K, F, e, c, τ, L, hR, hFs, hhol, hinj, himage, hC, hK, he, hsource, hes,
    hτ, hcoord, hΓLip⟩ := exists_synced_smoothConformal_coordinates hb hS hsc hγt
  let Γ : ℝ → ℂ := physicalCircleTrace F
  choose WΓ hWΓ using fun E => transport_exists_of_lipschitz Γ hΓLip E
  obtain ⟨Kγt, hKγt⟩ := hγt.lipschitz
  obtain ⟨Wt, hWt⟩ := transport_exists_of_lipschitz γt hKγt E₀
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  have hWΓcomp : IsTransport (γt ∘ τ) E₀ (WΓ E₀) := (funext hcoord : Γ = γt ∘ τ) ▸ hWΓ E₀
  have hmono : monodromy (WΓ E₀) = monodromy Wt :=
    monodromy_comp hKγt hτ.monotone hKτ hτ.zero hτ.endpoint hWt hWΓcomp
  have hcutΓ : cutC (WΓ E₀ (2 * π)) (basisVec 0) ≠ 0 := by
    change monodromy (WΓ E₀) (basisVec 0) - basisVec 0 ≠ 0
    rw [hmono]
    exact hcut Wt hWt
  have hmult : originalNeumannMultiplicity (F '' ball (0 : ℂ) 1) E₀ = m := by
    simp [originalNeumannMultiplicity, himage, hm]
  subst hmult
  have hbF : Bornology.IsBounded (F '' ball (0 : ℂ) 1) := himage.symm ▸ hb
  have hLF : IsLipschitzDomain (F '' ball (0 : ℂ) 1) := himage.symm ▸ hS.isLipschitzDomain
  have hγtF : IsBoundaryParam (F '' ball (0 : ℂ) 1) γt := himage.symm ▸ hγt
  obtain ⟨A, δ, -, hδ, hbound⟩ :=
    exists_localConformal_herglotz_bound hR F hFs hbF hLF hhol hinj hC hK
      e he hsource hes hγtF hτ hcoord hΓLip WΓ hWΓ hE₀ hcutΓ
  refine ⟨A, δ, hδ, fun E hE hEδ hnr => ?_⟩
  obtain ⟨W', hW'⟩ := transport_exists_of_lipschitz γt hKγt E
  obtain ⟨L', hL'⟩ := hbound E hE hEδ (himage.symm ▸ hnr) W' hW'
  rw [monodromyAt_eq hKγ (hWs E)]
  have hshift := cayleyRankBound_of_herglotzForm_bound hKγt (by simpa using hγt.periodic 0)
    hW' A A le_rfl L' hL'
  intro n v s hv hs hEig hAs
  have hu : Ws E t ∈ unitary (Ell2 →L[ℂ] Ell2) := transport_mem_unitary hKγ (hWs E) ht
  let eu : Ell2 ≃ₗᵢ[ℂ] Ell2 := Unitary.linearIsometryEquiv ⟨Ws E t, hu⟩
  refine hshift n (fun k => eu (v k)) s (hv.comp_linearIsometryEquiv eu) hs (fun k => ?_) hAs
  have hWW : ContinuousLinearMap.adjoint (Ws E t) (Ws E t (v k)) = v k := by
    simpa [ContinuousLinearMap.star_eq_adjoint] using
      congrArg (fun T : Ell2 →L[ℂ] Ell2 => T (v k)) (Unitary.mem_iff.mp hu).1
  change monodromy W' (Ws E t (v k)) = Complex.exp (s k * Complex.I) • Ws E t (v k)
  rw [monodromy_basepoint hKγ hγ.periodic (hWs E) ht hW', ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, hWW, hEig k, map_smul]

private theorem cutPhaseCount_const {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ) (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseCount Ω γ ε E₂ = cutPhaseCount Ω γ ε E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have h := cutPhaseSum_monodromyAt_sub' hK hclosed hε0 hε E₁ E₂ h1 h12 hcut
  rw [integral_areaDensity_eq hK hclosed] at h
  erw [hγ.area] at h
  unfold cutPhaseCount
  rw [div_left_inj' (by positivity)]
  linarith

private theorem phase_summable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    Summable (phaseTerm (monodromyAt γ E)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  have hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E}.encard = ((0 : ℕ) : ℕ∞) := by
    rw [Nat.cast_zero, Set.encard_eq_zero]
    exact Set.eq_empty_of_forall_notMem fun i hi => hnr i hi
  obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E hE 0 hm
  have hcot : ∀ t : ℝ, 0 < t → t < 2 * π → ∀ v : Ell2, v ≠ 0 →
      monodromy W v = Complex.exp (t * Complex.I) • v → Real.cot (t / 2) ≤ A := by
    rw [← monodromyAt_eq hK hW]
    exact fun t ht0 ht v hv => (hA E hE (by simpa using ha) hnr).cot_le ht0 ht hv
  have hU := monodromy_mem_unitary' hK hW
  have hsum := summable_eigenMult_monodromy hK hclosed hE.le hW
  rw [monodromyAt_eq hK hW]
  exact summable_phaseTerm_of_upper_finite hU
    (upper_eigen_finite_of_cot_bound hU
      (isCompactOperator_monodromy_sub_one hK hclosed hE.le hW) hsum A hcot) hsum

private theorem phaseCount_initial_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → phaseCount Ω γ E ≤ 1 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨Cq, hCq0, hT⟩ := exists_linear_traceBound_monodromyAt hK hclosed
  obtain ⟨δr, hδr, hrank⟩ : ∃ δr > 0, ∀ E, 0 < E → E < δr →
      CayleyRankBound (monodromyAt γ E) 0 1 := by
    have hL := hS.isLipschitzDomain
    obtain ⟨z₁, hz₁⟩ := hL.1.2.nonempty
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hL.1.1 z₁ hz₁
    have hΩpos : 0 < (volume Ω).toReal := ENNReal.toReal_pos
      (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
    obtain ⟨δ₁, hδ₁, h₁⟩ := small_energy_imForm_basisVec_neg hb hL hγ
    obtain ⟨δ₅, hδ₅, h₅⟩ := herglotz_imSchur_nonneg hb hL hγ hr hball
    obtain ⟨δa, hδa, hadm⟩ := exists_admissible_herglotzVec hb hΩpos (γ 0) z₁
    refine ⟨min δ₁ (min δ₅ (δa ^ 2)), lt_min hδ₁ (lt_min hδ₅ (by positivity)), fun E hE hEδ => ?_⟩
    obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
    have hneg := h₁ E hE (hEδ.trans_le (min_le_left _ _)) W hW
    have hk : |Real.sqrt E| < δa := by
      rw [abs_of_nonneg (Real.sqrt_nonneg E), ← Real.sqrt_sq hδa.le]
      exact Real.sqrt_lt_sqrt hE.le (hEδ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hnonneg : ∀ v : Ell2, imPair (monodromy W) (basisVec 0) v = 0 →
        0 ≤ imForm (monodromy W) v :=
      nonneg_of_imSchur_nonneg (monodromy W) dense_finSupp (fun w _ => by
        obtain ⟨t, a, ha, hvec, hng, hmean⟩ := hadm (Real.sqrt E) hk w
        have ht := h₅ E hE (hEδ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
          W hW a ha hng hmean
        rwa [hvec, imSchur_add_smul _ hneg.ne] at ht)
    let ℓ : Ell2 →ₗ[ℂ] ℂ :=
      { toFun := fun v => imPair (monodromy W) (basisVec 0) v
        map_add' := imPair_add_right (monodromy W) _
        map_smul' := fun c v => imPair_smul_right (monodromy W) _ v c }
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (ℓ.comp (herglotzVecLin (Real.sqrt E) (γ 0)))
    rw [monodromyAt_eq hK hW]
    refine cayleyRankBound_of_herglotzForm_bound hK hclosed hW 0 0 le_rfl
      (LinearMap.pi fun _ => g) fun a ha hLa => ?_
    have hga : g a = imPair (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) := by
      simpa [ℓ, herglotzVecLin] using congrArg (fun F => F ⟨a, ha⟩) hg
    have h0 : g a = 0 := congrFun hLa 0
    simpa [herglotzForm_eq_im hK hclosed hW ha, imForm] using
      hnonneg (herglotzVec ha (Real.sqrt E) (γ 0)) (by rw [← hga, h0])
  set v := (volume Ω).toReal
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hS.1.1.measure_pos volume hS.1.2.nonempty).ne' hb.measure_lt_top.ne
  have hpi := Real.pi_pos
  set δ := min δr (1 / (Cq + 1))
  have hδpos : 0 < δ := lt_min hδr (by positivity)
  have hcut : ∀ E, 0 < E → E < δ →
      Complex.exp (π * Complex.I) ∉ spectrum ℂ (monodromyAt γ E) := by
    intro E hE hEδ hmem
    rw [Complex.exp_pi_mul_I] at hmem
    obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) hmem (by norm_num)
    have h1 : E < 1 / (Cq + 1) := hEδ.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    exact not_eigen_neg_one_of_traceBound (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
      (by nlinarith) hw0 hw
  set c := (v / 2 + π / 2 * Cq) / (2 * π) with hc
  have hJb : ∀ E, 0 < E → E < δ → |cutPhaseCount Ω γ π E| ≤ c * E := by
    intro E hE _
    obtain ⟨-, hP⟩ := cutPhaseSum_pi_bound (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
    rw [cutPhaseCount, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      div_le_iff₀ (by positivity)]
    have := abs_sub (v * E / 2) (cutPhaseSum π (monodromyAt γ E))
    rw [abs_of_pos (by positivity : (0 : ℝ) < v * E / 2)] at this
    calc |v * E / 2 - cutPhaseSum π (monodromyAt γ E)| ≤ v * E / 2 + π / 2 * (Cq * E) := by linarith
      _ = c * E * (2 * π) := by rw [hc]; field_simp
  have hJ0 : ∀ E, 0 < E → E < δ → cutPhaseCount Ω γ π E = 0 := by
    intro E hE hEδ
    have hev : ∀ᶠ F in 𝓝[>] (0 : ℝ), |cutPhaseCount Ω γ π E| ≤ c * F := by
      filter_upwards [Ioo_mem_nhdsGT hE] with F hF
      rw [cutPhaseCount_const hγ hpi (by linarith) F E hF.1 hF.2.le
        (fun G hG => hcut G (hF.1.trans_le hG.1) (hG.2.trans_lt hEδ))]
      exact hJb F hF.1 (hF.2.trans hEδ)
    have hlim : Tendsto (fun F => c * F) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_id.const_mul c : Tendsto (fun F : ℝ => c * F) (𝓝 0) _).mono_left
        nhdsWithin_le_nhds
    exact abs_nonpos_iff.mp (ge_of_tendsto hlim hev)
  refine ⟨δ, hδpos, fun E hE hEδ => ?_⟩
  set U := monodromyAt γ E with hUdef
  have hUu : U ∈ unitary (Ell2 →L[ℂ] Ell2) := monodromyAt_mem_unitary hK E
  have hUc : IsCompactOperator ⇑(U - 1) := isCompactOperator_monodromyAt_sub_one hK hclosed hE.le
  obtain ⟨hsa, hle⟩ := arcCount_le (ε := π) (A := 0) hUu hUc (by linarith)
    (fun t ht0 htπ => div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)) |>.trans_eq
      (Real.cot_eq_cos_div_sin _).symm)
    (hrank E hE (hEδ.trans_le (min_le_left _ _)))
  obtain ⟨hcs, -⟩ := cutPhaseSum_pi_bound hUu hUc (hT E hE.le)
  have hps : Summable (phaseTerm U) := by
    have : phaseTerm U = fun z => cutPhaseTerm π U z - 2 * π * arcTerm π U z := by
      funext z; rw [cutPhaseTerm_eq]; ring
    exact this ▸ hcs.sub (hsa.mul_left _)
  have hM : phaseCount Ω γ E = cutPhaseCount Ω γ π E + arcCount π U := by
    rw [phaseCount, cutPhaseCount, ← hUdef, cutPhaseSum_eq_add hps hsa]; field_simp; ring
  rw [hM, hJ0 E hE hEδ, zero_add]
  exact_mod_cast hle

private theorem phaseCount_const {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hno : ∀ j, ∀ E ∈ Set.Icc E₁ E₂, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    phaseCount Ω γ E₂ = phaseCount Ω γ E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hloc : ∀ E₀ ∈ Set.Icc E₁ E₂, ∃ a > 0, ∀ E ∈ Set.Icc E₁ E₂, ∀ E' ∈ Set.Icc E₁ E₂,
      |E - E₀| < a → |E' - E₀| < a → E ≤ E' → phaseCount Ω γ E' = phaseCount Ω γ E := by
    intro E₀ hE₀
    have hpos₀ : 0 < E₀ := h1.trans_le hE₀.1
    have hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = ((0 : ℕ) : ℕ∞) := by
      rw [Nat.cast_zero, Set.encard_eq_zero]
      exact Set.eq_empty_of_forall_notMem fun i hi => hno i E₀ hE₀ hi
    obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E₀ hpos₀ 0 hm
    obtain ⟨ε, hε0, hεπ, hεA⟩ := exists_cot_half_gt A
    have hnoarc : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a → ∀ t, 0 < t → t ≤ ε → ∀ v : Ell2,
        v ≠ 0 → monodromyAt γ E v ≠ Complex.exp (t * Complex.I) • v := fun E hE hEa =>
      (hA E (h1.trans_le hE.1) hEa (fun j => hno j E hE)).no_arc_eigen hεπ hεA
    have hJ : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a →
        phaseCount Ω γ E = cutPhaseCount Ω γ ε E := fun E hE hEa => by
      rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_phaseSum (monodromyAt_mem_unitary hK E)
        (isCompactOperator_monodromyAt_sub_one hK hclosed (h1.trans_le hE.1).le)
        (fun t ht0 htε => hnoarc E hE hEa t ht0 htε.le)]
    refine ⟨a, ha, fun E hE E' hE' hEa hE'a hEE' => ?_⟩
    rw [hJ E hE hEa, hJ E' hE' hE'a]
    refine cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E E'
      (h1.trans_le hE.1) hEE' (fun F hF => ?_)
    have hFI : F ∈ Set.Icc E₁ E₂ := ⟨hE.1.trans hF.1, hF.2.trans hE'.2⟩
    have hFa : |F - E₀| < a := by
      rw [abs_lt] at hEa hE'a ⊢; constructor <;> linarith [hF.1, hF.2]
    exact exp_mul_I_notMem_spectrum (isCompactOperator_monodromyAt_sub_one hK hclosed
      (h1.trans_le hFI.1).le) hε0 hεπ (fun v hv => hnoarc F hFI hFa ε hε0 le_rfl v hv)
  let f : Set.Icc E₁ E₂ → ℝ := fun E => phaseCount Ω γ E
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨a, ha, hx⟩ := hloc x x.2
    filter_upwards [Metric.ball_mem_nhds x ha] with y hy
    have hy' : |(y : ℝ) - x| < a := by rwa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hy
    have hx0 : |(x : ℝ) - x| < a := by simpa using ha
    rcases le_total (y : ℝ) x with h | h
    · exact (hx y y.2 x x.2 hy' hx0 h).symm
    · exact hx x x.2 y y.2 hx0 hy' h
  have := Subtype.preconnectedSpace (s := Set.Icc E₁ E₂) isPreconnected_Icc
  exact hf.apply_eq_of_preconnectedSpace ⟨E₂, h12, le_rfl⟩ ⟨E₁, le_rfl, h12⟩

private theorem phaseCount_jump {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (j : ℕ)
    (hj : 0 < neumannEigenvalue Ω j) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = neumannEigenvalue Ω j}.encard = m) :
    ∃ δ > 0, ∀ E₁ E₂, 0 < E₁ → (neumannEigenvalue Ω j).toReal - δ < E₁ →
      E₁ < (neumannEigenvalue Ω j).toReal → (neumannEigenvalue Ω j).toReal < E₂ →
      E₂ < (neumannEigenvalue Ω j).toReal + δ →
      (∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E₁) →
      (∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E₂) →
      phaseCount Ω γ E₂ ≤ phaseCount Ω γ E₁ + m := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hfin := eig_ne_top hS.isLipschitzDomain j
  set μ := (neumannEigenvalue Ω j).toReal with hμdef
  have hμ0 : 0 < μ := ENNReal.toReal_pos hj.ne' hfin
  have hm' : {i | neumannEigenvalue Ω i = ENNReal.ofReal μ}.encard = m := by
    rwa [hμdef, ENNReal.ofReal_toReal hfin]
  obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ μ hμ0 m hm'
  obtain ⟨ε₀, hε₀, hε₀π, hε₀A⟩ := exists_cot_half_gt A
  set S : Set ℝ := {t | t ∈ Set.Ioo 0 ε₀ ∧ ∃ v : Ell2, v ≠ 0 ∧
    monodromyAt γ μ v = Complex.exp (t * Complex.I) • v}
  have hS_count : S.Countable := by
    obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK μ
    have hsum := summable_eigenMult_monodromy hK hclosed hμ0.le hW
    rw [← monodromyAt_eq hK hW] at hsum
    refine Set.MapsTo.countable_of_injOn (f := fun t : ℝ => Complex.exp (t * Complex.I))
      (t := Subtype.val '' Function.support
        (fun z : {z : ℂ // z ≠ 1} => (eigenMult (monodromyAt γ μ) z : ℝ) * ‖(z : ℂ) - 1‖))
      ?_ ?_ (hsum.countable_support.image _)
    · rintro t ⟨⟨ht0, htε⟩, v, hv0, hv⟩
      have hne : Complex.exp (t * Complex.I) ≠ 1 := fun h1 => by
        have := congrArg Complex.im h1
        rw [Complex.exp_ofReal_mul_I_im, Complex.one_im] at this
        linarith [Real.sin_pos_of_pos_of_lt_pi ht0 (htε.trans hε₀π)]
      refine ⟨⟨_, hne⟩, ?_, rfl⟩
      have := finiteDimensional_eigenspace
        (isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le) hne
      have hpos : 0 < eigenMult (monodromyAt γ μ) (Complex.exp (t * Complex.I)) :=
        Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, fun h => hv0 (by simpa using h)⟩
      exact (mul_pos (by exact_mod_cast hpos) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).ne'
    · intro s hs t ht hst
      have := congrArg Complex.arg hst
      simp only at this
      rwa [Complex.arg_exp_mul_I, Complex.arg_exp_mul_I, (toIocMod_eq_self _).mpr,
        (toIocMod_eq_self _).mpr] at this
      all_goals constructor <;> linarith [hs.1.1, hs.1.2, ht.1.1, ht.1.2]
  obtain ⟨ε, ⟨hε0, hεε₀⟩, hεS⟩ : (Set.Ioo 0 ε₀ \ S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    have h0 := measure_mono_null hne (hS_count.measure_zero MeasureTheory.volume)
    rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hεπ : ε < π := hεε₀.trans hε₀π
  have hεA : A < Real.cot (ε / 2) :=
    lt_of_lt_of_le hε₀A (cot_half_le_cot_half hε0 hεε₀.le hε₀π)
  have hspecμ : Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ μ) :=
    exp_mul_I_notMem_spectrum (isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le) hε0 hεπ
      (fun v hv h => hεS ⟨⟨hε0, hεε₀⟩, v, hv, h⟩)
  have hnhds : {E : ℝ | IsUnit (algebraMap ℂ (Ell2 →L[ℂ] Ell2) (Complex.exp (ε * Complex.I)) -
      monodromyAt γ E)} ∈ 𝓝 μ := by
    rw [spectrum.mem_iff, not_not] at hspecμ
    exact (continuousAt_const.sub (continuousAt_monodromyAt hK hclosed hμ0)).preimage_mem_nhds
      (Units.isOpen.mem_nhds hspecμ)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min a δ₁, lt_min ha hδ₁, ?_⟩
  intro E₁ E₂ hE₁0 hE₁lo hE₁hi hE₂lo hE₂hi hnr₁ hnr₂
  have hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E) := fun E hE => by
    rw [spectrum.mem_iff, not_not]
    exact hball (Metric.mem_ball.mpr (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_right a δ₁, hE.1, hE.2]))
  have hJ := cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E₁ E₂ hE₁0 (by linarith) hcut
  have hdec : ∀ E, 0 < E → |E - μ| < a → (∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E) →
      phaseCount Ω γ E = cutPhaseCount Ω γ ε E + arcCount ε (monodromyAt γ E) ∧
        arcCount ε (monodromyAt γ E) ≤ m := fun E hE hEa hnr => by
    obtain ⟨hsa, hle⟩ := arcCount_le (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (by linarith [Real.pi_pos])
      (fun t ht0 htε => lt_of_lt_of_le hεA (cot_half_le_cot_half ht0 htε.le hεπ))
      (hA E hE hEa hnr)
    refine ⟨?_, hle⟩
    rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_add (phase_summable hb hS hsc hγ E hE hnr) hsa]
    have := Real.pi_pos; field_simp; ring
  have hE₁a : |E₁ - μ| < a := abs_lt.mpr ⟨by linarith [min_le_left a δ₁], by linarith [min_le_left a δ₁]⟩
  have hE₂a : |E₂ - μ| < a := abs_lt.mpr ⟨by linarith [min_le_left a δ₁], by linarith [min_le_left a δ₁]⟩
  obtain ⟨h1eq, -⟩ := hdec E₁ hE₁0 hE₁a hnr₁
  obtain ⟨h2eq, h2le⟩ := hdec E₂ (by linarith) hE₂a hnr₂
  rw [h1eq, h2eq, hJ]
  linarith [arcCount_nonneg ε (monodromyAt γ E₁)]

private theorem phaseCount_le_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    ENNReal.ofReal (phaseCount Ω γ E) ≤ (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  have hL := hS.isLipschitzDomain
  have hfin : ∀ j, neumannEigenvalue Ω j ≠ ⊤ := eig_ne_top hL
  set lam : ℕ → ℝ := fun j => (neumannEigenvalue Ω j).toReal with hlam
  have hμ : ∀ j, neumannEigenvalue Ω j = ENNReal.ofReal (lam j) := fun j =>
    (ENNReal.ofReal_toReal (hfin j)).symm
  have hne : ∀ j (t : ℝ), 0 ≤ t → (neumannEigenvalue Ω j ≠ ENNReal.ofReal t ↔ lam j ≠ t) :=
    fun j t ht => by rw [hμ j, ne_eq, ne_eq, ENNReal.ofReal_eq_ofReal_iff ENNReal.toReal_nonneg ht]
  have hcount : neumannCount Ω (ENNReal.ofReal E) = {j | lam j < E}.encard := by
    rw [neumannCount]; congr 1; ext j; simp [hμ j, ENNReal.ofReal_lt_ofReal_iff hE]
  by_cases hinf : {j | lam j < E}.Finite
  swap
  · rw [hcount, Set.encard_eq_top_iff.mpr hinf, ENat.toENNReal_top]; exact le_top
  have h0 : lam 0 = 0 := by simp [hlam, neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb]
  have key := phase_le_count_of_jumps lam h0 (phaseCount Ω γ)
    (by obtain ⟨δ, hδ, h⟩ := phaseCount_initial_le hb hS hγ; exact ⟨δ, hδ, fun E hE hEδ _ => h E hE hEδ⟩)
    (fun E₁ E₂ h1 h12 hno => (phaseCount_const hb hS hsc hγ E₁ E₂ h1 h12 fun j t ht =>
      (hne j t (h1.le.trans ht.1)).mpr fun h => hno j (h ▸ ht)).le)
    (fun j hj m hm => by
      have hset : {i | neumannEigenvalue Ω i = neumannEigenvalue Ω j} = {i | lam i = lam j} := by
        ext i; exact (ENNReal.toReal_eq_toReal_iff' (hfin i) (hfin j)).symm
      obtain ⟨δ, hδ, h⟩ := phaseCount_jump hb hS hsc hγ j
        (by rw [hμ j]; exact ENNReal.ofReal_pos.mpr hj) m (hset ▸ hm)
      exact ⟨δ, hδ, fun E₁ E₂ h1 h2 h3 h4 h5 h6 h7 => h E₁ E₂ h1 h2 h3 h4 h5
        (fun i => (hne i E₁ h1.le).mpr (h6 i))
        (fun i => (hne i E₂ (h1.trans (h3.trans h4)).le).mpr (h7 i))⟩)
    E hE (fun j => (hne j E hE.le).mp (hnr j)) hinf
  rw [hcount, ← hinf.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal key

private theorem smooth_count_nonresonant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ E W) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖monodromy W - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hU := monodromy_mem_unitary' hK hW
  have hUc := isCompactOperator_monodromy_sub_one hK hclosed hE.le hW
  have hs := phase_summable hb hS hsc hγ E hE hnr
  have hM := phaseCount_le_count hb hS hsc hγ E hE hnr
  rw [phaseCount, monodromyAt_eq hK hW] at hM
  rw [monodromyAt_eq hK hW] at hs
  have hnn : ∀ z : {z : ℂ // z ≠ 1}, 0 ≤ -phaseTerm (monodromy W) z := fun z =>
    neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (argNeg_nonpos _))
  have hle : ‖monodromy W - 1‖ ≤ -phaseSum (monodromy W) := by
    rw [phaseSum, ← tsum_neg]
    by_cases hU1 : monodromy W = 1
    · conv_lhs => rw [hU1, sub_self, norm_zero]
      exact tsum_nonneg hnn
    · obtain ⟨c, v, hv0, hv, hc1, hcn⟩ := exists_eigenvalue_norm_sub_one hU hUc hU1
      let z₀ : {z : ℂ // z ≠ 1} := ⟨c, hc1⟩
      haveI := finiteDimensional_eigenspace hUc hc1
      have hpos : (1 : ℝ) ≤ eigenMult (monodromy W) c := by
        exact_mod_cast (Module.finrank_pos_iff_exists_ne_zero
          (R := ℂ) (M := Module.End.eigenspace (monodromy W : Ell2 →ₗ[ℂ] Ell2) c)).mpr
          ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, fun h => hv0 (by simpa using h)⟩
      have hz1 : ‖c‖ = 1 := norm_eq_one_of_eigen hU hv0 hv
      have h1 := norm_sub_one_le_neg_argNeg hz1
      have h2 : -argNeg c ≤ -phaseTerm (monodromy W) z₀ := by
        simp only [phaseTerm, z₀]; nlinarith [argNeg_nonpos c]
      exact (hcn.symm.le.trans (h1.trans h2)).trans (hs.neg.le_tsum z₀ fun i _ => hnn i)
  rw [count_lhs_eq_ofReal hb.measure_lt_top.ne hE.le]
  refine (ENNReal.ofReal_le_ofReal ?_).trans hM
  have := Real.pi_pos
  rw [show (volume Ω).toReal * E / (4 * π) + ‖monodromy W - 1‖ / (2 * π) =
    ((volume Ω).toReal * E / 2 + ‖monodromy W - 1‖) / (2 * π) by field_simp; ring]
  gcongr
  linarith

private theorem smooth_eigen {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (j : ℕ)
    (hj : 1 ≤ j) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ (neumannEigenvalue Ω j).toReal W) :
    volume Ω * neumannEigenvalue Ω j + ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≤
      ENNReal.ofReal (4 * π * j) := by
  classical
  have hL := hS.isLipschitzDomain
  have hfin := eig_ne_top hL j
  set E := (neumannEigenvalue Ω j).toReal
  have hE : 0 < E := ENNReal.toReal_pos (neumannEigenvalue_pos hb hL j hj).ne' hfin
  have hsc_count : volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
      ENNReal.ofReal (‖monodromy W - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
    obtain ⟨K, hK⟩ := hγ.lipschitz
    have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
    choose Ws hWs using fun E' : ℝ => transport_exists_of_lipschitz γ hK E'
    have hWE : monodromy (Ws E) = monodromy W := by
      unfold monodromy
      rw [transport_unique_of_lipschitz γ hK E (hWs E) hW ⟨by positivity, le_rfl⟩]
    set N : ℕ∞ := neumannCount Ω (ENNReal.ofReal E) with hNdef
    by_cases hN : N = ⊤
    · rw [hN, ENat.toENNReal_top]; exact le_top
    set T := {i : ℕ | neumannEigenvalue Ω i < ENNReal.ofReal E}
    have hT : T.Finite := Set.encard_ne_top_iff.mp hN
    have hN' : (N : ENNReal) ≠ ⊤ := by simpa using hN
    have hvol : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
    set g : ℝ → ℝ := fun E' => (volume Ω).toReal * E' / (4 * π) + ‖monodromy (Ws E') - 1‖ / (2 * π)
    have hev2 : ∀ᶠ E' in 𝓝[<] E, ∀ i ∈ T, (neumannEigenvalue Ω i).toReal < E' :=
      hT.eventually_all.mpr fun i hi => by
        have hlt : (neumannEigenvalue Ω i).toReal < E :=
          ((ENNReal.toReal_lt_toReal (ne_top_of_lt hi) ENNReal.ofReal_ne_top).mpr hi).trans_le
            (by rw [ENNReal.toReal_ofReal hE.le])
        exact Filter.mem_of_superset (Ioo_mem_nhdsLT hlt) fun x hx => hx.1
    have hev : ∀ᶠ E' in 𝓝[<] E, g E' ≤ (N : ENNReal).toReal := by
      filter_upwards [Ioo_mem_nhdsLT hE, hev2] with E' hE' hT'
      have hlt : ENNReal.ofReal E' < ENNReal.ofReal E := (ENNReal.ofReal_lt_ofReal_iff hE).mpr hE'.2
      have hnr : ∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E' := fun i hi => by
        have := hT' i (show neumannEigenvalue Ω i < _ from hi ▸ hlt)
        rw [hi, ENNReal.toReal_ofReal hE'.1.le] at this
        exact lt_irrefl _ this
      have hcount : neumannCount Ω (ENNReal.ofReal E') = N := by
        rw [hNdef, neumannCount, neumannCount]; congr 1; ext i
        change neumannEigenvalue Ω i < _ ↔ neumannEigenvalue Ω i < _; constructor
        · exact fun h => h.trans hlt
        · intro h
          rw [← ENNReal.ofReal_toReal (ne_top_of_lt h)]
          exact (ENNReal.ofReal_lt_ofReal_iff hE'.1).mpr (hT' i h)
      have h := smooth_count_nonresonant hb hS hsc hγ E' hE'.1 hnr (Ws E') (hWs E')
      rw [hcount, count_lhs_eq_ofReal hvol hE'.1.le] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hN').mp h
    have hcont : ContinuousAt g E :=
      ((continuous_const.mul continuous_id).div_const _).continuousAt.add
        ((((hasDerivAt_monodromy_energy hK hclosed hWs hE).continuousAt).sub
          continuousAt_const).norm.div_const _)
    rw [count_lhs_eq_ofReal hvol hE.le, ← hWE]
    exact (ENNReal.ofReal_le_iff_le_toReal hN').mpr
      (le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev)
  rw [ENNReal.ofReal_toReal hfin] at hsc_count
  have hc : ((neumannCount Ω (neumannEigenvalue Ω j) : ℕ∞) : ENNReal) ≤ (j : ENNReal) := by
    simpa [neumannCount] using ENat.toENNReal_le.mpr
      (encard_lt_le_of_monotone _ (neumannEigenvalue_monotone Ω) j)
  have h2 := hsc_count.trans hc
  have h4 : ENNReal.ofReal (4 * π) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have h3 := mul_le_mul_left h2 (ENNReal.ofReal (4 * π))
  rw [add_mul, ENNReal.div_mul_cancel h4 ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul (by positivity)] at h3
  convert h3 using 2
  · congr 1; field_simp; ring
  · rw [mul_comm (j : ENNReal), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

theorem strict_neumann_polya (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) := by
  have hfin := eig_ne_top hL j
  have hE : 0 < (neumannEigenvalue Ω j).toReal :=
    ENNReal.toReal_pos (neumannEigenvalue_pos hb hL j hj).ne' hfin
  obtain ⟨γ, hγ⟩ := exists_boundaryParam hb hL hsc
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK (neumannEigenvalue Ω j).toReal
  obtain ⟨A⟩ := exists_ballZarnescu hb hL
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_boundaryParam_ballZarnescu hb hL hγ A)
  choose γ' hγ' τ hτm hτL hτ0 hτ2 hτc using fun n => hN (n + N) (Nat.le_add_left N n)
  have hfr : ∀ θ, γ θ ∈ closure Ω := fun θ => by
    have h1 : γ θ ∈ γ '' Set.Icc 0 (0 + 2 * π) := by
      rw [hγ.periodic.image_Icc Real.two_pi_pos]; exact Set.mem_range_self θ
    rw [zero_add, hγ.image] at h1
    exact frontier_subset_closure h1
  have hcl : ∀ n, LipschitzWith (A.lip * K) (A.map (n + N) ∘ γ) := fun n =>
    lipschitzOnWith_univ.mp ((A.lipschitz (n + N)).comp (hK.lipschitzOnWith (s := Set.univ))
      fun θ _ => hfr θ)
  choose Ws hWs using fun n => transport_exists_of_lipschitz (A.map (n + N) ∘ γ) (hcl n)
    (neumannEigenvalue (A.map (n + N) '' Ω) j).toReal
  choose Ws' hWs' using fun n => transport_exists_of_lipschitz (γ' n)
    ((hγ' n).lipschitz.choose_spec) (neumannEigenvalue (A.map (n + N) '' Ω) j).toReal
  have hsmooth : ∀ n, volume (A.map (n + N) '' Ω) * neumannEigenvalue (A.map (n + N) '' Ω) j +
      ENNReal.ofReal (2 * ‖monodromy (Ws n) - 1‖) ≤ ENNReal.ofReal (4 * π * j) := fun n => by
    obtain ⟨Kτ, hKτ⟩ := hτL n
    obtain ⟨K', hK'⟩ := (hγ' n).lipschitz
    have hWcomp : IsTransport (γ' n ∘ τ n) _ (Ws n) := (hτc n).symm ▸ hWs n
    rw [monodromy_comp hK' (hτm n) hKτ (hτ0 n) (hτ2 n) (hWs' n) hWcomp]
    exact smooth_eigen (hb.subset (A.subset _)) (A.smooth _)
      (((A.map (n + N)).image Ω).symm.toHomotopyEquiv.simplyConnectedSpace)
      (hγ' n) j hj (Ws' n) (hWs' n)
  have hvolfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  obtain ⟨hμ, hvol⟩ := tendsto_ballZarnescu_eigen_and_volume hb hL A N j
  have hct : TendstoUniformlyOn (fun n => A.map (n + N) ∘ γ) γ atTop (Set.Icc 0 (2 * π)) := by
    have h := (A.tendsto.comp γ).mono (fun θ _ => hfr θ : Set.Icc 0 (2 * π) ⊆ γ ⁻¹' closure Ω)
    exact fun u hu => (tendsto_add_atTop_nat N).eventually (h u hu)
  have hclen : ∃ B, ∀ n, ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (A.map (n + N) ∘ γ) θ‖ ≤ B :=
    ⟨2 * π * (A.lip * K), fun n => by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
        (f := fun θ => ‖deriv (⇑(A.map (n + N)) ∘ γ) θ‖) (C := A.lip * K) fun θ _ => by
          rw [norm_norm]; exact_mod_cast norm_deriv_le_of_lipschitz (hcl n)
      rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
      exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; linarith)⟩
  have hq := lipschitz_quantitative_of_approximation (fun n => A.map (n + N) '' Ω) j hK hcl hclosed
    (fun n => by simp [Function.comp, hclosed]) hct hclen hW hWs hsmooth hvolfin hfin hvol hμ
  have hU := norm_sub_one_pos (monodromy_ne_one hb hL hγ _ hE W hW)
  have hpos : ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  exact lt_of_lt_of_le (ENNReal.lt_add_right (ENNReal.mul_ne_top hvolfin hfin) hpos) hq

theorem strict_neumann_polya_count (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) :=
  count_of_eigen _ _ hb.measure_lt_top.ne (neumannEigenvalue_monotone Ω)
    (neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb) (strict_neumann_polya Ω hb hL hsc) E hE

end PolyaNeumann

end