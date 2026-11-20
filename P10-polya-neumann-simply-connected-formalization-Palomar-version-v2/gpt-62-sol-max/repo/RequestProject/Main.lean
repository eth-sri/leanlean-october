module

public import RequestProject.Finite
public import RequestProject.Transport
public import RequestProject.Unitarity
public import RequestProject.CurveContinuity
public import RequestProject.AreaTrace
public import RequestProject.Driven
public import RequestProject.CayleyFactorization
public import RequestProject.Phase
public import RequestProject.CutCorrection
public import RequestProject.Reparam
public import RequestProject.BoundaryOrigin
public import RequestProject.PeriodicForm
public import RequestProject.Coercivity
public import RequestProject.NegativeIndex
public import RequestProject.FiniteRankCompletion
public import RequestProject.RankBound
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
public import RequestProject.SmallEnergyCore
public import RequestProject.NeumannMultiplicity
public import RequestProject.OriginalSmoothCayleyBound

/-!
# The strict Neumann Pólya inequality on simply connected planar domains

Main results of the paper:

* `PolyaNeumann.strict_neumann_polya` (Theorem 10.16): for every bounded simply connected
  Lipschitz domain `Ω ⊂ ℝ²` and every `j ≥ 1`, `|Ω| μ_j(Ω) < 4π j`;
* `PolyaNeumann.strict_neumann_polya_count`: for every `E > 0`, `N_N(E) > |Ω| E / (4π)`.

The proof is assembled, exactly as in the paper, from
* Lemma 3.3 (discreteness of the Neumann spectrum),
* the quantitative Lipschitz inequality (Theorem 10.15)
  `|Ω| μ_j + 2 ‖U_{μ_j} - I‖ ≤ 4π j`,
* Lemma 10.5 (`U_E ≠ I` for `E > 0`),
* Lemma 3.5 (equivalence of the eigenvalue and counting forms).
-/

@[expose] public section

open scoped Real ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-! ### Lemma 3.3: the discrete Neumann spectrum -/

/-- Lemma 3.3: the Neumann eigenvalues of a Lipschitz domain are finite. -/
theorem neumannEigenvalue_lt_top {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (j : ℕ) :
    neumannEigenvalue Ω j < ⊤ :=
  neumannEigenvalue_lt_top_of_isOpen hL.1.1 hL.1.2.nonempty j

/-! ### Boundary parametrization and transport (Section 10) -/

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω)
include Ω hb hL hsc

/-- A bounded simply connected Lipschitz domain admits a positively oriented
rescaled-arclength parametrization of its Jordan boundary. -/
theorem exists_boundaryParam : ∃ γ : ℝ → ℂ, IsBoundaryParam Ω γ := by
  have hconn := isPreconnected_frontier_of_simplyConnected hb hL hsc
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him⟩ := exists_jordanParam_of_isPreconnected_frontier hb hL hconn
  obtain ⟨σ, hσ, hin, hout⟩ := windingNumber_pm_one_of_jordan hb hL hK hper hinj him
    (isConnected_compl_closure_of_frontier hb hL hconn)
  have harea := integral_signedAreaDensity_of_winding hL.1.1 hb hK him σ hin hout
  obtain ⟨γ1, ⟨K1, hK1⟩, hper1, hinj1, him1, ⟨c, hc, hspeed⟩, harea1, -⟩ :=
    exists_constSpeed_reparam hK hper hinj
  rcases hσ with rfl | rfl
  · exact ⟨γ1, ⟨⟨K1, hK1⟩, hper1, hinj1, him1.trans him, ⟨c, hc, hspeed⟩,
      show ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ1 θ = _ by simp [harea1, harea]⟩⟩
  · obtain ⟨γ2, hK2, hper2, hinj2, him2, hspeed2, harea2⟩ :=
      exists_reverse_param hK1 hper1 hinj1 hspeed
    exact ⟨γ2, ⟨⟨K1, hK2⟩, hper2, hinj2, him2.trans (him1.trans him), ⟨c, hc, hspeed2⟩,
      show ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ2 θ = _ by simp [harea2, harea1, harea]⟩⟩

end

private lemma not_finiteDimensional_ell2 : ¬ FiniteDimensional ℂ Ell2 := by
  intro h
  let e : HilbertBasis ℕ ℂ Ell2 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Ell2)
  have := e.orthonormal.linearIndependent.finite
  exact not_finite ℕ


section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E)
include Ω hb hL γ hγ E hE

/-- Lemma 10.5: for every `E > 0`, `dim ker(V_E - I) ≤ dim ker(A_N - E) < ∞`; in particular
the monodromy satisfies `U_E ≠ I`. The finiteness of `dim ker(A_N - E)` is
`finiteDimensional_neumannEigenspace` (from Rellich compactness); if `U_E = I`, the fixed space
of `V_E` would be all of the infinite-dimensional space `ℓ²(ℕ₀)`. -/
theorem monodromyAt_ne_one : monodromyAt γ E ≠ 1 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  rw [monodromyAt_eq hK hW]
  intro h
  obtain ⟨T, hT⟩ := fixedSpace_to_neumannEigenspace_of_reconstruction hγ hE hW
    (neumann_reconstruction_of_compatible hb hL hγ hE)
  haveI := finiteDimensional_neumannEigenspace hb hL E
  have hV : W (2 * π) = 1 := by
    simpa [monodromy, ← ContinuousLinearMap.star_eq_adjoint] using congrArg star h
  haveI : FiniteDimensional ℂ
      (LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2)) :=
    Module.Finite.of_injective T hT
  have htop : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) = ⊤ := by
    simp_all
  rw [htop] at this
  exact not_finiteDimensional_ell2 (LinearEquiv.finiteDimensional Submodule.topEquiv)

end

/-! ### Analytic domains (Section 9) -/

/-- Proposition 7.10 (uniform Cayley bound and resonance rank), read on eigenvectors through
the Cayley correspondence (an eigenvalue `e^{it}` of `U_E`, `0 < t < 2π`, is the eigenvalue
`cot(t/2)` of the Cayley transform `K_E`). Let `E₀ > 0` have Neumann multiplicity `m`: the
number of indices `i` with `μ_i = E₀` (so `m = 0` if `E₀` is nonresonant). Then there are `A`
and `a > 0` such that at every nonresonant energy `E > 0` with `|E - E₀| < a`, every orthonormal
family of eigenvectors of `U_E` with eigenvalues `e^{it}`, `cot(t/2) > A`, has at most `m`
members (`rank 1_{(A,∞)}(K_E) ≤ m`; for `m = 0` this is `K_E ≤ A`).
Proved from the original analytic-domain Herglotz bound and the chosen-origin Cayley transfer
(`uniform_cayley_rank_bound_of_analytic_domain`). -/
theorem uniform_cayley_rank_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsAnalyticDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E₀ : ℝ) (hE₀ : 0 < E₀) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = m) :
    ∃ A a : ℝ, 0 < a ∧ ∀ E, 0 < E → |E - E₀| < a →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      CayleyRankBound (monodromyAt γ E) A m := by
  exact uniform_cayley_rank_bound_of_analytic_domain hb hS hsc hγ E₀ hE₀ m hm
    (monodromyAt_ne_one hb hS.isLipschitzDomain hγ E₀ hE₀)

/-- Lemma 9.3 (continuity of a cut logarithm), for the monodromy of a bounded analytic Jordan
domain: let `0 < ε < 2π` and let `[E₁, E₂] ⊂ (0, ∞)` be an interval on which `e^{iε}` (hence the
whole radial cut through it) avoids the spectrum of `U_E`. Then the cut phase count
`J_ε(E) = (E|Ω|/2 - tr(-i log_ε U_E)) / (2π)` takes the same value at `E₁` and `E₂`. Here the
trace is written as the multiplicity-weighted eigenvalue sum `∑_{z ≠ 1} mult(z) argCut ε z`.
Proved from `cutPhaseSum_monodromyAt_sub` and Green's formula `∫ b = 2|Ω|` (part of the
boundary parametrization). -/
theorem cutPhaseCount_const {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ) (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseCount Ω γ ε E₂ = cutPhaseCount Ω γ ε E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have h := cutPhaseSum_monodromyAt_sub hK hclosed hε0 hε E₁ E₂ h1 h12 hcut
  have harea : ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = 2 * (volume Ω).toReal := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  rw [harea] at h
  unfold cutPhaseCount
  rw [div_left_inj' (by positivity)]
  linarith

private theorem summable_eigenMult_monodromyAt {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hc : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) :
    Summable (fun z : {z : ℂ // z ≠ 1} => (eigenMult (monodromyAt γ E) z : ℝ) * ‖(z : ℂ) - 1‖) := by
  obtain ⟨C, -, hC⟩ := exists_linear_traceBound_monodromyAt hK hc
  exact summable_eigenMult_mul_norm (monodromyAt_mem_unitary hK E) (hC E hE)

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsAnalyticDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E)
include Ω hb hS hsc γ hγ E hE hnr

/-- The phase sum converges at every nonresonant energy: a sufficiently small positive cut
avoids the spectrum and changes no eigenvalue's phase. -/
private theorem phase_summable : Summable (phaseTerm (monodromyAt γ E)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E hE 0 (by simp [hnr])
  obtain ⟨ε, hε, hεπ, hεA⟩ := exists_cot_half_gt A
  have hno := (hA E hE (by simpa using ha) hnr).no_arc_eigen hεπ hεA
  have hU := monodromyAt_mem_unitary hK E
  have hC := isCompactOperator_monodromyAt_sub_one hK hclosed hE.le
  refine (summable_cutPhaseTerm hU (summable_norm_eigIdx (summable_eigenMult_monodromyAt hK hclosed hE.le))
    hε (by linarith [Real.pi_pos]) (exp_mul_I_notMem_spectrum hC hε hεπ (hno ε hε le_rfl))).congr ?_
  intro z
  rw [cutPhaseTerm_eq, arcTerm_eq_zero hU hC (fun t ht h => hno t ht h.le), mul_zero, add_zero]

end

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
include Ω hb hL γ hγ

/-- Lemma 8.7 (positive principal phases at small energy), read on eigenvectors through the
Cayley correspondence: there is `δ > 0` such that for `0 < E < δ`, every orthonormal family of
eigenvectors of `U_E` with eigenvalues `e^{it}`, `cot(t/2) > 0` (that is, positive principal
phases `t ∈ (0, π)`), has at most one member.
Proved, as in the paper, from `ind₋ 𝒜_E ≤ 1` on Herglotz data (`small_energy_herglotz_bound`,
Lemma 8.6) and the Cayley factorization, which turns two positive principal phases into a
two-dimensional negative subspace of `𝒜_E` (`cayleyRankBound_of_herglotzForm_bound`). -/
theorem small_energy_cayley_rank_bound  :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → CayleyRankBound (monodromyAt γ E) 0 1 := by
  obtain ⟨δ, hδ, hA⟩ := small_energy_herglotz_bound hb hL hγ
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  refine ⟨δ, hδ, fun E hE hEδ => ?_⟩
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  obtain ⟨L, hL⟩ := hA E hE hEδ W hW
  rw [monodromyAt_eq hK hW]
  exact cayleyRankBound_of_herglotzForm_bound hK hclosed hW 0 0 le_rfl L
    (fun a ha hLa => by simp_all)

end

/-- Lemma 8.8 (initial value of the phase count): for a bounded analytic Jordan domain,
`M(E) = 1` for all sufficiently small `E > 0`. Proved, as in the paper (Lemmas 8.7–8.8): the
trace-norm bound `‖U_E - I‖_{𝒮₁} ≤ C E` keeps `-1` out of the spectrum and makes the principal
phase sum `O(E)`; the principal cut phase count `J_π` is constant (`cutPhaseCount_const`) and
tends to `0`, so `∑ θ_j = E|Ω|/2`; exactly one principal phase is positive
(`small_energy_cayley_rank_bound`, and the sum is positive), and `M = J_π + 1 = 1`. -/
theorem phaseCount_initial {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → phaseCount Ω γ E = 1 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨Cq, hCq0, hT⟩ := exists_linear_traceBound_monodromyAt hK hclosed
  obtain ⟨δr, hδr, hrank⟩ := small_energy_cayley_rank_bound hb hL hγ
  set v := (volume Ω).toReal with hv
  have hvpos := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have hpi := Real.pi_pos
  set δ := min δr (1 / (Cq + 1)) with hδ
  have hδpos : 0 < δ := lt_min hδr (by positivity)
  have hsmall : ∀ E, 0 < E → E < δ → Cq * E < 2 := by
    intro E hE hEδ
    have h1 := hEδ.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  -- `-1` avoids the spectrum
  have hcut : ∀ E, 0 < E → E < δ →
      Complex.exp (π * Complex.I) ∉ spectrum ℂ (monodromyAt γ E) := by
    intro E hE hEδ hmem
    rw [Complex.exp_pi_mul_I] at hmem
    obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) hmem (by norm_num)
    exact not_eigen_neg_one_of_traceBound (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
      (hsmall E hE hEδ) hw0 hw
  -- `J_π(E) = O(E)`
  set c := (v / 2 + π / 2 * Cq) / (2 * π) with hc
  have hJb : ∀ E, 0 < E → E < δ → |cutPhaseCount Ω γ π E| ≤ c * E := by
    intro E hE hEδ
    obtain ⟨-, hP⟩ := cutPhaseSum_pi_bound (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
    rw [cutPhaseCount, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      div_le_iff₀ (by positivity)]
    calc |v * E / 2 - cutPhaseSum π (monodromyAt γ E)|
        ≤ v * E / 2 + π / 2 * (Cq * E) := by
          have h := abs_sub (v * E / 2) (cutPhaseSum π (monodromyAt γ E))
          rw [abs_of_nonneg (by positivity : 0 ≤ v * E / 2)] at h
          exact h.trans (add_le_add_right hP _)
      _ = c * E * (2 * π) := by rw [hc]; field_simp
  -- `J_π = 0`
  have hJ0 : ∀ E, 0 < E → E < δ → cutPhaseCount Ω γ π E = 0 := by
    intro E hE hEδ
    have hev : ∀ᶠ F in 𝓝[>] (0 : ℝ), |cutPhaseCount Ω γ π E| ≤ c * F := by
      filter_upwards [Ioo_mem_nhdsGT hE] with F hF
      rw [cutPhaseCount_const hγ hpi (by linarith) F E hF.1 hF.2.le
        (fun G hG => hcut G (hF.1.trans_le hG.1) (hG.2.trans_lt hEδ))]
      exact hJb F hF.1 (hF.2.trans hEδ)
    have hlim : Tendsto (fun F => c * F) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul c).mono_left nhdsWithin_le_nhds
    exact abs_nonpos_iff.mp (ge_of_tendsto hlim hev)
  refine ⟨δ, hδpos, fun E hE hEδ => ?_⟩
  set U := monodromyAt γ E with hUdef
  have hUu := monodromyAt_mem_unitary hK E
  have hUc := isCompactOperator_monodromyAt_sub_one hK hclosed hE.le
  obtain ⟨hsa, hle⟩ := arcCount_le (ε := π) (A := 0) hUu hUc (by linarith)
    (fun t ht0 htπ => by
      rw [Real.cot_eq_cos_div_sin]
      exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))
    (hrank E hE (hEδ.trans_le (min_le_left _ _)))
  obtain ⟨hcs, -⟩ := cutPhaseSum_pi_bound hUu hUc (hT E hE.le)
  have hM := phaseCount_eq_cutPhaseCount_add_arcCount (Ω := Ω) hcs hsa
  have hJ := hJ0 E hE hEδ
  -- the principal phase sum is `E|Ω|/2 > 0`
  have hP : cutPhaseSum π U = v * E / 2 := by
    unfold cutPhaseCount at hJ
    exact (sub_eq_zero.mp ((div_eq_zero_iff.mp hJ).resolve_right Real.two_pi_pos.ne')).symm
  have hge : 1 ≤ arcCount π U := by
    by_contra hlt
    push_neg at hlt
    have hall : ∀ z, arcTerm π U z = 0 := by
      intro z
      by_contra hz
      have h1 : 1 ≤ arcTerm π U z := by
        unfold arcTerm at hz ⊢
        split_ifs at hz ⊢ with h
        · have : eigenMult U z ≠ 0 := by exact_mod_cast hz
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
        trivial
      have h2 : arcTerm π U z ≤ arcCount π U :=
        hsa.le_tsum z (fun j _ => arcTerm_nonneg π U j)
      linarith
    have hnp : cutPhaseSum π U ≤ 0 := by
      refine tsum_nonpos fun z => ?_
      rw [cutPhaseTerm_eq, hall z, mul_zero, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (argNeg_nonpos _)
    have : 0 < v * E / 2 := by positivity
    linarith
  rw [hM, hJ0 E hE hEδ, zero_add]
  exact le_antisymm (by exact_mod_cast hle) hge

/-- Lemma 9.4 (constancy away from the Neumann spectrum): `M` is constant on every interval
`[E₁, E₂] ⊆ (0, ∞)` containing no Neumann eigenvalue. Proved, as in the paper: locally the
uniform Cayley bound `K_E ≤ A` (`uniform_cayley_rank_bound`) excludes an arc
`{e^{it} : 0 < t ≤ ε}` from the spectrum of `U_E`, so `M = J_ε` there, and `J_ε` is locally
constant (`cutPhaseCount_const`); local constancy on an interval gives constancy. -/
theorem phaseCount_const {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsAnalyticDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hno : ∀ j, ∀ E ∈ Set.Icc E₁ E₂, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    phaseCount Ω γ E₂ = phaseCount Ω γ E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  -- local constancy
  have hloc : ∀ E₀ ∈ Set.Icc E₁ E₂, ∃ a > 0, ∀ E ∈ Set.Icc E₁ E₂, ∀ E' ∈ Set.Icc E₁ E₂,
      |E - E₀| < a → |E' - E₀| < a → E ≤ E' → phaseCount Ω γ E' = phaseCount Ω γ E := by
    intro E₀ hE₀
    have hpos₀ := h1.trans_le hE₀.1
    have hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = ((0 : ℕ) : ℕ∞) := by
      simp_all
    obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E₀ hpos₀ 0 hm
    obtain ⟨ε, hε0, hεπ, hεA⟩ := exists_cot_half_gt A
    have hnoarc : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a → ∀ t, 0 < t → t ≤ ε → ∀ v : Ell2,
        v ≠ 0 → monodromyAt γ E v ≠ Complex.exp (t * Complex.I) • v := fun E hE hEa =>
      (hA E (h1.trans_le hE.1) hEa (fun j => hno j E hE)).no_arc_eigen hεπ hεA
    have hJ : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a →
        phaseCount Ω γ E = cutPhaseCount Ω γ ε E := by
      intro E hE hEa
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
  -- constancy on the interval
  let f : Set.Icc E₁ E₂ → ℝ := fun E => phaseCount Ω γ E
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨a, ha, hx⟩ := hloc x x.2
    filter_upwards [Metric.ball_mem_nhds x ha] with y hy
    have hy' : |(y : ℝ) - x| < a := by
      assumption
    have hx0 : |(x : ℝ) - x| < a := by simp_all
    rcases le_total (y : ℝ) x with h | h
    grind
    grind
  haveI : PreconnectedSpace (Set.Icc E₁ E₂) := Subtype.preconnectedSpace isPreconnected_Icc
  exact hf.apply_eq_of_preconnectedSpace ⟨E₂, h12, le_rfl⟩ ⟨E₁, le_rfl, h12⟩

/-- Lemma 9.5 (bound on a jump): let `μ = μ_j > 0` be a Neumann eigenvalue of multiplicity
`m`, here the number of indices `i` with `μ_i = μ`. Then, for nonresonant energies
`0 < E₁ < μ < E₂` close enough to `μ`, `M(E₂) ≤ M(E₁) + m`. Proved, as in the paper: take `A` from
the resonance rank bound (`uniform_cayley_rank_bound`) and a cut `e^{iε}` with `cot(ε/2) > A`
outside the (countable) set of eigenvalues of `U_μ`; it stays outside the spectrum of `U_E` for
`E` near `μ`, so `J_ε` is constant there (`cutPhaseCount_const`), and
`M(E) = J_ε(E) + n_{(0,ε)}(U_E)` with `0 ≤ n_{(0,ε)}(U_E) ≤ m`. -/
theorem phaseCount_jump {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsAnalyticDomain Ω)
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
  have hfin := (neumannEigenvalue_lt_top hS.isLipschitzDomain j).ne
  set μ := (neumannEigenvalue Ω j).toReal with hμdef
  have hμ0 := ENNReal.toReal_pos hj.ne' hfin
  have hm' : {i | neumannEigenvalue Ω i = ENNReal.ofReal μ}.encard = m := by
    simp_all
  obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ μ hμ0 m hm'
  obtain ⟨ε₀, hε₀, hε₀π, hε₀A⟩ := exists_cot_half_gt A
  have hsum := summable_eigenMult_monodromyAt hK hclosed hμ0.le
  let S : Set ℝ := (fun z : {z : ℂ // z ≠ 1} => Complex.arg z) ''
    Function.support (fun z : {z : ℂ // z ≠ 1} => (eigenMult (monodromyAt γ μ) z : ℝ) * ‖(z : ℂ) - 1‖)
  have hSd : Dense Sᶜ := (hsum.countable_support.image _).dense_compl ℝ
  obtain ⟨ε, ⟨hε0, hεε₀⟩, hεS⟩ := hSd.inter_open_nonempty _ isOpen_Ioo (Set.nonempty_Ioo.mpr hε₀)
  have hεπ := hεε₀.trans hε₀π
  have hεA := hε₀A.trans_le (cot_half_le_cot_half hε0 hεε₀.le hε₀π)
  have hC := isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le
  have hspecμ := exp_mul_I_notMem_spectrum hC hε0 hεπ (by
    intro v hv h
    apply hεS
    have hne := exp_mul_I_ne_one hε0 (by linarith [Real.pi_pos] : ε < 2 * π)
    have hp := eigenMult_pos_of_eigen hC hne hv h
    refine ⟨⟨_, hne⟩, mul_ne_zero (by exact_mod_cast hp.ne') (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)), ?_⟩
    simp only [Complex.arg_exp_mul_I]
    exact (toIocMod_eq_self _).mpr ⟨by linarith [Real.pi_pos], by linarith⟩)
  have hnhds : {E : ℝ | Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)} ∈ 𝓝 μ := by
    simp only [spectrum.notMem_iff] at hspecμ ⊢
    exact (continuousAt_const.sub (continuousAt_monodromyAt hK hclosed hμ0)).preimage_mem_nhds
      (Units.isOpen.mem_nhds hspecμ)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min a δ₁, lt_min ha hδ₁, ?_⟩
  intro E₁ E₂ hE₁0 hE₁lo hE₁hi hE₂lo hE₂hi hnr₁ hnr₂
  have hnear {R E : ℝ} (hR : min a δ₁ ≤ R) (hE : E ∈ Set.Icc E₁ E₂) : |E - μ| < R :=
    abs_lt.mpr ⟨by linarith [hE.1], by linarith [hE.2]⟩
  have hcut (E : ℝ) (hE : E ∈ Set.Icc E₁ E₂) :
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E) :=
    hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hnear (min_le_right ..) hE)
  have hJ := cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E₁ E₂ hE₁0
    (by linarith) hcut
  -- `M = J_ε + n_{(0,ε)}` with `0 ≤ n_{(0,ε)} ≤ m`
  have hdec (E : ℝ) (hE : E ∈ Set.Icc E₁ E₂) (hEa : |E - μ| < a)
      (hnr : ∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E) :
      phaseCount Ω γ E = cutPhaseCount Ω γ ε E + arcCount ε (monodromyAt γ E) ∧
        arcCount ε (monodromyAt γ E) ≤ m := by
    have hpos := hE₁0.trans_le hE.1
    have hU := monodromyAt_mem_unitary hK E
    obtain ⟨hsa, hle⟩ := arcCount_le hU
      (isCompactOperator_monodromyAt_sub_one hK hclosed hpos.le) (by linarith [Real.pi_pos])
      (fun t ht0 htε => hεA.trans_le (cot_half_le_cot_half ht0 htε.le hεπ)) (hA E hpos hEa hnr)
    have hsumE := summable_norm_eigIdx (summable_eigenMult_monodromyAt hK hclosed hpos.le)
    exact ⟨phaseCount_eq_cutPhaseCount_add_arcCount
      (summable_cutPhaseTerm hU hsumE hε0 (by linarith [Real.pi_pos]) (hcut E hE)) hsa, hle⟩
  have h₁ : E₁ ∈ Set.Icc E₁ E₂ := ⟨le_rfl, by linarith⟩
  have h₂ : E₂ ∈ Set.Icc E₁ E₂ := ⟨by linarith, le_rfl⟩
  obtain ⟨h1eq, -⟩ := hdec E₁ h₁ (hnear (min_le_left ..) h₁) hnr₁
  obtain ⟨h2eq, h2le⟩ := hdec E₂ h₂ (hnear (min_le_left ..) h₂) hnr₂
  rw [h1eq, h2eq, hJ]
  linarith [arcCount_nonneg ε (monodromyAt γ E₁)]

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsAnalyticDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E)
include Ω hb hS hsc γ hγ E hE hnr

/-- Lemma 9.6 (comparison with the strict count): for a bounded analytic Jordan domain and every
nonresonant `E > 0`, `M(E) ≤ N_N(E)`. Proved, as in the paper, by induction across the
finitely many eigenvalues below `E`, from the initial value (Lemma 8.8), the constancy away
from the spectrum (Lemma 9.4) and the jump bound (Lemma 9.5). -/
theorem phaseCount_le_count  :
    ENNReal.ofReal (phaseCount Ω γ E) ≤ (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  have hL := hS.isLipschitzDomain
  have hfin := fun j => (neumannEigenvalue_lt_top hL j).ne
  set lam : ℕ → ℝ := fun j => (neumannEigenvalue Ω j).toReal with hlam
  have hμ := fun j =>
    (ENNReal.ofReal_toReal (hfin j)).symm
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => ENNReal.toReal_nonneg
  -- conversions between the two descriptions of the spectrum
  have hne : ∀ j (t : ℝ), 0 ≤ t → (neumannEigenvalue Ω j ≠ ENNReal.ofReal t ↔ lam j ≠ t) := by
    intro j t ht
    rw [hμ j, ne_eq, ENNReal.ofReal_eq_ofReal_iff (hlam0 j) ht]
  have hcount : neumannCount Ω (ENNReal.ofReal E) = {j | lam j < E}.encard := by
    unfold neumannCount
    congr 1
    ext j
    simp only [Set.mem_setOf_eq]
    rw [hμ j, ENNReal.ofReal_lt_ofReal_iff hE]
  by_cases hinf : {j | lam j < E}.Finite
  swap
  · rw [hcount, Set.encard_eq_top_iff.mpr hinf]; simp
  have h0 : lam 0 = 0 := by
    simp [hlam, neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb]
  have key := phase_le_count_of_jumps lam h0 (phaseCount Ω γ)
    (by
      obtain ⟨δ, hδ, h⟩ := phaseCount_initial hb hS.isLipschitzDomain hγ
      grind)
    (by
      intro E₁ E₂ h1 h12 hno
      refine (phaseCount_const hb hS hsc hγ E₁ E₂ h1 h12 fun j t ht => ?_).le
      rw [hne j t (h1.le.trans ht.1)]
      rintro rfl
      tauto)
    (by
      intro j hj m hm
      have hj' : 0 < neumannEigenvalue Ω j := by
        rw [hμ j]; positivity
      have hset : {i | neumannEigenvalue Ω i = neumannEigenvalue Ω j} = {i | lam i = lam j} := by
        ext i
        simp  
        grind
      obtain ⟨δ, hδ, h⟩ := phaseCount_jump hb hS hsc hγ j hj' m (hset ▸ hm)
      refine ⟨δ, hδ, fun E₁ E₂ h1 h2 h3 h4 h5 h6 h7 => h E₁ E₂ h1 h2 h3 h4 h5 ?_ ?_⟩
      grind
      grind)
    E hE (fun j => (hne j E hE.le).mp (hnr j)) hinf
  rw [hcount, ← hinf.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  gcongr

/-- Theorem 9.7 at nonresonant energies (Lemma 9.2 combined with the phase count): for a
bounded analytic Jordan domain and a nonresonant `E > 0`,
`N_N(E) ≥ E |Ω| / (4π) + ‖U_E - I‖ / (2π)`. `U_E - I` is compact (Lemma 4.7), so if
`U_E ≠ I` its norm is `|z - 1|` for an eigenvalue `z ≠ 1` of `U_E` (Lemma 9.2). -/
private theorem analytic_count_nonresonant :
    ENNReal.ofReal ((volume Ω).toReal * E / (4 * π) +
        ‖monodromyAt γ E - 1‖ / (2 * π)) ≤ (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hc : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have h := norm_sub_one_le_neg_phaseSum (monodromyAt_mem_unitary hK E)
    (isCompactOperator_monodromyAt_sub_one hK hc hE.le) (phase_summable hb hS hsc hγ E hE hnr)
  refine (ENNReal.ofReal_le_ofReal ?_).trans (phaseCount_le_count hb hS hsc hγ E hE hnr)
  have hπ := Real.pi_pos
  unfold phaseCount
  field_simp
  linarith

end

/-- Theorem 9.7 (quantitative smooth counting inequality): for a bounded analytic Jordan
domain and every `E > 0`, `N_N(E) ≥ E |Ω| / (4π) + ‖U_E - I‖ / (2π)`. Proved, as in the paper,
from the nonresonant case by approaching `E` from below through nonresonant energies, using
the continuity of `E ↦ U_E` (Lemma 4.7). -/
theorem analytic_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsAnalyticDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) :
    ENNReal.ofReal ((volume Ω).toReal * E / (4 * π) +
        ‖monodromyAt γ E - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  let S : Set ℝ := (Set.range fun j => (neumannEigenvalue Ω j).toReal)ᶜ
  have hd : Dense S := (Set.countable_range _).dense_compl ℝ
  haveI : (𝓝[Set.Ioo 0 E ∩ S] E).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
    (closure_minimal (hd.open_subset_closure_inter isOpen_Ioo) isClosed_closure
      (by rw [closure_Ioo hE.ne]; exact ⟨hE.le, le_rfl⟩))
  let g (t : ℝ) := ENNReal.ofReal ((volume Ω).toReal * t / (4 * π) +
    ‖monodromyAt γ t - 1‖ / (2 * π))
  have hcont : ContinuousAt g E := by
    have hm := continuousAt_monodromyAt hK hclosed hE
    exact ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
  apply le_of_tendsto (x := 𝓝[Set.Ioo 0 E ∩ S] E) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hnr j (hj : neumannEigenvalue Ω j = ENNReal.ofReal t) : False :=
    ht.2 ⟨j, by simp [hj, ENNReal.toReal_ofReal ht.1.1.le]⟩
  have h := analytic_count_nonresonant hb hS hsc hγ t ht.1.1 hnr
  exact h.trans (ENat.toENNReal_mono (Set.encard_mono fun j hj =>
    hj.trans_le (ENNReal.ofReal_le_ofReal ht.1.2.le)))

/-! ### Lipschitz domains -/

/-- Norm convergence of the monodromy along the approximating boundary curves. -/
private theorem bz_monodromy_tendsto {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (A : BallZarnescuApprox Ω) (E : ℝ) :
    Tendsto (fun n => monodromyAt (A.map n ∘ γ) E) atTop (𝓝 (monodromyAt γ E)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hl n := (A.lipschitzWith n).comp hK
  have hc : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hunif :=
    (A.tendsto.comp γ).mono fun t ht => frontier_subset_closure (hγ.image ▸ Set.mem_image_of_mem γ ht)
  have hlength : ∃ B, ∀ n, ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (A.map n ∘ γ) θ‖ ≤ B := by
    refine ⟨2 * π * (A.lip * K), fun n => ?_⟩
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (f := fun θ => ‖deriv (A.map n ∘ γ) θ‖) (C := (A.lip * K : NNReal))
      (fun θ _ => by simpa using norm_deriv_le_of_lipschitz (hl n))
    rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
    exact (le_abs_self _).trans (by simp_all [mul_comm])
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  choose Wn hWn using fun n => transport_exists_of_lipschitz (A.map n ∘ γ) (hl n) E
  simp_rw [monodromyAt_eq hK hW, fun n => monodromyAt_eq (hl n) (hWn n)]
  exact monodromy_tendsto_of_tendstoUniformlyOn hK hl hc (fun n => congrArg (A.map n) hc)
    hunif hlength tendsto_const_nhds hW hWn

/-- If the analytic counting bound at a fixed energy exceeds `j` in the limit,
then the `j`th eigenvalue of the original domain is at most that energy. -/
private theorem le_of_bz_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (j : ℕ) {E : ℝ} (hE : 0 < E)
    (h : (j : ℝ) < (volume Ω).toReal * E / (4 * π) + ‖monodromyAt γ E - 1‖ / (2 * π)) :
    neumannEigenvalue Ω j ≤ ENNReal.ofReal E := by
  obtain ⟨A⟩ := exists_ballZarnescu hb hL
  let D n := A.map n '' Ω
  let α n := A.map n ∘ γ
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hl n := (A.lipschitzWith n).comp hK
  have hvol := (ENNReal.tendsto_toReal hb.measure_lt_top.ne).comp A.tendsto_volume
  have hU := bz_monodromy_tendsto hγ A E
  have hg : Tendsto (fun n => (volume (D n)).toReal * E / (4 * π) +
      ‖monodromyAt (α n) E - 1‖ / (2 * π)) atTop
      (𝓝 ((volume Ω).toReal * E / (4 * π) + ‖monodromyAt γ E - 1‖ / (2 * π))) :=
    ((hvol.mul_const _).div_const _).add ((hU.sub_const _).norm.div_const _)
  refine A.neumannEigenvalue_le_of_eventually_lt hb hL j hE ?_
  filter_upwards [hg.eventually (Ioi_mem_nhds h), eventually_boundaryParam_ballZarnescu hb hL hγ A]
    with n hn ⟨γ', hγ', τ, hτm, ⟨Kτ, hKτ⟩, hzero, hend, hcomp⟩
  obtain ⟨K', hK'⟩ := hγ'.lipschitz
  obtain ⟨W', hW'⟩ := transport_exists_of_lipschitz γ' hK' E
  have hmono : monodromyAt (α n) E = monodromyAt γ' E := by
    rw [monodromyAt_eq (hl n) (hcomp ▸ isTransport_comp hK' hτm hKτ hzero hend hW'),
      monodromyAt_eq hK' hW']
    simp [monodromy, hend]
  have hs := analytic_count (hb.subset (A.subset n)) (A.analytic n)
    ((A.map n).image Ω).symm.toHomotopyEquiv.simplyConnectedSpace hγ' E hE
  rw [← hmono] at hs
  by_contra! hbad
  have hc :=
    ENat.toENNReal_le.mpr (by
      simpa using (Set.encard_mono (fun _ hi => lt_of_lt_of_le hi hbad)).trans
        (encard_lt_le_of_monotone _ (neumannEigenvalue_monotone (D n)) j))
  exact (not_le.mpr ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (Nat.cast_nonneg j) hn)).mpr hn))
    (by simpa using hs.trans hc)


section

variable (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω)
include Ω hb hL hsc

/-- **Theorem 10.16 (strict Neumann Pólya inequality).** For every bounded simply connected
Lipschitz domain `Ω ⊂ ℝ²` and every integer `j ≥ 1`, `|Ω| μ_j(Ω) < 4π j`. -/
theorem strict_neumann_polya  (j : ℕ) (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) := by
  have hV : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hv := ENNReal.toReal_pos (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hV
  have hj' : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  let e := 4 * π * j / (volume Ω).toReal
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨γ, hγ⟩ := exists_boundaryParam hb hL hsc
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hU := norm_sub_one_pos (monodromyAt_ne_one hb hL hγ e he)
  have hm := continuousAt_monodromyAt hK (by simpa using hγ.periodic 0) he
  let q := fun E => (volume Ω).toReal * E / (4 * π) + ‖monodromyAt γ E - 1‖ / (2 * π)
  have hq : ContinuousAt q e := by fun_prop
  have harea : (volume Ω).toReal * e = 4 * π * j := by
    dsimp [e]
    field_simp
  have hlt : (j : ℝ) < q e := by
    dsimp [q]
    rw [harea, mul_div_cancel_left₀ _ (by positivity)]
    exact lt_add_of_pos_right _ (div_pos hU Real.two_pi_pos)
  have hI : ∀ᶠ E in 𝓝[<] e, E ∈ Set.Ioo 0 e := Ioo_mem_nhdsLT he
  obtain ⟨E, hE, hqE⟩ := (hI.and
    ((hq.tendsto.eventually (Ioi_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds)).exists
  calc
    volume Ω * neumannEigenvalue Ω j ≤ volume Ω * ENNReal.ofReal E := by
      gcongr
      exact le_of_bz_count hb hL hsc hγ j hE.1 hqE
    _ < ENNReal.ofReal (4 * π * j) := by
      rw [← ENNReal.ofReal_toReal hV, ← ENNReal.ofReal_mul hv.le, ← harea]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hv.le hE.1.le) |>.2
        (mul_lt_mul_of_pos_left hE.2 hv)

/-- **Theorem 10.16, counting form.** For every bounded simply connected Lipschitz domain
and every `E > 0`, `N_N(E) > |Ω| E / (4π)`. -/
theorem strict_neumann_polya_count  (E : ℝ) (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) :=
  count_of_eigen _ _ hb.measure_lt_top.ne (neumannEigenvalue_monotone Ω)
    (neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb) (strict_neumann_polya Ω hb hL hsc) E hE

end

end PolyaNeumann

/-!
Stable top-level entry points for automated audits and downstream users.
The original namespaced declarations above remain the canonical proof
statements; these aliases provide the same compact API as the companion
Dirichlet formalization.
-/

end
