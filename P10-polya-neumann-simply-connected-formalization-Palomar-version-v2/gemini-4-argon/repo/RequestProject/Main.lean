module

public import RequestProject.Poincare
public import RequestProject.Finite
public import RequestProject.Transport
public import RequestProject.Unitarity
public import RequestProject.CurveContinuity
public import RequestProject.AreaTrace
public import RequestProject.Driven
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import RequestProject.Phase
public import RequestProject.Transmutation
public import RequestProject.CutCorrection
public import RequestProject.Reparam
public import RequestProject.BoundaryOrigin
public import RequestProject.PeriodicForm
public import RequestProject.Coercivity
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Tactic
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

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- Lemma 3.3: the Neumann eigenvalues of a Lipschitz domain are finite. -/
local notation "Φ0" => neumannEigenvalue Ω

theorem neumannEigenvalue_lt_top  (hL : IsLipschitzDomain Ω) j :
    Φ0 j < ⊤ :=
  neumannEigenvalue_lt_top_of_isOpen hL.1.1 hL.1.2.nonempty j

/-! ### Boundary parametrization and transport (Section 10) -/

/-- External theorem E3 (planar Lipschitz boundaries), in the form used here: the boundary of a
bounded simply connected Lipschitz domain is a single Lipschitz Jordan curve. That is, `∂Ω` has
a Lipschitz `2π`-periodic parametrization `γ` that is injective on `[0, 2π)` and has image
`∂Ω`.
Proved from `isPreconnected_frontier_of_simplyConnected` (the boundary is connected,
`BoundaryConnected.lean`) and `exists_jordanParam_of_isPreconnected_frontier` (a connected
Lipschitz boundary is a single Lipschitz Jordan curve, obtained by walking along the boundary
through uniform Lipschitz charts, `BoundaryChart.lean`, `BoundaryWalk.lean`, `BoundaryLoop.lean`). -/
theorem exists_lipschitzJordanParam_topological  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      Set.InjOn γ (Set.Ico 0 (2 * π)) ∧ γ '' Set.Icc 0 (2 * π) = frontier Ω :=
  exists_jordanParam_of_isPreconnected_frontier hb hL
    (isPreconnected_frontier_of_simplyConnected hb hL hsc)

/-- Lemma 10.2: the Lipschitz transport of a boundary parametrization exists and is unique
on `[0, L]`. -/
local notation "Φ3" => IsBoundaryParam Ω γ

theorem transport_exists_unique   (hγ : Φ3) E :
    ∃ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W ∧
      ∀ W' : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W' → Set.EqOn W W' (Set.Icc 0 (2 * π)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  exact ⟨W, hW, fun W' hW' => transport_unique_of_lipschitz γ hK E hW hW'⟩

/-- The standard basis vectors of `ℓ²(ℕ₀)` are orthonormal. -/
lemma orthonormal_basisVec : Orthonormal ℂ basisVec := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [basisVec, lp.inner_single_left]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- Lemma 10.5: for every `E > 0`, `dim ker(V_E - I) ≤ dim ker(A_N - E) < ∞`; in particular
the monodromy satisfies `U_E ≠ I`. The finiteness of `dim ker(A_N - E)` is
`finiteDimensional_neumannEigenspace` (from Rellich compactness); if `U_E = I`, the fixed space
of `V_E` would be all of the infinite-dimensional space `ℓ²(ℕ₀)`. -/
theorem monodromy_ne_one  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) 
    (hγ : Φ3) E (hE : 0 < E) W
    (hW : IsTransport γ E W) : monodromy W ≠ 1 := by
  intro h
  obtain ⟨T, hT⟩ := fixedSpace_to_neumannEigenspace_of_reconstruction hγ hE hW (neumann_reconstruction_of_compatible hb hL hγ hE)
  haveI := finiteDimensional_neumannEigenspace hb hL E
  haveI : FiniteDimensional ℂ
      (LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2)) :=
    Module.Finite.of_injective T hT
  have htop : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) = ⊤ := by
    rw [show W (2 * π) = 1 by
      have h2 := congrArg ContinuousLinearMap.adjoint h
      rw [monodromy, ContinuousLinearMap.adjoint_adjoint] at h2
      rw [h2, ← ContinuousLinearMap.star_eq_adjoint, star_one], sub_self, ContinuousLinearMap.coe_zero]
    exact LinearMap.ker_zero
  rw [htop] at this
  exact (show ¬ FiniteDimensional ℂ Ell2 by
    intro h
    have := orthonormal_basisVec.linearIndependent.finite
    exact not_finite ℕ) (LinearEquiv.finiteDimensional Submodule.topEquiv)

/-! ### Smooth domains (Section 9) -/

/-- The real form of the left-hand side of the counting inequality. -/
lemma count_lhs_eq_ofReal  (hvol : volume Ω ≠ ⊤)  (hE : 0 ≤ E)
    (U : Ell2 →L[ℂ] Ell2) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖U - 1‖ / (2 * π)) =
      ENNReal.ofReal ((volume Ω).toReal * E / (4 * π) + ‖U - 1‖ / (2 * π)) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity : 0 < 4 * π),
    ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * π),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol]

/-- Proposition 7.10 (uniform Cayley bound and resonance rank), read on eigenvectors through
the Cayley correspondence (an eigenvalue `e^{it}` of `U_E`, `0 < t < 2π`, is the eigenvalue
`cot(t/2)` of the Cayley transform `K_E`). Let `E₀ > 0` have Neumann multiplicity `m`: the
number of indices `i` with `μ_i = E₀` (so `m = 0` if `E₀` is nonresonant). Then there are `A`
and `a > 0` such that at every nonresonant energy `E > 0` with `|E - E₀| < a`, every orthonormal
family of eigenvectors of `U_E` with eigenvalues `e^{it}`, `cot(t/2) > A`, has at most `m`
members (`rank 1_{(A,∞)}(K_E) ≤ m`; for `m = 0` this is `K_E ≤ A`).
Proved from the original smooth-domain Herglotz bound and the chosen-origin Cayley transfer
(`uniform_cayley_rank_bound_of_original_smooth_domain`). -/
local notation "Φ2" => monodromyAt γ

theorem uniform_cayley_rank_bound  (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) 
    (hγ : Φ3) E₀ (hE₀ : 0 < E₀) (m : ℕ)
    (hm : {i | Φ0 i = ENNReal.ofReal E₀}.encard = m) :
    ∃ A a : ℝ, 0 < a ∧ ∀ E, 0 < E → |E - E₀| < a →
      (∀ j, Φ0 j ≠ ENNReal.ofReal E) →
      CayleyRankBound (Φ2 E) A m := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨W₀, hW₀⟩ := transport_exists_of_lipschitz γ hK E₀
  exact uniform_cayley_rank_bound_of_original_smooth_domain hb hS hsc hγ E₀ hE₀ m hm (by
    rw [monodromyAt_eq hK hW₀]
    exact monodromy_ne_one hb hS.isLipschitzDomain hγ E₀ hE₀ W₀ hW₀)

/-- Lemma 9.3 (continuity of a cut logarithm), for the monodromy of a bounded smooth Jordan
domain: let `0 < ε < 2π` and let `[E₁, E₂] ⊂ (0, ∞)` be an interval on which `e^{iε}` (hence the
whole radial cut through it) avoids the spectrum of `U_E`. Then the cut phase count
`J_ε(E) = (E|Ω|/2 - tr(-i log_ε U_E)) / (2π)` takes the same value at `E₁` and `E₂`. Here the
trace is written as the multiplicity-weighted eigenvalue sum `∑_{z ≠ 1} mult(z) argCut ε z`.
Proved from `cutPhaseSum_monodromyAt_sub` and Green's formula `∫ b = 2|Ω|` (part of the
boundary parametrization). -/
theorem cutPhaseCount_const   (hγ : Φ3) 
    (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ) (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (Φ2 E)) :
    cutPhaseCount Ω γ ε E₂ = cutPhaseCount Ω γ ε E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have h := cutPhaseSum_monodromyAt_sub' hK hclosed hε0 hε E₁ E₂ h1 h12 hcut
  rw [show ∫ θ in 0..(2 * π), areaDensity γ θ = 2 * (volume Ω).toReal by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area] at h
  unfold cutPhaseCount
  rw [div_left_inj' (by positivity)]
  linarith

/-- Lemma 9.1 (absolute summability): for a bounded smooth Jordan domain and a nonresonant
energy `E > 0`, the multiplicity-weighted negative-branch phase sum
`∑_{z ∈ σ_p(U_E) \ {1}} Arg₋ z` is absolutely convergent. (The paper also shows that `M(E)` is an
integer; that part is not needed here.) Proved, as in the paper, from the finiteness of the
upper-semicircle eigenvalues (`upper_eigenvalues_finite`), the bound
`|Arg₋ z| ≤ (π/2)|z - 1|` on the lower semicircle and the trace-class property of `U_E - I`
(Lemma 4.7, `summable_eigenMult_monodromy`), which makes `∑ mult(z) |z - 1|` finite. -/
theorem phase_summable  (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω)  (hγ : Φ3) E
    (hE : 0 < E) (hnr : ∀ j, Φ0 j ≠ ENNReal.ofReal E) :
    Summable (phaseTerm (Φ2 E)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  have hfin : {z : ℂ | 0 < z.im ∧ ∃ v : Ell2, v ≠ 0 ∧ Φ2 E v = z • v}.Finite := by
    obtain ⟨K, hK⟩ := hγ.lipschitz
    have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
    obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
    obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ t : ℝ, 0 < t → t < 2 * π → ∀ v : Ell2, v ≠ 0 → Φ2 E v = Complex.exp (t * Complex.I) • v → Real.cot (t / 2) ≤ A := by
      obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E hE 0 (by
        rw [Nat.cast_zero, Set.encard_eq_zero]
        exact Set.eq_empty_of_forall_notMem fun i hi => hnr i hi)
      exact ⟨A, fun t ht0 ht v hv hUv =>
        (hA E hE (by rw [sub_self, abs_zero]; exact ha) hnr).cot_le ht0 ht hv hUv⟩
    rw [monodromyAt_eq hK hW] at hA ⊢
    exact upper_eigen_finite_of_cot_bound (by
      rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
      exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩))
      (isCompactOperator_monodromy_sub_one hK hclosed hE.le hW)
      (summable_eigenMult_monodromy hK hclosed hE.le hW) A hA
  rw [monodromyAt_eq hK hW] at hfin ⊢
  exact summable_phaseTerm_of_upper_finite (by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)) hfin
    (summable_eigenMult_monodromy hK (by simpa using hγ.periodic 0) hE.le hW)

/-- Lemma 9.4 (constancy away from the Neumann spectrum): `M` is constant on every interval
`[E₁, E₂] ⊆ (0, ∞)` containing no Neumann eigenvalue. Proved, as in the paper: locally the
uniform Cayley bound `K_E ≤ A` (`uniform_cayley_rank_bound`) excludes an arc
`{e^{it} : 0 < t ≤ ε}` from the spectrum of `U_E`, so `M = J_ε` there, and `J_ε` is locally
constant (`cutPhaseCount_const`); local constancy on an interval gives constancy. -/
local notation "Φ1" => phaseCount Ω γ

theorem phaseCount_const  (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω)  (hγ : Φ3) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hno : ∀ j, ∀ E ∈ Set.Icc E₁ E₂, Φ0 j ≠ ENNReal.ofReal E) :
    Φ1 E₂ = Φ1 E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  -- local constancy
  have hloc : ∀ E₀ ∈ Set.Icc E₁ E₂, ∃ a > 0, ∀ E ∈ Set.Icc E₁ E₂, ∀ E' ∈ Set.Icc E₁ E₂,
      |E - E₀| < a → |E' - E₀| < a → E ≤ E' → Φ1 E' = Φ1 E := by
    intro E₀ hE₀
    obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E₀ (h1.trans_le hE₀.1) 0 (by
      rw [Nat.cast_zero, Set.encard_eq_zero]
      exact Set.eq_empty_of_forall_notMem fun i hi => hno i E₀ hE₀ hi)
    obtain ⟨ε, hε0, hεπ, hεA⟩ := exists_cot_half_gt A
    have hnoarc : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a → ∀ t, 0 < t → t ≤ ε → ∀ v : Ell2,
        v ≠ 0 → Φ2 E v ≠ Complex.exp (t * Complex.I) • v := fun E hE hEa =>
      (hA E (h1.trans_le hE.1) hEa (fun j => hno j E hE)).no_arc_eigen hεπ hεA
    have hJ : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a →
        Φ1 E = cutPhaseCount Ω γ ε E := by
      intro E hE hEa
      rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_phaseSum (monodromyAt_mem_unitary hK E)
        (isCompactOperator_monodromyAt_sub_one hK hclosed (h1.trans_le hE.1).le)
        (fun t ht0 htε => hnoarc E hE hEa t ht0 htε.le)]
    refine ⟨a, ha, fun E hE E' hE' hEa hE'a hEE' => ?_⟩
    rw [hJ E hE hEa, hJ E' hE' hE'a]
    refine cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E E'
      (h1.trans_le hE.1) hEE' (fun F hF => ?_)
    have hFI : F ∈ Set.Icc E₁ E₂ := ⟨hE.1.trans hF.1, hF.2.trans hE'.2⟩
    exact exp_mul_I_notMem_spectrum (isCompactOperator_monodromyAt_sub_one hK hclosed
      (h1.trans_le hFI.1).le) hε0 hεπ (fun v hv => hnoarc F hFI (by
        rw [abs_lt] at hEa hE'a ⊢; constructor <;> linarith [hF.1, hF.2]) ε hε0 le_rfl v hv)
  -- constancy on the interval
  let f : Set.Icc E₁ E₂ → ℝ := fun E => Φ1 E
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨a, ha, hx⟩ := hloc x x.2
    filter_upwards [Metric.ball_mem_nhds x ha] with y hy
    have hy' : |(y : ℝ) - x| < a := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hy; exact hy
    have hx0 : |(x : ℝ) - x| < a := by rw [sub_self, abs_zero]; exact ha
    rcases le_total (y : ℝ) x with h | h
    · exact (hx y y.2 x x.2 hy' hx0 h).symm
    · exact hx x x.2 y y.2 hx0 hy' h
  haveI : PreconnectedSpace (Set.Icc E₁ E₂) := Subtype.preconnectedSpace isPreconnected_Icc
  exact hf.apply_eq_of_preconnectedSpace ⟨E₂, h12, le_rfl⟩ ⟨E₁, le_rfl, h12⟩

/-- Theorem 9.7 at nonresonant energies (Lemma 9.2 combined with the phase count): for a
bounded smooth Jordan domain and a nonresonant `E > 0`,
`N_N(E) ≥ E |Ω| / (4π) + ‖U_E - I‖ / (2π)`. `U_E - I` is compact (Lemma 4.7), so if
`U_E ≠ I` its norm is `|z - 1|` for an eigenvalue `z ≠ 1` of `U_E` (Lemma 9.2). -/
theorem smooth_count_nonresonant  (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) 
    (hγ : Φ3) E (hE : 0 < E)
    (hnr : ∀ j, Φ0 j ≠ ENNReal.ofReal E) W
    (hW : IsTransport γ E W) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖monodromy W - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  obtain ⟨ι, z, hz, h1, hall, hs, hM⟩ : ∃ (ι : Type) (z : ι → ℂ), (∀ i, ‖z i‖ = 1) ∧ (∀ i, z i ≠ 1) ∧ (∀ (c : ℂ) (v : Ell2), v ≠ 0 → monodromy W v = c • v → c ≠ 1 → ∃ i, z i = c) ∧ Summable (fun i => argNeg (z i)) ∧ ENNReal.ofReal (((volume Ω).toReal * E / 2 - ∑' i, argNeg (z i)) / (2 * π)) ≤ (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
    obtain ⟨K, hK⟩ := hγ.lipschitz
    have hUunit : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
      rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
      exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
    have hs := phase_summable hb hS hsc hγ E hE hnr
    rw [monodromyAt_eq hK hW] at hs
    obtain ⟨ι, z, hz, h1, hall, hsum, htsum⟩ := exists_eigen_family hUunit
      (isCompactOperator_monodromy_sub_one hK (by simpa using hγ.periodic 0) hE.le hW) hs
    refine ⟨ι, z, hz, h1, hall, hsum, ?_⟩
    have h : ENNReal.ofReal (Φ1 E) ≤ (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
      have hL := hS.isLipschitzDomain
      have hfin : ∀ j, Φ0 j ≠ ⊤ := fun j => (neumannEigenvalue_lt_top hL j).ne
      set lam : ℕ → ℝ := fun j => (Φ0 j).toReal with hlam
      have hμ : ∀ j, Φ0 j = ENNReal.ofReal (lam j) := fun j =>
        (ENNReal.ofReal_toReal (hfin j)).symm
      have hne : ∀ j t, 0 ≤ t → (Φ0 j ≠ ENNReal.ofReal t ↔ lam j ≠ t) := by
        intro j t ht
        rw [hμ j, ne_eq, ne_eq, ENNReal.ofReal_eq_ofReal_iff ((fun j => ENNReal.toReal_nonneg) j) ht]
      have hlt : ∀ t, 0 < t → {j | Φ0 j < ENNReal.ofReal t} =
          {j | lam j < t} := by
        intro t ht
        ext j
        simp
        rw [hμ j, ENNReal.ofReal_lt_ofReal_iff ht]
      have hcount : neumannCount Ω (ENNReal.ofReal E) = {j | lam j < E}.encard := by
        rw [neumannCount, hlt E hE]
      by_cases hinf : {j | lam j < E}.Finite
      swap
      · rw [hcount, Set.encard_eq_top_iff.mpr hinf, ENat.toENNReal_top]; exact le_top
      have key := phase_le_count_of_jumps lam (by
        simp [hlam, neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb]) (Φ1)
        (by
          obtain ⟨δ, hδ, h⟩ : ∃ δ > 0, ∀ E, 0 < E → E < δ → Φ1 E = 1 := by
            obtain ⟨K, hK⟩ := hγ.lipschitz
            have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
            obtain ⟨Cq, hCq0, hT⟩ := exists_linear_traceBound_monodromyAt hK hclosed
            obtain ⟨δr, hδr, hrank⟩ : ∃ δ > 0, ∀ E, 0 < E → E < δ → CayleyRankBound (Φ2 E) 0 1 := by
              obtain ⟨δ, hδ, hA⟩ := small_energy_herglotz_bound' hb hS.isLipschitzDomain hγ
              obtain ⟨K, hK⟩ := hγ.lipschitz
              refine ⟨δ, hδ, fun E hE hEδ => ?_⟩
              obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
              obtain ⟨L, hL⟩ := hA E hE hEδ W hW
              rw [monodromyAt_eq hK hW]
              exact cayleyRankBound_of_herglotzForm_bound hK (by simpa using hγ.periodic 0) hW 0 0 le_rfl L
                (fun a ha hLa => by rw [zero_mul, neg_zero]; exact hL a ha hLa)
            set v := (volume Ω).toReal with hv
            have hvpos := ENNReal.toReal_pos
              (hS.1.1.measure_pos volume hS.1.2.nonempty).ne' hb.measure_lt_top.ne
            have hpi := Real.pi_pos
            set δ := min δr (1 / (Cq + 1)) with hδ
            have hcut : ∀ E, 0 < E → E < δ →
                Complex.exp (π * Complex.I) ∉ spectrum ℂ (Φ2 E) := by
              intro E hE hEδ hmem
              rw [Complex.exp_pi_mul_I] at hmem
              obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum
                (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) hmem (by norm_num)
              exact not_eigen_neg_one_of_traceBound (monodromyAt_mem_unitary hK E)
                (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
                ((show ∀ E, 0 < E → E < δ → Cq * E < 2 by
                  intro E hE hEδ
                  have h1 := hEδ.trans_le (min_le_right _ _)
                  rw [lt_div_iff₀ (by positivity)] at h1
                  nlinarith) E hE hEδ) hw0 hw
            set c := (v / 2 + π / 2 * Cq) / (2 * π) with hc
            have hJ0 : ∀ E, 0 < E → E < δ → cutPhaseCount Ω γ π E = 0 := by
              intro E hE hEδ
              exact abs_nonpos_iff.mp (ge_of_tendsto (by
                have h : Tendsto (fun F => c * F) (𝓝 0) (𝓝 (c * 0)) :=
                  tendsto_id.const_mul c
                rw [mul_zero] at h
                exact h.mono_left nhdsWithin_le_nhds) (show ∀ᶠ F in 𝓝[>] 0, |cutPhaseCount Ω γ π E| ≤ c * F by
                  filter_upwards [Ioo_mem_nhdsGT hE] with F hF
                  rw [cutPhaseCount_const hγ hpi (by linarith) F E hF.1 hF.2.le
                    (fun G hG => hcut G (hF.1.trans_le hG.1) (hG.2.trans_lt hEδ))]
                  exact (show ∀ E, 0 < E → E < δ → |cutPhaseCount Ω γ π E| ≤ c * E by
                    intro E hE hEδ
                    obtain ⟨-, hP⟩ := cutPhaseSum_pi_bound (monodromyAt_mem_unitary hK E)
                      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
                    rw [cutPhaseCount, abs_div, abs_of_pos (by positivity : 0 < 2 * π),
                      div_le_iff₀ (by positivity)]
                    have h1 : |v * E / 2 - cutPhaseSum π (Φ2 E)| ≤
                        v * E / 2 + π / 2 * (Cq * E) := by
                      have := abs_sub (v * E / 2) (cutPhaseSum π (Φ2 E))
                      rw [abs_of_pos (by positivity : 0 < v * E / 2)] at this
                      linarith
                    calc _ ≤ _ := h1
                      _ = _ := by rw [hc]; field_simp) F hF.1 (hF.2.trans hEδ)))
            refine ⟨δ, (lt_min hδr (by positivity) : 0 < δ), fun E hE hEδ => ?_⟩
            set U := Φ2 E with hUdef
            have hUu : U ∈ unitary (Ell2 →L[ℂ] Ell2) := monodromyAt_mem_unitary hK E
            have hUc := isCompactOperator_monodromyAt_sub_one hK hclosed hE.le
            obtain ⟨hsa, hle⟩ := arcCount_le (ε := π) (A := 0) hUu hUc (by linarith)
              (fun t ht0 htπ => by
                rw [Real.cot_eq_cos_div_sin]
                exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
                  (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))
              (hrank E hE (hEδ.trans_le (min_le_left _ _)))
            obtain ⟨hcs, -⟩ := cutPhaseSum_pi_bound hUu hUc (hT E hE.le)
            have hdec := cutPhaseSum_eq_add (by
              rw [show phaseTerm U = fun z => cutPhaseTerm π U z - 2 * π * arcTerm π U z by
                funext z; rw [cutPhaseTerm_eq]; ring]; exact hcs.sub (hsa.mul_left _)) hsa
            have hJ := hJ0 E hE hEδ
            have hM : Φ1 E = cutPhaseCount Ω γ π E + arcCount π U := by
              rw [phaseCount, cutPhaseCount, ← hUdef, hdec]; field_simp; ring
            have hP : cutPhaseSum π U = v * E / 2 := by
              rw [cutPhaseCount, div_eq_zero_iff] at hJ
              rcases hJ with h | h
              · linarith
              · linarith
            rw [hM, hJ0 E hE hEδ, zero_add]
            exact le_antisymm (by exact_mod_cast hle) (by
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
                  · exact absurd rfl hz
                have h2 : arcTerm π U z ≤ arcCount π U :=
                  hsa.le_tsum z (fun j _ => arcTerm_nonneg π U j)
                linarith
              have hnp : cutPhaseSum π U ≤ 0 := by
                refine tsum_nonpos fun z => ?_
                rw [cutPhaseTerm_eq, hall z, mul_zero, add_zero, phaseTerm]
                exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (argNeg_nonpos _)
              have : 0 < v * E / 2 := by positivity
              linarith)
          exact ⟨δ, hδ, fun E hE hEδ _ => (h E hE hEδ).le⟩)
        (by
          intro E₁ E₂ h1 h12 hno
          refine (phaseCount_const hb hS hsc hγ E₁ E₂ h1 h12 fun j t ht => ?_).le
          rw [hne j t (h1.le.trans ht.1)]
          rintro rfl
          exact hno j ht)
        (by
          intro j hj m hm
          have hset : {i | Φ0 i = Φ0 j} = {i | lam i = lam j} := by
            ext i
            simp
            exact ENNReal.toReal_eq_toReal_iff' (hfin i) (hfin j) |>.symm
          obtain ⟨δ, hδ, h⟩ : ∃ δ > 0, ∀ E₁ E₂, 0 < E₁ → (Φ0 j).toReal - δ < E₁ → E₁ < (Φ0 j).toReal → (Φ0 j).toReal < E₂ → E₂ < (Φ0 j).toReal + δ → (∀ i, Φ0 i ≠ ENNReal.ofReal E₁) → (∀ i, Φ0 i ≠ ENNReal.ofReal E₂) → Φ1 E₂ ≤ Φ1 E₁ + m := by
            obtain ⟨K, hK⟩ := hγ.lipschitz
            have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
            have hfin := (neumannEigenvalue_lt_top hS.isLipschitzDomain j).ne
            set μ := (Φ0 j).toReal with hμdef
            have hμ0 := ENNReal.toReal_pos (show 0 < Φ0 j by
              rw [hμ j]; exact ENNReal.ofReal_pos.mpr hj).ne' hfin
            obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ μ hμ0 m (by
              rw [hμdef, ENNReal.ofReal_toReal hfin]; exact (hset ▸ hm))
            obtain ⟨ε₀, hε₀, hε₀π, hε₀A⟩ := exists_cot_half_gt A
            set S := {t | t ∈ Set.Ioo 0 ε₀ ∧ ∃ v : Ell2, v ≠ 0 ∧
              Φ2 μ v = Complex.exp (t * Complex.I) • v} with hSdef
            obtain ⟨ε, ⟨hε0, hεε₀⟩, hεS⟩ : (Set.Ioo 0 ε₀ \ S).Nonempty := by
              by_contra hne
              rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hne
              have h0 := measure_mono_null hne ((show S.Countable by
                obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK μ
                have hsum := summable_eigenMult_monodromy hK hclosed hμ0.le hW
                rw [← monodromyAt_eq hK hW] at hsum
                refine Set.MapsTo.countable_of_injOn (f := fun t => Complex.exp (t * Complex.I))
                  (t := Subtype.val '' Function.support
                    (fun z : {z : ℂ // z ≠ 1} => (eigenMult (Φ2 μ) z : ℝ) * ‖(z : ℂ) - 1‖))
                  ?_ ?_ (hsum.countable_support.image _)
                · rintro t ⟨⟨ht0, htε⟩, v, hv0, hv⟩
                  have hne : Complex.exp (t * Complex.I) ≠ 1 := by
                    intro h1
                    have := congrArg Complex.im h1
                    rw [Complex.exp_ofReal_mul_I_im, Complex.one_im] at this
                    linarith [Real.sin_pos_of_pos_of_lt_pi ht0 (htε.trans hε₀π)]
                  refine ⟨⟨_, hne⟩, ?_, rfl⟩
                  haveI := finiteDimensional_eigenspace
                    (isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le) hne
                  have hn := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
                  exact (mul_pos (by exact_mod_cast (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, fun h => hv0 (by simpa using h)⟩ : 0 < eigenMult (Φ2 μ) (Complex.exp (t * Complex.I)))) hn).ne'
                · intro s hs t ht hst
                  have := congrArg Complex.arg hst
                  simp only at this
                  rwa [Complex.arg_exp_mul_I, Complex.arg_exp_mul_I, (toIocMod_eq_self _).mpr,
                    (toIocMod_eq_self _).mpr] at this
                  all_goals constructor <;> linarith [hs.1.1, hs.1.2, ht.1.1, ht.1.2]).measure_zero MeasureTheory.volume)
              rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h0
              linarith
            have hεπ : ε < π := hεε₀.trans hε₀π
            have hspecμ :=
              exp_mul_I_notMem_spectrum (isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le) hε0 hεπ
                (fun v hv h => hεS ⟨⟨hε0, hεε₀⟩, v, hv, h⟩)
            obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp (by
              rw [spectrum.mem_iff, not_not] at hspecμ
              exact (continuousAt_const.sub (continuousAt_monodromyAt hK hclosed hμ0)).preimage_mem_nhds
                (Units.isOpen.mem_nhds hspecμ))
            refine ⟨min a δ₁, lt_min ha hδ₁, ?_⟩
            intro E₁ E₂ hE₁0 hE₁lo hE₁hi hE₂lo hE₂hi hnr₁ hnr₂
            have hdec : ∀ E, 0 < E → |E - μ| < a → (∀ i, Φ0 i ≠ ENNReal.ofReal E) →
                Φ1 E = cutPhaseCount Ω γ ε E + arcCount ε (Φ2 E) ∧
                  arcCount ε (Φ2 E) ≤ m := by
              intro E hE hEa hnr
              obtain ⟨hsa, hle⟩ := arcCount_le (monodromyAt_mem_unitary hK E)
                (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (by linarith [Real.pi_pos])
                (fun t ht0 htε => lt_of_lt_of_le (lt_of_lt_of_le hε₀A (cot_half_le_cot_half hε0 hεε₀.le hε₀π)) (cot_half_le_cot_half ht0 htε.le hεπ))
                (hA E hE hEa hnr)
              refine ⟨?_, hle⟩
              rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_add (phase_summable hb hS hsc hγ E hE hnr) hsa]
              field_simp
              ring
            obtain ⟨h1eq, -⟩ := hdec E₁ hE₁0 (by
              rw [abs_lt]; constructor <;> linarith [min_le_left a δ₁]) hnr₁
            obtain ⟨h2eq, h2le⟩ := hdec E₂ (by linarith) (by
              rw [abs_lt]; constructor <;> linarith [min_le_left a δ₁]) hnr₂
            rw [h1eq, h2eq, (cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E₁ E₂ hE₁0 (by linarith) (by
              intro E hE
              rw [spectrum.mem_iff, not_not]
              exact (hball (by
                rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                constructor <;> linarith [min_le_right a δ₁, hE.1, hE.2]))))]
            linarith [arcCount_nonneg ε (Φ2 E₁)]
          refine ⟨δ, hδ, fun E₁ E₂ h1 h2 h3 h4 h5 h6 h7 => h E₁ E₂ h1 h2 h3 h4 h5 ?_ ?_⟩
          · intro i; rw [hne i E₁ h1.le]; exact h6 i
          · intro i; rw [hne i E₂ (h1.trans (h3.trans h4)).le]; exact h7 i)
        E hE (fun j => (hne j E hE.le).mp (hnr j)) hinf
      rw [hcount, ← hinf.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal key
    rwa [phaseCount, monodromyAt_eq hK hW, ← htsum] at h
  obtain ⟨K, hK⟩ := hγ.lipschitz
  rw [count_lhs_eq_ofReal hb.measure_lt_top.ne hE.le]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hM
  rw [mul_comm ((volume Ω).toReal) E]
  exact (phase_integer_ge hz h1 hs E (volume Ω).toReal _ (by
    by_cases hU1 : monodromy W = 1
    · left; rw [hU1, sub_self, norm_zero]
    · right
      obtain ⟨c, v, hv0, hv, hc1, hcn⟩ := exists_eigenvalue_norm_sub_one (by
        rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
        exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩))
        (isCompactOperator_monodromy_sub_one hK (by simpa using hγ.periodic 0) hE.le hW) hU1
      obtain ⟨i, rfl⟩ := hall c v hv0 hv hc1
      exact ⟨i, hcn⟩))

/-- Theorem 9.7 (quantitative smooth counting inequality): for a bounded smooth Jordan
domain and every `E > 0`, `N_N(E) ≥ E |Ω| / (4π) + ‖U_E - I‖ / (2π)`. Proved, as in the paper,
from the nonresonant case by approaching `E` from below through nonresonant energies, using
the continuity of `E ↦ U_E` (Lemma 4.7). -/
theorem smooth_count  (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω)  (hγ : Φ3) E
    (hE : 0 < E) W (hW : IsTransport γ E W) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖monodromy W - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  classical
  obtain ⟨K, hK⟩ := hγ.lipschitz
  choose Ws hWs using fun E' => transport_exists_of_lipschitz γ hK E'
  set N := neumannCount Ω (ENNReal.ofReal E) with hNdef
  by_cases hN : N = ⊤
  · rw [hN, ENat.toENNReal_top]; exact le_top
  set T := {j : ℕ | Φ0 j < ENNReal.ofReal E} with hTdef
  have hN' : (N : ENNReal) ≠ ⊤ := by simpa using hN
  have hvol : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  -- the real form of the left-hand side
  set g : ℝ → ℝ := fun E' => (volume Ω).toReal * E' / (4 * π) +
    ‖monodromy (Ws E') - 1‖ / (2 * π) with hg
  -- nonresonant energies just below `E`
  have hev2 : ∀ᶠ E' in 𝓝[<] E, ∀ j ∈ T, (Φ0 j).toReal < E' :=
    (Set.encard_ne_top_iff.mp hN).eventually_all.mpr fun j hj => by
      have hlt :=
        (ENNReal.toReal_lt_toReal (ne_top_of_lt hj) ENNReal.ofReal_ne_top).mpr hj |>.trans_le
          (by rw [ENNReal.toReal_ofReal hE.le])
      exact Ioo_mem_nhdsLT hlt |> Filter.mem_of_superset <| fun x hx => hx.1
  -- continuity of `g` at `E`
  rw [count_lhs_eq_ofReal hvol hE.le, ← (show monodromy (Ws E) = monodromy W by
    unfold monodromy
    rw [transport_unique_of_lipschitz γ hK E (hWs E) hW ⟨by positivity, le_rfl⟩])]
  exact (ENNReal.ofReal_le_iff_le_toReal hN').mpr (le_of_tendsto ((show ContinuousAt g E by
    exact ((continuous_const.mul continuous_id).div_const _).continuousAt.add
      ((((hasDerivAt_monodromy_energy hK (by simpa using hγ.periodic 0) hWs hE).continuousAt).sub continuousAt_const).norm.div_const _)).tendsto.mono_left nhdsWithin_le_nhds) (by
    filter_upwards [Ioo_mem_nhdsLT hE, hev2] with E' hE' hT'
    have hlt :=
      (ENNReal.ofReal_lt_ofReal_iff hE).mpr hE'.2
    have h := smooth_count_nonresonant hb hS hsc hγ E' hE'.1 (by
      intro j hj
      have := hT' j (by
        show Φ0 j < _
        rw [hj]; exact hlt)
      rw [hj, ENNReal.toReal_ofReal hE'.1.le] at this
      exact lt_irrefl _ this) (Ws E') (hWs E')
    rw [show neumannCount Ω (ENNReal.ofReal E') = N by
      rw [hNdef, neumannCount, neumannCount]
      congr 1
      ext j
      simp
      constructor
      · intro h; exact h.trans hlt
      · intro h
        rw [← ENNReal.ofReal_toReal (ne_top_of_lt h)]
        exact (ENNReal.ofReal_lt_ofReal_iff hE'.1).mpr (hT' j h), count_lhs_eq_ofReal hvol hE'.1.le] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hN').mp h))

/-- Corollary 9.8 (quantitative smooth eigenvalue inequality): for a bounded smooth Jordan
domain and `j ≥ 1`, `|Ω| μ_j + 2 ‖U_{μ_j} - I‖ ≤ 4π j`. -/
theorem smooth_eigen  (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω)  (hγ : Φ3) j
    (hj : 1 ≤ j) W
    (hW : IsTransport γ (Φ0 j).toReal W) :
    volume Ω * Φ0 j + ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≤
      ENNReal.ofReal (4 * π * j) := by
  have hL := hS.isLipschitzDomain
  have hfin := (neumannEigenvalue_lt_top hL j).ne
  have h := smooth_count hb hS hsc hγ _ (ENNReal.toReal_pos (neumannEigenvalue_pos hb hL j hj).ne' hfin) W hW
  rw [ENNReal.ofReal_toReal hfin] at h
  have h3 := mul_le_mul_left (h.trans (by
    simpa [neumannCount] using (ENat.toENNReal_le.mpr (encard_lt_le_of_monotone _ (neumannEigenvalue_monotone Ω) j)))) (ENNReal.ofReal (4 * π))
  rw [add_mul, ENNReal.div_mul_cancel (by
    simp; positivity) ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul (by positivity)] at h3
  convert h3 using 2
  · congr 1; field_simp; ring
  · rw [mul_comm (j : ENNReal), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-! ### Lipschitz domains (Section 10) -/

/-- The data produced by the smooth approximation of Section 10 (Definition 10.8), together
with the properties of it used in the limit argument. For a bounded simply connected Lipschitz
domain `Ω` with boundary parametrization `γ`:
* smooth bounded simply connected domains `Ω_n = f_n(Ω)` with boundary parametrizations `γ'_n`
  (External theorem BZ);
* the curves `γ_n = f_n ∘ γ - f_n(γ(0))`, closed and uniformly Lipschitz, converging uniformly
  to `γ` with bounded lengths, whose monodromies agree with those of `γ'_n`
  (Lemma 10.14, via Lemma 10.3);
* densities `ρ_n = |det Df_n|`, uniformly bounded and converging to `1` a.e., with
  `|Ω_n| = ∫_Ω ρ_n` (Lemma 10.9 and change of variables);
* pulled-back forms `q_n`, `m_n` on `L²(Ω)`: `μ_j(Ω_n)` obeys the min–max bound for
  `q_n / m_n` on subspaces of `H¹(Ω)` (Lemma 10.10), `q_n → q_Ω` and `m_n → 1` uniformly on
  unit spheres of finite-dimensional subspaces of `H¹(Ω)` (Lemma 10.11), and along subsequences
  with convergent eigenvalues there are orthonormal limits of the eigenfunctions
  (the compactness part of Lemma 10.13). -/
structure SmoothApproximation (Ω : Set ℂ) (γ : ℝ → ℂ) where
  /-- The approximating smooth domains `Ω_n`. -/
  dom : ℕ → Set ℂ
  dom_bounded : ∀ n, Bornology.IsBounded (dom n)
  dom_smooth : ∀ n, IsSmoothDomain (dom n)
  dom_simplyConnected : ∀ n, SimplyConnectedSpace (dom n)
  /-- Boundary parametrizations `γ'_n` of `∂Ω_n`. -/
  param : ℕ → ℝ → ℂ
  param_isBoundaryParam : ∀ n, IsBoundaryParam (dom n) (param n)
  /-- The transported curves `γ_n = f_n ∘ γ - f_n(γ(0))`. -/
  curve : ℕ → ℝ → ℂ
  curveLip : ℕ → NNReal
  curve_lipschitz : ∀ n, LipschitzWith (curveLip n) (curve n)
  curve_closed : ∀ n, curve n (2 * π) = curve n 0
  curve_tendsto : TendstoUniformlyOn curve γ atTop (Set.Icc 0 (2 * π))
  curve_length : ∃ B, ∀ n, ∫ θ in 0..(2 * π), ‖deriv (curve n) θ‖ ≤ B
  monodromy_eq : ∀ n (E : ℝ) (W W' : ℝ → Ell2 →L[ℂ] Ell2), IsTransport (curve n) E W →
    IsTransport (param n) E W' → monodromy W = monodromy W'
  /-- The densities `ρ_n = |det Df_n|`. -/
  density : ℕ → ℂ → ℝ
  densityBound : ℝ
  density_aestronglyMeasurable : ∀ n, AEStronglyMeasurable (density n) (volume.restrict Ω)
  density_bound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |density n w| ≤ densityBound
  density_tendsto : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => density n w) atTop (𝓝 1)
  volume_dom : ∀ n, volume (dom n) = ENNReal.ofReal (∫ w in Ω, density n w)
  /-- The pulled-back Neumann forms `q_n[u,u]` and masses `m_n[u,u]`. -/
  formQ : ℕ → L2 Ω → ℝ
  formM : ℕ → L2 Ω → ℝ
  minmax : ∀ (j n : ℕ) (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 →
    (S : Set (L2 Ω)) ⊆ H1 Ω → neumannEigenvalue (dom n) j ≤
      ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1), ENNReal.ofReal (formQ n u / formM n u)
  formQ_tendsto : ∀ S : Submodule ℂ (L2 Ω), FiniteDimensional ℂ S → (S : Set (L2 Ω)) ⊆ H1 Ω →
    TendstoUniformlyOn formQ (fun u => (neumannEnergy Ω u).toReal) atTop
      ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1)
  formM_tendsto : ∀ S : Submodule ℂ (L2 Ω), FiniteDimensional ℂ S → (S : Set (L2 Ω)) ⊆ H1 Ω →
    TendstoUniformlyOn formM (fun _ => 1) atTop ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1)
  limits : ∀ (j : ℕ) (φ : ℕ → ℕ), StrictMono φ → ∀ lam : ENNReal, lam < ⊤ →
    Tendsto (fun n => neumannEigenvalue (dom (φ n)) j) atTop (𝓝 lam) →
    ∃ u : Fin (j + 1) → L2 Ω, Orthonormal ℂ u ∧ ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2)

/-- **Theorem 10.16 (strict Neumann Pólya inequality).** For every bounded simply connected
Lipschitz domain `Ω ⊂ ℝ²` and every integer `j ≥ 1`, `|Ω| μ_j(Ω) < 4π j`. -/
theorem strict_neumann_polya Ω (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) j (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) := by
  have hfin := (neumannEigenvalue_lt_top hL j).ne
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℂ, IsBoundaryParam Ω γ := by
    obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him, harea⟩ := (show ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧ Set.InjOn γ (Set.Ico 0 (2 * π)) ∧ γ '' Set.Icc 0 (2 * π) = frontier Ω ∧ |∫ θ in 0..(2 * π), signedAreaDensity γ θ| = 2 * (volume Ω).toReal by
      obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him, σ, hσ, hin, hout⟩ :=
        (show ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧ Set.InjOn γ (Set.Ico 0 (2 * π)) ∧ γ '' Set.Icc 0 (2 * π) = frontier Ω ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (∀ z ∈ Ω, windingNumber γ z = σ) ∧ ∀ z, z ∉ closure Ω → windingNumber γ z = 0 by
          obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him⟩ := exists_lipschitzJordanParam_topological hb hL hsc
          exact ⟨γ, ⟨K, hK⟩, hper, hinj, him, windingNumber_pm_one_of_jordan hb hL hK hper hinj him
            (by
              obtain ⟨γ, ⟨K, hK⟩, -, -, him⟩ := exists_lipschitzJordanParam_topological hb hL hsc
              refine isConnected_compl_closure_of_frontier hb hL ?_
              rw [← him]
              exact isPreconnected_Icc.image γ hK.continuous.continuousOn)⟩)
      refine ⟨γ, ⟨K, hK⟩, hper, hinj, him, ?_⟩
      rw [integral_signedAreaDensity_of_winding hL.1.1 hb hK him σ hin hout, abs_mul, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg]
      rcases hσ with rfl | rfl <;> norm_num)
    obtain ⟨γ1, ⟨K1, hK1⟩, hper1, hinj1, him1, ⟨c, hc, hspeed⟩, harea1, -⟩ :=
      exists_constSpeed_reparam hK hper hinj
    have hv : 0 ≤ 2 * (volume Ω).toReal := by positivity
    rcases (abs_eq hv).mp harea with hpos | hneg
    · exact ⟨γ1, ⟨⟨K1, hK1⟩, hper1, hinj1, him1.trans him, ⟨c, hc, hspeed⟩,
        show ∫ θ in 0..(2 * π), signedAreaDensity γ1 θ = _ by rw [harea1, hpos]⟩⟩
    · obtain ⟨γ2, hK2, hper2, hinj2, him2, hspeed2, harea2⟩ :=
        exists_reverse_param hK1 hper1 hinj1 hspeed
      exact ⟨γ2, ⟨⟨K1, hK2⟩, hper2, hinj2, him2.trans (him1.trans him), ⟨c, hc, hspeed2⟩,
        show ∫ θ in 0..(2 * π), signedAreaDensity γ2 θ = _ by
          rw [harea2, harea1, hneg, neg_neg]⟩⟩
  obtain ⟨W, hW, -⟩ := transport_exists_unique hγ (neumannEigenvalue Ω j).toReal
  have hU := norm_sub_one_pos (monodromy_ne_one hb hL hγ _ (ENNReal.toReal_pos (neumannEigenvalue_pos hb hL j hj).ne' hfin) W hW)
  exact lt_of_lt_of_le (ENNReal.lt_add_right (ENNReal.mul_ne_top hb.measure_lt_top.ne hfin) (by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)) (show volume Ω * neumannEigenvalue Ω j + ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≤ ENNReal.ofReal (4 * π * j) by
      obtain ⟨A⟩ : Nonempty (SmoothApproximation Ω γ) := by
        obtain ⟨A⟩ := exists_ballZarnescu hb hL
        obtain ⟨formQ, hmin, hQ, hlim⟩ := exists_pullbackForms hb hL A
        obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_boundaryParam_ballZarnescu hb hL hγ A)
        choose γ' hγ' τ hτm hτL hτ0 hτ2 hτc using fun n => hN (n + N) (Nat.le_add_left N n)
        obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
        have hΩo := hL.1.1
        have hfr : ∀ θ, γ θ ∈ closure Ω := by
          intro θ
          have h1 : γ θ ∈ γ '' Set.Icc 0 (0 + 2 * π) := by
            rw [hγ.periodic.image_Icc Real.two_pi_pos]; exact Set.mem_range_self θ
          rw [zero_add, hγ.image] at h1
          exact frontier_subset_closure h1
        have hcl : ∀ n, LipschitzWith (A.lip * Kγ) (A.map (n + N) ∘ γ) := fun n =>
          lipschitzOnWith_univ.mp ((A.lipschitz (n + N)).comp (hKγ.lipschitzOnWith (s := Set.univ))
            fun θ _ => hfr θ)
        have hmeas : ∀ n, AEStronglyMeasurable (fun w => |(fderiv ℝ (A.map (n + N)) w).det|)
            volume := fun n =>
          ((continuous_abs.comp ContinuousLinearMap.continuous_det).measurable.comp
            (measurable_fderiv ℝ _)).aestronglyMeasurable
        have hbound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω),
            |(fderiv ℝ (A.map (n + N)) w).det| ≤ A.lip ^ 2 := fun n =>
          ae_restrict_of_forall_mem hΩo.measurableSet fun w hw =>
            abs_det_fderiv_le hΩo ((A.lipschitz (n + N)).mono subset_closure) hw
        have hdt : ∀ᵐ w ∂(volume.restrict Ω),
            Tendsto (fun n => |(fderiv ℝ (A.map (n + N)) w).det|) atTop (𝓝 1) := by
          refine ae_restrict_of_forall_mem hΩo.measurableSet fun w hw => ?_
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [(tendsto_add_atTop_nat N).eventually (A.collar_shrink w hw)] with n hn
          have hloc : (A.map (n + N) : ℂ → ℂ) =ᶠ[𝓝 w] id :=
            Filter.mem_of_superset ((A.collar_closed _).isOpen_compl.mem_nhds hn)
              fun x hx => A.eq_self _ x hx
          rw [hloc.fderiv_eq, fderiv_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
            LinearMap.det_id, abs_one]
        refine ⟨{
          dom := fun n => A.map (n + N) '' Ω
          dom_bounded := fun n => hb.subset (A.subset _)
          dom_smooth := fun n => A.smooth _
          dom_simplyConnected := fun n =>
            ((A.map (n + N)).image Ω).symm.toHomotopyEquiv.simplyConnectedSpace
          param := γ'
          param_isBoundaryParam := hγ'
          curve := fun n => A.map (n + N) ∘ γ
          curveLip := fun _ => A.lip * Kγ
          curve_lipschitz := hcl
          curve_closed := fun n => by simp [Function.comp, show γ (2 * π) = γ 0 by simpa using hγ.periodic 0]
          curve_tendsto := ?_
          curve_length := ⟨2 * π * (A.lip * Kγ), fun n => ?_⟩
          monodromy_eq := fun n E W W' hW hW' => ?_
          density := fun n w => |(fderiv ℝ (A.map (n + N)) w).det|
          densityBound := A.lip ^ 2
          density_aestronglyMeasurable := fun n => (hmeas n).restrict
          density_bound := fun n => (hbound n).mono fun w hw => by rwa [abs_abs]
          density_tendsto := hdt
          volume_dom := fun n => ?_
          formQ := fun n => formQ (n + N)
          formM := fun n => weightedMass Ω (fun w => |(fderiv ℝ (A.map (n + N)) w).det|)
          minmax := fun j n S hS hH => hmin j (n + N) S hS hH
          formQ_tendsto := fun S hS hH => ?_
          formM_tendsto := fun S hS _ => tendstoUniformlyOn_weightedMass _ _ (fun n => (hmeas n).restrict)
            (fun n => (hbound n).mono fun w hw => by rwa [abs_abs]) hdt S hS
          limits := fun j φ hφ lam hlam h => hlim j (fun n => φ n + N)
            (fun a b hab => Nat.add_lt_add_right (hφ hab) N) lam hlam h }⟩
        case refine_1 =>
          have h := (A.tendsto.comp γ).mono (fun θ _ => hfr θ : Set.Icc 0 (2 * π) ⊆ γ ⁻¹' closure Ω)
          exact fun u hu => (tendsto_add_atTop_nat N).eventually (h u hu)
        case refine_2 =>
          have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
            (f := fun θ => ‖deriv (⇑(A.map (n + N)) ∘ γ) θ‖) (C := A.lip * Kγ) fun θ _ => by
              rw [norm_norm]; exact_mod_cast norm_deriv_le_of_lipschitz (hcl n)
          rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
          exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; linarith)
        case refine_3 =>
          obtain ⟨Kτ, hKτ⟩ := hτL n
          obtain ⟨K', hK'⟩ := (hγ' n).lipschitz
          rw [← hτc n] at hW
          exact monodromy_comp hK' (hτm n) hKτ (hτ0 n) (hτ2 n) hW' hW
        case refine_4 =>
          rw [volume_image_eq_lintegral hΩo ((A.lipschitz (n + N)).mono subset_closure) (A.map (n + N)).injective.injOn,
            ofReal_integral_eq_lintegral_ofReal]
          · exact Measure.integrableOn_of_bounded hb.measure_lt_top.ne (hmeas n)
              ((hbound n).mono fun w hw => by rwa [Real.norm_eq_abs, abs_abs])
          · exact Eventually.of_forall fun _ => abs_nonneg _
        case refine_5 => exact fun u hu => (tendsto_add_atTop_nat N).eventually (hQ S hS hH u hu)
      obtain ⟨K, hK⟩ := hγ.lipschitz
      choose Ws hWs using fun n => transport_exists_of_lipschitz (A.curve n) (A.curve_lipschitz n)
        (neumannEigenvalue (A.dom n) j).toReal
      choose Ws' hWs' using fun n => transport_exists_of_lipschitz (A.param n)
        ((A.param_isBoundaryParam n).lipschitz.choose_spec) (neumannEigenvalue (A.dom n) j).toReal
      have hvolfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
      exact lipschitz_quantitative_of_approximation A.dom j hK A.curve_lipschitz (by simpa using hγ.periodic 0)
        A.curve_closed A.curve_tendsto A.curve_length hW hWs (by
          intro n
          rw [A.monodromy_eq n _ _ _ (hWs n) (hWs' n)]
          exact smooth_eigen (A.dom_bounded n) (A.dom_smooth n) (A.dom_simplyConnected n)
            (A.param_isBoundaryParam n) j hj (Ws' n) (hWs' n)) hvolfin
        (neumannEigenvalue_lt_top hL j).ne (tendsto_volume_of_density hvolfin A.dom A.density A.densityBound A.density_aestronglyMeasurable A.density_bound A.density_tendsto A.volume_dom) (tendsto_neumannEigenvalue j (fun n => neumannEigenvalue (A.dom n) j) A.formQ A.formM (A.minmax j) (fun S hS hH => A.formQ_tendsto S (Module.finite_of_finrank_eq_succ hS) hH) (fun S hS hH => A.formM_tendsto S (Module.finite_of_finrank_eq_succ hS) hH) (A.limits j)))

/-- **Theorem 10.16, counting form.** For every bounded simply connected Lipschitz domain
and every `E > 0`, `N_N(E) > |Ω| E / (4π)`. -/
theorem strict_neumann_polya_count Ω (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) E (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) :=
  (show (∀ j : ℕ, 1 ≤ j → volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j)) ↔ (∀ E : ℝ, 0 < E → volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) < (neumannCount Ω (ENNReal.ofReal E) : ENNReal)) by
    constructor
    · intro h E hE
      exact count_of_eigen _ _ hb.measure_lt_top.ne (neumannEigenvalue_monotone Ω)
        (neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb) h E hE
    · intro h j hj
      exact eigen_of_count _ _ (neumannEigenvalue_monotone Ω)
        (neumannEigenvalue_pos hb hL) (fun j _ => (neumannEigenvalue_lt_top hL j).ne) h j hj).mp (strict_neumann_polya Ω hb hL hsc) E hE

end PolyaNeumann

/-!
Stable top-level entry points for automated audits and downstream users.
The original namespaced declarations above remain the canonical proof
statements; these aliases provide the same compact API as the companion
Dirichlet formalization.
-/

end
