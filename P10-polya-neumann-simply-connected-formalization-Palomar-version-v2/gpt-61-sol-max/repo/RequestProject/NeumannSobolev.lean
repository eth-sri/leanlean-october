module

public import RequestProject.PlanarTypes

public import RequestProject.NeumannEigenspace
public import RequestProject.WeakCompact

/-!
# The operator of the actual weak Neumann form

The form domain below consists of L² functions together with their two weak
derivatives. Its Hilbert inner product is the shifted form `q + ⟨·,·⟩`.
The adjoint of its inclusion constructs the resolvent, without any spectral
or min–max assumption.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- Value and both weak derivatives, with the Hilbert sum norm. -/
abbrev H1Jet Ω := PiLp 2 (fun _ : Fin 3 => L2 Ω)

def h1JetSubmodule Ω : Submodule ℂ (H1Jet Ω) where
  carrier := {x | IsWeakGradient Ω (x 0) (fun i => x i.succ)}
  zero_mem' := isWeakGradient_zero
  add_mem' := fun hx hy => hx.add hy
  smul_mem' := fun c _ hx => hx.smul c

theorem isClosed_h1JetSubmodule Ω :
    IsClosed (h1JetSubmodule Ω : Set (H1Jet Ω)) := by
  refine IsSeqClosed.isClosed fun x X hx hX => ?_
  exact isWeakGradient_of_tendsto hx
    (((PiLp.continuous_apply 2 (fun _ : Fin 3 => L2 Ω) 0).tendsto X).comp hX)
    (fun i => ((PiLp.continuous_apply 2 (fun _ : Fin 3 => L2 Ω) i.succ).tendsto X).comp hX)

/-- The genuine H¹ space, retaining the weak gradient as part of its data. -/
abbrev NeumannH1 Ω := h1JetSubmodule Ω

instance (Ω : PlanarSet) : CompleteSpace (NeumannH1 Ω) :=
  (isClosed_h1JetSubmodule Ω).completeSpace_coe

def h1Value (Ω : PlanarSet) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  (PiLp.proj 2 (fun _ : Fin 3 => L2 Ω) 0).comp (h1JetSubmodule Ω).subtypeL

def h1Gradient (Ω : PlanarSet) (i : Coord) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  (PiLp.proj 2 (fun _ : Fin 3 => L2 Ω) i.succ).comp (h1JetSubmodule Ω).subtypeL

theorem h1Value_weakGradient Ω u :
    IsWeakGradient Ω (h1Value Ω u) (fun i => h1Gradient Ω i u) := u.property

def h1Vector {Ω : PlanarSet} {u : L2 Ω} {g : Coord → L2 Ω}
    (hg : IsWeakGradient Ω u g) : NeumannH1 Ω :=
  ⟨WithLp.toLp 2 (Fin.cons u g), hg⟩

section
variable {Ω } {u } {g } (hg : IsWeakGradient Ω u g)
include Ω u g hg

@[simp] theorem h1Value_h1Vector : h1Value Ω (h1Vector hg) = u := rfl

@[simp] theorem h1Gradient_h1Vector i : h1Gradient Ω i (h1Vector hg) = g i := rfl

end


theorem h1Value_range Ω : Set.range (h1Value Ω) = H1 Ω := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, h1Value_weakGradient Ω v⟩
  · rintro ⟨g, hg⟩
    exact ⟨h1Vector hg, rfl⟩

theorem h1Value_injective  (hΩ : IsOpen Ω) :
    Function.Injective (h1Value Ω) := by
  intro u v huv
  have hgrad := (h1Value_weakGradient Ω u).unique hΩ
    (huv.symm ▸ h1Value_weakGradient Ω v)
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact huv
  · exact congrFun hgrad j

theorem h1_inner Ω u v :
    ⟪u, v⟫_ℂ = ⟪h1Value Ω u, h1Value Ω v⟫_ℂ +
      ∑ i, ⟪h1Gradient Ω i u, h1Gradient Ω i v⟫_ℂ := rfl

theorem h1_norm_sq Ω u :
    ‖u‖ ^ 2 = ‖h1Value Ω u‖ ^ 2 + ∑ i, ‖h1Gradient Ω i u‖ ^ 2 := by
  have h := h1_inner Ω u u
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)

theorem h1_ext  
    (hv : h1Value Ω u = h1Value Ω v)
    (hg : ∀ i : Coord, h1Gradient Ω i u = h1Gradient Ω i v) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  exact Fin.cases hv hg

theorem h1Value_norm_le  u :
    ‖h1Value Ω u‖ ≤ ‖u‖ := PiLp.norm_apply_le (u : H1Jet Ω) 0

theorem h1Gradient_norm_le  u i :
    ‖h1Gradient Ω i u‖ ≤ ‖u‖ := PiLp.norm_apply_le (u : H1Jet Ω) i.succ

theorem h1_norm_le_of_components  u 
    (hv : ‖h1Value Ω u‖ ≤ A) (hg : ∀ i : Coord, ‖h1Gradient Ω i u‖ ≤ A) :
    ‖u‖ ≤ Real.sqrt 3 * A := by
  have hA := (norm_nonneg _).trans hv
  have hs := h1_norm_sq Ω u
  rw [Fin.sum_univ_two] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [(sq_le_sq₀ (norm_nonneg _) hA).2 hv,
    (sq_le_sq₀ (norm_nonneg _) hA).2 (hg 0),
    (sq_le_sq₀ (norm_nonneg _) hA).2 (hg 1)]

/-- H¹ test vectors separate L², proved using actual smooth test functions. -/
theorem eq_zero_of_inner_h1  (hΩ : IsOpen Ω) f
    (hf : ∀ u : NeumannH1 Ω, ⟪h1Value Ω u, f⟫_ℂ = 0) : f = 0 := by
  have hloc := locallyIntegrable_indicator_L2 hΩ.measurableSet f
  have h0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn Ω)
    (fun ψ hψ hψc hψs => by
      let φ  := fun w => (ψ w : ℂ)
      have hφ : TestFunction Ω φ :=
        ⟨Complex.ofRealCLM.contDiff.comp hψ, hψc.comp_left Complex.ofReal_zero,
          (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs⟩
      let g  := fun i => (hφ.memLp_fderiv (coordDir i)).toLp _
      have hg  :=
        isWeakGradient_of_smooth hφ.1 hφ.memLp (fun i => hφ.memLp_fderiv _)
      have h := hf (h1Vector hg)
      rw [h1Value_h1Vector, L2.inner_def] at h
      have heq : ∫ w in Ω, (ψ w) • (f : PlaneMap) w = 0 := by
        rw [← h]
        apply integral_congr_ae
        filter_upwards [hφ.memLp.coeFn_toLp] with w hw
        simp [hw, φ, RCLike.inner_apply, Complex.real_smul, mul_comm]
      have e : ∀ w, ψ w • Ω.indicator (fun z => (f : PlaneMap) z) w =
          Ω.indicator (fun w => ψ w • (f : PlaneMap) w) w := by
        intro w
        by_cases hw : w ∈ Ω <;> simp [hw]
      simp_rw [e]
      rw [integral_indicator hΩ.measurableSet, heq])
  apply Lp.ext
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mpr h0,
    Lp.coeFn_zero ℂ 2 (volume.restrict Ω), ae_restrict_mem hΩ.measurableSet] with w hw hz hwΩ
  simp_all

theorem h1Value_denseRange  (hΩ : IsOpen Ω) : DenseRange (h1Value Ω) := by
  change Dense ((h1Value Ω).range : Set (L2 Ω))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply eq_bot_iff.mpr
  intro f hf
  exact eq_zero_of_inner_h1 hΩ f (fun u =>
    ((h1Value Ω).range.mem_orthogonal f).mp hf _ ⟨u, rfl⟩)

/-- Convergent subsequences imply total boundedness even when their limits
need not belong to the set. -/
theorem totallyBounded_of_subsequence {X : Type*} [UniformSpace X] s
    (H : ∀ u : ℕ → X, (∀ n, u n ∈ s) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X, Tendsto (u ∘ φ) atTop (𝓝 v)) :
    TotallyBounded s := by
  classical
  intro V V_in
  contrapose! H
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      ∀ n m, m < n → u m ∉ UniformSpace.ball (u n) V := by
    simp  [Set.not_subset] at H
    have := seq_of_forall_finite_exists H
    simp  [forall_and] at this
    assumption
  refine ⟨u, u_in, fun φ hφ v huφ => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V :=
    huφ.cauchySeq.mem_entourage V_in
  exact hu (φ (N + 1)) (φ N) (hφ (Nat.lt_add_one N))
    (hN (N + 1) N N.le_succ le_rfl)

/-- Rellich compactness is compactness of the actual H¹ inclusion. -/
theorem h1Value_isCompactOperator  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : IsCompactOperator (h1Value Ω) := by
  classical
  let S  := h1Value Ω '' Metric.closedBall 0 1
  have hS : TotallyBounded S := by
    apply totallyBounded_of_subsequence
    intro u hu
    choose v hv hveq using hu
    have hvnorm (n : ℕ) : ‖v n‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv n
    have hweak (n : ℕ) : IsWeakGradient Ω (u n) (fun i => h1Gradient Ω i (v n)) := by
      rw [← hveq n]
      exact h1Value_weakGradient Ω (v n)
    have huC (n : ℕ) : ‖u n‖ ≤ 1 := by
      rw [← hveq n]
      exact (PiLp.norm_apply_le (v n : H1Jet Ω) 0).trans (hvnorm n)
    have hgC (n : ℕ) (i : Coord)  :=
      (PiLp.norm_apply_le (v n : H1Jet Ω) i.succ).trans (hvnorm n)
    exact rellich_compact hb hL u (fun n i => h1Gradient Ω i (v n)) hweak 1 huC hgC
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (h1Value Ω).toLinearMap one_pos).2
  exact isCompact_iff_totallyBounded_isComplete.2 ⟨hS.closure, isClosed_closure.isComplete⟩

end PolyaNeumann

end
