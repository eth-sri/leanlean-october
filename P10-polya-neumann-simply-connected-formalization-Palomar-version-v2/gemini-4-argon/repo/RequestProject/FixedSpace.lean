module

public import RequestProject.Herglotz
public import RequestProject.NeumannEigenspace
public import RequestProject.Driven
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import RequestProject.CurveContinuity

/-!
# The fixed space of the monodromy and Herglotz-compatible traces (Lemma 10.5)

The paper proves `dim ker(V_E - I) ≤ dim ker(A_N - E)` in two steps:

1. (pairing step, proved here) if `V_E v = v`, the observation `f₀ = O_E v = ⟨e₀, W_E(·) v⟩`
   is a Lipschitz closed boundary function orthogonal to the conormal trace `g_a` of every
   Herglotz wave (`observation_mem_compatibleTraces`, from Lemma 4.4 in `Herglotz.lean`);
2. (Cauchy reconstruction, Lemma 4.8) every such compatible boundary function `h` is the
   Dirichlet trace of a unique Helmholtz solution with zero Neumann data, i.e. of a Neumann
   eigenfunction, depending linearly on `h`.

We formalize the space of compatible traces (`compatibleTraces`) and deduce the injective map
from the fixed space into the Neumann eigenspace from any linear reconstruction map that only
kills traces vanishing on `[0, L]` (`fixedSpace_to_neumannEigenspace_of_reconstruction`),
using the injectivity of the observation map (Lemma 10.4).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The boundary functions `h` on `[0, L]` compatible with the Herglotz waves at energy `E`:
`h` is Lipschitz on `[0, L]` (in particular in `H¹`), closed (`h(L) = h(0)`), and
`∫₀^L conj(g_a) h = 0` for the conormal trace `g_a` of every Herglotz wave with `L²` direction
density `a` (the compatibility condition of Lemma 4.8 with zero conormal data). -/
def compatibleTraces (γ : ℝ → ℂ) (E : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {h | (∃ K, LipschitzOnWith K h (Icc 0 (2 * π))) ∧ h (2 * π) = h 0 ∧
    ∀ a, IsDirDensity a →
      IntervalIntegrable (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * h s) volume 0
        (2 * π) ∧
      ∫ s in 0..(2 * π), conj (herglotzConormal (Real.sqrt E) a γ s) * h s = 0}
  zero_mem' := ⟨⟨0, LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp⟩, rfl, fun a _ => by
    simp⟩
  add_mem' := by
    rintro h₁ h₂ ⟨⟨K₁, hK₁⟩, hc₁, hi₁⟩ ⟨⟨K₂, hK₂⟩, hc₂, hi₂⟩
    refine ⟨⟨K₁ + K₂, hK₁.add hK₂⟩, by simp [hc₁, hc₂], fun a ha => ?_⟩
    obtain ⟨hI₁, hZ₁⟩ := hi₁ a ha
    obtain ⟨hI₂, hZ₂⟩ := hi₂ a ha
    have heq : (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * (h₁ + h₂) s) =
        fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * h₁ s +
          conj (herglotzConormal (Real.sqrt E) a γ s) * h₂ s := by
      funext s; simp; ring
    rw [heq]
    exact ⟨hI₁.add hI₂, by rw [intervalIntegral.integral_add hI₁ hI₂, hZ₁, hZ₂, add_zero]⟩
  smul_mem' := by
    rintro c h ⟨⟨K, hK⟩, hc, hi⟩
    refine ⟨⟨‖c‖₊ * K, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩, by simp [hc],
      fun a ha => ?_⟩
    · rw [dist_eq_norm, Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul, NNReal.coe_mul,
        coe_nnnorm, mul_assoc, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (hK.dist_le_mul x hx y hy) (norm_nonneg _)
    · obtain ⟨hI, hZ⟩ := hi a ha
      have heq : (fun s => conj (herglotzConormal (Real.sqrt E) a γ s) * (c • h) s) =
          fun s => c * (conj (herglotzConormal (Real.sqrt E) a γ s) * h s) := by
        funext s; simp; ring
      rw [heq]
      exact ⟨hI.const_mul c, by rw [intervalIntegral.integral_const_mul, hZ, mul_zero]⟩

/-- The observation `O_E v` of a fixed vector `V_E v = v` of the monodromy of a closed
Lipschitz curve is a compatible trace (Lemma 10.5, pairing step). -/
theorem observation_mem_compatibleTraces   (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0)   (hW : IsTransport γ E W)
     (hv : W (2 * π) v = v) : observation W v ∈ compatibleTraces γ E := by
  have hπ : 0 ≤ 2 * π := by positivity
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  have hcont : ContinuousOn (observation W v) (Icc 0 (2 * π)) :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  refine ⟨⟨KW * ‖v‖₊, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩, ?_, fun a ha => ?_⟩
  · rw [dist_eq_norm, observation, observation, ← inner_sub_right, ← ContinuousLinearMap.sub_apply]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [show ‖basisVec 0‖ = 1 by simp [basisVec], one_mul, NNReal.coe_mul, coe_nnnorm]
    refine ((W x - W y).le_opNorm v).trans ?_
    rw [← dist_eq_norm, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hKW.dist_le_mul x hx y hy) (norm_nonneg v)
  · simp [observation, hv, show W 0 = 1 by simpa using hW.2 0 ⟨le_rfl, hπ⟩]
  · obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
    refine ⟨?_, integral_conj_herglotzConormal_mul_observation hK hclosed hW hv ha⟩
    simpa using intervalIntegrable_smul_of_continuousOn hcont (g := fun s => conj (herglotzConormal (Real.sqrt E) a γ s)) (Complex.continuous_conj.comp_aestronglyMeasurable hgm) (B := B) (fun s => by rw [Complex.norm_conj]; exact hgB s) ⟨le_rfl, hπ⟩ ⟨hπ, le_rfl⟩

/-- The observation map restricted to the fixed space `ker(V_E - I)`, with values in the
compatible traces. -/
def observationFixed   (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0)   (hW : IsTransport γ E W) :
    LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) →ₗ[ℂ]
      compatibleTraces γ E where
  toFun v := ⟨observation W v, observation_mem_compatibleTraces hK hclosed hW (by
    have := v.2
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at this
    exact this)⟩
  map_add' v w := by
    ext θ
    show inner ℂ (basisVec 0) (W θ (v + w)) =
      inner ℂ (basisVec 0) (W θ v) + inner ℂ (basisVec 0) (W θ w)
    rw [map_add, inner_add_right]
  map_smul' c v := by
    ext θ
    show inner ℂ (basisVec 0) (W θ (c • v)) = c * inner ℂ (basisVec 0) (W θ v)
    rw [map_smul, inner_smul_right]

/-- **Lemma 10.5 (first inequality), reduced to Cauchy reconstruction.** Given a linear
reconstruction map from compatible traces to the Neumann eigenspace which only kills traces
vanishing on `[0, L]`, the fixed space of `V_E` embeds injectively into the Neumann eigenspace:
`dim ker(V_E - I) ≤ dim ker(A_N - E)`. -/
theorem fixedSpace_to_neumannEigenspace_of_reconstruction  
    (hγ : IsBoundaryParam Ω γ)  (hE : 0 < E) 
    (hW : IsTransport γ E W)
    (hR : ∃ R : compatibleTraces γ E →ₗ[ℂ] neumannEigenspace Ω E,
      ∀ h, R h = 0 → ∀ θ ∈ Icc 0 (2 * π), (h : ℝ → ℂ) θ = 0) :
    ∃ T : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) →ₗ[ℂ]
      neumannEigenspace Ω E, Function.Injective T := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨R, hR⟩ := hR
  refine ⟨R ∘ₗ observationFixed hK (by simpa using hγ.periodic 0) hW, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  exact Subtype.ext (observation_injective_of_boundaryParam hγ hE hW v ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => (hR _ hv) θ hθ)))

end PolyaNeumann
