module

public import RequestProject.HerglotzMain
public import RequestProject.SmallEnergyForm
public import RequestProject.PeriodicForm

/-!
# The Schur pairing on Herglotz data

For a Herglotz density `a` with conormal trace `g = g_a` and coefficient vector `v = v_a(γ(0))`,
the pairing `B(e₀, v) = 2i ⟨e₀, (U_E - U_E^*) v⟩` of `SmallEnergyForm.lean` is the boundary
pairing of `g` with the function `b_E(θ) = ⟨e₀, W(θ) s_E⟩` (`smallB`):

  `B(e₀, v) = √2 ∫₀^L conj(b_E) g`   (`imPair_herglotzVec`).

Together with `herglotzForm_eq_im` this expresses the Schur complement `C(v)` of Lemma 8.6 on
Herglotz data entirely through boundary integrals of `g`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

variable {γ : ℝ → ℂ} {K : NNReal}

/-- The observation of the radial vector is `b_E`. -/
lemma observation_radialVec (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) :
    observation W (radialVec W) θ = smallB W θ := by
  unfold observation smallB basisVec
  simp [lp.inner_single_left]

/-- Abstract identity: for unitary `V`, `⟨e, (V^* - V) v⟩ = ⟨(I + V^*) e, (V^* - I) v⟩`. -/
lemma inner_adjoint_sub_eq {V : Ell2 →L[ℂ] Ell2} (hV : V ∈ unitary (Ell2 →L[ℂ] Ell2))
    (e v : Ell2) :
    ⟪e, (ContinuousLinearMap.adjoint V - V) v⟫_ℂ =
      ⟪e + ContinuousLinearMap.adjoint V e, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ := by
  have hVV : V * ContinuousLinearMap.adjoint V = 1 := (Unitary.mem_iff.mp hV).2
  have h1 : ⟪ContinuousLinearMap.adjoint V e, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ =
      ⟪e, v - V v⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply, map_sub,
      ← ContinuousLinearMap.mul_apply, hVV,
      ContinuousLinearMap.one_apply]
  rw [inner_add_left, h1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_right, inner_sub_right, inner_sub_right]
  ring

/-- **The Schur pairing on Herglotz data.** `B(e₀, v_a) = √2 ∫₀^L conj(b_E) g_a`. -/
theorem imPair_herglotzVec (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    imPair (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      Real.sqrt 2 *
        ∫ θ in 0..(2 * π), conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  obtain ⟨hO, -⟩ := herglotzForm_eq hK hclosed hW ha
  set g := herglotzConormal (Real.sqrt E) a γ with hgdef
  set V := W (2 * π) with hVdef
  set v := herglotzVec ha (Real.sqrt E) (γ 0) with hvdef
  have hR := inner_observationAdj_right hW.1 hgm hgB (radialVec W)
  rw [hO, inner_smul_right] at hR
  have hint : l2Inner (observation W (radialVec W)) g =
      ∫ θ in 0..(2 * π), conj (smallB W θ) * g θ := by
    unfold l2Inner
    simp [observation_radialVec]
  have hrad : radialVec W = basisVec 0 + ContinuousLinearMap.adjoint V (basisVec 0) := rfl
  have hkey := inner_adjoint_sub_eq (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩) (basisVec 0) v
  have hU : monodromy W - ContinuousLinearMap.adjoint (monodromy W) =
      ContinuousLinearMap.adjoint V - V := by
    simp [monodromy, hVdef]
  unfold imPair
  have h2 : ((Real.sqrt 2 : ℂ)) * Real.sqrt 2 = 2 := by
    simp [← Complex.ofReal_mul]
  grind

/-- **The Schur complement on Herglotz data.**
`C(v_a) = herglotzForm W γ E a - |∫₀^L conj(b_E) g_a|² / a_E`. -/
theorem imSchur_herglotzVec {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      herglotzForm W γ E a -
        ‖∫ θ in 0..(2 * π), conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ‖ ^ 2 /
          smallA W := by
  unfold imSchur
  rw [imPair_herglotzVec hK hclosed hW ha, imForm_monodromy_basisVec, imForm,
    ← herglotzForm_eq_im hK hclosed hW ha, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  ring

end PolyaNeumann
