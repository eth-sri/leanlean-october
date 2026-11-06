module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section

open MeasureTheory Set Filter
open scoped ComplexConjugate InnerProductSpace


namespace PolyaNeumann

/-- The observation of the radial vector is `b_E`. -/
lemma observation_radialVec W θ :
    observation W (radialVec W) θ = smallB W θ := by
  unfold observation smallB basisVec
  rw [lp.inner_single_left]
  simp

/-- Abstract identity: for unitary `V`, `⟨e, (V^* - V) v⟩ = ⟨(I + V^*) e, (V^* - I) v⟩`. -/
lemma inner_adjoint_sub_eq {V : ComplexEnd Ell2} (hV : V ∈ unitary (ComplexEnd Ell2))
    (e v : Ell2) :
    ⟪e, (ContinuousLinearMap.adjoint V - V) v⟫_ℂ =
      ⟪e + ContinuousLinearMap.adjoint V e, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ := by
  have hVV : V * ContinuousLinearMap.adjoint V = 1 := by
    exact (Unitary.mem_iff.mp hV).2
  have h1 : ⟪ContinuousLinearMap.adjoint V e, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ =
      ⟪e, v - V v⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply, map_sub,
      ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hVV,
      ContinuousLinearMap.one_apply]
  rw [inner_add_left, h1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_right, inner_sub_right, inner_sub_right]
  ring

section
variable {γ } {K } (hK : LipschitzWith K γ) (hclosed : γ circlePeriod = γ 0) {E } {W } (hW : IsTransport γ E W) {a } (ha : IsDirDensity a)
include γ K hK hclosed E W hW a ha

/-- **The Schur pairing on Herglotz data.** `B(e₀, v_a) = √2 ∫₀^L conj(b_E) g_a`. -/
theorem imPair_herglotzVec :
    imPair (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      (Real.sqrt 2 : ℂ) *
        ∫ θ in (0 : ℝ)..circlePeriod, conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  obtain ⟨hO, -⟩ := herglotzForm_eq hK hclosed hW ha
  set g := herglotzConormal (Real.sqrt E) a γ with hgdef
  set V := W circlePeriod with hVdef
  set v := herglotzVec ha (Real.sqrt E) (γ 0) with hvdef
  have hV  :=
    transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hR := inner_observationAdj_right hW.1 hgm hgB (radialVec W)
  rw [hO, inner_smul_right] at hR
  have hint : l2Inner (observation W (radialVec W)) g =
      ∫ θ in (0 : ℝ)..circlePeriod, conj (smallB W θ) * g θ := by
    simp_all [l2Inner, observation_radialVec]
  rw [hint] at hR
  have hrad : radialVec W = basisVec 0 + ContinuousLinearMap.adjoint V (basisVec 0) := rfl
  have hkey := inner_adjoint_sub_eq hV (basisVec 0) v
  rw [← hrad] at hkey
  have hU : monodromy W - ContinuousLinearMap.adjoint (monodromy W) =
      ContinuousLinearMap.adjoint V - V := by
    simp_all [monodromy, PolyaNeumann.Ell2]
  unfold imPair
  rw [hU, hkey, ← hR]
  have h2 : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  linear_combination (-⟪radialVec W, (ContinuousLinearMap.adjoint V - 1) v⟫_ℂ * Complex.I) * h2

/-- **The Schur complement on Herglotz data.**
`C(v_a) = herglotzForm W γ E a - |∫₀^L conj(b_E) g_a|² / a_E`. -/
theorem imSchur_herglotzVec :
    imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) =
      herglotzForm W γ E a -
        ‖∫ θ in (0 : ℝ)..circlePeriod, conj (smallB W θ) * herglotzConormal (Real.sqrt E) a γ θ‖ ^ 2 /
          smallA W := by
  unfold imSchur
  rw [imPair_herglotzVec hK hclosed hW ha, imForm_monodromy_basisVec, imForm,
    ← herglotzForm_eq_im hK hclosed hW ha, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  ring

end


end PolyaNeumann
