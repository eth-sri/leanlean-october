module

public import RequestProject.FourierLipschitz
public import RequestProject.SmallTransport
public import RequestProject.CutCorrection

/-!
# Lemma 6.3: the periodic projected observation is Hilbert–Schmidt into `H¹(𝕋)`

For a transport `W` of a Lipschitz curve, let `c_E = (V_E^* - I) e₀` and let `Π^c_E` be the
orthogonal projection onto `c_E^⊥` (`cutProj`). The projected observation
`v ↦ O_E Π^c_E v = ⟨e₀, W(·) Π^c_E v⟩` has matching endpoint values (Lemma 6.4), and its row
`r(θ) = Π^c_E W(θ)^* e₀` is Lipschitz on `[0, L]`. Extending `r` periodically and applying the
difference-quotient estimate of `FourierLipschitz.lean` gives, for every orthonormal family
`(vⱼ)` of `ℓ²`, `∑ⱼ ∑ₙ n² |(O_E Π^c_E vⱼ)^(n)|² < ∞` (`projected_observation_hilbertSchmidt`):
the Hilbert–Schmidt property of `O_E Π^c_E : ℓ² → H¹(𝕋)` of Lemma 6.3.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

/-! ### Periodic extension -/

variable {γ : ℝ → ℂ}

section Periodize

variable {H : Type*} [NormedAddCommGroup H]

/-- The `2π`-periodic extension of the restriction of `f` to `[0, 2π)`. -/
def periodize (f : ℝ → H) : ℝ → H := fun θ => f (toIcoMod two_pi_pos 0 θ)

omit [NormedAddCommGroup H] in
lemma periodize_apply_of_mem {f : ℝ → H}  (hθ : θ ∈ Set.Ico 0 (2 * π)) :
    periodize f θ = f θ := by
  unfold periodize
  rw [(toIcoMod_eq_self two_pi_pos).mpr (by simpa using hθ)]

omit [NormedAddCommGroup H] in
lemma periodic_periodize (f : ℝ → H) : Function.Periodic (periodize f) (2 * π) := by
  intro θ
  unfold periodize
  rw [toIcoMod_add_right]

omit [NormedAddCommGroup H] in
lemma periodize_apply_two_pi {f : ℝ → H} (hend : f (2 * π) = f 0) :
    periodize f (2 * π) = f (2 * π) := by
  have := periodic_periodize f 0
  rw [zero_add] at this
  rw [this, periodize_apply_of_mem ⟨le_rfl, two_pi_pos⟩, hend]

omit [NormedAddCommGroup H] in
lemma periodize_eqOn_Icc {f : ℝ → H} (hend : f (2 * π) = f 0) :
    Set.EqOn (periodize f) f (Set.Icc 0 (2 * π)) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.2 with h | h
  · rw [h]; exact periodize_apply_two_pi hend
  · exact periodize_apply_of_mem ⟨hθ.1, h⟩

/-- Lipschitz bound for short steps of the periodic extension. -/
lemma norm_periodize_add_sub_le {f : ℝ → H} 
    (hf : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π), ‖f x - f y‖ ≤ K * |x - y|)
    (hend : f (2 * π) = f 0) (x d : ℝ) (hd0 : 0 ≤ d) (hd : d < 2 * π) :
    ‖periodize f (x + d) - periodize f x‖ ≤ K * d := by
  set x' := toIcoMod two_pi_pos 0 x with hx'
  have hx'mem : x' ∈ Set.Ico 0 (2 * π) := by
    simpa using toIcoMod_mem_Ico two_pi_pos 0 x
  obtain ⟨m, hm⟩ := show ∃ m : ℤ, x = x' + m • (2 * π) by
    refine ⟨toIcoDiv two_pi_pos 0 x, ?_⟩
    rw [hx', toIcoMod]
    abel
  have hper := periodic_periodize f
  rw [show periodize f x = periodize f x' by
    rw [hm, hper.zsmul], show periodize f (x + d) = periodize f (x' + d) by
    rw [hm, show x' + m • (2 * π) + d = x' + d + m • (2 * π) by abel, hper.zsmul], periodize_apply_of_mem hx'mem]
  by_cases hlt : x' + d < 2 * π
  · rw [periodize_apply_of_mem ⟨by linarith [hx'mem.1], hlt⟩]
    have := hf (x' + d) ⟨by linarith [hx'mem.1], hlt.le⟩ x' ⟨hx'mem.1, hx'mem.2.le⟩
    rwa [add_sub_cancel_left, abs_of_nonneg hd0] at this
  · push_neg at hlt
    have hy : x' + d - 2 * π ∈ Set.Ico 0 (2 * π) := ⟨by linarith, by linarith [hx'mem.2]⟩
    rw [show periodize f (x' + d) = f (x' + d - 2 * π) by
      rw [← periodize_apply_of_mem (f := f) hy, ← hper (x' + d - 2 * π), sub_add_cancel]]
    have h1 := hf (x' + d - 2 * π) ⟨hy.1, hy.2.le⟩ 0 ⟨le_rfl, two_pi_pos.le⟩
    have h2 := hf (2 * π) ⟨two_pi_pos.le, le_rfl⟩ x' ⟨hx'mem.1, hx'mem.2.le⟩
    rw [sub_zero, abs_of_nonneg hy.1] at h1
    rw [abs_of_nonneg (by linarith [hx'mem.2])] at h2
    calc _ = _ := by
          rw [hend]; abel_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

/-- The periodic extension of a function that is `K`-Lipschitz on `[0, 2π]` with equal endpoint
values is `K`-Lipschitz on `ℝ`. -/
theorem lipschitzWith_periodize {f : ℝ → H} {K : NNReal}
    (hf : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π), ‖f x - f y‖ ≤ K * |x - y|)
    (hend : f (2 * π) = f 0) : LipschitzWith K (periodize f) := by
  have key : ∀ x y : ℝ, x ≤ y → ‖periodize f y - periodize f x‖ ≤ K * (y - x) := by
    intro x y hxy
    set q := toIcoDiv two_pi_pos 0 (y - x)
    set d := toIcoMod two_pi_pos 0 (y - x)
    have hdmem : d ∈ Set.Ico 0 (2 * π) := by
      simpa using toIcoMod_mem_Ico two_pi_pos 0 (y - x)
    have hyd : y = x + d + q • (2 * π) := by
      have : d = y - x - q • (2 * π) := rfl
      rw [this]; abel
    have hdle : d ≤ y - x := by
      rw [show y - x = d + q • (2 * π) by rw [hyd]; abel, zsmul_eq_mul]
      have : (0 : ℝ) ≤ q := by exact_mod_cast (by
        by_contra hneg
        push_neg at hneg
        have : q • (2 * π) ≤ -(2 * π) := by
          rw [zsmul_eq_mul]
          have : (q : ℝ) ≤ -1 := by exact_mod_cast (by omega)
          nlinarith [two_pi_pos]
        have : y - x = d + q • (2 * π) := by rw [hyd]; abel
        linarith [hdmem.2])
      nlinarith [two_pi_pos]
    rw [show periodize f y = periodize f (x + d) by rw [hyd, (periodic_periodize f).zsmul]]
    calc _ ≤ _ :=
          norm_periodize_add_sub_le hf hend x d hdmem.1 hdmem.2
      _ ≤ _ := by gcongr
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, Real.dist_eq]
  rcases le_total x y with h | h
  · rw [norm_sub_rev, abs_of_nonpos (by linarith)]
    simpa using key x y h
  · rw [abs_of_nonneg (by linarith)]
    exact key y x h

end Periodize

/-! ### The projected observation row -/

lemma cutProj_apply_self (c : Ell2) : cutProj c c = 0 := by
  rw [cutProj_eq_starProjection]
  exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero c

lemma inner_cutProj_left (c x y : Ell2) : ⟪cutProj c x, y⟫_ℂ = ⟪x, cutProj c y⟫_ℂ := by
  rw [cutProj_eq_starProjection]
  exact Submodule.inner_starProjection_left_eq_right (ℂ ∙ c)ᗮ x y

lemma norm_cutProj_apply_le (c x : Ell2) : ‖cutProj c x‖ ≤ ‖x‖ := by
  rw [cutProj_eq_starProjection]
  exact Submodule.norm_starProjection_apply_le (ℂ ∙ c)ᗮ x

/-- The row `r_E(θ) = Π^c_E W(θ)^* e₀` of the projected observation. -/
def projObsRow (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) : Ell2 :=
  cutProj (cutC (W (2 * π)) (basisVec 0)) (ContinuousLinearMap.adjoint (W θ) (basisVec 0))

lemma observation_cutProj_eq (W : ℝ → Ell2 →L[ℂ] Ell2) v θ :
    observation W (cutProj (cutC (W (2 * π)) (basisVec 0)) v) θ = ⟪projObsRow W θ, v⟫_ℂ := by
  rw [observation, projObsRow, inner_cutProj_left, ContinuousLinearMap.adjoint_inner_left]

lemma projObsRow_endpoint   
    (hW : IsTransport γ E W) : projObsRow W (2 * π) = projObsRow W 0 := by
  unfold projObsRow
  rw [show W 0 = 1 by
    simpa using hW.2 0 ⟨le_rfl, by positivity⟩]
  rw [show ContinuousLinearMap.adjoint (W (2 * π)) (basisVec 0) = cutC (W (2 * π)) (basisVec 0) + basisVec 0 by
    simp [cutC], map_add, cutProj_apply_self, zero_add, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  rfl

lemma norm_projObsRow_sub_le   (hK : LipschitzWith K γ) 
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) 
    (h₁ : θ₁ ∈ Set.Icc 0 (2 * π)) (h₂ : θ₂ ∈ Set.Icc 0 (2 * π)) :
    ‖projObsRow W θ₁ - projObsRow W θ₂‖ ≤ Real.sqrt E * shiftConst * K * |θ₁ - θ₂| := by
  unfold projObsRow
  rw [← map_sub, ← ContinuousLinearMap.sub_apply, ← map_sub]
  refine (norm_cutProj_apply_le _ _).trans ?_
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map, show ‖basisVec 0‖ = 1 by simp [basisVec], mul_one]
  exact norm_transport_sub_le_lip hK hW h₁ h₂

/-- **Lemma 6.3 (Hilbert–Schmidt part).** For a transport `W` of a Lipschitz curve and an
orthonormal family `(vⱼ)` of `ℓ²`, the Fourier coefficients on `[0, L]` of the periodic
functions `O_E Π^c_E vⱼ = ⟨e₀, W(·) Π^c_E vⱼ⟩` satisfy `∑ⱼ ∑ₙ n² |cⱼ(n)|² < ∞`. Together with
`∑ⱼ ∑ₙ |cⱼ(n)|² = ‖O_E Π^c_E‖²_{𝒮₂} ≤ L`, this is the Hilbert–Schmidt property of
`O_E Π^c_E : ℓ² → H¹(𝕋)`. -/
theorem projected_observation_hilbertSchmidt   (hK : LipschitzWith K γ)
    {E : ℝ} {W} (hW : IsTransport γ E W) {ι : Type*} {v}
    (hv : Orthonormal ℂ v) :
    Summable fun p : ι × ℤ => ((p.2 : ℝ)) ^ 2 * ‖fourierCoeffOn two_pi_pos
      (fun θ => observation W (cutProj (cutC (W (2 * π)) (basisVec 0)) (v p.1)) θ) p.2‖ ^ 2 := by
  set M : NNReal := ⟨Real.sqrt E * shiftConst * K, by
    have := shiftConst_nonneg; positivity⟩
  have hend := projObsRow_endpoint hW
  have h := summable_sq_mul_fourierCoeff hv (lipschitzWith_periodize (fun x hx y hy => norm_projObsRow_sub_le hK hW hx hy) hend : LipschitzWith M (periodize (projObsRow W))) (periodic_periodize _)
  refine h.congr fun p => ?_
  congr 3
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at hθ
  rw [observation_cutProj_eq, periodize_eqOn_Icc hend hθ]

end PolyaNeumann
