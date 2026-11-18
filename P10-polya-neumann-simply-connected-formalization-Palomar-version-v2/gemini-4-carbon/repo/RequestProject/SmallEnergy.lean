module

public import RequestProject.CutPhase

@[expose] public section

noncomputable section

open scoped Real
open MeasureTheory Filter Topology Set

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma abs_arg_le_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    |Complex.arg z| ≤ π / 2 * ‖z - 1‖ := by
  set t := Complex.arg z
  have hexp : z = Complex.exp (Complex.I * t) := by
    simpa [hz, mul_comm] using (Complex.norm_mul_exp_arg_mul_I z).symm
  have ⟨hlo, hhi⟩ := abs_le.mp (Complex.abs_arg_le_pi z)
  have hsin : |Real.sin (t / 2)| = Real.sin (|t| / 2) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg]
      exact abs_of_nonpos (by
        simpa using Real.sin_nonneg_of_nonneg_of_le_pi (x := -(t / 2)) (by linarith) (by linarith))
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two, hsin]
  have hs := Real.mul_le_sin (by positivity : 0 ≤ |t| / 2) (by linarith [Complex.abs_arg_le_pi z])
  have hpi := Real.pi_pos
  have h2 : 2 / π * (|t| / 2) * π = |t| := by field_simp
  nlinarith

lemma abs_argCut_pi (z : ℂ) : |argCut π z| = |Complex.arg z| := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  unfold argCut argNeg
  by_cases ha : Complex.arg z < 0
  · rw [if_pos ha, if_neg (by linarith)]
  · rw [if_neg ha]
    rcases hhi.lt_or_eq with h | h
    · rw [if_pos (by linarith)]; ring_nf
    · rw [if_neg (by linarith), h, abs_of_neg (by linarith), abs_of_pos hpi]; ring

lemma sum_eigenMult_mul_norm_le {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C)
    (s : Finset {z : ℂ // z ≠ 1}) :
    ∑ z ∈ s, (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖ ≤ C := by
  classical
  obtain ⟨e, he, heig⟩ := exists_orthonormal_eigen_family hU hC s
  have key := hT.sum_norm_le _ e e he he
  have hterm : ∀ p : (Σ z : s, Fin (eigenMult U z)),
      ‖inner ℂ (e p) ((U - 1) (e p))‖ = ‖((p.1 : {z : ℂ // z ≠ 1}) : ℂ) - 1‖ := fun p => by
    have hs : ∀ (c : ℂ) (v : H), c • v - v = (c - 1) • v := fun c v => by rw [sub_smul, one_smul]
    rw [ContinuousLinearMap.sub_apply, heig, ContinuousLinearMap.one_apply, hs,
      inner_smul_right, inner_self_eq_norm_sq_to_K, he.1 p]
    simp
  simp only [hterm] at key
  refine le_trans (le_of_eq ?_) key
  rw [Fintype.sum_sigma]
  simp [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_coe_sort s]

lemma cutPhaseSum_pi_bound {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C) :
    Summable (cutPhaseTerm π U) ∧ |cutPhaseSum π U| ≤ π / 2 * C := by
  set g : {z : ℂ // z ≠ 1} → ℝ := fun z => (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖
  have hgnn : ∀ z, 0 ≤ g z := fun _ => by positivity
  have hgs : Summable g := summable_of_sum_le hgnn (sum_eigenMult_mul_norm_le hU hC hT)
  have hgt : ∑' z, g z ≤ C := Real.tsum_le_of_sum_le hgnn (sum_eigenMult_mul_norm_le hU hC hT)
  have hb : ∀ z, ‖cutPhaseTerm π U z‖ ≤ π / 2 * g z := fun z => by
    rw [cutPhaseTerm, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
    by_cases hm : eigenMult U z = 0
    · simp [hm]; exact mul_nonneg (by positivity) (hgnn z)
    have hm' : 0 < Module.finrank ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
      Nat.pos_of_ne_zero hm
    haveI := Module.finite_of_finrank_pos hm'
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm'
    have hz1 : ‖(z : ℂ)‖ = 1 :=
      norm_eq_one_of_eigen hU (fun h => hv0 (by simp [h])) (Module.End.mem_eigenspace_iff.mp hv)
    rw [abs_argCut_pi]
    linarith [mul_le_mul_of_nonneg_left (abs_arg_le_of_norm_eq_one hz1)
      (Nat.cast_nonneg (eigenMult U z))]
  have hs : Summable (cutPhaseTerm π U) := Summable.of_norm_bounded (hgs.mul_left (π / 2)) hb
  refine ⟨hs, ?_⟩
  calc |cutPhaseSum π U| = ‖∑' z, cutPhaseTerm π U z‖ := by rw [cutPhaseSum, Real.norm_eq_abs]
    _ ≤ ∑' z, ‖cutPhaseTerm π U z‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' z, π / 2 * g z := Summable.tsum_le_tsum hb hs.norm (hgs.mul_left _)
    _ ≤ π / 2 * C := tsum_mul_left.trans_le (mul_le_mul_of_nonneg_left hgt (by positivity))

lemma not_eigen_neg_one_of_traceBound {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C) (hC2 : C < 2)
    {v : H} (hv : v ≠ 0) : U v ≠ (-1 : ℂ) • v := by
  intro hUv
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  haveI := finiteDimensional_eigenspace hC hne
  have hpos : 0 < eigenMult U (-1 : ℂ) := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hUv⟩, fun h => hv (by simpa using h)⟩
  have h := sum_eigenMult_mul_norm_le hU hC hT {⟨-1, hne⟩}
  rw [Finset.sum_singleton] at h
  have h2 : ‖((-1 : ℂ) - 1)‖ = 2 := by norm_num
  simp only [h2] at h
  have : (1 : ℝ) ≤ eigenMult U (-1 : ℂ) := by exact_mod_cast hpos
  linarith

end General

theorem exists_linear_traceBound_monodromyAt {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → TraceBound (monodromyAt γ E - 1) (C * E) := by
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  set Cq : ℝ := 1 / 4 * ((R * K * 3) * (2 * π))
  choose Ws hWs using fun E' : ℝ => transport_exists_of_lipschitz γ hK E'
  have hCq0 : 0 ≤ Cq := (traceBound_curvatureOp hK hR (hWs 0)).nonneg
  refine ⟨Cq, hCq0, fun E hE => ?_⟩
  have hW : TraceBound (Ws E (2 * π) - 1) (Cq * E) := by
    rcases eq_or_lt_of_le hE with rfl | hEpos
    · rw [transport_zero_energy (hWs 0), sub_self, mul_zero]; exact TraceBound.zero
    have hlim : Tendsto (fun δ => Ws E (2 * π) - Ws δ (2 * π)) (𝓝[>] 0)
        (𝓝 (Ws E (2 * π) - 1)) := by
      have h := tendsto_transport_energy hK hWs 0 h2π
      rw [transport_zero_energy (hWs 0)] at h
      exact (tendsto_const_nhds.sub h).mono_left nhdsWithin_le_nhds
    refine TraceBound.of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hEpos] with δ hδ
    refine (TraceBound.sub_of_hasDerivAt (g := fun E' => Ws E' (2 * π))
      (g' := fun t => -(Complex.I • (Ws t (2 * π) * curvatureOp γ (Ws t)))) hδ.2.le
      (fun t ht => hasDerivAt_transport_energy hK hclosed hWs (hδ.1.trans_le ht.1))
      fun t _ => ?_).mono (mul_le_mul_of_nonneg_left (by linarith [hδ.1]) hCq0)
    have h := ((traceBound_curvatureOp hK hR (hWs t)).unitary_mul
      (transport_mem_unitary hK (hWs t) h2π)).smul Complex.I
    rw [Complex.norm_I, one_mul] at h
    exact h.neg
  have hU := transport_mem_unitary hK (hWs E) h2π
  have heq : monodromy (Ws E) - 1 = -(star (Ws E (2 * π)) * (Ws E (2 * π) - 1)) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint, mul_sub, (Unitary.mem_iff.mp hU).1,
      mul_one, neg_sub]
  rw [monodromyAt_eq hK (hWs E), heq]
  exact (hW.unitary_mul (Unitary.star_mem hU)).neg

end PolyaNeumann
