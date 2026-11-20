module

public import RequestProject.FixedSpace
public import RequestProject.CutPhase
public import RequestProject.PeriodicForm

/-!
# The Herglotz form and the Cayley rank bound (Proposition 7.10, Lemma 8.7)

For a Herglotz wave `u_a` with conormal trace `g_a` and Dirichlet trace `h_a = u_a ∘ γ`, the
paper's boundary form `⟨g_a, 𝒜_E g_a⟩` with `𝒜_E = 2 𝒩(E) + i (T_E - T_E^*)` reads
(at a nonresonant energy, where `𝒩(E) g_a = h_a`)

  `herglotzForm W γ E a = Re ∫₀^L conj(g_a) (2 h_a + i (T_E - T_E^*) g_a)`.

Both Proposition 7.10 and Lemma 8.7 deduce a bound on the number of eigenphases of `U_E` with
large Cayley eigenvalue `cot(t/2)` from a lower bound on this form on a subspace of finite
codimension. We prove this deduction (`cayleyRankBound_of_herglotzForm_bound`):

* every vector of `ℓ²` is a Herglotz vector `y_a(z)` at any base point `z`
  (`herglotzVec_synthDens`), and `a ↦ y_a(z)` is linear (`herglotzVecLin`);
* the Herglotz form is `Re ⟨O_E^* g_a, √2 (y + V_E^* y)⟩` with `O_E^* g_a = √2 i (V_E^* - I) y`,
  `y = y_a(γ(0))` (`herglotzForm_eq`; the Cayley factorization of Lemma 4.17, written without
  inverting `I - V_E`); equivalently it is `-4 Im ⟨y, U_E y⟩` (`herglotzForm_eq_im`), so on
  Herglotz data the form only depends on the monodromy;
* on combinations of eigenvectors of `U_E = V_E^*` with eigenvalues `e^{it_k}` this is
  `-∑ |c_k|² cot(t_k/2)` (`re_inner_eigen_sum`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The Herglotz boundary form `Re ∫₀^L conj(g_a) (2 h_a + i (T_E - T_E^*) g_a)`, where
`g_a` is the conormal trace and `h_a = u_a ∘ γ` the Dirichlet trace of the Herglotz wave with
direction density `a` at wave number `√E`, and `T_E` is the Volterra operator of the transport
`W`. At a nonresonant energy this is `Re ⟨g_a, 𝒜_E g_a⟩`. -/
def herglotzForm (W : ℝ → Ell2 →L[ℂ] Ell2) (γ : ℝ → ℂ) (E : ℝ) (a : ℝ → ℂ) : ℝ :=
  (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal (Real.sqrt E) a γ θ) *
    (2 * herglotzWave (Real.sqrt E) a (γ θ) +
      Complex.I * (volterraOp W (herglotzConormal (Real.sqrt E) a γ) θ -
        volterraOpAdj W (herglotzConormal (Real.sqrt E) a γ) θ))).re

section

variable (k : ℝ)
include k

/-- Plane waves are multiplicative in the base point. -/
lemma planeWave_add  (z w : ℂ) (φ : ℝ) :
    planeWave k (z + w) φ = planeWave k z φ * planeWave k w φ := by
  unfold planeWave
  rw [← Complex.exp_add]
  congr 1
  rw [add_mul, Complex.add_re]
  push_cast
  ring

/-- Moving the base point of the Herglotz coefficients into the density. -/
lemma herglotzCoeff_shift  (a : ℝ → ℂ) (m : ℤ) (z : ℂ) :
    herglotzCoeff k (fun φ => a φ * planeWave k (-z) φ) m z = herglotzCoeff k a m 0 := by
  unfold herglotzCoeff
  congr 2
  funext φ
  have h := planeWave_add k (-z) z φ
  grind

end

/-- The Fourier coefficients of the synthesized density: `c₀ = √2 v₀`, `c_n = v_n` (`n ≥ 1`),
`c_n = 0` (`n < 0`). -/
def synthCoeff (v : Ell2) (m : ℤ) : ℂ :=
  if m = 0 then (Real.sqrt 2 : ℂ) * (v : ℕ → ℂ) 0 else if 0 < m then (v : ℕ → ℂ) m.toNat else 0

lemma synthCoeff_add (v w : Ell2) (m : ℤ) :
    synthCoeff (v + w) m = synthCoeff v m + synthCoeff w m := by
  unfold synthCoeff; split_ifs <;> simp [mul_add]

lemma synthCoeff_smul (c : ℂ) (v : Ell2) (m : ℤ) :
    synthCoeff (c • v) m = c * synthCoeff v m := by
  unfold synthCoeff; split_ifs <;> simp; ring

lemma hasSum_sq_synthCoeff (v : Ell2) :
    HasSum (fun m => ‖synthCoeff v m‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2) := by
  have hv : HasSum (fun n : ℕ => ‖(v : ℕ → ℂ) n‖ ^ 2) (‖v‖ ^ 2) := by
    have := lp.hasSum_norm (p := 2) (by norm_num) v
    simp_all
  have hpos : HasSum (fun n : ℕ => ‖synthCoeff v n‖ ^ 2) (‖v‖ ^ 2 + ‖(v : ℕ → ℂ) 0‖ ^ 2) := by
    have h2 := hv.add (hasSum_ite_eq 0 (‖(v : ℕ → ℂ) 0‖ ^ 2))
    refine h2.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hr : ‖(Real.sqrt 2 : ℂ)‖ ^ 2 = 2 := by
        simp
      simp [synthCoeff, mul_pow]
      ring
    grind [synthCoeff, Int.toNat_natCast, add_zero]
  have hneg : HasSum (fun n : ℕ => ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2) 0 := by
    have : ∀ n : ℕ, ‖synthCoeff v (-((n : ℤ) + 1))‖ ^ 2 = 0 := fun n => by grind [synthCoeff, norm_zero]
    simp only [this]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one (f := fun m => ‖synthCoeff v m‖ ^ 2) hpos hneg
  simp_all

lemma memℓp_synthCoeff (v : Ell2) : Memℓp (synthCoeff v) 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa using (hasSum_sq_synthCoeff v).summable

/-- The synthesized `L²` function on the circle. -/
def synthL2 (v : Ell2) : Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _) :=
  fourierBasis.repr.symm ⟨synthCoeff v, memℓp_synthCoeff v⟩

lemma synthL2_add (v w : Ell2) : synthL2 (v + w) = synthL2 v + synthL2 w := by
  unfold synthL2
  rw [← map_add]
  congr 1
  exact lp.ext (funext fun m => synthCoeff_add v w m)

lemma synthL2_smul (c : ℂ) (v : Ell2) : synthL2 (c • v) = c • synthL2 v := by
  unfold synthL2
  rw [← map_smul]
  congr 1
  exact lp.ext (funext fun m => synthCoeff_smul c v m)

lemma fourierCoeff_synthL2 (v : Ell2) (m : ℤ) : fourierCoeff (synthL2 v) m = synthCoeff v m := by
  rw [← fourierBasis_repr, synthL2, LinearIsometryEquiv.apply_symm_apply]

/-- The synthesized density, shifted to the base point `z₁`. -/
def synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) (φ : ℝ) : ℂ :=
  (synthL2 v : AddCircle (2 * π) → ℂ) φ * planeWave k (-z₁) φ

lemma isDirDensity_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) : IsDirDensity (synthDens k z₁ v) := by
  have hfm : MemLp (synthL2 v : AddCircle (2 * π) → ℂ) 2 :=
    memLp_haarAddCircle_iff.mp (Lp.memLp _)
  have ha₀ : IsDirDensity fun φ : ℝ => (synthL2 v : AddCircle (2 * π) → ℂ) φ := by
    have := hfm.comp_measurePreserving (AddCircle.measurePreserving_mk (2 * π) 0)
    rw [zero_add] at this
    exact this
  exact ha₀.of_le ((MemLp.aestronglyMeasurable ha₀).mul (continuous_planeWave k (-z₁)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => by rw [synthDens, norm_mul, norm_planeWave, mul_one])

lemma herglotzCoeff_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) (m : ℤ) :
    herglotzCoeff k (synthDens k z₁ v) m z₁ = synthCoeff v m := by
  unfold synthDens
  rw [herglotzCoeff_shift, herglotzCoeff_zero_eq_fourierCoeff, fourierCoeff_synthL2]

lemma herglotzCoeff_synthDens_neg (k : ℝ) (z₁ : ℂ) (v : Ell2) (j : ℕ) (hj : 1 ≤ j) :
    herglotzCoeff k (synthDens k z₁ v) (-(j : ℤ)) z₁ = 0 := by grind [herglotzCoeff_synthDens, synthCoeff]

lemma herglotzVec_synthDens (k : ℝ) (z₁ : ℂ) (v : Ell2) :
    herglotzVec (isDirDensity_synthDens k z₁ v) k z₁ = v := by
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply]
  unfold herglotzSeq
  split_ifs with hn
  simp_all [herglotzCoeff_synthDens, synthCoeff]
  grind [herglotzCoeff_synthDens, synthCoeff, Int.toNat_natCast]

lemma herglotzCoeff_add_density {a b : ℝ → ℂ} (ha : IsDirDensity a)
    (hb : IsDirDensity b) (k : ℝ) (m : ℤ) (z : ℂ) :
    herglotzCoeff k (a + b) m z = herglotzCoeff k a m z + herglotzCoeff k b m z := by
  unfold herglotzCoeff
  simp only [Pi.add_apply, add_mul, mul_add]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_herglotz ha.intervalIntegrable k m z)
    (intervalIntegrable_herglotz hb.intervalIntegrable k m z), mul_add]

lemma herglotzCoeff_smul_density (a : ℝ → ℂ) (c : ℂ) (k : ℝ) (m : ℤ) (z : ℂ) :
    herglotzCoeff k (c • a) m z = c * herglotzCoeff k a m z := by
  unfold herglotzCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  have h : (fun φ : ℝ => Complex.exp (-((m : ℂ) * φ * Complex.I)) *
      (c * a φ * planeWave k z φ)) = fun φ : ℝ => c *
        (Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a φ * planeWave k z φ)) := by
    grind
  rw [h, intervalIntegral.integral_const_mul]
  ring

lemma herglotzVec_add {a b : ℝ → ℂ} (ha : IsDirDensity a) (hb : IsDirDensity b)
    (k : ℝ) (z : ℂ) :
    herglotzVec (ha.add hb) k z = herglotzVec ha k z + herglotzVec hb k z := by
  refine lp.ext (funext fun n => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, herglotzVec_apply, herglotzSeq,
    herglotzCoeff_add_density ha hb]
  split_ifs <;> simp [add_div]

lemma herglotzVec_smul {a : ℝ → ℂ} (ha : IsDirDensity a) (c : ℂ) (k : ℝ) (z : ℂ) :
    herglotzVec (ha.const_smul c) k z = c • herglotzVec ha k z := by
  refine lp.ext (funext fun n => ?_)
  simp only [lp.coeFn_smul, Pi.smul_apply, herglotzVec_apply, herglotzSeq,
    herglotzCoeff_smul_density, smul_eq_mul]
  split_ifs <;> simp [mul_div_assoc]

/-- The `L²` direction densities, as a submodule of all functions. -/
def dirDensities : Submodule ℂ (ℝ → ℂ) where
  carrier := {a | IsDirDensity a}
  add_mem' ha hb := MemLp.add ha hb
  zero_mem' := MemLp.zero
  smul_mem' c _ ha := MemLp.const_smul ha c

/-- `a ↦ y_a(z)` as a linear map on direction densities. -/
def herglotzVecLin (k : ℝ) (z : ℂ) : dirDensities →ₗ[ℂ] Ell2 where
  toFun a := herglotzVec (a.2 : IsDirDensity a.1) k z
  map_add' a b := herglotzVec_add a.2 b.2 k z
  map_smul' c a := herglotzVec_smul a.2 c k z

lemma sqrt_two_mul_I_ne_zero : ((Real.sqrt 2 : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (by simp)
    Complex.I_ne_zero

/-- `cot(t/2) = i (e^{it} + 1)/(e^{it} - 1)` for `0 < t < 2π`. -/
lemma cot_half_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * π) :
    ((Real.cot (t / 2) : ℝ) : ℂ) = Complex.I * ((Complex.exp (t * Complex.I) + 1) /
      (Complex.exp (t * Complex.I) - 1)) := by
  have he1 := exp_mul_I_ne_one h0 h1
  set w : ℂ := Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) with hwdef
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hew : Complex.exp (t * Complex.I) = w * w := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hew] at he1 ⊢
  have hd2 := sub_ne_zero.mpr he1
  have hd3 : w⁻¹ - w ≠ 0 := by
    grind
  rw [Complex.ofReal_cot, Complex.cot_eq_cos_div_sin, Complex.cos, Complex.sin, neg_mul, Complex.exp_neg]
  rw [div_div_div_cancel_right₀ (two_ne_zero), eq_comm, mul_div_assoc',
    div_eq_div_iff hd2 (mul_ne_zero hd3 Complex.I_ne_zero)]
  grind [Complex.I_sq]

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {a : ℝ → ℂ} (ha : IsDirDensity a)
include γ K hK hclosed E W hW a ha

/-- Cayley factorization of the adjoint observation and of the uncorrected pointwise form. -/
theorem herglotz_cayley_factorization :
    observationAdj W (herglotzConormal (Real.sqrt E) a γ) =
        ((Real.sqrt 2 : ℂ) * Complex.I) • (ContinuousLinearMap.adjoint (W (2 * π)) - 1)
          (herglotzVec ha (Real.sqrt E) (γ 0)) ∧
      EqOn (periodicA W (fun θ => herglotzWave (Real.sqrt E) a (γ θ))
        (herglotzConormal (Real.sqrt E) a γ))
        (observation W ((Real.sqrt 2 : ℂ) • (herglotzVec ha (Real.sqrt E) (γ 0) +
            ContinuousLinearMap.adjoint (W (2 * π)) (herglotzVec ha (Real.sqrt E) (γ 0))))) (Icc 0 (2 * π)) := by
  obtain ⟨hO, htrace⟩ := herglotz_driven_boundary hK hclosed hW ha
  refine ⟨hO, ?_⟩
  set g := herglotzConormal (Real.sqrt E) a γ
  set V := W (2 * π)
  set v := herglotzVec ha (Real.sqrt E) (γ 0)
  intro θ hθ
  have htr := htrace θ hθ
  have hadd := volterraOp_add_adj_of_intervalIntegrable hW.1
    (intervalIntegrable_herglotzConormal ha.intervalIntegrable (Real.sqrt E) hK _ _) hθ
  rw [hO] at hadd
  rw [periodicA]
  simp only [observation, map_smul, map_add, map_sub, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_smul_right, inner_add_right, inner_sub_right]
    at htr hadd ⊢
  linear_combination 2 * htr - Complex.I * hadd +
    ((Real.sqrt 2 : ℂ) * (inner ℂ (basisVec 0) ((W θ) v) -
      inner ℂ (basisVec 0) ((W θ) ((ContinuousLinearMap.adjoint V) v)))) * Complex.I_sq

/-- The Herglotz form through the Cayley factorization (Lemma 4.17, without inverting
`I - V_E`): with `y = y_a(γ(0))`, `O_E^* g_a = √2 i (V_E^* - I) y` and the form is
`Re ⟨O_E^* g_a, √2 (y + V_E^* y)⟩`. -/
theorem herglotzForm_eq  :
    observationAdj W (herglotzConormal (Real.sqrt E) a γ) =
        ((Real.sqrt 2 : ℂ) * Complex.I) • (ContinuousLinearMap.adjoint (W (2 * π)) - 1)
          (herglotzVec ha (Real.sqrt E) (γ 0)) ∧
      herglotzForm W γ E a =
        (⟪observationAdj W (herglotzConormal (Real.sqrt E) a γ),
          (Real.sqrt 2 : ℂ) • (herglotzVec ha (Real.sqrt E) (γ 0) +
            ContinuousLinearMap.adjoint (W (2 * π)) (herglotzVec ha (Real.sqrt E) (γ 0)))⟫_ℂ).re := by
  obtain ⟨hO, hpt⟩ := herglotz_cayley_factorization hK hclosed hW ha
  refine ⟨hO, ?_⟩
  rw [herglotzForm, inner_observationAdj hW.1 (intervalIntegrable_herglotzConormal ha.intervalIntegrable _ hK _ _)]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  exact congrArg (conj (herglotzConormal (Real.sqrt E) a γ θ) * ·) (hpt hθ)

/-- On Herglotz data the form depends only on the monodromy `U_E = V_E^*`:
`herglotzForm W γ E a = -4 Im ⟨y, U_E y⟩` with `y = y_a(γ(0))`. -/
theorem herglotzForm_eq_im  :
    herglotzForm W γ E a = -4 * (⟪herglotzVec ha (Real.sqrt E) (γ 0),
      monodromy W (herglotzVec ha (Real.sqrt E) (γ 0))⟫_ℂ).im := by
  obtain ⟨hO, hF⟩ := herglotzForm_eq hK hclosed hW ha
  rw [hF, hO]
  set y := herglotzVec ha (Real.sqrt E) (γ 0)
  have hU : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
    rw [monodromy]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
  have hnorm : ⟪monodromy W y, monodromy W y⟫_ℂ = ⟪y, y⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.star_eq_adjoint, (Unitary.mem_iff.mp hU).1,
      ContinuousLinearMap.one_apply]
  change (⟪((Real.sqrt 2 : ℂ) * Complex.I) • (monodromy W - 1) y,
    (Real.sqrt 2 : ℂ) • (y + monodromy W y)⟫_ℂ).re = _
  rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, inner_add_right, inner_add_right, hnorm,
    ← inner_conj_symm (monodromy W y) y]
  set w := ⟪y, monodromy W y⟫_ℂ
  have h2 : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have e : -(((Real.sqrt 2 : ℂ)) * Complex.I) * ((Real.sqrt 2 : ℂ) *
      (conj w + ⟪y, y⟫_ℂ - (⟪y, y⟫_ℂ + w))) = -(2 * Complex.I) * (conj w - w) := by
    linear_combination (-(Complex.I) * (conj w - w)) * h2
  rw [show ((Real.sqrt 2 : ℂ)) * -Complex.I = -(((Real.sqrt 2 : ℂ)) * Complex.I) by ring, e]
  simp [Complex.mul_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

end

/-- On combinations of eigenvectors of `U = V^*` with eigenvalues `e^{it_k}`, the Cayley pairing
is `-∑ |c_k|² cot(t_k/2)`. -/
theorem re_inner_eigen_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H →L[ℂ] H) {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℂ v) (t : Fin n → ℝ)
    (ht : ∀ k, 0 < t k ∧ t k < 2 * π) (hU : ∀ k, U (v k) = Complex.exp (t k * Complex.I) • v k)
    (c : Fin n → ℂ) :
    (⟪∑ k, c k • v k, (Real.sqrt 2 : ℂ) •
        (∑ k, c k • (((Real.sqrt 2 : ℂ) * Complex.I) *
            (Complex.exp (t k * Complex.I) - 1))⁻¹ • v k +
          U (∑ k, c k • (((Real.sqrt 2 : ℂ) * Complex.I) *
            (Complex.exp (t k * Complex.I) - 1))⁻¹ • v k))⟫_ℂ).re =
      -∑ k, ‖c k‖ ^ 2 * Real.cot (t k / 2) := by
  set s : ℂ := (Real.sqrt 2 : ℂ) * Complex.I with hs
  set μ : Fin n → ℂ := fun k => Complex.exp (t k * Complex.I) with hμ
  have hsum : (Real.sqrt 2 : ℂ) • (∑ k, c k • (s * (μ k - 1))⁻¹ • v k +
      U (∑ k, c k • (s * (μ k - 1))⁻¹ • v k)) =
      ∑ k, ((Real.sqrt 2 : ℂ) * (c k * (s * (μ k - 1))⁻¹ * (1 + μ k))) • v k := by
    rw [map_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, hU k]
    simp only [μ]
    module
  rw [hsum, hv.inner_sum c _ Finset.univ, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcot := cot_half_eq (ht k).1 (ht k).2
  have hμ1 := sub_ne_zero.mpr (exp_mul_I_ne_one (ht k).1 (ht k).2)
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp
  have hc : conj (c k) * c k = ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; simp
  have key : conj (c k) * ((Real.sqrt 2 : ℂ) * (c k * (s * (μ k - 1))⁻¹ * (1 + μ k))) =
      ((-(‖c k‖ ^ 2 * Real.cot (t k / 2)) : ℝ) : ℂ) := by
    have e1 : conj (c k) * ((Real.sqrt 2 : ℂ) * (c k * (s * (μ k - 1))⁻¹ * (1 + μ k))) =
        (conj (c k) * c k) * (-(Complex.I * ((μ k + 1) / (μ k - 1)))) := by
      rw [hs]
      field_simp
      rw [Complex.I_sq]
      ring
    rw [e1, hc, ← hcot]
    simp
  rw [key, Complex.ofReal_re]

/-- **Proposition 7.10 / Lemma 8.7 (Cayley rank bound from a lower bound on the Herglotz
form).** For a closed Lipschitz curve and a transport `W` at energy `E`, suppose that
`herglotzForm W γ E a ≥ -A₁ ‖O_E^* g_a‖²` for every `L²` density `a` in the kernel of a linear
map `L : (ℝ → ℂ) → ℂ^m`. Then for `A ≥ A₁`, every orthonormal family of eigenvectors of the
monodromy `U_E` with eigenvalues `e^{it}`, `0 < t < 2π`, `cot(t/2) > A`, has at most `m`
members. -/
theorem cayleyRankBound_of_herglotzForm_bound {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) {m : ℕ} (A₁ A : ℝ) (hA : A₁ ≤ A)
    (L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ a (_ : IsDirDensity a), L a = 0 →
      -(A₁ * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
        herglotzForm W γ E a) :
    CayleyRankBound (monodromy W) A m := by
  classical
  intro n v t hv ht hUv hcot
  by_contra hlt
  push_neg at hlt
  set s : ℂ := (Real.sqrt 2 : ℂ) * Complex.I with hs
  set μ : Fin n → ℂ := fun k => Complex.exp (t k * Complex.I) with hμ
  set y : Fin n → Ell2 := fun k => (s * (μ k - 1))⁻¹ • v k with hydef
  let as (i : Fin n) : dirDensities := ⟨synthDens (Real.sqrt E) (γ 0) (y i),
    isDirDensity_synthDens _ _ _⟩
  let φ := L ∘ₗ dirDensities.subtype ∘ₗ Fintype.linearCombination ℂ as
  have hker : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let a : dirDensities := ∑ i, c i • as i
  have ha : IsDirDensity a := a.property
  have hLa : L a = 0 := hc
  obtain ⟨hO, hF⟩ := herglotzForm_eq hK hclosed hW ha
  have hy : herglotzVec ha (Real.sqrt E) (γ 0) = ∑ i, c i • y i := by
    change herglotzVecLin _ _ (∑ i, c i • as i) = _
    simp [map_sum, as, herglotzVecLin, herglotzVec_synthDens]
  have hμ1 : ∀ k, μ k - 1 ≠ 0 := fun k =>
    sub_ne_zero.mpr (exp_mul_I_ne_one (ht k).1 (ht k).2)
  have hs0 : s ≠ 0 := sqrt_two_mul_I_ne_zero
  have hx : observationAdj W (herglotzConormal (Real.sqrt E) a γ) = ∑ k, c k • v k := by
    rw [hO, hy, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_comm, hydef]
    simp only [map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    have hU := hUv k
    rw [monodromy] at hU
    have e : Complex.exp (t k * Complex.I) • v k - v k =
        (Complex.exp (t k * Complex.I) - 1) • v k := by rw [sub_smul, one_smul]
    rw [hU, e, smul_smul, smul_smul]
    rw [smul_smul]
    refine congrArg (fun r : ℂ => r • v k) ?_
    have h1 := hμ1 k
    simp only [hμ] at h1 ⊢
    rw [← hs]
    field_simp
  have hb := hbound a ha hLa
  rw [hF, hx, hy] at hb
  have hre := re_inner_eigen_sum (monodromy W) v hv t ht hUv c
  simp only [monodromy] at hre
  rw [hre] at hb
  have hn : ‖∑ k, c k • v k‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hv.inner_sum c c Finset.univ]
    simp [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  rw [hn] at hb
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hc0 (funext hall)
  have hlt2 : A * ∑ k, ‖c k‖ ^ 2 < ∑ k, ‖c k‖ ^ 2 * Real.cot (t k / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hcot i).le (by positivity)
    · exact ⟨j, Finset.mem_univ _, by rw [mul_comm]; exact mul_lt_mul_of_pos_left (hcot j) (by positivity)⟩
  have hnn : 0 ≤ ∑ k, ‖c k‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  nlinarith [mul_le_mul_of_nonneg_right hA hnn]

end PolyaNeumann
