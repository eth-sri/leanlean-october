module

public import OAI.Combinatorics.EuclideanRamsey.Discretization

public section


open MeasureTheory Filter Topology Metric

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔟" => (n:ℝ)
local notation "𝔞" => (by positivity)
local notation "𝔠" => (C.map (↑))

notation "𝔳" t:max => (t⁻¹ • v γ)
notation "𝔰" F:71 => ∑ γ ∈ S, c γ * F

theorem rational_smoothing (hd : 1 ≤ d)
    (Λ : Fin s → AddSubgroup (Lattice k)) ν
    (C : 𝕄 k ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose = 1)
    (hcos : ∀ i,cosetPushforward (Λ i) ν = 0)
    (hzero : mass ν = 0) (hfirst : ∀ j,firstMoment ν j = 0)
    (hsecond : ∀ j l,secondMoment ν j l = C j l)
    η (hη : 0 < η) :
    ∃ (n : ℕ) (μ : LatticeRing k) (ζ : ℚ), 0 < ζ ∧
      (∀ i,cosetPushforward (Λ i) μ = 0) ∧
      (∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l) ∧
      (∑' δ : Lattice k,max (-(μ.coeff δ:ℝ)) 0*gradientWeight U (latticeSample n δ)) < η*ζ := by
  obtain ⟨b,hb,hbc,-,hbI,hbη⟩ := compact_smoothing hd 𝔠 U (by simp_all) hU η hη
  obtain ⟨K,hK,hT⟩ := compact_taylor_bound hb hbc
  obtain ⟨r,hr,hbr⟩ := hbc.exists_pos_le_norm
  let S := ν.coeff.support
  let c γ : ℝ := ν.coeff γ
  let v (γ : Lattice k) j := -(γ j : ℝ)
  have hm : ∑ γ ∈ S, c γ = 0 ∧ ∀ j l, 𝔰 v γ j = 0 ∧
      ∑ γ ∈ S, c γ * v γ j * v γ l = C j l := by
    simp [c, v]
    exact_mod_cast And.intro hzero fun j l => And.intro (hfirst j) (hsecond j l)
  have hD t (ht : 0 < t) x : |t^2*(𝔰 b (x+𝔳 t))-stencilDifferential 𝔠 b x| ≤
      (∑ γ ∈ S, |c γ| * K*‖v γ‖^3)/t := by
    have A : 𝔰 b x = 0 := by rw [← Finset.sum_mul, hm.1, zero_mul]
    have B : 𝔰 fderiv ℝ b x (𝔳 t) = 0 := by
      simp [mul_left_comm _ t⁻¹, ← Finset.mul_sum, linear_moment_contract S _ v (fun j => (hm.2 j j).1)]
    have B2 : 𝔰 ((1/2:ℝ)*iteratedFDeriv ℝ 2 b x ![𝔳 t,𝔳 t]) =
        t⁻¹^2 * stencilDifferential 𝔠 b x := by
      have := bilinear_moment_contract S (fun γ => c γ) v (hessianB b x)
      simp only [← hessianB_eq, map_smul, smul_apply, fun j l => (hm.2 j l).2] at *
      simp only [stencilDifferential, secondOperator, ← hessianB_eq, ← this, Matrix.map_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [show t^2*(𝔰 b (x+𝔳 t))-stencilDifferential 𝔠 b x =
      t^2*𝔰 (b (x+𝔳 t)-b x-fderiv ℝ b x (𝔳 t)-
        (1/2:ℝ)*iteratedFDeriv ℝ 2 b x ![𝔳 t,𝔳 t]) by
      simp only [mul_sub, Finset.sum_sub_distrib, A, B, B2]
      field_simp; ring, abs_mul,
      abs_of_pos 𝔞]
    calc _ ≤ t^2 * ∑ γ ∈ S, |c γ| * (K * ‖𝔳 t‖^3) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun γ _ => by
            rw [abs_mul]
            gcongr; exact hT _ _)
      _ = _ := by
          simp [norm_smul, abs_of_pos ht, Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun _ _ => by field_simp
  have hR : 0 < r + ∑ γ ∈ S, ‖v γ‖ := by positivity
  obtain ⟨W,hW⟩ := (isCompact_closedBall (0 : 𝕍 k) (r + ∑ γ ∈ S, ‖v γ‖)).exists_bound_of_continuousOn
    (show Continuous (gradientWeight U) by unfold gradientWeight; fun_prop).continuousOn
  have hd2 := hb.continuous_iteratedFDeriv (m := 2) (by norm_cast)
  have he := lattice_riemann_perturb (fun x => max (-stencilDifferential 𝔠 b x) 0 * gradientWeight U x)
    (fun n x => max (-(𝔟^2*𝔰 b (x+𝔳 𝔟))) 0 * gradientWeight U x)
    (by unfold stencilDifferential secondOperator gradientWeight; fun_prop) hR
    (fun x hx => closedBall_subset_closedBall (le_add_of_nonneg_right 𝔞)
      (closure_minimal (fun y hy => mem_closedBall_zero_iff.2 (not_le.1 (hy ∘ hbr y)).le) isClosed_closedBall
      (support_iteratedFDeriv_subset (𝕜 := ℝ) 2 fun h => hx (by simp [stencilDifferential, secondOperator, h]))))
    (fun n x hx => by
      by_contra h
      refine hx ?_
      dsimp only
      rw [Finset.sum_eq_zero fun γ hγ => ?_]
      · simp
      have := norm_add_le (x + 𝔳 𝔟) (-(𝔳 𝔟))
      have := Finset.single_le_sum (fun γ _ => norm_nonneg (v γ)) hγ
      have := mul_le_of_le_one_left (norm_nonneg (v γ)) (Nat.cast_inv_le_one n)
      simp [norm_smul] at *
      simp [hbr _ (by linarith)])
    (fun n => (∑ γ ∈ S, |c γ| * K*‖v γ‖^3) * W / n)
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop) fun n hn x hx => by
      rw [← sub_mul, abs_mul, mul_div_right_comm]
      exact mul_le_mul ((abs_max_sub_max_le_abs _ _ _).trans (by
        simpa [abs_sub_comm, neg_add_eq_sub] using hD n 𝔞 x)) (hW x hx) (abs_nonneg _) 𝔞
  have hZ := lattice_riemann hb.continuous hbc
  obtain ⟨n,hn,hp,he⟩ := ((eventually_ge_atTop 1).and ((tendsto_const_nhds.eventually_lt hZ hbI).and
    (he.eventually_lt (tendsto_const_nhds.mul hZ) hbη))).exists
  have hs δ γ : latticeSample n δ+𝔳 𝔟 = latticeSample n (δ-γ) := by
    ext
    simp [latticeSample, sub_div]; ring
  have hg X : max (-(𝔟^2*X)) 0 = n^2 * max (-X) 0 := by
    rw [mul_max_of_nonneg _ _ 𝔞, mul_neg, mul_zero]
  simp only [hs, hg, mul_assoc, tsum_mul_left] at he
  obtain ⟨p,hp0,hpη⟩ := rationalize_convolution ν (fun δ => gradientWeight U (latticeSample n δ)) (η/n^2)
    (latticeSample_finite_support (by omega) hbc) ((div_pos_iff_of_pos_right 𝔞).1 hp) (by
      rw [div_mul_eq_mul_div, lt_div_iff₀ 𝔞]
      rw [← mul_div_assoc, div_lt_div_iff_of_pos_right 𝔞] at he
      linarith)
  refine ⟨n, ν*p, mass p/n^2, div_pos (mod_cast hp0) 𝔞, fun i => ?_, fun j l => ?_, ?_⟩
  · have := AddMonoidAlgebra.mapDomain_mul (QuotientAddGroup.mk' (Λ i)) ν p
    rw [show AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' (Λ i)) ν = 0 from AddMonoidAlgebra.coeff_injective (hcos i), zero_mul] at this
    exact congrArg AddMonoidAlgebra.coeff this
  · simp [(moments_mul ν p).2.2, hzero, hfirst, hsecond]
    ring
  · simpa [mul_div_assoc', div_mul_eq_mul_div] using hpη
