module

public import AnalyticESC.Main.Criterion
public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# The polynomial example of Section 1.2.2

The system `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` lies in `𝔖_3` for
`ε = 1/100`, has `c_max < 1/5`, `β ≤ 1` and distortions `1/2`-apart at `0`, so Proposition 1.8
shows that it satisfies the SESC.
-/

namespace Challenge

/-- The maps of the polynomial example in Section 1.2.2. -/
noncomputable def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

end Challenge

namespace AnalyticESC

open Set Metric Filter Topology Challenge
export Challenge (exampleMaps)

/-! ### Points of `cl B_{1/100}` -/

private lemma example_bounds {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖z‖ ≤ 101 / 100 ∧ -(1 / 100) ≤ z.re := by
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le (by norm_num) hz
  have h1 := norm_sub_norm_le z x
  have h2 := Complex.abs_re_le_norm (z - x)
  rw [Complex.norm_real, Real.norm_of_nonneg hx.1] at h1
  rw [Complex.sub_re, Complex.ofReal_re] at h2
  exact ⟨by linarith [hx.2], by linarith [neg_abs_le (z.re - x), hx.1]⟩

/-! ### The maps and their derivatives -/

private lemma hasDerivAt_exampleMaps_zero (z : ℂ) : HasDerivAt (exampleMaps 0) (1 / 8) z :=
  hasDerivAt_id' z |>.div_const 8

private lemma hasDerivAt_exampleMaps_one (z : ℂ) :
    HasDerivAt (exampleMaps 1) (1 / 8 + z / 16) z :=
  ((hasDerivAt_id' z |>.div_const 8).add ((hasDerivAt_pow 2 z).div_const 32)).congr_deriv
    (by push_cast; ring)

private lemma hasDerivAt_exampleMaps_two (z : ℂ) :
    HasDerivAt (exampleMaps 2) (1 / 16 + z / 16) z :=
  (((hasDerivAt_id' z |>.div_const 16).add
    ((hasDerivAt_pow 2 z).div_const 32)).add_const (29 / 32 : ℂ)).congr_deriv
    (by push_cast; ring)

lemma deriv_exampleMaps_zero : deriv (exampleMaps 0) = fun _ => 1 / 8 :=
  funext fun z => (hasDerivAt_exampleMaps_zero z).deriv

lemma deriv_exampleMaps_one : deriv (exampleMaps 1) = fun z => 1 / 8 + z / 16 :=
  funext fun z => (hasDerivAt_exampleMaps_one z).deriv

private lemma deriv_exampleMaps_two : deriv (exampleMaps 2) = fun z => 1 / 16 + z / 16 :=
  funext fun z => (hasDerivAt_exampleMaps_two z).deriv

/-! ### Values at real points -/

lemma exampleMaps_zero_ofReal (x : ℝ) : exampleMaps 0 x = ((x / 8 : ℝ) : ℂ) := by
  change (x : ℂ) / 8 = _; push_cast; rfl

lemma exampleMaps_one_ofReal (x : ℝ) :
    exampleMaps 1 x = ((x / 8 + x ^ 2 / 32 : ℝ) : ℂ) := by
  change (x : ℂ) / 8 + (x : ℂ) ^ 2 / 32 = _; push_cast; rfl

lemma exampleMaps_two_ofReal (x : ℝ) :
    exampleMaps 2 x = ((x / 16 + x ^ 2 / 32 + 29 / 32 : ℝ) : ℂ) := by
  change (x : ℂ) / 16 + (x : ℂ) ^ 2 / 32 + 29 / 32 = _; push_cast; rfl

/-! ### Norm estimates -/

private lemma example_norm_deriv_le (c : ℂ) {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖c + z / 16‖ ≤ ‖c‖ + 101 / 100 / 16 := by
  have hz' := (example_bounds hz).1
  refine (norm_add_le _ _).trans ?_
  rw [norm_div]; norm_num; linarith

private lemma example_re_deriv_pos (c : ℝ) (hc : 1 / 1600 < c) {z : ℂ}
    (hz : z ∈ closure (nbhd (1 / 100))) : (c : ℂ) + z / 16 ≠ 0 := by
  have hz' := (example_bounds hz).2
  intro h
  have h' := congrArg Complex.re h
  rw [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.zero_re] at h'
  linarith

private lemma example_fin_three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

private lemma example_norm_deriv_le_all (i : Fin 3) {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖deriv (exampleMaps i) z‖ ≤ 19 / 100 := by
  obtain rfl | rfl | rfl := example_fin_three i
  · rw [deriv_exampleMaps_zero]; norm_num
  · rw [deriv_exampleMaps_one]; exact (example_norm_deriv_le _ hz).trans (by norm_num)
  · rw [deriv_exampleMaps_two]; exact (example_norm_deriv_le _ hz).trans (by norm_num)

/-! ### The three maps lie in the class -/

theorem exampleMaps_inClass (i : Fin 3) : InClass (1 / 100) (exampleMaps i) := by
  refine InClass.of_deriv (by norm_num) (fun z _ => ?_) (fun x _ => ?_) (fun x hx => ?_)
    (fun z hz => ?_) (fun z hz => (example_norm_deriv_le_all i hz).trans_lt (by norm_num))
  · obtain rfl | rfl | rfl := example_fin_three i
    · exact (hasDerivAt_exampleMaps_zero z).differentiableAt.differentiableWithinAt
    · exact (hasDerivAt_exampleMaps_one z).differentiableAt.differentiableWithinAt
    · exact (hasDerivAt_exampleMaps_two z).differentiableAt.differentiableWithinAt
  · obtain rfl | rfl | rfl := example_fin_three i <;>
      simp only [exampleMaps_zero_ofReal, exampleMaps_one_ofReal, exampleMaps_two_ofReal,
        Complex.ofReal_im]
  · obtain ⟨h0, h1⟩ := hx
    obtain rfl | rfl | rfl := example_fin_three i <;>
      simp only [exampleMaps_zero_ofReal, exampleMaps_one_ofReal, exampleMaps_two_ofReal,
        Complex.ofReal_re] <;>
      constructor <;> nlinarith
  · obtain rfl | rfl | rfl := example_fin_three i
    · rw [deriv_exampleMaps_zero]; norm_num
    · rw [deriv_exampleMaps_one]
      have h := example_re_deriv_pos (1 / 8) (by norm_num) hz; push_cast at h; exact h
    · rw [deriv_exampleMaps_two]
      have h := example_re_deriv_pos (1 / 16) (by norm_num) hz; push_cast at h; exact h

/-- The example as an IFS in `𝔖_3`, with `ε = 1/100`. -/
noncomputable def exampleIFS : IFS 3 (1 / 100) where
  f := exampleMaps
  ε_pos := by norm_num
  inClass := exampleMaps_inClass

/-! ### The constants `c_max` and `β` -/

theorem exampleIFS_cmax_lt : exampleIFS.cmax < 1 / 5 := by
  have : Nonempty (closure (nbhd (1 / 100 : ℝ))) := ⟨⟨0, zero_mem_closure_nbhd (by norm_num)⟩⟩
  exact (ciSup_le fun i => ciSup_le fun z => example_norm_deriv_le_all i z.2).trans_lt (by norm_num)

private lemma example_nonlin_zero (z : ℂ) : exampleIFS.nonlin 0 z = 0 := by
  change deriv (deriv (exampleMaps 0)) z / deriv (exampleMaps 0) z = 0
  rw [deriv_exampleMaps_zero, deriv_const, zero_div]

private lemma example_nonlin_one (z : ℂ) :
    exampleIFS.nonlin 1 z = 1 / 16 / (1 / 8 + z / 16) := by
  change deriv (deriv (exampleMaps 1)) z / deriv (exampleMaps 1) z = _
  rw [deriv_exampleMaps_one, ((hasDerivAt_id' z).div_const 16 |>.const_add (1 / 8)).deriv]

private lemma example_nonlin_two (z : ℂ) :
    exampleIFS.nonlin 2 z = 1 / 16 / (1 / 16 + z / 16) := by
  change deriv (deriv (exampleMaps 2)) z / deriv (exampleMaps 2) z = _
  rw [deriv_exampleMaps_two, ((hasDerivAt_id' z).div_const 16 |>.const_add (1 / 16)).deriv]

/-! ### Separation of the distortions and the SESC -/

/-- The example satisfies the SESC. -/
theorem exampleIFS_sesc : exampleIFS.SESC := by
  have h0 := example_nonlin_zero 0
  have h1 : exampleIFS.nonlin 1 0 = 1 / 2 := by rw [example_nonlin_one]; norm_num
  have h2 : exampleIFS.nonlin 2 0 = 1 := by rw [example_nonlin_two]; norm_num
  have hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ x ∈ I, (1 / 2 : ℝ) ≤ ‖exampleIFS.nonlin i x - exampleIFS.nonlin j x‖ := fun i j hij =>
    ⟨0, ⟨le_rfl, zero_le_one⟩, by
      rw [Complex.ofReal_zero]
      obtain rfl | rfl | rfl := example_fin_three i <;>
        obtain rfl | rfl | rfl := example_fin_three j <;>
        first | exact absurd rfl hij | (simp only [h0, h1, h2]; norm_num)⟩
  obtain ⟨_, h⟩ := exampleIFS.proposition_1_8 (by norm_num) (by norm_num) hsep
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  have hb : exampleIFS.beta ≤ 1 := ciSup_le fun x => ciSup_le fun i => by
    have hx0 := x.2.1
    have hbd (c : ℝ) (hc : 1 / 16 ≤ c) : ‖(1 / 16 : ℂ) / (c + (x : ℂ) / 16)‖ ≤ 1 := by
      rw [show (1 / 16 : ℂ) / (c + (x : ℂ) / 16) =
        ((1 / 16 / (c + (x : ℝ) / 16) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg (by norm_num) (by linarith)), div_le_one (by linarith)]
      linarith
    obtain rfl | rfl | rfl := example_fin_three i
    · rw [example_nonlin_zero, norm_zero]; exact zero_le_one
    · rw [example_nonlin_one]; simpa using hbd (1 / 8) (by norm_num)
    · rw [example_nonlin_two]; simpa using hbd (1 / 16) le_rfl
  have hc := exampleIFS_cmax_lt
  have hc0 := exampleIFS.cmax_nonneg
  refine (h ?_).2
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

end AnalyticESC
