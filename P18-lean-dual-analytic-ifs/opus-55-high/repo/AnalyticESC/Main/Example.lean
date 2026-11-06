module

public import AnalyticESC.Main.Criterion
public import AnalyticESC.Generic.Class
set_option hygiene false
local notation "𝔞" => (hasDerivAt_pow 2 z).div_const 32
local notation "𝖑" => exampleMaps i

local notation "𝖐" => 1 / 100


@[expose] public section

/-!
# The polynomial example of Section 1.2.2

The system `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` lies in `𝔖_3` for
`ε = 1/100`, has `c_max < 1/5`, `β ≤ 1` and distortions `1/2`-apart at `0`, so Proposition 1.8
shows that it satisfies the SESC.
-/

namespace AnalyticESC
variable (i : Fin 3) (x : ℝ)

variable {z : ℂ}



/-- The maps of the polynomial example in Section 1.2.2. -/
noncomputable def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

lemma example_fin_three : i = 0 ∨ i = 1 ∨ i = 2 := by grind

/-! ### The maps and their derivatives -/

lemma hasDerivAt_exampleMaps_zero z : HasDerivAt (exampleMaps 0) (1 / 8) z :=
  hasDerivAt_id' z |>.div_const 8

lemma hasDerivAt_exampleMaps_one z : HasDerivAt (exampleMaps 1) (1 / 8 + z / 16) z :=
  ((hasDerivAt_id' z |>.div_const 8).add 𝔞).congr_deriv
    (by grind)

lemma hasDerivAt_exampleMaps_two z : HasDerivAt (exampleMaps 2) (1 / 16 + z / 16) z :=
  (((hasDerivAt_id' z |>.div_const 16).add 𝔞).add_const
    (29 / 32 : ℂ)).congr_deriv (by grind)

lemma deriv_exampleMaps_zero : deriv (exampleMaps 0) = fun _ => 1 / 8 :=
  funext fun z => (hasDerivAt_exampleMaps_zero z).deriv

lemma deriv_exampleMaps_one : deriv (exampleMaps 1) = fun z => 1 / 8 + z / 16 :=
  funext fun z => (hasDerivAt_exampleMaps_one z).deriv

lemma deriv_exampleMaps_two : deriv (exampleMaps 2) = fun z => 1 / 16 + z / 16 :=
  funext fun z => (hasDerivAt_exampleMaps_two z).deriv

lemma exampleMaps_zero_ofReal : exampleMaps 0 x = ((x / 8 : ℝ) : ℂ) := by aesop

lemma exampleMaps_one_ofReal : exampleMaps 1 x = ((x / 8 + x ^ 2 / 32 : ℝ) : ℂ) := by aesop

lemma exampleMaps_two_ofReal :
    exampleMaps 2 x = ((x / 16 + x ^ 2 / 32 + 29 / 32 : ℝ) : ℂ) := by aesop

/-! ### Norm estimates -/

/-- On `cl B_{1/100}`, `|c + z/16| ≤ |c| + 101/1600` and `c + z/16 ≠ 0` for `c > 1/1600`. -/
lemma example_deriv_le {c : ℝ} (hc : 1 / 1600 < c) (hz : z ∈ 𝔹 𝖐) :
    c + z / 16 ≠ 0 ∧ ‖c + z / 16‖ ≤ c + 101 / 1600 := by
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le (by norm_num) hz
  have h1 := norm_sub_norm_le z x
  have h2 := Complex.abs_re_le_norm (z - x)
  rw [Complex.norm_real, Real.norm_of_nonneg hx.1] at h1
  rw [Complex.sub_re, Complex.ofReal_re] at h2
  refine ⟨fun h => ?_, (norm_add_le _ _).trans ?_⟩
  · have h' := congrArg Complex.re h
    rw [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.zero_re] at h'
    grind
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    norm_num
    grind

/-- On `cl B_{1/100}`, `0 < |f_i'| ≤ 19/100`. -/
lemma example_deriv (hz : z ∈ 𝔹 𝖐) :
    deriv 𝖑 z ≠ 0 ∧ ‖deriv 𝖑 z‖ ≤ 19 / 100 := by
  obtain rfl | rfl | rfl := example_fin_three i
  · norm_num [deriv_exampleMaps_zero]
  · have := example_deriv_le (c := 1 / 8) (by norm_num) hz
    push_cast at this
    exact deriv_exampleMaps_one ▸ ⟨this.1, this.2.trans (by norm_num)⟩
  · have := example_deriv_le (c := 1 / 16) (by norm_num) hz
    push_cast at this
    exact deriv_exampleMaps_two ▸ ⟨this.1, this.2.trans (by norm_num)⟩

/-! ### The three maps lie in the class -/

lemma example_inClass {i : Fin 3} (g : ℝ → ℝ) (hd : Differentiable ℂ 𝖑)
    (hg : ∀ x : ℝ, exampleMaps i x = g x) (hI : Ɐ g x ∈ I) :
    InClass 𝖐 𝖑 :=
  InClass.of_deriv (by norm_num) hd.differentiableOn (fun x _ => by simp_all)
    (fun x hx => by simp_all) (fun z hz => (example_deriv i hz).1)
    (fun z hz => (example_deriv i hz).2.trans_lt (by norm_num))

theorem exampleMaps_inClass : InClass 𝖐 𝖑 := by
  obtain rfl | rfl | rfl := example_fin_three i
  · exact example_inClass _ (fun z => (hasDerivAt_exampleMaps_zero z).differentiableAt)
      exampleMaps_zero_ofReal fun x ⟨h0, h1⟩ => ⟨by linarith, by linarith⟩
  · exact example_inClass _ (fun z => (hasDerivAt_exampleMaps_one z).differentiableAt)
      exampleMaps_one_ofReal fun x ⟨h0, h1⟩ => ⟨by positivity, by nlinarith⟩
  · exact example_inClass _ (fun z => (hasDerivAt_exampleMaps_two z).differentiableAt)
      exampleMaps_two_ofReal fun x ⟨h0, h1⟩ => ⟨by positivity, by nlinarith⟩

/-- The example as an IFS in `𝔖_3`, with `ε = 1/100`. -/
noncomputable def exampleIFS : IFS 3 𝖐 where
  f := exampleMaps
  ε_pos := by norm_num
  inClass := exampleMaps_inClass

/-! ### The constants `c_max` and `β` -/

theorem exampleIFS_cmax_lt : exampleIFS.cmax < 1 / 5 := by
  have : Nonempty (𝔹 (1 / 100 : ℝ)) := ⟨⟨0, zero_mem_closure_nbhd (by norm_num)⟩⟩
  have h : exampleIFS.cmax ≤ 19 / 100 :=
    ciSup_le fun i => ciSup_le fun z => (example_deriv i z.2).2
  linarith

theorem exampleIFS_beta_le : exampleIFS.beta ≤ 1 := by
  refine ciSup_le fun x => ciSup_le fun i => ?_
  fin_cases i <;>
    simp [IFS.nonlin, exampleIFS, deriv_exampleMaps_zero, deriv_exampleMaps_one,
      deriv_exampleMaps_two] <;>
    refine div_le_one_of_le₀ ((Complex.re_le_norm _).trans' ?_) (norm_nonneg _) <;> norm_num <;>
    linarith [x.2.1]

/-! ### Separation of the distortions and the SESC -/

/-- The example satisfies the SESC. -/
theorem exampleIFS_sesc : exampleIFS.SESC := by
  obtain ⟨hβ, h⟩ := exampleIFS.proposition_1_8 (α := 1 / 2) (by norm_num) (by norm_num)
    fun i j hij => ⟨0, zero_mem_I, by
      revert hij
      fin_cases i <;> fin_cases j <;>
        norm_num [IFS.nonlin, exampleIFS, deriv_exampleMaps_zero, deriv_exampleMaps_one,
          deriv_exampleMaps_two]⟩
  have hc := exampleIFS_cmax_lt
  have hb := exampleIFS_beta_le
  refine (h ?_).2
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The example lies in `𝔖_3` for some `ε > 0` and satisfies the SESC. -/
theorem example_sesc :
    ∃ ε > 0, ∃ Φ : IFS 3 ε, Φ.f = exampleMaps ∧ Φ.SESC :=
  ⟨1 / 100, by norm_num, exampleIFS, rfl, exampleIFS_sesc⟩

end AnalyticESC
