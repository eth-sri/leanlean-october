module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ImprovedExponents.Pipeline.Claims
public import ImprovedExponents.Pipeline.Choose
public import ImprovedExponents.Pipeline.Solved
public import ImprovedExponents.Total.Explicit
public import ImprovedExponents.Total.Uniform
public import ImprovedExponents.Total.Lop

@[expose] public section

/-!
# Exact Triangle from a thin-product claim

The deduction of Section 3 of the paper for programs, with rational exponents in the program text.

* `explicitFrom_of_thinClaim_orig`: the reduction of Theorem 17 as printed, with
  `D(n) = ⌊n^d⌋` and `g = ⌈D^η⌉`. A thin-product claim with exponents `γ`, `q` on the instances with
  `D ≤ N^ε`, `d < ε`, gives Exact Triangle in time `O(κ n^{3-δ} log n)` for every
  `δ < d min(η, min(γ, 1/2 - q) - η)`.
* `explicitFrom_of_thinClaim_mid`: the reduction that passes the true size of the middle part. With
  the prime size `σ ∈ (1/2, 1)` and the inner dimension `≈ n^e` it runs the host at
  `D' = ⌊n^{2σe}⌋`, `g' = ⌈D'^{(2σ-1)/(2σ)}⌉`, and gives every
  `δ < e min(2σ - 1, min(γ, σ - q) - (2σ - 1))`. It holds in every time model `M` that detects
  Lop-AE-SparseTri as `lightModel` does and has the host at the true size of the middle part
  (`MidHostRat M`); `lightModel` is one (`midHostRat_light`).
* `explicitFrom_tuple`: the second statement for an admissible tuple `(c, θ, σ, ε)` and every `δ`
  below its saving `tupleSaving c θ σ ε`, in the same models.
* `allSolved_of_explicitFrom`: from there to the four problems on the word RAM.
-/

namespace ImprovedExponents

open Light Light.Sec3 ParamRoutines

/-- **From Exact Triangle to the four problems**, for the programs. -/
def allSolved_of_explicitFrom {δ} {e} hδ0 (hδ1 : δ ≤ 1)
    (h : ExplicitFrom lightModel δ e) :=
  allSolved_of_uniform hδ1 h
    (exactTriangleUniform_of_explicitFrom lightModel e hδ0 hδ1 h claim_bruteForce
      closure_chooseBySize fun _ _ hle hT => SolvedIn.mono hT hle)

/-- The Lop claim from a thin-product claim of the program model, with the exponent capped at 1. -/
def lopClaim_of_thinClaim_light {ε γ q} (hthin : ThinClaim lightModel ε γ q) (hγ : 0 ≤ γ)
    (hq : 0 ≤ q) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :=
  lopClaim_of_thinClaim lightModel (le_min hγ zero_le_one) hq
    (by nlinarith [min_le_right γ 1, le_min hγ zero_le_one])
    (hthin.mono_gamma (min_le_left _ _)) claim_lopCountFromThinProduct claim_lopDetectFromCount

/-- A Lop claim of `lightModel` is one of every model that detects Lop-AE-SparseTri as `lightModel`
does. -/
theorem LopClaim.of_lopDetect_eq {M} (hM : M.lopDetect = lightModel.lopDetect)
    {ε γ q} (h : LopClaim lightModel ε γ q) : LopClaim M ε γ q := by
  obtain ⟨C, Td, hTd, hb⟩ := h
  exact ⟨C, Td, by rw [hM]; exact hTd, hb⟩

/-- **The reduction charged at the true size of the middle part**, at a rational prime size `σ`
and a rational exponent `e` of the inner dimension. -/
theorem explicitFrom_of_thinClaim_mid {ε γ q δ} {σ e : ℚ}
    (hthin : ThinClaim lightModel ε γ q) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hε : ε ≤ 1 / 2)
    (hσ1 : (1 / 2 : ℝ) < σ) (hσ2 : (σ : ℝ) < 1) (he0 : (0 : ℝ) < e) (he : (e : ℝ) < ε)
    (hδ0 : 0 ≤ δ) (hsmall : 3 * (σ : ℝ) * e + δ ≤ 19 / 100)
    (hδ : δ < (e : ℝ) * min (2 * (σ : ℝ) - 1) (min γ (σ - q) - (2 * σ - 1)))
     M (hM : M.lopDetect = lightModel.lopDetect) (hhost : MidHostRat M) :
    ExplicitFrom M δ 1 := by
  set d : ℚ := 2 * σ * e with hd
  set η : ℚ := (2 * σ - 1) / (2 * σ) with hη
  have hdR : (d : ℝ) = 2 * σ * e := by rw [hd]; push_cast; ring
  have hηR : (η : ℝ) = (2 * σ - 1) / (2 * σ) := by rw [hη]; push_cast; ring
  have hd0R : (0 : ℝ) < d := by rw [hdR]; positivity
  have hη0R : (0 : ℝ) < η := by ram_arith
  have hη1R : (η : ℝ) < 1 / 2 := by
    rw [hηR, div_lt_iff₀ (by linarith)]
    linarith
  have hd0 : 0 < d := mod_cast hd0R
  have hη0 : 0 < η := mod_cast hη0R
  have hone : 1 - (η : ℝ) = 1 / (2 * σ) := by
    grind





  have hhost := hhost d.num.toNat d.den η.num.toNat η.den d.den_pos η.den_pos (by
    have  := mul_num_lt_mul_den hd0.le (k := 1) (l := 1) (by norm_num)
      (by push_cast; linarith)
    omega
  ) (by
    have  := mul_num_lt_mul_den hη0.le (k := 1) (l := 2) (by norm_num)
      (by push_cast; linarith)
    omega
  )
  -- the three exponents, in terms of `σ` and `e`
  have h1 : (d : ℝ) * η = e * (2 * σ - 1) := by
    rw [hdR, hηR]
    field_simp



  have hkey :=
    calc (d : ℝ) * min (η : ℝ) (min (min γ 1 * (1 - η)) (1 / 2 - q * (1 - η)) - η)
        = min ((d : ℝ) * η)
            (d * (min (min γ 1 * (1 - η)) (1 / 2 - q * (1 - η)) - η)) :=
          mul_min_of_nonneg _ _ hd0R.le
      _ = min ((d : ℝ) * η) (min (d * (min γ 1 * (1 - η)))
            (d * (1 / 2 - q * (1 - η))) - d * η) := by
          rw [mul_sub, mul_min_of_nonneg _ _ hd0R.le]
      _ = min ((e : ℝ) * (2 * σ - 1))
            (min (e * min γ 1) (e * (σ - q)) - e * (2 * σ - 1)) := by
          rw [h1, (by
            rw [hone, hdR]
            field_simp
           : (d : ℝ) * (min γ 1 * (1 - η)) = e * min γ 1), (by
            rw [hone, hdR]
            field_simp
           : (d : ℝ) * (1 / 2 - q * (1 - η)) = e * (σ - q))]
      _ = min ((e : ℝ) * (2 * σ - 1))
            (e * (min (min γ 1) (σ - q) - (2 * σ - 1))) := by
          grind [mul_min_of_nonneg]
      _ = (e : ℝ) * min (2 * (σ : ℝ) - 1) (min (min γ 1) (σ - q) - (2 * σ - 1)) :=
          (mul_min_of_nonneg _ _ he0.le).symm
      _ = e * min (2 * (σ : ℝ) - 1) (min γ (σ - q) - (2 * σ - 1)) := by rw [(by
        grind
       : min (min γ 1) (σ - q) = min γ (σ - q))]
  refine explicitFrom_mid M (D := paramDRat d.num.toNat d.den)
    (g := paramGRatOf d.num.toNat d.den η.num.toNat η.den) hd0R hη0R hη1R
    (le_min hγ zero_le_one) hq hδ0 (by rw [hdR]; linarith) (fun n => ?_) (fun n => ?_) hhost ((lopClaim_of_thinClaim_light hthin hγ hq (he0.le.trans he.le) hε).of_lopDetect_eq hM)
    ?_ (by rwa [hkey])
  · rw [(rat_eq_div hd0.le)]
    rfl
  · rw [(rat_eq_div hη0.le)]
    rfl
  · grind

end ImprovedExponents
