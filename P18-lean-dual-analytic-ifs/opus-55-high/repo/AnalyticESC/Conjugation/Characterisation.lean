module

public import AnalyticESC.Conjugation.Uniqueness
public import AnalyticESC.Conjugation.Composite

public section

set_option hygiene false
local notation "𝔞" => Φ.f k
local notation "𝖅" => Ɐ deriv g x ≠ 0
local notation "𝖔" => p k₀

local notation "𝖓" => Φ.f k₀

local notation "𝖒" => p k

local notation "𝖑" => Φ.inClass k

local notation "𝖐" => hp k

local notation "𝖏" => koenigs 𝔞 𝖒

/-!
# Single-map conjugation

If the functions `Ĥ_{f_k}` all agree on `[0,1]`, the real part of the linearising map of one of
the `f_k` conjugates every `f_k` to a contracting similarity.
-/

namespace AnalyticESC

variable {x : ℝ}



variable {f : ℂ → ℂ}

/-- At points of `[0,1]`, the derivative of a map of the class is real, nonzero and of modulus
less than one. -/
theorem char_re_deriv_ne_zero_abs_lt_one (hε : 0 < ε) (hf : InClass ε f)
    (hx : x ∈ I) : (deriv f x).re ≠ 0 ∧ |(deriv f x).re| < 1 := by
  have hcl := ofReal_mem_closure hε hx
  exact ⟨fun h => hf.deriv_ne_zero _ hcl (Complex.ext h (im_deriv_eq_zero isOpen_nbhd hf.differentiableOn hf.im_eq_zero (ofReal_mem_nbhd (by linarith) hx))),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

/-- `Re ĝ ∘ f = Re f'(p) · Re ĝ` on `[0,1]`. -/
theorem char_re_koenigs_conj (hε : 0 < ε) (hf : InClass ε f) (hp : p ∈ I)
    (hfp : f p = p) (hx : x ∈ I) :
    (koenigs f p ((f x).re : ℂ)).re = (deriv f p).re * (koenigs f p x).re := by
  have hx' := ofReal_mem_nbhd hε hx
  have hfx : (((f x).re : ℝ) : ℂ) = f x :=
    Complex.ext (by simp) (by simp [hf.im_eq_zero x (ofReal_mem_nbhd (by linarith) hx)])
  rw [hfx, koenigs_comp hε hf hp hfp hx', Complex.mul_re, im_koenigs_ofReal hε hf hp hx',
    mul_zero, sub_zero]

namespace IFS

variable (Φ : IFS N ε)

/-- If `Ĥ_{f_k} = Ĥ_{f_{k₀}}` on `[0,1]` for every `k`, then `Re ĝ` for `f_{k₀}` is an analytic
coordinate with nonvanishing derivative conjugating every `f_k` to a contracting similarity
(Lemma 5.1). -/
theorem exists_conj_of_hatH_eq (k₀ : Fin N)
    (hH : ∀ k, Ɐ hatH 𝔞 x = hatH 𝖓 x) :
    ∃ g, IsAnalyticCoord g ∧ 𝖅 ∧ ∃ lam t : Fin N → ℝ, ∀ k,
      lam k ≠ 0 ∧ |lam k| < 1 ∧ Ɐ g (Φ.f k x).re = lam k * g x + t k := by
  have hε := Φ.ε_pos
  choose p hp hfp using fun k => (existsUnique_fixedPoint hε 𝖑).exists
  -- `Re ĝ_k` has derivative `Re ĝ_k' > 0`, and `(Re ĝ_k')' = Re Ĥ_{f_{k₀}} · Re ĝ_k'` on `I`
  have hK : ∀ k, Ɐ HasDerivAt (fun t : ℝ => (koenigs 𝔞 𝖒 t).re)
      (deriv 𝖏 x).re x ∧
      HasDerivAt (fun t : ℝ => (deriv 𝖏 t).re)
        ((hatH 𝖓 x).re * (deriv 𝖏 x).re) x ∧
      0 < (deriv 𝖏 x).re := fun k x hx => by
    have hx' := isOpen_nbhd.mem_nhds (ofReal_mem_nbhd hε hx)
    have hd := differentiableOn_koenigs hε 𝖑 𝖐
    have h := hasDerivAt_re_ofReal ((hd.deriv isOpen_nbhd).differentiableAt hx')
    rw [deriv_deriv_koenigs hε 𝖑 𝖐 (ofReal_mem_nbhd hε hx),
      Complex.mul_re, (deriv_koenigs_ofReal hε 𝖑 𝖐 hx).1, mul_zero,
      sub_zero, hH k x hx] at h
    exact ⟨hasDerivAt_re_ofReal (hd.differentiableAt hx'), h,
      (deriv_koenigs_ofReal hε 𝖑 𝖐 hx).2⟩
  have hc : ∀ k, ∃ l t, l ≠ 0 ∧ |l| < 1 ∧
      Ɐ (koenigs 𝖓 𝖔 (Φ.f k x).re).re =
        l * (koenigs 𝖓 𝖔 x).re + t := fun k => by
    -- `Re ĝ_{k₀}' / Re ĝ_k'` and then `Re ĝ_{k₀} - c Re ĝ_k` have zero derivative on `I`
    have hu := eq_of_hasDerivWithinAt_zero_I (fun x hx => by
      convert ((hK k₀ x hx).2.1.div (hK k x hx).2.1 (hK k x hx).2.2.ne').hasDerivWithinAt
        using 1
      ring) 𝖐
    simp only [Pi.div_apply] at hu
    set c := (deriv (koenigs 𝖓 𝖔) 𝖒).re / (deriv 𝖏 𝖒).re
    have hv := eq_of_hasDerivWithinAt_zero_I (fun x hx => by
      convert ((hK k₀ x hx).1.sub ((hK k x hx).1.const_mul c)).hasDerivWithinAt using 1
      rw [← hu x hx, div_mul_cancel₀ _ (hK k x hx).2.2.ne', sub_self]) 𝖐
    refine ⟨_, (koenigs 𝖓 𝖔 𝖒).re * (1 - (𝔡 Φ k 𝖒).re),
      (char_re_deriv_ne_zero_abs_lt_one hε 𝖑 𝖐).1,
      (char_re_deriv_ne_zero_abs_lt_one hε 𝖑 𝖐).2, fun x hx => ?_⟩
    have h1 := hv _ ((Φ.inClass k).re_mem_I x hx)
    have h2 := hv x hx
    simp [koenigs_self] at h1 h2
    linear_combination h1 + c * char_re_koenigs_conj hε 𝖑 𝖐 (hfp k) hx -
      (𝔡 Φ k 𝖒).re * h2
  choose lam t h using hc
  have hd : Ɐ deriv (fun t : ℝ => (koenigs 𝖓 𝖔 t).re) x ≠ 0 :=
    fun x hx => (hK k₀ x hx).1.deriv ▸ (hK k₀ x hx).2.2.ne'
  exact ⟨_, ⟨analyticOnNhd_re_ofReal hε (differentiableOn_koenigs hε (Φ.inClass k₀) (hp k₀)),
    (strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun x hx => (hK k₀ x hx).1.continuousAt.continuousWithinAt) fun x hx =>
        (hK k₀ x (interior_subset hx)).1.deriv ▸ (hK k₀ x (interior_subset hx)).2.2).injOn⟩,
    hd, lam, t, h⟩

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates `f_i` to a contracting similarity. Contraction of the other conjugated
maps is not asserted. -/
theorem theorem_1_12_similarity i :
    ∃ g, IsAnalyticCoord g ∧ 𝖅 ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ Ɐ g (Φ.f i x).re = lam * g x + t := by
  obtain ⟨g, hg, hd, lam, t, h⟩ := (koenigsIFS Φ.ε_pos (Φ.inClass i)).exists_conj_of_hatH_eq 0
    fun _ _ _ => rfl
  tauto

end IFS

end AnalyticESC
