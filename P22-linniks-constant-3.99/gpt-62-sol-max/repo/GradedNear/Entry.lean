module

public import GradedNear.ZeroForm
public import GradedNear.LaplaceDecay

/-!
# Entry bounds of the rows (paper §9.4)

The rows of §6.5 bound an entry's response through the zeros it keeps.

* **A kept zero at the entry's height.** This covers an ordinary character's representative
  `ρ_j`, the first family's `ρ₁`, the reserved second family's representative, the outside
  global zero and a hidden column. If `Im ρ = γ_j` and `λ_ρ ≤ hi`, the zero contributes at least
  `F(hi - s_j)`:
  * its multiplicity is at least one;
  * the argument `λ_ρ - s_j` of its term is real;
  * `F` is nonnegative and decreasing on the real line, since `f ≥ 0`.
* **A kept zero with `λ_ρ ≥ s_j`**, which lies at or left of the test point. It contributes at
  least its term `Re F(z) ≥ 0`, counted once. The `rc` pair's conjugate zero and the first
  family's second zero are of this kind.

`keptBound_single` and `keptBound_pair` are the resulting lower bounds for `keptBound`, the
numerator of an entry's feature in `graded_near_threshold`.
-/

@[expose] public section

open Complex

noncomputable section

namespace GradedNear

scoped notation "entryTerm " D:max E:max q:max j:max ρ:max =>
  zeroTerm (NearData.f D) q (entryAnchor D E j) (Entries.γ E j) ρ

/-- A zero of a non-principal `L(s, χ)` has multiplicity at least one. -/
lemma one_le_zmult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have hz := ((analyticOnNhd_LFunction hχ) ρ (Set.mem_univ ρ)).analyticOrderAt_ne_zero.mpr hρ
  rw [← Nat.cast_analyticOrderNatAt (order_LFunction_ne_top hχ ρ)] at hz
  unfold zmult
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hz)

/-- A zero at the entry's height has the real term `F(λ_ρ - σ)`, which is at least `F(hi - σ)`
for `λ_ρ ≤ hi`, and nonnegative. -/
private lemma entry_at_height_le {D : NearData} (hD : D.Valid) (hf2 : Condition2 D.f)
    {q : ℕ} {ι : Type*} (E : Entries q ι) (j : ι) {hi : ℝ} {ρ : ℂ}
    (hγ : ρ.im = E.γ j) (hhi : zeroOffset q ρ ≤ hi) :
    heightTerm D E j hi ≤ entryTerm D E q j ρ ∧ 0 ≤ entryTerm D E q j ρ := by
  let hf := hD.f_cond
  have hc x : IntervalIntegrable (fun t => D.f t * Real.exp (-(x * t))) MeasureTheory.volume 0 D.xf := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hf.pos.le]
    exact (hf.cont.mono Set.Icc_subset_Ici_self).mul (by fun_prop)
  simp only [zeroTerm, hγ, sub_self, zero_mul, ofReal_zero, add_zero,
    Decay.laplace_eq_intervalIntegral hf, laplace_integrand_real, intervalIntegral.integral_ofReal, ofReal_re]
  constructor
  · refine intervalIntegral.integral_mono_on hf.pos.le (hc _) (hc _) fun t ht => ?_
    have := hf2.nonneg t ht.1
    have := ht.1
    gcongr
  · exact intervalIntegral.integral_nonneg hf.pos.le fun t ht =>
      mul_nonneg (hf2.nonneg t ht.1) (Real.exp_pos _).le

variable {q : ℕ} {ι : Type*}

section KeptBounds

variable [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
  (E : Entries q ι) (Sz : ι → Finset ℂ)

include hD hf2

/-- **An entry keeping one zero at its height**, as for an ordinary character in the bin
`[lo, hi]`: `keptBound ≥ F(hi - s_j) - f(0)/6 - η`. -/
theorem keptBound_single (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : zeroOffset q ρ ≤ hi) :
    heightTerm D E j hi - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  obtain ⟨h, h0⟩ := entry_at_height_le hD hf2 E j hγ hhi
  nlinarith [one_le_zmult hχ hρ]

/-- **An entry keeping a zero at its height and a second zero at or left of the test point**,
as for the `rc` pair and the first family's second zero:
`keptBound ≥ F(hi - s_j) + Re F(z') - f(0)/6 - η`, where `Re F(z') ≥ 0` is the second zero's
term. -/
theorem keptBound_pair (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : zeroOffset q ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hleft : entryAnchor D E j ≤ zeroOffset q ρ') :
    heightTerm D E j hi +
        entryTerm D E q j ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  obtain ⟨h, h0⟩ := entry_at_height_le hD hf2 E j hγ hhi
  nlinarith [one_le_zmult hχ hρ, one_le_zmult hχ hρ', zeroTerm_nonneg hf2 (γ := E.γ j) hleft]

/-- **A kept multiple zero at the entry's height**, as for the first family's double zero
(`ρ' = ρ₁`, `y = 0`): with multiplicity at least `2`, the kept terms are at least `F(hi - s_j)`
plus the zero's own term. -/
theorem keptBound_double (η : ℝ) (j : ι) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : zeroOffset q ρ ≤ hi) :
    heightTerm D E j hi +
        entryTerm D E q j ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := entry_at_height_le hD hf2 E j hγ hhi
  nlinarith

/-- **An entry keeping a zero at its height and a second zero whose term may be negative**, as
for the shifted row's `rc` entry, whose conjugate zero `ρ̄₁` lies left of the anchor. Suppose the
second zero's term is at least `-C` and its multiplicity is at most the first's (for a real
character, conjugate zeros have equal multiplicity). Then the kept terms minus `f(0)/6` are at
least `F(hi - s_j) - C - f(0)/6`, unless that number is `≤ 0`, in which case the entry's feature
is `≤ 0` and it contributes nothing to (T). -/
theorem keptBound_pair_neg (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi C : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : zeroOffset q ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ entryTerm D E q j ρ') :
    heightTerm D E j hi - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      heightTerm D E j hi - C - D.f 0 / 6 ≤ 0 := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  obtain ⟨hA, hA0⟩ := entry_at_height_le hD hf2 E j hγ hhi
  have hm2 := one_le_zmult hχ hρ'
  have hf0 := hf2.nonneg 0 le_rfl
  by_cases hAB : 0 ≤ entryTerm D E q j ρ +
      entryTerm D E q j ρ'
  · left; nlinarith
  · right; linarith

end KeptBounds

/-- **A row whose entries each keep one zero at their own height** (paper §9.4: ordinary
characters, the first family, the reserved second family, the outside global zero and hidden
columns). Entry `j` sits at the height of a zero `ρ_j` of `L(s, χ_j)` in its disc with
`λ_{ρ_j} ≤ hi_j`. Every other disc zero with `λ_ρ < s_j` must be at normalized height distance
`≥ M`, and there are at most `K₀` of them. Then the entries satisfy the threshold form (T) with
the features `(F(hi_j - s_j) - f(0)/6 - η) / N`, which is the form the leaf builders compute. -/
theorem single_zero_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    SeparatedModuli[M, δ, q => NearFamily[D, q; ι, E =>
        ∀ (ρ : ι → ℂ) (hi : ι → ℝ),
          (∀ j, DirichletCharacter.LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            discGap (E.γ j) (ρ j) ≤ δ ∧ zeroOffset q (ρ j) ≤ hi j) →
          (∀ j, ∀ ρ' : ℂ, DirichletCharacter.LFunction (E.χ j) ρ' = 0 →
            discGap (E.γ j) ρ' ≤ δ → ρ' ≠ ρ j →
            zeroOffset q ρ' < entryAnchor D E j → M ≤ heightGap q (E.γ j) ρ') →
          (∀ j, (∑ᶠ ρ' ∈ {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
              discGap (E.γ j) ρ' ≤ δ ∧ ρ' ≠ ρ j ∧
              zeroOffset q ρ' < entryAnchor D E j}, zmult (E.χ j) ρ') ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < diagNumerator D E j) →
            ThresholdForm[j; (heightTerm D E j (hi j) - D.f 0 / 6 - η) / Real.sqrt ((1 + η) * D.IB * Dn),
              diagNumerator D E j / Dn; (D.d₁ + η) / Dn]]] := by
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ := graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj ρ hi hρ hsep hK Dn hDn hDj
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj (fun j => {ρ j})
    (fun j ρ' hρ' => (Finset.mem_singleton.mp hρ').symm ▸ ⟨(hρ j).1, (hρ j).2.2.1⟩)
    (by simpa only [Finset.mem_singleton] using hsep)
    (fun j => by simpa only [Finset.mem_singleton] using hK j) Dn hDn hDj
  refine ⟨τ, hτ0, hτd, le_trans ?_ hT⟩
  gcongr with j
  · exact div_nonneg (hDj j).le hDn.le
  · exact keptBound_single D hD hf2 E _ η j (hχ j) rfl (hρ j).1 (hρ j).2.1 (hρ j).2.2.2

/-- The conjugate entry `(χ̄, -γ)` keeping the conjugate zero `ρ̄` has the same term as
`(χ, γ)` keeping `ρ`, since `Re F(z̄) = Re F(z)` for real `f`. -/
lemma zeroTerm_conj (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) :
    zeroTerm f q σ (-γ) ((starRingEnd ℂ) ρ) = zeroTerm f q σ γ ρ := by
  unfold zeroTerm
  rw [← laplace_re_conj f]
  congr 2
  simp [-natCast_log]; push_cast; ring
end GradedNear
