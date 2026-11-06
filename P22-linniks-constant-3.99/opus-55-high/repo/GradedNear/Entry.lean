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

/-- A zero at the entry's height has the real term `F(λ_ρ - σ)`, which is at least `F(hi - σ)`
for `λ_ρ ≤ hi` (`F` decreases on the real line), and nonnegative. -/
lemma zeroTerm_at_height_le {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
    (hf2 : Condition2 f) {q : ℕ} {σ γ hi : ℝ} {ρ : ℂ} (hγ : ρ.im = γ)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace f ((hi - σ : ℝ) : ℂ)).re ≤ zeroTerm f q σ γ ρ ∧ 0 ≤ zeroTerm f q σ γ ρ := by
  have key : ∀ x : ℝ, (laplace f (x : ℂ)).re = ∫ t in (0 : ℝ)..x₀, f t * Real.exp (-(x * t)) :=
    fun x => by
      rw [Decay.laplace_eq_intervalIntegral hf, ← Complex.ofReal_re (∫ t in (0 : ℝ)..x₀, _),
        ← intervalIntegral.integral_ofReal]
      simp_all
  have hc : ∀ x : ℝ, IntervalIntegrable (fun t => f t * Real.exp (-(x * t))) MeasureTheory.volume
      0 x₀ := fun x => ((hf.cont.mono Set.Icc_subset_Ici_self).mul (by fun_prop)).intervalIntegrable_of_Icc hf.pos.le
  simp only [zeroTerm, hγ, sub_self, zero_mul, ofReal_zero, add_zero, key]
  exact ⟨intervalIntegral.integral_mono_on hf.pos.le (hc _) (hc _) fun t ht =>
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [ht.1])) (hf2.nonneg t ht.1),
    intervalIntegral.integral_nonneg hf.pos.le fun t ht =>
      mul_nonneg (hf2.nonneg t ht.1) (Real.exp_pos _).le⟩

/-- A zero of a non-principal `L(s, χ)` has multiplicity at least one. -/
lemma one_le_zmult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have htop := ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 2)
    (Set.mem_univ ρ) (by simp [analyticOrderAt_eq_zero.2 (.inr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num : 1 ≤ (2 : ℂ).re)))])
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (ENat.toNat_eq_zero.not.2
    (not_or.2 ⟨analyticOrderAt_ne_zero.2 ⟨ha ρ trivial, hρ⟩, htop⟩))

variable {q : ℕ} {ι : Type*}

/-- **An entry keeping one zero at its height**, as for an ordinary character in the bin
`[lo, hi]`: `keptBound ≥ F(hi - s_j) - f(0)/6 - η`. -/
theorem keptBound_single [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  rw [keptBound, hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith [one_le_zmult hχ hρ]

/-- **An entry keeping a zero at its height and a second zero at or left of the test point**,
as for the `rc` pair and the first family's second zero:
`keptBound ≥ F(hi - s_j) + Re F(z') - f(0)/6 - η`, where `Re F(z') ≥ 0` is the second zero's
term. -/
theorem keptBound_pair [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hleft : D.s - E.δ j ≤ (1 - ρ'.re) * Real.log q) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  rw [keptBound, hS, Finset.sum_pair hne]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  have h2 : 0 ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' := hf2.re_nonneg _ (by simpa [-Complex.natCast_log] using hleft)
  nlinarith [one_le_zmult hχ hρ, one_le_zmult hχ hρ']

/-- **A row whose entries each keep one zero at their own height** (paper §9.4: ordinary
characters, the first family, the reserved second family, the outside global zero and hidden
columns). Entry `j` sits at the height of a zero `ρ_j` of `L(s, χ_j)` in its disc with
`λ_{ρ_j} ≤ hi_j`. Every other disc zero with `λ_ρ < s_j` must be at normalized height distance
`≥ M`, and there are at most `K₀` of them. Then the entries satisfy the threshold form (T) with
the features `(F(hi_j - s_j) - f(0)/6 - η) / N`, which is the form the leaf builders compute. -/
theorem single_zero_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ (ρ : ι → ℂ) (hi : ι → ℝ),
          (∀ j, DirichletCharacter.LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ j‖ ≤ δ ∧ (1 - (ρ j).re) * Real.log q ≤ hi j) →
          (∀ j, ∀ ρ' : ℂ, DirichletCharacter.LFunction (E.χ j) ρ' = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ → ρ' ≠ ρ j →
            (1 - ρ'.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ'.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ' ∈ {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ ∧ ρ' ≠ ρ j ∧
              (1 - ρ'.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ') ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((D.d₁ + η) / Dn) ∧
              ∑ j, (max 0 (((laplace D.f ((hi j - (D.s - E.δ j) : ℝ) : ℂ)).re - D.f 0 / 6 - η) /
                  Real.sqrt ((1 + η) * D.IB * Dn) - τ)) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ := graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, fun q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj ρ hi hρ hsep hK Dn
    hDn hDj => ?_⟩
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj (fun j => {ρ j})
    (fun j ρ' hρ' => by grind)
    (fun j ρ' h1 h2 h3 => hsep j ρ' h1 h2 (by grind)) (fun j => by simp_all) Dn
    hDn hDj
  refine ⟨τ, hτ0, hτd, hT.trans' (Finset.sum_le_sum fun j _ => ?_)⟩
  have := div_pos (hDj j) hDn
  gcongr
  exact keptBound_single D hD hf2 E (fun j => {ρ j}) η j (hχ j) rfl (hρ j).1 (hρ j).2.1 (hρ j).2.2.2

/-- The conjugate entry `(χ̄, -γ)` keeping the conjugate zero `ρ̄` has the same term as
`(χ, γ)` keeping `ρ`, since `Re F(z̄) = Re F(z)` for real `f`. -/
lemma zeroTerm_conj (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) :
    zeroTerm f q σ (-γ) ((starRingEnd ℂ) ρ) = zeroTerm f q σ γ ρ := by
  rw [zeroTerm, zeroTerm, ← laplace_re_conj f]
  congr 2
  apply Complex.ext <;> simp [-Complex.natCast_log]
  ring

/-- **A kept multiple zero at the entry's height**, as for the first family's double zero
(`ρ' = ρ₁`, `y = 0`): with multiplicity at least `2`, the kept terms are at least `F(hi - s_j)`
plus the zero's own term. -/
theorem keptBound_double [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  rw [keptBound, hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith

/-- **An entry keeping a zero at its height and a second zero whose term may be negative**, as
for the shifted row's `rc` entry, whose conjugate zero `ρ̄₁` lies left of the anchor. Suppose the
second zero's term is at least `-C` and its multiplicity is at most the first's (for a real
character, conjugate zeros have equal multiplicity). Then the kept terms minus `f(0)/6` are at
least `F(hi - s_j) - C - f(0)/6`, unless that number is `≤ 0`, in which case the entry's feature
is `≤ 0` and it contributes nothing to (T). -/
theorem keptBound_pair_neg [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi C : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ') :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ 0 := by
  rw [keptBound, hS, Finset.sum_pair hne]
  obtain ⟨hA, hA0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  refine or_iff_not_imp_right.2 fun h => ?_
  nlinarith [hf2.nonneg 0 le_rfl, one_le_zmult hχ hρ']

end GradedNear
