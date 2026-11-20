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

section
variable {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (hf2 : Condition2 f)
include hf hf2

open MeasureTheory Set in
/-- Nonnegativity of the kernel gives both positivity and antitonicity on the real axis. -/
lemma axis_bounds {x y : ℝ} (h : x ≤ y) :
    (laplace f (y : ℂ)).re ≤ (laplace f (x : ℂ)).re ∧ 0 ≤ (laplace f (x : ℂ)).re := by
  let k z t := f t * Real.exp (-z*t)
  have eq (z : ℝ) : (laplace f (z : ℂ)).re = ∫ t in Ioc (0:ℝ) x₀, k z t :=
    (laplace_real ..).trans (truncate_Ioi fun t ht => by simp [hf.vanish t ht])
  have hi z : IntegrableOn (k z) (Ioc 0 x₀) := ((hf.cont.mono Icc_subset_Ici_self).mul
    (by fun_prop)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [eq, eq]; refine ⟨setIntegral_mono_on (hi y) (hi x) measurableSet_Ioc fun t ht => ?_,
    setIntegral_nonneg measurableSet_Ioc fun t ht => mul_nonneg (hf2.nonneg t ht.1.le) (Real.exp_pos _).le⟩
  dsimp [k]; gcongr <;> first | exact hf2.nonneg _ ht.1.le | exact ht.1.le

/-- A zero at the entry's height has the real term `F(λ_ρ - σ)`, which is at least `F(hi - σ)`
for `λ_ρ ≤ hi`, and nonnegative. -/
lemma zeroTerm_at_height_le {q : ℕ} {σ γ hi : ℝ} {ρ : ℂ} (hγ : ρ.im = γ)
    (hhi : λρ[q] ρ ≤ hi) :
    (laplace f ((hi - σ : ℝ) : ℂ)).re ≤ zeroTerm f q σ γ ρ ∧ 0 ≤ zeroTerm f q σ γ ρ := by
  simp only [zeroTerm, hγ, sub_self, zero_mul, ofReal_zero, add_zero]
  exact axis_bounds hf hf2 (sub_le_sub_right hhi _)

/-- **A kept zero at the entry's height.** If `Im ρ = γ` and `λ_ρ = (1 - Re ρ)𝓛 ≤ hi`, the
zero's term, with multiplicity, is at least `F(hi - σ)`. -/
lemma zeroTerm_at_height {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ γ hi : ℝ} {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (hγ : ρ.im = γ)
    (hhi : λρ[q] ρ ≤ hi) :
    (laplace f ((hi - σ : ℝ) : ℂ)).re ≤ zmult χ ρ * zeroTerm f q σ γ ρ := by
  obtain ⟨hle, h0⟩ := zeroTerm_at_height_le hf hf2 (σ := σ) hγ hhi
  exact hle.trans (le_mul_of_one_le_left h0 (one_le_zmult hχ hρ))

end

/-- The conjugate entry `(χ̄, -γ)` keeping the conjugate zero `ρ̄` has the same term as
`(χ, γ)` keeping `ρ`, since `Re F(z̄) = Re F(z)` for real `f`. -/
lemma zeroTerm_conj (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) :
    zeroTerm f q σ (-γ) ((starRingEnd ℂ) ρ) = zeroTerm f q σ γ ρ := by
  apply laplace_reflect <;> simp <;> ring

section
variable {q : ℕ} {ι : Type*} [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι)
include hD hf2

local notation "sⱼ" => anchorOf D E j
local notation "Zⱼ" => zeroTerm D.f q sⱼ (E.γ j)
local notation "Fⱼ " hi:max => upperTerm D E j hi

/-- **An entry keeping one zero at its height**, as for an ordinary character in the bin
`[lo, hi]`: `keptBound ≥ F(hi - s_j) - f(0)/6 - η`. -/
theorem keptBound_single (hχ : E.χ j ≠ 1) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : λρ[q] ρ ≤ hi) :
    Fⱼ hi - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  rw [keptBound, hS, Finset.sum_singleton]
  linarith [zeroTerm_at_height hD.f_cond hf2 hχ (σ := sⱼ) hρ hγ hhi]

/-- **An entry keeping a zero at its height and a second zero at or left of the test point**,
as for the `rc` pair and the first family's second zero:
`keptBound ≥ F(hi - s_j) + Re F(z') - f(0)/6 - η`, where `Re F(z') ≥ 0` is the second zero's
term. -/
theorem keptBound_pair (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : λρ[q] ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hleft : sⱼ ≤ λρ[q] ρ') :
    Fⱼ hi +
        Zⱼ ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  rw [keptBound, hS, Finset.sum_pair hne]
  have h1 := zeroTerm_at_height hD.f_cond hf2 hχ (σ := sⱼ) hρ hγ hhi
  have h2 := le_mul_of_one_le_left (zeroTerm_nonneg hf2 (γ := E.γ j) hleft) (one_le_zmult hχ hρ')
  linarith

/-- **A kept multiple zero at the entry's height**, as for the first family's double zero
(`ρ' = ρ₁`, `y = 0`): with multiplicity at least `2`, the kept terms are at least `F(hi - s_j)`
plus the zero's own term. -/
theorem keptBound_double {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : λρ[q] ρ ≤ hi) :
    Fⱼ hi +
        Zⱼ ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  rw [keptBound, hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := sⱼ) hγ hhi
  nlinarith

/-- **An entry keeping a zero at its height and a second zero whose term may be negative**, as
for the shifted row's `rc` entry, whose conjugate zero `ρ̄₁` lies left of the anchor. Suppose the
second zero's term is at least `-C` and its multiplicity is at most the first's (for a real
character, conjugate zeros have equal multiplicity). Then the kept terms minus `f(0)/6` are at
least `F(hi - s_j) - C - f(0)/6`, unless that number is `≤ 0`, in which case the entry's feature
is `≤ 0` and it contributes nothing to (T). -/
theorem keptBound_pair_neg (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi C : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : λρ[q] ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ Zⱼ ρ') :
    Fⱼ hi - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      Fⱼ hi - C - D.f 0 / 6 ≤ 0 := by
  rw [keptBound, hS, Finset.sum_pair hne]
  obtain ⟨hA, hA0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := sⱼ) hγ hhi
  have hf0 := hf2.nonneg 0 le_rfl
  by_cases hAB : 0 ≤ Zⱼ ρ +
      Zⱼ ρ'
  · left
    nlinarith [mul_le_mul_of_nonneg_right hm hA0, mul_le_mul_of_nonneg_left (one_le_zmult hχ hρ') hAB]
  · right
    linarith

end

section
variable {q : ℕ} [NeZero q] {ι : Type*}
open scoped ComplexConjugate

/-- **`keptBound_pair_neg` for the conjugate pair of a real character**: the entry keeps a zero
`ρ` at its height and the conjugate zero `ρ̄`. For a real character, conjugate zeros have equal
multiplicity (`zmult_conj`), so the multiplicity hypothesis of `keptBound_pair_neg` is automatic.
All other hypotheses are those of `keptBound_pair_neg` with `ρ' = ρ̄`. -/
theorem keptBound_pair_neg_real (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1)
    (hreal : ∀ a : ZMod q, conj (E.χ j a) = E.χ j a) {ρ : ℂ} {hi C : ℝ}
    (hne : ρ ≠ conj ρ) (hS : Sz j = {ρ, conj ρ}) (hγ : ρ.im = E.γ j)
    (hhi : λρ[q] ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) (conj ρ) = 0)
    (hC : -C ≤ zeroTerm D.f q (anchorOf D E j) (E.γ j) (conj ρ)) :
    upperTerm D E j hi - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      upperTerm D E j hi - C - D.f 0 / 6 ≤ 0 :=
  keptBound_pair_neg D hD hf2 E Sz j hχ hne hS hγ hhi hρ' (zmult_conj hχ hreal ρ).le hC


end

/-- **A row whose entries each keep one zero at their own height** (paper §9.4: ordinary
characters, the first family, the reserved second family, the outside global zero and hidden
columns). Entry `j` sits at the height of a zero `ρ_j` of `L(s, χ_j)` in its disc with
`λ_{ρ_j} ≤ hi_j`. Every other disc zero with `λ_ρ < s_j` must be at normalized height distance
`≥ M`, and there are at most `K₀` of them. Then the entries satisfy the threshold form (T) with
the features `(F(hi_j - s_j) - f(0)/6 - η) / N`, which is the form the leaf builders compute. -/
theorem single_zero_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    ExistsDiscControls M δ,
      ForLargeEntries q ι E of D,
        ∀ (ρ : ι → ℂ) (hi : ι → ℝ),
          (∀ j, DirichletCharacter.LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            inDisc[E.γ j, δ] (ρ j) ∧ λρ[q] (ρ j) ≤ hi j) →
          (∀ j, adverseFar q (E.χ j) (E.γ j) (anchorOf D E j) δ M where z ↦ (z ≠ ρ j)) →
          (∀ j, adverseCount q (E.χ j) (E.γ j) (anchorOf D E j) δ where z ↦ (z ≠ ρ j) ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < rowDiag D E j) →
            HasThreshold[(D.d₁ + η)/Dn] j ↦
              ((upperTerm D E j (hi j) - D.f 0 / 6 - η) /
                Real.sqrt ((1+η)*D.IB*Dn), (rowDiag D E j)/Dn) := by
  gconvert graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη
  intro ρ hi hρ hsep hK Dn hDn hDj
  have hT := this (fun j => {ρ j})
    (by simpa only [Finset.mem_singleton, forall_eq] using fun j => And.intro (hρ j).1 (hρ j).2.2.1)
    (by simpa only [Finset.mem_singleton] using hsep) (by simpa only [Finset.mem_singleton] using hK) Dn hDn hDj
  obtain ⟨τ, hτ, hτd, h⟩ := hT
  refine ⟨τ, hτ, hτd, le_trans ?_ h⟩
  gcongr with j <;> try positivity [hDj j]
  exact keptBound_single D hD hf2 E (fun j => {ρ j}) η j (‹∀ i, E.χ i ≠ 1› j) rfl (hρ j).1 (hρ j).2.1 (hρ j).2.2.2

end GradedNear
