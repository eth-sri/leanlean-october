module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.OneSided.Decomposition.Lists

public import Erdos408.OneSided.Model

/-!
# The edge operator is Hermitian

For a position model with an antisymmetric determinant and disjoint bands, the row operation
at any damping exponent is Hermitian (`blueprint/one_sided_type_ii.md` §12, S1). Reversing an
edge keeps the pads, keeps the cross-edge ban (by injectivity of the lists and disjointness
of the bands), negates `t`, swaps the last-slot products, and conjugates the arc integral.
The symmetrization and the good-state projection are real and symmetric, so `𝒜` is Hermitian.
The damping factors out of the row operation at both ends (`rowOp_eq_damp`).
-/

@[expose] public section

section

namespace Erdos408.OneSided

open Finset Real
open scoped Matrix ComplexConjugate

variable {K : ℕ}

/-- Negating the frequency conjugates the arc integral. -/
theorem arcIntegral_neg  A₀ x Y   n  :
    arcIntegral A₀ x Y (-n) = conj (arcIntegral A₀ x Y n) := by
  simp only [arcIntegral, map_sum, ← intervalIntegral.intervalIntegral_conj]
  refine sum_congr rfl fun k _ => sum_congr rfl fun h _ =>
    intervalIntegral.integral_congr fun θ _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

section
variable (M : PosModel) {x : ℝ} {d : Data K} {J : ℕ} (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {p : Lists K J} (hp : p ∈ lists x d J) (i : Fin K) {p' : Lists K J}


include hp in
/-- The labels of a list are in their bands. -/
theorem mem_band_of_mem_lists        
         h  : p i h ∈ band x (d.a i) := by solve_by_elim [_root_.Erdos408.OneSided.lists_slot_mem_band]

include hp in
/-- The groups of a list are injective. -/
theorem injective_of_mem_lists        
        : Function.Injective (p i) := by solve_by_elim [_root_.Erdos408.OneSided.lists_group_injective]

/-- The lists of a state. -/
theorem PosModel.mem_lists       (s : M.State x d) :
    s.1.2 ∈ lists x d (padCount x) := by
  classical
  exact (mem_product.1 (mem_filter.1 s.2).1).2

include hdisj in
/-- With copied pads and disjoint bands, the cross-edge ban only concerns the last slots. -/
theorem ban_iff_last      
       
    (hp' : p' ∈ lists x d J) (hpad : ∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) :
    (∀ i i' h', p' i (Fin.last _) ≠ p i' h') ↔
      ∀ i i', p' i (Fin.last _) ≠ p i' (Fin.last _) := by
  refine ⟨fun h i i' => h i i' _, fun h i i' h' => ?_⟩
  induction h' using Fin.lastCases with
  | last => exact h i i'
  | cast k =>
    rw [← hpad]
    by_cases hii : i = i'
    · subst hii
      exact fun he => (Fin.castSucc_lt_last k).ne' (injective_of_mem_lists hp' i he)
    · exact fun he => Finset.disjoint_left.1 (hdisj i i' hii) (mem_band_of_mem_lists hp' i _)
        (he ▸ mem_band_of_mem_lists hp' i' _)

end

namespace PosModel

variable (M : PosModel) {x : ℝ} {d : Data K}

/-- With an antisymmetric determinant and disjoint bands, the row operation is Hermitian. -/
theorem star_rowOp (hdet : ∀ P Q, M.det Q P = -M.det P Q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))  q A₀ Y d₀ 
     s s'  : star (M.rowOp q A₀ x d Y d₀ s' s) = M.rowOp q A₀ x d Y d₀ s s' := by
  classical
  by_cases hpad : ∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc
  · -- step: the reversed edge passes the same restrictions
    have hD : padProd s'.1.2 = padProd s.1.2 := by
      simp only [padProd, hpad]
    have hban := ban_iff_last hdisj (M.mem_lists s') hpad
    have hban' := ban_iff_last hdisj (M.mem_lists s) fun i h => (hpad i h).symm
    have hiff : ((∀ i (h : Fin (padCount x)), s.1.2 i h.castSucc = s'.1.2 i h.castSucc) ∧
        (∀ i i' h', s.1.2 i (Fin.last _) ≠ s'.1.2 i' h') ∧
        d₀ ≤ (padProd s'.1.2 : ℝ) ∧ (padProd s'.1.2 : ℝ) < 2 * d₀ ∧
        (padProd s'.1.2 : ℤ) ∣ M.det s'.1.1 s.1.1) ↔
        ((∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc) ∧
        (∀ i i' h', s'.1.2 i (Fin.last _) ≠ s.1.2 i' h') ∧
        d₀ ≤ (padProd s.1.2 : ℝ) ∧ (padProd s.1.2 : ℝ) < 2 * d₀ ∧
        (padProd s.1.2 : ℤ) ∣ M.det s.1.1 s'.1.1) := by
      rw [hban, hban', hD, hdet, dvd_neg]
      exact ⟨fun h => ⟨hpad, fun i i' he => h.2.1 i' i he.symm, h.2.2⟩,
        fun h => ⟨fun i k => (hpad i k).symm, fun i i' he => h.2.1 i' i he.symm, h.2.2⟩⟩
    by_cases hC : (∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc) ∧
        (∀ i i' h', s'.1.2 i (Fin.last _) ≠ s.1.2 i' h') ∧
        d₀ ≤ (padProd s.1.2 : ℝ) ∧ (padProd s.1.2 : ℝ) < 2 * d₀ ∧
        (padProd s.1.2 : ℤ) ∣ M.det s.1.1 s'.1.1
    · -- step: reversing negates `t`, swaps `a` and `b`, and conjugates the arc integral
      rw [rowOp, rowOp, ite_eq_left (hiff.2 hC), ite_eq_left hC, hD, hdet,
        Int.neg_ediv_of_dvd hC.2.2.2.2]
      set t := M.det s.1.1 s'.1.1 / padProd s.1.2
      have hind : (-t = (lastProd s'.1.2 : ℤ) - lastProd s.1.2) ↔
          (t = (lastProd s.1.2 : ℤ) - lastProd s'.1.2) := by omega
      have hψ : plateau (((-t : ℤ) : ℝ) / Y) = plateau ((t : ℝ) / Y) := by
        simp only [plateau, Int.cast_neg, neg_div, abs_neg]
      have harc : -t - lastProd s'.1.2 + lastProd s.1.2 =
          -(t - lastProd s.1.2 + lastProd s'.1.2) := by ring
      simp only [hind, hψ, harc, arcIntegral_neg, star_mul', Complex.star_def,
        Complex.conj_ofReal, map_sub, Complex.conj_conj, apply_ite (starRingEnd ℂ), map_one,
        map_zero]
      congr 2
      grind
    · rw [rowOp, rowOp, ite_eq_right (mt hiff.1 hC), ite_eq_right hC, star_zero]
  · -- step: the pads differ in both directions
    have hpad' : ¬∀ i (h : Fin (padCount x)), s.1.2 i h.castSucc = s'.1.2 i h.castSucc :=
      fun h => hpad fun i k => (h i k).symm
    grind [rowOp]

/-- The slot symmetrization is Hermitian. -/
theorem conjTranspose_symOp : (M.symOp x d)ᴴ = M.symOp x d := by
  classical
  ext s s'
  rw [Matrix.conjTranspose_apply, symOp, symOp]
  -- step: invert the permutations
  have hperm : ∀ s s' : M.State x d, (∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)),
      ∀ i, s.1.2 i = s'.1.2 i ∘ σ i) →
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i :=
    fun s s' ⟨σ, hσ⟩ => ⟨fun i => (σ i)⁻¹, fun i => funext fun h => by
      simp [hσ]⟩
  have hiff : (s'.1.1 = s.1.1 ∧ ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)),
      ∀ i, s.1.2 i = s'.1.2 i ∘ σ i) ↔ (s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i) :=
    ⟨fun h => ⟨h.1.symm, hperm s s' h.2⟩, fun h => ⟨h.1.symm, hperm s' s h.2⟩⟩
  rw [if_congr hiff rfl rfl]
  split_ifs <;> simp

section
variable (hdet : ∀ P Q, M.det Q P = -M.det P Q) (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (q A₀ Y d₀ : ℝ)


/-- The good-state projection is Hermitian. -/
theorem conjTranspose_goodOp   : (M.goodOp x d Y d₀)ᴴ = M.goodOp x d Y d₀ := by
  simp_all [goodOp]

include hdet hdisj in
/-- With an antisymmetric determinant and disjoint bands, the row operation is Hermitian. -/
theorem conjTranspose_rowOp  
        :
    (M.rowOp q A₀ x d Y d₀)ᴴ = M.rowOp q A₀ x d Y d₀ := by
  ext s s'
  rw [Matrix.conjTranspose_apply, M.star_rowOp hdet hdisj]

include hdet hdisj in
/-- With an antisymmetric determinant and disjoint bands, `𝒜` is Hermitian. -/
theorem conjTranspose_edgeOp  
        :
    (M.edgeOp q A₀ x d Y d₀)ᴴ = M.edgeOp q A₀ x d Y d₀ := by
  simp only [edgeOp, Matrix.conjTranspose_mul, conjTranspose_goodOp, conjTranspose_symOp,
    M.conjTranspose_rowOp hdet hdisj, mul_assoc]

end

/-- The damping factors out of the row operation: `𝒯_q(s, s') = d(s) 𝒯_1(s, s') d(s')` with
`d(s) = q^{(ω(P) - KM)/2}`. -/
theorem rowOp_eq_damp  {q}  (hq : 0 < q)  A₀ Y d₀   s s'  :
    M.rowOp q A₀ x d Y d₀ s s' =
      ((q ^ (((M.bandCount x d s.1.1 : ℝ) - K * (padCount x + 1)) / 2) : ℝ) : ℂ) *
        M.rowOp 1 A₀ x d Y d₀ s s' *
        ((q ^ (((M.bandCount x d s'.1.1 : ℝ) - K * (padCount x + 1)) / 2) : ℝ) : ℂ) := by
  simp only [rowOp]
  split_ifs <;> (try rw [one_rpow, rpow_add hq]) <;> push_cast <;> ring

end PosModel

end Erdos408.OneSided
