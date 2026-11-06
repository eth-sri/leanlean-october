module
public import Mathlib.Tactic

public import OAI.NumberTheory.PrimeGaps.AdditiveSieve

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace Erdos821.P4Frame

noncomputable section

def frameCellMass {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (j : κ)  :=
  ∑ x, if cell x = j then w x else 0

def frameCellKernel {α κ γ } [Fintype α] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (ξ : ℝ) (D X : α)  :=
  if cell D = cell X ∧ ξ ≤ frameCellMass w cell (cell X) then
    (frameCellMass w cell (cell X) : ℂ)⁻¹ * ∑ c, star (χ c D) * χ c X
  else 0

def frameCellApply {α κ γ } [Fintype α] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (ξ : ℝ)
    (f : α → ℂ) (X : α)  :=
  ∑ D, (w D : ℂ) * frameCellKernel w cell χ ξ D X * f D

def weightedFrameNorm {α } [Fintype α] (w : α → ℝ) (f : α → ℂ)  :=
  Real.sqrt (∑ x, w x * ‖f x‖ ^ 2)

/-- §3 conditional frame estimate. Weights need not have total mass one.
There is no cell-count cost: distinct cells are orthogonal blocks.
Suggested route: weighted vectors sqrt(w x) χ(c,x) / sqrt(cell mass),
then OAI.LargePrimeGaps.norm_sum_smul_sq_le_gram and gram_large_sieve
(OAI.NumberTheory.PrimeGaps.AdditiveSieve, prebuilt). -/
def CellFrameTask  :=
  ∀ (α κ γ : Type) [Fintype α] [Fintype κ] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (ξ δ : ℝ),
    (∀ x, 0 ≤ w x) → (∀ c x, ‖χ c x‖ ≤ 1) → 0 < ξ → 0 ≤ δ →
    (∀ j : κ, ξ ≤ frameCellMass w cell j → ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ) →
    ∀ f : α → ℂ,
      weightedFrameNorm w (frameCellApply w cell χ ξ f) ≤
        (1 + (Fintype.card γ : ℝ) * δ / ξ) * weightedFrameNorm w f

end

noncomputable section

variable {α κ γ : Type*} [Fintype α] [Fintype κ] [Fintype γ] [DecidableEq κ]

/-- Cell coefficient: weighted inner product of `χ c` with `f` over cell `j`. -/
def cellCoeff (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (j : κ) (c : γ)  :=
  ∑ D, if cell D = j then (w D : ℂ) * star (χ c D) * f D else 0

omit [Fintype κ] in
lemma mass_nonneg (w : α → ℝ) (cell : α → κ) (hw : ∀ x, 0 ≤ w x) (j : κ) :
    0 ≤ frameCellMass w cell j := by
  unfold frameCellMass
  apply Finset.sum_nonneg
  intro x _
  by_cases h : cell x = j <;> simp [h, hw x]

omit [Fintype κ] in
/-- `Tf` vanishes on cells whose mass is below `ξ`. -/
lemma apply_eq_zero_of_lt (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ)
    (ξ : ℝ) (f : α → ℂ) (X : α)
    (h : ¬ ξ ≤ frameCellMass w cell (cell X)) :
    frameCellApply w cell χ ξ f X = 0 := by
  unfold frameCellApply frameCellKernel
  apply Finset.sum_eq_zero
  grind

omit [Fintype κ] in
/-- `Tf` formula on cells whose mass reaches `ξ`. -/
lemma apply_eq_formula_of_le (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ)
    (ξ : ℝ) (f : α → ℂ) (X : α)
    (h : ξ ≤ frameCellMass w cell (cell X)) :
    frameCellApply w cell χ ξ f X =
      (frameCellMass w cell (cell X) : ℂ)⁻¹ *
        ∑ c, cellCoeff w cell χ f (cell X) c * χ c X := by
  classical
  unfold frameCellApply frameCellKernel cellCoeff
  have hker : ∀ D : α,
      (if cell D = cell X ∧ ξ ≤ frameCellMass w cell (cell X) then
        (frameCellMass w cell (cell X) : ℂ)⁻¹ * ∑ c, star (χ c D) * χ c X
        else 0)
      = if cell D = cell X then
        (frameCellMass w cell (cell X) : ℂ)⁻¹ * ∑ c, star (χ c D) * χ c X
        else 0 := by
    simp_all
  simp_rw [hker]
  have hexpand : ∀ D : α,
      (w D : ℂ) *
        (if cell D = cell X then
          (frameCellMass w cell (cell X) : ℂ)⁻¹ * ∑ c, star (χ c D) * χ c X
          else 0) * f D
      = (frameCellMass w cell (cell X) : ℂ)⁻¹ *
        ∑ c, (if cell D = cell X then (w D : ℂ) * star (χ c D) * f D else 0) *
          χ c X := by
    intro D
    by_cases hD : cell D = cell X
    · simp only [hD, ite_true]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring
    · simp [hD]
  simp_rw [hexpand]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_mul]

/-- Weighted cell vector `√w(x) χ(c,x)` supported on cell `j`. -/
def cellVec (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (j : κ) (c : γ)  :=
  WithLp.toLp 2 (fun x => if cell x = j then ((Real.sqrt (w x) : ℝ) : ℂ) * χ c x else 0)

/-- Weighted signal vector `√w(x) f(x)` supported on cell `j`. -/
def cellU (w : α → ℝ) (cell : α → κ) (f : α → ℂ) (j : κ)  :=
  WithLp.toLp 2 (fun x => if cell x = j then ((Real.sqrt (w x) : ℝ) : ℂ) * f x else 0)

omit [Fintype α] in
lemma sqrt_mul_self_complex (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)  x  :
    ((Real.sqrt (w x) : ℝ) : ℂ) * ((Real.sqrt (w x) : ℝ) : ℂ) = (w x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw x)]


omit [Fintype κ] [Fintype γ] in
lemma inner_cellVec (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (j : κ) (c d : γ) :
    inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d) =
      ∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0 := by
  classical
  unfold cellVec
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : cell x = j
  · simp only [hx, ite_true]
    rw [RCLike.inner_apply']
    have hsq := sqrt_mul_self_complex w hw x
    
    have hconj : conj (((Real.sqrt (w x) : ℝ) : ℂ) * χ c x) =
        ((Real.sqrt (w x) : ℝ) : ℂ) * star (χ c x) := by
      rw [map_mul, Complex.conj_ofReal, starRingEnd_apply]
    grind
  · simp [hx]

omit [Fintype κ] [Fintype γ] in
lemma inner_cellU (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (j : κ) (c : γ) :
    inner ℂ (cellVec w cell χ j c) (cellU w cell f j) = cellCoeff w cell χ f j c := by
  classical
  unfold cellVec cellU cellCoeff
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : cell x = j
  · simp only [hx, ite_true]
    rw [RCLike.inner_apply']
    have hsq := sqrt_mul_self_complex w hw x
    
    have hconj : conj (((Real.sqrt (w x) : ℝ) : ℂ) * χ c x) =
        ((Real.sqrt (w x) : ℝ) : ℂ) * star (χ c x) := by
      rw [map_mul, Complex.conj_ofReal, starRingEnd_apply]
    grind
  · rw [ite_eq_right hx]
    simp only
    simp [hx]

omit [Fintype κ] in
lemma norm_cellU_sq (w : α → ℝ) (cell : α → κ) (f : α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (j : κ) :
    ‖cellU w cell f j‖ ^ 2 =
      ∑ x, if cell x = j then w x * ‖f x‖ ^ 2 else 0 := by
  classical
  have h : ‖cellU w cell f j‖ ^ 2 = ∑ x, ‖cellU w cell f j x‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : cell x = j
  · simp only [cellU, hx, ite_true, PiLp.toLp_apply]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (w x) := Real.sqrt_nonneg _
    have hnorm_sqrt : ‖(((Real.sqrt (w x) : ℝ) : ℂ))‖ = Real.sqrt (w x) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg]
    rw [norm_mul, hnorm_sqrt, mul_pow, Real.sq_sqrt (hw x)]
  · simp [cellU, hx, PiLp.toLp_apply]

omit [Fintype κ] [Fintype γ] in
lemma inner_diag_le (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hχ : ∀ c x, ‖χ c x‖ ≤ 1) (j : κ) (c : γ) :
    ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j c)‖ ≤
      frameCellMass w cell j := by
  classical
  rw [inner_cellVec w cell χ hw j c c]
  calc ‖∑ x, (if cell x = j then (w x : ℂ) * star (χ c x) * χ c x else 0)‖
      ≤ ∑ x, ‖(if cell x = j then (w x : ℂ) * star (χ c x) * χ c x else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x, (if cell x = j then w x else 0) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : cell x = j
        · simp only [hx, ite_true]
          have h1 : ‖(((w x : ℝ)) : ℂ)‖ = w x := by
            simp_all
          have hstar_norm : ‖star (χ c x)‖ = ‖χ c x‖ := by simp
          have hχ1 : ‖χ c x‖ ≤ 1 := hχ c x
          have hnn : 0 ≤ ‖χ c x‖ := norm_nonneg _
          have hprod : ‖χ c x‖ * ‖χ c x‖ ≤ 1 := by
            nlinarith
          calc ‖(w x : ℂ) * star (χ c x) * χ c x‖
              = ‖(((w x : ℝ)) : ℂ)‖ * ‖star (χ c x)‖ * ‖χ c x‖ := by
                simp
            _ = w x * (‖χ c x‖ * ‖χ c x‖) := by rw [h1, hstar_norm]; ring
            _ ≤ w x * 1 := mul_le_mul_of_nonneg_left hprod (hw x)
            _ = w x := mul_one _
        · simp [hx]
    _ = frameCellMass w cell j := rfl

omit [Fintype κ] in
lemma row_sum_le (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hχ : ∀ c x, ‖χ c x‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (j : κ)
    (hoff : ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ)
    (c : γ) :
    ∑ d ∈ (Finset.univ : Finset γ),
        ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ ≤
      frameCellMass w cell j + (Fintype.card γ : ℝ) * δ := by
  classical
  have hdiag : ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j c)‖ ≤
      frameCellMass w cell j :=
    inner_diag_le w cell χ hw hχ j c
  have hoff' : ∀ d ∈ Finset.univ.erase c,
      ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ ≤ δ := by
    intro d hd
    have hne : c ≠ d := by
      intro heq
      have hmem := Finset.mem_erase.mp hd
      exact hmem.1 heq.symm
    have hne' : c ≠ d := hne
    -- inner equals hypothesis sum
    rw [inner_cellVec w cell χ hw j c d]
    exact hoff c d hne'
  have hsplit : ∑ d ∈ (Finset.univ : Finset γ),
        ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ =
      ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j c)‖ +
        ∑ d ∈ Finset.univ.erase c,
          ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ := by
    norm_num
  rw [hsplit]
  have herase_le : ∑ d ∈ Finset.univ.erase c,
        ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ ≤
      ((Finset.univ.erase c).card : ℝ) * δ := by
    calc ∑ d ∈ Finset.univ.erase c,
            ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖
        ≤ ∑ _d ∈ Finset.univ.erase c, δ :=
          Finset.sum_le_sum hoff'
      _ = ((Finset.univ.erase c).card : ℝ) * δ := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hcard_le : ((Finset.univ.erase c).card : ℝ) ≤ (Fintype.card γ : ℝ) := by
    norm_num
  have herase_le2 : ((Finset.univ.erase c).card : ℝ) * δ ≤
      (Fintype.card γ : ℝ) * δ :=
    mul_le_mul_of_nonneg_right hcard_le hδ
  linarith [hdiag, herase_le, herase_le2]

/-- Synthesis vector `∑ c, a_c • v_c` for cell `j`. -/
def synthVec (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (j : κ)  :=
  ∑ c ∈ (Finset.univ : Finset γ),
    (cellCoeff w cell χ f j c) • cellVec w cell χ j c

omit [Fintype κ] in
lemma norm_synth_le (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hχ : ∀ c x, ‖χ c x‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (j : κ)
    (hoff : ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ) :
    ‖synthVec w cell χ f j‖ ^ 2 ≤
      (frameCellMass w cell j + (Fintype.card γ : ℝ) * δ) *
        ∑ c ∈ (Finset.univ : Finset γ), ‖cellCoeff w cell χ f j c‖ ^ 2 := by
  classical
  
  have hrows : ∀ c ∈ (Finset.univ : Finset γ),
      ∑ d ∈ (Finset.univ : Finset γ),
        ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ ≤
        frameCellMass w cell j + (Fintype.card γ : ℝ) * δ := by
    intro c _
    exact row_sum_le w cell χ hw hχ δ hδ j hoff c
  have hgram := OAI.LargePrimeGaps.norm_sum_smul_sq_le_gram
    (Finset.univ : Finset γ) (cellVec w cell χ j)
    (cellCoeff w cell χ f j)
  have hdef : (∑ i ∈ (Finset.univ : Finset γ),
      (cellCoeff w cell χ f j i) • cellVec w cell χ j i) =
      synthVec w cell χ f j := rfl
  rw [hdef] at hgram
  -- hgram : ‖synth‖^2 ≤ ∑_c ‖a_c‖^2 * row_c
  calc ‖synthVec w cell χ f j‖ ^ 2
      ≤ ∑ c ∈ (Finset.univ : Finset γ),
          ‖cellCoeff w cell χ f j c‖ ^ 2 *
            (∑ d ∈ (Finset.univ : Finset γ),
              ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖) := hgram
    _ ≤ ∑ c ∈ (Finset.univ : Finset γ),
          ‖cellCoeff w cell χ f j c‖ ^ 2 *
            (frameCellMass w cell j + (Fintype.card γ : ℝ) * δ) := by
        apply Finset.sum_le_sum
        intro c hc
        apply mul_le_mul_of_nonneg_left (hrows c hc) (sq_nonneg _)
    _ = (frameCellMass w cell j + (Fintype.card γ : ℝ) * δ) *
          ∑ c ∈ (Finset.univ : Finset γ), ‖cellCoeff w cell χ f j c‖ ^ 2 := by
        rw [← Finset.sum_mul, mul_comm]

omit [Fintype κ] in
lemma coeff_energy_le (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hχ : ∀ c x, ‖χ c x‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (j : κ)
    (hoff : ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ) :
    ∑ c ∈ (Finset.univ : Finset γ), ‖cellCoeff w cell χ f j c‖ ^ 2 ≤
      (frameCellMass w cell j + (Fintype.card γ : ℝ) * δ) *
        ‖cellU w cell f j‖ ^ 2 := by
  classical
  have hB : 0 ≤ frameCellMass w cell j + (Fintype.card γ : ℝ) * δ := by
    have hM := mass_nonneg w cell hw j
    have hcard : 0 ≤ (Fintype.card γ : ℝ) * δ := by
      apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact hδ
    linarith
  have hrows : ∀ c ∈ (Finset.univ : Finset γ),
      ∑ d ∈ (Finset.univ : Finset γ),
        ‖inner ℂ (cellVec w cell χ j c) (cellVec w cell χ j d)‖ ≤
        frameCellMass w cell j + (Fintype.card γ : ℝ) * δ := by
    intro c _
    exact row_sum_le w cell χ hw hχ δ hδ j hoff c
  have hlarge := OAI.LargePrimeGaps.gram_large_sieve
    (Finset.univ : Finset γ) (cellVec w cell χ j) hB hrows (cellU w cell f j)
  -- hlarge : ∑_c ‖inner (v c) u‖^2 ≤ B * ‖u‖^2
  have heq : ∀ c : γ, ‖inner ℂ (cellVec w cell χ j c) (cellU w cell f j)‖ ^ 2 =
      ‖cellCoeff w cell χ f j c‖ ^ 2 := by
    intro c
    rw [inner_cellU w cell χ f hw j c]
  simp_rw [heq] at hlarge
  exact hlarge

omit [Fintype κ] in
lemma synth_apply (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (j : κ) (X : α) :
    (synthVec w cell χ f j) X =
      if cell X = j then ((Real.sqrt (w X) : ℝ) : ℂ) *
        (∑ c, cellCoeff w cell χ f j c * χ c X) else 0 := by
  classical
  unfold synthVec cellVec
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : cell X = j
  · simp only [hx, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · simp [hx]

omit [Fintype κ] in
lemma norm_synth_sq (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (j : κ) :
    ‖synthVec w cell χ f j‖ ^ 2 =
      ∑ X, if cell X = j then
        w X * ‖∑ c, cellCoeff w cell χ f j c * χ c X‖ ^ 2 else 0 := by
  classical
  have h : ‖synthVec w cell χ f j‖ ^ 2 =
      ∑ X, ‖(synthVec w cell χ f j) X‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [h]
  apply Finset.sum_congr rfl
  intro X _
  rw [synth_apply w cell χ f j X]
  by_cases hx : cell X = j
  · simp only [hx, ite_true]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (w X) := Real.sqrt_nonneg _
    have hnorm_sqrt : ‖(((Real.sqrt (w X) : ℝ) : ℂ))‖ = Real.sqrt (w X) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg]
    rw [norm_mul, hnorm_sqrt, mul_pow, Real.sq_sqrt (hw X)]
  · simp [hx]

omit [Fintype κ] in
lemma per_cell_le (w : α → ℝ) (cell : α → κ) (χ : γ → α → ℂ) (f : α → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hχ : ∀ c x, ‖χ c x‖ ≤ 1)
    (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 ≤ δ)
    (hoff : ∀ j : κ, ξ ≤ frameCellMass w cell j → ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ)
    (j : κ) (hMj : ξ ≤ frameCellMass w cell j) :
    (∑ X, if cell X = j then
      w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2 else 0) ≤
      (1 + (Fintype.card γ : ℝ) * δ / ξ) ^ 2 *
        (∑ X, if cell X = j then w X * ‖f X‖ ^ 2 else 0) := by
  classical
  set M := frameCellMass w cell j with hMdef
  set B : ℝ := M + (Fintype.card γ : ℝ) * δ with hBdef
  set C : ℝ := 1 + (Fintype.card γ : ℝ) * δ / ξ with hCdef
  have hMpos : 0 < M := lt_of_lt_of_le hξ hMj
  
  have hcard_nonneg : 0 ≤ (Fintype.card γ : ℝ) * δ := by
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact hδ
  have hBnonneg : 0 ≤ B := by simp [hBdef]; linarith
  
  have hoff_j : ∀ c d : γ, c ≠ d →
      ‖∑ x, if cell x = j then (w x : ℂ) * star (χ c x) * χ d x else 0‖ ≤ δ :=
    hoff j hMj
  have hsynth : ‖synthVec w cell χ f j‖ ^ 2 ≤ B ^ 2 * ‖cellU w cell f j‖ ^ 2 := by
    have h1 := norm_synth_le w cell χ f hw hχ δ hδ j hoff_j
    have h2 := coeff_energy_le w cell χ f hw hχ δ hδ j hoff_j
    
    rw [← hBdef] at h1 h2
    -- h1 : ‖synth‖^2 ≤ B * ∑‖a‖^2, h2 : ∑‖a‖^2 ≤ B * ‖u‖^2
    calc ‖synthVec w cell χ f j‖ ^ 2
        ≤ B * (∑ c ∈ (Finset.univ : Finset γ), ‖cellCoeff w cell χ f j c‖ ^ 2) := h1
      _ ≤ B * (B * ‖cellU w cell f j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hBnonneg
      _ = B ^ 2 * ‖cellU w cell f j‖ ^ 2 := by ring
  have hu_eq : ‖cellU w cell f j‖ ^ 2 =
      ∑ X, if cell X = j then w X * ‖f X‖ ^ 2 else 0 :=
    norm_cellU_sq w cell f hw j
  have hsynth_eq : ‖synthVec w cell χ f j‖ ^ 2 =
      ∑ X, if cell X = j then
        w X * ‖∑ c, cellCoeff w cell χ f j c * χ c X‖ ^ 2 else 0 :=
    norm_synth_sq w cell χ f hw j
  -- Relate Tf energy to synth energy via M⁻²
  
  have hnorm_inv : ‖((M : ℝ) : ℂ)⁻¹‖ = M⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
  have hE_eq : (∑ X, if cell X = j then
      w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2 else 0) =
      (M ^ 2)⁻¹ * (∑ X, if cell X = j then
        w X * ‖∑ c, cellCoeff w cell χ f j c * χ c X‖ ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    by_cases hx : cell X = j
    · simp only [hx, ite_true]
      have hMX : frameCellMass w cell (cell X) = M := by
        simp [hMdef, hx]
      have hle : ξ ≤ frameCellMass w cell (cell X) := by
        rw [hMX]; exact hMj
      have hTf := apply_eq_formula_of_le w cell χ ξ f X hle
      have hcoeff : ∀ c : γ, cellCoeff w cell χ f (cell X) c =
          cellCoeff w cell χ f j c := by
        intro c
        simp [hx]
      rw [hTf]
      simp_rw [hcoeff]
      rw [hMX]
      -- ‖M⁻¹ * S‖^2 = M⁻² * ‖S‖^2
      have hS : ∀ S : ℂ, w X * ‖((M : ℝ) : ℂ)⁻¹ * S‖ ^ 2 =
          (M ^ 2)⁻¹ * (w X * ‖S‖ ^ 2) := by
        intro S
        rw [norm_mul, hnorm_inv, mul_pow, inv_pow]
        ring
      exact hS _
    · simp [hx]
  rw [hE_eq, ← hsynth_eq, ← hu_eq]
  -- Now goal: M⁻² * ‖synth‖^2 ≤ C^2 * E_j, with ‖synth‖^2 ≤ B^2 * E_j
  have hBM_le : B / M ≤ C := by
    simp only [hBdef, hCdef]
    
    
    have hdiv : (Fintype.card γ : ℝ) * δ / M ≤
        (Fintype.card γ : ℝ) * δ / ξ := by
      gcongr
    have hBM : (M + (Fintype.card γ : ℝ) * δ) / M =
        1 + (Fintype.card γ : ℝ) * δ / M := by
      field_simp
    rw [hBM]
    linarith [hdiv]
  have hBM_nonneg : 0 ≤ B / M := div_nonneg hBnonneg (le_of_lt hMpos)
  
  have hsq_le : (B / M) ^ 2 ≤ C ^ 2 :=
    pow_le_pow_left₀ hBM_nonneg hBM_le 2
  have hmain : (M ^ 2)⁻¹ * ‖synthVec w cell χ f j‖ ^ 2 ≤
      C ^ 2 * ‖cellU w cell f j‖ ^ 2 := by
    have h1 : (M ^ 2)⁻¹ * ‖synthVec w cell χ f j‖ ^ 2 ≤
        (M ^ 2)⁻¹ * (B ^ 2 * ‖cellU w cell f j‖ ^ 2) := mul_le_mul_of_nonneg_left hsynth (by positivity)
    have h2 : (M ^ 2)⁻¹ * (B ^ 2 * ‖cellU w cell f j‖ ^ 2) =
        (B / M) ^ 2 * ‖cellU w cell f j‖ ^ 2 := by
      rw [div_pow]
      field_simp
    rw [h2] at h1
    calc (M ^ 2)⁻¹ * ‖synthVec w cell χ f j‖ ^ 2
        ≤ (B / M) ^ 2 * ‖cellU w cell f j‖ ^ 2 := h1
      _ ≤ C ^ 2 * ‖cellU w cell f j‖ ^ 2 := mul_le_mul_of_nonneg_right hsq_le (sq_nonneg _)
  exact hmain

theorem CellFrameTask_proof : CellFrameTask := by
  classical
  intro α κ γ _ _ _ _ w cell χ ξ δ hw hχ hξ hδ hoff f
  unfold weightedFrameNorm
  set C : ℝ := 1 + (Fintype.card γ : ℝ) * δ / ξ with hCdef
  have hcard_nonneg : 0 ≤ (Fintype.card γ : ℝ) * δ := by
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact hδ
  have hCdiv_nonneg : 0 ≤ (Fintype.card γ : ℝ) * δ / ξ :=
    div_nonneg hcard_nonneg (le_of_lt hξ)
  have hC_nonneg : 0 ≤ C := by simp [hCdef]; linarith
  have hC_sq_nonneg : 0 ≤ C ^ 2 := sq_nonneg _
  -- Partition of total energies over cells
  have hpart : ∀ g : α → ℝ,
      (∑ j : κ, ∑ X : α, (if cell X = j then g X else 0)) = ∑ X, g X := by
    intro g
    rw [Finset.sum_comm]
    norm_num
  -- Actually `∑ j : κ, ...` is `∑ j ∈ univ, ...` definitionally; adjust
  have hE_part : (∑ j : κ, ∑ X : α, (if cell X = j then w X * ‖f X‖ ^ 2 else 0))
      = ∑ X, w X * ‖f X‖ ^ 2 := hpart _
  have hE'_part : (∑ j : κ, ∑ X : α,
      (if cell X = j then w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2 else 0))
      = ∑ X, w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2 := hpart _
  -- Per-cell bound
  have hcell : ∀ j : κ,
      (∑ X : α, (if cell X = j then
        w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2 else 0)) ≤
        C ^ 2 * (∑ X : α, (if cell X = j then w X * ‖f X‖ ^ 2 else 0)) := by
    intro j
    by_cases hMj : ξ ≤ frameCellMass w cell j
    · have hle := per_cell_le w cell χ f hw hχ ξ δ hξ hδ hoff j hMj
      simp only [hCdef] at hle ⊢
      exact hle
    · -- Vanishing block
      have hzero : (∑ X : α, (if cell X = j then
          w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro X _
        by_cases hx : cell X = j
        · simp only [hx, ite_true]
          have hMX : frameCellMass w cell (cell X) = frameCellMass w cell j := by
            simp [hx]
          have hlt : ¬ ξ ≤ frameCellMass w cell (cell X) := by
            rw [hMX]; exact hMj
          have hTf0 := apply_eq_zero_of_lt w cell χ ξ f X hlt
          simp [hTf0]
        · simp [hx]
      rw [hzero]
      apply mul_nonneg (sq_nonneg _)
      apply Finset.sum_nonneg
      intro X _
      bound
  have htotal : (∑ X, w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2) ≤
      C ^ 2 * (∑ X, w X * ‖f X‖ ^ 2) := by
    rw [← hE'_part, ← hE_part, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact hcell j
  -- Take square roots
  have hsqrt : Real.sqrt (∑ X, w X * ‖frameCellApply w cell χ ξ f X‖ ^ 2) ≤
      C * Real.sqrt (∑ X, w X * ‖f X‖ ^ 2) := by
    
    have hC2E : C * Real.sqrt (∑ X, w X * ‖f X‖ ^ 2) =
        Real.sqrt (C ^ 2 * (∑ X, w X * ‖f X‖ ^ 2)) := by
      rw [Real.sqrt_mul hC_sq_nonneg, Real.sqrt_sq hC_nonneg]
    rw [hC2E]
    exact Real.sqrt_le_sqrt htotal
  simpa [hCdef] using hsqrt

end

end Erdos821.P4Frame
