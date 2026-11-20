module

public import Erdos408.OneSided.Moment.Edge.Adjoint

/-!
# The columns of the dirty raw edges by reversal

PD §4 "Dirty raw edges": reversal exchanges the stored groups `S` and the promoted groups `I`
(`mem:edge-factorial`), changes only bounded `V_i` factors, and retains both good-state tests
and the ban. So the weighted column of the piece `(S, I)` at an output `s'` is at most `2^K μ(s')`
times the row of the piece `(I, S)` at `s'`.

* `revChoice`: the reversed choice of an edge `s → s'`. Its source symmetrization is `σ'^{-1}`,
  its stored groups are the promoted groups, its target is the source position, its new labels
  are the unshared source primes `b_i` (promoted exactly on `S`), and its target symmetrization
  is `σ^{-1}`.
* `edgeValid_revChoice`, `chainEdgeOut_revChoice`: the reversed choice is admissible and leads
  back to `s`; it solves the reversed raw determinant equation.
* `measure_mul_rawAmp_le`: the adjoint calculation `μ(s) rawAmp(s, c) ≤ 2^K μ(s') rawAmp(s',
  c^rev)`.
* `sum_col_rawAmp_le`: the column bound.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

section Reversal

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The reversed edge choice: the source symmetrization `σ'^{-1}`, the promoted groups as
stored groups, the source position as target, the unshared source primes as new labels
(promoted exactly on the stored groups), and the target symmetrization `σ^{-1}`. -/
def revChoice (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    EdgeChoice x d Y d₀ u v r :=
  (fun i => (c.2.2.2.2 i).symm, univ.filter (fun i => (c.2.2.2.1 i).2 = true), s.1,
    fun i => (edgeSrc s c i (Fin.last _), decide (i ∈ c.2.1)), fun i => (c.1 i).symm)

/-- The source lists of the reversed choice: the target lists reordered by `σ'^{-1}`, which
are the source lists reordered by `σ` with the new label in the last slot. -/
theorem edgeSrc_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₂ : s'.2.1.1 = edgeTgt s c) (i : Fin K) (h : Fin (padCount x + 1)) :
    edgeSrc s' (revChoice s c) i h =
      if h = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h := by
  change s'.2.1.1 i ((c.2.2.2.2 i).symm h) = _
  rw [h₂, edgeTgt_symm]

/-- The target lists of the reversed choice are the source lists. -/
theorem edgeTgt_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₂ : s'.2.1.1 = edgeTgt s c) : edgeTgt s' (revChoice s c) = s.2.1.1 := by
  funext i h
  change (if (c.1 i).symm h = Fin.last _ then edgeSrc s c i (Fin.last _)
    else edgeSrc s' (revChoice s c) i ((c.1 i).symm h)) = _
  rw [edgeSrc_revChoice h₂]
  split_ifs with hh
  · change s.2.1.1 i (c.1 i (Fin.last _)) = _
    rw [← hh, Equiv.apply_symm_apply]
  · change s.2.1.1 i (c.1 i ((c.1 i).symm h)) = _
    rw [Equiv.apply_symm_apply]

/-- The reversed choice has the same pad product. -/
theorem edgePad_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₂ : s'.2.1.1 = edgeTgt s c) : edgePad s' (revChoice s c) = edgePad s c := by
  unfold edgePad
  simp only [edgeSrc_revChoice h₂, Fin.castSucc_ne_last, ↓reduceIte]

/-- The unshared source primes of the reversed choice are the new labels. -/
theorem prod_edgeSrc_revChoice {s s' : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (h₂ : s'.2.1.1 = edgeTgt s c) :
    ∏ i, edgeSrc s' (revChoice s c) i (Fin.last _) = ∏ i, (c.2.2.2.1 i).1 := by
  simp only [edgeSrc_revChoice h₂, ↓reduceIte]

/-- The reversed determinant is the negated determinant. -/
theorem edgeDet_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₁ : s'.1 = c.2.2.1) : edgeDet s' (revChoice s c) = -edgeDet s c := by
  unfold edgeDet
  change s'.1.1.1 * s.1.1.2 - s'.1.1.2 * s.1.1.1 = _
  rw [h₁]
  ring

/-- The particle promoted by the reversed choice is the particle stored by the edge. -/
theorem edgePromoted_revChoice (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) :
    edgePromoted (revChoice s c) i = edgeStored s c i := rfl

/-- The particle stored by the reversed choice is the particle promoted by the edge. -/
theorem edgeStored_revChoice {s s' : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c)
    (i : Fin K) : edgeStored s' (revChoice s c) i = edgePromoted c i := by
  unfold edgeStored edgePromoted
  rw [edgeSrc_revChoice h₂, ite_eq_left rfl, h₁]

/-- The memory after the reversed choice is the source memory: the reversed edge stores the
promoted particles back and promotes the stored particles. -/
theorem edgeMem_revChoice (hdisj : d.BandsDisjoint x)
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c) :
    edgeMem s' (revChoice s c) = s.2.2.1 := by
  classical
  funext xp
  have hP := card_promoted_le hdisj hc hv xp
  -- the reversed promotions are the stored groups, and the reversed stores the promotions
  have hQ : (univ.filter fun i => ((revChoice s c).2.2.2.1 i).2 ∧
      edgePromoted (revChoice s c) i = xp.1).card =
        (c.2.1.filter fun i => edgeStored s c i = xp.1).card := by
    congr 1
    ext i
    rw [mem_filter, mem_filter, edgePromoted_revChoice]
    simp only [mem_univ, true_and]
    change (decide (i ∈ c.2.1) = true ∧ _) ↔ _
    rw [decide_eq_true_iff]
  have hP' : ((revChoice s c).2.1.filter fun i => edgeStored s' (revChoice s c) i = xp.1).card =
      (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card := by
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, edgeStored_revChoice h₁ h₂]
    change (i ∈ univ.filter (fun i => (c.2.2.2.1 i).2 = true) ∧ _) ↔ _
    rw [mem_filter]
    simp only [mem_univ, true_and]
  unfold edgeMem
  rw [hQ, hP', h₃]
  unfold edgeMem
  omega

/-- **The reversed choice is admissible**: its target lists are the source lists, the ban
holds since the source lists are distinct and the new labels avoid them, the pad product is
the same, both good-state tests swap, the stored particles are pending after the edge, and the
promoted particles are particles. -/
theorem edgeValid_revChoice
    (hdisj : d.BandsDisjoint x)
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c) :
    EdgeValid x d Y d₀ u v r B s' (revChoice s c) := by
  classical
  obtain ⟨-, hban, hD₁, hD₂, hdvd, hgood, hgood', hprom, hstore, -⟩ := id hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [edgeTgt_revChoice h₂]
    exact s.2.1.2
  · -- the ban: `b_i` is no target label
    intro i i' h
    change edgeSrc s c i (Fin.last _) ≠ s'.2.1.1 i' h
    rw [h₂]
    unfold edgeTgt
    dsimp only
    split_ifs with hh
    · exact (hban i' i _).symm
    · intro heq
      change s.2.1.1 i (c.1 i (Fin.last _)) = s.2.1.1 i' (c.1 i' (c.2.2.2.2 i' h)) at heq
      have hii : i = i' := by
        by_contra hii
        exact disjoint_left.1 (hdisj i i' hii) (mem_band_of_mem_lists s.2.1.2 i _)
          (heq ▸ mem_band_of_mem_lists s.2.1.2 i' _)
      subst hii
      exact hh ((c.1 i).injective (injective_of_mem_lists s.2.1.2 i heq)).symm
  · rw [edgePad_revChoice h₂]
    exact hD₁
  · rw [edgePad_revChoice h₂]
    exact hD₂
  · rw [edgePad_revChoice h₂, edgeDet_revChoice h₁]
    exact dvd_neg.2 hdvd
  · rw [h₁, h₂]
    exact hgood'
  · rw [edgeTgt_revChoice h₂]
    exact hgood
  · -- the stored particles are pending after the edge
    intro i hi
    have hiS : i ∈ c.2.1 := by simpa [revChoice] using hi
    refine ⟨⟨edgeStored s c i, hstore i hiS⟩, rfl, ?_⟩
    rw [h₃]
    unfold edgeMem
    have : 1 ≤ (c.2.1.filter fun j =>
        edgeStored s c j = (⟨edgeStored s c i, hstore i hiS⟩ : Particle x d).1).card :=
      card_pos.2 ⟨i, mem_filter.2 ⟨hiS, rfl⟩⟩
    omega
  · -- the promoted particles are particles
    intro i hi
    obtain ⟨xp, hxp, -⟩ := hprom i ((mem_filter.1 hi).2)
    rw [edgeStored_revChoice h₁ h₂, ← hxp]
    exact xp.2
  · rw [edgeMem_revChoice hdisj hc hv h₁ h₂ h₃]
    exact s.2.2.2

/-- The reversed choice leads back to the source. -/
theorem chainEdgeOut_revChoice
    (hdisj : d.BandsDisjoint x)
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c) :
    chainEdgeOut x d Y d₀ u v r B s' (revChoice s c) = s := by
  rw [chainEdgeOut_of_valid (edgeValid_revChoice hdisj hc hv h₁ h₂ h₃)]
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · exact edgeTgt_revChoice h₂
  · exact edgeMem_revChoice hdisj hc hv h₁ h₂ h₃

/-- The reversed choice solves the reversed raw determinant equation. -/
theorem rawDet_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h : RawDet s c) :
    RawDet s' (revChoice s c) := by
  unfold RawDet at h ⊢
  rw [edgeDet_revChoice h₁, edgePad_revChoice h₂, prod_edgeSrc_revChoice h₂]
  change -edgeDet s c = (edgePad s c : ℤ) * (((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℤ) -
    ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ))
  linear_combination -h

/-- Reversal exchanges the stored and the promoted groups. -/
theorem revChoice_mem_rawChoices {s : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} {S I : Finset (Fin K)}
    (hc : c ∈ rawChoices x d Y d₀ u v r S I) :
    revChoice s c ∈ rawChoices x d Y d₀ u v r I S := by
  obtain ⟨-, hS, hI⟩ := mem_filter.1 hc
  refine mem_filter.2 ⟨?_, hI, ?_⟩
  · simp only [edgeChoices, mem_product, mem_univ, true_and, and_true]
    exact Fintype.mem_piFinset.2 fun i => mem_product.2
      ⟨mem_band_edgeSrc s c i _, mem_univ _⟩
  · ext i
    rw [mem_filter, ← hS]
    simp only [mem_univ, true_and]
    change decide (i ∈ c.2.1) = true ↔ _
    rw [decide_eq_true_iff]

/-! ### The adjoint calculation -/

/-- **The adjoint calculation** (PD `mem:edge-factorial`): for an admissible edge `s → s'`,
`μ(s) ∏_i w_i ≤ 2^K μ(s') ∏_i w_i^{rev}`, where the reversed weights are `S'(y_i)/V(b_i)` for a
stored particle `y_i` and `ν(b_i)` otherwise. Removing a promoted particle `x_i` from `S` trades
its weight `S(x_i)` for `ν(a_i)`, which cancels the target label and leaves `1/V(a_i) ≤ 2`;
storing `b_i` trades the source label `ν(b_i)` for the multiplicity `S'(y_i) ≤ S'(y_i)/V(b_i)`. -/
theorem measure_mul_rawWeight_le
    (hdisj : d.BandsDisjoint x)
    (hV : d.BandsBalanced x)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c) :
    (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
        rawWeight q N s c ≤
      2 ^ K * ((∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
        ∏ i, if i ∈ c.2.1 then
          (memAt x d (edgeMem s c) (edgeStored s c i) : ℝ) /
            primeMass x d (edgeSrc s c i (Fin.last _))
        else primeWeight q x d N (edgeSrc s c i (Fin.last _))) := by
  classical
  rw [edge_weight_transport hdisj hνpos hc hv]
  conv_rhs =>
    rw [mul_comm (2 ^ K), mul_assoc,
      ← show (∏ _ : Fin K, (2 : ℝ)) = 2 ^ K by simp, ← prod_mul_distrib]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (prod_nonneg fun _ _ => prod_nonneg fun _ _ => hν _)
      (memWeight_nonneg (fun _ => hν _) _))
  refine prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
  · unfold reverseLabelWeight
    exact mul_nonneg (by split_ifs <;> first | positivity | apply hν)
      (by split_ifs; exacts [inv_nonneg.2 (primeMass_nonneg _), zero_le_one])
  · unfold reverseLabelWeight
    have ha := (hV i).1
    have hb := hV i
    rw [← primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)] at ha
    rw [← primeMass_eq_of_mem_band hdisj (mem_band_edgeSrc s c i (Fin.last _))] at hb
    refine mul_le_mul ?_ ?_ ?_ ?_
    · split_ifs
      · rw [le_div_iff₀ (by linarith [hb.1])]
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) hb.2
      · rfl
    · split_ifs
      · exact promotionFactor_le_two ha
      · norm_num
    · split_ifs; exacts [inv_nonneg.2 (primeMass_nonneg _), zero_le_one]
    · split_ifs
      · exact div_nonneg (Nat.cast_nonneg _) (primeMass_nonneg _)
      · exact hν _

end Reversal

/-! ### The column bound -/

section Column

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The output of an admissible edge choice. -/
private theorem out_eq {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : EdgeValid x d Y d₀ u v r B s c) (hs' : chainEdgeOut x d Y d₀ u v r B s c = s') :
    s'.1 = c.2.2.1 ∧ s'.2.1.1 = edgeTgt s c ∧ s'.2.2.1 = edgeMem s c := by
  rw [← hs', chainEdgeOut_of_valid hv]
  exact ⟨rfl, rfl, rfl⟩

/-- The weight product of the reversed choice. -/
theorem rawWeight_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₃ : s'.2.2.1 = edgeMem s c) :
    rawWeight q N s' (revChoice s c) = ∏ i, if i ∈ c.2.1 then
      (memAt x d (edgeMem s c) (edgeStored s c i) : ℝ) /
        primeMass x d (edgeSrc s c i (Fin.last _))
    else primeWeight q x d N (edgeSrc s c i (Fin.last _)) := by
  unfold rawWeight
  refine prod_congr rfl fun i _ => ?_
  change (if decide (i ∈ c.2.1) = true then _ else _) = _
  rw [edgePromoted_revChoice, sum_ite_eq_memAt, h₃]
  simp only [decide_eq_true_eq]
  rfl

/-- **The adjoint calculation for the raw coefficients**: for an admissible raw edge `s → s'`,
`μ(s) rawAmp(s, c) ≤ 2^K μ(s') rawAmp(s', c^rev)`. The pending factors swap, and
`measure_mul_rawWeight_le` compares the rest. -/
theorem measure_mul_rawAmp_le (hdisj : d.BandsDisjoint x)
    (hV : d.BandsBalanced x)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p) (hq : 0 < q)
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (h : EdgeValid x d Y d₀ u v r B s c ∧ RawDet s c)
    (hs' : chainEdgeOut x d Y d₀ u v r B s c = s') :
    chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c ≤
      2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' * rawAmp q N s' (revChoice s c)) := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := out_eq h.1 hs'
  have hv' := edgeValid_revChoice hdisj hc h.1 h₁ h₂ h₃
  have hdet' := rawDet_revChoice h₁ h₂ h.2
  have hmem := edgeMem_revChoice hdisj hc h.1 h₁ h₂ h₃
  have hadj := measure_mul_rawWeight_le hdisj hV hν hνpos hc h.1
  rw [← rawWeight_revChoice (q := q) (N := N) h₃] at hadj
  unfold rawAmp chainMeasure
  rw [ite_eq_left h, ite_eq_left ⟨hv', hdet'⟩, hmem, h₁, h₂, h₃]
  change _ ≤ _ * ((∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
    memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
      ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
        pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 * rawWeight q N s' (revChoice s c)))
  have hρ0 := (pendingWeight_pos hq).le
  have hk : 0 ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
      pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 := by positivity
  calc (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
        ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * rawWeight q N s c)
      = ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1) *
          ((∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
            memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
            rawWeight q N s c) := by ring
    _ ≤ ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1) *
          (2 ^ K * ((∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
            memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
            rawWeight q N s' (revChoice s c))) := mul_le_mul_of_nonneg_left hadj hk
    _ = _ := by ring

/-- An admissible raw edge of the piece `(S, I)` reaching `s'` is recovered from `s'` and its
reversed choice. -/
theorem eq_of_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    {S I : Finset (Fin K)} (hc : c ∈ rawChoices x d Y d₀ u v r S I)
    (hv : EdgeValid x d Y d₀ u v r B s c) (hs' : chainEdgeOut x d Y d₀ u v r B s c = s') :
    c = (fun i => ((revChoice s c).2.2.2.2 i).symm, S, s'.1,
      fun i => (s'.2.1.1 i ((revChoice s c).1 i (Fin.last _)), decide (i ∈ I)),
      fun i => ((revChoice s c).1 i).symm) := by
  obtain ⟨h₁, h₂, -⟩ := out_eq hv hs'
  obtain ⟨-, hS, hI⟩ := mem_filter.1 hc
  refine Prod.ext (funext fun i => ?_) (Prod.ext hS (Prod.ext h₁.symm
    (Prod.ext (funext fun i => ?_) (funext fun i => ?_))))
  · exact (Equiv.symm_symm _).symm
  · change c.2.2.2.1 i = (s'.2.1.1 i ((c.2.2.2.2 i).symm (Fin.last _)), decide (i ∈ I))
    rw [h₂, edgeTgt_symm, ite_eq_left rfl]
    refine Prod.ext rfl ?_
    change (c.2.2.2.1 i).2 = decide (i ∈ I)
    rw [← hI]
    cases hf : (c.2.2.2.1 i).2 <;> simp [hf]
  · exact (Equiv.symm_symm _).symm

open scoped Classical in
/-- **The column bound by reversal** (PD §4, dirty raw edges): the measure-weighted raw
coefficients of the piece `(S, I)` reaching `s'` sum to at most `2^K μ(s')` times the row of
the piece `(I, S)` at `s'`. Each admissible raw edge reaching `s'` is determined by its
reversed choice, which lies in the piece `(I, S)` (`eq_of_revChoice`). -/
theorem sum_col_rawAmp_le (hq : 0 < q)
    (hdisj : d.BandsDisjoint x)
    (hV : d.BandsBalanced x)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (S I : Finset (Fin K))
    (s' : ChainState x d Y d₀ u v r B) :
    ∑ s, ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter
        (fun c => chainEdgeOut x d Y d₀ u v r B s c = s'),
      chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c ≤
      2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
        ∑ c' ∈ rawChoices x d Y d₀ u v r I S, rawAmp q N s' c') := by
  classical
  have hV' : d.BandsLower x := fun i => (hV i).1
  have hν := primeWeight_nonneg_of hV' hb (q := q) (N := N)
  have hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p := fun i p hp =>
    (primeWeight_le_two hV' hb hp).1
  have hμ0 : ∀ t : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N t :=
    fun t => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  set X := ((univ : Finset (ChainState x d Y d₀ u v r B)) ×ˢ
    rawChoices x d Y d₀ u v r S I).filter fun p =>
      chainEdgeOut x d Y d₀ u v r B p.1 p.2 = s' ∧ EdgeValid x d Y d₀ u v r B p.1 p.2 ∧
        RawDet p.1 p.2 with hX
  have hrc : ∀ p ∈ X, p.2 ∈ rawChoices x d Y d₀ u v r S I := fun p hp =>
    (mem_product.1 (mem_filter.1 hp).1).2
  -- only the admissible raw edges contribute
  have hLHS : ∑ s, ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter
      (fun c => chainEdgeOut x d Y d₀ u v r B s c = s'),
        chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c =
      ∑ p ∈ X, chainMeasure q x d Y d₀ u v r B N p.1 * rawAmp q N p.1 p.2 := by
    rw [hX, sum_filter, sum_product]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_filter]
    refine sum_congr rfl fun c _ => ?_
    by_cases hout : chainEdgeOut x d Y d₀ u v r B t c = s'
    · by_cases hvd : EdgeValid x d Y d₀ u v r B t c ∧ RawDet t c
      · rw [ite_eq_left hout, ite_eq_left ⟨hout, hvd⟩]
      · rw [ite_eq_left hout, ite_eq_right fun h => hvd h.2]
        unfold rawAmp
        rw [ite_eq_right hvd, mul_zero]
    · rw [ite_eq_right hout, ite_eq_right fun h => hout h.1]
  -- the reversal is injective on the admissible raw edges reaching `s'`
  have hinj : Set.InjOn (fun p : ChainState x d Y d₀ u v r B × EdgeChoice x d Y d₀ u v r =>
      revChoice p.1 p.2) X := by
    intro p hp p' hp' heq
    obtain ⟨hout, hv, -⟩ := (mem_filter.1 hp).2
    obtain ⟨hout', hv', -⟩ := (mem_filter.1 hp').2
    have hc := (mem_filter.1 (hrc p hp)).1
    have hc' := (mem_filter.1 (hrc p' hp')).1
    simp only at heq
    obtain ⟨h₁, h₂, h₃⟩ := out_eq hv hout
    obtain ⟨h₁', h₂', h₃'⟩ := out_eq hv' hout'
    have hs : p.1 = p'.1 := by
      rw [← chainEdgeOut_revChoice hdisj hc hv h₁ h₂ h₃,
        ← chainEdgeOut_revChoice hdisj hc' hv' h₁' h₂' h₃', heq]
    refine Prod.ext hs ?_
    rw [eq_of_revChoice (hrc p hp) hv hout, eq_of_revChoice (hrc p' hp') hv' hout', heq]
  rw [hLHS]
  calc ∑ p ∈ X, chainMeasure q x d Y d₀ u v r B N p.1 * rawAmp q N p.1 p.2
      ≤ ∑ p ∈ X, 2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
          rawAmp q N s' (revChoice p.1 p.2)) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨hout, hvd⟩ := (mem_filter.1 hp).2
        exact measure_mul_rawAmp_le hdisj hV hν hνpos hq (mem_filter.1 (hrc p hp)).1 hvd hout
    _ ≤ ∑ c' ∈ rawChoices x d Y d₀ u v r I S,
          2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' * rawAmp q N s' c') := by
        refine sum_le_sum_of_injOn (fun p => revChoice p.1 p.2) hinj (fun c' hc' => ?_)
          (fun p _ => le_rfl) fun c' hc' _ => ?_
        · obtain ⟨p, hp, rfl⟩ := mem_image.1 hc'
          exact revChoice_mem_rawChoices (hrc p hp)
        · exact mul_nonneg (by positivity) (mul_nonneg (hμ0 s')
            (rawAmp_nonneg hq hdisj hV' hν s' (mem_filter.1 hc').1))
    _ = 2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
          ∑ c' ∈ rawChoices x d Y d₀ u v r I S, rawAmp q N s' c') := by
        rw [← mul_sum, ← mul_sum]

end Column

end Erdos408.OneSided
