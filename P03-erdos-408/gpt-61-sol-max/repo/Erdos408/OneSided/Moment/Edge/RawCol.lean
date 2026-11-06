module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.OneSided.Moment.Phased.Edge

public import Erdos408.OneSided.Moment.Edge.RawRow

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
def revChoice (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)  :=
  (fun i => (c.2.2.2.2 i).symm, univ.filter (fun i => (c.2.2.2.1 i).2 = true), s.1,
    fun i => (edgeSrc s c i (Fin.last _), decide (i ∈ c.2.1)), fun i => (c.1 i).symm)

section
variable {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r} (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (i : Fin K)


/-- The output of an admissible edge choice. -/
private alias chainEdgeOut_of_valid' := _root_.Erdos408.OneSided.chainEdgeOut_of_valid

/-- The target lists after undoing `σ'`: the new label in the last slot, and the source lists
reordered by `σ` elsewhere. -/
private alias edgeTgt_symm' := _root_.Erdos408.OneSided.edgeTgt_symm

include h₂ in
/-- The source lists of the reversed choice: the target lists reordered by `σ'^{-1}`, which
are the source lists reordered by `σ` with the new label in the last slot. -/
theorem edgeSrc_revChoice    
        (h : Fin (padCount x + 1)) :
    edgeSrc s' (revChoice s c) i h =
      if h = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h := by
  change s'.2.1.1 i ((c.2.2.2.2 i).symm h) = _
  rw [h₂, edgeTgt_symm']

include h₂ in
/-- The target lists of the reversed choice are the source lists. -/
theorem edgeTgt_revChoice    
      : edgeTgt s' (revChoice s c) = s.2.1.1 := by
  funext i h
  change (if (c.1 i).symm h = Fin.last _ then edgeSrc s c i (Fin.last _)
    else edgeSrc s' (revChoice s c) i ((c.1 i).symm h)) = _
  rw [edgeSrc_revChoice h₂]
  split_ifs with hh
  · change s.2.1.1 i (c.1 i (Fin.last _)) = _
    rw [← hh, Equiv.apply_symm_apply]
  · change s.2.1.1 i (c.1 i ((c.1 i).symm h)) = _
    rw [Equiv.apply_symm_apply]

include h₂ in
/-- The reversed choice has the same pad product. -/
theorem edgePad_revChoice    
      : edgePad s' (revChoice s c) = edgePad s c := by
  unfold edgePad
  simp_all [edgeSrc_revChoice]

include h₂ in
/-- The unshared source primes of the reversed choice are the new labels. -/
theorem prod_edgeSrc_revChoice  
        :
    ∏ i, edgeSrc s' (revChoice s c) i (Fin.last _) = ∏ i, (c.2.2.2.1 i).1 := by
  simp only [edgeSrc_revChoice h₂, ↓reduceIte]

include h₁ in
/-- The reversed determinant is the negated determinant. -/
theorem edgeDet_revChoice    
      : edgeDet s' (revChoice s c) = -edgeDet s c := by
  unfold edgeDet
  change s'.1.1.1 * s.1.1.2 - s'.1.1.2 * s.1.1.1 = _
  rw [h₁]
  ring

/-- The particle promoted by the reversed choice is the particle stored by the edge. -/
theorem edgePromoted_revChoice (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) :
    edgePromoted (revChoice s c) i = edgeStored s c i := rfl

include h₁ h₂ in
/-- The particle stored by the reversed choice is the particle promoted by the edge. -/
theorem edgeStored_revChoice  
         
      : edgeStored s' (revChoice s c) i = edgePromoted c i := by
  unfold edgeStored edgePromoted
  rw [edgeSrc_revChoice h₂, ite_eq_left rfl, h₁]

end

section
variable (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)


/-- The unshared source prime of each group lies in its band. -/
private alias mem_band_edgeSrc' := _root_.Erdos408.OneSided.mem_band_edgeSrc

include hdisj in
/-- With disjoint bands, each particle is promoted by at most one group. -/
private alias card_promoted_le_one' := _root_.Erdos408.OneSided.card_promoted_le_one

include hdisj in
/-- With disjoint bands, each particle is stored by at most one group. -/
private theorem card_stored_le_one'
     
        (xp : Particle x d) :
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card ≤ 1 :=
  card_le_one.2 fun i hi j hj => by
    by_contra hij
    have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm)
    change edgeSrc s c i (Fin.last _) = edgeSrc s c j (Fin.last _) at hij'
    exact disjoint_left.1 (hdisj i j hij) (mem_band_edgeSrc' s c i _)
      (hij' ▸ mem_band_edgeSrc' s c j _)

end

section
variable (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1) (hν : ∀ p, 0 ≤ primeWeight q x d N p) (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p) {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r} (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c) (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c)


include hdisj hc hv in
/-- With disjoint bands, an admissible edge promotes each particle at most as often as it is
pending. -/
private alias card_promoted_le' := _root_.Erdos408.OneSided.card_promoted_le

include hdisj hc hv h₁ h₂ h₃ in
/-- The memory after the reversed choice is the source memory: the reversed edge stores the
promoted particles back and promotes the stored particles. -/
theorem edgeMem_revChoice  
       
       
          :
    edgeMem s' (revChoice s c) = s.2.2.1 := by
  classical
  funext xp
  have hP := card_promoted_le' hdisj hc hv xp
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

include hdisj hc hv h₁ h₂ h₃ in
/-- **The reversed choice is admissible**: its target lists are the source lists, the ban
holds since the source lists are distinct and the new labels avoid them, the pad product is
the same, both good-state tests swap, the stored particles are pending after the edge, and the
promoted particles are particles. -/
theorem edgeValid_revChoice
     
       
       
          :
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
    have hiI : (c.2.2.2.1 i).2 = true := (mem_filter.1 hi).2
    obtain ⟨xp, hxp, -⟩ := hprom i hiI
    rw [edgeStored_revChoice h₁ h₂, ← hxp]
    exact xp.2
  · rw [edgeMem_revChoice hdisj hc hv h₁ h₂ h₃]
    exact s.2.2.2

include hdisj hc hv h₁ h₂ h₃ in
/-- The reversed choice leads back to the source. -/
theorem chainEdgeOut_revChoice
     
       
       
          :
    chainEdgeOut x d Y d₀ u v r B s' (revChoice s c) = s := by
  rw [chainEdgeOut_of_valid' (edgeValid_revChoice hdisj hc hv h₁ h₂ h₃)]
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · exact edgeTgt_revChoice h₂
  · exact edgeMem_revChoice hdisj hc hv h₁ h₂ h₃

include h₁ h₂ in
/-- The reversed choice solves the reversed raw determinant equation. -/
theorem rawDet_revChoice    
        (h : RawDet s c) :
    RawDet s' (revChoice s c) := by
  unfold RawDet at h ⊢
  rw [edgeDet_revChoice h₁, edgePad_revChoice h₂, prod_edgeSrc_revChoice h₂]
  change -edgeDet s c = (edgePad s c : ℤ) * (((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℤ) -
    ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ))
  linear_combination -h

/-- Reversal exchanges the stored and the promoted groups. -/
theorem revChoice_mem_rawChoices  
       {S I} 
    (hc : c ∈ rawChoices x d Y d₀ u v r S I) :
    revChoice s c ∈ rawChoices x d Y d₀ u v r I S := by
  obtain ⟨-, hS, hI⟩ := mem_filter.1 hc
  refine mem_filter.2 ⟨?_, hI, ?_⟩
  · simp only [edgeChoices, mem_product, mem_univ, true_and, and_true]
    exact Fintype.mem_piFinset.2 fun i => mem_product.2
      ⟨mem_band_edgeSrc' s c i _, mem_univ _⟩
  · ext i
    rw [mem_filter, ← hS]
    simp only [mem_univ, true_and]
    change decide (i ∈ c.2.1) = true ↔ _
    rw [decide_eq_true_iff]

/-! ### The adjoint calculation -/



/-- **The memory weight under an edge**: removing `P ≤ 1` and adding `Q ≤ 1` particles at each
point, `w(S) ∏ S^P ∏ ν^Q = w(S') ∏ ν^P ∏ S'^Q` for `S' = S - P + Q`. -/
private theorem memWeight_mul_eq' {X : Type*} [Fintype X] [DecidableEq X] (ν : X → ℝ)
    (S P Q : X → ℕ) (hP : ∀ x, P x ≤ 1) (hQ : ∀ x, Q x ≤ 1) (hPS : ∀ x, P x ≤ S x) :
    memWeight ν S * (∏ x, (S x : ℝ) ^ P x) * ∏ x, ν x ^ Q x =
      memWeight ν (fun x => S x - P x + Q x) * (∏ x, ν x ^ P x) *
        ∏ x, ((S x - P x + Q x : ℕ) : ℝ) ^ Q x := by solve_by_elim [_root_.SharedProofs.shared_memWeight_mul_eq]

/-- A product over the points `y` of `f(y)` to the number of indices `i ∈ F` with `g(i) = y` is
the product over `i ∈ F` of `f` over the fiber of `g(i)`. -/
private theorem prod_pow_card_filter' {α ι M : Type*} [DecidableEq α] [CommMonoid M]
    {T : Finset α} (F : Finset ι) (g : ι → α) (f : ↥T → M) :
    ∏ y : ↥T, f y ^ (F.filter fun i => g i = y.1).card =
      ∏ i ∈ F, ∏ y : ↥T with y.1 = g i, f y := by solve_by_elim [_root_.SharedProofs.shared_prod_pow_card_filter]

/-- The fiber of a point of a subtype is a singleton. -/
private theorem filter_val_eq' {α : Type*} [DecidableEq α] {T : Finset α} {y : α} (z : ↥T)
    (hz : z.1 = y) : (univ.filter fun w : ↥T => w.1 = y) = {z} := by solve_by_elim [_root_.SharedProofs.shared_filter_val_eq]

/-- **The list weights under an edge**: `∏ f(act) ∏_i f(a_i) = ∏ f(act') ∏_i f(b_i)`, since the
source and target lists share their pads and differ by `b_i ↔ a_i`. -/
private alias prod_edgeTgt_mul' := _root_.Erdos408.OneSided.prod_edgeTgt_mul

include hdisj hV hν hνpos hc hv in
/-- **The adjoint calculation** (PD `mem:edge-factorial`): for an admissible edge `s → s'`,
`μ(s) ∏_i w_i ≤ 2^K μ(s') ∏_i w_i^{rev}`, where the reversed weights are `S'(y_i)/V(b_i)` for a
stored particle `y_i` and `ν(b_i)` otherwise. Removing a promoted particle `x_i` from `S` trades
its weight `S(x_i)` for `ν(a_i)`, which cancels the target label and leaves `1/V(a_i) ≤ 2`;
storing `b_i` trades the source label `ν(b_i)` for the multiplicity `S'(y_i) ≤ S'(y_i)/V(b_i)`. -/
theorem measure_mul_rawWeight_le
     
     
     
     
       
        :
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
  set ν := primeWeight q x d N with hνdef
  set S := s.2.2.1 with hS
  set S' := edgeMem s c with hS'
  set P : Particle x d → ℕ := fun xp =>
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card with hPdef
  set Q : Particle x d → ℕ := fun xp =>
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card with hQdef
  have hprom := hv.2.2.2.2.2.2.2.1
  have hstore := hv.2.2.2.2.2.2.2.2.1
  have hVa : ∀ i, 1 / 2 ≤ primeMass x d (c.2.2.2.1 i).1 := fun i => by
    rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)]
    exact (hV i).1
  have hVb : ∀ i, 1 / 2 ≤ primeMass x d (edgeSrc s c i (Fin.last _)) ∧
      primeMass x d (edgeSrc s c i (Fin.last _)) ≤ 1 := fun i => by
    rw [primeMass_eq_of_mem_band hdisj (mem_band_edgeSrc' s c i _)]
    exact hV i
  -- each particle is promoted and stored at most once, and only if pending
  have hP1 : ∀ xp, P xp ≤ 1 := card_promoted_le_one' hdisj hc
  have hQ1 : ∀ xp, Q xp ≤ 1 := card_stored_le_one' hdisj s c
  have hPS : ∀ xp, P xp ≤ S xp := card_promoted_le' hdisj hc hv
  -- the products over the particles as products over the groups
  have hfibP : ∀ f : Particle x d → ℝ, ∏ xp, f xp ^ P xp =
      ∏ i, if (c.2.2.2.1 i).2 = true then
        ∏ xp : Particle x d with xp.1 = edgePromoted c i, f xp else 1 := by
    intro f
    have hP' : ∀ xp, P xp = ((univ.filter fun i => (c.2.2.2.1 i).2 = true).filter
        fun i => edgePromoted c i = xp.1).card := fun xp => by rw [filter_filter]
    rw [prod_congr rfl fun xp _ => by rw [hP' xp], prod_pow_card_filter', prod_filter]
  have hii : ∏ xp, (S xp : ℝ) ^ P xp = ∏ i, if (c.2.2.2.1 i).2 = true then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0) else 1 := by
    rw [hfibP]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hf
    · obtain ⟨yp, hyp, -⟩ := hprom i hf
      rw [filter_val_eq' yp hyp, prod_singleton, ← sum_filter, filter_val_eq' yp hyp,
        sum_singleton]
    · rfl
  have hiii : ∏ xp : Particle x d, ν xp.1.1 ^ P xp =
      ∏ i, if (c.2.2.2.1 i).2 = true then ν (c.2.2.2.1 i).1 else 1 := by
    rw [hfibP]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hf
    · obtain ⟨yp, hyp, -⟩ := hprom i hf
      rw [filter_val_eq' yp hyp, prod_singleton, hyp]
      rfl
    · rfl
  have hiv : ∏ xp : Particle x d, ν xp.1.1 ^ Q xp =
      ∏ i, if i ∈ c.2.1 then ν (edgeSrc s c i (Fin.last _)) else 1 := by
    rw [prod_pow_card_filter', prod_ite_mem, univ_inter]
    refine prod_congr rfl fun i hi => ?_
    rw [filter_val_eq' ⟨_, hstore i hi⟩ rfl, prod_singleton]
    rfl
  have hv' : ∏ xp : Particle x d, ((S' xp : ℕ) : ℝ) ^ Q xp =
      ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ) else 1 := by
    rw [prod_pow_card_filter', prod_ite_mem, univ_inter]
    refine prod_congr rfl fun i hi => ?_
    rw [filter_val_eq' ⟨_, hstore i hi⟩ rfl, prod_singleton, memAt_eq, dite_eq_left (hstore i hi)]
  -- the memory weights
  have hmw := memWeight_mul_eq' (fun xp : Particle x d => ν xp.1.1) S P Q hP1 hQ1 hPS
  change memWeight _ S * _ * _ = memWeight _ S' * _ * ∏ xp, ((S' xp : ℕ) : ℝ) ^ Q xp at hmw
  set A := ∏ i, if (c.2.2.2.1 i).2 = true then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0) else 1 with hAdef
  set T := ∏ i, if i ∈ c.2.1 then ν (edgeSrc s c i (Fin.last _)) else 1 with hTdef
  set Bν := ∏ i, if (c.2.2.2.1 i).2 = true then ν (c.2.2.2.1 i).1 else 1 with hBdef
  set Mm := ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ) else 1 with hMdef
  set mW := memWeight (fun xp : Particle x d => ν xp.1.1) S with hmW
  set mW' := memWeight (fun xp : Particle x d => ν xp.1.1) S' with hmW'
  have hmW'0 : 0 ≤ mW' := memWeight_nonneg (fun xp => hν _) _
  have hA : mW * A * T = mW' * Bν * Mm := by rw [← hii, ← hiv, hmw, hiii, hv']
  -- the per-group rearrangements
  set E := ∏ i, if (c.2.2.2.1 i).2 = true then (primeMass x d (c.2.2.2.1 i).1)⁻¹
    else ν (c.2.2.2.1 i).1 with hEdef
  set G := ∏ i, if (c.2.2.2.1 i).2 = true then (primeMass x d (c.2.2.2.1 i).1)⁻¹ else 1
    with hGdef
  set Na := ∏ i, ν (c.2.2.2.1 i).1 with hNa
  set Nb := ∏ i, ν (edgeSrc s c i (Fin.last _)) with hNb
  set Cm := ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ)
    else ν (edgeSrc s c i (Fin.last _)) with hCm
  set Wr := ∏ i, if i ∈ c.2.1 then
      (memAt x d S' (edgeStored s c i) : ℝ) / primeMass x d (edgeSrc s c i (Fin.last _))
    else ν (edgeSrc s c i (Fin.last _)) with hWr
  set Two := ∏ i, if (c.2.2.2.1 i).2 = true then (2 : ℝ) else 1 with hTwo
  have hW : rawWeight q N s c = A * E := by
    rw [hAdef, hEdef, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [div_eq_mul_inv]
    · rw [one_mul]
  have hBE : Bν * E = Na * G := by
    rw [hBdef, hEdef, hNa, hGdef, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    split_ifs
    · rfl
    · rw [one_mul, mul_one]
  have hNbM : Nb * Mm = Cm * T := by
    rw [hNb, hMdef, hCm, hTdef, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [mul_comm]
    · rfl
  have hG : G ≤ Two := by
    rw [hGdef, hTwo]
    refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · split_ifs
      exacts [inv_nonneg.2 (by linarith [hVa i]), zero_le_one]
    · split_ifs
      · have := hVa i
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      · exact le_rfl
  have hTwoK : Two ≤ 2 ^ K := by
    calc Two ≤ ∏ _i : Fin K, (2 : ℝ) :=
          prod_le_prod₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by
            split_ifs <;> norm_num
      _ = 2 ^ K := by rw [prod_const, card_univ, Fintype.card_fin]
  have hCmWr : Cm ≤ Wr := by
    refine prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
    · split_ifs
      exacts [Nat.cast_nonneg _, hν _]
    · split_ifs
      · obtain ⟨h₁, h₂⟩ := hVb i
        rw [le_div_iff₀ (by linarith)]
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) h₂
      · exact le_rfl
  have hT : 0 < T := prod_pos fun i _ => by
    split_ifs
    exacts [hνpos i _ (mem_band_edgeSrc' s c i _), zero_lt_one]
  
  have hΛ'0 : 0 ≤ ∏ i, ∏ h, ν (edgeTgt s c i h) :=
    prod_nonneg fun i _ => prod_nonneg fun h _ => hν _
  
  have hCm0 : 0 ≤ Cm := prod_nonneg fun i _ => by
    split_ifs
    exacts [Nat.cast_nonneg _, hν _]
  have hΛ := prod_edgeTgt_mul' ν s c
  rw [← hNa, ← hNb] at hΛ
  rw [hW]
  have hmain : (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW * (A * E) ≤
      (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * Two) := by
    refine le_of_mul_le_mul_right ?_ hT
    calc (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW * (A * E) * T
        = (∏ i, ∏ h, ν (s.2.1.1 i h)) * E * (mW * A * T) := by ring
      _ = (∏ i, ∏ h, ν (s.2.1.1 i h)) * E * (mW' * Bν * Mm) := by rw [hA]
      _ = (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW' * Mm * (Bν * E) := by ring
      _ = ((∏ i, ∏ h, ν (s.2.1.1 i h)) * Na) * mW' * G * Mm := by rw [hBE]; ring
      _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * G * (Nb * Mm) := by rw [hΛ]; ring
      _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm * T * G := by rw [hNbM]; ring
      _ ≤ (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm * T * Two :=
          mul_le_mul_of_nonneg_left hG
            (mul_nonneg (mul_nonneg (mul_nonneg hΛ'0 hmW'0) hCm0) hT.le)
      _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * Two) * T := by ring
  refine hmain.trans ?_
  calc (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * Two)
      = Two * ((∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm) := by ring
    _ ≤ 2 ^ K * ((∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Wr) := by
        gcongr

end

end Reversal

/-! ### The column bound -/



variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

section
variable (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1) (hν : ∀ p, 0 ≤ primeWeight q x d N p) (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p) (hq : 0 < q) {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r} (hv : EdgeValid x d Y d₀ u v r B s c) (hc : c ∈ edgeChoices x d Y d₀ u v r) (h : EdgeValid x d Y d₀ u v r B s c ∧ RawDet s c) (hs' : chainEdgeOut x d Y d₀ u v r B s c = s')


include hv hs' in
/-- The output of an admissible edge choice. -/
private theorem out_eq    
        :
    s'.1 = c.2.2.1 ∧ s'.2.1.1 = edgeTgt s c ∧ s'.2.2.1 = edgeMem s c := by
  rw [← hs', chainEdgeOut_of_valid' hv]
  exact ⟨rfl, rfl, rfl⟩

/-- The weight product of the reversed choice. -/
theorem rawWeight_revChoice    
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

include hdisj hV hν hνpos hq hc h hs' in
/-- **The adjoint calculation for the raw coefficients**: for an admissible raw edge `s → s'`,
`μ(s) rawAmp(s, c) ≤ 2^K μ(s') rawAmp(s', c^rev)`. The pending factors swap, and
`measure_mul_rawWeight_le` compares the rest. -/
theorem measure_mul_rawAmp_le  
     
     
       
       
       
      :
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
theorem eq_of_revChoice    
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
    rw [h₂, edgeTgt_symm', ite_eq_left rfl]
    aesop
  · exact (Equiv.symm_symm _).symm

open scoped Classical in
include hq in
/-- **The column bound by reversal** (PD §4, dirty raw edges): the measure-weighted raw
coefficients of the piece `(S, I)` reaching `s'` sum to at most `2^K μ(s')` times the row of
the piece `(I, S)` at `s'`. Each admissible raw edge reaching `s'` is determined by its
reversed choice, which lies in the piece `(I, S)` (`eq_of_revChoice`). -/
theorem sum_col_rawAmp_le  
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)  S I 
     s'  :
    ∑ s, ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter
        (fun c => chainEdgeOut x d Y d₀ u v r B s c = s'),
      chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c ≤
      2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
        ∑ c' ∈ rawChoices x d Y d₀ u v r I S, rawAmp q N s' c') := by
  classical
  have hV' : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV i).1
  have hν := primeWeight_nonneg_of hV' hb (q := q) (N := N)
  have hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p := fun i p hp =>
    (primeWeight_le_two hdisj hV' hb hp).1
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
    have hcc : p.2 = p'.2 := by
      rw [eq_of_revChoice (hrc p hp) hv hout, eq_of_revChoice (hrc p' hp') hv' hout', heq]
    exact Prod.ext hs hcc
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

end



end Erdos408.OneSided
