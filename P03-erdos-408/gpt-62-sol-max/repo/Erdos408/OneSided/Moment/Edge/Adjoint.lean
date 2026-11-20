module

public import Erdos408.OneSided.Moment.Edge.RawRow

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real
open scoped Classical

variable {K : ℕ}

/-- The per-particle identity behind the memory weight: if `S' = S - P + Q` with `P, Q ≤ 1`
and `P ≤ S`, then `y^S/S! · S^P · y^Q = y^{S'}/S'! · y^P · S'^Q`. -/
private theorem pow_div_factorial_mul_eq {a P Q : ℕ} (y : ℝ) (hP : P ≤ 1) (hQ : Q ≤ 1)
    (hPa : P ≤ a) :
    y ^ a / (a.factorial : ℝ) * (a : ℝ) ^ P * y ^ Q =
      y ^ (a - P + Q) / ((a - P + Q).factorial : ℝ) * y ^ P * ((a - P + Q : ℕ) : ℝ) ^ Q := by
  interval_cases P <;> interval_cases Q
  · simp
  · rw [Nat.sub_zero, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.add_zero]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring

/-- **The memory weight under an edge**: removing `P ≤ 1` and adding `Q ≤ 1` particles at each
point, `w(S) ∏ S^P ∏ ν^Q = w(S') ∏ ν^P ∏ S'^Q` for `S' = S - P + Q`. -/
private theorem memWeight_mul_eq {X : Type*} [Fintype X] [DecidableEq X] (ν : X → ℝ)
    (S P Q : X → ℕ) (hP : ∀ x, P x ≤ 1) (hQ : ∀ x, Q x ≤ 1) (hPS : ∀ x, P x ≤ S x) :
    memWeight ν S * (∏ x, (S x : ℝ) ^ P x) * ∏ x, ν x ^ Q x =
      memWeight ν (fun x => S x - P x + Q x) * (∏ x, ν x ^ P x) *
        ∏ x, ((S x - P x + Q x : ℕ) : ℝ) ^ Q x := by
  unfold memWeight
  simp only [← prod_mul_distrib]
  exact prod_congr rfl fun x _ => pow_div_factorial_mul_eq (ν x) (hP x) (hQ x) (hPS x)

/-- A product over the points `y` of `f(y)` to the number of indices `i ∈ F` with `g(i) = y` is
the product over `i ∈ F` of `f` over the fiber of `g(i)`. -/
private theorem prod_pow_card_filter {α ι M : Type*} [DecidableEq α] [CommMonoid M]
    {T : Finset α} (F : Finset ι) (g : ι → α) (f : ↥T → M) :
    ∏ y : ↥T, f y ^ (F.filter fun i => g i = y.1).card =
      ∏ i ∈ F, ∏ y : ↥T with y.1 = g i, f y := by
  calc ∏ y : ↥T, f y ^ (F.filter fun i => g i = y.1).card
      = ∏ y : ↥T, ∏ i ∈ F, if g i = y.1 then f y else 1 :=
        prod_congr rfl fun y _ => by rw [← prod_const, prod_filter]
    _ = ∏ i ∈ F, ∏ y : ↥T, if g i = y.1 then f y else 1 := prod_comm
    _ = ∏ i ∈ F, ∏ y : ↥T with y.1 = g i, f y :=
        prod_congr rfl fun i _ => by
          rw [prod_filter]
          exact prod_congr rfl fun y _ => by simp only [eq_comm]

/-- The fiber of a point of a subtype is a singleton. -/
private theorem filter_val_eq {α : Type*} [DecidableEq α] {T : Finset α} {y : α} (z : ↥T)
    (hz : z.1 = y) : (univ.filter fun w : ↥T => w.1 = y) = {z} := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_singleton, ← hz, Subtype.ext_iff]

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The output of an admissible edge choice. -/
theorem chainEdgeOut_of_valid {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : EdgeValid x d Y d₀ u v r B s c) :
    chainEdgeOut x d Y d₀ u v r B s c =
      (c.2.2.1, ⟨edgeTgt s c, hv.1⟩, ⟨edgeMem s c, hv.2.2.2.2.2.2.2.2.2⟩) := by
  unfold chainEdgeOut
  rw [dite_eq_left hv]

/-- The target lists after undoing `σ'`: the new label in the last slot, and the source lists
reordered by `σ` elsewhere. -/
theorem edgeTgt_symm (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)
    (i : Fin K) (h : Fin (padCount x + 1)) :
    edgeTgt s c i ((c.2.2.2.2 i).symm h) =
      if h = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h := by
  simp only [edgeTgt, Equiv.apply_symm_apply]

/-- The pad product is a product of target labels. -/
theorem edgePad_eq_tgt (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    edgePad s c = ∏ i, ∏ h : Fin (padCount x), edgeTgt s c i ((c.2.2.2.2 i).symm h.castSucc) := by
  simp only [edgePad, edgeTgt_symm, Fin.castSucc_ne_last, ↓reduceIte]

/-- The new label of a group is a target label. -/
theorem label_eq_tgt (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)
    (i : Fin K) : (c.2.2.2.1 i).1 = edgeTgt s c i ((c.2.2.2.2 i).symm (Fin.last _)) := by
  simp only [edgeTgt_symm, ↓reduceIte]

/-- Away from the last slot, the source labels are target labels. -/
theorem edgeSrc_eq_tgt (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)
    (i : Fin K) {h : Fin (padCount x + 1)} (hh : h ≠ Fin.last _) :
    edgeSrc s c i h = edgeTgt s c i ((c.2.2.2.2 i).symm h) := by
  rw [edgeTgt_symm, ite_eq_right hh]

/-- **The list weights under an edge**: `∏ f(act) ∏_i f(a_i) = ∏ f(act') ∏_i f(b_i)`, since the
source and target lists share their pads and differ by `b_i ↔ a_i`. -/
private theorem prod_edgeTgt_mul (f : ℕ → ℝ) (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    (∏ i, ∏ h, f (s.2.1.1 i h)) * ∏ i, f (c.2.2.2.1 i).1 =
      (∏ i, ∏ h, f (edgeTgt s c i h)) * ∏ i, f (edgeSrc s c i (Fin.last _)) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have h₁ : ∏ h, f (s.2.1.1 i h) =
      (∏ h : Fin (padCount x), f (edgeSrc s c i h.castSucc)) * f (edgeSrc s c i (Fin.last _)) := by
    rw [← Fin.prod_univ_castSucc (fun h => f (edgeSrc s c i h))]
    exact (Equiv.prod_comp (c.1 i) (fun h => f (s.2.1.1 i h))).symm
  have h₂ : ∏ h, f (edgeTgt s c i h) =
      (∏ h : Fin (padCount x), f (edgeSrc s c i h.castSucc)) * f (c.2.2.2.1 i).1 := by
    rw [← Equiv.prod_comp (c.2.2.2.2 i).symm, Fin.prod_univ_castSucc]
    simp only [edgeTgt_symm, Fin.castSucc_ne_last, ↓reduceIte]
  rw [h₁, h₂]
  ring

/-- The reordered source labels of each group lie in its band. -/
theorem mem_band_edgeSrc (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)
    (i : Fin K) (h : Fin (padCount x + 1)) : edgeSrc s c i h ∈ band x (d.a i) :=
  mem_band_of_mem_lists s.2.1.2 i _

/-- With disjoint bands, each particle is promoted by at most one group. -/
theorem card_promoted_le_one
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {c : EdgeChoice x d Y d₀ u v r} (hc : c ∈ edgeChoices x d Y d₀ u v r) (xp : Particle x d) :
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card ≤ 1 :=
  card_le_one.2 fun i hi j hj => by
    by_contra hij
    have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.2.trans (mem_filter.1 hj).2.2.symm)
    change (c.2.2.2.1 i).1 = (c.2.2.2.1 j).1 at hij'
    refine disjoint_left.1 (hdisj i j hij) (mem_band_lab hc i) ?_
    rw [hij']
    exact mem_band_lab hc j

/-- With disjoint bands, an admissible edge promotes each particle at most as often as it is
pending. -/
theorem card_promoted_le
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (xp : Particle x d) :
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card ≤ s.2.2.1 xp := by
  classical
  rcases Nat.eq_zero_or_pos
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · obtain ⟨i, hi⟩ := card_pos.1 hpos
    obtain ⟨hf, he⟩ := (mem_filter.1 hi).2
    obtain ⟨yp, hyp, hS1⟩ := hv.2.2.2.2.2.2.2.1 i hf
    have hyx : yp = xp := Subtype.ext (hyp.trans he)
    rw [← hyx]
    exact (card_promoted_le_one hdisj hc yp).trans hS1

/-- With disjoint bands, each particle is stored by at most one group. -/
private theorem card_stored_le_one
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) (xp : Particle x d) :
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card ≤ 1 :=
  card_le_one.2 fun i hi j hj => by
    by_contra hij
    have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm)
    change edgeSrc s c i (Fin.last _) = edgeSrc s c j (Fin.last _) at hij'
    exact disjoint_left.1 (hdisj i j hij) (mem_band_edgeSrc s c i _)
      (hij' ▸ mem_band_edgeSrc s c j _)

/-- The weight of a reversed label, with the reciprocal mass of a forward promotion.
A stored label receives its multiplicity at the original position. -/
def reverseLabelWeight (q : ℝ) (N : ℕ) (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) : ℝ :=
  (if i ∈ c.2.1 then (memAt x d (edgeMem s c) (edgeStored s c i) : ℝ)
    else primeWeight q x d N (edgeSrc s c i (Fin.last _))) *
  (if (c.2.2.2.1 i).2 then (primeMass x d (c.2.2.2.1 i).1)⁻¹ else 1)

/-- Exact transport of the measure-weighted label product across an admissible edge. -/
theorem edge_weight_transport
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c) :
    (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
        rawWeight q N s c =
      (∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
        ∏ i, reverseLabelWeight q N s c i := by
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
  -- each particle is promoted and stored at most once, and only if pending
  have hP1 : ∀ xp, P xp ≤ 1 := card_promoted_le_one hdisj hc
  have hQ1 : ∀ xp, Q xp ≤ 1 := card_stored_le_one hdisj s c
  have hPS : ∀ xp, P xp ≤ S xp := card_promoted_le hdisj hc hv
  -- the products over the particles as products over the groups
  have hfibP : ∀ f : Particle x d → ℝ, ∏ xp, f xp ^ P xp =
      ∏ i, if (c.2.2.2.1 i).2 = true then
        ∏ xp : Particle x d with xp.1 = edgePromoted c i, f xp else 1 := by
    intro f
    have hP' : ∀ xp, P xp = ((univ.filter fun i => (c.2.2.2.1 i).2 = true).filter
        fun i => edgePromoted c i = xp.1).card := fun xp => by rw [filter_filter]
    rw [prod_congr rfl fun xp _ => by rw [hP' xp], prod_pow_card_filter, prod_filter]
  have hii : ∏ xp, (S xp : ℝ) ^ P xp = ∏ i, if (c.2.2.2.1 i).2 = true then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0) else 1 := by
    rw [hfibP]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hf
    · obtain ⟨yp, hyp, -⟩ := hprom i hf
      rw [filter_val_eq yp hyp, prod_singleton, ← sum_filter, filter_val_eq yp hyp,
        sum_singleton]
    · rfl
  have hiii : ∏ xp : Particle x d, ν xp.1.1 ^ P xp =
      ∏ i, if (c.2.2.2.1 i).2 = true then ν (c.2.2.2.1 i).1 else 1 := by
    rw [hfibP]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hf
    · obtain ⟨yp, hyp, -⟩ := hprom i hf
      rw [filter_val_eq yp hyp, prod_singleton, hyp]
      rfl
    · rfl
  have hiv : ∏ xp : Particle x d, ν xp.1.1 ^ Q xp =
      ∏ i, if i ∈ c.2.1 then ν (edgeSrc s c i (Fin.last _)) else 1 := by
    rw [prod_pow_card_filter, prod_ite_mem, univ_inter]
    refine prod_congr rfl fun i hi => ?_
    rw [filter_val_eq ⟨_, hstore i hi⟩ rfl, prod_singleton]
    rfl
  have hv' : ∏ xp : Particle x d, ((S' xp : ℕ) : ℝ) ^ Q xp =
      ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ) else 1 := by
    rw [prod_pow_card_filter, prod_ite_mem, univ_inter]
    refine prod_congr rfl fun i hi => ?_
    rw [filter_val_eq ⟨_, hstore i hi⟩ rfl, prod_singleton, memAt_eq, dite_eq_left (hstore i hi)]
  -- the memory weights
  have hmw := memWeight_mul_eq (fun xp : Particle x d => ν xp.1.1) S P Q hP1 hQ1 hPS
  change memWeight _ S * _ * _ = memWeight _ S' * _ * ∏ xp, ((S' xp : ℕ) : ℝ) ^ Q xp at hmw
  set A := ∏ i, if (c.2.2.2.1 i).2 = true then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0) else 1 with hAdef
  set T := ∏ i, if i ∈ c.2.1 then ν (edgeSrc s c i (Fin.last _)) else 1 with hTdef
  set Bν := ∏ i, if (c.2.2.2.1 i).2 = true then ν (c.2.2.2.1 i).1 else 1 with hBdef
  set Mm := ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ) else 1 with hMdef
  set mW := memWeight (fun xp : Particle x d => ν xp.1.1) S with hmW
  set mW' := memWeight (fun xp : Particle x d => ν xp.1.1) S' with hmW'
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
  have hT : 0 < T := prod_pos fun i _ => by
    split_ifs
    exacts [hνpos i _ (mem_band_edgeSrc s c i _), zero_lt_one]
  have hΛ := prod_edgeTgt_mul ν s c
  rw [← hNa, ← hNb] at hΛ
  rw [hW]
  have hrev : (∏ i, reverseLabelWeight q N s c i) = Cm * G := prod_mul_distrib
  rw [hrev]
  apply mul_right_cancel₀ hT.ne'
  calc (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW * (A * E) * T
      = (∏ i, ∏ h, ν (s.2.1.1 i h)) * E * (mW * A * T) := by ring
    _ = (∏ i, ∏ h, ν (s.2.1.1 i h)) * E * (mW' * Bν * Mm) := by rw [hA]
    _ = (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW' * Mm * (Bν * E) := by ring
    _ = ((∏ i, ∏ h, ν (s.2.1.1 i h)) * Na) * mW' * G * Mm := by rw [hBE]; ring
    _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * G * (Nb * Mm) := by rw [hΛ]; ring
    _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm * T * G := by rw [hNbM]; ring
    _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * G) * T := by ring

/-- Widen the reciprocal mass of a promotion to the factor two. -/
theorem promotionFactor_le_two {a : ℝ} (ha : 1 / 2 ≤ a) : a⁻¹ ≤ 2 := by
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

end Erdos408.OneSided
