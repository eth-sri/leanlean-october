module

public import proofs.HordijkSteelThreshold.Ambient


@[expose] public section

namespace HordijkSteelThreshold

section CombinatorialWords

def shortBinaryWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k + 1 => insert [] ((Finset.univ : Finset Bool).biUnion
      fun b => (shortBinaryWords k).image (List.cons b))

theorem mem_shortBinaryWords (s : List Bool) : ∀ k : ℕ, s ∈ shortBinaryWords k ↔ s.length ≤ k
  | 0 => by simp [shortBinaryWords]
  | k + 1 => by
    cases s with
    | nil => simp [shortBinaryWords]
    | cons b t => cases b <;> simp [shortBinaryWords, mem_shortBinaryWords t k]

private theorem shortBinaryWords_card_exact : ∀ n : ℕ, (shortBinaryWords n).card + 1 = 2 ^ (n + 1)
  | 0 => rfl
  | n + 1 => by
    have he : shortBinaryWords (n + 1) = insert []
        (((shortBinaryWords n).image (List.cons true)) ∪ ((shortBinaryWords n).image (List.cons false))) := by
      ext; simp [shortBinaryWords]
    have hd : Disjoint ((shortBinaryWords n).image (List.cons true))
        ((shortBinaryWords n).image (List.cons false)) :=
      Finset.disjoint_left.mpr fun _ hs ht => by
        obtain ⟨_, _, ha⟩ := Finset.mem_image.mp hs; obtain ⟨_, _, hb⟩ := Finset.mem_image.mp ht
        cases ha.trans hb.symm
    rw [he, Finset.card_insert_of_notMem (by simp), Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective, pow_succ]
    have := shortBinaryWords_card_exact n; omega

private theorem shortBinaryWords_card_lt (k : ℕ) : (shortBinaryWords k).card < 2 ^ (k + 1) := by
  have := shortBinaryWords_card_exact k; omega

private theorem core_containing_words_card_lt (S : Finset (List Bool)) (core : List Bool) (k : ℕ)
    (hc : ∀ s ∈ S, ∃ l r : List Bool, s = l ++ core ++ r)
    (hl : ∀ s ∈ S, s.length ≤ core.length + k) : S.card < 2 ^ (2 * (k + 1)) := by
  have hs : S ⊆ ((shortBinaryWords k) ×ˢ (shortBinaryWords k)).image fun lr => lr.1 ++ core ++ lr.2 :=
    fun s h => by
      obtain ⟨l, r, rfl⟩ := hc s h
      have hlen := hl _ h; simp only [List.length_append] at hlen
      exact Finset.mem_image.mpr ⟨(l, r), Finset.mem_product.mpr
        ⟨(mem_shortBinaryWords l k).mpr (by omega), (mem_shortBinaryWords r k).mpr (by omega)⟩, rfl⟩
  exact ((Finset.card_le_card hs).trans (Finset.card_image_le.trans (Finset.card_product _ _).le)).trans_lt
    ((Nat.mul_self_lt_mul_self (shortBinaryWords_card_lt k)).trans_eq (by rw [← pow_add, two_mul]))

def actualBinaryWords (N : ℕ) : Finset (List Bool) := (shortBinaryWords N).erase []

theorem mem_actualBinaryWords (s : List Bool) (N : ℕ) :
    s ∈ actualBinaryWords N ↔ s ≠ [] ∧ s.length ≤ N := by
  simp [actualBinaryWords, mem_shortBinaryWords]

theorem actualBinaryWords_card (N : ℕ) : (actualBinaryWords N).card = 2 ^ (N + 1) - 2 := by
  have := shortBinaryWords_card_exact N
  rw [actualBinaryWords, Finset.card_erase_of_mem ((mem_shortBinaryWords [] N).mpr (Nat.zero_le _))]
  omega

private theorem molecular_minor_side_below_band (N M : ℕ) (hMN : M < N)
    (S : Finset (List Bool)) (hsub : S ⊆ actualBinaryWords N)
    (hminor : S.card ≤ (actualBinaryWords N \ S).card)
    (hconstant : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
      M ≤ u.length → M ≤ v.length → (u ∈ S ↔ v ∈ S))
    (s : List Bool) (hs : s ∈ S) : s.length < M := by
  by_contra h
  have hM : 0 < M := by
    by_contra hz
    have hc : actualBinaryWords N \ S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun t ht =>
      (Finset.mem_sdiff.mp ht).2 ((hconstant s (hsub hs) t (Finset.mem_sdiff.mp ht).1 (by omega) (by omega)).mp hs)
    have := Finset.card_pos.mpr ⟨s, hs⟩
    rw [hc, Finset.card_empty] at hminor; omega
  have hcomp : actualBinaryWords N \ S ⊆ shortBinaryWords (M - 1) := fun t ht => by
    obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
    exact (mem_shortBinaryWords t _).mpr (by
      by_contra hge; exact htS ((hconstant s (hsub hs) t htU (by omega) (by omega)).mp hs))
  have hc : (actualBinaryWords N \ S).card < 2 ^ M := by
    simpa [Nat.sub_add_cancel hM] using (Finset.card_le_card hcomp).trans_lt (shortBinaryWords_card_lt (M - 1))
  have hp : (2 : ℕ) ^ M < 2 ^ N := (pow_lt_pow_iff_right₀ one_lt_two).mpr hMN
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  rw [actualBinaryWords_card, pow_succ] at hpart; omega

private def endWordChoices (s : List Bool) : Finset (List Bool) :=
  [s, s.tail, s.dropLast, false :: s, true :: s, s ++ [false], s ++ [true]].toFinset

@[simp] private theorem mem_endWordChoices {s x : List Bool} :
    x ∈ endWordChoices s ↔
      x = s ∨ x = s.tail ∨ x = s.dropLast ∨ x = false :: s ∨ x = true :: s ∨ x = s ++ [false] ∨ x = s ++ [true] := by
  simp [endWordChoices]

private theorem endWordChoices_card (s : List Bool) : (endWordChoices s).card ≤ 7 := List.toFinset_card_le _

attribute [irreducible] endWordChoices

private def endWordBall : ℕ → List Bool → Finset (List Bool)
  | 0, s => {s}
  | k + 1, s => (endWordChoices s).biUnion (endWordBall k)

private theorem endWordBall_self : ∀ k s, s ∈ endWordBall k s
  | 0, _ => Finset.mem_singleton_self _
  | k + 1, s => Finset.mem_biUnion.mpr ⟨s, by simp, endWordBall_self k s⟩

private theorem mem_endWordBall_succ {k : ℕ} {u x v : List Bool}
    (hx : x ∈ endWordChoices u) (hv : v ∈ endWordBall k x) : v ∈ endWordBall (k + 1) u :=
  Finset.mem_biUnion.mpr ⟨x, hx, hv⟩

private theorem mem_endWordBall_one {u v : List Bool} (h : v ∈ endWordChoices u) : v ∈ endWordBall 1 u :=
  mem_endWordBall_succ h (endWordBall_self 0 v)

private theorem endWordBall_card : ∀ k s, (endWordBall k s).card ≤ 7 ^ k
  | 0, _ => by simp [endWordBall]
  | k + 1, s => Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (g := fun _ => 7 ^ k) fun v _ => endWordBall_card k v).trans
        (by simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]; rw [Nat.mul_comm (7 ^ k)]
            exact Nat.mul_le_mul_right _ (endWordChoices_card s)))

private theorem endWordBall_trans : ∀ {j k u v w}, v ∈ endWordBall j u → w ∈ endWordBall k v → w ∈ endWordBall (j + k) u
  | 0, _, _, _, _, hv, hw => by rw [Nat.zero_add]; exact Finset.mem_singleton.mp hv ▸ hw
  | j + 1, _, _, _, _, hv, hw => by
    obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.mp hv
    rw [Nat.succ_add]; exact Finset.mem_biUnion.mpr ⟨x, hx, endWordBall_trans hvx hw⟩

private theorem endWordBall_mono {j k : ℕ} (h : j ≤ k) {u v : List Bool} (hv : v ∈ endWordBall j u) :
    v ∈ endWordBall k u := by
  rw [show k = j + (k - j) by omega]; exact endWordBall_trans hv (endWordBall_self _ _)

private theorem endWordChoices_symm {u v : List Bool} (h : v ∈ endWordChoices u) : u ∈ endWordChoices v := by
  rcases mem_endWordChoices.mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try simp
  · cases u with | nil => simp | cons b _ => cases b <;> simp
  · by_cases hu : u = []
    · simp [hu]
    · rw [← List.dropLast_append_getLast hu, List.dropLast_concat]; cases u.getLast hu <;> simp

private theorem endWordBall_symm : ∀ {k u v}, v ∈ endWordBall k u → u ∈ endWordBall k v
  | 0, _, _, h => by simpa [endWordBall] using (Finset.mem_singleton.mp h).symm
  | k + 1, u, _, h => by
    obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.mp h
    exact endWordBall_trans (j := k) (k := 1) (endWordBall_symm hvx) (mem_endWordBall_one (endWordChoices_symm hx))

private theorem endWordBall_length : ∀ {k u v}, v ∈ endWordBall k u → v.length ≤ u.length + k
  | 0, _, _, h => by simp [Finset.mem_singleton.mp h]
  | k + 1, u, _, h => by
    obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.mp h
    have := endWordBall_length hvx
    rcases mem_endWordChoices.mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at * <;> omega

private theorem endWordBall_protects_core : ∀ {k u v}, v ∈ endWordBall k u →
    ∀ {core left right : List Bool}, u = left ++ core ++ right → k ≤ left.length → k ≤ right.length →
    ∃ l r : List Bool, v = l ++ core ++ r
  | 0, _, _, hv, _, left, right, hu, _, _ => ⟨left, right, (Finset.mem_singleton.mp hv).trans hu⟩
  | k + 1, _, _, hv, core, left, right, hu, hl, hr => by
    obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.mp hv
    have hstep : ∃ l r : List Bool, x = l ++ core ++ r ∧ k ≤ l.length ∧ k ≤ r.length := by
      rcases mem_endWordChoices.mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨left, right, hu, by omega, by omega⟩
      · cases left with | nil => simp at hl | cons _ t => exact ⟨t, right, by simp [hu, List.append_assoc], by simp at hl; omega, by omega⟩
      · have hn : right ≠ [] := fun he => by simp [he] at hr
        refine ⟨left, right.dropLast, ?_, by omega, by simp; omega⟩
        conv_lhs => rw [hu, ← List.dropLast_append_getLast hn]
        simp [← List.append_assoc]
      · exact ⟨false :: left, right, by simp [hu], by dsimp; omega, by omega⟩
      · exact ⟨true :: left, right, by simp [hu], by dsimp; omega, by omega⟩
      · exact ⟨left, right ++ [false], by simp [hu, List.append_assoc], by omega, by simp; omega⟩
      · exact ⟨left, right ++ [true], by simp [hu, List.append_assoc], by omega, by simp; omega⟩
    obtain ⟨l, r, hx', hkl, hkr⟩ := hstep
    exact endWordBall_protects_core hvx hx' hkl hkr

private theorem endWordBall_common_core (u v core : List Bool)
    (hu : ∃ l r : List Bool, u = l ++ core ++ r)
    (hv : ∃ l r : List Bool, v = l ++ core ++ r) :
    v ∈ endWordBall (u.length + v.length - 2 * core.length) u := by
  have hpad (l r : List Bool) : l ++ core ++ r ∈ endWordBall (l.length + r.length) core := by
    have hl (a : List Bool) : a ++ core ∈ endWordBall a.length core := by
      induction a with
      | nil => exact endWordBall_self 0 _
      | cons b a ih =>
        rw [List.length_cons]
        exact endWordBall_trans (j := a.length) (k := 1) ih (mem_endWordBall_one (by cases b <;> simp))
    have hr (b : List Bool) : ∀ s : List Bool, s ++ b ∈ endWordBall b.length s := by
      induction b with
      | nil => intro s; rw [List.append_nil]; exact endWordBall_self 0 _
      | cons c b ih =>
        intro s; rw [List.length_cons, show s ++ c :: b = (s ++ [c]) ++ b by simp]
        exact mem_endWordBall_succ (by cases c <;> simp) (ih (s ++ [c]))
    exact endWordBall_trans (j := l.length) (k := r.length) (hl l) (hr r (l ++ core))
  obtain ⟨l1, r1, rfl⟩ := hu; obtain ⟨l2, r2, rfl⟩ := hv
  rw [show (l1 ++ core ++ r1).length + (l2 ++ core ++ r2).length - 2 * core.length =
    (l1.length + r1.length) + (l2.length + r2.length) by simp; omega]
  exact endWordBall_trans (j := l1.length + r1.length) (k := l2.length + r2.length)
    (endWordBall_symm (hpad l1 r1)) (hpad l2 r2)

private def wordBasicVerts (L N : ℕ) : Finset (List Bool) :=
  insert [] ((actualBinaryWords N).filter fun s => L < s.length)

@[simp] private theorem mem_wordBasicVerts {L N : ℕ} {s : List Bool} :
    s ∈ wordBasicVerts L N ↔ s = [] ∨ (L < s.length ∧ s.length ≤ N) := by
  simp only [wordBasicVerts, Finset.mem_insert, Finset.mem_filter, mem_actualBinaryWords]
  exact or_congr_right ⟨fun ⟨⟨_, hN⟩, hL⟩ => ⟨hL, hN⟩,
    fun ⟨hL, hN⟩ => ⟨⟨List.length_pos_iff.mp (by omega), hN⟩, hL⟩⟩

private def wordBasicEdges (L N : ℕ) : Finset (List Bool × Bool) :=
  ((actualBinaryWords N).filter fun s => L < s.length) ×ˢ Finset.univ

@[simp] private theorem mem_wordBasicEdges {L N : ℕ} {e : List Bool × Bool} :
    e ∈ wordBasicEdges L N ↔ L < e.1.length ∧ e.1.length ≤ N := by
  simp only [wordBasicEdges, Finset.mem_product, Finset.mem_filter, mem_actualBinaryWords, Finset.mem_univ, and_true]
  exact ⟨fun ⟨⟨_, hN⟩, hL⟩ => ⟨hL, hN⟩, fun ⟨hL, hN⟩ => ⟨⟨List.length_pos_iff.mp (by omega), hN⟩, hL⟩⟩

end CombinatorialWords

/-- Explicit base constant C for the contour envelope size C^b. -/
def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped Topology ENNReal

noncomputable def staticOpenReactions {N : ℕ} (ω : Reaction N → Prop) : Finset (Reaction N) :=
  Finset.univ.filter ω

noncomputable def staticReactionMeasure (N : ℕ) (a : I) : Measure (Reaction N → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable instance staticReactionMeasure_probability (N : ℕ) (a : I) :
    IsProbabilityMeasure (staticReactionMeasure N a) := by
  unfold staticReactionMeasure; infer_instance

noncomputable def contourBudget (a : I) (k : ℕ) : ENNReal :=
  (molecularContourConstant : ENNReal) * (1 - (toNNReal a : ENNReal) ^ 2) ^ k

private def quadParity (f : Fin 4 → Bool) : Bool := ((f 0 ^^ f 1) ^^ f 2) ^^ f 3

private theorem quadParity_closed_subset : ∀ F C : Fin 4 → Bool,
    (∀ i, F i = true → C i = true) →
    (∀ i j, F i = true → C j = true → F j = true) →
    quadParity C = false → quadParity F = false := by decide

private def diamondPotential {V : Type*} (right : V → V) (rightEdge : V → Bool) : ℕ → V → Bool
  | 0, _ => false
  | k + 1, v => rightEdge v ^^ diamondPotential right rightEdge k (right v)

private def foodWordLeft (L : ℕ) (s : List Bool) : List Bool := if s.length ≤ L + 1 then [] else s.tail
private def foodWordRight (L : ℕ) (s : List Bool) : List Bool := if s.length ≤ L + 1 then [] else s.dropLast
private def wordEdgeParent (L : ℕ) (e : List Bool × Bool) : List Bool :=
  if e.2 then foodWordRight L e.1 else foodWordLeft L e.1

private theorem foodWordParents_commute (L : ℕ) (s : List Bool) :
    foodWordLeft L (foodWordRight L s) = foodWordRight L (foodWordLeft L s) := by
  by_cases h : s.length ≤ L + 1
  · simp [foodWordLeft, foodWordRight, h]
  · simp only [foodWordLeft, foodWordRight, ite_eq_right h, List.length_dropLast, List.length_tail]
    split_ifs <;> simp [List.tail_dropLast]

private theorem foodWordLeft_vert {L N : ℕ} {v : List Bool} (hv : v ∈ wordBasicVerts L N) :
    foodWordLeft L v ∈ wordBasicVerts L N := by
  rw [mem_wordBasicVerts] at hv ⊢
  rcases hv with rfl | ⟨_, hN⟩
  · simp [foodWordLeft]
  · by_cases h : v.length ≤ L + 1 <;> simp [foodWordLeft, h]; omega

private theorem foodWordRight_vert {L N : ℕ} {v : List Bool} (hv : v ∈ wordBasicVerts L N) :
    foodWordRight L v ∈ wordBasicVerts L N := by
  rw [mem_wordBasicVerts] at hv ⊢
  rcases hv with rfl | ⟨_, hN⟩
  · simp [foodWordRight]
  · by_cases h : v.length ≤ L + 1 <;> simp [foodWordRight, h]; omega

private theorem foodWordRight_len (L : ℕ) (s : List Bool) :
    (foodWordRight L s).length ≤ s.length - 1 := by
  simp only [foodWordRight]; split_ifs <;> simp

private theorem diamondPotential_edges {L N : ℕ} (leftEdge rightEdge : List Bool → Bool)
    (hroot : leftEdge [] = false ∧ rightEdge [] = false)
    (hdiamond : ∀ v ∈ wordBasicVerts L N,
      (((leftEdge v ^^ rightEdge v) ^^ leftEdge (foodWordRight L v)) ^^ rightEdge (foodWordLeft L v)) = false)
    (k : ℕ) : ∀ v ∈ wordBasicVerts L N, v.length - L ≤ k →
      ((diamondPotential (foodWordRight L) rightEdge k v ^^ diamondPotential (foodWordRight L) rightEdge k (foodWordLeft L v)) = leftEdge v) ∧
      ((diamondPotential (foodWordRight L) rightEdge k v ^^ diamondPotential (foodWordRight L) rightEdge k (foodWordRight L v)) = rightEdge v) := by
  have h1 : ∀ a b rv rlv lv lrv : Bool, (a ^^ b) = lrv → (((lv ^^ rv) ^^ lrv) ^^ rlv) = false → ((rv ^^ a) ^^ (rlv ^^ b)) = lv := by decide
  have h2 : ∀ a b c rv : Bool, (b ^^ c) = rv → ((a ^^ b) ^^ (rv ^^ c)) = a := by decide
  induction k with
  | zero =>
    intro v hv hk
    obtain rfl : v = [] := (mem_wordBasicVerts.mp hv).resolve_right (by omega)
    simp [diamondPotential, hroot.1, hroot.2]
  | succ k ih =>
    intro v hv hk
    obtain ⟨hil, hir⟩ := ih (foodWordRight L v) (foodWordRight_vert hv) (by have := foodWordRight_len L v; omega)
    rw [foodWordParents_commute] at hil
    exact ⟨h1 _ _ _ _ _ _ hil (hdiamond v hv), h2 _ _ _ _ hir⟩

private noncomputable def wordGraphCut (L N : ℕ) (f : List Bool → Bool) : Finset (List Bool × Bool) :=
  (wordBasicEdges L N).filter fun e => f e.1 ≠ f (wordEdgeParent L e)

private def wordEdgeReach (L : ℕ) (active : Finset (List Bool × Bool)) : List Bool → List Bool → Prop :=
  Relation.EqvGen fun x y => ∃ e ∈ active, e.1 = x ∧ wordEdgeParent L e = y

private theorem wordGraph_disabled_bond {L N : ℕ} (active : Finset (List Bool × Bool))
    {x y : List Bool} (hx : x ∈ wordBasicVerts L N) (hy : y ∈ wordBasicVerts L N)
    (hxy : ¬ wordEdgeReach L active x y) :
    ∃ f : List Bool → Bool, f x ≠ f y ∧
      wordGraphCut L N f ⊆ wordBasicEdges L N \ active ∧ (wordGraphCut L N f).Nonempty ∧
      ∀ g : List Bool → Bool, (wordGraphCut L N g).Nonempty →
        wordGraphCut L N g ⊆ wordGraphCut L N f → wordGraphCut L N g = wordGraphCut L N f := by
  have hroot {w : List Bool} (hw : w ∈ wordBasicVerts L N) : wordEdgeReach L (wordBasicEdges L N) w [] := by
    suffices ∀ k z, z ∈ wordBasicVerts L N → z.length - L ≤ k → wordEdgeReach L (wordBasicEdges L N) z [] from
      this N w hw (by rcases mem_wordBasicVerts.mp hw with rfl | ⟨_, hN⟩ <;> [simp; omega])
    intro k; induction k with
    | zero => intro z hz hk; exact (mem_wordBasicVerts.mp hz).resolve_right (by omega) ▸ .refl _
    | succ k ih =>
      intro z hz hk
      rcases mem_wordBasicVerts.mp hz with rfl | hz'
      · exact .refl _
      · exact .trans _ _ _ (.rel _ _ ⟨(z, true), mem_wordBasicEdges.mpr hz', rfl, rfl⟩)
          (ih _ (foodWordRight_vert hz) (by dsimp [wordEdgeParent]; have := foodWordRight_len L z; omega))
  have hhost : wordEdgeReach L (wordBasicEdges L N) x y := .trans _ _ _ (hroot hx) (.symm _ _ (hroot hy))
  have hex : ∃ k : ℕ, ∃ f : List Bool → Bool, f x ≠ f y ∧
      wordGraphCut L N f ⊆ wordBasicEdges L N \ active ∧ (wordGraphCut L N f).card = k := by
    let f0 (v : List Bool) := decide (wordEdgeReach L active x v)
    refine ⟨_, f0, by have hxx : wordEdgeReach L active x x := .refl x; simp [f0, hxx, hxy], fun e he => ?_, rfl⟩
    obtain ⟨heE, hdiff⟩ := Finset.mem_filter.mp he
    refine Finset.mem_sdiff.mpr ⟨heE, fun heA => hdiff ?_⟩
    have hab : wordEdgeReach L active e.1 (wordEdgeParent L e) := .rel _ _ ⟨e, heA, rfl, rfl⟩
    simp [f0, show wordEdgeReach L active x e.1 ↔ wordEdgeReach L active x (wordEdgeParent L e) from
      ⟨fun h => .trans _ _ _ h hab, fun h => .trans _ _ _ h (.symm _ _ hab)⟩]
  obtain ⟨f, hf, hc, hcard⟩ := Nat.find_spec hex
  have hmin (g : List Bool → Bool) (hg : g x ≠ g y) (hgc : wordGraphCut L N g ⊆ wordBasicEdges L N \ active) :
      (wordGraphCut L N f).card ≤ (wordGraphCut L N g).card := hcard ▸ Nat.find_min' hex ⟨g, hg, hgc, rfl⟩
  refine ⟨f, hf, hc, ?_, fun g hgne hgsub => ?_⟩
  · by_contra hn
    have hlbl {u v} (h : wordEdgeReach L (wordBasicEdges L N) u v) : f u = f v := by
      induction h with
      | rel _ _ h => obtain ⟨e, he, rfl, rfl⟩ := h; by_contra hd; exact hn ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩⟩
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact hf (hlbl hhost)
  · by_cases hsep : g x ≠ g y
    · exact Finset.eq_of_subset_of_card_le hgsub (hmin g hsep (hgsub.trans hc))
    · have heq : g x = g y := not_ne_iff.mp hsep
      have hxor : wordGraphCut L N (fun v => f v ^^ g v) = wordGraphCut L N f \ wordGraphCut L N g := by
        ext e; by_cases he : e ∈ wordBasicEdges L N <;> simp [wordGraphCut, he]
        have hi := @hgsub e; simp [wordGraphCut, he] at hi
        generalize f e.1 = a, f (wordEdgeParent L e) = b, g e.1 = c, g (wordEdgeParent L e) = d at hi ⊢
        decide +revert
      have hsmall := Finset.card_lt_card (Finset.sdiff_ssubset hgsub hgne)
      have hm := hmin (fun v => f v ^^ g v)
        (by rw [heq]; generalize f x = a, f y = b, g y = c at hf ⊢; decide +revert)
        (hxor ▸ Finset.sdiff_subset.trans hc)
      rw [hxor] at hm; omega

private theorem foodWordLeft_preimage {L : ℕ} {u v : List Bool} (hv : v ≠ [])
    (hp : foodWordLeft L u = v) : ∃ b : Bool, u = b :: v := by
  have hs : ¬ u.length ≤ L + 1 := fun h => hv (by simpa [foodWordLeft, h] using hp.symm)
  rw [foodWordLeft, ite_eq_right hs] at hp
  cases u with
  | nil => simp at hs
  | cons b _ => exact ⟨b, congrArg (List.cons b) hp⟩

private theorem foodWordRight_preimage {L : ℕ} {u v : List Bool} (hv : v ≠ [])
    (hp : foodWordRight L u = v) : ∃ b : Bool, u = v ++ [b] := by
  have hs : ¬ u.length ≤ L + 1 := fun h => hv (by simpa [foodWordRight, h] using hp.symm)
  rw [foodWordRight, ite_eq_right hs] at hp
  have hu : u ≠ [] := fun h => by simp [h] at hs
  exact ⟨u.getLast hu, hp ▸ (List.dropLast_append_getLast hu).symm⟩

private theorem wordEdgeParent_fiber_card {L N : ℕ} (side : Bool) {v : List Bool} (hv : v ≠ []) :
    ((wordBasicVerts L N).filter fun u => wordEdgeParent L (u, side) = v).card ≤ 2 := by
  have hs : ((wordBasicVerts L N).filter fun u => wordEdgeParent L (u, side) = v) ⊆
      (Finset.univ : Finset Bool).image fun b => if side then v ++ [b] else b :: v := fun u hu => by
    have hp := (Finset.mem_filter.mp hu).2
    cases side
    · obtain ⟨b, hb⟩ := foodWordLeft_preimage hv hp; exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩
    · obtain ⟨b, hb⟩ := foodWordRight_preimage hv hp; exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by decide))

private def sourceShortSplit {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ) : ℕ :=
  if side then molLength x - k else k

private def sourceShortReaction {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  sourceSplitReaction x (sourceShortSplit x side k)
    (by cases side <;> simp [sourceShortSplit] <;> omega)
    (by cases side <;> simp [sourceShortSplit] <;> omega)

private abbrev WordShortKey (w : ℕ) := (List Bool × Bool) × Fin w

private def wordDetourLower (L : ℕ) {w : ℕ} (d : WordShortKey w) : Option (WordShortKey w) :=
  if d.2.val = 0 ∨ wordEdgeParent L d.1 = [] then none
  else some ((wordEdgeParent L d.1, d.1.2), ⟨d.2.val - 1, (Nat.sub_le _ _).trans_lt d.2.2⟩)

private noncomputable def wordDetourKeys (L : ℕ) {w : ℕ} (d : WordShortKey w) : Finset (WordShortKey w) :=
  {d} ∪ (wordDetourLower L d).toFinset

private theorem wordDetourLower_details {L w : ℕ} (d r : WordShortKey w)
    (h : wordDetourLower L d = some r) :
    wordEdgeParent L d.1 = r.1.1 ∧ d.1.2 = r.1.2 ∧ d.2.val = r.2.val + 1 ∧ r.1.1 ≠ [] := by
  unfold wordDetourLower at h; split_ifs at h with hz
  simp only [Option.some.injEq] at h; subst h; simp only [not_or] at hz
  exact ⟨rfl, rfl, by dsimp; omega, hz.2⟩

private noncomputable def wordShortSourceOption {L N w : ℕ} (hL : 2 * w ≤ L)
    (r : WordShortKey w) : Option (Reaction N) :=
  if hr : L < r.1.1.length ∧ r.1.1.length ≤ N then
    some (sourceShortReaction
      (sourceWordMolecule r.1.1 (by omega) hr.2)
      r.1.2 (r.2.val + 1) (Nat.succ_pos _) (by have := r.2.2; simp; omega))
  else none

private noncomputable def wordDetourSourceReactions {L N w : ℕ} (hL : 2 * w ≤ L)
    (d : WordShortKey w) : Finset (Reaction N) :=
  (wordDetourKeys L d).biUnion fun r => (wordShortSourceOption hL r).toFinset

private theorem wordDetourSourceReactions_card {L N w : ℕ} (hL : 2 * w ≤ L) (d : WordShortKey w) :
    (wordDetourSourceReactions (N := N) hL d).card ≤ 2 := by
  have hk : (wordDetourKeys L d).card ≤ 2 :=
    (Finset.card_union_le _ _).trans (by cases wordDetourLower L d <;> simp)
  exact Finset.card_biUnion_le.trans
    ((Finset.sum_le_sum (g := fun _ => 1) fun r _ => by cases wordShortSourceOption (N := N) hL r <;> simp).trans
      (by simpa using hk))

private theorem wordDetourSourceReactions_incidence {L N w : ℕ} (hL : 2 * w ≤ L) (a : Reaction N) :
    ((wordBasicEdges L N ×ˢ (Finset.univ : Finset (Fin w))).filter
      fun d => a ∈ wordDetourSourceReactions hL d).card ≤ 3 := by
  let U := wordBasicEdges L N ×ˢ (Finset.univ : Finset (Fin w))
  by_cases ha : ∃ r : WordShortKey w, wordShortSourceOption hL r = some a
  · obtain ⟨r, hr⟩ := ha
    have hinj {s : WordShortKey w} (hs : wordShortSourceOption hL s = some a) : s = r := by
      unfold wordShortSourceOption at hs hr
      split_ifs at hs with hsn; split_ifs at hr with hrn
      have he := (Option.some.inj hs).trans (Option.some.inj hr).symm
      have hp : s.1.1 = r.1.1 := by
        simpa [sourceShortReaction, sourceSplitReaction, reactionProduct] using congrArg (moleculeWord ∘ reactionProduct) he
      have hl := congrArg reactionLeftLength he
      have := s.2.2; have := r.2.2
      simp only [sourceShortReaction, sourceSplitReaction_leftLength, sourceShortSplit, sourceWordMolecule_length, hp] at hl
      rcases hs1 : s.1.2 <;> rcases hr1 : r.1.2 <;> simp [hs1, hr1] at hl
      · exact Prod.ext (Prod.ext hp (hs1.trans hr1.symm)) (Fin.ext (by omega))
      · omega
      · omega
      · exact Prod.ext (Prod.ext hp (hs1.trans hr1.symm)) (Fin.ext (by omega))
    have hrn : r.1.1 ≠ [] := by
      unfold wordShortSourceOption at hr; split_ifs at hr with h; exact List.length_pos_iff.mp (by omega)
    have hlow : (U.filter fun d => wordDetourLower L d = some r).card ≤ 2 :=
      (Finset.card_le_card_of_injOn (fun d : WordShortKey w => d.1.1)
        (t := (wordBasicVerts L N).filter fun u => wordEdgeParent L (u, r.1.2) = r.1.1)
        (fun d hd => by
          obtain ⟨hdU, hdl⟩ := Finset.mem_filter.mp hd
          obtain ⟨hp, hs, _, _⟩ := wordDetourLower_details d r hdl
          exact Finset.mem_filter.mpr ⟨mem_wordBasicVerts.mpr (.inr (mem_wordBasicEdges.mp (Finset.mem_product.mp hdU).1)),
            by simpa [← hs] using hp⟩)
        fun d hd e he hde => by
          obtain ⟨_, hs, hj, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
          obtain ⟨_, ht, hk, _⟩ := wordDetourLower_details e r (Finset.mem_filter.mp he).2
          exact Prod.ext (Prod.ext hde (hs.trans ht.symm)) (Fin.ext (by omega))).trans
        (wordEdgeParent_fiber_card r.1.2 hrn)
    have hsub : (U.filter fun d => a ∈ wordDetourSourceReactions hL d) ⊆
        insert r (U.filter fun d => wordDetourLower L d = some r) := fun d hd => by
      obtain ⟨hdU, hdR⟩ := Finset.mem_filter.mp hd
      obtain ⟨s, hs, hsa⟩ := Finset.mem_biUnion.mp hdR
      obtain rfl := hinj (Option.mem_toFinset.mp hsa)
      rcases Finset.mem_union.mp hs with h1 | h2
      · exact Finset.mem_insert.mpr (.inl (Finset.mem_singleton.mp h1).symm)
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hdU, Option.mem_toFinset.mp h2⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
  · rw [show (U.filter fun d => a ∈ wordDetourSourceReactions hL d) = ∅ from
      Finset.eq_empty_iff_forall_notMem.mpr fun d hd =>
        let ⟨r, _, hr⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
        ha ⟨r, Option.mem_toFinset.mp hr⟩]; simp

private def wordDropShort (s : List Bool) (side : Bool) (k : ℕ) : List Bool :=
  if side then s.take (s.length - k) else s.drop k

private def wordGenerated {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) (s : List Bool) : Prop :=
  ∀ x : Molecule N, moleculeWord x = s → x ∈ temporaryReactionClosure L S

private theorem wordGenerated_short {N L : ℕ} {S : Finset (Reaction N)} {s : List Bool}
    (hs : s.length ≤ L) : wordGenerated L S s :=
  fun x hx => temporaryReactionClosure_food S x (moleculeWord_length x ▸ hx ▸ hs)

private theorem wordGenerated_mol {N L : ℕ} {S : Finset (Reaction N)} (x : Molecule N) :
    wordGenerated L S (moleculeWord x) ↔ x ∈ temporaryReactionClosure L S :=
  ⟨fun h => h x rfl, fun hx _ hy => moleculeWord_injective hy ▸ hx⟩

private theorem wordShortSourceOption_gen {L N w : ℕ} (hL : 2 * w ≤ L) {S : Finset (Reaction N)}
    (r : WordShortKey w) (hr : L < r.1.1.length ∧ r.1.1.length ≤ N)
    (hmem : (wordShortSourceOption hL r).toFinset ⊆ S) :
    wordGenerated L S r.1.1 ↔ wordGenerated L S (wordDropShort r.1.1 r.1.2 (r.2.val + 1)) := by
  have hj := r.2.2
  let a := sourceShortReaction
    (sourceWordMolecule r.1.1 (by omega) hr.2)
    r.1.2 (r.2.val + 1) (Nat.succ_pos _) (by simp; omega)
  have haS : a ∈ S := hmem (Option.mem_toFinset.mpr (by unfold wordShortSourceOption; rw [dite_eq_left hr]; rfl))
  have hp : moleculeWord (reactionProduct a) = r.1.1 := by
    simp [a, sourceShortReaction, sourceSplitReaction, reactionProduct]
  nth_rw 1 [← hp]; rw [wordGenerated_mol]
  rcases r with ⟨⟨v, _ | _⟩, j⟩
  · have hfood : reactionLeft a ∈ temporaryReactionClosure L S :=
      temporaryReactionClosure_food S _ (by simp [a, sourceShortReaction, sourceShortSplit]; omega)
    have hrw : wordDropShort v false (j.val + 1) = moleculeWord (reactionRight a) := by
      simp [a, moleculeWord_reactionRight, sourceShortReaction, sourceSplitReaction,
        reactionProduct, reactionLeftLength, sourceShortSplit, wordDropShort]
    dsimp; rw [hrw, wordGenerated_mol]
    exact ⟨fun h => (temporaryReactionClosure_cleavage S a haS h).2,
      fun h => temporaryReactionClosure_ligation S a haS hfood h⟩
  · have hfood : reactionRight a ∈ temporaryReactionClosure L S :=
      temporaryReactionClosure_food S _ (by
        rw [← moleculeWord_length]; simp [a, moleculeWord_reactionRight, sourceShortReaction,
          sourceSplitReaction, reactionProduct, reactionLeftLength, sourceShortSplit]
        dsimp at hr hj; omega)
    have hrw : wordDropShort v true (j.val + 1) = moleculeWord (reactionLeft a) := by
      simp [a, moleculeWord_reactionLeft, sourceShortReaction, sourceSplitReaction,
        reactionProduct, reactionLeftLength, sourceShortSplit, wordDropShort]
      dsimp at hr hj; omega
    dsimp; rw [hrw, wordGenerated_mol]
    exact ⟨fun h => (temporaryReactionClosure_cleavage S a haS h).1,
      fun h => temporaryReactionClosure_ligation S a haS h hfood⟩

private def wordDiamondSlot (L : ℕ) (v : List Bool) : Fin 4 → List Bool × Bool :=
  ![(v, false), (v, true), (foodWordRight L v, false), (foodWordLeft L v, true)]

private def wordDiamondAdjacent (L N : ℕ) (e d : List Bool × Bool) : Prop :=
  ∃ v ∈ wordBasicVerts L N, ∃ i j, wordDiamondSlot L v i = e ∧ wordDiamondSlot L v j = d

private def wordContourReach (L N : ℕ) (C : Finset (List Bool × Bool)) :=
  Relation.EqvGen fun e d => e ∈ C ∧ d ∈ C ∧ wordDiamondAdjacent L N e d

private theorem wordBond_diamond_connected {L N : ℕ} (f : List Bool → Bool)
    (hmin : ∀ g : List Bool → Bool, (wordGraphCut L N g).Nonempty →
      wordGraphCut L N g ⊆ wordGraphCut L N f → wordGraphCut L N g = wordGraphCut L N f)
    (e d : List Bool × Bool) (he : e ∈ wordGraphCut L N f) (hd : d ∈ wordGraphCut L N f) :
    wordContourReach L N (wordGraphCut L N f) e d := by
  let F := (wordGraphCut L N f).filter fun a => wordContourReach L N (wordGraphCut L N f) e a
  have hsub : F ⊆ wordGraphCut L N f := Finset.filter_subset _ _
  let ind (H : Finset (List Bool × Bool)) (x : List Bool × Bool) : Bool := decide (x ∈ H)
  have hind (h : List Bool → Bool) {v : List Bool} (b : Bool) (hv : v ∈ wordBasicVerts L N) :
      ind (wordGraphCut L N h) (v, b) = (h v ^^ h (wordEdgeParent L (v, b))) := by
    rcases mem_wordBasicVerts.mp hv with rfl | hxE
    · have hp : wordEdgeParent L ([], b) = [] := by unfold wordEdgeParent; split <;> simp [foodWordLeft, foodWordRight]
      simp [ind, wordGraphCut, hp]
    · have hm : (v, b) ∈ wordBasicEdges L N := mem_wordBasicEdges.mpr hxE
      cases ha : h v <;> cases hb : h (wordEdgeParent L (v, b)) <;> simp [ind, wordGraphCut, hm, ha, hb]
  have hxor4 : ∀ a b c d : Bool, ((((a ^^ c) ^^ (a ^^ b)) ^^ (b ^^ d)) ^^ (c ^^ d)) = false := by decide
  have hparF (v : List Bool) (hv : v ∈ wordBasicVerts L N) :
      quadParity (fun i => ind F (wordDiamondSlot L v i)) = false := by
    refine quadParity_closed_subset _ (fun i => ind (wordGraphCut L N f) (wordDiamondSlot L v i))
      (fun i hi => decide_eq_true (hsub (of_decide_eq_true hi)))
      (fun i j hi hj => decide_eq_true <| by
        obtain ⟨hiC, hiR⟩ := Finset.mem_filter.mp (of_decide_eq_true hi)
        exact Finset.mem_filter.mpr ⟨of_decide_eq_true hj, .trans _ _ _ hiR (.rel _ _ ⟨hiC, of_decide_eq_true hj, v, hv, i, j, rfl, rfl⟩)⟩) ?_
    simp only [quadParity, wordDiamondSlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      hind f _ hv, hind f _ (foodWordRight_vert hv), hind f _ (foodWordLeft_vert hv),
      wordEdgeParent, Bool.false_eq_true, ite_false, ite_true, foodWordParents_commute]
    exact hxor4 _ _ _ _
  let g := diamondPotential (foodWordRight L) (fun v => ind F (v, true)) N
  have hg : wordGraphCut L N g = F := by
    have hFB : F ⊆ wordBasicEdges L N := hsub.trans (Finset.filter_subset _ _)
    have hr : ind F ([], false) = false ∧ ind F ([], true) = false := by
      constructor <;> exact decide_eq_false fun h => by have := mem_wordBasicEdges.mp (hFB h); simp at this
    ext x
    by_cases hxB : x ∈ wordBasicEdges L N
    · have hxv : x.1 ∈ wordBasicVerts L N := mem_wordBasicVerts.mpr (.inr (mem_wordBasicEdges.mp hxB))
      have hp := diamondPotential_edges (fun v => ind F (v, false)) (fun v => ind F (v, true)) hr hparF N
        x.1 hxv (by have := (mem_wordBasicEdges.mp hxB).2; omega)
      have hx : (g x.1 ^^ g (wordEdgeParent L x)) = ind F x := by rcases x with ⟨v, _ | _⟩ <;> [exact hp.1; exact hp.2]
      have hi := hind g x.2 hxv; rw [hx] at hi
      exact decide_eq_decide.mp hi
    · exact ⟨fun h => (hxB (Finset.mem_filter.mp h).1).elim, fun h => (hxB (hFB h)).elim⟩
  have hEq : F = wordGraphCut L N f := hg ▸ hmin g (hg ▸ ⟨e, Finset.mem_filter.mpr ⟨he, .refl e⟩⟩) (hg ▸ hsub)
  exact (Finset.mem_filter.mp (hEq.symm ▸ hd)).2

private noncomputable def edgeWalk {V : Type*} [DecidableEq V] (nbrs : V → Finset V) : ℕ → V → Finset (List V)
  | 0, r => {[r]}
  | k + 1, r => (nbrs r).biUnion fun x => (edgeWalk nbrs k x).image (r :: ·)

private theorem mem_edgeWalk_cons {V : Type*} [DecidableEq V] {nbrs : V → Finset V} {k : ℕ} {r x : V} {xs : List V}
    (hx : x ∈ nbrs r) (hxs : xs ∈ edgeWalk nbrs k x) : r :: xs ∈ edgeWalk nbrs (k + 1) r :=
  Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _ hxs⟩

private theorem edgeWalk_card {V : Type*} [DecidableEq V] (nbrs : V → Finset V) (d : ℕ) (hd : ∀ v, (nbrs v).card ≤ d) :
    ∀ k r, (edgeWalk nbrs k r).card ≤ d ^ k
  | 0, _ => by simp [edgeWalk]
  | k + 1, r => Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (g := fun _ => d ^ k) fun x _ =>
        Finset.card_image_le.trans (edgeWalk_card nbrs d hd k x)).trans
        (by simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]; rw [Nat.mul_comm (d ^ k)]
            exact Nat.mul_le_mul_right _ (hd r)))

private theorem edgeWalk_splice {V : Type*} [DecidableEq V] (nbrs : V → Finset V) : ∀ {k r p}, p ∈ edgeWalk nbrs k r →
    ∀ {u v}, u ∈ p → v ∈ nbrs u → u ∈ nbrs v →
    ∃ q ∈ edgeWalk nbrs (k + 2) r, q.toFinset = insert v p.toFinset
  | 0, r, p, hp, u, v, hu, hvu, huv => by
    obtain rfl := Finset.mem_singleton.mp hp; obtain rfl : u = r := by simpa using hu
    exact ⟨[u, v, u], mem_edgeWalk_cons hvu (mem_edgeWalk_cons huv (Finset.mem_singleton_self _)), by ext; simp [or_comm]⟩
  | k + 1, r, p, hp, u, v, hu, hvu, huv => by
    simp only [edgeWalk, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hp
    rcases List.mem_cons.mp hu with rfl | huxs
    · exact ⟨u :: v :: u :: xs, mem_edgeWalk_cons hvu (mem_edgeWalk_cons huv (mem_edgeWalk_cons hx hxs)), by ext; simp⟩
    · obtain ⟨ys, hys, hfin⟩ := edgeWalk_splice nbrs hxs huxs hvu huv
      exact ⟨r :: ys, mem_edgeWalk_cons hx hys, by ext; simp [List.toFinset_cons, hfin]; tauto⟩

private noncomputable def contourNbrs (L N : ℕ) (e : List Bool × Bool) : Finset (List Bool × Bool) :=
  if e ∈ wordBasicEdges L N then
    (((wordBasicVerts L N).filter fun v => ∃ i, wordDiamondSlot L v i = e).biUnion
      fun v => ((Finset.univ : Finset (Fin 4)).image (wordDiamondSlot L v)).erase e) ∩ wordBasicEdges L N
  else ∅

private theorem mem_contourNbrs {L N : ℕ} {e d : List Bool × Bool} :
    d ∈ contourNbrs L N e ↔ e ∈ wordBasicEdges L N ∧ d ∈ wordBasicEdges L N ∧ d ≠ e ∧ wordDiamondAdjacent L N e d := by
  unfold contourNbrs; split_ifs with he
  · simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_image, Finset.mem_univ, true_and, he, wordDiamondAdjacent]
    tauto
  · simp [he]

private theorem contourNbrs_card (L N : ℕ) (e : List Bool × Bool) : (contourNbrs L N e).card ≤ 9 := by
  unfold contourNbrs; split_ifs with he
  · have hn : e.1 ≠ [] := List.length_pos_iff.mp (by have := (mem_wordBasicEdges.mp he).1; omega)
    set inc := (wordBasicVerts L N).filter fun v => ∃ i, wordDiamondSlot L v i = e
    have hinc : inc.card ≤ 3 := by
      have hs : inc ⊆ insert e.1 ((wordBasicVerts L N).filter fun v => wordEdgeParent L (v, !e.2) = e.1) := fun v hv => by
        obtain ⟨hvV, i, hi⟩ := Finset.mem_filter.mp hv
        rcases e with ⟨u, _ | _⟩ <;> (fin_cases i <;> simp_all [wordDiamondSlot, wordEdgeParent])
      have := wordEdgeParent_fiber_card (L := L) (N := N) (!e.2) hn
      exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans (by omega))
    refine (Finset.card_le_card Finset.inter_subset_left).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum (g := fun _ => 3) fun v hv => ?_).trans (by simp only [Finset.sum_const, smul_eq_mul]; omega)
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
    rw [Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)]
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := wordDiamondSlot L v)
    simp at this; omega
  · simp

private theorem contour_cover_walk {L N : ℕ} (C : Finset (List Bool × Bool))
    (hsub : C ⊆ wordBasicEdges L N) (r : List Bool × Bool) (hr : r ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach L N C r d) :
    ∃ p ∈ edgeWalk (contourNbrs L N) (2 * (C.card - 1)) r, p.toFinset = C := by
  have hcross (S : Finset (List Bool × Bool)) (hs : S ⊆ C) (hrs : r ∈ S) (hne : S ≠ C) :
      ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ v ∈ contourNbrs L N u := by
    by_contra! h
    have cl (u v) (hu : u ∈ C) (hv : v ∈ C) (ha : wordDiamondAdjacent L N u v) (huS : u ∈ S) : v ∈ S := by
      by_contra hvS
      exact h u huS v hv hvS (mem_contourNbrs.mpr ⟨hsub hu, hsub hv, fun he => hvS (he ▸ huS), ha⟩)
    have inv (u v) (hp : wordContourReach L N C u v) : u ∈ S ↔ v ∈ S := by
      induction hp with
      | rel _ _ hrel => obtain ⟨hu, hv, w, hw, i, j, hi, hj⟩ := hrel; exact ⟨cl _ _ hu hv ⟨w, hw, i, j, hi, hj⟩, cl _ _ hv hu ⟨w, hw, j, i, hj, hi⟩⟩
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact hne (Finset.Subset.antisymm hs fun d hd => (inv r d (hconn d hd)).mp hrs)
  have extd (m : ℕ) : ∀ p, p ∈ edgeWalk (contourNbrs L N) (2 * (p.toFinset.card - 1)) r →
      p.toFinset ⊆ C → r ∈ p → C.card - p.toFinset.card = m →
      ∃ q ∈ edgeWalk (contourNbrs L N) (2 * (C.card - 1)) r, q.toFinset = C := by
    induction m with
    | zero =>
      intro p hp hsubP _ hm
      have he := Finset.eq_of_subset_of_card_le hsubP (by omega)
      exact ⟨p, he ▸ hp, he⟩
    | succ m ih =>
      intro p hp hsubP hrp hm
      obtain ⟨u, hu, v, hv, hvs, huv⟩ := hcross _ hsubP (List.mem_toFinset.mpr hrp)
        fun he => by rw [he, tsub_self] at hm; cases hm
      have hvu : u ∈ contourNbrs L N v := by
        obtain ⟨huB, hvB, hne, w, hw, i, j, hi, hj⟩ := mem_contourNbrs.mp huv
        exact mem_contourNbrs.mpr ⟨hvB, huB, hne.symm, w, hw, j, i, hj, hi⟩
      obtain ⟨q, hq, hqf⟩ := edgeWalk_splice _ hp (List.mem_toFinset.mp hu) huv hvu
      have hqsub : q.toFinset ⊆ C := by rw [hqf]; exact Finset.insert_subset hv hsubP
      have := Finset.card_pos.mpr ⟨r, List.mem_toFinset.mpr hrp⟩
      have hc : q.toFinset.card = p.toFinset.card + 1 := by rw [hqf, Finset.card_insert_of_notMem hvs]
      have := Finset.card_le_card hqsub
      exact ih q (by rwa [show 2 * (q.toFinset.card - 1) = 2 * (p.toFinset.card - 1) + 2 by omega])
        hqsub (List.mem_toFinset.mp (hqf ▸ Finset.mem_insert_of_mem (List.mem_toFinset.mpr hrp))) (by omega)
  exact extd _ [r] (by simp [edgeWalk]) (by simpa using hr) (by simp) rfl

private noncomputable def wordAnchoredContours (L N : ℕ) (r : List Bool × Bool) (b : ℕ) :=
  (wordBasicEdges L N).powerset.filter fun C => C.card = b ∧ r ∈ C ∧ ∀ d ∈ C, wordContourReach L N C r d

private theorem wordAnchoredContours_card (L N : ℕ) (r : List Bool × Bool) (b : ℕ) :
    (wordAnchoredContours L N r b).card ≤ 81 ^ (b - 1) := by
  have hs : wordAnchoredContours L N r b ⊆ (edgeWalk (contourNbrs L N) (2 * (b - 1)) r).image List.toFinset :=
    fun C hC => by
      obtain ⟨hpow, hb, hr, hc⟩ := Finset.mem_filter.mp hC
      obtain ⟨p, hp, hpf⟩ := contour_cover_walk C (Finset.mem_powerset.mp hpow) r hr hc
      exact Finset.mem_image.mpr ⟨p, hb ▸ hp, hpf⟩
  simpa [pow_mul] using (Finset.card_le_card hs).trans
    (Finset.card_image_le.trans (edgeWalk_card (contourNbrs L N) 9 (contourNbrs_card L N) _ r))

private theorem wordContour_product_locality {L N : ℕ} (C : Finset (List Bool × Bool))
    (hsub : C ⊆ wordBasicEdges L N) (e : List Bool × Bool) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach L N C e d) (d : List Bool × Bool) (hd : d ∈ C) :
    d.1 ∈ endWordBall (4 * (C.card - 1)) e.1 := by
  obtain ⟨p, hp, hpf⟩ := contour_cover_walk C hsub e he hconn
  have hslot (w : List Bool) (i : Fin 4) (hB : wordDiamondSlot L w i ∈ wordBasicEdges L N) :
      w ∈ endWordBall 1 (wordDiamondSlot L w i).1 := by
    refine mem_endWordBall_one ?_
    have hn : (wordDiamondSlot L w i).1 ≠ [] := List.length_pos_iff.mp (by have := (mem_wordBasicEdges.mp hB).1; omega)
    fin_cases i
    · simp [wordDiamondSlot]
    · simp [wordDiamondSlot]
    · obtain ⟨b, hb⟩ := foodWordRight_preimage (by simpa [wordDiamondSlot] using hn) rfl
      dsimp [wordDiamondSlot]; generalize foodWordRight L w = u at hb; subst hb; cases b <;> simp
    · obtain ⟨b, hb⟩ := foodWordLeft_preimage (by simpa [wordDiamondSlot] using hn) rfl
      dsimp [wordDiamondSlot]; generalize foodWordLeft L w = u at hb; subst hb; cases b <;> simp
  have hwalk (k : ℕ) : ∀ (u : List Bool × Bool) q, q ∈ edgeWalk (contourNbrs L N) k u →
      ∀ x ∈ q, x.1 ∈ endWordBall (2 * k) u.1 := by
    induction k with
    | zero =>
      intro u q hq x hx; obtain rfl := Finset.mem_singleton.mp hq; obtain rfl : x = u := by simpa using hx
      exact endWordBall_self 0 _
    | succ k ih =>
      intro u q hq x hx
      simp only [edgeWalk, Finset.mem_biUnion, Finset.mem_image] at hq
      obtain ⟨y, hy, ys, hys, rfl⟩ := hq
      rcases List.mem_cons.mp hx with rfl | hxy
      · exact endWordBall_self _ _
      · obtain ⟨huB, hyB, _, w, _, i, j, rfl, rfl⟩ := mem_contourNbrs.mp hy
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        exact endWordBall_trans (j := 2) (k := 2 * k)
          (endWordBall_trans (j := 1) (k := 1) (hslot w i huB) (endWordBall_symm (hslot w j hyB)))
          (ih _ ys hys x hxy)
  rw [show 4 * (C.card - 1) = 2 * (2 * (C.card - 1)) by omega]
  exact hwalk (2 * (C.card - 1)) e p hp d (List.mem_toFinset.mp (hpf.symm ▸ hd))

private theorem wordCut_core_avoiding_root {L N : ℕ} (f : List Bool → Bool) (core : List Bool)
    (hc : ∀ e ∈ wordGraphCut L N f, ∃ l r : List Bool, e.1 = l ++ core ++ r)
    {v : List Bool} (hvV : v ∈ wordBasicVerts L N) (hv : ¬ ∃ l r : List Bool, v = l ++ core ++ r) :
    f v = f [] := by
  suffices ∀ k u, u ∈ wordBasicVerts L N → u.length - L ≤ k →
      (¬ ∃ l r : List Bool, u = l ++ core ++ r) → f u = f [] from
    this N v hvV (by rcases mem_wordBasicVerts.mp hvV with rfl | ⟨_, hN⟩ <;> [simp; omega]) hv
  intro k; induction k with
  | zero => intro u hu hk _; exact (mem_wordBasicVerts.mp hu).resolve_right (by omega) ▸ rfl
  | succ k ih =>
    intro u hu hk hav
    rcases mem_wordBasicVerts.mp hu with rfl | huE
    · rfl
    · have heq : f u = f (foodWordRight L u) := by
        by_contra hne
        exact hav (hc (u, true) (Finset.mem_filter.mpr ⟨mem_wordBasicEdges.mpr huE, hne⟩))
      rw [heq]
      by_cases hp : foodWordRight L u = []
      · rw [hp]
      · exact ih _ (foodWordRight_vert hu) (by have := foodWordRight_len L u; omega)
          fun ⟨l, r, hpar⟩ => by
            obtain ⟨b, hb⟩ := foodWordRight_preimage hp rfl
            exact hav ⟨l, r ++ [b], by rw [hb, hpar, List.append_assoc]⟩

private theorem highBand_label_constant {A : Type*} (g : List Bool → A) (M N : ℕ) (hMN : M < N)
    (hparent : ∀ s : List Bool, M < s.length → s.length ≤ N → g s = g s.tail ∧ g s = g s.dropLast)
    (u v : List Bool) (hu : M ≤ u.length ∧ u.length ≤ N) (hv : M ≤ v.length ∧ v.length ≤ N) : g u = g v := by
  have hshift (a b : Bool) (t : List Bool) (ht : t.length + 1 = M) : g (a :: t) = g (t ++ [b]) := by
    have h := hparent ((a :: t) ++ [b]) (by simp; omega) (by simp; omega)
    simp only [List.dropLast_concat] at h; simpa using h.2.symm.trans h.1
  have rot (front : List Bool) : ∀ (middle suffix : List Bool), front.length = suffix.length → front.length + middle.length = M →
      g (front ++ middle) = g (middle ++ suffix) := by
    induction front with
    | nil => intro _ suffix hs _; cases suffix <;> simp_all
    | cons a front ih =>
      intro middle suffix hs ht
      cases suffix with
      | nil => simp at hs
      | cons b suffix =>
        have h1 := hshift a b (front ++ middle) (by simp at *; omega)
        have h2 := ih (middle ++ [b]) suffix (Nat.succ.inj hs) (by simp at *; omega)
        rw [List.append_assoc] at h1; simpa [List.append_assoc] using h1.trans h2
  let base := List.replicate M false
  have desc (n : ℕ) : ∀ s : List Bool, s.length = n → M ≤ n → n ≤ N → g s = g base := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hlo hhi; by_cases he : n = M
      · simpa using rot s [] base (by simp [base, hs, he]) (by simpa [he] using hs)
      · exact (hparent s (by omega) (by omega)).2.trans
          (ih s.dropLast.length (by simp; omega) s.dropLast rfl (by simp; omega) (by simp; omega))
  exact (desc _ u rfl hu.1 hu.2).trans (desc _ v rfl hv.1 hv.2).symm

private theorem wordCut_above_boundary_parents {L N M : ℕ} (f : List Bool → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut L N f, e.1.length ≤ M)
    (s : List Bool) (hs : M < s.length) (hN : s.length ≤ N) :
    f s = f s.tail ∧ f s = f s.dropLast := by
  have heq (b : Bool) : f s = f (wordEdgeParent L (s, b)) := by
    by_contra h
    exact (hcut (s, b) (Finset.mem_filter.mpr ⟨mem_wordBasicEdges.mpr ⟨by dsimp; omega, hN⟩, h⟩)).not_gt hs
  have hlong : ¬ s.length ≤ L + 1 := by omega
  exact ⟨by simpa [wordEdgeParent, foodWordLeft, hlong] using heq false,
    by simpa [wordEdgeParent, foodWordRight, hlong] using heq true⟩

private theorem wordCut_nonfood_length_le {L N M : ℕ} (f : List Bool → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut L N f, e.1.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut L N f, ∃ l r : List Bool, e.1 = l ++ core ++ r)
    {u : List Bool} (hN : u.length ≤ N) (hu : f u ≠ f []) : u.length ≤ M := by
  by_contra h
  cases core with
  | nil => exact hne rfl
  | cons a t =>
    let v := List.replicate M (!a)
    have hav : ¬ ∃ l r : List Bool, v = l ++ (a :: t) ++ r := fun ⟨l, r, he⟩ => by
      have hm : a ∈ v := by rw [he]; simp
      cases a <;> simp [v] at hm
    have hconst := highBand_label_constant f M N (by omega)
      (wordCut_above_boundary_parents f hLM hcut) u v ⟨by omega, hN⟩ ⟨by simp [v], by simp [v]; omega⟩
    exact hu (hconst.trans (wordCut_core_avoiding_root f _ hcore
      (mem_wordBasicVerts.mpr (.inr ⟨by simp [v]; omega, by simp [v]; omega⟩)) hav))

private def molecularWordVertex (L : ℕ) (s : List Bool) : List Bool :=
  if L < s.length then s else []

private noncomputable def wordMolecularSide (L N : ℕ) (f : List Bool → Bool) (c : Bool) :=
  (actualBinaryWords N).filter fun s => f (molecularWordVertex L s) = c

private noncomputable def wordMoleculeContourEnvelope (L N : ℕ) (s : List Bool) (b : ℕ) :=
  ((wordBasicEdges L N).filter fun e => e.1 ∈ endWordBall (64 * b) s).biUnion fun e => wordAnchoredContours L N e b

private theorem wordMoleculeContourEnvelope_card (L N : ℕ) (s : List Bool) (b : ℕ) (hb : 0 < b) :
    (wordMoleculeContourEnvelope L N s b).card ≤ molecularContourConstant ^ b := by
  let anchors := (wordBasicEdges L N).filter fun e => e.1 ∈ endWordBall (64 * b) s
  have hanc : anchors.card ≤ 2 * 7 ^ (64 * b) := by
    have hc : anchors.card ≤ ((endWordBall (64 * b) s) ×ˢ (Finset.univ : Finset Bool)).card :=
      Finset.card_le_card fun e he => Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2, Finset.mem_univ _⟩
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc
    have := endWordBall_card (64 * b) s; omega
  have hraw : (wordMoleculeContourEnvelope L N s b).card ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) :=
    Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 81 ^ (b - 1))
      fun e _ => wordAnchoredContours_card L N e b).trans
      (by simp only [Finset.sum_const, nsmul_eq_mul]; exact Nat.mul_le_mul_right _ hanc))
  calc
    _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := hraw
    _ ≤ 2 ^ b * 7 ^ (64 * b) * 81 ^ b :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 2) hb))
        (pow_le_pow_right₀ (by decide) (Nat.sub_le b 1))
    _ = molecularContourConstant ^ b := by simp only [molecularContourConstant, mul_pow, pow_mul]

private theorem wordBond_mem_molecule_envelope {L N : ℕ} (f : List Bool → Bool)
    (hmin : ∀ g : List Bool → Bool, (wordGraphCut L N g).Nonempty →
      wordGraphCut L N g ⊆ wordGraphCut L N f → wordGraphCut L N g = wordGraphCut L N f)
    (hn : (wordGraphCut L N f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide L N f c).card ≤ (actualBinaryWords N \ wordMolecularSide L N f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide L N f c) :
    wordGraphCut L N f ∈ wordMoleculeContourEnvelope L N s (wordGraphCut L N f).card := by
  obtain ⟨e, he⟩ := hn
  let b := (wordGraphCut L N f).card
  have hb : 0 < b := Finset.card_pos.mpr ⟨e, he⟩
  have hsub : wordGraphCut L N f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
  have hconn (d) (hd : d ∈ wordGraphCut L N f) := wordBond_diamond_connected f hmin e d he hd
  obtain ⟨heL, heN⟩ := mem_wordBasicEdges.mp (hsub he)
  obtain ⟨hsU, hslabel⟩ := Finset.mem_filter.mp hs
  have hsN := ((mem_actualBinaryWords s N).mp hsU).2
  have htriv := endWordBall_common_core s e.1 [] ⟨[], s, by simp⟩ ⟨[], e.1, by simp⟩
  have hball : e.1 ∈ endWordBall (64 * b) s := by
    by_cases hshort : e.1.length ≤ 8 * b
    · let M := e.1.length + 4 * b
      have hcut (d) (hd : d ∈ wordGraphCut L N f) : d.1.length ≤ M := by
        have := endWordBall_length (wordContour_product_locality _ hsub e he hconn d hd); dsimp [M, b]; omega
      have hsM : s.length ≤ M := by
        by_cases hMN : M < N
        · refine (molecular_minor_side_below_band N M hMN (wordMolecularSide L N f c) (Finset.filter_subset _ _) hminor (fun u hu v hv hMu hMv => ?_) s hs).le
          have heq := highBand_label_constant f M N hMN (wordCut_above_boundary_parents f (by dsimp [M]; omega) hcut)
            u v ⟨hMu, ((mem_actualBinaryWords u N).mp hu).2⟩ ⟨hMv, ((mem_actualBinaryWords v N).mp hv).2⟩
          have huL : L < u.length := by dsimp [M] at hMu; omega
          have hvL : L < v.length := by dsimp [M] at hMv; omega
          rw [wordMolecularSide, Finset.mem_filter, Finset.mem_filter, molecularWordVertex, molecularWordVertex,
            ite_eq_left huL, ite_eq_left hvL, heq]
          exact ⟨fun h => ⟨hv, h.2⟩, fun h => ⟨hu, h.2⟩⟩
        · omega
      exact endWordBall_mono (by simp [M] at hsM ⊢; omega) htriv
    · let r := 4 * b
      let left := e.1.take r
      let core := (e.1.drop r).take (e.1.length - 2 * r)
      let right := (e.1.drop r).drop (e.1.length - 2 * r)
      have ha : e.1 = left ++ core ++ right := by simp [left, core, right, List.append_assoc, List.take_append_drop]
      have hclen : core.length = e.1.length - 2 * r := by simp [core]; omega
      have hcne : core ≠ [] := fun hc0 => by simp [hc0] at hclen; omega
      have hcore (d) (hd : d ∈ wordGraphCut L N f) : ∃ a1 b1, d.1 = a1 ++ core ++ b1 :=
        endWordBall_protects_core (wordContour_product_locality _ hsub e he hconn d hd) ha
          (by simp [left, r]; omega) (by simp [right, r]; omega)
      have hcut (d) (hd : d ∈ wordGraphCut L N f) : d.1.length ≤ e.1.length + r := by
        have := endWordBall_length (wordContour_product_locality _ hsub e he hconn d hd); dsimp [r, b]; omega
      have hLM : L < e.1.length + r := by omega
      have lift {t : List Bool} (htU : t ∈ actualBinaryWords N) (htne : f (molecularWordVertex L t) ≠ f []) :
          (∃ a1 b1, t = a1 ++ core ++ b1) ∧ t.length ≤ e.1.length + r := by
        have htN := ((mem_actualBinaryWords t N).mp htU).2
        have htL : L < t.length := by by_contra h; exact htne (by simp [molecularWordVertex, h])
        have hu : f t ≠ f [] := by simpa [molecularWordVertex, htL] using htne
        exact ⟨by by_contra hav; exact hu (wordCut_core_avoiding_root f core hcore (mem_wordBasicVerts.mpr (.inr ⟨htL, htN⟩)) hav),
          wordCut_nonfood_length_le f hLM hcut core hcne hcore htN hu⟩
      by_cases hc : c = f []
      · subst hc
        have hnflt : (actualBinaryWords N \ wordMolecularSide L N f (f [])).card < 2 ^ (2 * (3 * r + 1)) :=
          core_containing_words_card_lt _ core (3 * r)
            (fun t ht => (lift (Finset.mem_sdiff.mp ht).1 fun he => (Finset.mem_sdiff.mp ht).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ht).1, he⟩)).1)
            (fun t ht => (lift (Finset.mem_sdiff.mp ht).1 fun he => (Finset.mem_sdiff.mp ht).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ht).1, he⟩)).2.trans (by omega))
        have hp := (Finset.card_sdiff_add_card_eq_card (s := wordMolecularSide L N f (f [])) (Finset.filter_subset _ _)).trans (actualBinaryWords_card N)
        have hNle : N ≤ 2 * (3 * r + 1) := (pow_le_pow_iff_right₀ one_lt_two).mp (show 2 ^ N ≤ 2 ^ (2 * (3 * r + 1)) by rw [pow_succ] at hp; omega)
        exact endWordBall_mono (by simp [r] at hNle ⊢; omega) htriv
      · obtain ⟨huc, hul⟩ := lift hsU (hslabel ▸ hc)
        exact endWordBall_mono (by dsimp [r] at *; omega) (endWordBall_common_core s e.1 core huc ⟨left, right, ha⟩)
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨hsub he, hball⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, rfl, he, hconn⟩⟩

private theorem exists_disjoint_detours {ι R : Type*} [DecidableEq R] (S : Finset ι) (support : ι → Finset R)
    (hsize : ∀ i ∈ S, (support i).card ≤ 2)
    (huse : ∀ r, (S.filter fun j => r ∈ support j).card ≤ 3) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) ∧ S.card ≤ 5 * T.card := by
  let fam := S.powerset.filter fun T => decide (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) = true
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image fam Finset.card ⟨∅, by simp [fam]⟩
  obtain ⟨hTS, hdisB⟩ := Finset.mem_filter.mp hT
  have hsub := Finset.mem_powerset.mp hTS
  have hdis := of_decide_eq_true hdisB
  let conf (j : ι) := (S.erase j).filter fun i => ¬ Disjoint (support j) (support i)
  have hconf (j : ι) (hj : j ∈ S) : (conf j).card ≤ 4 := by
    have hs : conf j ⊆ (support j).biUnion fun r => (S.filter fun i => r ∈ support i).erase j := fun i hi => by
      obtain ⟨hiS, hnd⟩ := Finset.mem_filter.mp hi
      obtain ⟨r, hrj, hri⟩ := Finset.not_disjoint_iff.mp hnd
      exact Finset.mem_biUnion.mpr ⟨r, hrj, Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hiS).1, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hiS).2, hri⟩⟩⟩
    refine (Finset.card_le_card hs).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_sum (g := fun _ => 2) fun r hr => ?_).trans (by have := hsize j hj; simp; omega)
    have hm : j ∈ S.filter fun i => r ∈ support i := Finset.mem_filter.mpr ⟨hj, hr⟩
    have := Finset.card_erase_add_one hm; have := huse r; omega
  have hcov : S ⊆ T.biUnion fun j => insert j (conf j) := fun i hi => by
    by_cases hiT : i ∈ T
    · exact Finset.mem_biUnion.mpr ⟨i, hiT, Finset.mem_insert_self _ _⟩
    · have hex : ∃ j ∈ T, ¬ Disjoint (support i) (support j) := by
        by_contra! hn
        have hnew : insert i T ∈ fam := Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), decide_eq_true fun j hj k hk hne => by
            rcases Finset.mem_insert.mp hj with rfl | hjT <;> rcases Finset.mem_insert.mp hk with rfl | hkT
            · exact (hne rfl).elim
            · exact hn k hkT
            · exact (hn j hjT).symm
            · exact hdis j hjT k hkT hne⟩
        have hc := hmax (insert i T) hnew; rw [Finset.card_insert_of_notMem hiT] at hc; omega
      obtain ⟨j, hj, hij⟩ := hex
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨fun he => hiT (he ▸ hj), hi⟩, fun h => hij h.symm⟩)⟩
  refine ⟨T, hsub, hdis, (Finset.card_le_card hcov).trans (Finset.card_biUnion_le.trans ?_)⟩
  exact (Finset.sum_le_sum (g := fun _ => 5) fun j hj =>
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (hconf j (hsub hj)))).trans_eq (by simp [Nat.mul_comm])

private theorem disjoint_supports_failure_le {ι R : Type*} [DecidableEq R] (a : I)
    (S : ι → Finset R) (U : Finset ι)
    (hdis : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → Disjoint (S i) (S j))
    (hsz : ∀ i ∈ U, (S i).card ≤ 2) :
    Measure.infinitePi (fun _ : R => ambientCoordLaw a) {ω | ∀ i ∈ U, ¬ ∀ r ∈ S i, ω r} ≤
      (1 - (toNNReal a : ENNReal) ^ 2) ^ U.card := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    have hiU : Disjoint (U.biUnion S) (S i) := (Finset.disjoint_biUnion_left _ _ _).2 fun j hj =>
      hdis j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _) fun he => hi (he ▸ hj)
    let E : Set (R → Prop) := {ω | ∀ j ∈ U, ¬ ∀ r ∈ S j, ω r}
    rw [show {ω : R → Prop | ∀ j ∈ insert i U, ¬ ∀ r ∈ S j, ω r} = E ∩ {ω | ¬ ∀ r ∈ S i, ω r} by ext; simp [E, and_comm],
      iid_prefix_failure_measure a (U.biUnion S) (S i) hiU E fun _ _ he =>
        forall₂_congr fun j hj => not_congr <| forall₂_congr fun r hr => by rw [he r (Finset.mem_biUnion.mpr ⟨j, hj, hr⟩)],
      Finset.card_insert_of_notMem hi, pow_succ]
    exact mul_le_mul' (ih (fun j hj d hd => hdis j (Finset.mem_insert_of_mem hj) d (Finset.mem_insert_of_mem hd))
      fun j hj => hsz j (Finset.mem_insert_of_mem hj))
      (tsub_le_tsub_left (pow_le_pow_of_le_one zero_le (by exact_mod_cast a.2.2) (hsz i (Finset.mem_insert_self _ _))) 1)

private def contourDetoursFailed {L N w : ℕ} (hL : 2 * w ≤ L)
    (C : Finset (List Bool × Bool)) (ω : Reaction N → Prop) : Prop :=
  ∀ d ∈ C ×ˢ (Finset.univ : Finset (Fin w)), ¬ ∀ r ∈ wordDetourSourceReactions hL d, ω r

private theorem staticReaction_contour_failure {L N w k : ℕ} (hL : 2 * w ≤ L)
    (hk : 5 * k ≤ w) {C : Finset (List Bool × Bool)} (hC : C ⊆ wordBasicEdges L N) (a : I) :
    staticReactionMeasure N a {ω | contourDetoursFailed hL C ω} ≤
      ((1 - (toNNReal a : ENNReal) ^ 2) ^ k) ^ C.card := by
  obtain ⟨T, hT, hd, hc⟩ := exists_disjoint_detours (C ×ˢ (Finset.univ : Finset (Fin w)))
    (wordDetourSourceReactions (L := L) (N := N) hL) (fun d _ => wordDetourSourceReactions_card hL d) fun r =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.product_subset_product_left hC))).trans
        (wordDetourSourceReactions_incidence hL r)
  have hkt : k * C.card ≤ T.card := by
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
    have := Nat.mul_le_mul_right C.card hk; nlinarith
  exact ((measure_mono (s := {ω | contourDetoursFailed hL C ω}) fun _ h d hdT => h d (hT hdT)).trans
    (disjoint_supports_failure_le a _ T hd fun d _ => wordDetourSourceReactions_card hL d)).trans
    ((pow_le_pow_of_le_one zero_le tsub_le_self hkt).trans_eq (pow_mul _ _ _))

private def moleculeContourBad {L N w : ℕ} (hL : 2 * w ≤ L) (s : List Bool) (ω : Reaction N → Prop) : Prop :=
  ∃ j : ℕ, ∃ C ∈ wordMoleculeContourEnvelope L N s (j + 1), contourDetoursFailed hL C ω

private theorem measure_moleculeContourBad_le {L N w k : ℕ} (hL : 2 * w ≤ L)
    (hk : 5 * k ≤ w) (s : List Bool) (a : I) :
    staticReactionMeasure N a {ω | moleculeContourBad hL s ω} ≤
      contourBudget a k / (1 - contourBudget a k) := by
  have hsz (b : ℕ) (hb : 0 < b) :
      staticReactionMeasure N a {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s b, contourDetoursFailed hL C ω} ≤
        (contourBudget a k) ^ b := by
    let E := wordMoleculeContourEnvelope L N s b
    rw [show {ω : Reaction N → Prop | ∃ C ∈ E, contourDetoursFailed hL C ω} =
        ⋃ C ∈ E, {ω | contourDetoursFailed hL C ω} by ext; simp]
    calc
      _ ≤ ∑ C ∈ E, staticReactionMeasure N a {ω | contourDetoursFailed hL C ω} := measure_biUnion_finset_le E _
      _ ≤ ∑ _C ∈ E, ((1 - (toNNReal a : ENNReal) ^ 2) ^ k) ^ b := Finset.sum_le_sum fun C hC => by
          obtain ⟨_, _, he⟩ := Finset.mem_biUnion.mp hC
          obtain ⟨hpw, hcb, _⟩ := Finset.mem_filter.mp he
          simpa [hcb] using staticReaction_contour_failure hL hk (Finset.mem_powerset.mp hpw) a
      _ = (E.card : ENNReal) * ((1 - (toNNReal a : ENNReal) ^ 2) ^ k) ^ b := by simp
      _ ≤ (molecularContourConstant : ENNReal) ^ b * ((1 - (toNNReal a : ENNReal) ^ 2) ^ k) ^ b := by
          gcongr; exact_mod_cast wordMoleculeContourEnvelope_card L N s b hb
      _ = (contourBudget a k) ^ b := by rw [contourBudget, mul_pow]
  rw [show {ω | moleculeContourBad hL s ω} =
      ⋃ j : ℕ, {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s (j + 1), contourDetoursFailed hL C ω} by
      ext; simp [moleculeContourBad]]
  exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun j => hsz (j + 1) (Nat.succ_pos _)).trans_eq
    (by rw [ENNReal.tsum_geometric_add_one, div_eq_mul_inv]))

private noncomputable def wordEffectiveEdges {L N w : ℕ} (hL : 2 * w ≤ L)
    (ω : Reaction N → Prop) : Finset (List Bool × Bool) :=
  (wordBasicEdges L N).filter fun e => ∃ j : Fin w, ∀ a ∈ wordDetourSourceReactions hL (e, j), ω a

private theorem outside_moleculeContourBad_connected {L N w : ℕ} (hL : 2 * w ≤ L)
    (ω : Reaction N → Prop) {s t : List Bool}
    (hs : s ∈ actualBinaryWords N) (ht : t ∈ actualBinaryWords N)
    (hsg : ¬ moleculeContourBad hL s ω) (htg : ¬ moleculeContourBad hL t ω) :
    wordEdgeReach L (wordEffectiveEdges hL ω) (molecularWordVertex L s) (molecularWordVertex L t) := by
  by_contra hn
  have hmv {u : List Bool} (hu : u ∈ actualBinaryWords N) : molecularWordVertex L u ∈ wordBasicVerts L N := by
    have := ((mem_actualBinaryWords u N).mp hu).2
    by_cases h : L < u.length <;> simp [molecularWordVertex, h, this]
  obtain ⟨f, hneq, hcut, hne, hmin⟩ := wordGraph_disabled_bond (wordEffectiveEdges hL ω) (hmv hs) (hmv ht) hn
  have hfail : contourDetoursFailed hL (wordGraphCut L N f) ω := fun d hd hopen => by
    obtain ⟨hb, hnE⟩ := Finset.mem_sdiff.mp (hcut (Finset.mem_product.mp hd).1)
    exact hnE (Finset.mem_filter.mpr ⟨hb, d.2, hopen⟩)
  have hbad {u c} (hu : u ∈ wordMolecularSide L N f c) (hng : ¬ moleculeContourBad hL u ω) :
      (actualBinaryWords N \ wordMolecularSide L N f c).card < (wordMolecularSide L N f c).card := by
    by_contra hle
    have hb := Finset.card_pos.mpr hne
    exact hng ⟨(wordGraphCut L N f).card - 1, wordGraphCut L N f,
      (Nat.sub_add_cancel hb).symm ▸ wordBond_mem_molecule_envelope f hmin hne c (Nat.le_of_not_lt hle) u hu, hfail⟩
  have hcomp (c d : Bool) (hcd : c ≠ d) : actualBinaryWords N \ wordMolecularSide L N f c = wordMolecularSide L N f d := by
    ext u; cases c <;> cases d <;> cases hu : f (molecularWordVertex L u) <;> simp_all [wordMolecularSide]
  have hs1 := hbad (Finset.mem_filter.mpr ⟨hs, rfl⟩) hsg
  have ht1 := hbad (Finset.mem_filter.mpr ⟨ht, rfl⟩) htg
  rw [hcomp _ _ hneq] at hs1; rw [hcomp _ _ hneq.symm] at ht1; omega

private abbrev ActualBinaryWord (N : ℕ) := ↥(actualBinaryWords N)

private noncomputable def rootedMolecularWords {L N w : ℕ} (hL : 2 * w ≤ L)
    (ω : Reaction N → Prop) : Finset (ActualBinaryWord N) :=
  Finset.univ.filter fun s => wordEdgeReach L (wordEffectiveEdges hL ω) [] (molecularWordVertex L s.1)

private theorem rootedMolecularWords_card_le_closure {L N w : ℕ} (hL : 2 * w ≤ L)
    (ω : Reaction N → Prop) :
    (rootedMolecularWords hL ω).card ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card := by
  let S := staticOpenReactions ω
  have hlen_drop (s side k) : (wordDropShort s side k).length = s.length - k := by cases side <;> simp [wordDropShort]
  have hstep (e : List Bool × Bool) (he : e ∈ wordEffectiveEdges hL ω) :
      wordGenerated L S e.1 ↔ wordGenerated L S (wordEdgeParent L e) := by
    obtain ⟨hb, j, hj⟩ := Finset.mem_filter.mp he
    have heB := mem_wordBasicEdges.mp hb
    have hmem (r) (hr : r ∈ wordDetourKeys L (e, j)) : (wordShortSourceOption hL r).toFinset ⊆ S :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj a (Finset.mem_biUnion.mpr ⟨r, hr, ha⟩)⟩
    have hup := wordShortSourceOption_gen hL (e, j) heB (hmem _ (by simp [wordDetourKeys]))
    have hpar_eq (hlong : ¬ e.1.length ≤ L + 1) : wordEdgeParent L e = wordDropShort e.1 e.2 1 := by
      rcases e with ⟨v, _ | _⟩ <;> simp [wordEdgeParent, foodWordLeft, foodWordRight, wordDropShort, List.dropLast_eq_take, hlong]
    by_cases hle : e.1.length ≤ L + 1
    · have hp0 : wordEdgeParent L e = [] := by
        rcases e with ⟨v, _ | _⟩ <;> simp [wordEdgeParent, foodWordLeft, foodWordRight, hle]
      exact hup.trans ⟨fun _ => wordGenerated_short (by simp [hp0]),
        fun _ => wordGenerated_short (by dsimp; rw [hlen_drop]; omega)⟩
    · by_cases hj0 : j.val = 0
      · simpa [hj0, hpar_eq hle] using hup
      · have hpB : L < (wordEdgeParent L e).length ∧ (wordEdgeParent L e).length ≤ N := by
          rw [hpar_eq hle, hlen_drop]; omega
        have hp : wordEdgeParent L e ≠ [] := List.length_pos_iff.mp (by omega)
        let r : WordShortKey w := ((wordEdgeParent L e, e.2), ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.2⟩)
        have hlow := wordShortSourceOption_gen hL r hpB (hmem r (by simp [wordDetourKeys, wordDetourLower, hj0, hp, r]))
        have hcomp : wordDropShort (wordEdgeParent L e) e.2 (r.2.val + 1) = wordDropShort e.1 e.2 (j.val + 1) := by
          rw [show r.2.val + 1 = j.val by dsimp [r]; omega, hpar_eq hle]
          cases e.2 <;> simp [wordDropShort, List.take_take]
          omega
        exact hup.trans (hcomp ▸ hlow.symm)
  have hreach {u v : List Bool} (h : wordEdgeReach L (wordEffectiveEdges hL ω) u v) :
      wordGenerated L S u ↔ wordGenerated L S v := by
    induction h with
    | rel _ _ h => obtain ⟨e, he, rfl, rfl⟩ := h; exact hstep e he
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  let src (s : ActualBinaryWord N) : Molecule N :=
    sourceWordMolecule s.1 (List.length_pos_iff.mpr ((mem_actualBinaryWords s.1 N).mp s.2).1)
      ((mem_actualBinaryWords s.1 N).mp s.2).2
  refine Finset.card_le_card_of_injOn src (fun s hs => ?_)
    fun s _ t _ h => Subtype.ext (by simpa [src] using congrArg moleculeWord h)
  have hg := (hreach (Finset.mem_filter.mp hs).2).mp (wordGenerated_short (by simp))
  by_cases hsL : s.1.length ≤ L
  · exact temporaryReactionClosure_food S _ (by simpa [src] using hsL)
  · have hm : molecularWordVertex L s.1 = s.1 := by simp [molecularWordVertex, not_le.mp hsL]
    exact (hm ▸ hg) (src s) (by simp [src])

private theorem measure_pool_deficit_le {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [DecidableEq X]
    (μ : Measure Ω) (bad pool : Ω → Finset X) (root : X)
    (hcover : ∀ ω, root ∉ bad ω → ∀ x, x ∉ bad ω → x ∈ pool ω)
    (δ : ENNReal) (hbad : ∀ x, μ {ω | x ∈ bad ω} ≤ δ) (d : ℕ) (hd : 0 < d) :
    μ {ω | (pool ω).card + d ≤ Fintype.card X} ≤ δ + (Fintype.card X : ENNReal) * δ / d := by
  have hsub : {ω | (pool ω).card + d ≤ Fintype.card X} ⊆ {ω | root ∈ bad ω} ∪ {ω | d ≤ (bad ω).card} :=
    fun ω (hω : _ + d ≤ _) => by
      by_cases hr : root ∈ bad ω
      · exact .inl hr
      · have huniv : bad ω ∪ pool ω = Finset.univ := Finset.eq_univ_of_forall fun x => by
          by_cases hx : x ∈ bad ω <;> [exact Finset.mem_union_left _ hx; exact Finset.mem_union_right _ (hcover ω hr x hx)]
        have hcu : Fintype.card X ≤ (bad ω).card + (pool ω).card := by
          rw [← Finset.card_univ, ← huniv]; exact Finset.card_union_le _ _
        exact .inr (by change d ≤ _; omega)
  have hlint : (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) ≤ Fintype.card X * δ := by
    have he (ω : Ω) : ((bad ω).card : ENNReal) = ∑ x : X, Set.indicator {ω | x ∈ bad ω} 1 ω := by
      simp [Set.indicator_apply]
    simp_rw [he]; rw [lintegral_finsetSum Finset.univ fun _ _ => measurable_of_finite _]
    refine (Finset.sum_le_sum (g := fun _ => δ) fun x _ => ?_).trans_eq (by simp)
    rw [lintegral_indicator_one (Set.toFinite _).measurableSet]; exact hbad x
  have hm := meas_ge_le_lintegral_div (μ := μ) (f := fun ω => ((bad ω).card : ENNReal))
    (measurable_of_finite _).aemeasurable (ε := (d : ENNReal)) (by exact_mod_cast hd.ne') (by simp)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (hbad root)
    ((by simpa only [Nat.cast_le] using hm : μ {ω | d ≤ (bad ω).card} ≤ _).trans (ENNReal.div_le_div_right hlint _))))

theorem measure_temporaryClosure_deficit {L N w k : ℕ} (hL : 2 * w ≤ L)
    (hk : 5 * k ≤ w) (hfood : 0 < L) (hN : 0 < N) (a : I) (d : ℕ) (hd : 0 < d) :
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card + d ≤ Fintype.card (Molecule N)} ≤
      contourBudget a k / (1 - contourBudget a k) +
      (Fintype.card (Molecule N) : ENNReal) * (contourBudget a k / (1 - contourBudget a k)) / d := by
  let root : ActualBinaryWord N := ⟨[false], (mem_actualBinaryWords [false] N).mpr ⟨by simp, by simpa using Nat.succ_le_of_lt hN⟩⟩
  rw [card_molecules_exact, ← actualBinaryWords_card, ← Fintype.card_coe]
  refine (measure_mono fun ω (hω : _ + d ≤ _) => Nat.add_le_add_right (rootedMolecularWords_card_le_closure hL ω) d |>.trans hω).trans ?_
  exact measure_pool_deficit_le (staticReactionMeasure N a)
    (fun ω => Finset.univ.filter fun s : ActualBinaryWord N => moleculeContourBad hL s.1 ω)
    (rootedMolecularWords hL) root
    (fun ω hr s hs => by
      have hp := outside_moleculeContourBad_connected hL ω root.2 s.2 (by simpa using hr) (by simpa using hs)
      rw [show molecularWordVertex L root.1 = [] by
        simp [molecularWordVertex, root, not_lt.mpr (Nat.succ_le_of_lt hfood)]] at hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    _ (fun s => by simpa using measure_moleculeContourBad_le hL hk s.1 a) d hd

open RAF RAFEmergenceApprox.Generic

theorem static_decreasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Antitone P) :
    staticReactionMeasure N c {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N a {ω | P (staticOpenReactions ω)} := by
  simp only [staticReactionMeasure, Measure.infinitePi_eq_pi]
  exact product_decreasing_mono (fun _ => a) (fun _ => c) (fun _ => hac) _
    fun x y hxy => hP fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy r (Finset.mem_filter.mp hr).2⟩

def lawToSample {n : ℕ} (ω : Reaction n → Molecule n → Prop) : CatalysisSample n :=
  ({z | ω z.2.val z.1}, {z | ω z.2.val z.1})

private theorem colLaw_to_setBernoulli {X J : Type*} [Fintype X] [Fintype J] (p : I) :
    (Measure.pi fun _ : J => colLaw X p).map (fun ω => {z : X × J | ω z.2 z.1}) =
      setBernoulli (Set.univ : Set (X × J)) p := by
  have hswap : (Measure.pi fun _ : J => colLaw X p).map (fun ω (z : X × J) => ω z.2 z.1) =
      Measure.infinitePi fun _ : X × J => ambientCoordLaw p := by
    rw [Measure.infinitePi_eq_pi]
    refine Measure.ext_of_singleton fun v => ?_
    rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton v),
      show (fun ω : J → X → Prop => fun z : X × J => ω z.2 z.1) ⁻¹' {v} = {fun j x => v (x, j)} by
        ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
        exact ⟨fun h j x => h (x, j), fun h ⟨x, j⟩ => h j x⟩,
      pi_singleton, pi_singleton]
    simp_rw [colLaw, pi_singleton]
    rw [← Finset.univ_product_univ, Finset.prod_product_right]
  rw [show (fun ω : J → X → Prop => {z : X × J | ω z.2 z.1}) =
      (fun v : X × J → Prop => {z | v z}) ∘ (fun ω z => ω z.2 z.1) from rfl,
    ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hswap, setBernoulli_eq_map]
  simp [ambientCoordLaw, bernoulliMeasure_def]

theorem lawToSample_map (n : ℕ) (lambda : ℝ) :
    (law (X := Molecule n) fun _ : Reaction n => catalysisP n lambda).map lawToSample =
      uniformCatalysisMeasure n lambda := by
  let p := catalysisP n lambda
  let μ : Reaction n → Measure (Molecule n → Prop) := fun _ => colLaw (Molecule n) p
  have hmp := (measurePreserving_piEquivPiSubtypeProd μ (RevSeedReaction (binaryPolymerCRS n 2))).map_eq
  have hcomp : lawToSample = (Prod.map (fun ω : PolymerSeedReaction n 2 → Molecule n → Prop => {z : SeedCoord n | ω z.2 z.1})
      (fun ω : NonseedReaction n → Molecule n → Prop => {z : NonseedCoord n | ω z.2 z.1})) ∘
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ => Molecule n → Prop) (RevSeedReaction (binaryPolymerCRS n 2)) := by
    ext ω <;> rfl
  rw [law, hcomp, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hmp,
    ← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _),
    colLaw_to_setBernoulli, colLaw_to_setBernoulli, uniformCatalysisMeasure]

theorem uniform_raf_eq_law (n : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) =
      law (X := Molecule n) (fun _ : Reaction n => catalysisP n lambda) (crsRAFEvent (binaryPolymerCRS n 2)) := by
  rw [← lawToSample_map n lambda, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  have hc (ω : Reaction n → Molecule n → Prop) : catalysisOf (lawToSample ω) = fun x r => ω r x := by
    funext x r; by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;> simp [catalysisOf, lawToSample, h]
  simp only [Set.preimage, HasRAFEvent, crsRAFEvent, Set.mem_ofPred_eq, hc]

theorem canonical_raf_ge_near_full_static (n m : ℕ) (lambda : ℝ) (hm : 0 < m)
    (q : I) (hk : 6 < nearFullPoolSize n m)
    (hq : q ≤ fixedPoolParameter (catalysisP n lambda) (nearFullPoolSize n m)) :
    staticReactionMeasure n q {ω | (m - 1) * Fintype.card (Molecule n) ≤
      m * (temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
        uniformCatalysisMeasure n lambda (HasRAFEvent n) := by
  rw [uniform_raf_eq_law, staticReactionMeasure, Measure.infinitePi_eq_pi]
  exact crs_near_full_lower (binaryPolymerCRS n 2) rfl (catalysisP n lambda) q hm hk hq

end HordijkSteelThreshold
