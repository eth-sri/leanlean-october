module

public import Chazelle.Golf

public import Chazelle.Core.FuseDegGen

/-!
# The degree of the revised fusion, part 2: keys, offsets and faced regions (general models)

* `sideInArc_compl`, `off_same_side`, `off_sep`: cyclic intervals of keys read through offsets
  from a base key.
* `ncard_biUnion_le_mul`, `ncard_attKeys_le`: counting keys of attachments.
* `arc_start_of_faced`, `arc_end_of_faced`, `arc_end_of_faced_zero`, `faced_before_zero`: a region
  faced just after (before) a cut position has an arc starting (ending) there.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn)
open Chazelle.Geometry (lerp)
open WalkEmbed

namespace FuseDeg

variable {M : Model}

/-! ## Cyclic intervals and offsets -/

/-- Away from its ends, a key is in exactly one of the two cyclic intervals between them. -/
theorem sideInArc_compl {a b x : ℝ} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    sideInArc a b x ↔ ¬ sideInArc b a x := by
  unfold sideInArc
  rcases lt_or_gt_of_ne hab with h | h
  · Ξ ite_eq_left h, ite_eq_right (not_lt.2 h.le)
    constructor
    · rintro ⟨h1, h2⟩ (h3 | h3) <;> linarith
    · intro h3
      push Not at h3
      exact ⟨lt_of_le_of_ne h3.2 (Ne.symm hxa), lt_of_le_of_ne h3.1 hxb⟩
  · Ξ ite_eq_right (not_lt.2 h.le), ite_eq_left h
    constructor
    · rintro (h1 | h1) ⟨h2, h3⟩ <;> linarith
    · intro h3
      Ξ' not_and_or at h3
      push Not at h3
      rcases h3 with h3 | h3
      · right; exact lt_of_le_of_ne h3 hxb
      · left; exact lt_of_le_of_ne h3 (Ne.symm hxa)

/-- **Two keys with no end of `(A, B)` between them are on the same side.** -/
theorem off_same_side {n g A B x y : ℝ} (hg : 0 ≤ g) (hgn : g < n) (hA : 0 ≤ A) (hAn : A < n)
    (hB : 0 ≤ B) (hBn : B < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hAB : A ≠ B) (hxy : off n g x ≤ off n g y)
    (hA' : off n g A < off n g x ∨ off n g y < off n g A)
    (hB' : off n g B < off n g x ∨ off n g y < off n g B) :
    sideInArc A B x ↔ sideInArc A B y := by
  have hne : off n g A ≠ off n g B := fun h => hAB (off_inj hg hgn hA hAn hB hBn h)
  have hxA : x ≠ A := by rintro rfl; rcases hA' with h | h <;> linarith
  have hxB : x ≠ B := by rintro rfl; rcases hB' with h | h <;> linarith
  have hyA : y ≠ A := by rintro rfl; rcases hA' with h | h <;> linarith
  have hyB : y ≠ B := by rintro rfl; rcases hB' with h | h <;> linarith
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sideInArc_iff_off hg hgn hA hAn hB hBn hx hxn h,
      sideInArc_iff_off hg hgn hA hAn hB hBn hy hyn h]
    rcases hA' with h1 | h1 <;> rcases hB' with h2 | h2 <;> constructor <;>
      rintro ⟨h3, h4⟩ <;> first | (constructor <;> linarith)
  · rw [sideInArc_compl hAB hxA hxB, sideInArc_compl hAB hyA hyB,
      sideInArc_iff_off hg hgn hB hBn hA hAn hx hxn h,
      sideInArc_iff_off hg hgn hB hBn hA hAn hy hyn h]
    rcases hA' with h1 | h1 <;> rcases hB' with h2 | h2 <;> constructor <;>
      intro h3 h4 <;> apply h3 <;> obtain ⟨h5, h6⟩ := h4 <;>
      first | (constructor <;> linarith)

/-- **Two keys with both ends of `(A, B)` between them are on the same side.** -/
theorem off_same_side_in {n g A B x y : ℝ} (hg : 0 ≤ g) (hgn : g < n) (hA : 0 ≤ A) (hAn : A < n)
    (hB : 0 ≤ B) (hBn : B < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hAB : A ≠ B) (hA' : off n g x < off n g A ∧ off n g A < off n g y)
    (hB' : off n g x < off n g B ∧ off n g B < off n g y) :
    sideInArc A B x ↔ sideInArc A B y := by
  have hne : off n g A ≠ off n g B := fun h => hAB (off_inj hg hgn hA hAn hB hBn h)
  have hxA : x ≠ A := by rintro rfl; linarith [hA'.1]
  have hxB : x ≠ B := by rintro rfl; linarith [hB'.1]
  have hyA : y ≠ A := by rintro rfl; linarith [hA'.2]
  have hyB : y ≠ B := by rintro rfl; linarith [hB'.2]
  obtain ⟨h1, h2⟩ := hA'
  obtain ⟨h3, h4⟩ := hB'
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sideInArc_iff_off hg hgn hA hAn hB hBn hx hxn h,
      sideInArc_iff_off hg hgn hA hAn hB hBn hy hyn h]
    constructor <;> rintro ⟨h5, h6⟩ <;> exfalso <;> linarith
  · rw [sideInArc_compl hAB hxA hxB, sideInArc_compl hAB hyA hyB,
      sideInArc_iff_off hg hgn hB hBn hA hAn hx hxn h,
      sideInArc_iff_off hg hgn hB hBn hA hAn hy hyn h]
    constructor <;> intro _ ⟨h5, h6⟩ <;> linarith

/-- **A chord with one end between two keys and the other outside separates them.** -/
theorem off_sep {n g A B x y : ℝ} (hg : 0 ≤ g) (hgn : g < n) (hA : 0 ≤ A) (hAn : A < n)
    (hB : 0 ≤ B) (hBn : B < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hA' : off n g x < off n g A ∧ off n g A < off n g y)
    (hB' : off n g B < off n g x ∨ off n g y < off n g B) :
    sideInArc A B x ↔ ¬ sideInArc A B y := by
  have hAB : A ≠ B := by rintro rfl; rcases hB' with h | h <;> linarith [hA'.1, hA'.2]
  have hne : off n g A ≠ off n g B := fun h => hAB (off_inj hg hgn hA hAn hB hBn h)
  have hxA : x ≠ A := by rintro rfl; linarith [hA'.1]
  have hxB : x ≠ B := by rintro rfl; rcases hB' with h | h <;> linarith [hA'.1, hA'.2]
  have hyA : y ≠ A := by rintro rfl; linarith [hA'.2]
  have hyB : y ≠ B := by rintro rfl; rcases hB' with h | h <;> linarith [hA'.1, hA'.2]
  obtain ⟨h1, h2⟩ := hA'
  rcases lt_or_gt_of_ne hne with h | h
  · rw [sideInArc_iff_off hg hgn hA hAn hB hBn hx hxn h,
      sideInArc_iff_off hg hgn hA hAn hB hBn hy hyn h]
    rcases hB' with h3 | h3
    · exfalso; linarith
    · constructor
      · rintro ⟨h4, -⟩; linarith
      · intro h4; exfalso; exact h4 ⟨h2, h3⟩
  · rw [sideInArc_compl hAB hxA hxB, sideInArc_compl hAB hyA hyB,
      sideInArc_iff_off hg hgn hB hBn hA hAn hx hxn h,
      sideInArc_iff_off hg hgn hB hBn hA hAn hy hyn h]
    rcases hB' with h3 | h3
    · constructor
      · intro h4; exfalso; exact h4 ⟨h3, h1⟩
      · intro h4; exfalso; apply h4; intro ⟨h5, h6⟩; linarith
    · exfalso; linarith

/-! ## Counting keys -/

/-- A finite union of sets of at most `k` elements has at most `k` times as many elements as
there are sets. -/
theorem ncard_biUnion_le_mul {ι α : Type*} {T : Set ι} (hT : T.Finite) (s : ι → Set α) {k : ℕ}
    (hs : ∀ i ∈ T, (s i).ncard ≤ k) : (⋃ i ∈ T, s i).ncard ≤ k * T.ncard := by
  classical
  have e : (⋃ i ∈ T, s i) = ⋃ i ∈ hT.toFinset, s i := by
    ext x; ϴ Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop
  Ξ e, Set.ncard_eq_toFinset_card T hT
  refine (Chazelle.Chain.ncard_biUnion_finset_le _ _).trans ?_
  calc ∑ i ∈ hT.toFinset, (s i).ncard ≤ ∑ _i ∈ hT.toFinset, k :=
        Finset.sum_le_sum fun i hi => hs i (hT.mem_toFinset.1 hi)
    _ = k * hT.toFinset.card := Ρ Finset.sum_const, smul_eq_mul, mul_comm

/-- The keys at which a set is attached. -/
def attKeys (M : Model) (c : Set Point) : Set ℝ :=
  {x | ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ x = p + t}

/-- **An admissible chord is attached at at most two keys** (one at each endpoint). -/
theorem ncard_attKeys_le (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    (attKeys M c).ncard ≤ 2 := by
  classical
  obtain ⟨a, b, hab, hce, -, hop, -, -⟩ := hM.ends c hc
  let f : ℝ → Point := fun x => sidePt M.W ⌊x⌋₊ (x - ⌊x⌋₊)
  have hkey : ∀ (p : ℕ) (t : ℝ), 0 ≤ t → t < 1 → f (p + t) = sidePt M.W p t := by
    intro p t ht ht1
    have hfl : ⌊(p : ℝ) + t⌋₊ = p := by
      rw [Nat.floor_eq_iff (⟢)]; constructor <;> linarith
    simp only [f, hfl]; congr 1; ring
  have hmaps : MapsTo f (attKeys M c) {a, b} := by
    rintro x ⟨p, t, hA, rfl⟩
    Ξ hkey p t hA.2.1 hA.2.2.1
    have hq := hA.2.2.2.1
    Ξ' hce at hq
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hq
    have hnD := hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · exact absurd (hs ▸ hop s ⟨h0, h1⟩) hnD
      · right; rw [hs, h1, Geometry.lerp_one]; rfl
    · left; Ξ hs, ← h0, Geometry.lerp_zero
  have hinj : InjOn f (attKeys M c) := by
    rintro x ⟨p, t, hA, rfl⟩ y ⟨p', t', hA', rfl⟩ hxy
    Ξ' hkey p t hA.2.1 hA.2.2.1, hkey p' t' hA'.2.1 hA'.2.2.1 at hxy
    obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hA hA' hxy
    rfl
  calc (attKeys M c).ncard ≤ ({a, b} : Set Point).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj
    _ ≤ 2 := (Set.ncard_insert_le a {b}).trans (Ρ Set.ncard_singleton)

/-- The keys at which the chords of a finite admissible set `T` are attached: at most `2 |T|`. -/
theorem ncard_attKeys_union_le (hM : WalkAx M) {T : Set (Set Point)} (hT : T ⊆ M.Adm)
    (hfin : T.Finite) : (⋃ c ∈ T, attKeys M c).ncard ≤ 2 * T.ncard :=
  ncard_biUnion_le_mul hfin _ fun _c hc => ncard_attKeys_le hM (hT hc)

/-! ## Arcs at cut positions -/

/-- The positions just before a walk vertex face the region of an arc ending there. -/
theorem faced_before_zero {F : Set (Set Point)} {V : Set Point} {l : ℝ} {p : ℕ}
    (hp : p < M.W.n) (harcV : M.IsArc F V l (p + 0)) (hVne : l ≠ (p : ℝ) + 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) V := by
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · have hl0 : 0 ≤ l := harcV.1
    have hln := harcV.2.1
    have hl0' : 0 < l := lt_of_le_of_ne hl0 (fun h => hVne (by rw [← h, h0]; simp))
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (M.W.n - l) from
      lt_min one_pos (⟡))] with s hs hs'
    have hs0 : (0 : ℝ) < s := hs
    have hs1 : s < 1 := hs'.2.trans_le (min_le_left _ _)
    have hs2 : s < M.W.n - l := hs'.2.trans_le (min_le_right _ _)
    have e : (0 + M.W.n - 1) % M.W.n = M.W.n - 1 := by
      rw [Nat.mod_eq_of_lt (show 0 + M.W.n - 1 < M.W.n by omega)]; omega
    Ξ h0, e
    refine harcV.2.2.2.2.2.2 _ _ (⋄) (⟡) (⟡) ?_
    have hc : ((M.W.n - 1 : ℕ) : ℝ) = M.W.n - 1 := by rw [Nat.cast_sub (⋄)]; simp
    Ξ hc, h0
    unfold sideInArc
    Ξ ite_eq_right (by push_cast; linarith)
    left; linarith
  · filter_upwards [eventually_before_end hVne, Ioo_mem_nhdsGT one_pos] with s h1 h2
    have e : (p + M.W.n - 1) % M.W.n = p - 1 := by
      rw [show p + M.W.n - 1 = p - 1 + M.W.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (⋄)]
    Ξ e
    refine harcV.2.2.2.2.2.2 _ _ (⋄) (by linarith [h2.2]) (by linarith [h2.1]) ?_
    have hc : ((p - 1 : ℕ) : ℝ) = p - 1 := by rw [Nat.cast_sub (⋄)]; simp
    Ξ hc, show (p : ℝ) - 1 + (1 - s) = p + 0 - s by ring
    exact h1

/-- **A region faced just after a cut position has an arc starting there.** -/
theorem arc_start_of_faced (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    {U : Set Point} (hU : U ∈ M.regions F) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p (t + s) U) :
    ∃ r, M.IsArc F U (p + t) r := by
  obtain ⟨U₀, -, -, r, hU₀, -, -, harc, -, -⟩ := hM.attach_face hF hfin hc hA
  have h₀ := faced_after hA.1 hA.2.1 hA.2.2.1 harc (WalkAx.arc_cuts ⟨c, hc⟩ harc).2.2
  obtain ⟨s, h1, h2⟩ := (h₀.and hf).exists
  exact ⟨r, (WalkAx.faces_unique hU₀ hU h1 h2) ▸ harc⟩

/-- **A region faced just before a cut position inside a walk edge has an arc ending there.** -/
theorem arc_end_of_faced (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (ht : 0 < t) {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p (t - s) U) : ∃ l, M.IsArc F U l (p + t) := by
  obtain ⟨-, V₀, l, -, -, hV₀, -, -, harc, -⟩ := hM.attach_face hF hfin hc hA
  have h₀ := faced_before hA.1 ht hA.2.2.1 harc (WalkAx.arc_cuts ⟨c, hc⟩ harc).2.2
  obtain ⟨s, h1, h2⟩ := (h₀.and hf).exists
  exact ⟨l, (WalkAx.faces_unique hV₀ hU h1 h2) ▸ harc⟩

/-- **A region faced just before a cut walk vertex has an arc ending there.** -/
theorem arc_end_of_faced_zero (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) U) :
    ∃ l, M.IsArc F U l (p + 0) := by
  obtain ⟨-, V₀, l, -, -, hV₀, -, -, harc, -⟩ := hM.attach_face hF hfin hc hA
  have h₀ := faced_before_zero hA.1 harc (WalkAx.arc_cuts ⟨c, hc⟩ harc).2.2
  obtain ⟨s, h1, h2⟩ := (h₀.and hf).exists
  exact ⟨l, (WalkAx.faces_unique hV₀ hU h1 h2) ▸ harc⟩


/-! ## Non-cut keys near a key -/

/-- The keys just after a key are not cuts. -/
theorem eventually_not_cut_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F (x + s) := by
  have hK := hM.finite_cuts hF hfin
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x + s ≠ y)).2 fun y _ => by
      rcases le_or_gt y x with hy | hy
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have : (0 : ℝ) < s := hs
        intro h; linarith
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y - x by linarith)] with s hs
        intro h; linarith [hs.2]
  filter_upwards [h] with s hs hcut
  exact hs _ hcut rfl

/-- The keys just before a key are not cuts. -/
theorem eventually_not_cut_before (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F (x - s) := by
  have hK := hM.finite_cuts hF hfin
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x - s ≠ y)).2 fun y _ => by
      rcases le_or_gt x y with hy | hy
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have : (0 : ℝ) < s := hs
        intro h; linarith
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - y by linarith)] with s hs
        intro h; linarith [hs.2]
  filter_upwards [h] with s hs hcut
  exact hs _ hcut rfl


/-- **Faced positions next to an adjacency**: if a region has an arc starting (ending) at the
position of offset `d + t` from the walk vertex `g`, then non-cut positions faced by it exist at
offsets just above (below) `d + t`. -/
theorem adj_near (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hne : F.Nonempty) {g : ℕ} {R : Set Point} {d : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdt : 0 < (d : ℝ) + t) (hadj : Adj M F R ((g + d) % M.W.n) t) :
    (∀ b : ℝ, (d : ℝ) + t < b → ∃ (d₁ : ℕ) (t₁ : ℝ), d₁ ≤ d ∧ t₁ ∈ Ioo (0 : ℝ) 1 ∧
      (d : ℝ) + t < d₁ + t₁ ∧ (d₁ : ℝ) + t₁ < b ∧
      ¬ M.IsCut F (((g + d₁) % M.W.n : ℕ) + t₁) ∧ M.Faces ((g + d₁) % M.W.n) t₁ R) ∨
    (∀ a : ℝ, a < (d : ℝ) + t → ∃ (d₁ : ℕ) (t₁ : ℝ), d₁ ≤ d ∧ t₁ ∈ Ioo (0 : ℝ) 1 ∧
      a < d₁ + t₁ ∧ (d₁ : ℝ) + t₁ < d + t ∧
      ¬ M.IsCut F (((g + d₁) % M.W.n : ℕ) + t₁) ∧ M.Faces ((g + d₁) % M.W.n) t₁ R) := by
  have hn : 0 < M.W.n := by
    rcases hadj with ⟨r, h⟩ | ⟨l, h⟩
    · have := h.2.1; exact_mod_cast (h.1.trans_lt this)
    · have := h.2.2.2.1; exact_mod_cast (h.2.2.1.trans_lt this)
  set p := (g + d) % M.W.n with hp
  rcases hadj with ⟨r, harc⟩ | ⟨l, harc⟩
  · left
    intro b hb
    have h1 := faced_after (Nat.mod_lt _ hn) ht0 ht1 harc (WalkAx.arc_cuts hne harc).2.2
    obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := (((h1.and (eventually_not_cut_after hM hF hfin
      ((p : ℝ) + t))).and self_mem_nhdsWithin).and (Ioo_mem_nhdsGT (show (0 : ℝ) <
        min (1 - t) (b - (d + t)) from lt_min (⟡) (⟡)))).exists
    have hs0 := hs3
    have hs5 : s < 1 - t := hs4.2.trans_le (min_le_left _ _)
    have hs6 : s < b - (d + t) := hs4.2.trans_le (min_le_right _ _)
    refine ⟨d, t + s, le_rfl, ⟨⟡, ⟡⟩, ⟡, ⟡, ?_, hs1⟩
    rw [← add_assoc]; exact hs2
  · right
    intro a ha
    rcases ht0.lt_or_eq with ht0' | ht0'
    · have h1 := faced_before (Nat.mod_lt _ hn) ht0' ht1 harc (WalkAx.arc_cuts hne harc).2.2
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := (((h1.and (eventually_not_cut_before hM hF hfin
        ((p : ℝ) + t))).and self_mem_nhdsWithin).and (Ioo_mem_nhdsGT (show (0 : ℝ) <
          min t ((d + t) - a) from lt_min ht0' (⟡)))).exists
      have hs0 := hs3
      have hs5 : s < t := hs4.2.trans_le (min_le_left _ _)
      have hs6 : s < (d + t) - a := hs4.2.trans_le (min_le_right _ _)
      refine ⟨d, t - s, le_rfl, ⟨⟡, ⟡⟩, ⟡, ⟡, ?_, hs1⟩
      rw [show (p : ℝ) + (t - s) = p + t - s by ring]; exact hs2
    · subst ht0'
      have hd1 : 1 ≤ d := by
        have : (0 : ℝ) < d := ⟡
        exact_mod_cast this
      have h1 := faced_before_zero (Nat.mod_lt _ hn) harc (WalkAx.arc_cuts hne harc).2.2
      have hpm : (p + M.W.n - 1) % M.W.n = (g + (d - 1)) % M.W.n := mod_pred_mod hn g hd1
      Ξ' hpm at h1
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := (((h1.and (eventually_not_cut_before hM hF hfin
        ((((g + (d - 1)) % M.W.n : ℕ) : ℝ) + 1))).and self_mem_nhdsWithin).and
        (Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 ((d + 0) - a) from
          lt_min one_pos (⟡)))).exists
      have hs0 := hs3
      have hs5 : s < 1 := hs4.2.trans_le (min_le_left _ _)
      have hs6 : s < (d + 0) - a := hs4.2.trans_le (min_le_right _ _)
      have hc : ((d - 1 : ℕ) : ℝ) = d - 1 := by rw [Nat.cast_sub hd1]; simp
      refine ⟨d - 1, 1 - s, ⋄, ⟨⟡, ⟡⟩, by rw [hc]; linarith,
        by rw [hc]; linarith, ?_, hs1⟩
      rw [show (((g + (d - 1)) % M.W.n : ℕ) : ℝ) + (1 - s) =
        (((g + (d - 1)) % M.W.n : ℕ) : ℝ) + 1 - s by ring]
      exact hs2


/-- The exit chords of `R` attached at an offset in `(0, L)` from `g` next to which `R` is faced,
and whose other attachment is outside the stretch (the *crossing* chords of a piece). -/
def CrossX (M : Model) (F : Set (Set Point)) (R : Set Point) (g L : ℕ) : Set (Set Point) :=
  {f | f ∈ exits M F R ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧
    SideAttach M.W f ((g + d) % M.W.n) t ∧ Adj M F R ((g + d) % M.W.n) t ∧
    ∃ (pb : ℕ) (tb : ℝ), SideAttach M.W f pb tb ∧
      sidePt M.W pb tb ≠ sidePt M.W ((g + d) % M.W.n) t ∧
      (off M.W.n g (pb + tb) = 0 ∨ (L : ℝ) ≤ off M.W.n g (pb + tb))}

/-- The chords attached at the position of offset `o` from `g` (with vertex offset `< L`): at most
two. -/
theorem ncard_at_off_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (g L : ℕ) (o : ℝ) :
    {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ o = d + t ∧
      SideAttach M.W f ((g + d) % M.W.n) t}.ncard ≤ 2 := by
  by_cases h : ∃ (d : ℕ) (t : ℝ), 0 ≤ t ∧ t < 1 ∧ o = d + t
  · obtain ⟨d₀, t₀, ht₀, ht₀1, ho⟩ := h
    refine le_trans (Set.ncard_le_ncard ?_ (hfin.subset fun f hf => hf.1))
      (ncard_at_le hM hF hfin ((g + d₀) % M.W.n) t₀)
    rintro f ⟨hf, d, t, -, ht, ht1, ho', hA⟩
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj ht ht1 ht₀ ht₀1 (ho'.symm.trans ho)
    exact ⟨hf, hA⟩
  · have : {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ o = d + t ∧
        SideAttach M.W f ((g + d) % M.W.n) t} = ∅ := by
      ext f
      ϴ Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists
      intro _ d t _ ht ht1 ho _
      exact h ⟨d, t, ht, ht1, ho⟩
    rw [this, Set.ncard_empty]; omega

/-- **At most four crossing chords per piece**: the positions of crossing chords next to which
`R` is faced are at most two (the first and the last of `R`'s positions in the stretch), by the
separation of the walk by a chord. -/
theorem crossX_ncard_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {g L : ℕ} (hg : g < M.W.n) (hLn : L < M.W.n) {R : Set Point} (hR : R ∈ M.regions F) :
    (CrossX M F R g L).ncard ≤ 4 := by
  set n := M.W.n with hn_def
  have hn : 0 < n := ⋄
  have hgR : (g : ℝ) < n := by exact_mod_cast hg
  set O : Set ℝ := {o | ∃ f ∈ exits M F R, ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
    0 < (d : ℝ) + t ∧ SideAttach M.W f ((g + d) % n) t ∧ Adj M F R ((g + d) % n) t ∧
    (∃ (pb : ℕ) (tb : ℝ), SideAttach M.W f pb tb ∧
      sidePt M.W pb tb ≠ sidePt M.W ((g + d) % n) t ∧
      (off n g (pb + tb) = 0 ∨ (L : ℝ) ≤ off n g (pb + tb))) ∧ o = d + t} with hO
  have hkey : ∀ {p : ℕ}, p < n → ∀ {t : ℝ}, 0 ≤ t → t < 1 →
      0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n := by
    intro p hp t ht ht1
    have : (p : ℝ) + 1 ≤ n := by exact_mod_cast hp
    exact ⟨⟢, ⟡⟩
  have hLR : ∀ {d : ℕ} {t : ℝ}, d < L → t < 1 → (d : ℝ) + t < L := fun {d t} hd ht => by
    have : (d : ℝ) + 1 ≤ L := by exact_mod_cast hd
    linarith
  -- no three positions
  have hno3 : ∀ x ∈ O, ∀ y ∈ O, ∀ z ∈ O, x < y → y < z → False := by
    rintro _ ⟨f₁, hf₁, d₁, t₁, hd₁, ht₁, ht₁1, hdt₁, hA₁, hadj₁, -, rfl⟩
      _ ⟨f₂, hf₂, d₂, t₂, hd₂, ht₂, ht₂1, hdt₂, hA₂, hadj₂, ⟨pb, tb, hB, hBne, hBo⟩, rfl⟩
      _ ⟨f₃, hf₃, d₃, t₃, hd₃, ht₃, ht₃1, hdt₃, hA₃, hadj₃, -, rfl⟩ h12 h23
    have hne : F.Nonempty := ⟨f₁, hf₁.1⟩
    -- the separation by `f₂` of two faced positions on its two sides
    have hsep : ∀ {dx dy : ℕ} {tx ty : ℝ}, dx < n → dy < n → tx ∈ Ioo (0 : ℝ) 1 →
        ty ∈ Ioo (0 : ℝ) 1 → 0 < (dx : ℝ) + tx → (dx : ℝ) + tx < d₂ + t₂ →
        (d₂ : ℝ) + t₂ < dy + ty → (dy : ℝ) + ty < L →
        ¬ M.IsCut F (((g + dx) % n : ℕ) + tx) → M.Faces ((g + dx) % n) tx R →
        ¬ M.IsCut F (((g + dy) % n : ℕ) + ty) → M.Faces ((g + dy) % n) ty R → False := by
      intro dx dy tx ty hdx hdy htx hty h0 h1 h2 h3 hcx hfx hcy hfy
      have hox : off n g (((g + dx) % n : ℕ) + tx) = dx + tx := off_key hg hdx htx.1.le htx.2
      have hoy : off n g (((g + dy) % n : ℕ) + ty) = dy + ty := off_key hg hdy hty.1.le hty.2
      have hoA : off n g (((g + d₂) % n : ℕ) + t₂) = d₂ + t₂ :=
        off_key hg (⋄) ht₂ ht₂1
      have hKx := hkey (Nat.mod_lt (g + dx) hn) htx.1.le htx.2
      have hKy := hkey (Nat.mod_lt (g + dy) hn) hty.1.le hty.2
      have hKA := hkey (Nat.mod_lt (g + d₂) hn) ht₂ ht₂1
      have hKB := hkey hB.1 hB.2.1 hB.2.2.1
      have hs : M.Separates f₂ (((g + dx) % n : ℕ) + tx) (((g + dy) % n : ℕ) + ty) := by
        refine ⟨(g + d₂) % n, pb, t₂, tb, hA₂, hB, Ne.symm hBne, ?_⟩
        refine off_sep (Nat.cast_nonneg g) hgR hKA.1 hKA.2 hKB.1 hKB.2 hKx.1 hKx.2 hKy.1 hKy.2
          ⟨by rw [hox, hoA]; exact h1, by rw [hoy, hoA]; exact h2⟩ ?_
        Ξ hox, hoy
        rcases hBo with h | h
        · left; rw [h]; exact h0
        · right; linarith
      exact ((hM.eq_iff_not_separates hF hfin hR hR (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) htx hty
        hcx hcy hfx hfy).1 rfl) f₂ hf₂.1 hs
    -- a faced position of `R` near the first position, below the second
    obtain ⟨dx, tx, hdx, htx, hx0, hx1, hcx, hfx⟩ : ∃ (dx : ℕ) (tx : ℝ), dx ≤ d₁ ∧
        tx ∈ Ioo (0 : ℝ) 1 ∧ 0 < (dx : ℝ) + tx ∧ (dx : ℝ) + tx < d₂ + t₂ ∧
        ¬ M.IsCut F (((g + dx) % n : ℕ) + tx) ∧ M.Faces ((g + dx) % n) tx R := by
      rcases adj_near hM hF hfin hne ht₁ ht₁1 hdt₁ hadj₁ with h | h
      · obtain ⟨dx, tx, hdx, htx, h1, h2, h3, h4⟩ := h _ h12
        exact ⟨dx, tx, hdx, htx, ⟡, h2, h3, h4⟩
      · obtain ⟨dx, tx, hdx, htx, h1, h2, h3, h4⟩ := h 0 hdt₁
        exact ⟨dx, tx, hdx, htx, h1, ⟡, h3, h4⟩
    -- a faced position of `R` near the third position, above the second
    obtain ⟨dz, tz, hdz, htz, hz0, hz1, hcz, hfz⟩ : ∃ (dz : ℕ) (tz : ℝ), dz ≤ d₃ ∧
        tz ∈ Ioo (0 : ℝ) 1 ∧ (d₂ : ℝ) + t₂ < dz + tz ∧ (dz : ℝ) + tz < L ∧
        ¬ M.IsCut F (((g + dz) % n : ℕ) + tz) ∧ M.Faces ((g + dz) % n) tz R := by
      rcases adj_near hM hF hfin hne ht₃ ht₃1 hdt₃ hadj₃ with h | h
      · obtain ⟨dz, tz, hdz, htz, h1, h2, h3, h4⟩ := h _ (hLR hd₃ ht₃1)
        exact ⟨dz, tz, hdz, htz, ⟡, h2, h3, h4⟩
      · obtain ⟨dz, tz, hdz, htz, h1, h2, h3, h4⟩ := h _ h23
        exact ⟨dz, tz, hdz, htz, h1, by linarith [hLR hd₃ ht₃1], h3, h4⟩
    rcases adj_near hM hF hfin hne ht₂ ht₂1 hdt₂ hadj₂ with h | h
    · obtain ⟨dy, ty, hdy, hty, h1, h2, h3, h4⟩ := h _ h23
      exact hsep (⋄) (⋄) htx hty hx0 hx1 h1 (by linarith [hLR hd₃ ht₃1])
        hcx hfx h3 h4
    · obtain ⟨dy, ty, hdy, hty, h1, h2, h3, h4⟩ := h _ h12
      exact hsep (⋄) (⋄) hty htz (⟡) h2 hz0 hz1 h3 h4 hcz hfz
  have hOfin : O.Finite := by
    refine ((hM.finite_cuts hF hfin).image (off n g)).subset ?_
    rintro _ ⟨f, hf, d, t, hd, ht, ht1, -, hA, -, -, rfl⟩
    exact ⟨_, ⟨f, hf.1, _, _, hA, rfl⟩, off_key hg (⋄) ht ht1⟩
  have hO2 : O.ncard ≤ 2 := ncard_le_two_of_no_three hno3
  have hsub : CrossX M F R g L ⊆ ⋃ o ∈ O, {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧
      t < 1 ∧ o = d + t ∧ SideAttach M.W f ((g + d) % M.W.n) t} := by
    rintro f ⟨hf, d, t, hd, ht, ht1, hdt, hA, hadj, hX⟩
    ϴ Set.mem_iUnion
    exact ⟨d + t, ⟨f, hf, d, t, hd, ht, ht1, hdt, hA, hadj, hX, rfl⟩,
      hf.1, d, t, hd, ht, ht1, rfl, hA⟩
  calc (CrossX M F R g L).ncard
      ≤ (⋃ o ∈ O, {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ o = d + t ∧
          SideAttach M.W f ((g + d) % M.W.n) t}).ncard :=
        Set.ncard_le_ncard hsub (hfin.subset (by
          intro f hf; ϴ' Set.mem_iUnion at hf; obtain ⟨o, -, hf, -⟩ := hf; exact hf))
    _ ≤ 2 * O.ncard := ncard_biUnion_le_mul hOfin _ fun o _ => ncard_at_off_le hM hF hfin g L o
    _ ≤ 4 := ⋄

end FuseDeg

end

end Chazelle.Core
