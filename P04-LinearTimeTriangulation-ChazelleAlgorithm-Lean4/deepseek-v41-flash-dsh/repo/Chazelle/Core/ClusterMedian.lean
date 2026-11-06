module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterEuler
public import Chazelle.Core.ClusterLbRam

/-!
# WP-I, part 19: the centroid of a piece in preorder terms

A piece is a segment `[lo, hi)` of positions whose keys `κ i = pre (φ i)` (the preorder numbers of
the faces `φ i` of its vertices) are sorted.  A node `z` of the tree `R` is *good* if more than
half of the keys lie in its preorder interval (`GdN`).

* `good_anc_median`: every good node is an ancestor of the face `φ m` of the median position
  `m = lo + (hi - lo) / 2`;
* `good_root`: the root is good for a nonempty piece;
* `iterate_up_root`: `2^L ≥ n` steps up reach the root;
* `anc_ch_unique`: two children of the same node on the path to `y` are equal;
* `centroid_of_climb`: the result of the climb (`climbStmt_exec`) is a good node none of whose
  children is good.
-/

namespace Chazelle.Core.Cluster

namespace BTree

@[expose] public section

variable {R : BTree}

/-- The good predicate: more than half of the keys of `[lo, hi)` lie in the interval of `z`. -/
def GdN (pre sz κ : ℕ → ℕ) (lo hi z : ℕ) : Prop :=
  hi - lo < 2 * cntIn κ lo hi (pre z) (pre z + sz z)

/-- The count of a key interval is at most the number of positions in any range containing all
positions whose key is in the interval. -/
theorem cntIn_le_of_sub {κ : ℕ → ℕ} {lo hi a b l r : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → a ≤ κ i → κ i < b → l ≤ i ∧ i < r) :
    cntIn κ lo hi a b ≤ r - l := by
  unfold cntIn
  Ξ ← Nat.card_Ico l r
  refine Finset.card_le_card (fun i hi' => ?_)
  ϴ' Finset.mem_filter, Finset.mem_Ico at hi' ⊢
  exact h i hi'.1.1 hi'.1.2 hi'.2.1 hi'.2.2

/-- **The median**: a key interval holding more than half of the sorted keys holds the key of
the median position. -/
theorem median_mem {κ : ℕ → ℕ} {lo hi a b : ℕ} (hs : Sorted κ lo hi)
    (hg : hi - lo < 2 * cntIn κ lo hi a b) :
    a ≤ κ (lo + (hi - lo) / 2) ∧ κ (lo + (hi - lo) / 2) < b := by
  have hlh : lo < hi := by
    by_contra h
    have : cntIn κ lo hi a b = 0 := by
      unfold cntIn
      Ξ Finset.card_eq_zero, Finset.filter_eq_empty_iff
      intro i hi'; simp only [Finset.mem_Ico] at hi'; omega
    omega
  set m := lo + (hi - lo) / 2
  have hm : m < hi := ⋄
  constructor
  · by_contra h
    push Not at h
    have := cntIn_le_of_sub (κ := κ) (lo := lo) (hi := hi) (a := a) (b := b) (l := m + 1) (r := hi)
      (fun i h1 h2 h3 _ => by
        refine ⟨?_, h2⟩
        by_contra hi'
        have := hs i m h1 (⋄) hm
        omega)
    omega
  · by_contra h
    push Not at h
    have := cntIn_le_of_sub (κ := κ) (lo := lo) (hi := hi) (a := a) (b := b) (l := lo) (r := m)
      (fun i h1 h2 _ h4 => by
        refine ⟨h1, ?_⟩
        by_contra hi'
        have := hs m i (⋄) (⋄) h2
        omega)
    omega

variable {pre slot : ℕ → ℕ}

/-- **Every good node is an ancestor of the median face.** -/
theorem good_anc_median (hR : R.OK) (hP : R.PreInv pre slot R.n) {κ φ : ℕ → ℕ} {lo hi z : ℕ}
    (hs : Sorted κ lo hi) (hκ : ∀ i, lo ≤ i → i < hi → φ i < R.n ∧ κ i = pre (φ i))
    (hz : z < R.n) (hg : GdN pre (fun g => (R.sub g).card) κ lo hi z) :
    R.Anc z (φ (lo + (hi - lo) / 2)) := by
  unfold GdN at hg
  simp only at hg
  have hlh : lo < hi := by
    by_contra h
    have : cntIn κ lo hi (pre z) (pre z + (R.sub z).card) = 0 := by
      unfold cntIn
      Ξ Finset.card_eq_zero, Finset.filter_eq_empty_iff
      intro i hi'; ϴ' Finset.mem_Ico at hi'; omega
    omega
  obtain ⟨h1, h2⟩ := median_mem hs hg
  obtain ⟨hφ, hκm⟩ := hκ (lo + (hi - lo) / 2) (⋄) (⋄)
  Ξ' hκm at h1 h2
  exact (hP.anc_iff hR hz hφ).mpr ⟨h1, h2⟩

/-- **The root is good** for a nonempty piece whose keys are preorders. -/
theorem good_root (hR : R.OK) (hP : R.PreInv pre slot R.n) {κ φ : ℕ → ℕ} {lo hi : ℕ}
    (hκ : ∀ i, lo ≤ i → i < hi → φ i < R.n ∧ κ i = pre (φ i)) (hlh : lo < hi) :
    GdN pre (fun g => (R.sub g).card) κ lo hi R.root := by
  unfold GdN cntIn
  simp only
  Ξ hP.root, hR.card_sub_root
  have : (Finset.Ico lo hi).filter (fun i => 0 ≤ κ i ∧ κ i < 0 + R.n) = Finset.Ico lo hi := by
    refine Finset.filter_true_of_mem (fun i hi' => ?_)
    ϴ' Finset.mem_Ico at hi'
    obtain ⟨a, b⟩ := hκ i hi'.1 hi'.2
    Ξ b
    exact ⟨Nat.zero_le _, by have := hP.pre_lt hR a; omega⟩
  Ξ this, Nat.card_Ico
  omega

/-- Going up `j ≥ pos h` steps reaches the root. -/
theorem iterate_up_root (hR : R.OK) {h : ℕ} (hh : h < R.n) {j : ℕ} (hj : R.pos h ≤ j) :
    R.up^[j] h = R.root := by
  induction j generalizing h with
  | zero =>
    have : R.pos h = 0 := ⋄
    have e := (hR.pos_spec hh).2
    Ξ' this at e
    rw [Function.iterate_zero_apply, ← e]; rfl
  | succ j ih =>
    Ξ Function.iterate_succ_apply
    by_cases hr : h = R.root
    · have : R.up h = h := ⊚ up, hr
      Ξ this
      exact ih hh (by rw [hr, hR.pos_root]; omega)
    · have hup : R.up h = R.par h := ⊚ up, hr
      obtain ⟨a, b⟩ := hR.par_spec hh hr
      Ξ hup
      exact ih a (⋄)

/-- **Two children of one node on the path to `y` are equal.** -/
theorem anc_ch_unique (hR : R.OK) {y c c' : ℕ} (hy : y < R.n) (hc : R.Anc c y)
    (hc' : R.Anc c' y) (hcr : c ≠ R.root) (hcr' : c' ≠ R.root) (hp : R.par c = R.par c') :
    c = c' := by
  -- ancestors of `y` are totally ordered
  obtain ⟨m, hm⟩ := hc
  obtain ⟨m', hm'⟩ := hc'
  have hcn : c < R.n := hm ▸ hR.iterate_up_lt m hy
  have hcn' : c' < R.n := hm' ▸ hR.iterate_up_lt m' hy
  have key : ∀ {a b : ℕ} {i j : ℕ}, R.up^[i] y = a → R.up^[j] y = b → i ≤ j → a < R.n →
      a ≠ R.root → b ≠ R.root → R.par a = R.par b → a = b := by
    intro a b i j hi hj hij ha har hbr hpar
    by_contra hne
    have hab : R.Anc b a := ⟨j - i, by
      rw [← hi, ← Function.iterate_add_apply, show j - i + i = j by omega]; exact hj⟩
    have hba : b ≠ a := fun h => hne h.symm
    have h1 := (anc_iff_up hba).mp hab
    rw [show R.up a = R.par a by simp [up, har], hpar] at h1
    have hbn : b < R.n := hj ▸ hR.iterate_up_lt j hy
    have := hR.pos_le_of_anc (hR.par_spec hbn hbr).1 h1
    have := (hR.par_spec hbn hbr).2
    omega
  rcases le_total m m' with h | h
  · exact key hm hm' h hcn hcr hcr' hp
  · exact (key hm' hm h hcn' hcr' hcr hp.symm).symm

/-- **The centroid from the climb.**  If every good node is an ancestor of `y`, the result of
the climb (either `y` good, or `up x` good for an ancestor `x` of `y` that is not good) is a good
node without good children. -/
theorem centroid_of_climb (hR : R.OK) {Gd : ℕ → Prop} {y f : ℕ} (hy : y < R.n)
    (hanc : ∀ z, z < R.n → Gd z → R.Anc z y)
    (hres : (Gd y ∧ f = y) ∨ ∃ x n, R.up^[n] y = x ∧ ¬ Gd x ∧ Gd (R.up x) ∧ f = R.up x) :
    Gd f ∧ ∀ c, c < R.n → c ≠ R.root → R.par c = f → ¬ Gd c := by
  rcases hres with ⟨hg, rfl⟩ | ⟨x, n, hx, hng, hg, rfl⟩
  · refine ⟨hg, fun c hc hcr hpc hgc => ?_⟩
    have h1 := hanc c hc hgc
    have h2 : R.Anc f c := ⟨1, ⊚ up, hcr, hpc⟩
    have := hR.anc_antisymm hy hc h1 h2
    subst this
    have := (hR.par_spec hc hcr).2
    rw [hpc] at this; omega
  · have hxr : x ≠ R.root := by
      intro h
      have : R.up x = x := ⊚ up, h
      rw [this] at hg; exact hng hg
    have hxn : x < R.n := hx ▸ hR.iterate_up_lt n hy
    refine ⟨hg, fun c hc hcr hpc hgc => hng ?_⟩
    have hupx : R.up x = R.par x := ⊚ up, hxr
    have := anc_ch_unique hR hy (hanc c hc hgc) ⟨n, hx⟩ hcr hxr (Ρ hpc, hupx)
    rw [← this]; exact hgc

end

end BTree

end Chazelle.Core.Cluster
