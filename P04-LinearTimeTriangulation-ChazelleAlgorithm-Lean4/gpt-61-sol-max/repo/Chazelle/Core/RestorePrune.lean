module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreCounts
public import Chazelle.Core.FactsL23
public import Chazelle.Core.WalkEmbed

/-!
# WP-E, Lemma 3.2 part 6: pruning the candidates of an arc

The search for a chord from the arc `Aᵢ` to the arc `Aⱼ` of a region `R` narrows down the
candidate walk positions of `Aᵢ` with chords `aa'` of the host model shot from points `a` strictly
inside `Aᵢ`.  A candidate `x` is *good* if its own chord `xx'` ends on the closed arc `Aⱼ` and
passes the count test.  This file proves:

* `sideInArc_rot`: cyclic betweenness is invariant under rotation of the keys (`WalkEmbed.off`);
* `sideExits_mono`: the side counts only depend on the cut keys inside the key interval;
* `cyc_dom_open`, `cyc_dom_same`: the key intervals of `aa'` contain every cut key of the key
  intervals of `xx'` when `a'` is strictly inside `Aⱼ`, or when `a' = x'`;
* `prune`: **the pruning lemma** — if the shot chord `aa'` fails the count test and the good
  candidate `x` is neither `a` nor `a'`, then `x` is strictly on the side of `aa'` that contains
  the open arc `Aⱼ`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem SideAttach sideInArc sidePt regionsIn TouchesIn sideKey_inj
  sideInArc_swap)
open WalkEmbed (off)

variable {M : Model}

/-! ## Cyclic order -/

/-- Cyclic betweenness is invariant under rotation. -/
theorem sideInArc_rot {n g a b x : ℝ} (_hg0 : 0 ≤ g) (_hgn : g < n) (ha0 : 0 ≤ a) (han : a < n)
    (hb0 : 0 ≤ b) (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) :
    sideInArc a b x ↔ sideInArc (off n g a) (off n g b) (off n g x) := by
  unfold off sideInArc
  split_ifs <;> constructor <;> intro h <;> cyc_close

/-- The closed cyclic interval `[a, b]`. -/
def ClosedArc (a b x : ℝ) : Prop := sideInArc a b x ∨ x = a ∨ x = b

/-- Facts about an interval `(A, B)` (keys in `[0, n)`) containing the key `0`. -/
theorem cyc_zero {A B : ℝ} (hA0 : 0 ≤ A) (hAB : A ≠ B) (hi : sideInArc A B 0) : 0 < B ∧ B < A := by
  core_grind

/-- Outside an interval `(A, B)` containing `0`. -/
theorem cyc_zero_out {A B u : ℝ} (hBA : B < A) (h : ¬ sideInArc A B u) : B ≤ u ∧ u ≤ A := by
  core_grind

/-- On the closed interval `[A, B]` containing `0` inside. -/
theorem cyc_zero_closed {A B x : ℝ} (hBA : B < A) (h : ClosedArc A B x) : A ≤ x ∨ x ≤ B := by
  core_grind [sideInArc]

/-- **Domination when `a'` is strictly inside `Aⱼ`** (keys rotated so that `a` is at `0`). -/
theorem cyc_dom_open {A B A' B' x x' a' u : ℝ} (hA0 : 0 ≤ A) (_hB'0 : 0 ≤ B') (_hx0 : 0 ≤ x)
    (hAB : A ≠ B) (hi : sideInArc A B 0) (hjA : ¬ sideInArc A B A')
    (hjB : ¬ sideInArc A B B') (hj0 : ¬ sideInArc A' B' 0)
    (ha' : sideInArc A' B' a') (hx : ClosedArc A B x) (hx' : ClosedArc A' B' x') (hxx : x ≠ x')
    (hui : ¬ sideInArc A B u) (huj : ¬ sideInArc A' B' u) :
    (sideInArc x x' u → sideInArc 0 a' u) ∧ (sideInArc x' x u → sideInArc a' 0 u) := by
  core_grind

/-- **Domination when `a' = x'`** (keys rotated so that `a` is at `0`). -/
theorem cyc_dom_same {A B x k u : ℝ} (hA0 : 0 ≤ A) (hAB : A ≠ B) (hi : sideInArc A B 0)
    (hx : ClosedArc A B x) (hxk : x ≠ k) (hk : ¬ sideInArc A B k) (hui : ¬ sideInArc A B u) :
    (sideInArc x k u → sideInArc 0 k u) ∧ (sideInArc k x u → sideInArc k 0 u) := by
  obtain ⟨hB0, hBA⟩ := cyc_zero hA0 hAB hi
  obtain ⟨h1, h2⟩ := cyc_zero_out hBA hk
  obtain ⟨h5, h6⟩ := cyc_zero_out hBA hui
  have h7 := cyc_zero_closed hBA hx
  core_grind

/-- A start or an end version of `cyc_nosep`: the start of an interval is on the side of its
interior points (with respect to two keys outside the interval). -/
theorem cyc_nosep_start {a x y A B : ℝ} (hy : sideInArc a x y) (hA : ¬ sideInArc a x A)
    (hB : ¬ sideInArc a x B) (haA : a ≠ A) (haB : a ≠ B) (hAB : A ≠ B) :
    sideInArc A B y ↔ sideInArc A B a := by
  core_grind

/-- A more thorough closing tactic for cyclic case analyses (nested disjunctions). -/
macro "cyc_close2" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor! <;> linarith) | (right; constructor! <;> linarith)
  | (left; linarith) | (right; linarith)
  | (right; left; linarith) | (right; right; linarith)
  | (left; left; linarith) | (left; right; linarith)
  | (right; left; constructor! <;> linarith) | (right; right; constructor! <;> linarith)
  | (left; left; constructor! <;> linarith) | (left; right; constructor! <;> linarith)))

/-- The part of an interval before one of its interior points is inside the interval. -/
theorem cyc_sub_arc {a b w z : ℝ} (hw : sideInArc a b w) (hz : sideInArc a w z) :
    sideInArc a b z := by
  core_grind

section
variable {a b y w : ℝ} (hy : sideInArc a b y) (hw : sideInArc a b w) (hyw : y ≠ w)
include b hy hw hyw
/-- Of two distinct interior points of an interval, one is before the other. -/
theorem cyc_split :
    sideInArc a w y ∨ sideInArc a y w := by
  core_grind

/-- Two interior points of an interval: one is inside the part of the interval before the other. -/
theorem cyc_order :
    (sideInArc a w y ∧ ∀ z, sideInArc a w z → sideInArc a b z) ∨
      (sideInArc a y w ∧ ∀ z, sideInArc a y z → sideInArc a b z) := by
  rcases cyc_split hy hw hyw with h | h
  · exact Or.inl ⟨h, fun z hz => cyc_sub_arc hw hz⟩
  · exact Or.inr ⟨h, fun z hz => cyc_sub_arc hy hz⟩


end

/-- A closed interval avoiding two keys lies on one side of them. -/
theorem cyc_closed_side {a b y w k k' : ℝ} (hy : sideInArc a b y)
    (hw : ClosedArc a b w) (hk : ¬ sideInArc a b k) (hk' : ¬ sideInArc a b k') (hkk : k ≠ k')
    (hwk : w ≠ k) (hwk' : w ≠ k') :
    sideInArc k k' w ↔ sideInArc k k' y := by
  have hyk : y ≠ k := fun h => hk (h ▸ hy)
  have hyk' : y ≠ k' := fun h => hk' (h ▸ hy)
  rcases hw with hw | rfl | rfl
  · by_cases hyw : y = w
    · rw [hyw]
    rcases cyc_order hy hw hyw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (cyc_nosep h1 (fun h => hk (h2 _ h)) (fun h => hk' (h2 _ h)) hwk hwk' hkk).symm
    · exact cyc_nosep h1 (fun h => hk (h2 _ h)) (fun h => hk' (h2 _ h)) hyk hyk' hkk
  · exact (cyc_nosep_start hy hk hk' hwk hwk' hkk).symm
  · exact (cyc_nosep hy hk hk' hwk hwk' hkk).symm

/-- Two cyclic intervals with a common interior key and distinct starts: the start of one is
inside the other. -/
theorem cyc_overlap {a b a' b' y : ℝ} (hab : a ≠ b) (hab' : a' ≠ b') (haa : a ≠ a')
    (hy : sideInArc a b y) (hy' : sideInArc a' b' y) : sideInArc a b a' ∨ sideInArc a' b' a := by
  core_grind

/-- A key is strictly on one side when it avoids both ends. -/
theorem cyc_two {k k' x : ℝ} (hkk : k ≠ k') (hx : x ≠ k) (hx' : x ≠ k') :
    sideInArc k k' x ∨ sideInArc k' k x := by
  rcases cyc_cases (x := x) hkk with h | h | h | h
  all_goals simp_all

/-! ## Side counts -/

/-- The count test of a candidate chord: at least two exit chords of `R` attached strictly on each
side. -/
def CountOK (M : Model) (S : Set (Set Point)) (R : Set Point) (k₁ k₂ : ℝ) : Prop :=
  2 ≤ (sideExits M S R k₁ k₂).ncard ∧ 2 ≤ (sideExits M S R k₂ k₁).ncard

section
variable {S : Set (Set Point)}
/-- The side counts only depend on the cut keys inside the key interval. -/
theorem sideExits_mono {R : Set Point} {k₁ k₂ l₁ l₂ : ℝ}
    (h : ∀ u, M.IsCut S u → sideInArc k₁ k₂ u → sideInArc l₁ l₂ u) :
    sideExits M S R k₁ k₂ ⊆ sideExits M S R l₁ l₂ := by
  rintro c ⟨hc, p, t, hat, hin⟩
  exact ⟨hc, p, t, hat, h _ ⟨c, hc.1, p, t, hat, rfl⟩ hin⟩

/-- Domination of the count test. -/
theorem countOK_mono (hfin : S.Finite) {R : Set Point} {k₁ k₂ l₁ l₂ : ℝ}
    (h₁ : ∀ u, M.IsCut S u → sideInArc k₁ k₂ u → sideInArc l₁ l₂ u)
    (h₂ : ∀ u, M.IsCut S u → sideInArc k₂ k₁ u → sideInArc l₂ l₁ u)
    (hc : CountOK M S R k₁ k₂) : CountOK M S R l₁ l₂ := by
  have hf : ∀ a b : ℝ, (sideExits M S R a b).Finite := fun a b =>
    (hfin.subset (Merge.exitsIn_subset S R)).subset (sideExits_subset S R a b)
  exact ⟨hc.1.trans (ncard_le_ncard (sideExits_mono h₁) (hf _ _)),
    hc.2.trans (ncard_le_ncard (sideExits_mono h₂) (hf _ _))⟩

/-! ## The pruning lemma -/


end

/-- The key of an attachment is in `[0, n)`. -/
theorem key_range {W : Polygon} {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach W c p t) :
    0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < W.n := by
  have hp : (p : ℝ) + 1 ≤ W.n := by exact_mod_cast hA.1
  exact ⟨by have := hA.2.1; positivity, by linarith [hA.2.2.1]⟩

/-- Offsets are injective on `[0, n)`. -/
theorem off_inj {n g x y : ℝ} (_hg0 : 0 ≤ g) (_hgn : g < n) (hx0 : 0 ≤ x) (hxn : x < n)
    (hy0 : 0 ≤ y) (hyn : y < n) (h : off n g x = off n g y) : x = y := by
  core_grind

/-- Rotation of a closed interval. -/
theorem closedArc_rot {n g a b x : ℝ} (hg0 : 0 ≤ g) (hgn : g < n) (ha0 : 0 ≤ a) (han : a < n)
    (hb0 : 0 ≤ b) (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) :
    ClosedArc a b x ↔ ClosedArc (off n g a) (off n g b) (off n g x) := by
  unfold ClosedArc
  rw [sideInArc_rot hg0 hgn ha0 han hb0 hbn hx0 hxn]
  constructor
  · grind
  · rintro (h | h | h)
    · simp_all
    · exact Or.inr (Or.inl (off_inj hg0 hgn hx0 hxn ha0 han h))
    · exact Or.inr (Or.inr (off_inj hg0 hgn hx0 hxn hb0 hbn h))

section
variable (hM : WalkAx M)
include hM
/-- An attachment of an admissible chord `e` attached at `A` and `A'` is `A` or `A'` (by key). -/
theorem attach_key_cases {e : Set Point} (he : e ∈ M.Adm) {pa pb p : ℕ}
    {ta tb t : ℝ} (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (h : SideAttach M.W e p t) :
    (p : ℝ) + t = pa + ta ∨ (p : ℝ) + t = pb + tb := by
  obtain ⟨a, b, hab, heq, -, hopen, -, -⟩ := hM.ends e he
  rw [heq] at hA hB h
  have ha := hM.attach_endpoint hopen hA
  have hb := hM.attach_endpoint hopen hB
  have hx := hM.attach_endpoint hopen h
  rw [← heq] at hA hB h
  have key : ∀ (q : ℕ) (s : ℝ), SideAttach M.W e q s → sidePt M.W p t = sidePt M.W q s →
      (p : ℝ) + t = q + s := by
    intro q s hq hpt
    obtain ⟨h1, h2⟩ := attach_unique hM he h hq hpt
    rw [h1, h2]
  grind

/-- **The pruning lemma.**  Let `Aᵢ = (aᵢ, bᵢ)` and `Aⱼ = (aⱼ, bⱼ)` be two distinct arcs of the
region `R` of the nonempty family `S`.  Let the admissible chord `e_a` be attached at `A`, with key
strictly inside `Aᵢ`, and at `A'`, and fail the count test; let the admissible chord `e_x` be
attached at `X`, with key in the closed arc `Aᵢ`, and at `X'`, with key in the closed arc `Aⱼ`, and
pass the count test.  If the key of `X` is neither that of `A` nor that of `A'`, then `A'` is not
inside `Aⱼ`, and the key of `X` is strictly on the side of `e_a` that contains the open arc
`Aⱼ`. -/
theorem prune {S : Set (Set Point)} (_hS : S ⊆ M.Adm) (hfin : S.Finite)
    (hne : S.Nonempty) {R : Set Point} {ai bi aj bj : ℝ} (hAi : M.IsArc S R ai bi)
    (hAj : M.IsArc S R aj bj) (hij : ai ≠ aj)
    {ea : Set Point} (hea : ea ∈ M.Adm) {pa pa' : ℕ} {ta ta' : ℝ}
    (hA : SideAttach M.W ea pa ta) (hA' : SideAttach M.W ea pa' ta')
    (hAA' : sidePt M.W pa ta ≠ sidePt M.W pa' ta') (hka : sideInArc ai bi (pa + ta))
    {ex : Set Point} (hex : ex ∈ M.Adm) {px px' : ℕ} {tx tx' : ℝ}
    (hX : SideAttach M.W ex px tx) (hX' : SideAttach M.W ex px' tx')
    (hXX' : sidePt M.W px tx ≠ sidePt M.W px' tx') (hkx : ClosedArc ai bi (px + tx))
    (hkx' : ClosedArc aj bj (px' + tx'))
    (hgood : CountOK M S R (px + tx) (px' + tx')) (hbad : ¬ CountOK M S R (pa + ta) (pa' + ta'))
    (hxa : (px : ℝ) + tx ≠ pa + ta) (hxa' : (px : ℝ) + tx ≠ pa' + ta') :
    ¬ sideInArc aj bj (pa' + ta') ∧ ∀ y, sideInArc aj bj y →
      (sideInArc (pa + ta) (pa' + ta') (px + tx) ↔ sideInArc (pa + ta) (pa' + ta') y) := by
  set n : ℝ := (M.W.n : ℝ) with hn
  set ka : ℝ := (pa : ℝ) + ta with hkad
  set ka' : ℝ := (pa' : ℝ) + ta' with hka'd
  set kx : ℝ := (px : ℝ) + tx with hkxd
  set kx' : ℝ := (px' : ℝ) + tx' with hkx'd
  obtain ⟨hka0, hkan⟩ := key_range hA
  obtain ⟨hka'0, hka'n⟩ := key_range hA'
  obtain ⟨hkx0, hkxn⟩ := key_range hX
  obtain ⟨hkx'0, hkx'n⟩ := key_range hX'
  obtain ⟨hcai, hcbi, hab⟩ := WalkAx.arc_cuts hne hAi
  obtain ⟨hcaj, hcbj, hab'⟩ := WalkAx.arc_cuts hne hAj
  obtain ⟨hai0, hain, hbi0, hbin, -, hnoi, -⟩ := hAi
  obtain ⟨haj0, hajn, hbj0, hbjn, -, hnoj, -⟩ := hAj
  have hkk : ka ≠ ka' := key_ne_of_attach hA hA' hAA'
  have hxx : kx ≠ kx' := key_ne_of_attach hX hX' hXX'
  -- the two open arcs are disjoint
  have hF1 : ¬ sideInArc ai bi aj := fun h => hnoi _ h hcaj
  have hF1' : ¬ sideInArc ai bi bj := fun h => hnoi _ h hcbj
  have hF1'' : ¬ sideInArc aj bj ai := fun h => hnoj _ h hcai
  have disj : ∀ z, sideInArc ai bi z → ¬ sideInArc aj bj z := by
    intro z h1 h2
    rcases cyc_overlap hab hab' hij h1 h2 with h | h
    all_goals grind
  have hF2 : ¬ sideInArc aj bj ka := disj _ hka
  have hF4 : ¬ sideInArc ai bi kx' := by
    intro h
    rcases hkx' with h' | h' | h'
    · grind
    all_goals grind
  -- rotation by `ka`
  have rot := fun {a b x : ℝ} (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
      (hx0 : 0 ≤ x) (hxn : x < n) =>
    sideInArc_rot (n := n) (g := ka) hka0 hkan ha0 han hb0 hbn hx0 hxn
  have crot := fun {a b x : ℝ} (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
      (hx0 : 0 ≤ x) (hxn : x < n) =>
    closedArc_rot (n := n) (g := ka) hka0 hkan ha0 han hb0 hbn hx0 hxn
  have o0 : off n ka ka = 0 := WalkEmbed.off_self n ka
  have on0 : ∀ {x}, 0 ≤ x → 0 ≤ off n ka x := fun h => WalkEmbed.off_nonneg h hkan
  
  have oinj : ∀ {x y}, 0 ≤ x → x < n → 0 ≤ y → y < n → off n ka x = off n ka y → x = y :=
    fun hx0 hxn hy0 hyn h => off_inj hka0 hkan hx0 hxn hy0 hyn h
  have hi' : sideInArc (off n ka ai) (off n ka bi) 0 := by
    rw [← o0]; exact (rot hai0 hain hbi0 hbin hka0 hkan).1 hka
  have habo : off n ka ai ≠ off n ka bi := fun h => hab (oinj hai0 hain hbi0 hbin h)
  -- (a) `a'` is not inside `Aⱼ`
  have ha'j : ¬ sideInArc aj bj ka' := by
    intro ha'
    apply hbad
    refine countOK_mono hfin (fun u hu h => ?_) (fun u hu h => ?_) hgood
    · obtain ⟨hu0, hun⟩ := WalkAx.cut_bounds hu
      have hdom := cyc_dom_open (on0 hai0) (on0 hbj0) (on0 hkx0) habo hi'
        (by rw [← rot hai0 hain hbi0 hbin haj0 hajn]; exact hF1)
        (by rw [← rot hai0 hain hbi0 hbin hbj0 hbjn]; exact hF1')
        (by rw [← o0, ← rot haj0 hajn hbj0 hbjn hka0 hkan]; exact hF2)
        ((rot haj0 hajn hbj0 hbjn hka'0 hka'n).1 ha') ((crot hai0 hain hbi0 hbin hkx0 hkxn).1 hkx)
        ((crot haj0 hajn hbj0 hbjn hkx'0 hkx'n).1 hkx')
        (fun h => hxx (oinj hkx0 hkxn hkx'0 hkx'n h))
        (by rw [← rot hai0 hain hbi0 hbin hu0 hun]; exact fun h => hnoi _ h hu)
        (by rw [← rot haj0 hajn hbj0 hbjn hu0 hun]; exact fun h => hnoj _ h hu)
      have := hdom.1 ((rot hkx0 hkxn hkx'0 hkx'n hu0 hun).1 h)
      rw [← o0] at this
      exact (rot hka0 hkan hka'0 hka'n hu0 hun).2 this
    · obtain ⟨hu0, hun⟩ := WalkAx.cut_bounds hu
      have hdom := cyc_dom_open (on0 hai0) (on0 hbj0) (on0 hkx0) habo hi'
        (by rw [← rot hai0 hain hbi0 hbin haj0 hajn]; exact hF1)
        (by rw [← rot hai0 hain hbi0 hbin hbj0 hbjn]; exact hF1')
        (by rw [← o0, ← rot haj0 hajn hbj0 hbjn hka0 hkan]; exact hF2)
        ((rot haj0 hajn hbj0 hbjn hka'0 hka'n).1 ha') ((crot hai0 hain hbi0 hbin hkx0 hkxn).1 hkx)
        ((crot haj0 hajn hbj0 hbjn hkx'0 hkx'n).1 hkx')
        (fun h => hxx (oinj hkx0 hkxn hkx'0 hkx'n h))
        (by rw [← rot hai0 hain hbi0 hbin hu0 hun]; exact fun h => hnoi _ h hu)
        (by rw [← rot haj0 hajn hbj0 hbjn hu0 hun]; exact fun h => hnoj _ h hu)
      have := hdom.2 ((rot hkx'0 hkx'n hkx0 hkxn hu0 hun).1 h)
      rw [← o0] at this
      exact (rot hka'0 hka'n hka0 hkan hu0 hun).2 this
  -- (b) `x'` is not `a'`
  have hx'a' : kx' ≠ ka' := by
    intro heq
    have hF4' : ¬ sideInArc ai bi ka' := fun h => hF4 (heq ▸ h)
    apply hbad
    refine countOK_mono hfin (fun u hu h => ?_) (fun u hu h => ?_) hgood
    · obtain ⟨hu0, hun⟩ := WalkAx.cut_bounds hu
      have hdom := cyc_dom_same (on0 hai0) habo hi'
        ((crot hai0 hain hbi0 hbin hkx0 hkxn).1 hkx)
        (fun h => hxa' (oinj hkx0 hkxn hka'0 hka'n h))
        (by rw [← rot hai0 hain hbi0 hbin hka'0 hka'n]; exact hF4')
        (by rw [← rot hai0 hain hbi0 hbin hu0 hun]; exact fun h => hnoi _ h hu)
      rw [heq] at h
      have := hdom.1 ((rot hkx0 hkxn hka'0 hka'n hu0 hun).1 h)
      rw [← o0] at this
      exact (rot hka0 hkan hka'0 hka'n hu0 hun).2 this
    · obtain ⟨hu0, hun⟩ := WalkAx.cut_bounds hu
      have hdom := cyc_dom_same (on0 hai0) habo hi'
        ((crot hai0 hain hbi0 hbin hkx0 hkxn).1 hkx)
        (fun h => hxa' (oinj hkx0 hkxn hka'0 hka'n h))
        (by rw [← rot hai0 hain hbi0 hbin hka'0 hka'n]; exact hF4')
        (by rw [← rot hai0 hain hbi0 hbin hu0 hun]; exact fun h => hnoi _ h hu)
      rw [heq] at h
      have := hdom.2 ((rot hka'0 hka'n hkx0 hkxn hu0 hun).1 h)
      rw [← o0] at this
      exact (rot hka'0 hka'n hka0 hkan hu0 hun).2 this
  refine ⟨ha'j, fun y hy => ?_⟩
  -- (c) `x'`, hence `x`, is on the side of the open arc `Aⱼ`
  have hx'ka : kx' ≠ ka := fun h => hF4 (h ▸ hka)
  have hside := cyc_closed_side hy hkx' hF2 ha'j hkk hx'ka hx'a'
  have hne' : ex ≠ ea := by
    intro h
    rw [h] at hX
    rcases attach_key_cases hM hea hA hA' hAA' hX with h | h
    · exact hxa h
    grind
  rcases cyc_two hkk hx'ka hx'a' with h | h
  · have h1 := same_side hM hea hex hne' hA hA' hAA' hX' hX h
    rcases cyc_two hkk hxa hxa' with h2 | h2
    · grind
    grind
  · have h1 := same_side hM hea hex hne' hA' hA hAA'.symm hX' hX h
    rcases cyc_two hkk hxa hxa' with h2 | h2
    · grind
    · constructor
      · grind
      · intro h3
        exfalso
        exact (sideInArc_swap hkk hx'ka hx'a').1 (hside.2 h3) h


end

end

end Restore

end Chazelle.Core
