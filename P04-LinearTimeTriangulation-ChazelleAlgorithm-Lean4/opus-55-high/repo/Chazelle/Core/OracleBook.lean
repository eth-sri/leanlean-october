module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Programs.Tactics

section
set_option hygiene false
local macro "zqnf" : tactic => `(tactic| (zvmwh at this; omega))
local macro "zqng" : tactic => `(tactic| (rcases c with ⟨a, b⟩; simp only [ViewOK] at hwok; zvnpp at hwt; subst hwt))
local macro "zqnh" : tactic => `(tactic| (obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV; obtain ⟨hwok, hwt, hbr⟩ := hw))
local macro "zqni" : tactic => `(tactic| simp only [ChordOK] at hk)
local macro "zqnj" : tactic => `(tactic| simp only [ChordOK] at hk')
local macro "zqnk" : tactic => `(tactic| rintro ⟨hne, hp, h1, h2⟩)
local macro "zqnl" : tactic => `(tactic| (have hk' := hIok _ hwok; zvmxc at hk'; zvmwh at hlt; omega))
local macro "zqnm" : tactic => `(tactic| (simp only [View.key, View.tail] at hk ht; rw [show c = c' from by_grind]))
local macro "zqnn" : tactic => `(tactic| simp only [label])
local macro "zqno" : tactic => `(tactic| have hk := hOK _ hc)
local macro "zqnp" : tactic => `(tactic| rintro ⟨-, hp, h1, h2⟩)
local macro "zqnq" : tactic => `(tactic| (simp only [ViewOK] at hwok; zvnpp at hwt))
local macro "zqnr" : tactic => `(tactic| (intro w' hw'; have hk' := hIok _ hw'))
local macro "zqns" : tactic => `(tactic| exact hNC _ hp _ hc by_omega)
local macro "zqnt" : tactic => `(tactic| exact hNC _ hc _ hp by_omega)
local macro "zqnu" : tactic => `(tactic| (intro w' hw'; have hk' := hOok _ hw'))
local macro "zqnv" : tactic => `(tactic| (rcases c with ⟨a, b⟩; have hk' := hOok _ hwok))
local macro "zqnw" : tactic => `(tactic| (zvmwh at hle; omega))
local macro "zqnx" : tactic => `(tactic| (have hk'' := hOok _ hw'; zvmxc at hk''))
local macro "zqny" : tactic => `(tactic| (have := hIok _ hv'; zvmxc at this))
local macro "zqnz" : tactic => `(tactic| (have := hOok _ hv'; zvmxc at this))
local macro "zqoa" : tactic => `(tactic| (simp only [View.key, View.tail] at hk ht; omega))
local macro "zqob" : tactic => `(tactic| (have hle := hmin _ hwit hwitt ztoc))
local macro "zqoc" : tactic => `(tactic| (have := hall _ hwit hwitt; zvmwh at this; omega))
local macro "zqod" : tactic => `(tactic| (have hk' := hOK _ hc'; zvmxc at hk hk'; ext p; rw [mem_SSup, mem_SSup]; simp only; constructor))
local macro "zqoe" : tactic => `(tactic| rw [show x + N - 1 = ztoka + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega])
local macro "zqof" : tactic => `(tactic| rcases hbr with ⟨hlt, hmin⟩ | ⟨hall, hmin⟩)
local macro "zqog" : tactic => `(tactic| (have := hmin (.outM ztxyg) hw' rfl ztoc))
local macro "zqoh" : tactic => `(tactic| refine ⟨hp, h1, ?_⟩)
local macro "zqoi" : tactic => `(tactic| rcases c with ⟨u, v⟩)
local macro "zqoj" : tactic => `(tactic| (have hk := hIok _ hwok; zvmxc at hk; zvmwh at h0; omega))
local macro "zqok" : tactic => `(tactic| (have hk := hOok _ hwok; zvmxc at hk; zvmwh at h0; omega))
local macro "zqol" : tactic => `(tactic| (have hk := hIok _ hwok; zvmxc at hk; zvmwh at hlt; omega))
local macro "zqom" : tactic => `(tactic| (have := hmin (.inP ztcwt) hw' rfl ztoc))
local macro "zqon" : tactic => `(tactic| (have := hmin (.inM ztcwv) hw' rfl ztoc))
local macro "zqoo" : tactic => `(tactic| (have := hmin (.inM zthky) hw' rfl ztoc))
local macro "zqop" : tactic => `(tactic| (have := hmin (.outP zthdl) hw' rfl ztoc))
local macro "zqoq" : tactic => `(tactic| obtain ⟨f, hf, hfv⟩ := exists_view hw')
local macro "zqor" : tactic => `(tactic| by_contra hlt)
local macro "zqos" : tactic => `(tactic| (simp only; constructor))
local macro "zqot" : tactic => `(tactic| rcases hbr with h | ⟨hall, -⟩)
local macro "zqou" : tactic => `(tactic| obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ B.I from hv))
local macro "zqov" : tactic => `(tactic| obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ B.O from hv))
local macro "zqow" : tactic => `(tactic| obtain ⟨hN, -, -, hIok, hOok, -⟩ := hV)
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), part 3: planarity of two-page book maps

The preprocessing of Lemma 3.6 hands `ClusterSpec` a planar map (`PlanarMapAt`).  The map is
drawn as a **two-page book**: its vertices `0, …, N-1` lie on a circle (the *spine*, a cycle), the
*inner* chords are drawn inside the circle and the *outer* chords outside; the chords of one page
do not cross.  This file builds the combinatorial map of such a drawing and proves it planar.

## The rotation (`csucc`)

A generic construction: darts carry a vertex `g d` and a key `k d` that is injective on each
vertex; the rotation sends a dart to the dart of the next larger key at its vertex, cyclically
(`csucc`, a permutation `csuccPerm` whose cycles are exactly the vertices).

## The book map (`BookData`)

At vertex `x` the darts are ordered by the key: the forward spine dart (to `x + 1`, key `0`), the
inner chords by increasing offset of their other end, the backward spine dart (to `x - 1`, key
`N - 1`), the outer chords by decreasing offset.

## Planarity (`BookData.planar`)

By Euler's inequality (`CombMap.planar_iff`) it suffices to exhibit `E - V + 2` faces.  Each dart
gets a *label*: its page and the set of chords of that page enclosing the face on its left
(`Enc`, `Sup`, `SSup`).  The label is invariant under the face permutation (a case analysis at
the head of the dart, using the non-crossing condition: `label_fperm`), and the `|I| + |O| + 2`
labels `(inner, Sup c)`, `(inner, ∅)`, `(outer, Sup c)`, `(outer, ∅)` are attained and distinct.
-/
namespace Chazelle.Core
@[expose] public section
namespace OracleBook
open Equiv Finset

/-! ## The cyclic successor by key -/
section CSucc
variable {D : Type*} [Fintype D] [DecidableEq D] (g k : D → ℕ)

/-- The darts at the vertex of `d` with a larger key. -/
def above (d : D) : Finset D := Finset.univ.filter (fun e => g e = g d ∧ k d < k e)

/-- The darts at the vertex of `d`. -/
def fiber (d : D) : Finset D := Finset.univ.filter (fun e => g e = g d)
omit [DecidableEq D] in
theorem mem_fiber_self (d : D) : d ∈ fiber g d := by simp [fiber]

/-- A dart of minimal key in a nonempty set. -/
noncomputable def pickMin (s : Finset D) (hs : s.Nonempty) : D :=
  Classical.choose (s.exists_min_image k hs)
omit [Fintype D] [DecidableEq D] in
theorem pickMin_spec (s : Finset D) (hs : s.Nonempty) :
    pickMin k s hs ∈ s ∧ ∀ f ∈ s, k (pickMin k s hs) ≤ k f :=
  Classical.choose_spec (s.exists_min_image k hs)

/-- **The cyclic successor**: the dart of the next larger key at the same vertex, or the dart of
the smallest key if `d` has the largest. -/
noncomputable def csucc (d : D) : D :=
  if h : (above g k d).Nonempty then pickMin k _ h
  else pickMin k zttjz ztkks
omit [DecidableEq D] in
/-- Characterisation of the cyclic successor. -/
theorem csucc_spec (d : D) : g ztfqr = g d ∧
    ((k d < k ztfqr ∧ ∀ f, g f = g d → k d < k f → k ztfqr ≤ k f) ∨
      (ztibx ∧ ∀ f, g f = g d → k ztfqr ≤ k f)) := by
  unfold csucc
  zus
  · obtain ⟨hm, hmin⟩ := pickMin_spec k _ h
    simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
    exact ⟨hm.1, Or.inl ⟨hm.2, fun f hf hkf => hmin f by_omega⟩⟩
  · obtain ⟨hm, hmin⟩ := pickMin_spec k _ ztkks
    zuenp
    refine ⟨hm, Or.inr ⟨fun f hf => ?_, hmin⟩⟩
    zqor
    exact h ⟨f, by simp [above, hf]; omega⟩
variable {g k}

/-- The key is injective on each vertex. -/
def KeyInj (g k : D → ℕ) : Prop := ∀ a b, g a = g b → k a = k b → a = b
omit [DecidableEq D] in
/-- **Uniqueness**: a dart with the characterising property is the cyclic successor. -/
theorem csucc_eq (hinj : KeyInj g k) {d e : D} (he : g e = g d)
    (h : (k d < k e ∧ ∀ f, g f = g d → k d < k f → k e ≤ k f) ∨
      (ztibx ∧ ∀ f, g f = g d → k e ≤ k f)) : csucc g k d = e := by
  obtain ⟨hg, hs⟩ := csucc_spec g k d
  refine hinj _ _ (hg.trans he.symm) ?_
  grind
omit [DecidableEq D] in
/-- The cyclic successor is injective. -/
theorem csucc_injective (hinj : KeyInj g k) : Function.Injective zttin := by
  zujat
  obtain ⟨ha, hsa⟩ := csucc_spec g k a
  obtain ⟨hb, hsb⟩ := csucc_spec g k b
  rw [hab] at ha hsa
  have hgab := ha.symm.trans hb
  refine hinj a b hgab ?_
  grind

/-- The rotation as a permutation. -/
noncomputable def csuccPerm (hinj : KeyInj g k) : Perm D :=
  Equiv.ofBijective zttin (Finite.injective_iff_bijective.1 (csucc_injective hinj))
omit [DecidableEq D] in
@[simp] theorem csuccPerm_apply (hinj : KeyInj g k) (d : D) : csuccPerm hinj d = csucc g k d :=
  rfl
omit [DecidableEq D] in
/-- The rotation preserves vertices. -/
theorem g_csucc (d : D) : g ztfqr = g d := (csucc_spec g k d).1
omit [DecidableEq D] in
/-- **The rotation cycles are the vertices.** -/
theorem csucc_sameCycle (hinj : KeyInj g k) {d e : D} (h : g d = g e) :
    (csuccPerm hinj).SameCycle d e := by
  -- the dart of smallest key at the vertex
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image zttjz k ztkks
  zuenp
  have key : ∀ n, ∀ x, g x = g d → k x ≤ n → (csuccPerm hinj).SameCycle m x := by
    zugok
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro x hx hxn
    by_cases hlow : ∃ f, g f = g d ∧ k f < k x
    · -- the predecessor `p` of `x`
      obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image
        (Finset.univ.filter (fun f => g f = g d ∧ k f < k x)) k
        (by obtain ⟨f, hf⟩ := hlow; exact ⟨f, by_simp_all⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpmax
      have hsucc : csucc g k p = x := by
        refine csucc_eq hinj (hx.trans hp.1.symm) (Or.inl ⟨hp.2, fun f hf hpf => ?_⟩)
        grind
      have ih' := ih _ by_omega p hp.1 le_rfl
      refine ih'.trans ztfvv
      simp_all
    · push Not at hlow
      have  := hinj m x (hm.trans hx.symm) by_grind
      tauto
  exact (key _ d rfl le_rfl).symm.trans (key _ e h.symm le_rfl)
end CSucc

/-! ## Chords of a page and the enclosure sets -/

/-- A chord `(u, v)` of a page on `N` spine vertices: `u + 2 ≤ v < N`, and not the spine edge
`(0, N - 1)`. -/
def ChordOK (N : ℕ) (c : ℕ × ℕ) : Prop := c.1 + 2 ≤ c.2 ∧ c.2 < N ∧ ¬ (c.1 = 0 ∧ c.2 + 1 = N)

/-- The chords of a page do not cross. -/
def NonCross (L : List ztw) : Prop :=
  ∀ c ∈ L, ∀ c' ∈ L, ¬ (c.1 < c'.1 ∧ c'.1 < c.2 ∧ c.2 < c'.2)

/-- The chords of the page enclosing the spine edge `(x, x + 1)` (none for the closing edge
`(N - 1, 0)`). -/
def Enc (N : ℕ) (L : List ztw) (x : ℕ) : Finset ztw :=
  if x + 1 < N then L.toFinset.filter (fun c => c.1 ≤ x ∧ x + 1 ≤ c.2) else ∅

/-- The chords of the page enclosing the chord `c` (including `c`). -/
def Sup (L : List ztw) (c : ℕ × ℕ) : Finset ztw :=
  L.toFinset.filter (fun c' => c'.1 ≤ c.1 ∧ c.2 ≤ c'.2)

/-- The chords of the page strictly enclosing the chord `c`. -/
def SSup (L : List ztw) (c : ℕ × ℕ) : Finset ztw := (Sup L c).erase c
section Enclosure
variable {N : ℕ} {L : List (ℕ × ℕ)}
variable {p : ℕ × ℕ} {x : ℕ} {u v w : ℕ}
theorem pair_eq {a b : ℕ} (h1 : p.1 = a) (h2 : p.2 = b) : p = ztvk :=
  by grind
theorem mem_pair (hp : p ∈ L) {a : ℕ} (h1 : p.1 = a) : zttet ∈ L := by
  grind
theorem mem_pair' (hp : p ∈ L) {b : ℕ} (h2 : p.2 = b) : (p.1, b) ∈ L := by
  grind
theorem mem_Sup {c p : ℕ × ℕ} : p ∈ Sup L c ↔ p ∈ L ∧ p.1 ≤ c.1 ∧ c.2 ≤ p.2 := by
  simp [Sup]
theorem mem_SSup {c p : ℕ × ℕ} : p ∈ SSup L c ↔ p ≠ c ∧ p ∈ L ∧ p.1 ≤ c.1 ∧ c.2 ≤ p.2 := by
  simp [SSup, Sup]
theorem mem_Enc {p : ℕ × ℕ} :
    p ∈ Enc N L x ↔ x + 1 < N ∧ p ∈ L ∧ p.1 ≤ x ∧ x + 1 ≤ p.2 := by
  unfold Enc
  split_ifs with h <;> zumxk
variable (hNC : NonCross L) (hOK : ∀ c ∈ L, ChordOK N c)
include hNC hOK
theorem encA1 {x w : ℕ} (hc : ztuea ∈ L) (hmin : ∀ w', ztudz ∈ L → w ≤ w') :
    Enc N L x = Sup L ztuea := by
  zqno
  zqni
  zufj
  zukxk
  constructor
  · zqnp
    zqoh
    rcases Nat.lt_or_ge p.1 x with hlt | hge
    · by_contra hlt2
      zqns
    grind
  grind
theorem encA2 {x w : ℕ} (hc : ztudf ∈ L) (hno : ∀ w', ztudz ∉ L)
    (hmin : ∀ w', (w', x) ∈ L → w ≤ w') : Enc N L x = SSup L ztudf := by
  zqno
  zqni
  zufj
  zukxj
  constructor
  · rintro ⟨hx, hp, h1, h2⟩
    have hne : p.1 ≠ x := by_grind
    have hle : p.1 ≤ w := by
      zqor
      zqnt
    grind
  · zqnk
    zufct
    have hp2 : p.2 ≠ x := by_grind
    have := (hOK _ hp).2.1
    grind
omit hNC hOK in
theorem encA3 (_hNC : NonCross L) (hOK : ∀ c ∈ L, ChordOK N c) {x : ℕ} (hx : x < N)
    (hno : ∀ p ∈ L, p.1 ≠ x ∧ p.2 ≠ x) :
    Enc N L x = Enc N L (ztewn % N) := by
  zufj
  rw [mem_Enc, mem_Enc]
  zujdd
  · zujwz
    grind
  · have e : ztewn % N = x - 1 := by
      zqoe
    zui
    constructor
    · grind
    · rintro ⟨h0, hp, h1, h2⟩
      have := hno p hp
      have := (hOK p hp).2.1
      grind
theorem encB1 (hc : ztnz ∈ L) (hc' : ztkgt ∈ L) (huw : u < w)
    (hmin : ∀ w', ztcwv ∈ L → u < w' → w ≤ w') : Sup L ztnz = SSup L ztkgt := by
  have hk := hOK _ hc'
  zqni
  zufj
  rw [mem_Sup, mem_SSup]
  zqos
  · grind
  · zqnk
    refine ztkln
    zqor
    zuebq
    · zqnt
    grind
theorem encB2 {u v : ℕ} (hc : ztnz ∈ L) (hno : ∀ w', ztcwv ∈ L → w' ≤ u) :
    Sup L ztnz = Enc N L (v - 1) := by
  zqno
  zqni
  zufj
  rw [mem_Sup, mem_Enc]
  zqos
  · grind
  · zqnp
    refine ⟨hp, ?_, by_omega⟩
    zqor
    zuebq
    · zqnt
    grind
theorem encC1 (hc : ztnz ∈ L) (hc' : ztfuz ∈ L) (hvw : v < w)
    (hmin : ∀ w', ztcwt ∈ L → v < w' → w ≤ w') : SSup L ztnz = Sup L ztfuz := by
  zqno
  zqni
  zufj
  rw [mem_SSup, mem_Sup]
  zqos
  · zqnk
    zqoh
    rcases Nat.lt_or_ge p.1 u with hlt | hge
    · by_contra hlt2
      zuitl
    grind
  grind
theorem encC2 (hc : ztnz ∈ L) (hc' : ztkgs ∈ L)
    (hno : ∀ w', ztcwt ∈ L → w' ≤ v) (hmin : ∀ w', ztkgr ∈ L → w ≤ w') :
    SSup L ztnz = SSup L ztkgs := by
  zqno
  zqod
  · zqnk
    have hp1 : p.1 ≠ u := by_grind
    have hle : p.1 ≤ w := by
      zqor
      exact hNC _ hc' _ hp by_omega
    grind
  · zqnk
    zuhzt
    have hge : v ≤ p.2 := by
      zqor
      zqns
    grind
theorem encC3 {u v : ℕ} (hc : ztnz ∈ L) (hno : ∀ w', ztcwt ∈ L → w' ≤ v)
    (hno2 : ∀ w', ztkgr ∉ L) : SSup L ztnz = Enc N L (ztkgh % N) := by
  zqno
  zqni
  have hp1 : ∀ p ∈ L, p ≠ ztnz → p.1 ≤ u → v ≤ p.2 → p.1 ≠ u := by_grind
  zufj
  zukxm
  zubi
  rcases Nat.eq_zero_or_pos u with hu | hpos
  · have e : ztkgh % N = N - 1 := by
      simp_all
    grind
  · have e : ztkgh % N = u - 1 := by
      rw [show u + N - 1 = ztewa + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    zui
    constructor
    · grind
    · zqnp
      zuhzt
      have hge : v ≤ p.2 := by
        zqor
        zqns
      grind
theorem encD1 {x w : ℕ} (hx : x < N) (hc : ztzhl ∈ L)
    (hmax : ∀ w', ztzhk ∈ L → w' ≤ w) : Enc N L x = Sup L ztzhl := by
  zqno
  zqni
  have hx1 : x + 1 < N := by
    zumv
    have : ztzrd := by zunkk
    omega
  zulhc
  zvmwe at hc hmax ⊢
  zufj
  zukxk
  zqos
  · zqnp
    refine ztkln
    rcases Nat.lt_or_ge zthf p.2 with hv | hv
    · zqor
      zqnt
    grind
  grind
theorem encD2 {x w : ℕ} (hx : x < N) (hc : ztzht ∈ L)
    (hno : ∀ w', ztzhk ∉ L) (hmax : ∀ w', (zthf % N, w') ∈ L → w' ≤ w) :
    Enc N L x = SSup L ztzht := by
  zqno
  zqni
  zufj
  zukxj
  zubi
  by_cases hx1 : x + 1 < N
  · zulhc
    zvmwe at hc hno hmax hk ⊢
    constructor
    · zqnp
      have hp2 : p.2 ≠ x + 1 := by_grind
      have hge : w ≤ p.2 := by
        zqor
        zqns
      grind
    grind
  · have e : ztzrd := by zunkk
    grind
theorem encD3 (hx : x < N) (hno : ∀ p ∈ L, p.1 ≠ zthf % N ∧ p.2 ≠ zthf % N) :
    Enc N L x = Enc N L (zthf % N) := by
  zuftq
  rw [encA3 hNC hOK ztjkk hno]
  zucr
  rcases Nat.lt_or_ge zthf N with h | h
  · rw [Nat.mod_eq_of_lt h, show x + 1 + N - 1 = x + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]
  · rw [show x + 1 = N by omega, Nat.mod_self, zero_add, Nat.mod_eq_of_lt by_omega]
    omega
theorem encE1 (hc : ztnz ∈ L) (hc' : ztfuz ∈ L) (hwv : w < v)
    (hmax : ∀ w', ztcwt ∈ L → w' < v → w' ≤ w) : Sup L ztnz = SSup L ztfuz := by
  have hk := hOK _ hc'
  zqni
  zufj
  rw [mem_Sup, mem_SSup]
  zqos
  · grind
  · zqnk
    zqoh
    zqor
    zuebp
    · zqns
    grind
theorem encE2 {u v : ℕ} (hc : ztnz ∈ L) (hno : ∀ w', ztcwt ∈ L → v ≤ w') :
    Sup L ztnz = Enc N L u := by
  zqno
  zqni
  zufj
  rw [mem_Sup, mem_Enc]
  zqos
  · grind
  · zqnp
    zqoh
    zqor
    zuebp
    · zqns
    grind
theorem encF1 (hc : ztnz ∈ L) (hc' : ztkgt ∈ L) (hwu : w < u)
    (hmax : ∀ w', ztcwv ∈ L → w' < u → w' ≤ w) : SSup L ztnz = Sup L ztkgt := by
  zqno
  zqni
  zufj
  rw [mem_SSup, mem_Sup]
  zqos
  · zqnk
    refine ztkln
    zuebp
    · zuebq
      · zqor
        exact hNC _ hc' _ hp by_omega
      grind
    · zuhzu
      exact absurd (hNC _ hc' _ hp) by_omega
  grind
theorem encF2 (hc : ztnz ∈ L) (hc' : ztucq ∈ L)
    (hno : ∀ w', ztcwv ∈ L → u ≤ w') (hmax : ∀ w', ztfvd ∈ L → w' ≤ w) :
    SSup L ztnz = SSup L ztucq := by
  zqno
  zqod
  · zqnk
    zuhzu
    have hge : w ≤ p.2 := by
      zqor
      zuitl
    grind
  · zqnk
    zuhzp
    have hle : p.1 ≤ u := by
      zqor
      zqnt
    grind
theorem encF3 {u v : ℕ} (hc : ztnz ∈ L) (hno : ∀ w', ztcwv ∈ L → u ≤ w')
    (hno2 : ∀ w', ztfvd ∉ L) : SSup L ztnz = Enc N L v := by
  zqno
  zqni
  have hp2 : ∀ p ∈ L, p ≠ ztnz → p.1 ≤ u → p.2 ≠ v := by_grind
  zufj
  zukxm
  zqos
  · zqnk
    have := hp2 p hp hne h1
    have := (hOK p hp).2.1
    grind
  · zqnp
    zuhzp
    have hle : p.1 ≤ u := by
      zqor
      zqnt
    grind
end Enclosure

/-! ## Darts of a book map -/

/-- A dart of a book map, by kind: forward and backward spine darts of the spine edge
`(x, x + 1 mod N)`, the two darts `(u → v)`, `(v → u)` of an inner chord `(u, v)`, of an outer
chord. -/
inductive View where
  | spF (x : ℕ)
  | spB (x : ℕ)
  | inP (c : ℕ × ℕ)
  | inM (c : ℕ × ℕ)
  | outP (c : ℕ × ℕ)
  | outM (c : ℕ × ℕ)
  deriving DecidableEq
namespace View

/-- The tail (vertex) of a dart. -/
def tail (N : ℕ) : View → ℕ
  | spF x => x
  | spB x => zthf % N
  | inP c => c.1
  | inM c => c.2
  | outP c => c.1
  | outM c => c.2

/-- The head of a dart. -/
def head (N : ℕ) : View → ℕ
  | spF x => zthf % N
  | spB x => x
  | inP c => c.2
  | inM c => c.1
  | outP c => c.2
  | outM c => c.1

/-- The key of a dart at its tail: forward spine `0`, inner chords by increasing offset of the
head (`2 … N - 2`), backward spine `N - 1`, outer chords by decreasing offset (`N … 2 N - 4`). -/
def key (N : ℕ) : View → ℕ
  | spF _ => 0
  | spB _ => N - 1
  | inP c => c.2 - c.1
  | inM c => N - c.2 + c.1
  | outP c => 2 * N - 2 - (c.2 - c.1)
  | outM c => N - 2 + c.2 - c.1

/-- The opposite dart. -/
def rev : View → View
  | spF x => spB x
  | spB x => spF x
  | inP c => inM c
  | inM c => inP c
  | outP c => outM c
  | outM c => outP c
theorem tail_rev (N : ℕ) (v : View) : tail N v.rev = head N v := by cases v <;> rfl
end View

/-- **Data of a two-page book map**: `N` spine vertices, the inner and the outer chords. -/
structure BookData where
  /-- The number of spine vertices. -/
  N : ℕ
  /-- The inner chords. -/
  I : List ztw
  /-- The outer chords. -/
  O : List ztw
namespace BookData
variable (B : BookData)

/-- Validity: at least three spine vertices, distinct well-formed chords, no crossing within a
page. -/
def Valid : Prop :=
  3 ≤ B.N ∧ B.I.Nodup ∧ B.O.Nodup ∧ (∀ c ∈ B.I, ChordOK B.N c) ∧ (∀ c ∈ B.O, ChordOK B.N c) ∧
    NonCross B.I ∧ NonCross B.O

/-- The number of edges. -/
def E : ℕ := B.N + B.I.length + B.O.length

/-- The dart `d` (edge `d / 2`, direction `d % 2`) by kind: spine edges `0 … N - 1`, then the
inner chords, then the outer chords. -/
def view (d : ℕ) : View :=
  if d / 2 < B.N then (if d % 2 = 0 then .spF ztcmw else .spB ztcmw)
  else if d / 2 < B.N + B.I.length then
    (if d % 2 = 0 then .inP ztzsx
      else .inM ztzsx)
  else (if d % 2 = 0 then .outP ztzsy
      else .outM ztzsy)

/-- The darts that exist. -/
def ViewOK : View → Prop
  | .spF x => x < B.N
  | .spB x => x < B.N
  | .inP c => c ∈ B.I
  | .inM c => c ∈ B.I
  | .outP c => c ∈ B.O
  | .outM c => c ∈ B.O

/-- **The face label** of a dart: its page and the chords of that page enclosing the face on its
left. -/
def label : View → Bool × Finset ztw
  | .spF x => (false, Enc B.N B.O x)
  | .spB x => (true, Enc B.N B.I x)
  | .inP c => (true, Sup B.I c)
  | .inM c => (true, SSup B.I c)
  | .outP c => (false, SSup B.O c)
  | .outM c => (false, Sup B.O c)

/-- `w` is the next dart after key `k₀` at vertex `t`, cyclically. -/
def IsNext (t k₀ : ℕ) (w : View) : Prop :=
  B.ViewOK w ∧ View.tail B.N w = t ∧
    ((k₀ < View.key B.N w ∧ ∀ w', B.ViewOK w' → View.tail B.N w' = t → k₀ < View.key B.N w' →
        View.key B.N w ≤ View.key B.N w') ∨
      ((∀ w', B.ViewOK w' → View.tail B.N w' = t → View.key B.N w' ≤ k₀) ∧
        ∀ w', B.ViewOK w' → View.tail B.N w' = t → View.key B.N w ≤ View.key B.N w'))
theorem pred_mod_eq {N x : ℕ} (hx : x < N) (hx0 : 1 ≤ x) : ztewn % N = x - 1 := by
  zqoe
theorem pred_mod_zero {N : ℕ} (hN : 1 ≤ N) : (0 + N - 1) % N = N - 1 := by
  simp

/-- The backward spine dart into `x` from `x - 1` has tail... (the spine dart `(x - 1, x)`
reversed): its tail is `x`. -/
theorem tail_spB_pred {N x : ℕ} (hx : x < N) : (ztewn % N + 1) % N = x := by
  zujdd
  · rw [pred_mod_zero by_omega, Nat.sub_add_cancel by_omega, Nat.mod_self]
  · rw [pred_mod_eq hx hpos, Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hx]

/-- A spine vertex whose successor is `x` is `x - 1 mod N`. -/
theorem eq_pred_of_succ {N x y : ℕ} (hy : y < N) (h : zthlg % N = x) : y = ztewn % N := by
  rcases Nat.lt_or_ge zthlg N with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at h
    zubst
    rw [show y + 1 + N - 1 = y + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  · rw [show y + 1 = N by omega, Nat.mod_self] at h
    zubst
    rw [pred_mod_zero by_omega]
    omega

/-! ## Invariance of the face label -/
section Label
variable {B}

/-- Around a backward spine dart. -/
theorem label_next_spB (hV : B.Valid) {x : ℕ} (hx : x < B.N) {w : View}
    (hw : B.IsNext x 0 w) : B.label w = B.label (.spB x) := by
  zqnh
  have hwit : B.ViewOK (.spB ((x + B.N - 1) % B.N)) := Nat.mod_lt _ by_omega
  have hwitt : View.tail B.N ztpsc = x := tail_spB_pred hx
  obtain ⟨hpos, hmin⟩ : 0 < View.key B.N w ∧ ∀ w', B.ViewOK w' → View.tail B.N w' = x →
      0 < View.key B.N w' → View.key B.N w ≤ View.key B.N w' := by
    zqot
    · zubh
    · zqoc
  zqob
  cases w with
  | spF y => simp [View.key] at hpos
  | spB y =>
    zqnq
    have hy := eq_pred_of_succ hwok hwt
    have hno : ∀ p ∈ B.I, p.1 ≠ x ∧ p.2 ≠ x := by
      zuda
      have hk := hIok p hp
      zqni
      constructor
      · zudqd
        have := hmin (.inP p) hp h1 ztoc
        zqnf
      · zukji
        have := hmin (.inM p) hp h2 ztoc
        zqnf
    zqnn
    rw [hy, ← encA3 hInc hIok hx hno]
  | inP c =>
    zqoi
    zqnq
    subst hwt
    have hmin2 : ∀ w', ztcwt ∈ B.I → v ≤ w' := by
      zulnm
      have hk := hIok _ hw'
      zqni
      zqom
      zqnf
    zqnn
    rw [encA1 hInc hIok hwok hmin2]
  | inM c =>
    zqoi
    zqnq
    subst hwt
    have hk := hIok _ hwok
    zqni
    have hno : ∀ w', ztfvd ∉ B.I := by
      zqnr
      zqnj
      have := hmin (.inP ztfvd) hw' rfl ztoc
      zqnf
    have hmin2 : ∀ w', ztcwv ∈ B.I → u ≤ w' := by
      zqnr
      zqnj
      zqon
      zqnf
    zqnn
    rw [encA2 hInc hIok hwok hno hmin2]
  | outP c =>
    zqoi
    have hk := hOok _ hwok
    zqni
    zqnw
  | outM c =>
    zqoi
    have hk := hOok _ hwok
    zqni
    zqnw

/-- Around the forward dart of an inner chord. -/
theorem label_next_inP (hV : B.Valid) {u v : ℕ} (hc : ztnz ∈ B.I) {w : View}
    (hw : B.IsNext v (B.N - v + u) w) : B.label w = B.label (.inP ztnz) := by
  zqnh
  have hk := hIok _ hc
  zqni
  have hvN := hk.2.1
  have hwit : B.ViewOK (.spB ((v + B.N - 1) % B.N)) := Nat.mod_lt _ by_omega
  have hwitt : View.tail B.N ztpsc = v := tail_spB_pred hvN
  obtain ⟨hpos, hmin⟩ : B.N - v + u < View.key B.N w ∧ ∀ w', B.ViewOK w' →
      View.tail B.N w' = v → B.N - v + u < View.key B.N w' →
        View.key B.N w ≤ View.key B.N w' := by
    zqot
    · zubh
    · zqoc
  zqob
  cases w with
  | spF y => zvmwh at hpos; omega
  | spB y =>
    zqnq
    have hy := eq_pred_of_succ hwok hwt
    rw [pred_mod_eq hvN by_omega] at hy
    have hno : ∀ w', ztcwv ∈ B.I → w' ≤ u := by
      zqnr
      zqnj
      zqor
      zqon
      zqnf
    zqnn
    rw [hy, encB2 hInc hIok hc hno]
  | inP c =>
    zuidw
    simp only [ViewOK] at hwok
    have hk' := hIok _ hwok
    zqnj
    zujod
    zvmwh at hpos; omega
  | inM c =>
    zqng
    simp only [View.key] at hpos
    have hmin2 : ∀ w', zthky ∈ B.I → u < w' → a ≤ w' := by
      intro w' hw' huw
      have hk' := hIok _ hw'
      zqnj
      zqoo
      zqnf
    zqnn
    rw [encB1 hInc hIok hc hwok by_omega hmin2]
  | outP c =>
    zqnv
    zqnj
    zqnw
  | outM c =>
    zqnv
    zqnj
    zqnw

/-- Around the backward dart of an inner chord. -/
theorem label_next_inM (hV : B.Valid) {u v : ℕ} (hc : ztnz ∈ B.I) {w : View}
    (hw : B.IsNext u ztbnr w) : B.label w = B.label (.inM ztnz) := by
  zqnh
  have hk := hIok _ hc
  zqni
  have huN : u < B.N := by_omega
  have hwit : B.ViewOK (.spB ((u + B.N - 1) % B.N)) := Nat.mod_lt _ by_omega
  have hwitt : View.tail B.N ztpsc = u := tail_spB_pred huN
  obtain ⟨hpos, hmin⟩ : v - u < View.key B.N w ∧ ∀ w', B.ViewOK w' →
      View.tail B.N w' = u → v - u < View.key B.N w' →
        View.key B.N w ≤ View.key B.N w' := by
    zqot
    · zubh
    · zqoc
  zqob
  cases w with
  | spF y => zvmwh at hpos; omega
  | spB y =>
    zqnq
    have hy := eq_pred_of_succ hwok hwt
    have hno : ∀ w', ztcwt ∈ B.I → w' ≤ v := by
      zqnr
      zqnj
      zqor
      zqom
      zqnf
    have hno2 : ∀ w', ztkgr ∉ B.I := by
      zqnr
      zqnj
      have := hmin (.inM ztkgr) hw' rfl ztoc
      zqnf
    zqnn
    rw [hy, encC3 hInc hIok hc hno hno2]
  | inP c =>
    zqng
    simp only [View.key] at hpos
    have hmin2 : ∀ w', zthdl ∈ B.I → v < w' → b ≤ w' := by
      intro w' hw' hvw
      have hk' := hIok _ hw'
      zqnj
      have := hmin (.inP zthdl) hw' rfl ztoc
      zqnf
    zqnn
    rw [encC1 hInc hIok hc hwok by_omega hmin2]
  | inM c =>
    zqng
    have hkw := hIok _ hwok
    zvmxc at hkw
    have hno : ∀ w', zttfp ∈ B.I → w' ≤ v := by
      zqnr
      zqnj
      zqor
      have := hmin (.inP zttfp) hw' rfl ztoc
      zqnf
    have hmin2 : ∀ w', zthky ∈ B.I → a ≤ w' := by
      zqnr
      zqnj
      zqoo
      zqnf
    zqnn
    rw [encC2 hInc hIok hc hwok hno hmin2]
  | outP c =>
    zqnv
    zqnj
    zqnw
  | outM c =>
    zqnv
    zqnj
    zqnw

/-- In the wrap-around case at a vertex `t`, the next dart is the forward spine dart. -/
theorem eq_spF_of_wrap (hV : B.Valid) {t : ℕ} (ht : t < B.N) {w : View} (hwok : B.ViewOK w)
    (hwt : View.tail B.N w = t)
    (hmin : ∀ w', B.ViewOK w' → View.tail B.N w' = t → View.key B.N w ≤ View.key B.N w') :
    w = .spF t := by
  obtain ⟨hN, -, -, hIok, hOok, -, -⟩ := hV
  have h0 := hmin (.spF t) ht rfl
  cases w with
  | spF y => zvnpp at hwt; rw [hwt]
  | spB y => zvmwh at h0; omega
  | inP c =>
    zqoj
  | inM c =>
    zqoj
  | outP c =>
    zqok
  | outM c =>
    zqok

/-- Around a forward spine dart. -/
theorem label_next_spF (hV : B.Valid) {x : ℕ} (hx : x < B.N) {w : View}
    (hw : B.IsNext (zthf % B.N) ztnjo w) : B.label w = B.label (.spF x) := by
  have hV' := hV
  zqnh
  have hhN : zthf % B.N < B.N := Nat.mod_lt _ by_omega
  zqof
  · cases w with
    | spF y => zvmwh at hlt; omega
    | spB y => zvmwh at hlt; omega
    | inP c =>
      zqol
    | inM c =>
      zqol
    | outM c =>
      zqng
      have hmax : ∀ w', ztxyg ∈ B.O → w' ≤ a := by
        zqnu
        zqnj
        zqog
        zqnf
      zqnn
      rw [encD1 hOnc hOok hx hwok hmax]
    | outP c =>
      zqng
      have hk := hOok _ hwok
      zqni
      have hno : ∀ w', ztxyg ∉ B.O := by
        zqnu
        zqnj
        zqog
        zqnf
      have hmax : ∀ w', ztzhs ∈ B.O → w' ≤ b := by
        zqnu
        zqnj
        have := hmin (.outP ztzhs) hw' rfl ztoc
        zqnf
      zqnn
      rw [encD2 hOnc hOok hx hwok hno hmax]
  · have hw := eq_spF_of_wrap hV' hhN hwok hwt hmin
    subst hw
    have hno : ∀ p ∈ B.O, p.1 ≠ zthf % B.N ∧ p.2 ≠ zthf % B.N := by
      zuda
      have hk := hOok p hp
      zqni
      constructor
      · zudqd
        have := hall (.outP p) hp h1
        zqnf
      · zukji
        have := hall (.outM p) hp h2
        zqnf
    zqnn
    rw [encD3 hOnc hOok hx hno]

/-- Around the backward dart of an outer chord. -/
theorem label_next_outM (hV : B.Valid) {u v : ℕ} (hc : ztnz ∈ B.O) {w : View}
    (hw : B.IsNext u (2 * B.N - 2 - ztbnr) w) : B.label w = B.label (.outM ztnz) := by
  have hV' := hV
  zqnh
  have hk := hOok _ hc
  zqni
  zqof
  · cases w with
    | spF y => zvmwh at hlt; omega
    | spB y => zvmwh at hlt; omega
    | inP c =>
      zqnl
    | inM c =>
      zqnl
    | outM c =>
      zuidw
      have hk' := hOok _ hwok; zvmxc at hk'
      zujod
      zvmwh at hlt; omega
    | outP c =>
      zqng
      have hk' := hOok _ hwok
      zqnj
      zujoc
      have hmax : ∀ w', zthdl ∈ B.O → w' < v → w' ≤ b := by
        intro w' hw' hwv
        zqnx
        zqop
        zqnf
      zqnn
      rw [encE1 hOnc hOok hc hwok by_omega hmax]
  · zufwt

    have hno : ∀ w', ztcwt ∈ B.O → v ≤ w' := by
      zqnu
      zqnj
      zqor
      have := hall (.outP ztcwt) hw' rfl
      zqnf
    zqnn
    rw [encE2 hOnc hOok hc hno]

/-- Around the forward dart of an outer chord. -/
theorem label_next_outP (hV : B.Valid) {u v : ℕ} (hc : ztnz ∈ B.O) {w : View}
    (hw : B.IsNext v (B.N - 2 + v - u) w) : B.label w = B.label (.outP ztnz) := by
  have hV' := hV
  zqnh
  have hk := hOok _ hc
  zqni
  zqof
  · cases w with
    | spF y => zvmwh at hlt; omega
    | spB y => zvmwh at hlt; omega
    | inP c =>
      zqnl
    | inM c =>
      zqnl
    | outM c =>
      zqng
      have hk' := hOok _ hwok
      zqnj
      zujoc
      have hmax : ∀ w', zthky ∈ B.O → w' < u → w' ≤ a := by
        intro w' hw' hwu
        zqnx
        have := hmin (.outM zthky) hw' rfl ztoc
        zqnf
      zqnn
      rw [encF1 hOnc hOok hc hwok by_omega hmax]
    | outP c =>
      zqng
      have hk' := hOok _ hwok
      zqnj
      have hno : ∀ w', ztude ∈ B.O → u ≤ w' := by
        zulnm
        zqnx
        by_contra hlt'
        have := hmin (.outM ztude) hw' rfl ztoc
        zqnf
      have hmax : ∀ w', zthdl ∈ B.O → w' ≤ b := by
        zulnm
        zqnx
        zqop
        zqnf
      zqnn
      rw [encF2 hOnc hOok hc hwok hno hmax]
  · zufwt

    have hno : ∀ w', ztcwv ∈ B.O → u ≤ w' := by
      zqnu
      zqnj
      zqor
      have := hall (.outM ztcwv) hw' rfl
      zqnf
    have hno2 : ∀ w', ztfvd ∉ B.O := by
      zqnu
      zqnj
      have := hall (.outP ztfvd) hw' rfl
      zqnf
    zqnn
    rw [encF3 hOnc hOok hc hno hno2]

/-- **The face label is invariant**: the dart following the reverse of `v` at the head of `v`
has the label of `v`. -/
theorem label_next (hV : B.Valid) {v : View} (hv : B.ViewOK v) {w : View}
    (hw : B.IsNext zttdz (View.key B.N v.rev) w) : B.label w = B.label v := by
  cases v with
  | spF x => exact label_next_spF hV hv hw
  | spB x => exact label_next_spB hV hv hw
  | inP c => rcases c with ⟨u, v⟩; exact label_next_inP hV hv hw
  | inM c => rcases c with ⟨u, v⟩; exact label_next_inM hV hv hw
  | outP c => rcases c with ⟨u, v⟩; exact label_next_outP hV hv hw
  | outM c => rcases c with ⟨u, v⟩; exact label_next_outM hV hv hw
end Label

/-! ## Darts as numbers -/
variable {α : Type*} {c : Prop}
theorem ite_t [Decidable c] (h : c) (a b : α) :
    ztpch = a := by zumxk
theorem ite_f [Decidable c] (h : ¬ c) (a b : α) :
    ztpch = b := by zumxk
section Darts
variable {B}
theorem getD_mem {L : List ztw} {i : ℕ} (hi : i < L.length) : L.getD i ztdr ∈ L := by
  simp_all
theorem getD_eq {L : List ztw} {i : ℕ} (hi : i < L.length) : L.getD i ztdr = L[i] := by
  simp_all
variable {d : ℕ}
/-- Every dart has a kind that exists. -/
theorem view_ok (hd : d < 2 * B.E) : B.ViewOK ztbgk := by
  unfold view E at *
  split_ifs with h1 h2 h3 h4 h5 <;> simp only [ViewOK]
  · zubvv
  · zubvv
  · grind
  · grind
  · grind
  grind

/-- Every existing kind is a dart. -/
theorem exists_view {v : View} (hv : B.ViewOK v) : ∃ d, d < 2 * B.E ∧ B.view d = v := by
  unfold E
  cases v with
  | spF x =>
    refine ⟨2 * x, by simp only [ViewOK] at hv; omega, ?_⟩
    zujoe
    zuefa
    zuila
    zugjy
  | spB x =>
    refine ⟨2 * x + 1, by simp only [ViewOK] at hv; omega, ?_⟩
    zujoe
    zuefa
    rw [ite_t by_omega, ite_f by_omega]
    zugjy
  | inP c =>
    zqou
    refine ⟨2 * ztjgs, by_omega, ?_⟩
    zuefa
    rw [ite_f by_omega, ite_t by_omega, ite_t by_omega,
      show 2 * ztjgs / 2 - B.N = i by omega, getD_eq hi]
  | inM c =>
    zqou
    refine ⟨2 * ztjgs + 1, by_omega, ?_⟩
    zuefa
    rw [ite_f by_omega, ite_t by_omega, ite_f by_omega,
      show (2 * ztjgs + 1) / 2 - B.N = i by omega, getD_eq hi]
  | outP c =>
    zqov
    refine ⟨2 * ztgdc, by_omega, ?_⟩
    zuefa
    rw [ite_f by_omega, ite_f by_omega, ite_t by_omega,
      show 2 * ztgdc / 2 - B.N - B.I.length = i by omega, getD_eq hi]
  | outM c =>
    zqov
    refine ⟨2 * ztgdc + 1, by_omega, ?_⟩
    zuefa
    rw [ite_f by_omega, ite_f by_omega, ite_f by_omega,
      show (2 * ztgdc + 1) / 2 - B.N - B.I.length = i by omega, getD_eq hi]

/-- Distinct darts have distinct kinds. -/
theorem view_inj (hV : B.Valid) {d d' : ℕ} (hd : d < 2 * B.E) (hd' : d' < 2 * B.E)
    (h : B.view d = B.view d') : d = d' := by
  obtain ⟨-, hIn, hOn, -⟩ := hV
  unfold E at hd hd'
  unfold view at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;> simp only [View.spF.injEq,
    View.spB.injEq, View.inP.injEq, View.inM.injEq, View.outP.injEq, View.outM.injEq] at h <;> first
    | omega
    | (rw [getD_eq by_omega, getD_eq by_omega, hIn.getElem_inj_iff] at h; omega)
    | (rw [getD_eq by_omega, getD_eq by_omega, hOn.getElem_inj_iff] at h; omega)

/-- The opposite dart as a number. -/
def oppN (d : ℕ) : ℕ := if d % 2 = 0 then d + 1 else d - 1
theorem oppN_lt (hd : d < 2 * B.E) : oppN d < 2 * B.E := by
  zufdk
theorem oppN_oppN (d : ℕ) : oppN ztwbb = d := by
  zufdk
theorem oppN_ne (d : ℕ) : oppN d ≠ d := by
  zufdk
theorem view_oppN (d : ℕ) : B.view ztwbb = (B.view d).rev := by
  have h1 : oppN d / 2 = d / 2 := by unfold oppN; grind
  have h2 : oppN d % 2 = 0 ↔ ¬ d % 2 = 0 := by unfold oppN; grind
  zuefa
  zuwv
  by_cases hp : d % 2 = 0
  · have hq : ¬ oppN d % 2 = 0 := by_omega
    zuenq

  · have hq := h2.2 hp
    zuenq
theorem tail_lt (hV : B.Valid) {v : View} (hv : B.ViewOK v) : View.tail B.N v < B.N := by
  zqow
  cases v with
  | spF x => exact hv
  | spB x => exact Nat.mod_lt _ by_omega
  | inP c => have := (hIok _ hv).2.1; have := (hIok _ hv).1; zvnpp; omega
  | inM c => exact (hIok _ hv).2.1
  | outP c => have := (hOok _ hv).2.1; have := (hOok _ hv).1; zvnpp; omega
  | outM c => exact (hOok _ hv).2.1

/-- **Keys are injective at a vertex.** -/
theorem key_inj (hV : B.Valid) {v v' : View} (hv : B.ViewOK v) (hv' : B.ViewOK v')
    (ht : View.tail B.N v = View.tail B.N v') (hk : View.key B.N v = View.key B.N v') :
    v = v' := by
  zqow
  cases v with
  | spF x =>
    cases v' with
    | spF y => zvnpp at ht; zvnup
    | spB y => zvmwh at hk; omega
    | inP c => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | inM c => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outP c => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outM c => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
  | spB x =>
    cases v' with
    | spF y => zvmwh at hk; omega
    | spB y =>
      simp only [ViewOK] at hv hv'
      zvnpp at ht
      have e1 := eq_pred_of_succ hv rfl
      have e2 := eq_pred_of_succ hv' rfl
      rw [e1, e2, ht]
    | inP c => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | inM c => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outP c => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outM c => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
  | inP c =>
    zuegh
    cases v' with
    | spF y => zvmwh at hk; omega
    | spB y => zvmwh at hk; omega
    | inP c' =>
      zqny
      zqnm
    | inM c' =>
      zqny
      zqoa
    | outP c' => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outM c' => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
  | inM c =>
    zuegh
    cases v' with
    | spF y => zvmwh at hk; omega
    | spB y => zvmwh at hk; omega
    | inP c' =>
      zqny
      zqoa
    | inM c' =>
      zqny
      zqnm
    | outP c' => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outM c' => have := hOok _ hv'; zvmxc at this; zvmwh at hk; omega
  | outP c =>
    zuegi
    cases v' with
    | spF y => zvmwh at hk; omega
    | spB y => zvmwh at hk; omega
    | inP c' => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | inM c' => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outP c' =>
      zqnz
      zqnm
    | outM c' =>
      zqnz
      zqoa
  | outM c =>
    zuegi
    cases v' with
    | spF y => zvmwh at hk; omega
    | spB y => zvmwh at hk; omega
    | inP c' => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | inM c' => have := hIok _ hv'; zvmxc at this; zvmwh at hk; omega
    | outP c' =>
      zqnz
      zqoa
    | outM c' =>
      zqnz
      zqnm
end Darts

/-! ## The map and its planarity -/
section Map
variable {B}

/-- The vertex of a dart (as a number). -/
def gN (d : Fin ztbck) : ℕ := View.tail B.N ztbgk

/-- The key of a dart (as a number). -/
def kN (d : Fin ztbck) : ℕ := View.key B.N ztbgk
theorem keyInj (hV : B.Valid) : KeyInj (gN (B := B)) (kN (B := B)) := by
  intro a b hg hk
  exact Fin.ext (view_inj hV a.2 b.2 (key_inj hV (view_ok a.2) (view_ok b.2) hg hk))

/-- The rotation of the book map. -/
noncomputable def rotP (hV : B.Valid) : Perm ztyho := csuccPerm ztqsk

/-- The opposite dart as a permutation. -/
def oppP : Perm ztyho :=
  Function.Involutive.toPerm (fun d => ⟨oppN d, oppN_lt d.2⟩)
    (fun d => Fin.ext (oppN_oppN d))
@[simp] theorem oppP_val (d : Fin (2 * B.E)) : ((oppP (B := B)) d).1 = oppN d := rfl

/-- The face permutation `rot ∘ opp` of the book map. -/
noncomputable def fpermP (hV : B.Valid) : Perm ztyho := rotP hV * oppP

/-- **The face label is invariant under the face permutation.** -/
theorem label_fperm (hV : B.Valid) (d : Fin ztbck) :
    B.label (B.view (fpermP hV d)) = B.label ztbgk := by
  set e := oppP d with he
  have hev : B.view e = (B.view d).rev := by rw [he, oppP_val]; exact view_oppN d
  have hspec := csucc_spec (gN) (kN) e
  have hnext : B.IsNext (View.head B.N ztbgk) (View.key B.N (B.view d).rev)
      (B.view (csucc (gN) (kN) e).1) := by
    have hge : gN e = View.head B.N ztbgk := by
      unfold gN; rw [hev, View.tail_rev]
    have hke : kN e = View.key B.N (B.view d).rev := by unfold kN; rw [hev]
    obtain ⟨hg, hs⟩ := hspec
    refine ⟨view_ok by_omega, by rw [← hge]; exact hg, ?_⟩
    rw [← hke, ← hge]
    zuejz
    · refine Or.inl ⟨h1, fun w' hw' ht hk => ?_⟩
      zqoq
      have := h2 zthmy ztdml
        (by unfold kN; simp_all)
      zudwi
    · refine Or.inr ⟨fun w' hw' ht => ?_, fun w' hw' ht => ?_⟩
      · zqoq
        have := h1 zthmy ztdml
        unfold kN at this; simp_all
      · zqoq
        have := h2 zthmy ztdml
        zudwi
  exact label_next hV ztqyi hnext

/-- The label is constant on the cycles of the face permutation. -/
theorem label_sameCycle (hV : B.Valid) {a b : Fin ztbck} (h : (fpermP hV).SameCycle a b) :
    B.label ztuwl = B.label (B.view b) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  have key : ∀ n : ℕ, B.label (B.view ((fpermP hV ^ n) a)) = B.label ztuwl := by
    zugok
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, label_fperm, ih]
  simp_all

/-- The faces of the book map: the cycles of the face permutation. -/
abbrev FaceT (hV : B.Valid) : Type := Quotient (Perm.SameCycle.setoid (fpermP hV))

/-- **The book map.** -/
noncomputable def map (hV : B.Valid) :
    Separator.CombMap ztuyi ztmax ztyho where
  rot := rotP hV
  opp := oppP
  vert d := ⟨gN d, tail_lt hV ztqyi⟩
  face := Quotient.mk _
  opp_opp d := Fin.ext (oppN_oppN d)
  opp_ne d h := oppN_ne d.1 (congrArg Fin.val h)
  vert_rot d := Fin.ext (g_csucc (g := gN) (k := kN) d)
  sameCycle_of_vert d e h := csucc_sameCycle ztqsk by_grind
  face_fperm d := Quotient.sound (show (fpermP hV).SameCycle (rotP hV (oppP d)) d from
    ⟨-1, by rw [zpow_neg_one, Perm.inv_eq_iff_eq]; rfl⟩)
  sameCycle_of_face _ _ h := Quotient.exact h
  vert_surj x := ⟨⟨2 * x.1, by unfold E; omega⟩, Fin.ext (by
    show View.tail B.N (B.view (2 * x.1)) = x.1
    zuefa
    zuila
    zvnpp; omega)⟩
  face_surj := Quotient.mk_surjective
end Map
end BookData
namespace BookData

/-! ## Planarity -/
section Planar
variable {B : BookData}
noncomputable instance instFintypeFaceT (hV : B.Valid) : Fintype ztmax := Fintype.ofFinite _
noncomputable instance instDecEqFaceT (hV : B.Valid) : DecidableEq ztmax :=
  Classical.decEq _
variable {s : ℕ}
theorem view_spF (hs : s < B.N) : B.view ztssm = .spF s := by
  zuefa
  simp_all
theorem view_spB (hs : s < B.N) : B.view (2 * s + 1) = .spB s := by
  zuefa
  grind
theorem two_mul_lt (hs : s < B.N) : 2 * s < 2 * B.E := by unfold E; omega
theorem two_mul_add_one_lt (hs : s < B.N) : 2 * s + 1 < 2 * B.E := by unfold E; omega

/-- **The book map is connected** (through the spine). -/
theorem connected (hV : B.Valid) : (B.map hV).Connected := by
  intro S hrot hopp d hd e
  have hN := hV.1
  -- a set closed under the rotation contains whole vertices
  have hvert : ∀ x ∈ S, ∀ y : Fin _, gN y = gN x → y ∈ S := by
    zulnq
    have hsc : (rotP hV).SameCycle x y := csucc_sameCycle _ hy.symm
    obtain ⟨n, rfl⟩ := hsc.exists_nat_pow_eq
    clear hsc hy
    induction n with
    | zero => exact hx
    | succ n ih => zunaz; exact hrot _ ih
  set t := gN d with ht
  have htN : t < B.N := tail_lt hV ztqyi
  have hstep : ∀ j : ℕ, ∀ y : Fin _, gN y = ztubr % B.N → y ∈ S := by
    zujbf
    induction j with
    | zero =>
      zusy
      refine hvert d hd y ?_
      rw [hy, Nat.add_zero, Nat.mod_eq_of_lt htN]
    | succ j ih =>
      zusy
      set s := ztubr % B.N with hs
      have hsN : s < B.N := Nat.mod_lt _ by_omega
      have hF : (⟨2 * s, two_mul_lt hsN⟩ : Fin _) ∈ S := ih _ (by
        unfold gN; simp only; rw [view_spF hsN]; rfl)
      have hB := hopp _ hF
      refine hvert _ hB y ?_
      zujka
      show (t + ztl) % B.N = View.tail B.N (B.view (oppN _))
      rw [show oppN ztssm = 2 * s + 1 by unfold oppN; split_ifs <;> omega, view_spB hsN]
      zvnpp
      rw [hs, ← Nat.add_assoc, Nat.mod_add_mod]
  have heN : gN e < B.N := tail_lt hV (view_ok e.2)
  refine hstep ztpca e ?_
  rw [show t + ztpca = gN e + B.N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt heN]

/-- The face label, on faces. -/
noncomputable def labelQ (hV : B.Valid) : FaceT hV → Bool × Finset ztw :=
  Quotient.lift (fun d => B.label ztbgk) (fun _ _ h => label_sameCycle hV h)
theorem Sup_inj {L : List ztw} {c c' : ℕ × ℕ} (hc : c ∈ L) (hc' : c' ∈ L)
    (h : Sup L c = Sup L c') : c = c' := by
  have h1 : c ∈ Sup L c' := h ▸ mem_Sup.2 by_simp_all
  have h2 : c' ∈ Sup L c := h.symm ▸ mem_Sup.2 by_simp_all
  rw [mem_Sup] at h1 h2
  grind
theorem Sup_nonempty {L : List ztw} {c : ℕ × ℕ} (hc : c ∈ L) : Sup L c ≠ ∅ := by
  zuq
  have : c ∈ Sup L c := mem_Sup.2 by_simp_all
  simp_all

/-- **The book map has at least `|I| + |O| + 2` faces.** -/
theorem card_face_ge (hV : B.Valid) :
    B.I.length + B.O.length + 2 ≤ Fintype.card ztmax := by
  obtain ⟨hN, hIn, hOn, -⟩ := id hV
  -- the witness labels
  let f : Option ztuyh ⊕ Option ztuyj → Bool × Finset _
    | .inl none => (true, ∅)
    | .inl (some i) => (true, Sup B.I B.I[i])
    | .inr none => (false, ∅)
    | .inr (some j) => (false, Sup B.O B.O[j])
  have hmaps : ∀ a ∈ (Finset.univ : Finset _),
      f a ∈ Finset.univ.image (labelQ hV) := by
    zulmm
    rw [Finset.mem_image]
    rcases a with (_ | i) | (_ | j)
    · refine ⟨Quotient.mk _ ⟨2 * ztnjo + 1, two_mul_add_one_lt by_omega⟩, Finset.mem_univ _,
        ?_⟩
      show B.label _ = _
      rw [view_spB by_omega]
      zugzk

    · obtain ⟨d, hd, hdv⟩ := exists_view (v := .inP B.I[i]) ztdbx
      refine ztykn
      show B.label _ = _
      zukty
    · refine ⟨Quotient.mk _ ⟨2 * ztnjo, two_mul_lt by_omega⟩, Finset.mem_univ _, ?_⟩
      show B.label _ = _
      rw [view_spF by_omega]
      zugzk

    · obtain ⟨d, hd, hdv⟩ := exists_view (v := .outM B.O[j]) ztdbx
      refine ztykn
      show B.label _ = _
      zukty
  have hinj : Set.InjOn f (Finset.univ : Finset (Option ztuyh ⊕
      Option ztuyj)) := by
    intro a _ b _ hab
    rcases a with (_ | i) | (_ | j) <;> rcases b with (_ | i') | (_ | j') <;>
      simp only [f, Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and,
        true_and] at hab ⊢
    · zulxq
    · zulxp
    · rw [Fin.ext ((hIn.getElem_inj_iff).1 (Sup_inj (List.getElem_mem _)
        ztdbx hab))]
    · zulxq
    · zulxp
    · rw [Fin.ext ((hOn.getElem_inj_iff).1 (Sup_inj (List.getElem_mem _)
        ztdbx hab))]
  have h1 := Finset.card_le_card_of_injOn f hmaps hinj
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset _)) (f := labelQ hV)
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_option, Fintype.card_fin] at h1 h2
  omega

/-- **Planarity of the two-page book map.** -/
theorem planar (hV : B.Valid) : (B.map hV).Planar := by
  rw [Separator.CombMap.planar_iff]
  refine ⟨connected hV, ?_⟩
  have hF := card_face_ge hV
  unfold Separator.CombMap.euler Separator.CombMap.numE
  simp only [Fintype.card_fin]
  have : 2 * B.E / 2 = B.E := by_omega
  zubk
  unfold E at *
  omega
end Planar
end BookData
end OracleBook
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbmr" : tactic => `(tactic| have hkN := (((H.regs r hr).1 k).1 hk).1)
local macro "zqbms" : tactic => `(tactic| (apply hL
                                           rw [← hl, ← hh]
                                           exact (congrArg Prod.fst hp).symm))
local macro "zqbmt" : tactic => `(tactic| (rw [hD] at hzU
                                           obtain ⟨k, hk, hkc⟩ := exists_rec hfull hregs hr hc hzc hzD hzU
                                           obtain ⟨h1, h2, -, -⟩ := chord_facts hQ hdh hN hfull hh hcorr hsides hregs hr D hD hk))
local macro "zqbmu" : tactic => `(tactic| (obtain ⟨t, ht, hpt⟩ := rec_end_open hQ hdh hlp hhk hne hl0 hl1
                                           have he := inp_lt (b := revOf Q) hlp
                                           rcases hl with hl | hl))
local macro "zqbmv" : tactic => `(tactic| (obtain ⟨t, ht, hpt⟩ := rec_end_open hQ hdh hrp hhk hne hr0 hr1
                                           have he := inp_lt (b := revOf Q) hrp
                                           rcases hr' with hr' | hr'))
local macro "zqbmw" : tactic => `(tactic| rw [← hpt])
local macro "zqbmx" : tactic => `(tactic| (rw [hcab, rec_toSet] at hkc
                                           obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hab.lt.le hkc.symm
                                           by_cases hdn : (N.chord k).dn = r))
local macro "zqbmy" : tactic => `(tactic| refine ⟨by_omega, by_omega, fun hne => ?_, fun hne => ?_⟩)
local macro "zqbmz" : tactic => `(tactic| have hp := pos_vtx H.simple H.dh (rec_attach H.nf hkN).1 zttmz)
local macro "zqbna" : tactic => `(tactic| have hp := pos_vtx H.simple H.dh (rec_attach H.nf hkN).2.1 zttmz)
set_option hygiene true

/-!
# WP-N, part 3: chord records of a normal form of the full interior map

For the geometry polygon `Q` (simple, distinct heights) and a valid normal form `N` of the full
visibility map of the interior model `M = interiorModel Q`, whose chord records have their
height vertex `h < n` (see the report: `IsNF` does not bound `h`):

* a chord record describes a horizontal chord of `Q` at the height of vertex `h`, from the
  point of walk position `lpos` to that of `rpos` (`rec_hchord`);
* an end of the chord is the vertex `h` exactly when its walk edge starts at `h`
  (`pos_vtx`); otherwise it lies inside the edge `inp p` of `Q` carried by its walk edge `p`
  (`pos_open`).
-/
namespace Chazelle.Core
namespace OutNF
open Set Filter Topology
open Chazelle.Visibility
open Chazelle.Mountain (TrapData)
open Chazelle.Jordan (simple_vtx_inj succIdx_lt)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext point_ext_iff)
open Chazelle.Chain (SideAttach sidePt)
open OutWalk
@[expose] public section
variable {Q : Polygon}

/-! ## Walk positions of the interior model -/
variable {p : ℕ}
/-- The start of walk edge `p` of the interior model. -/
theorem wa_eq (hp : p < Q.n) :
    (interiorModel Q).wa p = Q.vtx (wv ztgl Q.n p) := walk_vtx Q hp

/-- The end of walk edge `p` of the interior model. -/
theorem wb_eq (hp : p < Q.n) :
    (interiorModel Q).wb p = Q.vtx ztzod := walk_succ Q hp

/-- `wv` is injective below `n`. -/
theorem wv_inj {b : Bool} {n x y : ℕ} (hx : x < n) (hy : y < n) (h : wv b n x = wv b n y) :
    x = y := by
  rw [← wv_wv hx, ← wv_wv hy, h]

/-- Walk edges are not horizontal (distinct heights). -/
theorem walk_nonhoriz (hQ : Q.Simple) (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n) :
    ((interiorModel Q).wa p).2 ≠ ((interiorModel Q).wb p).2 := by
  rw [wa_eq hp, wb_eq hp]
  zudov
  refine hdh _ _ ztwhy (wv_lt ztquf) fun h => ?_
  have := wv_inj hp ztquf h
  unfold nxt at this; grind

/-- The parameter of a walk position at the height of a vertex. -/
theorem param_eq (hQ : Q.Simple) (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n) (h : ℕ) :
    (interiorModel Q).param Q ztdw =
      ztgvo /
        ztfln := by
  simp only [Model.param, Setup.iteF ztryi]

/-- A walk position at the height of vertex `h` is at that height. -/
theorem pos_snd (hQ : Q.Simple) (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n) (h : ℕ) :
    ((interiorModel Q).pos Q ztdw).2 = (Q.vtx h).2 := by
  have hne := walk_nonhoriz hQ hdh hp
  have hne' : ((interiorModel Q).wb p).2 - ((interiorModel Q).wa p).2 ≠ 0 :=
    by grind
  simp only [Model.pos, lerp_snd]
  zujld
  simp_all

/-- **A walk position at the height of the start vertex of its walk edge is that vertex.** -/
theorem pos_vtx (hQ : Q.Simple) (hdh : DistinctHeights Q) {p h : ℕ} (hp : p < Q.n)
    (hh : wv ztgl Q.n p = h) : (interiorModel Q).pos Q ztdw = Q.vtx h := by
  have h0 : ztykz := by
    rw [param_eq hQ hdh hp, wa_eq hp, hh, sub_self, zero_div]
  simp only [Model.pos, h0, Geometry.lerp_zero]
  rw [wa_eq hp, hh]

/-- Otherwise the parameter is not zero. -/
theorem param_ne_zero (hQ : Q.Simple) (hdh : DistinctHeights Q) {p h : ℕ} (hp : p < Q.n)
    (hh : h < Q.n) (hne : wv ztgl Q.n p ≠ h) : (interiorModel Q).param Q ztdw ≠ 0 := by
  zujld
  have hne' :=
    sub_ne_zero.2 (Ne.symm ztryi)
  refine div_ne_zero (sub_ne_zero.2 ?_) hne'
  rw [wa_eq hp]
  exact hdh h _ hh ztwhy ztnr

/-- **A walk position with parameter in `(0, 1)` lies inside the edge of `Q` carried by its walk
edge.** -/
theorem pos_open (hp : p < Q.n) {x : WPos} (hx : x.edge = p)
    (ht : (interiorModel Q).param Q x ∈ Ioo (0 : ℝ) 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, (interiorModel Q).pos Q x =
      lerp ztypr ztxqs t := by
  have he := inp_lt (b := revOf Q) hp
  zulru
  rw [hx, wa_eq hp, wb_eq hp, ← nxt_eq he]
  zubyc
  · grind
  · rw [h1, h2, Geometry.lerp_symm]
    grind

/-! ## Chord records -/
variable {N : NF}

/-- A chord record in range is a member of the chord list. -/
theorem chord_mem {k : ℕ} (hk : k < N.nChords) : N.chord k ∈ N.chords := by
  zudly
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  grind

/-- The chord of a record is a chord of `Q`. -/
theorem rec_chords (hfull : N.F ztd Q = (interiorModel Q).Full) {k : ℕ}
    (hk : k < N.nChords) : (N.chord k).toSet ztd Q ∈ chords Q := by
  have : (N.chord k).toSet _ Q ∈ N.F ztd Q :=
    ⟨N.chord k, chord_mem hk, rfl⟩
  rw [hfull] at this
  tauto

/-- The walk edges of a record are walk edges and its parameters are in `[0, 1)`. -/
theorem rec_attach (hN : IsNF ztd Q N) {k : ℕ} (hk : k < N.nChords) :
    (N.chord k).lp < Q.n ∧ (N.chord k).rp < Q.n ∧
      0 ≤ (interiorModel Q).param Q (N.chord k).lpos ∧
      (interiorModel Q).param Q (N.chord k).lpos < 1 ∧
      0 ≤ (interiorModel Q).param Q (N.chord k).rpos ∧
      (interiorModel Q).param Q (N.chord k).rpos < 1 := by
  obtain ⟨hl, hr⟩ := hN.2.2.1 k hk
  have hn := walk_n Q
  exact ⟨hn ▸ hl.1, hn ▸ hr.1, hl.2.1, hl.2.2.1, hr.2.1, hr.2.2.1⟩

/-- **The chord of a record is a horizontal chord** at the height of its vertex, between the
points of its two walk positions. -/
theorem rec_hchord (hQ : Q.Simple) (hfull : N.F ztd Q = (interiorModel Q).Full)
    {k : ℕ} (hk : k < N.nChords) :
    IsHChord Q (Q.vtx (N.chord k).h).2 ((interiorModel Q).pos Q (N.chord k).lpos).1
      ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
  have hc := rec_chords hfull hk
  obtain ⟨v, σ, hv, hσ, hdir, hS, hch⟩ := chords_spec hQ hc
  have e : hseg (Q.vtx v).2 ztilp ztilo
      = hseg (Q.vtx (N.chord k).h).2 ((interiorModel Q).pos Q (N.chord k).lpos).1
        ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
    zugxo
  obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hch.lt.le e
  grind

/-- The chord of a record as a horizontal segment. -/
theorem rec_toSet (k : ℕ) : (N.chord k).toSet ztd Q =
    hseg (Q.vtx (N.chord k).h).2 ((interiorModel Q).pos Q (N.chord k).lpos).1
      ((interiorModel Q).pos Q (N.chord k).rpos).1 := rfl

/-! ## Regions of the full interior map -/

/-- The regions of the full interior map are the regions of the visibility map. -/
theorem model_regions (hfull : N.F ztd Q = (interiorModel Q).Full) :
    (interiorModel Q).regions ztwjs = regions Q := by
  tauto

/-- Just below a point of the open top side, the points are in the region. -/
theorem below_top (D : TrapData Q) {x : ℝ} (hx1 : edgeX Q D.i D.y₂ < x)
    (hx2 : x < edgeX Q D.j D.y₂) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → ((x, D.y₂ - ε) : Point) ∈ D.region := by
  obtain ⟨ε₁, hε₁, h⟩ := Metric.eventually_nhds_iff.1 ztswn
  refine ⟨ε₁, hε₁, fun ε hε hε' => h ?_ by_simp_all⟩
  zuowp; zunvl
  grind

/-- The end of a record at walk position `(p, h + 1)` whose walk edge does not start at `h`
lies inside the edge `inp p` of `Q`, hence is not a vertex. -/
theorem rec_end_open (hQ : Q.Simple) (hdh : DistinctHeights Q) {p h : ℕ} (hp : p < Q.n)
    (hh : h < Q.n) (hne : wv ztgl Q.n p ≠ h)
    (ht0 : 0 ≤ (interiorModel Q).param Q ztdw)
    (ht1 : (interiorModel Q).param Q ztdw < 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, (interiorModel Q).pos Q ztdw =
      lerp ztypr ztxqs t :=
  pos_open hp rfl ⟨lt_of_le_of_ne ht0 (Ne.symm (param_ne_zero hQ hdh hp hh hne)), ht1⟩

/-- An end of a record inside an edge `e` of `Q`, lying on edge `f`, forces `e = f`. -/
theorem edge_eq_of_open (hQ : Q.Simple) {e f : ℕ} (he : e < Q.n) (hf : f < Q.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hmem : lerp ztgep ztbakx t ∈ Q.edge f) :
    e = f := by
  zuct
  exact Chazelle.Jordan.simple_openEdge_not_mem_other hQ he ht hf ztnr hmem

/-- **The chord records of a region.**  Every exit chord of the region `reg r = D.region` is at
its top (`dn = r`, vertex `top`) or at its bottom (`dn ≠ r`, vertex `bot`); an end of it whose
walk edge does not start at its vertex lies on the left side edge (left end) or on the right
side edge (right end). -/
theorem chord_facts (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF ztd Q N)
    (hfull : N.F ztd Q = (interiorModel Q).Full)
    (hh : ∀ k, k < N.nChords → (N.chord k).h < Q.n) {reg : ℕ → Set Point}
    (hcorr : RegionCorr ztd Q N reg)
    (hsides : ChordSidesOK ztd Q N reg) (hregs : RegionsOK ztd Q N reg)
    {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q) (hD : D.region = reg r) {k : ℕ}
    (hk : k ∈ (N.region r).chords) :
    ztgvi ∧ ztgvj ∧
      (wv ztgl Q.n (N.chord k).lp ≠ (N.chord k).h →
        inp ztgl Q.n (N.chord k).lp = D.i) ∧
      (wv ztgl Q.n (N.chord k).rp ≠ (N.chord k).h →
        inp ztgl Q.n (N.chord k).rp = D.j) := by
  obtain ⟨hkN, z, ⟨hzc, hzD⟩, hzU⟩ := ((hregs r hr).1 k).1 hk
  rw [← hD] at hzU
  have hc := rec_chords hfull hkN
  have hhk := hh k hkN
  obtain ⟨hlp, hrp, hl0, hl1, hr0, hr1⟩ := rec_attach hN hkN
  have hch := rec_hchord hQ hfull hkN
  have hzc' := hzc
  rw [rec_toSet] at hzc'
  obtain ⟨hup, hdn, hside⟩ := hsides k hkN
  zubxw
  have hregQ : ztkoz := fun s hs => by
    rw [← model_regions hfull]; exact hcorr.1 s hs
  zukl
  have hposl : ((interiorModel Q).pos Q (N.chord k).lpos).2 = (Q.vtx (N.chord k).h).2 :=
    pos_snd hQ hdh hlp _
  have hposr : ((interiorModel Q).pos Q (N.chord k).rpos).2 = (Q.vtx (N.chord k).h).2 :=
    pos_snd hQ hdh hrp _
  rcases OutGeom.touch_cases hQ D hc hzc hzD hzU with ⟨hz2, hz1, hz3⟩ | ⟨hz2, hz1, hz3⟩
  · -- a top chord
    zulke
    have htop := OutGeom.vtx_eq_top hdh D hQ hhk hhy
    have hdnr : (N.chord k).dn = r := by
      obtain ⟨ε₁, hε₁, hbelow⟩ := below_top D hz1 hz3
      set ε := min ε₀ ε₁ / 2 with hεd
      zudpq
      have e1 : (ztfr : Point) ∈ reg (N.chord k).dn :=
        by grind
      have e2 : (ztfr : Point) ∈ reg r := by
        grind
      rcases regions_eq_or_disjoint (hregQ _ hdn) (hregQ _ hr) with he | he
      · exact hcorr.2.1 _ _ hdn hr he
      grind
    zukui
    have hzs : z ∈ hseg D.y₂ ((interiorModel Q).pos Q (N.chord k).lpos).1
        ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
      grind
    obtain ⟨-, hl, -, hr'⟩ := OutGeom.top_chord_ends hQ hdh D hch hzs hzD hz1 hz3
    zqbmy
    · zqbmu
      · refine edge_eq_of_open hQ he D.isTrap.hi ht ?_
        zqbmw
        change (interiorModel Q).pos Q (N.chord k).lpos ∈ _
        exact D.isTrap.mem_edgeL by_grind by_grind
          by_grind
      · zuhum

        zqbmw
        change (interiorModel Q).pos Q (N.chord k).lpos = _
        grind
    · zqbmv
      · refine edge_eq_of_open hQ he D.isTrap.hj ht ?_
        zqbmw
        change (interiorModel Q).pos Q (N.chord k).rpos ∈ _
        exact D.isTrap.mem_edgeR by_grind by_grind
          by_grind
      · zuhum

        zqbmw
        change (interiorModel Q).pos Q (N.chord k).rpos = _
        grind
  · -- a bottom chord
    zulke
    have hbot := OutGeom.vtx_eq_bot hdh D hQ hhk hhy
    have hdnr : (N.chord k).dn ≠ r := by
      intro hdr
      have e1 : ((z.1, z.2 - ε₀ / 2) : Point) ∈ reg (N.chord k).dn :=
        by grind
      rw [hdr, ← hD] at e1
      have := e1.1
      grind
    zukui
    have hzs : z ∈ hseg D.y₁ ((interiorModel Q).pos Q (N.chord k).lpos).1
        ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
      grind
    obtain ⟨-, hl, -, hr'⟩ := OutGeom.bot_chord_ends hQ hdh D hch hzs hzD hz1 hz3
    zqbmy
    · zqbmu
      · refine edge_eq_of_open hQ he D.isTrap.hi ht ?_
        zqbmw
        change (interiorModel Q).pos Q (N.chord k).lpos ∈ _
        exact D.isTrap.mem_edgeL by_grind by_grind
          by_grind
      · zuhul

        zqbmw
        change (interiorModel Q).pos Q (N.chord k).lpos = _
        grind
    · zqbmv
      · refine edge_eq_of_open hQ he D.isTrap.hj ht ?_
        zqbmw
        change (interiorModel Q).pos Q (N.chord k).rpos ∈ _
        exact D.isTrap.mem_edgeR by_grind by_grind
          by_grind
      · zuhul

        zqbmw
        change (interiorModel Q).pos Q (N.chord k).rpos = _
        grind

/-- A chord of `Q` touching the region `reg r` is the chord of a record listed by the region. -/
theorem exists_rec (hfull : N.F ztd Q = (interiorModel Q).Full) {reg : ℕ → Set Point}
    (hregs : RegionsOK ztd Q N reg) {r : ℕ} (hr : r < N.nRegions)
    {c : Set Point} (hc : c ∈ chords Q) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure ztcz) :
    ∃ k ∈ (N.region r).chords, (N.chord k).toSet ztd Q = c := by
  have hcF : c ∈ N.F ztd Q := by rw [hfull]; exact hc
  obtain ⟨rc, hrc, rfl⟩ := hcF
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hrc
  have hck : ztiyl := by
    zuub
  refine ⟨k, ((hregs r hr).1 k).2 ⟨hk, z, ⟨?_, hzD⟩, hzU⟩, by zuozf⟩
  simp_all

/-- A chord at the top height touching the region is the chord of a top record of it. -/
theorem top_chord_rec (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF ztd Q N)
    (hfull : N.F ztd Q = (interiorModel Q).Full)
    (hh : ∀ k, k < N.nChords → (N.chord k).h < Q.n) {reg : ℕ → Set Point}
    (hcorr : RegionCorr ztd Q N reg)
    (hsides : ChordSidesOK ztd Q N reg) (hregs : RegionsOK ztd Q N reg)
    {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q) (hD : D.region = reg r)
    {c : Set Point} (hc : c ∈ chords Q) {a b : ℝ} (hab : IsHChord Q D.y₂ a b)
    (hcab : c = hseg D.y₂ a b) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure D.region) :
    ∃ k ∈ (N.region r).chords, (N.chord k).dn = r ∧ (N.chord k).h = D.top ∧
      ((interiorModel Q).pos Q (N.chord k).lpos).1 = a ∧
      ((interiorModel Q).pos Q (N.chord k).rpos).1 = b := by
  zqbmt
  have hkN := (((hregs r hr).1 k).1 hk).1
  zqbmx
  · grind
  · exfalso
    have := h2 hdn
    rw [this, D.bot_snd hQ] at e1
    exact absurd e1.symm (D.isTrap.bot_lt.trans D.isTrap.lt_top).ne

/-- A chord at the bottom height touching the region is the chord of a bottom record of it. -/
theorem bot_chord_rec (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF ztd Q N)
    (hfull : N.F ztd Q = (interiorModel Q).Full)
    (hh : ∀ k, k < N.nChords → (N.chord k).h < Q.n) {reg : ℕ → Set Point}
    (hcorr : RegionCorr ztd Q N reg)
    (hsides : ChordSidesOK ztd Q N reg) (hregs : RegionsOK ztd Q N reg)
    {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q) (hD : D.region = reg r)
    {c : Set Point} (hc : c ∈ chords Q) {a b : ℝ} (hab : IsHChord Q D.y₁ a b)
    (hcab : c = hseg D.y₁ a b) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure D.region) :
    ∃ k ∈ (N.region r).chords, (N.chord k).dn ≠ r ∧ (N.chord k).h = D.bot ∧
      ((interiorModel Q).pos Q (N.chord k).lpos).1 = a ∧
      ((interiorModel Q).pos Q (N.chord k).rpos).1 = b := by
  zqbmt
  zqbmx
  · exfalso
    have := h1 hdn
    rw [this, D.top_snd hQ] at e1
    exact absurd e1 (D.isTrap.bot_lt.trans D.isTrap.lt_top).ne
  grind

/-! ## Region summaries -/

/-- The hypotheses on the geometry polygon, the normal form and its region correspondence. -/
structure RegCtx (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop where
  simple : Q.Simple
  dh : DistinctHeights Q
  nf : IsNF ztd Q N
  full : N.F ztd Q = (interiorModel Q).Full
  hlt : ∀ k, k < N.nChords → (N.chord k).h < Q.n
  corr : RegionCorr ztd Q N reg
  sides : ChordSidesOK ztd Q N reg
  regs : RegionsOK ztd Q N reg
variable {reg : ℕ → Set Point}

/-- `chord_facts` under the bundled hypotheses. -/
theorem RegCtx.facts (H : RegCtx Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg r) {k : ℕ} (hk : k ∈ (N.region r).chords) :
    ztgvi ∧ ztgvj ∧
      (wv ztgl Q.n (N.chord k).lp ≠ (N.chord k).h →
        inp ztgl Q.n (N.chord k).lp = D.i) ∧
      (wv ztgl Q.n (N.chord k).rp ≠ (N.chord k).h →
        inp ztgl Q.n (N.chord k).rp = D.j) :=
  chord_facts H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs hr D hD hk

/-- **No top record: the top side is empty.** -/
theorem RegCtx.no_top (H : RegCtx Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg r) (hno : ∀ k ∈ (N.region r).chords, (N.chord k).dn ≠ r) :
    edgeX Q D.j D.y₂ ≤ edgeX Q D.i D.y₂ := by
  zuso
  by_cases hL : (Q.vtx D.top).1 ≠ edgeX Q D.i D.y₂
  · obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, hdn, -⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all
  · zumig
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_right H.simple H.dh D by_grind
    obtain ⟨k, hk, hdn, -⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all

/-- **No bottom record: the bottom side is empty.** -/
theorem RegCtx.no_bot (H : RegCtx Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg r) (hno : ∀ k ∈ (N.region r).chords, (N.chord k).dn = r) :
    edgeX Q D.j D.y₁ ≤ edgeX Q D.i D.y₁ := by
  zuso
  by_cases hL : (Q.vtx D.bot).1 ≠ edgeX Q D.i D.y₁
  · obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, hdn, -⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all
  · zumig
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_right H.simple H.dh D by_grind
    obtain ⟨k, hk, hdn, -⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all

/-- **All left ends at vertices: the top and bottom vertices are at the left corners.** -/
theorem RegCtx.all_left (H : RegCtx Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg r)
    (hall : ∀ k ∈ (N.region r).chords, wv ztgl Q.n (N.chord k).lp = (N.chord k).h) :
    (Q.vtx D.top).1 = edgeX Q D.i D.y₂ ∧ (Q.vtx D.bot).1 = edgeX Q D.i D.y₁ := by
  constructor
  · zuldp
    obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, hl, -⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    zqbmr
    zqbmz
    zqbms
  · zuldp
    obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, hl, -⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    zqbmr
    zqbmz
    zqbms

/-- **All right ends at vertices: the top and bottom vertices are at the right corners.** -/
theorem RegCtx.all_right (H : RegCtx Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg r)
    (hall : ∀ k ∈ (N.region r).chords, wv ztgl Q.n (N.chord k).rp = (N.chord k).h) :
    (Q.vtx D.top).1 = edgeX Q D.j D.y₂ ∧ (Q.vtx D.bot).1 = edgeX Q D.j D.y₁ := by
  constructor
  · zuldp
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_right H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, -, hl⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    zqbmr
    zqbna
    zqbms
  · zuldp
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_right H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, -, hl⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    zqbmr
    zqbna
    zqbms

/-- The two ends of a record are not both at its vertex. -/
theorem RegCtx.not_both (H : RegCtx Q N reg) {k : ℕ} (hkN : k < N.nChords)
    (hl : wv ztgl Q.n (N.chord k).lp = (N.chord k).h)
    (hr : wv ztgl Q.n (N.chord k).rp = (N.chord k).h) : False := by
  have hpl := pos_vtx H.simple H.dh (rec_attach H.nf hkN).1 hl
  have hpr := pos_vtx H.simple H.dh (rec_attach H.nf hkN).2.1 hr
  have hch := rec_hchord H.simple H.full hkN
  have e1 : ((interiorModel Q).pos Q (N.chord k).lpos).1 = (Q.vtx (N.chord k).h).1 :=
    congrArg Prod.fst hpl
  have e2 : ((interiorModel Q).pos Q (N.chord k).rpos).1 = (Q.vtx (N.chord k).h).1 :=
    congrArg Prod.fst hpr
  have := hch.lt
  simp_all
end
end OutNF
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqxd" : tactic => `(tactic| (have w₃ := e₃.wb_right
                                          have k₃ : c₃.nreg 30015 = c.nreg 30015 := by_simp_all
                                          have o₃ := (hr₃ _ by_omega by_omega by_omega).trans h.one))
local macro "zqxe" : tactic => `(tactic| (have hj := h.j_hi
                                          have hk := h.rk
                                          zuhzh

                                          have hbd := h.bdst
                                          zumdw
                                          have him := h.i_mid))
local macro "zqxf" : tactic => `(tactic| refine ⟨fun r hb ha => ?_, rr₄.trans hrr₃, fun x hx => ?_, rm₄.trans hrm₃, o₄.trans ho₃⟩)
local macro "zqxg" : tactic => `(tactic| (have hlok : lo ≤ c.nreg 30015 := by_omega
                                          have hkhi : c.nreg 30015 < hi := by_omega))
local macro "zqxh" : tactic => `(tactic| (refine ⟨c₃, c₄, e₃, e₄, ?_, by_simp_all⟩
                                          have w₄ := e₄.wb_right))
set_option hygiene true

/-!
# Sorting on the RAM, part 2: a verified bottom-up merge sort (WP-C)

`sortStmt cmp` sorts `K` naturals ("items") by a comparison procedure `cmp`, a statement with a
contract `CmpOK` (it reads two items in registers `sr 0`, `sr 1`, writes the bit `le a b` into
`sr 2`, may write the bands `Bc` and nothing else, and preserves an arbitrary invariant `J`).
Only natural registers of band `bSort` (`sr i = bandReg bSort i = 30000 + i`), the allocator and
fresh memory are written; values are added, subtracted and compared, never multiplied; every
stored natural is an item, an index `≤ 2K` or an address below `ALLOC + 2K`.

## Registers (band `bSort`)

| register | role |
|---|---|
| `sr 0`, `sr 1`, `sr 2` | comparator: the two items, the answer bit |
| `sr 3`, `sr 4` | input: base `S` and length `K` of the item array |
| `sr 5` | output: base of the sorted array (fresh, below the new allocator) |
| `sr 6`, `sr 17` | the constants `1`, `2` |
| `sr 7`, `sr 8` | source and destination arrays of the current pass |
| `sr 9`, `sr 10` … `sr 12` | run width `w`; `lo`, `mid`, `hi` of the current pair of runs |
| `sr 13` … `sr 15` | merge cursors `i`, `j`, `k` (copy loop: `i`) |
| `sr 16`, `sr 18` | scratch (address, word) |

## Algorithm and cost

Copy the items to a fresh array `A₀ = ALLOC` (raising `ALLOC` by `2` per item, so that it grows
by `2K` in total), then run passes with widths `w = 1, 2, 4, …` while `w < K`, each merging the
runs `[lo, lo + w)`, `[lo + w, lo + 2w)` of the source array into the destination array
(`A₀`, `A₀ + K` alternately).  Cost (`sortStmt_exec`):
`≤ (κ + 30) (K (⌈log₂ K⌉ + 1) + 1)` for a comparator of cost `≤ κ`.

## Main result

`sortStmt_exec`: from a word-bounded configuration with the items `L` at `S` below the allocator
and room for the cost, the sort ends with a list `L'` at the output base that is a permutation of
`L`, sorted for `le` (`List.Pairwise`), in a fresh area, respecting `Frame (insert bSort Bc)` and
the invariant `J`.
-/
namespace Chazelle.Core
namespace SortR
open Machine Machine.Stmt Programs SortL
@[expose] public section
def sr (i : ℕ) : ℕ := 30000 + i

/-- Load the items `src[i]`, `src[j]` into the comparator registers. -/
def cmpLoad : Stmt :=
  block [.addN 30016 30007 30013, .loadN 30000 30016, .addN 30016 30007 30014, .loadN 30001 30016]

/-- Move `src[i]` to `dst[k]`, `i := i + 1`. -/
def takeL : Stmt :=
  block [.addN 30016 30007 30013, .loadN 30018 30016, .addN 30016 30008 30015, .storeN 30016 30018,
    .addN 30013 30013 30006]

/-- Move `src[j]` to `dst[k]`, `j := j + 1`. -/
def takeR : Stmt :=
  block [.addN 30016 30007 30014, .loadN 30018 30016, .addN 30016 30008 30015, .storeN 30016 30018,
    .addN 30014 30014 30006]

/-- One output word of a merge. -/
def mergeStep (cmp : Stmt) : Stmt :=
  .ifLtN 30013 30011
    (.ifLtN 30014 30012 (.seq cmpLoad (.seq cmp (.ifLtN 30002 30006 takeR takeL))) takeL) takeR

/-- The merge loop body: one output word, `k := k + 1`. -/
def mergeBody (cmp : Stmt) : Stmt := .seq (mergeStep cmp) ztgwt

/-- The merge of `src[lo, mid)` and `src[mid, hi)` into `dst[lo, hi)`. -/
def mergeLoop (cmp : Stmt) : Stmt := .whileLtN 30015 30012 ztvyy

/-- `r := min (x + w) K`. -/
def clamp (r x : ℕ) : Stmt :=
  .seq (.instr (.addN r x 30009)) (.ifLtN 30004 r (.instr (.copyN r 30004)) .skip)

/-- The merge cursors `i := lo`, `j := mid`, `k := lo`. -/
def cursors : Stmt := block [.copyN 30013 30010, .copyN 30014 30011, .copyN 30015 30010]

/-- `mid := min (lo + w) K`, `hi := min (mid + w) K`, cursors, merge, `lo := hi`. -/
def pairBody (cmp : Stmt) : Stmt :=
  .seq (clamp 30011 30010) (.seq (clamp 30012 30011)
    (.seq cursors (.seq ztvyz (.instr (.copyN 30010 30012)))))

/-- One pass: all pairs of runs. -/
def pairLoop (cmp : Stmt) : Stmt := .whileLtN 30010 30004 ztwbj

/-- Swap the arrays and double the width. -/
def swapBlock : Stmt := block [.copyN 30018 30007, .copyN 30007 30008, .copyN 30008 30018,
  .addN 30009 30009 30009]

/-- A pass with its bookkeeping. -/
def passBody (cmp : Stmt) : Stmt := .seq (.instr (.constN 30010 0)) (.seq ztwbl swapBlock)

/-- The passes, while `w < K`. -/
def passLoop (cmp : Stmt) : Stmt := .whileLtN 30009 30004 ztwbn

/-- Copy one item to the fresh array and raise the allocator by `2`. -/
def copyBody : Stmt :=
  block [.addN 30016 30003 30013, .loadN 30018 30016, .addN 30016 30007 30013, .storeN 30016 30018,
    .addN 30013 30013 30006, .addN 9999 9999 30017]

/-- The copy loop. -/
def copyLoop : Stmt := .whileLtN 30013 30004 copyBody

/-- Constants, the two fresh arrays, `i := 0`. -/
def sortInit : Stmt := block [.constN 30006 1, .constN 30017 2, .copyN 30007 9999,
  .addN 30008 9999 30004, .constN 30013 0]

/-- **The sort.** -/
def sortStmt (cmp : Stmt) : Stmt :=
  .seq sortInit (.seq copyLoop (.seq (.instr (.constN 30009 1))
    (.seq ztwbo (.instr (.copyN 30005 30007)))))

/-- The cost bound of the sort for a comparator of cost `≤ κ`. -/
def sortCost (κ K : ℕ) : ℕ := ztcxg * ztwko

/-! ## The comparator contract -/

/-- **Contract of a comparison procedure**: from every word-bounded configuration satisfying the
invariant `J`, `cmp` runs in at most `κ` steps, keeps `J`, writes into `sr 2` the bit
`le (sr 0) (sr 1)`, and changes no natural register except `sr 0 … sr 2` and those of the bands
`Bc` (never `ALLOC`), no real register outside `Bc`, no memory and no output. -/
def CmpOK (P : Polygon) (W : ℕ) (cmp : Stmt) (Bc : Finset ℕ) (J : Config → Prop)
    (le : ℕ → ℕ → Bool) (κ : ℕ) : Prop :=
  ∀ c, WordsBounded W c → J c →
    ∃ c' k, Exec P W cmp c c' k ∧ k ≤ κ ∧ J c' ∧
      c'.nreg 30002 = (if le ztjry ztjrz then 1 else 0) ∧
      (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → ztdyw →
        c'.nreg r = c.nreg r) ∧
      ztimt ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- `J` is insensitive to the writes of the sort itself (registers of band `bSort`, the
allocator, memory from `A₀` on). -/
def JStable (J : Config → Prop) (A₀ : ℕ) : Prop :=
  ∀ c c', J c → ztgnl →
    c'.rreg = c.rreg → ztpt → c'.rmem = c.rmem →
      c'.output = c.output → J c'

/-! ## A loop rule that also bounds the growth of a quantity by the cost -/

/-- `whileLtN` with a potential `Φ` (upper cost bound) and a quantity `ψ` that each iteration
raises by at most its cost: the whole loop raises `ψ` by at most its cost. -/
theorem whileLtN_potential_lb {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt}
    (I : Config → Prop) (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · zubu

    · zulfw

/-! ## Sort-local steps -/

/-- A step of the sort itself: only band `bSort`, the allocator and memory from `A₀` on change. -/
def SL (A₀ : ℕ) (c c' : Config) : Prop :=
  ztgnl ∧ c'.rreg = c.rreg ∧
    ztpt ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- **The global frame of the sort** relative to its entry configuration `c₀`: registers outside
the bands `bSort`, `Bc` and the allocator, real registers outside `Bc`, memory below `A₀`, real
memory and output are those of `c₀`. -/
def Loc (Bc : Finset ℕ) (A₀ : ℕ) (c₀ c : Config) : Prop :=
  (∀ r, bandOf r ∉ Bc → bandOf r ≠ bSort → r ≠ ALLOC → c.nreg r = c₀.nreg r) ∧
    ztimu ∧ ztiue ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The entry configuration is within the frame. -/
theorem Loc.refl (Bc : Finset ℕ) (A₀ : ℕ) (c : Config) : Loc Bc A₀ c c :=
  ⟨by_omega, by_simp_all, by_omega, rfl, rfl⟩

/-- A sort-local step keeps the global frame. -/
theorem Loc.sl {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : Loc Bc A₀ c₀ c)
    (h' : SL A₀ c c') : Loc Bc A₀ c₀ c' :=
  ⟨fun r h1 h2 h3 => (h'.1 r h2 h3).trans ztgjx,
    fun r h1 => by zuozm; exact h.2.1 r h1,
    fun a ha => (h'.2.2.1 a ha).trans zttlk, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- The band of a register of the sort band. -/
theorem bandOf_sort {r : ℕ} (h : bandOf r ≠ bSort) : r < 30000 ∨ 40000 ≤ r := by
  unfold bandOf bSort at h
  omega

/-! ## The straight-line pieces -/
section pieces
variable {P : Polygon} {W : ℕ}

/-- `takeL`: `dst[k] := src[i]`, `i := i + 1` (scratch `sr 16`, `sr 18`). -/
theorem takeL_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 30007 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30008 + c.nreg 30015 ≤ W) (h3 : c.nreg 30013 + c.nreg 30006 ≤ W) :
    ∃ c' k, Exec P W takeL c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem ztqhx (c.nmem ztjsa) ∧
      c'.nreg 30013 = c.nreg 30013 + c.nreg 30006 ∧
      (∀ r, r ≠ 30013 → r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold takeL
  exec_block
  · zubvv
  · simp_all
  · simp_all
  simp_all

/-- `takeR`: `dst[k] := src[j]`, `j := j + 1` (scratch `sr 16`, `sr 18`). -/
theorem takeR_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 30007 + c.nreg 30014 ≤ W)
    (h2 : c.nreg 30008 + c.nreg 30015 ≤ W) (h3 : c.nreg 30014 + c.nreg 30006 ≤ W) :
    ∃ c' k, Exec P W takeR c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem ztqhx (c.nmem ztqhw) ∧
      c'.nreg 30014 = c.nreg 30014 + c.nreg 30006 ∧
      (∀ r, r ≠ 30014 → r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold takeR
  exec_block
  · zubvv
  · simp_all
  · simp_all
  simp_all

/-- `cmpLoad`: `sr 0 := src[i]`, `sr 1 := src[j]` (scratch `sr 16`). -/
theorem cmpLoad_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 30007 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30007 + c.nreg 30014 ≤ W) :
    ∃ c' k, Exec P W cmpLoad c c' k ∧ k = 4 ∧
      c'.nreg 30000 = c.nmem ztjsa ∧
      c'.nreg 30001 = c.nmem ztqhw ∧
      (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30016 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmpLoad
  exec_block
  · zubvv
  · simp_all
  simp_all
variable {c : Config}
/-- `addN` with its effect spelled out. -/
theorem addN_char (hc : WordsBounded W c) (r x y : ℕ) (h : c.nreg x + c.nreg y ≤ W) :
    ∃ c', Exec P W (.instr (.addN r x y)) c c' 1 ∧ c'.nreg = upd c.nreg r ztqjc ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.addN hc r x y h, rfl, rfl, rfl, rfl, rfl⟩

/-- `copyN` with its effect spelled out. -/
theorem copyN_char (hc : WordsBounded W c) (r x : ℕ) :
    ∃ c', Exec P W (.instr (.copyN r x)) c c' 1 ∧ c'.nreg = upd c.nreg r ztmhf ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.copyN hc r x, rfl, rfl, rfl, rfl, rfl⟩

/-- `constN` with its effect spelled out. -/
theorem constN_char (hc : WordsBounded W c) (r v : ℕ) (h : v ≤ W) :
    ∃ c', Exec P W ztcyq c c' 1 ∧ c'.nreg = upd c.nreg r v ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  ⟨_, Exec.constN hc r v h, rfl, rfl, rfl, rfl, rfl⟩

/-- `clamp r x`: `r := min (x + w) K`, cost `≤ 3`. -/
theorem clamp_exec (hc : WordsBounded W c) (r x : ℕ) (hr : r ≠ 30004)
    (h : c.nreg x + c.nreg 30009 ≤ W) :
    ∃ c' k, Exec P W (clamp r x) c c' k ∧ k ≤ 3 ∧
      c'.nreg = upd c.nreg r (min (c.nreg x + c.nreg 30009) ztvif) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, e₁, n₁, m₁, rr₁, rm₁, o₁⟩ := addN_char (P := P) hc r x 30009 h
  have hK : c₁.nreg 30004 = c.nreg 30004 := by rw [n₁, Machine.upd_other _ _ _ (Ne.symm hr)]
  have hR : c₁.nreg r = c.nreg x + c.nreg 30009 := by_simp_all
  by_cases ht : c₁.nreg 30004 < c₁.nreg r
  · obtain ⟨c₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := copyN_char e₁.wb_right r 30004
    refine ⟨c₂, _, .seq e₁ ztspm, le_refl _, ?_, m₂.trans m₁, rr₂.trans rr₁,
      rm₂.trans rm₁, o₂.trans o₁⟩
    rw [n₂, hK, n₁, Machine.upd_upd_same]
    grind
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_false ht ztekc), le_refl _, ?_, m₁, rr₁, rm₁,
      o₁⟩
    simp_all

/-- `cursors`: `i := lo`, `j := mid`, `k := lo`, cost `3`. -/
theorem cursors_exec (hc : WordsBounded W c) :
    ∃ c' k, Exec P W cursors c c' k ∧ k = 3 ∧
      c'.nreg 30013 = c.nreg 30010 ∧ c'.nreg 30014 = c.nreg 30011 ∧
      c'.nreg 30015 = c.nreg 30010 ∧
      (∀ r, r ≠ 30013 → r ≠ 30014 → r ≠ 30015 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cursors
  exec_block
  simp_all

/-- `swapBlock`: exchange the arrays, double the width, cost `4`. -/
theorem swap_exec (hc : WordsBounded W c) (h : c.nreg 30009 + c.nreg 30009 ≤ W) :
    ∃ c' k, Exec P W swapBlock c c' k ∧ k = 4 ∧
      c'.nreg 30007 = c.nreg 30008 ∧ c'.nreg 30008 = c.nreg 30007 ∧
      c'.nreg 30009 = c.nreg 30009 + c.nreg 30009 ∧
      (∀ r, r ≠ 30007 → r ≠ 30008 → r ≠ 30009 → r ≠ 30018 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swapBlock
  exec_block
  · simp_all
  simp_all
end pieces

/-! ## Segments -/
variable {m : ℕ → ℕ} {p n : ℕ}
/-- Dropping from a list read as a segment. -/
theorem drop_of_seg {l : List ℕ} (h : seg m p n = l) (d : ℕ) :
    l.drop d = seg m zttvc ztttv := by
  rw [← h, seg_drop]

/-- A nonempty segment starts with its first word. -/
theorem seg_pos (h : 0 < n) : seg m p n = m p :: seg m ztr ztkl := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by_omega⟩
  rw [seg_succ]; rfl

/-- A segment of length `0` is empty. -/
theorem seg_eq_nil (h : n = 0) : seg m p n = [] := by
  simp_all

/-- Rewriting the bounds of a segment. -/
theorem seg_arg {p p' n n' : ℕ} (hp : p = p') (hn : n = n') :
    seg m p n = seg m p' n' := by
  simp_all

/-! ## The merge loop -/
section merge
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {le : ℕ → ℕ → Bool} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The merge loop invariant** for the merge of `a = src[lo, mid)` and `b = src[mid, hi)` into
`dst[lo, hi)`, relative to the entry configuration `c₀` of the sort and the entry
configuration `cS` of the merge. -/
structure MergeInv (W : ℕ) (J : Config → Prop) (le : ℕ → ℕ → Bool) (Bc : Finset ℕ) (A₀ : ℕ)
    (c₀ cS : Config) (src dst lo mid hi : ℕ) (a b : List ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  one : c.nreg 30006 = 1
  rsrc : c.nreg 30007 = src
  rdst : c.nreg 30008 = dst
  rmid : c.nreg 30011 = mid
  rhi : c.nreg 30012 = hi
  keep : ∀ r, ztblq → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
    r ≠ 30013 → r ≠ 30014 → r ≠ 30015 → r ≠ 30016 → r ≠ 30018 → c.nreg r = cS.nreg r
  lo_i : lo ≤ c.nreg 30013
  i_mid : c.nreg 30013 ≤ mid
  mid_j : mid ≤ c.nreg 30014
  j_hi : c.nreg 30014 ≤ hi
  rk : c.nreg 30015 + mid = c.nreg 30013 + c.nreg 30014
  bsrc : src + hi ≤ W
  bdst : dst + hi + 1 ≤ W
  disj : src + hi ≤ dst + lo ∨ dst + hi ≤ src + lo
  dA : A₀ ≤ dst
  ma : seg c.nmem ztuaw ztodm = a
  mb : seg c.nmem ztuax ztjxw = b
  out : seg c.nmem zttjh ztfqf ++
    List.merge (a.drop ztrmc) (b.drop ztrmd) le = List.merge a b le
  mem : ∀ x, ztewo → c.nmem x = cS.nmem x
variable {c₀ cS : Config} {src dst lo mid hi : ℕ} {a b : List ℕ}

/-- The invariant survives changes of the comparator registers, the scratch registers and the
bands `Bc` (the comparator's writes). -/
theorem MergeInv.congr {c c' : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) (hw : WordsBounded W c')
    (hJ : J c') (hloc : Loc Bc A₀ c₀ c') (hm : c'.nmem = c.nmem)
    (hr : ∀ r, ztblq → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      r ≠ 30016 → r ≠ 30018 → c'.nreg r = c.nreg r) :
    MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c' := by
  have e := fun r (h1 : 30000 ≤ r ∧ r < 40000) (h2 : r ≠ 30000) (h3 : r ≠ 30001) (h4 : r ≠ 30002)
    (h5 : r ≠ 30016) (h6 : r ≠ 30018) => hr r ztfft h2 h3 h4 h5 h6
  have e6 := e 30006 by_omega by_omega by_omega by_omega by_omega by_omega
  have e7 := e 30007 by_omega by_omega by_omega by_omega by_omega by_omega
  have e8 := e 30008 by_omega by_omega by_omega by_omega by_omega by_omega
  have e11 := e 30011 by_omega by_omega by_omega by_omega by_omega by_omega
  have e12 := e 30012 by_omega by_omega by_omega by_omega by_omega by_omega
  have e13 := e 30013 by_omega by_omega by_omega by_omega by_omega by_omega
  have e14 := e 30014 by_omega by_omega by_omega by_omega by_omega by_omega
  have e15 := e 30015 by_omega by_omega by_omega by_omega by_omega by_omega
  exact
  { wb := hw, hJ := hJ, loc := hloc, one := e6.trans h.one, rsrc := e7.trans h.rsrc,
    rdst := e8.trans h.rdst, rmid := e11.trans h.rmid, rhi := e12.trans h.rhi,
    keep := fun r hr1 h0 h1 h2 h13 h14 h15 h16 h18 =>
      (hr r hr1 h0 h1 h2 h16 h18).trans (h.keep r hr1 h0 h1 h2 h13 h14 h15 h16 h18),
    lo_i := e13 ▸ h.lo_i, i_mid := e13 ▸ h.i_mid, mid_j := e14 ▸ h.mid_j, j_hi := e14 ▸ h.j_hi,
    rk := by rw [e13, e14, e15]; exact h.rk, bsrc := h.bsrc, bdst := h.bdst, disj := h.disj,
    dA := h.dA, ma := hm ▸ h.ma, mb := hm ▸ h.mb, out := by rw [hm, e13, e14, e15]; exact h.out,
    mem := fun x hx => by zvmwi; exact h.mem x hx }

/-- The memory after a store at `dst + k` (`lo ≤ k < hi`) reads the same on the source window
and outside `[dst + lo, dst + hi)`. -/
theorem store_facts {c : Config} (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) {k v : ℕ}
    (hk1 : lo ≤ k) (hk2 : k < hi) :
    seg ztmpc ztuaw ztodm = a ∧
      seg ztmpc ztuax ztjxw = b ∧
      (∀ x, ztewo → upd c.nmem (dst + k) v x = cS.nmem x) := by
  have := h.lo_i; have := h.i_mid; have := h.mid_j; have := h.j_hi; have := h.disj
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← h.ma]; apply seg_congr; intro t ht
    zubc
  · rw [← h.mb]; apply seg_congr; intro t ht
    zubc
  · zumyl; exact h.mem x hx

/-- **Taking the left head**: `takeL` then `k := k + 1` keeps the invariant, when the left run is
not exhausted and its head is `≤` the head of the right run (if any). -/
theorem stepL (hJs : JStable J A₀) {c : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) (hil : c.nreg 30013 < mid)
    (hle : c.nreg 30014 < hi →
      le ztyie ztyif = true) :
    ∃ c₃ c₄, Exec P W takeL c c₃ 5 ∧ Exec P W ztgwt c₃ c₄ 1 ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c₄ ∧
      c₄.nreg 30015 = c.nreg 30015 + 1 := by
  zqxe
  obtain ⟨c₃, k₃, e₃, rfl, hm₃, hi₃, hr₃, hrr₃, hrm₃, ho₃⟩ := takeL_exec (P := P) c h.wb
    ztepx ztntm ztntl
  zqxd
  obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := addN_char (P := P) w₃ 30015 30015 30006
    by_omega
  zqxh
  -- the new memory
  have hm₄ : c₄.nmem = upd c.nmem ztrov ztyie := by
    zugwn
  zqxg
  obtain ⟨sa, sb, sm⟩ := store_facts h (v := c.nmem ztegf) hlok hkhi
  -- registers
  have r₄ : ∀ r, r ≠ 30013 → r ≠ 30015 → r ≠ 30016 → r ≠ 30018 → c₄.nreg r = c.nreg r := by
    simp_all
  have i₄ : c₄.nreg 30013 = c.nreg 30013 + 1 := by
    simp_all
  have j₄ : c₄.nreg 30014 = c.nreg 30014 := by_simp_all
  have kk₄ : ztpns := by
    simp_all
  -- the sort-local step
  have hsl : ztumd := by
    zqxf
    · have := bandOf_sort hb
      grind
    · zudka
  zuffz
  -- the list step
  have hA : a.drop ztrmc =
      c.nmem ztegf :: a.drop (c.nreg 30013 + 1 - lo) := by
    rw [drop_of_seg h.ma, drop_of_seg h.ma, seg_pos by_omega]
    grind
  zumek
  zvmze at hout
  have hstep := merge_step_left hout (fun y ys' hy => by
    have hjh : c.nreg 30014 < hi := by
      zukr
      rw [drop_of_seg h.mb, seg_eq_nil by_omega] at hy
      grind
    rw [drop_of_seg h.mb, seg_pos by_omega] at hy
    grind)
  exact
  { wb := w₄, hJ := hJ₄, loc := h.loc.sl hsl,
    one := by_grind,
    rsrc := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rsrc,
    rdst := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rdst,
    rmid := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rmid,
    rhi := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rhi,
    keep := fun r _ _ _ _ h13 _ h15 h16 h18 =>
      (r₄ r h13 h15 h16 h18).trans (h.keep r ‹_› ‹_› ‹_› ‹_› h13 ‹_› h15 h16 h18),
    lo_i := by_omega, i_mid := by_omega, mid_j := by_omega,
    j_hi := by_omega, rk := by_omega, bsrc := h.bsrc,
    bdst := h.bdst, disj := h.disj, dA := h.dA, ma := by_grind,
    mb := by_grind,
    out := by
      rw [hm₄, i₄, j₄, kk₄, show c.nreg 30015 + 1 - lo = ztfqf + 1 by omega,
        seg_upd_end _ _ (fun x => by
          zuner)]
      omega,
    mem := fun x hx => by zupbs; grind }

/-- **Taking the right head**: `takeR` then `k := k + 1` keeps the invariant, when the right run
is not exhausted and the head of the left run (if any) is not `≤` its head. -/
theorem stepR (hJs : JStable J A₀) {c : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) (hjl : c.nreg 30014 < hi)
    (hle : c.nreg 30013 < mid →
      le ztyie ztyif = false) :
    ∃ c₃ c₄, Exec P W takeR c c₃ 5 ∧ Exec P W ztgwt c₃ c₄ 1 ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c₄ ∧
      c₄.nreg 30015 = c.nreg 30015 + 1 := by
  zqxe
  obtain ⟨c₃, k₃, e₃, rfl, hm₃, hi₃, hr₃, hrr₃, hrm₃, ho₃⟩ := takeR_exec (P := P) c h.wb
    ztepx ztntm ztntl
  zqxd
  obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := addN_char (P := P) w₃ 30015 30015 30006
    by_omega
  zqxh
  -- the new memory
  have hm₄ : c₄.nmem = upd c.nmem ztrov ztyif := by
    zugwn
  zqxg
  obtain ⟨sa, sb, sm⟩ := store_facts h (v := c.nmem ztegg) hlok hkhi
  -- registers
  have r₄ : ∀ r, r ≠ 30014 → r ≠ 30015 → r ≠ 30016 → r ≠ 30018 → c₄.nreg r = c.nreg r := by
    simp_all
  have j₄ : c₄.nreg 30014 = c.nreg 30014 + 1 := by
    simp_all
  have i₄ : c₄.nreg 30013 = c.nreg 30013 := by_simp_all
  have kk₄ : ztpns := by
    simp_all
  -- the sort-local step
  have hsl : ztumd := by
    zqxf
    · have := bandOf_sort hb
      grind
    · zudka
  zuffz
  -- the list step
  have hB : b.drop ztrmd =
      c.nmem ztegg :: b.drop (c.nreg 30014 + 1 - mid) := by
    rw [drop_of_seg h.mb, drop_of_seg h.mb, seg_pos by_omega]
    grind
  zumek
  rw [hB] at hout
  have hstep := merge_step_right hout (fun x xs' hx => by
    have hil : c.nreg 30013 < mid := by
      zukr
      rw [drop_of_seg h.ma, seg_eq_nil by_omega] at hx
      grind
    rw [drop_of_seg h.ma, seg_pos by_omega] at hx
    grind)
  exact
  { wb := w₄, hJ := hJ₄, loc := h.loc.sl hsl,
    one := by_grind,
    rsrc := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rsrc,
    rdst := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rdst,
    rmid := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rmid,
    rhi := (r₄ _ by_omega by_omega by_omega by_omega).trans h.rhi,
    keep := fun r _ _ _ _ _ h14 h15 h16 h18 =>
      (r₄ r h14 h15 h16 h18).trans (h.keep r ‹_› ‹_› ‹_› ‹_› ‹_› h14 h15 h16 h18),
    lo_i := by_omega, i_mid := by_omega,
    mid_j := by_omega, j_hi := by_omega, rk := by_omega, bsrc := h.bsrc,
    bdst := h.bdst, disj := h.disj, dA := h.dA, ma := by_grind,
    mb := by_grind,
    out := by
      rw [hm₄, i₄, j₄, kk₄, show c.nreg 30015 + 1 - lo = ztfqf + 1 by omega,
        seg_upd_end _ _ (fun x => by
          zuner)]
      omega,
    mem := fun x hx => by zupbs; grind }

/-- The comparator keeps the global frame. -/
theorem Loc.cmp {c₀ c c' : Config} (h : Loc Bc A₀ c₀ c)
    (hr : ∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → ztdyw →
      c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) (hm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) : Loc Bc A₀ c₀ c' := by
  refine ⟨fun r h1 h2 h3 => ?_, fun r h1 => (hrr r h1).trans zttlj,
    fun a ha => by zvmwi; exact h.2.2.1 a ha, hrm.trans h.2.2.2.1, ho.trans h.2.2.2.2⟩
  have := bandOf_sort h2
  zufsa
variable {cmp : Stmt} {κ : ℕ}
/-- **One iteration of the merge loop** (cost `≤ κ + 14`). -/
theorem mergeBody_inv (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c)
    (hk : c.nreg 30015 < c.nreg 30012) :
    ∃ c' k, Exec P W ztvyy c c' k ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c' ∧ k ≤ κ + 14 ∧
      c'.nreg 30015 = c.nreg 30015 + 1 := by
  have hj := h.j_hi
  have hrk := h.rk
  zuhzh

  zumdw
  have him := h.i_mid
  rw [h.rhi] at hk
  unfold mergeBody mergeStep
  by_cases hi1 : c.nreg 30013 < mid
  · have t1 : c.nreg 30013 < c.nreg 30011 := by zupbt; omega
    by_cases hj1 : c.nreg 30014 < hi
    · have t2 : c.nreg 30014 < c.nreg 30012 := by rw [h.rhi]; omega
      -- load and compare
      obtain ⟨c₁, k₁, e₁, rfl, x₁, y₁, r₁, m₁, rr₁, rm₁, o₁⟩ := cmpLoad_exec (P := P) c h.wb
        ztepx ztepx
      have sl₁ : ztplf := ⟨fun r hb _ => by
          have := bandOf_sort hb; grind, rr₁,
        by simp_all, rm₁, o₁⟩
      have I₁ := h.congr e₁.wb_right (hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1
        sl₁.2.2.2.2) (h.loc.sl sl₁) m₁ by_simp_all
      obtain ⟨c₂, k₂, e₂, hk₂, hJ₂, bit₂, r₂, rr₂, m₂, rm₂, o₂⟩ := hcmp c₁ e₁.wb_right I₁.hJ
      have I₂ := I₁.congr e₂.wb_right hJ₂ (I₁.loc.cmp r₂ rr₂ m₂ rm₂ o₂) m₂
        (fun r hr h0 h1' h2' _ _ => r₂ r h0 h1' h2' (by
          zubbc
          · left; intro hm; apply hB
            have : bandOf r = bSort := by unfold bandOf bSort; omega
            simp_all
          omega))
      have i₂ : c₂.nreg 30013 = c.nreg 30013 := by
        rw [r₂ _ by_omega by_omega by_omega (Or.inl (by
          tauto)),
          r₁ _ by_omega by_omega by_omega]
      have j₂ : c₂.nreg 30014 = c.nreg 30014 := by
        rw [r₂ _ by_omega by_omega by_omega (Or.inl (by
          tauto)),
          r₁ _ by_omega by_omega by_omega]
      have k₂e : c₂.nreg 30015 = c.nreg 30015 := by
        rw [r₂ _ by_omega by_omega by_omega (Or.inl (by
          tauto)),
          r₁ _ by_omega by_omega by_omega]
      have mm₂ := m₂.trans m₁
      rw [x₁, y₁, h.rsrc] at bit₂
      by_cases hle : le ztyie ztyif = true
      · rw [ite_eq_left hle] at bit₂
        obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepL hJs I₂ by_omega
          by_simp_all
        refine ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_true t2 (.seq e₁ (.seq e₂
          (.ifLtN_false ztlgx e₃))))) e₄, I₄, by_omega,
          by omega⟩
      · rw [ite_eq_right hle] at bit₂
        obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepR hJs I₂ by_omega
          by_simp_all
        refine ⟨c₄, _, .seq (.ifLtN_true t1 (.ifLtN_true t2 (.seq e₁ (.seq e₂
          (.ifLtN_true ztlgx e₃))))) e₄, I₄, by_omega,
          by omega⟩
    · have t2 : ¬ c.nreg 30014 < c.nreg 30012 := by rw [h.rhi]; omega
      obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepL hJs h hi1 by_omega
      exact ⟨c₄, _, .seq (.ifLtN_true t1 ztnag) e₄, I₄, by_omega, k₄⟩
  · have t1 : ¬ c.nreg 30013 < c.nreg 30011 := by zupbt; omega
    obtain ⟨c₃, c₄, e₃, e₄, I₄, k₄⟩ := stepR hJs h by_omega by_omega
    exact ⟨c₄, _, .seq ztspb e₄, I₄, by_omega, k₄⟩

/-- **The merge loop**: from the invariant, the loop ends with `dst[lo, hi) = merge a b`, in at
most `(κ + 16) (hi - k) + 2` steps. -/
theorem mergeLoop_inv (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config}
    (h : MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c) :
    ∃ c' k, Exec P W ztvyz c c' k ∧
      MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b c' ∧
      k ≤ (κ + 16) * (hi - c.nreg 30015) + 2 ∧
      seg c'.nmem zttjh ztcw = List.merge a b le := by
  obtain ⟨c', k, e, I', hex, hk⟩ := Exec.whileLtN_bounded
    (MergeInv W J le Bc A₀ c₀ cS src dst lo mid hi a b) (fun d => hi - d.nreg 30015) (κ + 14)
    ztpf (fun d hd ht => by
      obtain ⟨d', k, e, I, hk, hk'⟩ := mergeBody_inv (P := P) hcmp hJs hB hd ht
      have := hd.rhi
      exact ⟨d', k, e, I, hk, by_omega⟩) h
  refine ⟨c', k, e, I', hk, ?_⟩
  have := I'.out
  have hi' := I'.rhi
  have h1 := I'.i_mid
  have h2 := I'.j_hi
  have h3 := I'.rk
  have h4 := I'.lo_i
  have h5 := I'.mid_j
  rw [hi'] at hex
  rw [List.drop_of_length_le (by rw [← I'.ma]; simp; omega),
    List.drop_of_length_le (by rw [← I'.mb]; simp; omega), List.nil_merge, List.append_nil,
    show c'.nreg 30015 - lo = hi - lo by omega] at this
  omega
end merge

/-! ## One pass -/
section pass
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {le : ℕ → ℕ → Bool} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the loop over the pairs of runs** of a pass with width `w` from the
source array `src` (holding `l`) to `dst`, relative to the entry configuration `c₀` of the sort
and `cP` of the pass: `dst[0, lo)` holds the pass of `l[0, lo)`. -/
structure PairInv (W : ℕ) (J : Config → Prop) (le : ℕ → ℕ → Bool) (Bc : Finset ℕ) (A₀ : ℕ)
    (c₀ cP : Config) (src dst w K : ℕ) (l : List ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  rK : c.nreg 30004 = K
  one : c.nreg 30006 = 1
  rsrc : c.nreg 30007 = src
  rdst : c.nreg 30008 = dst
  rw : c.nreg 30009 = w
  keep : ∀ r, ztblq → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
    ztofs → r ≠ 30018 → c.nreg r = cP.nreg r
  wpos : 0 < w
  wK : w < K
  lo_K : c.nreg 30010 ≤ K
  lo_t : c.nreg 30010 = K ∨ ∃ t, c.nreg 30010 = t * ztyx
  arr : (src = A₀ ∧ dst = A₀ + K) ∨ (src = A₀ + K ∧ dst = A₀)
  bW : A₀ + 2 * K + 1 ≤ W
  ml : seg c.nmem src K = l
  out : seg c.nmem dst ztvig = mpass le w (l.take ztvig)
  mem : ∀ x, (x < dst ∨ dst + K ≤ x) → c.nmem x = cP.nmem x
variable {c₀ cP : Config} {src dst w K : ℕ} {l : List ℕ}

/-- The pass of a prefix made of whole double blocks, extended by one double block. -/
theorem mpass_take_step (hw : 0 < w) {lo mid hi t : ℕ} (hlo : lo = t * ztyx)
    (hloK : lo < l.length) (hmid : mid = min zttsl l.length)
    (hhi : hi = min ztodl l.length) :
    mpass le w (l.take hi) = mpass le w (l.take lo) ++
      List.merge ((l.drop lo).take ztodm) ((l.drop mid).take ztjxw) le := by
  have e1 : l.take hi = l.take lo ++ (l.drop lo).take ztcw := by
    rw [← List.take_add]; grind
  have hlen : (l.take lo).length = t * ztyx := by
    grind
  have hb : hi - lo ≤ 2 * w := by_omega
  have hlen2 : ((l.drop lo).take ztcw).length ≤ 2 * w := by
    grind
  rw [e1, mpass_append hw t _ _ hlen, mpass_small hw _ hlen2]
  zugjz
  · rw [List.take_take]; grind
  · rw [List.drop_take, List.drop_drop]
    by_cases h : lo + w ≤ l.length
    · grind
    · rw [List.drop_of_length_le by_omega, List.drop_of_length_le by_omega]
      simp
variable {cmp : Stmt} {κ : ℕ}
/-- **One iteration of the pair loop**: merge one pair of runs. -/
theorem pairBody_inv (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config}
    (h : PairInv W J le Bc A₀ c₀ cP src dst w K l c) (hlt : c.nreg 30010 < c.nreg 30004) :
    ∃ c' k, Exec P W ztwbj c c' k ∧ PairInv W J le Bc A₀ c₀ cP src dst w K l c' ∧
      ztcxg * (K - c'.nreg 30010) + k + 2 ≤ ztcxg * ztrjr := by
  zuhwx

  have hwK := h.wK
  have hwp := h.wpos
  zumda
  zukst
  set lo := c.nreg 30010 with hlo
  set mid := min zttsl K with hmid
  set hi := min ztodl K with hhi
  -- mid, hi
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ := clamp_exec (P := P) h.wb 30011 30010
    by_omega (by rw [h.rw]; omega)
  have n₁' : c₁.nreg = upd c.nreg 30011 mid := by rw [n₁, h.rw, hK]
  have b₁ : c₁.nreg 30011 + c₁.nreg 30009 ≤ W := by
    rw [n₁', Machine.upd_same, Machine.upd_other _ _ _ by_omega, h.rw]; omega
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ := clamp_exec (P := P) e₁.wb_right 30012 30011
    by_omega b₁
  have n₂' : c₂.nreg = upd (upd c.nreg 30011 mid) 30012 hi := by
    rw [n₂, n₁']; zumzo
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, h.rw, hK]
  obtain ⟨c₃, k₃, e₃, rfl, i₃, j₃, kk₃, r₃, m₃, rr₃, rm₃, o₃⟩ := cursors_exec (P := P) e₂.wb_right
  have R₃ : ∀ r, r ≠ 30011 → r ≠ 30012 → r ≠ 30013 → r ≠ 30014 → r ≠ 30015 →
      c₃.nreg r = c.nreg r := by
    zuetf
    rw [r₃ r h3 h4 h5, n₂', Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]
  have mid₃ : c₃.nreg 30011 = mid := by
    rw [r₃ _ by_omega by_omega by_omega, n₂', Machine.upd_other _ _ _ by_omega,
      Machine.upd_same]
  have hi₃ : c₃.nreg 30012 = hi := by
    rw [r₃ _ by_omega by_omega by_omega, n₂', Machine.upd_same]
  have lo₂ : c₂.nreg 30010 = lo := by
    grind
  have mid₂ : c₂.nreg 30011 = mid := by
    grind
  rw [lo₂] at i₃ kk₃
  rw [mid₂] at j₃
  have mm₃ : ztckd := by_grind
  have sl₃ : SL A₀ c c₃ := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind,
    by grind, by_grind, by_grind, by_grind⟩
  have hJ₃ := hJs c c₃ h.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2
  -- the merge invariant at entry
  have I₃ : MergeInv W J le Bc A₀ c₀ c₃ src dst lo mid hi _
      _ c₃ :=
    { wb := e₃.wb_right, hJ := hJ₃, loc := h.loc.sl sl₃,
      one := (R₃ _ by_omega by_omega by_omega by_omega by_omega).trans h.one,
      rsrc := (R₃ _ by_omega by_omega by_omega by_omega by_omega).trans h.rsrc,
      rdst := (R₃ _ by_omega by_omega by_omega by_omega by_omega).trans h.rdst,
      rmid := mid₃, rhi := hi₃, keep := by_omega,
      lo_i := by rw [i₃], i_mid := by_omega, mid_j := by rw [j₃],
      j_hi := by_omega, rk := by_omega,
      bsrc := by_omega, bdst := by_omega, disj := by_omega, dA := by_omega, ma := rfl, mb := rfl,
      out := by rw [kk₃, i₃, j₃, Nat.sub_self, Nat.sub_self, seg_zero, List.drop_zero,
        List.drop_zero, List.nil_append],
      mem := by_omega }
  obtain ⟨c₄, k₄, e₄, I₄, hk₄, hseg₄⟩ := mergeLoop_inv (P := P) hcmp hJs hB I₃
  rw [kk₃] at hk₄
  obtain ⟨c₅, e₅, n₅, m₅, rr₅, rm₅, o₅⟩ := copyN_char (P := P) I₄.wb 30010 30012
  have hi₄ := I₄.rhi
  have lo₅ : c₅.nreg 30010 = hi := by rw [n₅, Machine.upd_same, hi₄]
  have R₅ : ∀ r, r ≠ 30010 → c₅.nreg r = c₄.nreg r := fun r hr => by
    zugwr
  have sl₅ : ztumf := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind, rr₅, by_grind, rm₅, o₅⟩
  -- registers of `c₅` outside the merge scratch
  have K₅ : ∀ r, ztblq → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      ztofs → r ≠ 30018 → c₅.nreg r = c.nreg r := by
    zuibz
    rw [R₅ r by_omega, I₄.keep r hr h0 h1 h2 by_omega by_omega by_omega by_omega h4,
      R₃ r by_omega by_omega by_omega by_omega by_omega]
  -- memory of `c₄`
  have M₄ : ∀ x, ztewo → c₄.nmem x = c.nmem x := fun x hx => by
    rw [I₄.mem x hx, mm₃]
  have hl : l.length = K := by rw [← h.ml, seg_length]
  refine ⟨c₅, _, .seq e₁ ztbq, ?_, ?_⟩
  · exact
    { wb := e₅.wb_right, hJ := hJs c₄ c₅ I₄.hJ sl₅.1 sl₅.2.1 sl₅.2.2.1 sl₅.2.2.2.1 sl₅.2.2.2.2,
      loc := I₄.loc.sl sl₅,
      rK := by_grind,
      one := (K₅ _ by_omega by_omega by_omega by_omega by_omega
        by_omega).trans h.one,
      rsrc := (K₅ _ by_omega by_omega by_omega by_omega by_omega
        by_omega).trans h.rsrc,
      rdst := (K₅ _ by_omega by_omega by_omega by_omega by_omega
        by_omega).trans h.rdst,
      rw := (K₅ _ by_omega by_omega by_omega by_omega by_omega
        by_omega).trans h.rw,
      keep := fun r hr h0 h1 h2 h3 h4 => (K₅ r hr h0 h1 h2 h3 h4).trans
        ztmkl,
      wpos := hwp, wK := hwK, lo_K := by_omega,
      lo_t := by
        zumom
        rcases h.lo_t with h' | ⟨t, ht⟩
        · omega
        · by_cases hc : lo + 2 * w ≤ K
          · right; exact ⟨t + 1, by rw [Nat.succ_mul]; omega⟩
          omega,
      arr := harr, bW := hbW,
      ml := by
        rw [m₅, ← h.ml]; apply seg_congr; intro t ht
        exact M₄ _ by_omega,
      out := by
        rw [lo₅, m₅, show hi = lo + ztcw by omega, seg_add, hseg₄]
        have t0 : ∃ t, lo = t * ztyx := by
          rcases h.lo_t with h' | ht
          · omega
          omega
        obtain ⟨t, ht⟩ := t0
        rw [show lo + ztcw = hi by omega,
          mpass_take_step hwp ht by_omega by_grind
            (show hi = min ztodl l.length by zvnen)]
        zucr
        · rw [← h.out]; apply seg_congr; grind
        · rw [mm₃, ← h.ml, seg_drop, seg_take, seg_drop, seg_take]
          zucr
          · zulvw
          · by_cases hc : mid < hi
            · zulvw
            · rw [seg_eq_nil by_omega, seg_eq_nil by_omega],
      mem := fun x hx => by
        rw [m₅, M₄ x by_omega]; exact h.mem x hx }
  · zumom
    have e1 : K - lo = (K - hi) + ztcw := by_omega
    rw [e1, Nat.mul_add]
    have : 1 ≤ hi - lo := by_omega
    grind

/-- **The pair loop**: one whole pass, `dst[0, K) = mpass w l`, cost `≤ (κ + 30) K + 2`. -/
theorem pairLoop_inv (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc) {c : Config}
    (h : PairInv W J le Bc A₀ c₀ cP src dst w K l c) :
    ∃ c' k, Exec P W ztwbl c c' k ∧ PairInv W J le Bc A₀ c₀ cP src dst w K l c' ∧
      k ≤ ztcxg * ztrjr + 2 ∧ c'.nreg 30010 = K ∧
      seg c'.nmem dst K = mpass le w l := by
  obtain ⟨c', k, e, I', hex, hk⟩ := Exec.whileLtN_potential
    (PairInv W J le Bc A₀ c₀ cP src dst w K l) (fun d => ztcxg * (K - d.nreg 30010))
    ztpf (fun d hd ht => pairBody_inv (P := P) hcmp hJs hB hd ht) h
  zuiwe
  have hlo := I'.lo_K
  have hlK : c'.nreg 30010 = K := by_omega
  refine ⟨c', k, e, I', hk, hlK, ?_⟩
  have := I'.out
  rw [hlK, List.take_of_length_le (by rw [← I'.ml, seg_length])] at this
  omega
end pass

/-! ## The passes -/
section passes
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {le : ℕ → ℕ → Bool} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the pass loop** (width `w = 2 ^ p`), relative to the entry configuration
`c₀` of the sort and the configuration `cC` at the start of the passes: the source array holds a
permutation of `L` whose blocks of width `w` are sorted. -/
structure PassInv (W : ℕ) (J : Config → Prop) (le : ℕ → ℕ → Bool) (Bc : Finset ℕ) (A₀ : ℕ)
    (c₀ cC : Config) (K : ℕ) (L : List ℕ) (p : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  rK : c.nreg 30004 = K
  one : c.nreg 30006 = 1
  rw : c.nreg 30009 = 2 ^ p
  keep : ∀ r, ztblq → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
    ztofr → r ≠ 30018 → c.nreg r = cC.nreg r
  arr : (c.nreg 30007 = A₀ ∧ c.nreg 30008 = A₀ + K) ∨ (c.nreg 30007 = A₀ + K ∧ c.nreg 30008 = A₀)
  bW : A₀ + 2 * K + 1 ≤ W
  lst : ∃ l, seg c.nmem (c.nreg 30007) K = l ∧ l.Perm L ∧ ChunkSorted le ztsss l
variable {c₀ cC : Config} {K : ℕ} {L : List ℕ}
variable {cmp : Stmt} {κ : ℕ}
/-- **One pass** (cost `≤ (κ + 30) K + 7`). -/
theorem passBody_inv (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    {p : ℕ} {c : Config} (h : PassInv W J le Bc A₀ c₀ cC K L p c)
    (hlt : c.nreg 30009 < c.nreg 30004) :
    ∃ c' k, Exec P W ztwbn c c' k ∧ PassInv W J le Bc A₀ c₀ cC K L ztr c' ∧
      k ≤ ztcxg * K + 7 := by
  zuhwx

  have hw := h.rw
  rw [hK, hw] at hlt
  obtain ⟨l, hl, hperm, hsorted⟩ := h.lst
  have hpos := Nat.two_pow_pos p
  obtain ⟨c₁, e₁, n₁, m₁, rr₁, rm₁, o₁⟩ := constN_char (P := P) h.wb 30010 0 by_omega
  have R₁ : ∀ r, r ≠ 30010 → c₁.nreg r = c.nreg r := by_simp_all
  have sl₁ : ztplf := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind, rr₁, by_simp_all, rm₁, o₁⟩
  have I₁ : PairInv W J le Bc A₀ c₀ c₁ _ _ _ K l c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := h.loc.sl sl₁, rK := by_simp_all, one := (R₁ _ by_omega).trans h.one,
      rsrc := by_simp_all, rdst := by_simp_all, rw := by_simp_all,
      keep := by_omega, wpos := hpos, wK := hlt,
      lo_K := by_simp_all,
      lo_t := by_simp_all, arr := h.arr, bW := hbW,
      ml := by_simp_all,
      out := by rw [n₁, Machine.upd_same, seg_zero, List.take_zero, mpass_nil],
      mem := by_omega }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hlo₂, hseg₂⟩ := pairLoop_inv (P := P) hcmp hJs hB I₁
  have hw₂ := I₂.rw
  obtain ⟨c₃, k₃, e₃, rfl, s₃, d₃, w₃, r₃, m₃, rr₃, rm₃, o₃⟩ := swap_exec (P := P) I₂.wb
    by_omega
  have sl₃ : ztume := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind, rr₃,
    by simp_all, rm₃, o₃⟩
  have K₃ : ∀ r, ztblq → r ≠ 30000 → r ≠ 30001 → r ≠ 30002 →
      ztofr → r ≠ 30018 → c₃.nreg r = c.nreg r := by
    zuibz
    rw [r₃ r by_omega by_omega by_omega h4, I₂.keep r hr h0 h1 h2 by_omega h4,
      R₁ r by_omega]
  have lo₁ : c₁.nreg 30010 = 0 := by rw [n₁, Machine.upd_same]
  refine ⟨c₃, _, .seq e₁ ztcr, ?_, by_grind⟩
  zumda
  have hs₂ := I₂.rsrc
  have hd₂ := I₂.rdst
  exact
  { wb := e₃.wb_right, hJ := hJs c₂ c₃ I₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
    loc := I₂.loc.sl sl₃,
    rK := by_grind,
    one := (K₃ _ by_omega by_omega by_omega by_omega by_omega
      by_omega).trans h.one,
    rw := by_omega,
    keep := fun r hr h0 h1 h2 h3 h4 => (K₃ r hr h0 h1 h2 h3 h4).trans ztmkl,
    arr := by_omega,
    bW := hbW,
    lst := ⟨mpass le ztsss l, by_grind, (mpass_perm _ _).trans hperm,
      by rw [pow_succ']; exact chunkSorted_mpass trans total hpos hsorted⟩ }

/-- **The passes**: from `w = 2 ^ p` until `w ≥ K`; at the end the source array is sorted.
Cost `≤ ((κ + 30) K + 9) (⌈log₂ K⌉ - p) + 2`. -/
theorem passLoop_inv (hcmp : CmpOK P W cmp Bc J le κ)
    (hJs : JStable J A₀) (hB : bSort ∉ Bc)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    {p : ℕ} {c : Config} (h : PassInv W J le Bc A₀ c₀ cC K L p c) :
    ∃ c' k, Exec P W ztwbo c c' k ∧ (∃ p', PassInv W J le Bc A₀ c₀ cC K L p' c') ∧
      k ≤ ztzho * (Nat.clog 2 K - p) + 2 ∧
      ∃ l, seg c'.nmem (c'.nreg 30007) K = l ∧ l.Perm L ∧ l.Pairwise fun a b => le a b := by
  obtain ⟨c', k, e, ⟨p', I'⟩, hex, hk⟩ := Exec.whileLtN_bounded
    (fun d => ∃ q, PassInv W J le Bc A₀ c₀ cC K L q d)
    (fun d => Nat.clog 2 K - Nat.log 2 (d.nreg 30009)) (ztcxg * K + 7)
    (fun _ ⟨_, h⟩ => h.wb) (fun d ⟨q, hd⟩ ht => by
      obtain ⟨d', k, e, I, hk⟩ := passBody_inv (P := P) hcmp hJs hB trans total hd ht
      refine ⟨d', k, e, by_grind, hk, ?_⟩
      have h1 := hd.rw
      have h2 := I.rw
      have h3 := hd.rK
      rw [h1, h3] at ht
      have hq := (Nat.lt_clog_iff_pow_lt by_norm_num).2 ht
      rw [h1, h2, Nat.log_pow by_norm_num, Nat.log_pow by_norm_num]
      omega) ⟨p, h⟩
  refine ⟨c', k, e, by_grind, by rw [h.rw, Nat.log_pow by_norm_num] at hk; exact hk, ?_⟩
  obtain ⟨l, hl, hperm, hs⟩ := I'.lst
  have hw := I'.rw
  zuiwe
  rw [hw, hK] at hex
  refine ⟨l, hl, hperm, pairwise_of_chunkSorted hs ?_⟩
  rw [← hl, seg_length]; omega
end passes

/-! ## The copy loop -/
section copy
variable {P : Polygon} {W : ℕ}
variable {c : Config}
/-- `copyBody`: `A₀[i] := S[i]`, `i := i + 1`, `ALLOC := ALLOC + 2`, cost `6`. -/
theorem copyBody_exec (hc : WordsBounded W c) (h1 : c.nreg 30003 + c.nreg 30013 ≤ W)
    (h2 : c.nreg 30007 + c.nreg 30013 ≤ W) (h3 : c.nreg 30013 + c.nreg 30006 ≤ W)
    (h4 : c.nreg 9999 + c.nreg 30017 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 6 ∧
      c'.nmem = upd c.nmem ztjsa (c.nmem (c.nreg 30003 + c.nreg 30013)) ∧
      c'.nreg 30013 = c.nreg 30013 + c.nreg 30006 ∧ c'.nreg 9999 = c.nreg 9999 + c.nreg 30017 ∧
      (∀ r, r ≠ 30013 → r ≠ 30016 → r ≠ 30018 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold copyBody
  exec_block
  · zubvv
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- `sortInit`: the constants, the arrays `A₀ = ALLOC`, `A₀ + K`, `i := 0`; cost `5`. -/
theorem sortInit_exec (hc : WordsBounded W c) (h1 : 2 ≤ W)
    (h2 : c.nreg 9999 + c.nreg 30004 ≤ W) :
    ∃ c' k, Exec P W sortInit c c' k ∧ k = 5 ∧
      c'.nreg 30006 = 1 ∧ c'.nreg 30017 = 2 ∧ c'.nreg 30007 = c.nreg 9999 ∧
      c'.nreg 30008 = c.nreg 9999 + c.nreg 30004 ∧ c'.nreg 30013 = 0 ∧
      (∀ r, r ≠ 30006 → r ≠ 30017 → r ≠ 30007 → r ≠ 30008 → r ≠ 30013 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sortInit
  exec_block
  · omega
  · omega
  · simp_all
  · omega
  simp_all
variable {J : Config → Prop} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The copy loop invariant**, relative to the entry configuration `c₀` of the sort: the first
`i` items are copied to `A₀`, and the allocator is `A₀ + 2 i`. -/
structure CopyInv (W : ℕ) (J : Config → Prop) (Bc : Finset ℕ) (A₀ : ℕ) (c₀ : Config)
    (S K : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : Loc Bc A₀ c₀ c
  rS : c.nreg 30003 = S
  rK : c.nreg 30004 = K
  one : c.nreg 30006 = 1
  two : c.nreg 30017 = 2
  rsrc : c.nreg 30007 = A₀
  rdst : c.nreg 30008 = A₀ + K
  iK : c.nreg 30013 ≤ K
  alloc : c.nreg ALLOC = A₀ + 2 * c.nreg 30013
  bS : S + K ≤ A₀
  bW : A₀ + 2 * K + 1 ≤ W
  cp : seg c.nmem A₀ ztvih = seg c₀.nmem S ztvih
variable {c₀ : Config} {S K : ℕ}

/-- **The copy loop**: cost `≤ 8 K + 2`, and the allocator grows by at most the cost. -/
theorem copyLoop_inv (hJs : JStable J A₀) {c : Config} (h : CopyInv W J Bc A₀ c₀ S K c) :
    ∃ c' k, Exec P W copyLoop c c' k ∧ CopyInv W J Bc A₀ c₀ S K c' ∧ c'.nreg 30013 = K ∧
      k ≤ 8 * (K - c.nreg 30013) + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, e, I', hex, hk, hψ⟩ := whileLtN_potential_lb (P := P) (a := 30013) (b := 30004)
    (CopyInv W J Bc A₀ c₀ S K) (fun d => 8 * (K - d.nreg 30013)) ztqnp
    ztpf (fun d hd ht => by
      have := hd.iK; have := hd.alloc; have := hd.bS; have := hd.bW
      have hK := hd.rK
      rw [hK] at ht
      obtain ⟨d', k, e, rfl, m', i', a', r', rr', rm', o'⟩ := copyBody_exec (P := P) hd.wb
        (by rw [hd.rS]; omega) ztntr (by zunsz; omega)
        (by rw [show (9999 : ℕ) = ALLOC from rfl, hd.alloc, hd.two]; omega)
      have sl : SL A₀ d d' := ⟨fun r hb ha => by
          have := bandOf_sort hb
          exact r' r by_omega by_omega by_omega ha, rr',
        fun x hx => by rw [m', Machine.upd_other _ _ _ ztntr], rm', o'⟩
      have hi' : d'.nreg 30013 = d.nreg 30013 + 1 := by rw [i', hd.one]
      refine ⟨d', 6, e, ?_, by_omega, by
        show d'.nreg 9999 ≤ d.nreg 9999 + 6
        rw [a', hd.two]; omega⟩
      exact
      { wb := e.wb_right, hJ := hJs d d' hd.hJ sl.1 sl.2.1 sl.2.2.1 sl.2.2.2.1 sl.2.2.2.2,
        loc := hd.loc.sl sl,
        rS := (r' _ by_omega by_omega by_omega by_omega).trans hd.rS,
        rK := by_simp_all,
        one := by_simp_all,
        two := (r' _ by_omega by_omega by_omega by_omega).trans hd.two,
        rsrc := (r' _ by_omega by_omega by_omega by_omega).trans hd.rsrc,
        rdst := (r' _ by_omega by_omega by_omega by_omega).trans hd.rdst,
        iK := by_omega,
        alloc := by
          show d'.nreg 9999 = _
          rw [a', hi', hd.two, show (9999 : ℕ) = ALLOC from rfl, hd.alloc]; omega,
        bS := hd.bS, bW := hd.bW,
        cp := by
          rw [hi', m', hd.rsrc, hd.rS,
            seg_upd_end _ _ (fun x => by
              rfl), seg_snoc, hd.cp]
          zugjz
          exact (hd.loc.2.2.1 _ by_omega) }) h
  have := I'.iK
  zuiwe
  rw [hK] at hex
  exact ⟨c', k, e, I', by_omega, hk, hψ⟩
end copy

/-! ## The sort -/

/-- The cost bound dominates the cost of the phases. -/
theorem sortCost_ge (κ K : ℕ) :
    5 + (8 * K + 2) + 1 + (ztzho * Nat.clog 2 K + 2) + 1 ≤ sortCost κ K := by
  unfold sortCost
  have hc : Nat.clog 2 K ≤ K := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  grind

/-- The cost bound leaves room for the two arrays. -/
theorem sortCost_room (κ K : ℕ) : 2 * K + 2 ≤ sortCost κ K := by
  unfold sortCost
  grind

/-- **The sort meets its specification** (at the level of executions).  From a word-bounded
configuration `c` satisfying `J`, with the items `L` stored at `S = sr 3` below the allocator,
`K = |L|` in `sr 4`, and room for `sortCost κ K` cells above the allocator, `sortStmt cmp` runs in
at most `sortCost κ K` steps and leaves in `sr 5` the base of a fresh array (between the old and
the new allocator) holding a permutation of `L` sorted for `le`; it keeps `J` and respects
`Frame (insert bSort Bc)`.  Hypotheses on the comparator: `CmpOK` with bands `Bc ∌ bSort`, `le`
transitive and total, and `J` insensitive to the sort's own writes (`JStable`). -/
theorem sortStmt_exec {P : Polygon} {W : ℕ} {cmp : Stmt} {Bc : Finset ℕ} {J : Config → Prop}
    {le : ℕ → ℕ → Bool} {κ : ℕ} (hcmp : CmpOK P W cmp Bc J le κ) (hB : bSort ∉ Bc)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    {c : Config} (hw : WordsBounded W c) (hJ : J c) (hJs : JStable J ztm)
    (L : List ℕ) (hL : seg c.nmem ztvie L.length = L) (hK : c.nreg 30004 = L.length)
    (hS : c.nreg 30003 + L.length ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + sortCost κ L.length ≤ W) :
    ∃ c' k, Exec P W ztwen c c' k ∧ k ≤ sortCost κ L.length ∧ J c' ∧
      Frame zttpk c c' k ∧
      c.nreg ALLOC ≤ c'.nreg 30005 ∧ c'.nreg 30005 + L.length ≤ c'.nreg ALLOC ∧
      ∃ L', seg c'.nmem ztvgl L.length = L' ∧ L'.Perm L ∧
        L'.Pairwise fun a b => le a b := by
  zuce
  zuvu
  have hr := sortCost_room κ K
  zubfv
  -- initialisation
  obtain ⟨c₁, k₁, e₁, rfl, o₁, t₁, s₁, d₁, i₁, r₁, m₁, rr₁, rm₁, out₁⟩ := sortInit_exec (P := P) hw
    by_omega by_omega
  have sl₁ : ztplf := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind,
    rr₁, by_simp_all, rm₁, out₁⟩
  have C₁ : CopyInv W J Bc A₀ c _ K c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (Loc.refl Bc A₀ c).sl sl₁,
      rS := by_simp_all,
      rK := by_simp_all,
      one := o₁, two := t₁, rsrc := s₁, rdst := by_omega,
      iK := by_omega,
      alloc := by rw [i₁, show ALLOC = 9999 from rfl, r₁ _ by_omega by_omega by_omega
        by_omega by_omega]; rfl,
      bS := hS, bW := by_omega, cp := by_simp_all }
  -- the copy
  obtain ⟨c₂, k₂, e₂, C₂, hi₂, hk₂, ha₂⟩ := copyLoop_inv (P := P) hJs C₁
  have hal₂ := C₂.alloc
  have hal₁ := C₁.alloc
  rw [hi₂] at hal₂
  rw [i₁] at hal₁ hk₂
  -- the width
  obtain ⟨c₃, e₃, n₃, m₃, rr₃, rm₃, out₃⟩ := constN_char (P := P) C₂.wb 30009 1 by_omega
  have R₃ : ∀ r, r ≠ 30009 → c₃.nreg r = c₂.nreg r := by_simp_all
  have sl₃ : ztume := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind, rr₃, by_grind, rm₃, out₃⟩
  have P₃ : PassInv W J le Bc A₀ c c₃ K L 0 c₃ :=
    { wb := e₃.wb_right, hJ := hJs c₂ c₃ C₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
      loc := C₂.loc.sl sl₃, rK := (R₃ _ by_omega).trans C₂.rK,
      one := (R₃ _ by_omega).trans C₂.one, rw := by zuoma; rfl,
      keep := by_omega,
      arr := Or.inl ⟨(R₃ _ by_omega).trans C₂.rsrc, (R₃ _ by_omega).trans C₂.rdst⟩,
      bW := C₂.bW,
      lst := ⟨L, by
          rw [R₃ _ by_omega, C₂.rsrc, m₃]
          have := C₂.cp
          grind,
        List.Perm.refl L, by rw [pow_zero]; exact chunkSorted_one L⟩ }
  -- the passes
  obtain ⟨c₄, k₄, e₄, ⟨p₄, P₄⟩, hk₄, l, hl, hperm, hsorted⟩ :=
    passLoop_inv (P := P) hcmp hJs hB trans total P₃
  rw [Nat.sub_zero] at hk₄
  -- the output
  obtain ⟨c₅, e₅, n₅, m₅, rr₅, rm₅, out₅⟩ := copyN_char (P := P) P₄.wb 30005 30007
  have R₅ : ∀ r, r ≠ 30005 → c₅.nreg r = c₄.nreg r := fun r hr => by
    zugwr
  have o₅ : c₅.nreg 30005 = c₄.nreg 30007 := by rw [n₅, Machine.upd_same]
  have sl₅ : ztumf := ⟨fun r hb _ => by
      have := bandOf_sort hb; grind, rr₅, by_grind, rm₅, out₅⟩
  have loc₅ := P₄.loc.sl sl₅
  have al₅ : c₅.nreg ALLOC = A₀ + 2 * K := by
    rw [R₅ _ by_decide, P₄.keep ALLOC ztbt by_decide by_decide by_decide
      by_decide by_decide, R₃ _ by_decide]
    omega
  have harr := P₄.arr
  have hk0 := sortCost_ge κ K
  refine ⟨c₅, _, .seq e₁ ztbq, by_omega,
    hJs c₄ c₅ P₄.hJ sl₅.1 sl₅.2.1 sl₅.2.2.1 sl₅.2.2.2.1 sl₅.2.2.2.2, ?_, by_omega,
    by omega, l, by_grind, hperm, hsorted⟩
  refine ⟨fun r hr ha => ?_, fun r hr => ?_, loc₅.2.2.1,
    fun a _ => by rw [loc₅.2.2.2.1], loc₅.2.2.2.2, by_omega, ?_⟩
  · zucjg
    exact loc₅.1 r hr.2 hr.1 ha
  · zucjg
    exact loc₅.2.1 r hr.2
  omega

/-- **The sort as a `Meets` judgement** (bands `bSort` and the comparator's `Bc`).  The
comparator's invariant `Ctx P W c₀` may depend on the entry configuration `c₀` (for instance on the
memory below the allocator, which the sort never writes), and so may the order `le P c₀`.
Input: the items `seg c.nmem S K` (`S = rd c bSort 3`, `K = rd c bSort 4`) below the allocator.
Output (`rd c' bSort 5`): a fresh array, between the old and the new allocator, holding a sorted
permutation of the items.  Cost `sortCost κ K`. -/
theorem sort_meets {cmp : Stmt} {Bc : Finset ℕ} (hB : bSort ∉ Bc) (κ : ℕ)
    (Ctx : Polygon → ℕ → Config → Config → Prop) (le : Polygon → Config → ℕ → ℕ → Bool) :
    Meets ztwen zttpk
      (fun P W c => Ctx P W c c ∧ CmpOK P W cmp Bc ztrix (le P c) κ ∧
        JStable ztrix ztm ∧
        (∀ a b d, le P c a b → le P c b d → le P c a d) ∧ (∀ a b, le P c a b || le P c b a) ∧
        rd c bSort 3 + rd c bSort 4 ≤ c.nreg ALLOC)
      (fun P c c' => c.nreg ALLOC ≤ rd c' bSort 5 ∧ rd c' bSort 5 + rd c bSort 4 ≤ c'.nreg ALLOC ∧
        (seg c'.nmem ztrvr ztiac).Perm (seg c.nmem (rd c bSort 3) ztiac) ∧
        (seg c'.nmem ztrvr ztiac).Pairwise fun a b => le P c a b)
      (fun _ c => sortCost κ ztiac) := by
  rintro P W c hw ⟨hJ, hcmp, hJs, htr, hto, hS⟩ hroom
  simp only at hroom ⊢
  have e3 : rd c bSort 3 = c.nreg 30003 := rfl
  have e4 : rd c bSort 4 = c.nreg 30004 := rfl
  have e5 : ∀ c' : Config, rd c' bSort 5 = c'.nreg 30005 := fun _ => rfl
  set L := seg c.nmem ztvie ztvif with hL
  have hlen : L.length = c.nreg 30004 := seg_length
  obtain ⟨c', k, e, hk, hJ', hfr, h1, h2, L', h3, h4, h5⟩ := sortStmt_exec (P := P) hcmp hB htr hto
    hw hJ hJs L by_simp_all hlen.symm by_omega
    by_simp_all
  grind
end
end SortR
end Chazelle.Core
end
namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs
@[expose] public section
def ifEqN (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e ztjdg

/-- The base register of field `f`. -/
def fb (f : ℕ) : ℕ := 60100 + f

/-- `d := field f [nreg x]` (temporary `60030`). -/
def ldF (d f x : ℕ) : Stmt := block [.addN 60030 ztgip x, .loadN d 60030]

/-- `field f [nreg x] := nreg v` (temporary `60030`). -/
def stF (f x v : ℕ) : Stmt := block [.addN 60030 ztgip x, .storeN 60030 v]
section spec
variable {P : Polygon} {W : ℕ}
variable {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
/-- Spec of `ifEqN`, equal case. -/
theorem ifEqN_eq
    (h : c.nreg a = c.nreg b) (ht : ∃ c' k, Exec P W t c c' k ∧ Q c' (k + 4)) :
    ∃ c' k, Exec P W ztqrk c c' k ∧ Q c' k := by
  unfold ifEqN
  zumjj
  omega

/-- Spec of `ifEqN`, unequal case (cost at most `k + 3`). -/
theorem ifEqN_ne
    (h : c.nreg a ≠ c.nreg b) (he : ∃ c' k, Exec P W e c c' k ∧ ∀ k', k' ≤ k + 3 → Q c' k') :
    ∃ c' k, Exec P W ztqrk c c' k ∧ Q c' k := by
  unfold ifEqN
  obtain ⟨c', k, ex, q⟩ := he
  zuhtf
  · tauto
  · have hlt' : c.nreg b < c.nreg a := by_omega
    exact ⟨c', k + 1 + 2, .ifLtN_false hlt (.ifLtN_true hlt' ex), q _ by_omega⟩

/-- Spec of `ldF`. -/
theorem ldF_exec (hw : WordsBounded W c) (d f x : ℕ)
    (hb : c.nreg ztgip + c.nreg x ≤ W) :
    ∃ c' k, Exec P W ztrsz c c' k ∧ k = 2 ∧
      c' = { c with nreg := (upd (upd c.nreg 60030 (c.nreg (fb f) + c.nreg x)) d
        (c.nmem ztcut)) } := by
  unfold ldF
  zujfs
  refine spec_step (Exec.loadN hw1 _ _) fun _ => ?_
  tauto

/-- Spec of `stF`. -/
theorem stF_exec (hw : WordsBounded W c) (f x v : ℕ) (hv : v ≠ 60030)
    (hb : c.nreg ztgip + c.nreg x ≤ W) :
    ∃ c' k, Exec P W ztrxf c c' k ∧ k = 2 ∧
      c' = { c with
        nreg := upd c.nreg 60030 ztcut
        nmem := upd c.nmem ztcut ztjsn } := by
  unfold stF
  zujfs
  refine spec_step (Exec.storeN hw1 _ _) fun _ => ?_
  refine spec_nil ‹_› ztmw
  simp_all
end spec

/-! ## Registers, frames and field views -/

/-- The constant registers of the decomposition. -/
structure DRegs (A R K CB RB LB : ℕ) (c : Config) : Prop where
  zero : c.nreg 60010 = 0
  one : c.nreg 60011 = 1
  two : c.nreg 60012 = 2
  rR : c.nreg 60013 = R
  rK : c.nreg 60014 = K
  rCB : c.nreg 60015 = CB
  rRB : c.nreg 60016 = RB
  rLB : c.nreg 60017 = LB
  rA : c.nreg 60018 = A
  rR1 : c.nreg 60019 = R - 1
  base : ∀ f, f < 20 → c.nreg ztgip = A + 12 + f * R

/-- A register the loops may not write: below `60020` or from `60100` on. -/
def Prot (r : ℕ) : Prop := r < 60020 ∨ 60100 ≤ r

/-- **The frame of a loop** of the decomposition: protected registers (except `ALLOC`), real
state and output unchanged; memory unchanged outside `[lo, hi)`. -/
def DFr (lo hi : ℕ) (c c' : Config) : Prop :=
  (∀ r, Prot r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
    c'.output = c.output ∧ ∀ a, ztnqq → c'.nmem a = c.nmem a
theorem DFr.refl (lo hi : ℕ) (c : Config) : DFr lo hi c c :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
variable {lo hi : ℕ} {m : ℕ → ℕ}
theorem DFr.trans {c₁ c₂ c₃ : Config} (h₁ : DFr lo hi c₁ c₂) (h₂ : DFr lo hi c₂ c₃) :
    DFr lo hi c₁ c₃ :=
  ⟨fun r h h' => (h₂.1 r h h').trans (h₁.1 r h h'), h₂.2.1.trans h₁.2.1,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    fun a ha => (h₂.2.2.2.2 a ha).trans (h₁.2.2.2.2 a ha)⟩
theorem DRegs.of_regs {A R K CB RB LB : ℕ} {c c' : Config} (h : DRegs A R K CB RB LB c)
    (k : ∀ r, Prot r → r ≠ ALLOC → c'.nreg r = c.nreg r) : DRegs A R K CB RB LB c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun f hf' => ?_⟩
  · zumye; exact h.zero
  · zumye; exact h.one
  · zumye; exact h.two
  · zumye; exact h.rR
  · zumye; exact h.rK
  · zumye; exact h.rCB
  · zumye; exact h.rRB
  · zumye; exact h.rLB
  · zumye; exact h.rA
  · zumye; exact h.rR1
  · rw [k _ (by unfold Prot fb; omega) (by unfold fb ALLOC; omega)]; exact h.base f hf'
theorem DRegs.frame {A R K CB RB LB lo hi : ℕ} {c c' : Config} (h : DRegs A R K CB RB LB c)
    (hf : DFr lo hi c c') : DRegs A R K CB RB LB c' := h.of_regs hf.1

/-- An explicit update of scratch registers (`60020 ≤ r < 60100`) is within the frame. -/
theorem DFr.nreg {c : Config} (f : ℕ → ℕ) (hf : ∀ r, Prot r → r ≠ ALLOC → f r = c.nreg r) :
    DFr lo hi c { c with nreg := f } :=
  ⟨hf, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- **The field view**: entry `i` of field `f`. -/
def fv (m : ℕ → ℕ) (A R f i : ℕ) : ℕ := m ztfmz
theorem addr_inj {A R f g i j : ℕ} (hi : i < R) (hj : j < R)
    (h : A + 12 + f * R + i = A + 12 + g * R + j) : f = g ∧ i = j := by
  rcases lt_trichotomy f g with hfg | rfl | hfg
  · have : ztbax * R ≤ g * R := Nat.mul_le_mul_right _ hfg
    grind
  · omega
  · have : ztbs * R ≤ f * R := Nat.mul_le_mul_right _ hfg
    grind

/-- A store into field `f` at `i` changes exactly that entry of the view. -/
theorem fv_store {A R f i v g j : ℕ} (hi : i < R) (hj : j < R) :
    fv (upd m ztfmz v) A R g j = if g = f ∧ j = i then v else fv m A R g j := by
  zumsr
  by_cases e : g = f ∧ j = i
  · simp_all
  · rw [ite_eq_right e, Machine.upd_other]
    zuq
    exact e (addr_inj hj hi h)

/-- A store into the field block leaves the memory outside it unchanged. -/
theorem fv_store_out {A R f i v a : ℕ} (hf : f < 19) (hi : i < R)
    (ha : a < A + 12 ∨ A + 12 + 19 * R ≤ a) : upd m ztfmz v a = m a := by
  zumlr
  zuq
  zufzt
  · omega
  · have : ztbax * R ≤ 19 * R := Nat.mul_le_mul_right _ by_omega
    grind
def setupS : Stmt := block [
  .constN 60010 0, .constN 60011 1, .constN 60012 2,
  .loadN 60014 60001,
  .addN 60030 60001 60012, .loadN 60013 60030,
  .addN 60030 60030 60011, .loadN 60015 60030,
  .addN 60030 60030 60012, .loadN 60016 60030,
  .addN 60030 60030 60012, .loadN 60017 60030,
  .copyN 60018 9999,
  .subN 60019 60013 60011,
  .constN 60031 12, .addN 60100 60018 60031,
  .addN 60101 60100 60013, .addN 60102 60101 60013, .addN 60103 60102 60013,
  .addN 60104 60103 60013, .addN 60105 60104 60013, .addN 60106 60105 60013,
  .addN 60107 60106 60013, .addN 60108 60107 60013, .addN 60109 60108 60013,
  .addN 60110 60109 60013, .addN 60111 60110 60013, .addN 60112 60111 60013,
  .addN 60113 60112 60013, .addN 60114 60113 60013, .addN 60115 60114 60013,
  .addN 60116 60115 60013, .addN 60117 60116 60013, .addN 60118 60117 60013,
  .addN 60119 60118 60013,
  .addN 60086 60119 60014, .addN 60086 60086 60014, .addN 60086 60086 60014]

/-- Raise the allocator to `DB + 3 K` (target in `60086`), one word per iteration. -/
def allocS : Stmt := .whileLtN 9999 60086 (.instr ztrht)

/-! ## Initialisation -/

/-- Clear entry `i` of the fields read before they are written: `vis`, `rem`, `pend` (`0`) and
`size` (`1`). -/
def initBody : Stmt := block [
  .addN 60030 60102 60020, .storeN 60030 60010, .addN 60030 60107 60020, .storeN 60030 60011,
  .addN 60030 60111 60020, .storeN 60030 60010, .addN 60030 60112 60020, .storeN 60030 60010,
  .addN 60020 60020 60011]

/-- The root: first in the queue (`ord`), visited (`vis`), active (`act`), with the root slot
(`side = 2`). -/
def rootInit : Stmt := block [
  .addN 60030 60101 60010, .storeN 60030 60010,
  .addN 60030 60102 60010, .storeN 60030 60011, .addN 60030 60113 60010, .storeN 60030 60011,
  .addN 60030 60115 60010, .storeN 60030 60012]

/-- **Initialisation.** -/
def initS : Stmt :=
  .seq ztcyp (.seq ztrif rootInit)

/-! ## The search -/

/-- Read chord `i = list[t]` of the current region and its endpoints `u`, `d`. -/
def bfsRead : Stmt := block [
  .addN 60030 60028 60021, .addN 60030 60017 60030, .loadN 60032 60030,
  .addN 60033 60032 60032, .addN 60033 60033 60033, .addN 60033 60033 60032,
  .addN 60033 60015 60033, .addN 60033 60033 60012, .addN 60033 60033 60011, .loadN 60034 60033,
  .addN 60033 60033 60011, .loadN 60035 60033]

/-- Discover `s` (in `60036`) through chord `i` (`60032`) from `r` (`60029`). -/
def bfsNew : Stmt := block [
  .addN 60030 60102 60036, .storeN 60030 60011,
  .addN 60030 60101 60026, .storeN 60030 60036,
  .addN 60030 60103 60036, .storeN 60030 60029,
  .addN 60030 60104 60036, .storeN 60030 60032,
  .addN 60030 60105 60036, .storeN 60030 60037,
  .addN 60030 60106 60032, .storeN 60030 60036,
  .addN 60026 60026 60011]

/-- The scan of one chord of the current region. -/
def bfsInner : Stmt :=
  .seq bfsRead (.seq (ifEqN 60034 60029 ztksl
      ztksk)
    (.seq (ldF 60038 2 60036) (.seq (ifEqN 60038 60011 .skip bfsNew)
      (.instr (.addN 60021 60021 60011)))))

/-- Dequeue a region and locate its exit-chord list. -/
def bfsDeq : Stmt := block [
  .addN 60030 60101 60025, .loadN 60029 60030,
  .addN 60025 60025 60011,
  .addN 60033 60029 60029, .addN 60033 60033 60033, .addN 60033 60033 60029,
  .addN 60033 60016 60033, .addN 60033 60033 60012, .loadN 60027 60033,
  .addN 60033 60033 60011, .loadN 60028 60033,
  .constN 60021 0]

/-- One step of the search. -/
def bfsOuter : Stmt := .seq bfsDeq ztrig

/-- **The search.** -/
def bfsS : Stmt := .seq (block [.constN 60025 0, .constN 60026 1]) (.whileLtN 60025 60026 bfsOuter)

/-! ## Pass 1: sizes -/

/-- Add the size of `r` (in `60040`) into its parent's. -/
def p1Add : Stmt := block [
  .addN 60030 60103 60040, .loadN 60043 60030,
  .addN 60030 60107 60040, .loadN 60044 60030,
  .addN 60031 60107 60043, .loadN 60045 60031,
  .addN 60045 60045 60044, .storeN 60031 60045]

/-- One step of the size pass. -/
def p1Body : Stmt :=
  .seq (block [.subN 60039 60019 60020, .addN 60030 60101 60039, .loadN 60040 60030])
    (.seq (.ifLtN 60010 60040
        ztejw
        .skip)
      ztckl)

/-- **The size pass.** -/
def p1S : Stmt := .seq ztcyp (.whileLtN 60020 60013 p1Body)

/-! ## Pass 2: tops and cut candidates -/

/-- `r` (in `60040`) is a top. -/
def topBr : Stmt := block [
  .addN 60030 60108 60040, .storeN 60030 60040,
  .addN 60030 60109 60040, .storeN 60030 60040,
  .addN 60030 60110 60040, .storeN 60030 60010]

/-- `r` (in `60040`) is no top: its top is its parent's; update the best candidate. -/
def ntBr : Stmt :=
  .seq (block [
      .addN 60030 60103 60040, .loadN 60043 60030,
      .addN 60030 60108 60043, .loadN 60046 60030,
      .addN 60030 60108 60040, .storeN 60030 60046,
      .addN 60030 60107 60040, .loadN 60044 60030,
      .addN 60030 60107 60046, .loadN 60047 60030,
      .subN 60048 60047 60044])
    (.seq (.ifLtN 60044 60048 (.instr (.copyN 60049 60044)) ztovt)
      (.seq (ldF 60050 10 60046)
        (.ifLtN 60050 60049
          (block [.addN 60030 60110 60046, .storeN 60030 60049,
            .addN 60030 60109 60046, .storeN 60030 60040]) .skip)))

/-- One step of the top pass. -/
def p2Body : Stmt :=
  .seq (block [.addN 60030 60101 60020, .loadN 60040 60030])
    (.seq (.ifLtN 60010 60040
        ztejx
        topBr)
      ztckl)

/-- **The top pass.** -/
def p2S : Stmt := .seq ztcyp (.whileLtN 60020 60013 p2Body)

/-! ## The chord pass -/

/-- `d := code (nreg x)`: `2 x + 1` if `best x = x`, else `2 pch (best x)`. -/
def codeS (d x : ℕ) : Stmt :=
  .seq (ldF 60051 9 x)
    (ifEqN 60051 x (block [.addN d x x, .addN d d 60011])
      (.seq (ldF 60052 4 60051) (.instr (.addN d 60052 60052))))

/-- Fill the two slots of the chord `e` (in `60020`) cut in the previous round. -/
def fillS : Stmt :=
  .seq ztrsy (.seq (ldF 60054 3 60053) (.seq (ldF 60055 8 60054)
    (.seq (ldF 60056 5 60053)
      (.seq (ifEqN 60056 60011 ztksm
          ztksn)
        (.seq (codeS 60059 60057) (.seq (codeS 60060 60058)
          (.seq (stF 17 60020 60059) (.seq (stF 18 60020 60060) (stF 12 60020 60010)))))))))

/-- Cut chord `e` (in `60020`) in the component of `t` (in `60055`). -/
def doS : Stmt :=
  .seq (stF 11 60020 60011) (.seq (stF 12 60020 60011) (.seq (ldF 60061 15 60055)
    (.seq (ifEqN 60061 60012 ztnav
        ztgql)
      (stF 16 60020 60062))))

/-- Is chord `e` (in `60020`) chosen? -/
def chkS : Stmt :=
  .seq ztrsy (.seq (ldF 60055 8 60053) (.seq (ldF 60064 13 60055)
    (ifEqN 60064 60011 (.seq (ldF 60065 9 60055) (ifEqN 60065 60053 doS .skip)) .skip)))

/-- One step of the chord pass. -/
def cpBody : Stmt :=
  .seq (ldF 60066 12 60020)
    (.seq (ifEqN 60066 60011 fillS zthqg)
      ztckl)

/-- **The chord pass.** -/
def cpS : Stmt := .seq ztcyp (.whileLtN 60020 60014 cpBody)

/-! ## The root step -/

/-- **The root step**: in the first round, the root code is the code of the root component. -/
def rootS : Stmt :=
  .seq (ldF 60068 13 60010)
    (ifEqN 60068 60011 (.seq (ldF 60069 15 60010)
        (ifEqN 60069 60012 (.seq (codeS 60070 60010) (.instr (.copyN 60024 60070))) .skip)) .skip)

/-! ## The region pass -/

/-- A singleton component finishes: its leaf gets its parent. -/
def singS : Stmt :=
  .seq (stF 13 60020 60010) (.seq (ldF 60071 15 60020)
    (.seq (ifEqN 60071 60012 ztiqr
        ztgqm)
      (.seq (stF 0 60020 60072) (.instr (.addN 60023 60023 60011)))))

/-- A cut component records its new pending slot (best candidate in `60075`). -/
def cutS : Stmt :=
  .seq (ldF 60074 4 60075) (.seq (stF 14 60020 60074) (.seq (ldF 60076 5 60075)
    (ifEqN 60076 60011 ztrxe ztrxd)))

/-- Region `r` (in `60020`) is a top. -/
def topR : Stmt :=
  .seq (ldF 60077 13 60020)
    (ifEqN 60077 60011 (.seq (ldF 60075 9 60020) (ifEqN 60075 60020 singS cutS)) .skip)

/-- Region `r` (in `60020`) is no top: it becomes one if its parent chord was just cut. -/
def ntR : Stmt :=
  .seq (ldF 60078 4 60020) (.seq (ldF 60079 12 60078)
    (ifEqN 60079 60011 (.seq (stF 13 60020 60011) (.seq (stF 14 60020 60078)
        (.seq (ldF 60080 5 60020) (ifEqN 60080 60011 ztrxd ztrxe))))
      .skip))

/-- One step of the region pass. -/
def rpBody : Stmt :=
  .seq (stF 7 60020 60011) (.seq (ldF 60081 8 60020)
    (.seq ztqrj ztckl))

/-- **The region pass.** -/
def rpS : Stmt := .seq ztcyp (.whileLtN 60020 60013 rpBody)

/-! ## The rounds -/

/-- **One round.** -/
def roundBody : Stmt :=
  .seq p1S (.seq p2S (.seq cpS (.seq rootS (.seq rpS (.instr (.addN 60022 60022 60011))))))

/-- **The rounds**, while fewer than `R` leaves are finished. -/
def roundsS : Stmt :=
  .seq zthsm (.whileLtN 60023 60013 roundBody)

/-! ## The node table and the header -/

/-- Copy node `k` (in `60020`) to `DB + 3 k`. -/
def fcBody : Stmt :=
  .seq (block [.addN 60082 60020 60020, .addN 60082 60082 60020, .addN 60082 60119 60082])
    (.seq (ldF 60083 16 60020) (.seq ztigp
      (.seq ztnaw (.seq (ldF 60083 17 60020)
        (.seq ztigp (.seq ztnaw
          (.seq (ldF 60083 18 60020) (.seq ztigp
            ztckl))))))))

/-- **The node table.** -/
def fcS : Stmt := .seq ztcyp (.whileLtN 60020 60014 fcBody)

/-- **The header** of the new normal form at `A`, and the output handle. -/
def hdrS : Stmt := block [
  .copyN 60030 60018, .storeN 60030 60014,
  .addN 60031 60001 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60030 60030 60011, .storeN 60030 60013,
  .addN 60031 60031 60012, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60031 60031 60011, .loadN 60085 60031, .addN 60030 60030 60011, .storeN 60030 60085,
  .addN 60030 60030 60011, .storeN 60030 60119,
  .addN 60030 60030 60011, .storeN 60030 60024,
  .addN 60030 60030 60011, .storeN 60030 60100,
  .addN 60030 60030 60011, .storeN 60030 60014,
  .copyN 60003 60018]

/-- **The decomposition program.** -/
def decompStmt : Stmt :=
  .seq setupS (.seq allocS (.seq initS (.seq bfsS (.seq roundsS (.seq fcS hdrS)))))
