module

public import Chazelle.Core.DownPhaseDrvXBkt

/-!
# Down phase, extraction (D6): buckets and arc tests by comparisons

For `N = buildNF I Q L E` in the setting `XHyp`:

* `arc_facts`: the arc records of `N` have proper end positions at vertex heights on walk edges
  `< n`, strictly increasing start keys, each ending where the next starts, and no arc start inside
  an arc;
* `OnArcP`, `onArc_iff`: the test `OnArcKey` by the comparisons `PosEq`, `PosLt`;
* `bkt_spec`: the bucket `keyBkt` of a position on arc `j` by the formula `bktF` on comparisons;
* `hlt_iff`: heights of the vertices of `Q` compare like the `(y, x)`-lexicographic order of the
  input `P`.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sidePt)
open BuildNF (codeLe wposOf buildNF gapStarts)
open DrvR (keyBkt OnArcKey ivB)

/-- **The arc test by comparisons.** -/
def OnArcP (Q : Polygon) (li : Bool) (N : NF) (j : ℕ) (x : WPos) : Prop :=
  PosEq x (N.arc j).s ∨ PosEq x (N.arc j).e ∨
    ((PosLt Q li (N.arc j).s (N.arc j).e → PosLt Q li (N.arc j).s x ∧ PosLt Q li x (N.arc j).e) ∧
      (¬ PosLt Q li (N.arc j).s (N.arc j).e → PosLt Q li (N.arc j).s x ∨ PosLt Q li x (N.arc j).e))

/-- A position fit for comparisons: proper, at a vertex height, on a walk edge `< n`. -/
def GoodPos (Q : Polygon) (x : WPos) : Prop :=
  ProperPos (interiorModel Q) Q Q.n x ∧ 1 ≤ x.hgt ∧ x.edge < Q.n

theorem bktF_congr {A j : ℕ} {a a' b b' c c' : Prop} [Decidable a] [Decidable a']
    [Decidable b] [Decidable b'] [Decidable c] [Decidable c'] (ha : a ↔ a') (hb : b ↔ b')
    (hc : c ↔ c') : bktF A j a b c = bktF A j a' b' c' := by
  unfold bktF
  by_cases h1 : a
  · rw [ite_eq_left h1, ite_eq_left (ha.1 h1)]
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (ha.2 h))]
    by_cases h2 : b
    · rw [ite_eq_left h2, ite_eq_left (hb.1 h2)]
    · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (hb.2 h))]
      by_cases h3 : c
      · rw [ite_eq_left h3, ite_eq_left (hc.1 h3)]
      · rw [ite_eq_right h3, ite_eq_right (fun h => h3 (hc.2 h))]

instance (x y : WPos) : Decidable (PosEq x y) := by unfold PosEq; infer_instance

section

variable {Q : Polygon} {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q)
  (hdh : DistinctHeights Q) (hn : 2 ≤ Q.n)
include hli hdh hn

/-- **The arc test by comparisons.** -/
theorem onArc_iff {N : NF} {j : ℕ} {x : WPos} (hx : GoodPos Q x) (hs : GoodPos Q (N.arc j).s)
    (he : GoodPos Q (N.arc j).e) : OnArcKey Q N j x ↔ OnArcP Q li N j x := by
  unfold OnArcKey OnArcP
  rw [key_eq_iff hli hdh hn hx.1 hs.1 hx.2.1 hs.2.1 hx.2.2 hs.2.2,
    key_eq_iff hli hdh hn hx.1 he.1 hx.2.1 he.2.1 hx.2.2 he.2.2]
  apply or_congr_right; apply or_congr_right
  have h1 := key_lt_iff hli hdh hn hs.1 he.1 hs.2.1 he.2.1 hs.2.2
  have h2 := key_lt_iff hli hdh hn hs.1 hx.1 hs.2.1 hx.2.1 hs.2.2
  have h3 := key_lt_iff hli hdh hn hx.1 he.1 hx.2.1 he.2.1 hx.2.2
  unfold sideInArc
  by_cases hse : PosLt Q li (N.arc j).s (N.arc j).e
  · rw [ite_eq_left (h1.2 hse), h2, h3]
    exact ⟨fun h => ⟨fun _ => h, fun h' => absurd hse h'⟩, fun h => h.1 hse⟩
  · rw [ite_eq_right (fun h => hse (h1.1 h)), h2, h3]
    exact ⟨fun h => ⟨fun h' => absurd h' hse, fun _ => h⟩, fun h => h.2 hse⟩

open Classical in
/-- **The bucket by comparisons.** -/
theorem bkt_spec {N : NF} {A : ℕ} (hA : N.arcs.length = A)
    (hinc : ∀ j j', j < j' → j' < A →
      (interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q (N.arc j').s)
    (hnext : ∀ j, j < A →
      (interiorModel Q).key Q (N.arc j).e = (interiorModel Q).key Q (N.arc ((j + 1) % A)).s)
    (hfree : ∀ j j', j < A → j' < A → ¬ sideInArc ((interiorModel Q).key Q (N.arc j).s)
      ((interiorModel Q).key Q (N.arc j).e) ((interiorModel Q).key Q (N.arc j').s))
    {x : WPos} {j : ℕ} (hj : j < A) (hx : GoodPos Q x) (hs : GoodPos Q (N.arc j).s)
    (he : GoodPos Q (N.arc j).e) (hon : OnArcP Q li N j x) :
    keyBkt Q N x = bktF A j (PosEq x (N.arc j).s) (PosEq x (N.arc j).e)
      (PosLt Q li (N.arc j).s x) := by
  classical
  rw [keyBkt_eq hA hinc hnext hfree hj ((onArc_iff hli hdh hn hx hs he).2 hon)]
  exact bktF_congr (key_eq_iff hli hdh hn hx.1 hs.1 hx.2.1 hs.2.1 hx.2.2 hs.2.2)
    (key_eq_iff hli hdh hn hx.1 he.1 hx.2.1 he.2.1 hx.2.2 he.2.2)
    (key_lt_iff hli hdh hn hs.1 hx.1 hs.2.1 hx.2.1 hs.2.2)

end

/-! ## The arcs of the interior normal form -/

section

variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF}

namespace XHyp

variable (X : XHyp P li L E reg r C NR)
include X

theorem hE : E.length = 2 * L.length := by rw [X.hperm.length_eq, List.length_range]

/-- **The arcs of the interior normal form.** -/
theorem arc_facts :
    (∀ j, j < (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length →
      GoodPos (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j).s ∧
      GoodPos (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j).e) ∧
    (∀ j j', j < j' → j' < (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length →
      (interiorModel (Qof P)).key (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j).s <
        (interiorModel (Qof P)).key (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j').s) ∧
    (∀ j, j < (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length →
      (interiorModel (Qof P)).key (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j).e =
        (interiorModel (Qof P)).key (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc
          ((j + 1) % (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length)).s) ∧
    (∀ j j', j < (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length →
      j' < (buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length →
      ¬ sideInArc
        ((interiorModel (Qof P)).key (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j).s)
        ((interiorModel (Qof P)).key (Qof P) ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j).e)
        ((interiorModel (Qof P)).key (Qof P)
          ((buildNF (interiorModel (Qof P)) (Qof P) L E).arc j').s)) := by
  set N := buildNF (interiorModel (Qof P)) (Qof P) L E with hNdef
  have hN := X.hN
  have hK := X.hK
  have hE := X.hE
  have hArcs := X.hregs.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hprop⟩ := hN
  have hWn : (interiorModel (Qof P)).W.n = (Qof P).n := DownMath.walk_n _
  -- every arc is an arc of its region
  have harc : ∀ j, j < N.arcs.length → (interiorModel (Qof P)).IsArc
      (N.F (interiorModel (Qof P)) (Qof P)) (reg (N.arc j).reg)
      ((interiorModel (Qof P)).key (Qof P) (N.arc j).s)
      ((interiorModel (Qof P)).key (Qof P) (N.arc j).e) := fun j hj => (hArcs.1 j hj).2
  -- the ends of the arcs are chord positions
  have hhgt : ∀ j, j < N.arcs.length → 1 ≤ (N.arc j).s.hgt ∧ 1 ≤ (N.arc j).e.hgt := by
    intro j hj
    obtain ⟨⟨i, -, hi⟩, ⟨i', -, hi'⟩⟩ := DownMath.arc_pos X.hQ X.hL X.hperm X.hsort hK hj
    constructor
    · rcases hi with h | h <;> rw [h] <;> exact Nat.succ_pos _
    · rcases hi' with h | h <;> rw [h] <;> exact Nat.succ_pos _
  have hedge : ∀ x : WPos, ProperPos (interiorModel (Qof P)) (Qof P) (Qof P).n x →
      (interiorModel (Qof P)).key (Qof P) x < (Qof P).n → x.edge < (Qof P).n := by
    intro x hx hk
    have : (x.edge : ℝ) < (Qof P).n := by
      have := hx.1; unfold Model.key at hk; linarith
    exact_mod_cast this
  refine ⟨fun j hj => ?_, fun j j' hjj hj' => key_s_strict hK X.hsort hE hjj hj',
    fun j hj => key_e_next hK X.hsort hE hj, fun j j' hj hj' hin => ?_⟩
  · obtain ⟨hs, he⟩ := hprop j hj
    obtain ⟨-, has, -, hbe, -⟩ := harc j hj
    rw [hWn] at has hbe
    exact ⟨⟨hs, (hhgt j hj).1, hedge _ hs has⟩, ⟨he, (hhgt j hj).2, hedge _ he hbe⟩⟩
  · have hcut := (WalkAx.arc_cuts X.hne (harc j' hj')).1
    exact (harc j hj).2.2.2.2.2.1 _ hin hcut

end XHyp

end

/-! ## Heights by the lexicographic order of the input -/

/-- **Heights of the geometry polygon** compare like the `(y, x)` order of the input. -/
theorem hlt_iff {P : Polygon} (hG : GoodEnv P) {u v : ℕ} (hu : u < (Qof P).n) (hv : v < (Qof P).n) :
    ((Qof P).vtx u).2 < ((Qof P).vtx v).2 ↔ Mountain.ylexLT (P.vtx u) (P.vtx v) := by
  have hgood := goodShear_epsOf hG.2
  have hn : (Qof P).n = P.n := shear_n _ P
  rw [hgood.2.2.1 u v (by rw [← hn]; exact hu) (by rw [← hn]; exact hv)]
  show _ ↔ ((Qof P).vtx u).2 < ((Qof P).vtx v).2 ∨
    (((Qof P).vtx u).2 = ((Qof P).vtx v).2 ∧ ((Qof P).vtx u).1 < ((Qof P).vtx v).1)
  constructor
  · exact Or.inl
  · rintro (h | ⟨h, h'⟩)
    · exact h
    · by_cases huv : u = v
      · subst huv; exact absurd h' (lt_irrefl _)
      · exact absurd h (hgood.2.1 u v hu hv huv)

end

end DrvX

end Chazelle.Core
