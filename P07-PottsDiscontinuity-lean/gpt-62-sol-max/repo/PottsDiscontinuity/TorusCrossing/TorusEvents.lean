module

public import PottsDiscontinuity.TorusCrossing.Fiber
public import PottsDiscontinuity.TorusCrossing.Ivt
public import PottsDiscontinuity.TorusCrossing.TorusDict
public import PottsDiscontinuity.TorusRC.CrossingContracts

/-!
# Torus crossing events seen from a board

Conversion of cell-level open paths of a board (for the primal configuration, and for the
complementary translated configuration) into walks of the lifted strip graph of the torus.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength
open scoped Classical

variable {N M : ℕ}

section

variable (hNp : 0 < N) (hMp : 0 < M) (n : ℕ)

/-- Vertical lifted crossing of the rows `[b, b + n]` inside the columns `[a, a + 3n]`. -/
def vCross (a b : ℤ) (A : RCConfig N M) : Prop :=
  ∃ u v : RotatedVertex, u.val.2 = b ∧ v.val.2 = b + n ∧
    ∃ w : (liftedStripGraph hNp hMp A a (a + 3 * (n : ℤ))).Walk u v,
      ∀ z ∈ w.support, b ≤ z.val.2 ∧ z.val.2 ≤ b + n

theorem vCross_zero_iff (A : RCConfig N M) :
    vCross hNp hMp n 0 0 A ↔ torusRCVerticalRectangleCrossing hNp hMp n A := by
  have h3 : (0 : ℤ) + 3 * (n : ℤ) = 3 * (n : ℤ) := zero_add _
  unfold vCross torusRCVerticalRectangleCrossing
  rw [h3]
  simp only [zero_add]

end

/-- Trim a board path to the prescribed rows, then lift its successive edges to the
strip. The same conversion works for the primal cells and the shifted dual cells. -/
theorem stepRel_to_vCross (hNp : 0 < N) (hMp : 0 < M) (n : ℕ) (hn : 0 < n)
    (a ρ : ℤ) (A : RCConfig N M) {P : Cell → Prop} (f : ∀ c, P c → RotatedVertex)
    (hrow : ∀ c hc, (f c hc).1.2 = c.2) (ends : Cell → Cell × Cell) {S : Finset Cell}
    (hP : ∀ m ∈ S, P (ends m).1 ∧ P (ends m).2)
    (hstep : ∀ m ∈ S, (ends m).1.2 = (ends m).2.2 + 1)
    (hadj : ∀ m (hm : m ∈ S),
      (liftedStripGraph hNp hMp A a (a + 3 * (n : ℤ))).Adj
        (f _ (hP m hm).1) (f _ (hP m hm).2))
    {u v : Cell} (hpath : Relation.ReflTransGen (StepRel ends S) u v)
    (hu : u.2 ≤ ρ) (hv : ρ + n ≤ v.2) : vCross hNp hMp n a ρ A := by
  let G := liftedStripGraph hNp hMp A a (a + 3 * (n : ℤ))
  have hstep' (p q : Cell) (h : StepRel ends S p q) : q.2 ≤ p.2 + 1 ∧ p.2 ≤ q.2 + 1 := by
    obtain ⟨m, hm, he | he⟩ := h <;> have hh := hstep m hm <;> rw [he] at hh <;>
      dsimp only at hh <;> omega
  have hedge {p q : Cell} (h : StepRel ends S p q) : ∃ hp : P p, ∃ hq : P q,
      G.Adj (f p hp) (f q hq) := by
    obtain ⟨m, hm, he | he⟩ := h
    · have h₁ : (ends m).1 = p := congrArg Prod.fst he
      have h₂ : (ends m).2 = q := congrArg Prod.snd he
      subst p q
      exact ⟨(hP m hm).1, (hP m hm).2, hadj m hm⟩
    · have h₁ : (ends m).2 = p := congrArg Prod.snd he
      have h₂ : (ends m).1 = q := congrArg Prod.fst he
      subst p q
      exact ⟨(hP m hm).2, (hP m hm).1, (hadj m hm).symm⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := ivt_path _ (fun c : Cell => c.2) hstep' ρ n hpath hu hv
  have hxP : P x := by
    rcases hxy.cases_head with e | ⟨z, hz, _⟩
    · subst y; omega
    · obtain ⟨h, _, _⟩ := hedge hz.1
      exact h
  obtain ⟨hyP, w, hw⟩ : ∃ hyP : P y, ∃ w : G.Walk (f x hxP) (f y hyP),
      ∀ r ∈ w.support, ρ ≤ r.1.2 ∧ r.1.2 ≤ ρ + n := by
    clear hy
    induction hxy with
    | refl => exact ⟨hxP, .nil, by simp [hrow, hx]⟩
    | @tail p q _ hpq ih =>
      obtain ⟨hp, w, hw⟩ := ih
      obtain ⟨_, hq, h⟩ := hedge hpq.1
      refine ⟨hq, w.concat h, ?_⟩
      simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
      rintro r (hr | rfl)
      · exact hw r hr
      · rw [hrow]
        exact ⟨hpq.2.2.2.1, hpq.2.2.2.2⟩
  exact ⟨f x hxP, f y hyP, (hrow _ _).trans hx, (hrow _ _).trans hy, w, hw⟩

theorem adj_oriented (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) (a b : ℤ)
    (hcol : a ≤ Q.x0 ∧ Q.x0 + Q.w ≤ b) {m : Cell} (hm : m ∈ boardOf Q hNp hMp A) :
    (liftedStripGraph hNp hMp A a b).Adj (toRV (primalEnds m).1 (primalEnds_fst_primal m))
      (toRV (primalEnds m).2 (primalEnds_snd_primal m)) := by
  obtain ⟨hmin, hmA⟩ := Finset.mem_filter.1 hm
  have hd := Q.pData.mem m hmin
  have h1 := Rect.mem_cells.1 (Rect.mem_pcells.1 hd.1).1
  have h2 := Rect.mem_cells.1 (Rect.mem_pcells.1 hd.2).1
  refine ⟨rotAdj_primalEnds m, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [liftedEdgeIndex_primalEnds] using hmA
  · change a ≤ (primalEnds m).1.1; omega
  · change (primalEnds m).1.1 ≤ b; omega
  · change a ≤ (primalEnds m).2.1; omega
  · change (primalEnds m).2.1 ≤ b; omega

/-- A crossing of the board between the two exploration zones gives a lifted vertical crossing of
rows `[ρ, ρ + n]` in the columns `[a, a + 3n]` containing the board. -/
theorem cross_to_vCross (hNp : 0 < N) (hMp : 0 < M) (Q : Rect) (A : RCConfig N M) {bB bT : ℕ}
    (n : ℕ) (hn : 0 < n) (a ρ : ℤ) (hcol : a ≤ Q.x0 ∧ Q.x0 + Q.w ≤ a + 3 * (n : ℤ))
    (hρ1 : Q.y0 + bB - 1 ≤ ρ) (hρ2 : ρ + n ≤ Q.y0 + Q.h - bT + 1)
    (hc : Q.crossEv bB bT (boardOf Q hNp hMp A)) : vCross hNp hMp n a ρ A := by
  obtain ⟨u, v, hu, hv, hpath⟩ := hc
  refine stepRel_to_vCross hNp hMp n hn a ρ A toRV (fun _ _ => rfl) primalEnds
    (fun m _ => ⟨primalEnds_fst_primal m, primalEnds_snd_primal m⟩)
    (fun m _ => by rw [Rect.primalEnds_fst_row, Rect.primalEnds_snd_row]; omega)
    (fun _ hm => adj_oriented hNp hMp Q A _ _ hcol hm) hpath (by omega) (by omega)

end PottsDiscontinuity.TorusCrossing
