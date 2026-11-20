module

public import PottsDiscontinuity.TorusCrossing.ExploreLocal

/-!
# Two explorations in the two ends of a board

A board `Q` contains a bottom sub-board `B` (height `bB`) and a top sub-board `T` (height `bT`),
with at least one row of gap.  From the bottom of `B` and from the top of `T` we explore the
dual cluster of the port row; the explored regions are vertex-disjoint.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

inductive Side where
  | lower | upper

namespace Rect

/-- The sub-board at the chosen end, together with its outer and inner port rows. -/
def endBoard (Q : Rect) (s : Side) (b : ℕ) : Rect :=
  ⟨Q.x0, (match s with | .lower => Q.y0 | .upper => Q.y0 + Q.h - b), Q.w, b⟩

def outerRow (Q : Rect) : Side → ℤ
  | .lower => Q.y0
  | .upper => Q.y0 + Q.h

def innerRow (Q : Rect) (s : Side) (b : ℕ) : ℤ :=
  match s with
  | .lower => Q.y0 + b
  | .upper => Q.y0 + Q.h - b

private theorem port_rows (Q : Rect) (s : Side) (b : ℕ) :
    let R := Q.endBoard s b
    let p := Q.outerRow s
    let t := Q.innerRow s b
    (p = R.y0 ∧ t = R.y0 + R.h) ∨ (p = R.y0 + R.h ∧ t = R.y0) := by
  cases s <;> simp [endBoard, outerRow, innerRow]

variable (Q : Rect)

noncomputable def explored (s : Side) (b : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.endBoard s b).expRm (Q.outerRow s) (Q.innerRow s b) A

noncomputable def barrier (s : Side) (b : ℕ) (A : Finset Cell) : Finset Cell :=
  (Q.endBoard s b).expBd (Q.outerRow s) (Q.innerRow s b) A

def hasBarrier (s : Side) (b : ℕ) (A : Finset Cell) : Prop :=
  ∀ t ∈ (Q.endBoard s b).faceRow (Q.innerRow s b), t ∉ (Q.endBoard s b).expD (Q.outerRow s) A

noncomputable def exAll (bB bT : ℕ) (A : Finset Cell) : Finset Cell :=
  Q.explored .lower bB A ∪ Q.explored .upper bT A

def barAll (bB bT : ℕ) (A : Finset Cell) : Prop :=
  Q.hasBarrier .lower bB A ∧ Q.hasBarrier .upper bT A

structure Geo (Q : Rect) (bB bT : ℕ) : Prop where
  hw : 0 < Q.w
  hbB : 0 < bB
  hbT : 0 < bT
  hgap : bB + bT < Q.h

variable {Q} {bB bT : ℕ}

theorem endBoard_inner_subset (s : Side) {b : ℕ} (h : b ≤ Q.h) : (Q.endBoard s b).inner ⊆ Q.inner := by
  intro m hm
  cases s <;> simp only [Rect.mem_inner, endBoard] at hm ⊢ <;> omega

private theorem explored_subset (s : Side) (b : ℕ) (A : Finset Cell) :
    Q.explored s b A ⊆ (Q.endBoard s b).inner := fun _ h => (mem_expRm_iff.1 h).1

theorem exAll_subset_inner (A : Finset Cell) (hg : Q.Geo bB bT) : Q.exAll bB bT A ⊆ Q.inner := by
  have h := hg.hgap
  exact Finset.union_subset
    ((explored_subset .lower bB A).trans (endBoard_inner_subset .lower (by omega)))
    ((explored_subset .upper bT A).trans (endBoard_inner_subset .upper (by omega)))

/-- Agreement on the two explored regions determines them and their crossing status. -/
theorem exAll_congr {A A' : Finset Cell} (h : A' ∩ Q.exAll bB bT A = A ∩ Q.exAll bB bT A) :
    Q.exAll bB bT A' = Q.exAll bB bT A ∧ (Q.barAll bB bT A' ↔ Q.barAll bB bT A) := by
  have key (s : Side) (b : ℕ) (hs : Q.explored s b A ⊆ Q.exAll bB bT A) :
      Q.explored s b A' = Q.explored s b A ∧ (Q.hasBarrier s b A' ↔ Q.hasBarrier s b A) := by
    have hr := congrArg (· ∩ Q.explored s b A) h
    rw [Finset.inter_assoc, Finset.inter_assoc, Finset.inter_eq_right.mpr hs] at hr
    have hd := expD_stop (Q.outerRow s) (Q.innerRow s b) hr
    exact ⟨(Q.endBoard s b).expRm_congr hd, by simp [hasBarrier, hd]⟩
  obtain ⟨hB, hB'⟩ := key .lower _ Finset.subset_union_left
  obtain ⟨hT, hT'⟩ := key .upper _ Finset.subset_union_right
  exact ⟨by simp [exAll, hB, hT], and_congr hB' hT'⟩

/-- A cell is an end of the primal edge of some medial vertex of `S`. -/
def Vtx (S : Finset Cell) (c : Cell) : Prop :=
  ∃ e ∈ S, c = (primalEnds e).1 ∨ c = (primalEnds e).2

theorem primalEnds_fst_row (e : Cell) : (primalEnds e).1.2 = e.2 := by
  unfold primalEnds; split_ifs <;> rfl

theorem primalEnds_snd_row (e : Cell) : (primalEnds e).2.2 = e.2 - 1 := by
  unfold primalEnds; split_ifs <;> rfl

theorem Vtx_iff_corners {S : Finset Cell} {c : Cell} (hc : IsPrimal c) :
    Vtx S c ↔ ∃ e ∈ S, e ∈ corners c := by
  simp_all [mem_primalEnds_iff, Vtx]

theorem Vtx_row_of_inner {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell} (hc : Vtx S c) :
    R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  obtain ⟨e, he, h⟩ := hc
  have := Rect.mem_inner.1 (hS he)
  rcases h with rfl | rfl
  · rw [primalEnds_fst_row]; omega
  · rw [primalEnds_snd_row]; omega

theorem Vtx_mem_pcells {R : Rect} {S : Finset Cell} (hS : S ⊆ R.inner) {c : Cell}
    (hc : Vtx S c) : c ∈ R.pcells := by
  obtain ⟨e, he, h⟩ := hc
  have hd := R.pData.mem e (hS he)
  rcases h with rfl | rfl
  · exact hd.1
  · exact hd.2

/-- A side consists of the vertices of its exploration and the outer port. -/
def sideVertices (Q : Rect) (s : Side) (b : ℕ) (A : Finset Cell) (c : Cell) : Prop :=
  Vtx (Q.explored s b A) c ∨ c.2 = Q.outerRow s

private theorem side_rows {A : Finset Cell} {c : Cell} {s : Side} {b : ℕ}
    (hc : Q.sideVertices s b A c) : (Q.endBoard s b).y0 ≤ c.2 ∧
      c.2 ≤ (Q.endBoard s b).y0 + b := by
  rcases hc with h | h
  · exact Vtx_row_of_inner (explored_subset s b A) h
  · cases s <;> simp [endBoard, outerRow] at h ⊢ <;> omega

private theorem Wlow_Wup_disjoint (hg : Q.Geo bB bT) {A : Finset Cell} {c : Cell}
    (h1 : Q.sideVertices .lower bB A c) (h2 : Q.sideVertices .upper bT A c) : False := by
  have a := (side_rows h1).2
  have b := (side_rows h2).1
  simp only [endBoard] at a b
  have := hg.hgap
  omega

theorem corner_coords {c e : Cell} (he : e ∈ corners c) :
    (e.1 = c.1 ∨ e.1 = c.1 + 1) ∧ (e.2 = c.2 ∨ e.2 = c.2 + 1) := by
  unfold corners at he
  grind

private theorem Vtx.isPrimal {S : Finset Cell} {c : Cell} (h : Vtx S c) : IsPrimal c := by
  obtain ⟨e, _, rfl | rfl⟩ := h
  exacts [primalEnds_fst_primal e, primalEnds_snd_primal e]

/-- An unexplored edge on an explored side meets the boundary of that side's exploration.
The argument is independent of which of the two outer rows starts the exploration. -/
private theorem explored_side_boundary {R : Rect} {S A : Finset Cell} {p₁ p₂ : ℤ}
    (hh : 0 < R.h)
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    (hex : R.expRm p₁ p₂ A ⊆ S) {c : Cell}
    (hside : Vtx (R.expRm p₁ p₂ A) c ∨ c.2 = p₁) (hUn : Vtx (Q.inner \ S) c)
    (hrow : c ∈ Q.pcells → c.2 = p₁ → c ∈ R.pcells)
    (hamb : ∀ c ∈ R.pcells, c.2 ≠ p₂ → ∀ e ∈ corners c, e ∈ Q.inner → e ∈ R.inner) :
    Vtx (R.expBd p₁ p₂ A) c := by
  have hc := hUn.isPrimal
  obtain ⟨e, he, hce⟩ := (Vtx_iff_corners hc).1 hUn
  obtain ⟨hQ, hS⟩ := Finset.mem_sdiff.mp he
  have hne := fun h => hS (hex h)
  rcases hside with hV | hrow₁
  · have hcR := Vtx_mem_pcells (R := R) (fun _ h => (mem_expRm_iff.mp h).1) hV
    obtain ⟨e', he', hce'⟩ := (Vtx_iff_corners hc).1 hV
    obtain ⟨b, hbc, hbd⟩ := vex_vun hh hp hb Q.inner hamb hcR
      ⟨e', hce', he'⟩ ⟨e, hce, hQ, hne⟩
    exact (Vtx_iff_corners hc).2 ⟨b, hbd, hbc⟩
  · have hcR := hrow (Vtx_mem_pcells Finset.sdiff_subset hUn) hrow₁
    have hrow₂ : c.2 ≠ p₂ := by rcases hp with hp | hp <;> omega
    exact (hne (corner_expRm_of_row_p1 (A := A) hcR hrow₁ hce (hamb _ hcR hrow₂ _ hce hQ))).elim

private theorem side_Un_bd {s : Side} {b : ℕ} {S A : Finset Cell} (hb : 0 < b)
    (hbar : Q.hasBarrier s b A) (hex : Q.explored s b A ⊆ S) {c : Cell}
    (hW : Q.sideVertices s b A c) (hUn : Vtx (Q.inner \ S) c) : Vtx (Q.barrier s b A) c := by
  refine explored_side_boundary hb (port_rows Q s b) hbar hex hW hUn ?_ ?_
  · intro hc hy
    cases s <;> simp only [Rect.mem_pcells, Rect.mem_cells, endBoard, outerRow] at hc hy ⊢ <;> exact ⟨by omega, hc.2⟩
  · intro z hz hn e he hQ
    have := corner_coords he
    cases s <;> simp only [Rect.mem_pcells, Rect.mem_cells, Rect.mem_inner, endBoard, innerRow]
      at hz hn hQ ⊢ <;> omega

theorem step_ends {S : Finset Cell} {z z' : Cell} (h : StepRel primalEnds S z z') :
    ∃ m ∈ S, (z = (primalEnds m).1 ∧ z' = (primalEnds m).2) ∨
      (z = (primalEnds m).2 ∧ z' = (primalEnds m).1) := by
  obtain ⟨m, hm, h⟩ := h
  refine ⟨m, hm, ?_⟩
  rcases h with h | h
  · simp_all
  simp_all

theorem step_of_mem {S : Finset Cell} {m : Cell} (hm : m ∈ S) :
    StepRel primalEnds S (primalEnds m).1 (primalEnds m).2 := ⟨m, hm, Or.inl rfl⟩

theorem barrier_subset_explored (Q : Rect) (s : Side) (b : ℕ) (A : Finset Cell) :
    Q.barrier s b A ⊆ Q.explored s b A := expBd_subset_expRm _ _ _

private theorem step_exAll_sides {A : Finset Cell} {x y : Cell}
    (h : StepRel primalEnds (Q.exAll bB bT A) x y) :
    (Q.sideVertices .lower bB A x ∧ Q.sideVertices .lower bB A y) ∨
      (Q.sideVertices .upper bT A x ∧ Q.sideVertices .upper bT A y) := by
  have key (s : Side) (b : ℕ) (h : StepRel primalEnds (Q.explored s b A) x y) :
      Q.sideVertices s b A x ∧ Q.sideVertices s b A y := by
    obtain ⟨m, hm, h | h⟩ := step_ends h <;> exact ⟨Or.inl ⟨_, hm, by tauto⟩, Or.inl ⟨_, hm, by tauto⟩⟩
  obtain ⟨m, hm, hf⟩ := h
  exact (Finset.mem_union.1 hm).imp (fun hm => key .lower bB ⟨m, hm, hf⟩)
    (fun hm => key .upper bT ⟨m, hm, hf⟩)

/-- Unexplored edges, together with the two barriers, connect the barriers. -/
def Success (L U : Finset Cell) : Set (Finset Cell) :=
  {A | ∃ x y, Vtx L x ∧ Vtx U y ∧
    Relation.ReflTransGen (StepRel primalEnds (A ∪ L ∪ U)) x y}

/-- The key topological consequence of the local analysis: an open path from the bottom row to the
top row of `Q`, in a configuration containing all explored edges, yields a path from the boundary
of the lower exploration to the boundary of the upper exploration which uses only unexplored open
edges and boundary edges. -/
theorem cross_to_success (hg : Q.Geo bB bT) {A₀ A : Finset Cell} (hbar : Q.barAll bB bT A₀)
    (hA : A ⊆ Q.inner) {u v : Cell} (hu : u.2 = Q.y0)
    (hv : v.2 = Q.y0 + Q.h)
    (hpath : Relation.ReflTransGen (StepRel primalEnds A) u v) :
    A \ Q.exAll bB bT A₀ ∈ Success (Q.barrier .lower bB A₀) (Q.barrier .upper bT A₀) := by
  by_contra hno
  let E := Q.exAll bB bT A₀
  let D := (A \ E) ∪ Q.barrier .lower bB A₀ ∪ Q.barrier .upper bT A₀
  -- Until a successful connection is found, every point reached is either on the lower
  -- side or connected to its boundary through unexplored edges, but not on the upper side.
  have hreach : Q.sideVertices .lower bB A₀ v ∨
      (¬ Q.sideVertices .upper bT A₀ v ∧ ∃ x, Vtx (Q.barrier .lower bB A₀) x ∧ Relation.ReflTransGen (StepRel primalEnds D) x v) := by
    clear hv
    induction hpath with
    | refl => exact Or.inl (Or.inr hu)
    | @tail a b _ hab ih =>
      obtain ⟨m, hm, hrep⟩ := hab
      by_cases hE : m ∈ E
      · rcases step_exAll_sides (show StepRel primalEnds E a b from ⟨m, hE, hrep⟩) with h | h
        · exact Or.inl h.2
        · exact False.elim (ih.elim (fun ha => Wlow_Wup_disjoint hg ha h.1) (fun ha => ha.1 h.1))
      · have ha : Vtx (Q.inner \ E) a := by
          refine ⟨m, Finset.mem_sdiff.mpr ⟨hA hm, hE⟩, ?_⟩
          grind
        have hb : Vtx (Q.inner \ E) b := by
          refine ⟨m, Finset.mem_sdiff.mpr ⟨hA hm, hE⟩, ?_⟩
          grind
        have hd : StepRel primalEnds D a b := ⟨m, Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hm, hE⟩)), hrep⟩
        obtain ⟨x, hx, hxa⟩ : ∃ x, Vtx (Q.barrier .lower bB A₀) x ∧ Relation.ReflTransGen (StepRel primalEnds D) x a :=
          ih.elim (fun h => ⟨a, side_Un_bd hg.hbB hbar.1 Finset.subset_union_left h ha, .refl⟩) And.right
        exact Or.inr ⟨fun h => hno ⟨x, b, hx, side_Un_bd hg.hbT hbar.2 Finset.subset_union_right h hb, hxa.tail hd⟩,
          x, hx, hxa.tail hd⟩
  exact hreach.elim (fun h => Wlow_Wup_disjoint hg h (Or.inr hv)) fun h => h.1 (Or.inr hv)

private theorem vtx_connected_of_first_connected {S : Finset Cell}
    (hS : ∀ ⦃m m'⦄, m ∈ S → m' ∈ S →
      Relation.ReflTransGen (StepRel primalEnds S) (primalEnds m).1 (primalEnds m').1)
    {x y : Cell} (hx : Vtx S x) (hy : Vtx S y) : Relation.ReflTransGen (StepRel primalEnds S) x y := by
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨n, hn, hny⟩ := hy
  have hfirst {e z} (he : e ∈ S) (hz : z = (primalEnds e).1 ∨ z = (primalEnds e).2) :
      Relation.ReflTransGen (StepRel primalEnds S) (primalEnds e).1 z :=
    hz.elim (fun h => h ▸ .refl) (fun h => h ▸ .single (step_of_mem he))
  have hback : Relation.ReflTransGen (StepRel primalEnds S) x (primalEnds m).1 := by
    rcases hmx with rfl | rfl
    · exact .refl
    · exact .single (stepRel_symm (step_of_mem hm))
  exact hback.trans ((hS hm hn).trans (hfirst hn hny))

theorem Vtx_barrier_connected {s : Side} {b : ℕ} (hb : 0 < b) (hw : 0 < Q.w)
    {A : Finset Cell} (hbar : Q.hasBarrier s b A) {x y : Cell}
    (hx : Vtx (Q.barrier s b A) x) (hy : Vtx (Q.barrier s b A) y) :
    Relation.ReflTransGen (StepRel primalEnds (Q.barrier s b A)) x y := by
  exact vtx_connected_of_first_connected (fun _ _ =>
    (Q.endBoard s b).bd_connected hb hw (port_rows Q s b) hbar) hx hy

/-- The equivalence classes are the lower side, the upper side and the remaining singletons. -/
private def sideSetoid (hg : Q.Geo bB bT) (A₀ : Finset Cell) : Setoid Cell where
  r a b := a = b ∨ (Q.sideVertices .lower bB A₀ a ∧ Q.sideVertices .lower bB A₀ b) ∨ (Q.sideVertices .upper bT A₀ a ∧ Q.sideVertices .upper bT A₀ b)
  iseqv := ⟨fun _ => Or.inl rfl, by grind, by
    intro a b c hab hbc
    have hb := @Wlow_Wup_disjoint Q bB bT hg A₀ b
    grind⟩

private theorem componentSetoid_le_side (hg : Q.Geo bB bT) (A₀ : Finset Cell) :
    FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀)) ≤
      (sideSetoid hg A₀).comap Subtype.val := by
  apply FK.componentSetoid_le
  · intro x y h
    rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData _ (exAll_subset_inner A₀ hg)] at h
    have key (a b : Cell) (h : Relation.ReflTransGen (StepRel primalEnds (Q.exAll bB bT A₀)) a b) :
        (sideSetoid hg A₀).r a b := by
      induction h with
      | refl => exact (sideSetoid hg A₀).refl _
      | tail _ hstep ih => exact (sideSetoid hg A₀).trans ih (Or.inr (step_exAll_sides hstep))
    exact key _ _ h
  · rintro x y (h | h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl ⟨Or.inr h.1, Or.inr h.2⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h.1, Or.inr h.2⟩)

/-- **Boundary comparison at the cell level**: two cells seeing unexplored edges and related in the
partition induced by the sep-wiring and the explored edges are equal or lie on the same boundary. -/
theorem kc (hg : Q.Geo bB bT) {A₀ : Finset Cell} (hbar : Q.barAll bB bT A₀) {x y : Q.pcells}
    (hx : Vtx (Q.inner \ Q.exAll bB bT A₀) x.1) (hy : Vtx (Q.inner \ Q.exAll bB bT A₀) y.1)
    (h : (FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData (Q.exAll bB bT A₀))).r x y) :
    x = y ∨ (Vtx (Q.barrier .lower bB A₀) x.1 ∧ Vtx (Q.barrier .lower bB A₀) y.1) ∨
      (Vtx (Q.barrier .upper bT A₀) x.1 ∧ Vtx (Q.barrier .upper bT A₀) y.1) := by
  rcases componentSetoid_le_side hg A₀ h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl ⟨side_Un_bd hg.hbB hbar.1 Finset.subset_union_left h₁ hx, side_Un_bd hg.hbB hbar.1 Finset.subset_union_left h₂ hy⟩)
  · exact Or.inr (Or.inr ⟨side_Un_bd hg.hbT hbar.2 Finset.subset_union_right h₁ hx, side_Un_bd hg.hbT hbar.2 Finset.subset_union_right h₂ hy⟩)

end Rect

end PottsDiscontinuity.TorusCrossing
