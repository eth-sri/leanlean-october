module

public import PottsDiscontinuity.FK.Wiring
public import PottsDiscontinuity.TorusCrossing.Cochain
public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# Exclusion: a primal connection and a crossing dual connection cannot coexist

If two primal cells are connected (with the bottom and top rows wired) in the configuration `A`,
then the dual endpoints of any closed edge `m` joining them cannot be connected (with left and
right columns wired) in the dual configuration `inner \ insert m A`.  The proof turns the primal
connection into a closed cochain (a primal cycle closed up by the collar zigzags that realise the
wiring) and evaluates its left-ray primitive.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity

namespace Rect

variable (R : Rect)

/-- The medial vertices of the zigzags just outside the bottom and top rows. -/
def collarAll : Finset Cell :=
  collar R.y0 R.x0 (R.x0 + R.w) ∪ collar (R.y0 + R.h + 1) R.x0 (R.x0 + R.w)

section

variable (A : Finset Cell)

/-- The relation "joined by a chain of open edges and collar zigzags", as a `ZMod 2` cochain. -/
def cochainRel (x y : R.pcells) : Prop :=
  ∃ f : Cell → ZMod 2, (∀ m, f m ≠ 0 → m ∈ A ∨ m ∈ R.collarAll) ∧
    ∀ c, IsPrimal c → cdeg f c = (if c = x.1 then 1 else 0) + (if c = y.1 then 1 else 0)

theorem cochainRel_refl (x : R.pcells) : R.cochainRel A x x := by
  refine ⟨fun _ => 0, fun m hm => absurd rfl hm, fun c _ => ?_⟩
  rw [cdeg_zero]
  split_ifs <;> decide

theorem cochainRel_symm {x y : R.pcells} (h : R.cochainRel A x y) :
    R.cochainRel A y x := by
  obtain ⟨f, hf, hdeg⟩ := h
  exact ⟨f, hf, fun c hc => by rw [hdeg c hc, add_comm]⟩

theorem cochainRel_trans {x y z : R.pcells} (h : R.cochainRel A x y)
    (h' : R.cochainRel A y z) : R.cochainRel A x z := by
  obtain ⟨f, hf, hdeg⟩ := h
  obtain ⟨g, hg, hdeg'⟩ := h'
  refine ⟨fun m => f m + g m, ?_, ?_⟩
  · intro m hm
    by_cases h : f m = 0
    · exact hg m (by simpa only [h, zero_add] using hm)
    · exact hf m h
  · intro c hc
    rw [cdeg_add, hdeg c hc, hdeg' c hc, add_assoc, ← add_assoc _ _ (ite _ _ _),
      zmod2_two, zero_add]

/-- The setoid of chain-connected primal cells. -/
def cochainSetoid : Setoid R.pcells where
  r := R.cochainRel A
  iseqv := ⟨R.cochainRel_refl A, R.cochainRel_symm A, R.cochainRel_trans A⟩

end

/-- A wiring relation between two cells of the same boundary row is a chain relation. -/
theorem cochainRel_of_row (A : Finset Cell) (a b : R.pcells) (r r' : ℤ)
    (hr : r' = R.y0 ∧ r = R.y0 ∨ r' = R.y0 + R.h ∧ r = R.y0 + R.h + 1)
    (ha : a.1.2 = r') (hb : b.1.2 = r') : R.cochainRel A a b := by
  wlog hab : a.1.1 ≤ b.1.1 generalizing a b
  · exact R.cochainRel_symm A (this b a hb ha (le_of_not_ge hab))
  have hac := mem_cells.1 (mem_pcells.1 a.2).1
  have hbc := mem_cells.1 (mem_pcells.1 b.2).1
  have ea : (a.1.1, r') = a.1 := Prod.ext rfl ha.symm
  have eb : (b.1.1, r') = b.1 := Prod.ext rfl hb.symm
  refine ⟨ind (collar r a.1.1 b.1.1), ?_, fun c hc => ?_⟩
  · intro m hm
    have h := mem_collar.mp (mem_of_ind_ne_zero hm)
    right
    grind only [mem_collar, collarAll, Finset.mem_union]
  · rw [cdeg_collar r a.1.1 b.1.1 hab r' (by omega)
      (ea ▸ (mem_pcells.1 a.2).2) (eb ▸ (mem_pcells.1 b.2).2) c hc, ea, eb]

/-- Open connectivity with wired rows is a chain relation. -/
theorem sep_le_cochain (A : Finset Cell) (hA : A ⊆ R.inner) :
    FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A) ≤ R.cochainSetoid A := by
  refine FK.componentSetoid_le _ _ _ _ (fun h => FK.reachableSetoid_le_of_adj _ _ ?_ h) ?_
  · intro x y hxy
    have h := (openGraph_adj_iff R.pData (cfgOf R.pData A) x y).1 hxy
    rw [openMedials_cfgOf R.pData A hA] at h
    obtain ⟨m, hm, hmxy⟩ := h
    refine ⟨ind {m}, fun m' hm' => Or.inl ?_, fun c hc => ?_⟩
    · simpa only [Finset.mem_singleton.mp (mem_of_ind_ne_zero hm')] using hm
    · rw [cdeg_ind_single m c hc]
      rcases hmxy with h | h <;> simp [h, add_comm]
  · intro a b hab
    rcases hab with h | h | h
    · simp_all
    · exact R.cochainRel_of_row A a b R.y0 R.y0 (Or.inl ⟨rfl, rfl⟩) h.1 h.2
    · exact R.cochainRel_of_row A a b (R.y0 + R.h + 1) (R.y0 + R.h)
        (Or.inr ⟨rfl, rfl⟩) h.1 h.2


theorem not_mem_collarAll_of_inner {m : Cell} (hm : m ∈ R.inner) : m ∉ R.collarAll := by
  intro h
  grind [mem_inner, mem_collar, collarAll]

theorem mem_collarAll {m : Cell} (h : m ∈ R.collarAll) :
    R.x0 < m.1 ∧ m.1 ≤ R.x0 + R.w ∧ (m.2 = R.y0 ∨ m.2 = R.y0 + R.h + 1) := by
  unfold collarAll at h
  rw [Finset.mem_union, mem_collar, mem_collar] at h
  omega

/-- The dual wiring: left and right columns of odd cells. -/
def dualBC : FK.BoundaryCondition R.dcells :=
  FK.BoundaryCondition.wired {z | z.1.1 = R.x0 ∨ z.1.1 = R.x0 + R.w}

/-- **Exclusion.**  If two primal cells joined by a closed edge `m` are already connected
(with wired rows), the dual endpoints of `m` are not connected in the complementary dual
configuration (with wired side columns). -/
theorem exclusion (A : Finset Cell) (hA : A ⊆ R.inner) (m : Cell) (hm : m ∈ R.inner)
    (hmA : m ∉ A) (u v : R.pcells) (hu : u.1 = (primalEnds m).1) (hv : v.1 = (primalEnds m).2)
    (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m).1) (hv' : v'.1 = (dualEnds m).2)
    (hrel : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    ¬ (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m A))).r u' v' := by
  intro hdual
  obtain ⟨f, hf, hdeg⟩ := R.sep_le_cochain A hA hrel
  let C (e : Cell) := f e + ind {m} e
  have hclosed (c : Cell) (hc : IsPrimal c) : cdeg C c = 0 := by
    dsimp [C]
    rw [cdeg_add, hdeg c hc, cdeg_ind_single m c hc, hu, hv, zmod2_two]
  have hsupp (e : Cell) (he : C e ≠ 0) : e ∈ R.inner ∨ e ∈ R.collarAll := by
    by_cases h : f e = 0
    · have h' : e = m := Finset.mem_singleton.mp
        (mem_of_ind_ne_zero (by simpa only [C, h, zero_add] using he))
      exact Or.inl (h' ▸ hm)
    · exact (hf e h).imp (fun he => hA he) id
  have hs (e : Cell) (he : C e ≠ 0) :
      R.x0 < e.1 ∧ e.1 ≤ R.x0 + R.w ∧ R.y0 ≤ e.2 := by
    rcases hsupp e he with h | h
    · have := mem_inner.mp h; omega
    · have := R.mem_collarAll h; omega
  have hx0 (e : Cell) (he : e.1 ≤ R.x0) : C e = 0 := by by_contra hn; have := hs e hn; omega
  have hxw (e : Cell) (he : R.x0 + (R.w : ℤ) < e.1) : C e = 0 := by by_contra hn; have := hs e hn; omega
  have hy0 (e : Cell) (he : e.2 ≤ R.y0 - 1) : C e = 0 := by by_contra hn; have := hs e hn; omega
  let g := leftPotential R.x0 (R.y0 - 1) C
  have hprim (e : Cell) (he : e ∈ R.inner) : g (dualEnds e).1 + g (dualEnds e).2 = C e :=
    leftPotential_primitive R.x0 (R.y0 - 1) R.w C hx0 hy0 (fun c hc _ _ => hclosed c hc)
      e (mem_inner.mp he).1 (mem_inner.mp he).2.1
  have hzero (z : Cell) (hz : z.1 = R.x0 ∨ z.1 = R.x0 + R.w) : g z = 0 :=
    leftPotential_zero_of_closed R.x0 (R.y0 - 1) R.w C hx0 hxw hy0
      (fun c hc _ _ => hclosed c hc) (by positivity) z (by omega)
  have hf0 {e : Cell} (hei : e ∈ R.inner) (heA : e ∉ A) : f e = 0 := by
    by_contra hn
    exact (hf e hn).elim heA (R.not_mem_collarAll_of_inner hei)
  have hker : FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m A)) ≤
      Setoid.ker (fun z : R.dcells => g z.1) := by
    refine FK.componentSetoid_le _ _ _ _ (fun h => FK.reachableSetoid_le_of_adj _ _ ?_ h) ?_
    · intro x y hxy
      have h := (openGraph_adj_iff R.dData _ x y).1 hxy
      rw [openMedials_cfgOf R.dData _ Finset.sdiff_subset] at h
      obtain ⟨e, he, hem⟩ := h
      rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at he
      apply potential_eq_of_ends (m := e) _ hem
      rw [hprim e he.1]
      simp [C, hf0 he.1 he.2.2, ind, he.2.1]
    · rintro a b (rfl | ⟨ha, hb⟩)
      · rfl
      · exact (hzero _ ha).trans (hzero _ hb).symm
  have h := hprim m hm
  have heq : g u'.1 = g v'.1 := hker hdual
  rw [← hu', ← hv', heq, zmod2_two] at h
  simp [C, hf0 hm hmA, ind] at h

end Rect

end PottsDiscontinuity.TorusCrossing
