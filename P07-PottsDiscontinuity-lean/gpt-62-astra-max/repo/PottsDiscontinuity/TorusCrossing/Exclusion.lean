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
variable (A : Finset Cell) (lo hi : ℤ) (h1 : R.x0 ≤ lo) (h2 : hi ≤ R.x0 + R.w) {m : Cell}

include A in
/-- The relation "joined by a chain of open edges and collar zigzags", as a `ZMod 2` cochain. -/
def cochainRel (x y : R.pcells) : Prop :=
  ∃ f, (∀ m, f m ≠ 0 → m ∈ A ∨ m ∈ R.collarAll) ∧
    ∀ c, IsPrimal c → cdeg f c = (if c = x.1 then 1 else 0) + (if c = y.1 then 1 else 0)

theorem cochainRel_refl (x : R.pcells) : R.cochainRel A x x := by
  refine ⟨fun _ => 0, fun m hm => absurd rfl hm, fun c _ => ?_⟩
  grind [cdeg_zero]

theorem cochainRel_symm {x y : R.pcells} (h : R.cochainRel A x y) :
    R.cochainRel A y x := by
  obtain ⟨f, hf, hdeg⟩ := h
  exact ⟨f, hf, fun c hc => by grind⟩

theorem cochainRel_trans {x y z : R.pcells} (h : R.cochainRel A x y)
    (h' : R.cochainRel A y z) : R.cochainRel A x z := by
  obtain ⟨f, hf, hdeg⟩ := h
  obtain ⟨g, hg, hdeg'⟩ := h'
  refine ⟨fun m => f m + g m, ?_, ?_⟩
  · grind
  · intro c hc
    grind [cdeg_add, hdeg c hc, hdeg' c hc]

include A in
/-- The setoid of chain-connected primal cells. -/
def cochainSetoid : Setoid R.pcells where
  r := R.cochainRel A
  iseqv := ⟨R.cochainRel_refl A, R.cochainRel_symm A, R.cochainRel_trans A⟩

include h1 h2 in
theorem collar_bottom_subset :
    collar R.y0 lo hi ⊆ R.collarAll := by
  grind [mem_collar, Finset.mem_union, collarAll]

include h1 h2 in
theorem collar_top_subset :
    collar (R.y0 + R.h + 1) lo hi ⊆ R.collarAll := by
  grind [mem_collar, Finset.mem_union, collarAll]

/-- A wiring relation between two cells of the same boundary row is a chain relation. -/
theorem cochainRel_of_row (a b : R.pcells) (r r' : ℤ)
    (hr : r' = R.y0 ∧ r = R.y0 ∨ r' = R.y0 + R.h ∧ r = R.y0 + R.h + 1)
    (ha : a.1.2 = r') (hb : b.1.2 = r') : R.cochainRel A a b := by
  have hac := mem_cells.1 (mem_pcells.1 a.2).1
  have hbc := mem_cells.1 (mem_pcells.1 b.2).1
  have hap := (mem_pcells.1 a.2).2
  have hbp := (mem_pcells.1 b.2).2
  have hrr : r' = r ∨ r' = r - 1 := by omega
  rcases le_total a.1.1 b.1.1 with hab | hab
  · refine ⟨ind (collar r a.1.1 b.1.1), ?_, ?_⟩
    · intro m hm
      right
      have : m ∈ collar r a.1.1 b.1.1 := by
        by_contra hn; exact hm (ind_apply_of_not_mem hn)
      rcases hr with hr | hr
      · rw [hr.2] at this
        exact R.collar_bottom_subset _ _ hac.1 hbc.2.1 this
      · rw [hr.2] at this
        exact R.collar_top_subset _ _ hac.1 hbc.2.1 this
    · intro c hc
      rw [cdeg_collar r a.1.1 b.1.1 hab r' hrr (by grind) (by grind) c hc]
      grind
  · refine ⟨ind (collar r b.1.1 a.1.1), ?_, ?_⟩
    · intro m hm
      right
      have : m ∈ collar r b.1.1 a.1.1 := by
        by_contra hn; exact hm (ind_apply_of_not_mem hn)
      rcases hr with hr | hr
      · rw [hr.2] at this
        exact R.collar_bottom_subset _ _ hbc.1 hac.2.1 this
      · rw [hr.2] at this
        exact R.collar_top_subset _ _ hbc.1 hac.2.1 this
    · intro c hc
      rw [cdeg_collar r b.1.1 a.1.1 hab r' hrr (by grind) (by grind) c hc]
      grind

/-- Open connectivity with wired rows is a chain relation. -/
theorem sep_le_cochain (hA : A ⊆ R.inner) :
    FK.componentSetoid R.sepBC (cfgOf R.pData A) ≤ R.cochainSetoid A := by
  apply FK.componentSetoid_le
  · intro u v huv
    have hle : (FK.openGraph (cfgOf R.pData A)).reachableSetoid ≤ R.cochainSetoid A := by
      apply FK.reachableSetoid_le_of_adj
      intro x y hxy
      have hxy' := (openGraph_adj_iff R.pData _ x y).1 hxy
      rw [openMedials_cfgOf R.pData hA] at hxy'
      obtain ⟨m, hm, hmxy⟩ := hxy'
      refine ⟨ind {m}, ?_, ?_⟩
      · intro m' hm'
        left
        have : m' ∈ ({m} : Finset Cell) := by
          by_contra hn; exact hm' (ind_apply_of_not_mem hn)
        grind
      · intro c hc
        rw [cdeg_ind_single m c hc]
        grind
    exact hle huv
  · intro a b hab
    rcases hab with h | h | h
    · simp_all
    · exact R.cochainRel_of_row A a b R.y0 R.y0 (Or.inl ⟨rfl, rfl⟩) h.1 h.2
    · exact R.cochainRel_of_row A a b _ _
        (Or.inr ⟨rfl, rfl⟩) h.1 h.2


theorem not_mem_collarAll_of_inner (hm : m ∈ R.inner) : m ∉ R.collarAll := by
  grind [Finset.mem_union, mem_collar, mem_inner, collarAll]

theorem mem_collarAll (h : m ∈ R.collarAll) :
    R.x0 < m.1 ∧ m.1 ≤ R.x0 + R.w ∧ (m.2 = R.y0 ∨ m.2 = R.y0 + R.h + 1) := by
  grind [Finset.mem_union, mem_collar, collarAll]

end

/-- The dual wiring: left and right columns of odd cells. -/
def dualBC : FK.BoundaryCondition R.dcells :=
  FK.BoundaryCondition.wired {z | z.1.1 = R.x0 ∨ z.1.1 = R.x0 + R.w}

/-- **Exclusion.**  If two primal cells joined by a closed edge `m` are already connected
(with wired rows), the dual endpoints of `m` are not connected in the complementary dual
configuration (with wired side columns). -/
theorem exclusion (A : Finset Cell) (hA : A ⊆ R.inner) (m : Cell) (hm : m ∈ R.inner)
    (hmA : m ∉ A) (u v : R.pcells) (hu : u.1 = (primalEnds m).1) (hv : v.1 = (primalEnds m).2)
    (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m).1) (hv' : v'.1 = (dualEnds m).2)
    (hrel : (FK.componentSetoid R.sepBC (cfgOf R.pData A)).r u v) :
    ¬ (FK.componentSetoid R.dualBC (cfgOf R.dData (R.inner \ insert m A))).r u' v' := by
  intro hdual
  obtain ⟨f, hf, hdeg⟩ := R.sep_le_cochain A hA hrel
  set C₀ : Cell → ZMod 2 := fun m' => f m' + ind {m} m' with hC₀
  have hclosed : ∀ c, IsPrimal c → cdeg C₀ c = 0 := by
    intro c hc
    rw [hC₀, cdeg_add, hdeg c hc, cdeg_ind_single m c hc, hu, hv]
    grind
  have hsupp : ∀ m', C₀ m' ≠ 0 → R.x0 < m'.1 ∧ m'.1 ≤ R.x0 + R.w ∧ R.y0 ≤ m'.2 := by
    intro m' hm'
    change f m' + ind {m} m' ≠ 0 at hm'
    by_cases h1 : f m' = 0
    · rw [h1, zero_add] at hm'
      have : m' ∈ ({m} : Finset Cell) := by
        by_contra hn; exact hm' (ind_apply_of_not_mem hn)
      grind [Finset.mem_singleton, mem_inner]
    · rcases hf m' h1 with h | h
      · grind [mem_inner]
      · have := R.mem_collarAll h; omega
  have hx0 : ∀ m' : Cell, m'.1 ≤ R.x0 → C₀ m' = 0 := by
    grind
  have hxw : ∀ m' : Cell, R.x0 + (R.w : ℤ) < m'.1 → C₀ m' = 0 := by
    grind
  have hy0 : ∀ m' : Cell, m'.2 ≤ R.y0 - 1 → C₀ m' = 0 := by
    grind
  have hclosed' : ∀ c : Cell, IsPrimal c → R.x0 ≤ c.1 → c.1 ≤ R.x0 + R.w → cdeg C₀ c = 0 :=
    fun c hc _ _ => hclosed c hc
  set g : Cell → ZMod 2 := leftPotential R.x0 (R.y0 - 1) C₀ with hg
  have hprim : ∀ m' : Cell, R.x0 < m'.1 → m'.1 ≤ R.x0 + R.w →
      g (dualEnds m').1 + g (dualEnds m').2 = C₀ m' := fun m' h1 h2 =>
    leftPotential_primitive R.x0 (R.y0 - 1) R.w C₀ hx0 hy0
      (fun c hc _ _ => hclosed c hc) m' h1 h2
  have hzero : ∀ z : Cell, z.1 = R.x0 ∨ z.1 = R.x0 + R.w → g z = 0 := by
    intro z hz
    exact leftPotential_zero_of_closed R.x0 (R.y0 - 1) R.w C₀ hx0 hxw hy0 hclosed' (by positivity)
      z (by omega)
  -- the dual component relation is contained in the kernel of `g`
  have hker : FK.componentSetoid R.dualBC (cfgOf R.dData (R.inner \ insert m A)) ≤
      Setoid.ker (fun z : R.dcells => g z.1) := by
    apply FK.componentSetoid_le
    · intro x y hxy
      have hle : (FK.openGraph (cfgOf R.dData (R.inner \ insert m A))).reachableSetoid ≤
          Setoid.ker (fun z : R.dcells => g z.1) := by
        apply FK.reachableSetoid_le_of_adj
        intro x y hxy
        have hxy' := (openGraph_adj_iff R.dData _ x y).1 hxy
        rw [openMedials_cfgOf R.dData Finset.sdiff_subset] at hxy'
        obtain ⟨m', hm', hmxy⟩ := hxy'
        rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hm'
        obtain ⟨hmi, hm1, hm2⟩ := hm'
        have hmi' := mem_inner.1 hmi
        have h0 : C₀ m' = 0 := by
          change f m' + ind {m} m' = 0
          have e1 : f m' = 0 := by
            by_contra hne
            rcases hf m' hne with h | h
            · exact hm2 h
            · exact R.not_mem_collarAll_of_inner hmi h
          have e2 : ind {m} m' = 0 := ind_apply_of_not_mem (by simpa using hm1)
          simp [e1, e2]
        have hs := hprim m' (by omega) (by omega)
        rw [h0] at hs
        show g x.1 = g y.1
        grind
      exact hle hxy
    · intro a b hab
      rcases hab with h | ⟨ha, hb⟩
      · subst h; rfl
      · show g a.1 = g b.1
        rw [hzero a.1 ha, hzero b.1 hb]
  have hker' := hker hdual
  have hgeq : g u'.1 = g v'.1 := hker'
  have hs := hprim m (by grind [mem_inner]) (by grind [mem_inner])
  have hfm : f m = 0 := by
    by_contra hne
    rcases hf m hne with h | h
    · exact hmA h
    · exact R.not_mem_collarAll_of_inner hm h
  have hCm : C₀ m = 1 := by
    change f m + ind {m} m = 1
    rw [hfm, ind_apply_of_mem (Finset.mem_singleton_self m)]; simp
  grind

end Rect

end PottsDiscontinuity.TorusCrossing
