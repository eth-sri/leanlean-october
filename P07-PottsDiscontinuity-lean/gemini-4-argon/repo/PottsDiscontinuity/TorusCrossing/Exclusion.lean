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

def cochainRel (A : Finset Cell) (x y : R.pcells) : Prop :=
  ∃ f : Cell → ZMod 2, (∀ m, f m ≠ 0 → m ∈ A ∨ m ∈ R.collarAll) ∧
    ∀ c, IsPrimal c → cdeg f c = (if c = x.1 then 1 else 0) + (if c = y.1 then 1 else 0)

theorem cochainRel_refl (A : Finset Cell) (x : R.pcells) : R.cochainRel A x x :=
  ⟨fun _ => 0, fun _ hm => absurd rfl hm, fun c _ => by rw [cdeg_zero]; split_ifs <;> decide⟩

theorem cochainRel_symm (A : Finset Cell) {x y : R.pcells} (h : R.cochainRel A x y) :
    R.cochainRel A y x := by
  obtain ⟨f, hf, hdeg⟩ := h
  exact ⟨f, hf, fun c hc => by rw [hdeg c hc, add_comm]⟩

theorem cochainRel_trans (A : Finset Cell) {x y z : R.pcells} (h : R.cochainRel A x y)
    (h' : R.cochainRel A y z) : R.cochainRel A x z := by
  obtain ⟨f, hf, hdeg⟩ := h
  obtain ⟨g, hg, hdeg'⟩ := h'
  refine ⟨fun m => f m + g m, fun m hm => ?_, fun c hc => ?_⟩
  · dsimp at hm
    by_cases h1 : f m = 0 <;> [exact hg m (by rwa [h1, zero_add] at hm); exact hf m h1]
  · rw [cdeg_add, hdeg c hc, hdeg' c hc]
    generalize (if c = x.1 then (1 : ZMod 2) else 0) = a
    generalize (if c = y.1 then (1 : ZMod 2) else 0) = b
    generalize (if c = z.1 then (1 : ZMod 2) else 0) = d
    revert a b d; decide

def cochainSetoid (A : Finset Cell) : Setoid R.pcells where
  r := R.cochainRel A
  iseqv := ⟨R.cochainRel_refl A, R.cochainRel_symm A, R.cochainRel_trans A⟩

theorem collar_bottom_subset (lo hi : ℤ) (h1 : R.x0 ≤ lo) (h2 : hi ≤ R.x0 + R.w) :
    collar R.y0 lo hi ⊆ R.collarAll := fun m hm => by
  rw [mem_collar] at hm
  rw [collarAll, Finset.mem_union, mem_collar, mem_collar]
  left; omega

theorem collar_top_subset (lo hi : ℤ) (h1 : R.x0 ≤ lo) (h2 : hi ≤ R.x0 + R.w) :
    collar (R.y0 + R.h + 1) lo hi ⊆ R.collarAll := fun m hm => by
  rw [mem_collar] at hm
  rw [collarAll, Finset.mem_union, mem_collar, mem_collar]
  right; omega

private theorem cochainRel_of_row_le (A : Finset Cell) (a b : R.pcells) (r r' : ℤ)
    (hr : r' = R.y0 ∧ r = R.y0 ∨ r' = R.y0 + R.h ∧ r = R.y0 + R.h + 1)
    (ha : a.1.2 = r') (hb : b.1.2 = r') (hab : a.1.1 ≤ b.1.1) : R.cochainRel A a b := by
  have hac := mem_cells.1 (mem_pcells.1 a.2).1
  have hbc := mem_cells.1 (mem_pcells.1 b.2).1
  have hap := (mem_pcells.1 a.2).2
  have hbp := (mem_pcells.1 b.2).2
  refine ⟨ind (collar r a.1.1 b.1.1), fun m hm => Or.inr ?_, fun c hc => ?_⟩
  · have hmem : m ∈ collar r a.1.1 b.1.1 := by by_contra hn; exact hm (ind_apply_of_not_mem hn)
    rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact R.collar_bottom_subset _ _ hac.1 hbc.2.1 hmem
    · exact R.collar_top_subset _ _ hac.1 hbc.2.1 hmem
  · rw [cdeg_collar r a.1.1 b.1.1 hab r' (by omega)
      (by unfold IsPrimal at *; rwa [← ha]) (by unfold IsPrimal at *; rwa [← hb]) c hc,
      show (a.1.1, r') = a.1 from Prod.ext rfl ha.symm,
      show (b.1.1, r') = b.1 from Prod.ext rfl hb.symm]

theorem cochainRel_of_row (A : Finset Cell) (a b : R.pcells) (r r' : ℤ)
    (hr : r' = R.y0 ∧ r = R.y0 ∨ r' = R.y0 + R.h ∧ r = R.y0 + R.h + 1)
    (ha : a.1.2 = r') (hb : b.1.2 = r') : R.cochainRel A a b := by
  rcases le_total a.1.1 b.1.1 with hab | hab
  · exact R.cochainRel_of_row_le A a b r r' hr ha hb hab
  · exact R.cochainRel_symm A (R.cochainRel_of_row_le A b a r r' hr hb ha hab)

theorem sep_le_cochain (A : Finset Cell) (hA : A ⊆ R.inner) :
    FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A) ≤ R.cochainSetoid A := by
  apply FK.componentSetoid_le
  · apply FK.reachableSetoid_le_of_adj
    intro x y hxy
    have hxy' := (openGraph_adj_iff R.pData (cfgOf R.pData A) x y).1 hxy
    rw [openMedials_cfgOf R.pData A hA] at hxy'
    obtain ⟨m, hm, hmxy⟩ := hxy'
    refine ⟨ind {m}, fun m' hm' => Or.inl ?_, fun c hc => ?_⟩
    · have : m' ∈ ({m} : Finset Cell) := by by_contra hn; exact hm' (ind_apply_of_not_mem hn)
      rwa [Finset.mem_singleton.1 this]
    · rw [cdeg_ind_single m c hc]
      rcases hmxy with h | h <;> [rw [h]; rw [h, add_comm]]
  · rintro a b (rfl | h | h)
    · exact R.cochainRel_refl A a
    · exact R.cochainRel_of_row A a b R.y0 R.y0 (Or.inl ⟨rfl, rfl⟩) h.1 h.2
    · exact R.cochainRel_of_row A a b (R.y0 + R.h + 1) (R.y0 + R.h) (Or.inr ⟨rfl, rfl⟩) h.1 h.2

theorem not_mem_collarAll_of_inner {m : Cell} (hm : m ∈ R.inner) : m ∉ R.collarAll := by
  intro h
  rw [collarAll, Finset.mem_union, mem_collar, mem_collar] at h
  rw [mem_inner] at hm; omega

theorem mem_collarAll {m : Cell} (h : m ∈ R.collarAll) :
    R.x0 < m.1 ∧ m.1 ≤ R.x0 + R.w ∧ (m.2 = R.y0 ∨ m.2 = R.y0 + R.h + 1) := by
  rw [collarAll, Finset.mem_union, mem_collar, mem_collar] at h; omega

def dualBC : FK.BoundaryCondition R.dcells :=
  FK.BoundaryCondition.wired {z | z.1.1 = R.x0 ∨ z.1.1 = R.x0 + R.w}

theorem exclusion (A : Finset Cell) (hA : A ⊆ R.inner) (m : Cell) (hm : m ∈ R.inner)
    (hmA : m ∉ A) (u v : R.pcells) (hu : u.1 = (primalEnds m).1) (hv : v.1 = (primalEnds m).2)
    (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m).1) (hv' : v'.1 = (dualEnds m).2)
    (hrel : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    ¬ (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m A))).r u' v' := by
  intro hdual
  obtain ⟨f, hf, hdeg⟩ := R.sep_le_cochain A hA hrel
  set C₀ : Cell → ZMod 2 := fun m' => f m' + ind {m} m' with hC₀
  have hclosed (c : Cell) (hc : IsPrimal c) : cdeg C₀ c = 0 := by
    rw [hC₀, cdeg_add, hdeg c hc, cdeg_ind_single m c hc, hu, hv]
    generalize (if c = (primalEnds m).1 then (1 : ZMod 2) else 0) = a
    generalize (if c = (primalEnds m).2 then (1 : ZMod 2) else 0) = b
    revert a b; decide
  have hsupp (m' : Cell) (hm' : C₀ m' ≠ 0) : R.x0 < m'.1 ∧ m'.1 ≤ R.x0 + R.w ∧ R.y0 ≤ m'.2 := by
    by_cases h1 : f m' = 0
    · have : m' ∈ ({m} : Finset Cell) := by
        by_contra hn; exact hm' (by dsimp [C₀]; rw [h1, zero_add, ind_apply_of_not_mem hn])
      rw [Finset.mem_singleton.1 this]; rw [mem_inner] at hm; omega
    · rcases hf m' h1 with h | h
      · have := mem_inner.1 (hA h); omega
      · have := R.mem_collarAll h; omega
  have hx0 (m' : Cell) (h : m'.1 ≤ R.x0) : C₀ m' = 0 := by
    by_contra hne; have := hsupp m' hne; omega
  have hxw (m' : Cell) (h : R.x0 + (R.w : ℤ) < m'.1) : C₀ m' = 0 := by
    by_contra hne; have := hsupp m' hne; omega
  have hy0 (m' : Cell) (h : m'.2 ≤ R.y0 - 1) : C₀ m' = 0 := by
    by_contra hne; have := hsupp m' hne; omega
  set g : Cell → ZMod 2 := leftPotential R.x0 (R.y0 - 1) C₀
  have hprim (m' : Cell) (h1 : R.x0 < m'.1) (h2 : m'.1 ≤ R.x0 + R.w) :
      g (dualEnds m').1 + g (dualEnds m').2 = C₀ m' :=
    leftPotential_primitive R.x0 (R.y0 - 1) R.w C₀ hx0 hy0 (fun c hc _ _ => hclosed c hc) m' h1 h2
  have hzero (z : Cell) (hz : z.1 = R.x0 ∨ z.1 = R.x0 + R.w) : g z = 0 :=
    leftPotential_zero_of_closed R.x0 (R.y0 - 1) R.w C₀ hx0 hxw hy0
      (fun c hc _ _ => hclosed c hc) (by positivity) z (by omega)
  have hfm_zero (m' : Cell) (hmi : m' ∈ R.inner) (hmA' : m' ∉ A) : f m' = 0 := by
    by_contra hne
    exact (hf m' hne).elim hmA' (R.not_mem_collarAll_of_inner hmi)
  have hker : FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m A)) ≤
      Setoid.ker (fun z : R.dcells => g z.1) := by
    apply FK.componentSetoid_le
    · apply FK.reachableSetoid_le_of_adj
      intro x y hxy
      have hxy' := (openGraph_adj_iff R.dData _ x y).1 hxy
      rw [openMedials_cfgOf R.dData _ Finset.sdiff_subset] at hxy'
      obtain ⟨m', hm', hmxy⟩ := hxy'
      rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hm'
      obtain ⟨hmi, hm1, hm2⟩ := hm'
      have hmi' := mem_inner.1 hmi
      have hs := hprim m' (by omega) (by omega)
      dsimp [C₀] at hs
      rw [hfm_zero m' hmi hm2, ind_apply_of_not_mem (by simpa using hm1), add_zero] at hs
      show g x.1 = g y.1
      rcases hmxy with h | h <;> rw [h] at hs <;>
        (revert hs; generalize g x.1 = a; generalize g y.1 = b; decide +revert)
    · rintro a b (rfl | ⟨ha, hb⟩)
      · rfl
      · show g a.1 = g b.1; rw [hzero a.1 ha, hzero b.1 hb]
  have hs := hprim m (by rw [mem_inner] at hm; omega) (by rw [mem_inner] at hm; omega)
  have hgeq : g u'.1 = g v'.1 := hker hdual
  dsimp [C₀] at hs
  rw [hfm_zero m hm hmA, ind_apply_of_mem (Finset.mem_singleton_self m), zero_add,
    ← hu', ← hv', hgeq, zmod2_two] at hs
  exact absurd hs (by decide)

end Rect

end PottsDiscontinuity.TorusCrossing
