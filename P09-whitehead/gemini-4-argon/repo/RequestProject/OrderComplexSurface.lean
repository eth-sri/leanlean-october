module

public import RequestProject.BarycentricSurface

@[expose] public section

namespace FiniteChains.ASC

universe u

variable {P : Type u} [PartialOrder P]

structure SurfaceRank (P : Type u) [PartialOrder P] where
  rk : P → ℕ
  rk_lt_of_lt : ∀ {x y : P}, x < y → rk x < rk y
  rk_le_two : ∀ x : P, rk x ≤ 2
  two_vertices : ∀ e : P, rk e = 1 → ExactlyTwo (fun v : P => v < e)
  two_faces : ∀ e : P, rk e = 1 → ExactlyTwo (fun f : P => e < f)
  two_edges : ∀ v f : P, rk v = 0 → rk f = 2 → v < f →
    ExactlyTwo (fun e : P => v < e ∧ e < f)
  exists_face : ∀ x : P, ∃ f : P, rk f = 2 ∧ x ≤ f
  exists_vertex : ∀ f : P, rk f = 2 → ∃ v : P, rk v = 0 ∧ v < f

theorem ExactlyTwo.congr {α : Sort*} {P Q : α → Prop} (h : ExactlyTwo P)
    (hPQ : ∀ x, P x ↔ Q x) : ExactlyTwo Q :=
  let ⟨x, y, hxy, hx, hy, huniq⟩ := h
  ⟨x, y, hxy, (hPQ x).1 hx, (hPQ y).1 hy, fun z hz => huniq z ((hPQ z).2 hz)⟩

namespace SurfaceRank

theorem rk_eq_of_le_of_rk_le (S : SurfaceRank P) {x y : P} (h : x ≤ y) (hxy : S.rk y ≤ S.rk x) : x = y :=
  h.lt_or_eq.elim (fun hlt => absurd (S.rk_lt_of_lt hlt) (by omega)) id

theorem edgeInTwoTriangles [DecidableEq P] (S : SurfaceRank P) : EdgeInTwoTriangles (orderComplex P) := by
  have niff {x y z : P} (hxy : x < y) :
      (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
        (z ≠ x ∧ z ≠ y ∧ (z ≤ x ∨ x ≤ z) ∧ (z ≤ y ∨ y ≤ z)) := by
    rw [mem_orderComplex, show ((insert z ({x, y} : Finset P) : Finset P) : Set P) = {z, x, y} by simp]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun ⟨hne, h⟩ => ⟨hne.1, hne.2,
        le_or_le_of_isChain h (by simp) (by simp), le_or_le_of_isChain h (by simp) (by simp)⟩,
      fun ⟨h1, h2, hzx, hzy⟩ => ⟨⟨h1, h2⟩, isChain_triple hzx hzy (.inl hxy.le)⟩⟩
  have key (x y : P) (hxy : x < y) :
      ExactlyTwo (fun z : P => z ∉ ({x, y} : Finset P) ∧
        insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) := by
    have h1 := S.rk_lt_of_lt hxy; have h2 := S.rk_le_two y
    have hcases : (S.rk x = 0 ∧ S.rk y = 1) ∨ (S.rk x = 1 ∧ S.rk y = 2) ∨ (S.rk x = 0 ∧ S.rk y = 2) := by omega
    rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · refine (S.two_faces y hy).congr fun z => Iff.trans ⟨fun h => ?_, fun ⟨hzx, hzy, hcx, hcy⟩ => ?_⟩ (niff hxy).symm
      · have hxz := lt_trans hxy h
        exact ⟨Ne.symm hxz.ne, Ne.symm h.ne, .inr hxz.le, .inr h.le⟩
      · have hxz : x < z := hcx.elim (fun hh => absurd hh fun h' => hzx (S.rk_eq_of_le_of_rk_le h' (by omega)))
          (fun h => lt_of_le_of_ne h (Ne.symm hzx))
        refine hcy.elim (fun h => ?_) (fun h => lt_of_le_of_ne h (Ne.symm hzy))
        have := S.rk_lt_of_lt hxz; have := S.rk_lt_of_lt (lt_of_le_of_ne h hzy); omega
    · refine (S.two_vertices x hx).congr fun z => Iff.trans ⟨fun h => ?_, fun ⟨hzx, hzy, hcx, hcy⟩ => ?_⟩ (niff hxy).symm
      · have hzy := lt_trans h hxy
        exact ⟨h.ne, hzy.ne, .inl h.le, .inl hzy.le⟩
      · refine hcx.elim (fun h => lt_of_le_of_ne h hzx) fun h => ?_
        have := S.rk_lt_of_lt (lt_of_le_of_ne h (Ne.symm hzx)); have := S.rk_le_two z
        exact hcy.elim (fun h' => absurd (S.rk_eq_of_le_of_rk_le h' (by omega)) hzy)
          (fun h' => absurd (S.rk_eq_of_le_of_rk_le h' (by omega)) (Ne.symm hzy))
    · refine (S.two_edges x y hx hy hxy).congr fun z => Iff.trans ⟨fun ⟨h1, h2⟩ =>
        ⟨Ne.symm h1.ne, h2.ne, .inr h1.le, .inl h2.le⟩, fun ⟨hzx, hzy, hcx, hcy⟩ => ?_⟩ (niff hxy).symm
      have hxz : x < z := hcx.elim (fun hh => absurd hh fun h' => hzx (S.rk_eq_of_le_of_rk_le h' (by omega)))
        (fun h => lt_of_le_of_ne h (Ne.symm hzx))
      refine ⟨hxz, hcy.elim (fun h => lt_of_le_of_ne h hzy) fun h => ?_⟩
      have := S.rk_lt_of_lt (lt_of_le_of_ne h (Ne.symm hzy)); have := S.rk_le_two z; omega
  intro s hs hcard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
  rcases hs (by simp) (by simp) hxy with h | h
  · exact key x y (lt_of_le_of_ne h hxy)
  · rw [Finset.pair_comm x y]; exact key y x (lt_of_le_of_ne h (Ne.symm hxy))

theorem chain_card_le_three (S : SurfaceRank P) {s : Finset P} (hs : s ∈ (orderComplex P).faces) : s.card ≤ 3 := by
  classical
  have hinj : Set.InjOn S.rk (s : Set P) := fun a ha b hb hab =>
    (le_or_le_of_isChain hs ha hb).elim (fun h => S.rk_eq_of_le_of_rk_le h (le_of_eq hab.symm))
      fun h => (S.rk_eq_of_le_of_rk_le h (le_of_eq hab)).symm
  have hsub : s.image S.rk ⊆ ({0, 1, 2} : Finset ℕ) := fun n hn => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hn
    have := S.rk_le_two a; interval_cases S.rk a <;> simp
  exact (Finset.card_image_of_injOn hinj).symm.trans_le (Finset.card_le_card hsub)

theorem vertexInTriangle [DecidableEq P] (S : SurfaceRank P) (x : P) :
    ∃ s ∈ (orderComplex P).faces, s.card = 3 ∧ x ∈ s := by
  classical
  have mkTri {a b c : P} (hab : a < b) (hbc : b < c) :
      ({a, b, c} : Finset P) ∈ (orderComplex P).faces ∧ ({a, b, c} : Finset P).card = 3 := by
    have hac := hab.trans hbc
    refine ⟨by rw [mem_orderComplex]; simpa [Finset.coe_insert] using
      isChain_triple (.inl hab.le) (.inl hac.le) (.inl hbc.le), ?_⟩
    rw [Finset.card_insert_of_notMem (by simp [hab.ne, hac.ne]),
      Finset.card_insert_of_notMem (by simp [hbc.ne])]; rfl
  obtain ⟨f, hf, hxf⟩ := S.exists_face x
  rcases eq_or_lt_of_le hxf with rfl | hlt
  · obtain ⟨v, hv, hvf⟩ := S.exists_vertex x hf
    obtain ⟨e, -, -, ⟨hve, hef⟩, -, -⟩ := S.two_edges v x hv hf hvf
    exact ⟨{v, e, x}, (mkTri hve hef).1, (mkTri hve hef).2, by simp⟩
  · have hrx : S.rk x = 0 ∨ S.rk x = 1 := by have := S.rk_lt_of_lt hlt; omega
    rcases hrx with hrx | hrx
    · obtain ⟨e', -, -, ⟨hxe, he'f⟩, -, -⟩ := S.two_edges x f hrx hf hlt
      exact ⟨{x, e', f}, (mkTri hxe he'f).1, (mkTri hxe he'f).2, by simp⟩
    · obtain ⟨w, -, -, hwx, -, -⟩ := S.two_vertices x hrx
      exact ⟨{w, x, f}, (mkTri hwx hlt).1, (mkTri hwx hlt).2, by simp⟩

end SurfaceRank

def LinkAdj (v : P) (x y : P) : Prop := v < x ∧ v < y ∧ (x ≤ y ∨ y ≤ x)

def LinkConnected (S : SurfaceRank P) : Prop :=
  ∀ v : P, S.rk v = 0 → ∀ x y : P, v < x → v < y → Relation.ReflTransGen (LinkAdj v) x y

structure ClosedSurfacePoset (P : Type u) [PartialOrder P] where
  toSurfaceRank : SurfaceRank P
  link_connected : LinkConnected toSurfaceRank
