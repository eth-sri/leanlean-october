module

public import Chazelle.MacT
public import Chazelle.Core.TopIdx
public import Chazelle.Core.SpecNF
public import Chazelle.Chain.Submap
public import Mathlib.Data.Set.Finite.Lemmas

namespace Chazelle.Mountain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD)
open Chazelle.Existence (vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext lerp_mem_segment
  continuous_lerp)
variable {P : Polygon}

/-- A point of an edge different from both endpoints lies on the open edge. -/
theorem openEdgePt_of_mem_edge_ne {e : ℕ} {p : Point} (h : p ∈ P.edge e) (h1 : p ≠ P.vtx e)
    (h2 : p ≠ P.vtx ztwmy) : OpenEdgePt P e p := by
  obtain ⟨t, ht0, ht1, rfl⟩ := h
  refine ⟨t, ⟨lt_of_le_of_ne ht0 ?_, lt_of_le_of_ne ht1 ?_⟩, rfl⟩
  · grind
  grind
namespace TrapData

/-- The closed bottom side lies in the closed trapezoid. -/
theorem mem_closedTrap_bot (D : TrapData P) {x : ℝ}
    (h1 : edgeX P D.i D.y₁ ≤ x) (h2 : x ≤ edgeX P D.j D.y₁) :
    (ztbqn : Point) ∈ closedTrap P D.i D.j D.y₁ D.y₂ :=
  ⟨le_rfl, (D.isTrap.bot_lt.trans D.isTrap.lt_top).le, h1, h2⟩

/-- The closed top side lies in the closed trapezoid. -/
theorem mem_closedTrap_top (D : TrapData P) {x : ℝ}
    (h1 : edgeX P D.i D.y₂ ≤ x) (h2 : x ≤ edgeX P D.j D.y₂) :
    (ztbnt : Point) ∈ closedTrap P D.i D.j D.y₁ D.y₂ :=
  ⟨(D.isTrap.bot_lt.trans D.isTrap.lt_top).le, le_rfl, h1, h2⟩

/-- The segment from the bottom vertex to the top vertex is a piece segment. -/
theorem isPieceEdge_bot_top (D : TrapData P) : IsPieceEdge P D.bot D.top := by
  zucuo
  · exact Or.inr (Or.inr (Or.inr (Or.inl (D.diag_mem_trapDiagonals h))))
  tauto

/-- **From the bottom vertex to the top vertex.**  If the bottom vertex of `D` is the vertex at
position `k` of the piece and one cell of `D` is interior to the piece, then the top vertex is
a neighbour of position `k` in the piece. -/
theorem bot_top_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {k : ℕ}
    (hk : k < l.length) (hc : l.getD k 0 = D.bot)
    (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∨
      D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary) :
    P.vtx D.top = (subPoly P l).vtx ztwwk ∨
      P.vtx D.top = (subPoly P l).vtx ztwnc := by
  have hpe := D.isPieceEdge_bot_top
  have hpe' : IsPieceEdge P ztcak D.top := by_simp_all
  apply hl.nbr_of_boundary hP hk ztgdl hpe'
  zuhus
  zummy
  have hlerp : lerp ztsv ztsw s = lerp ztsw ztsv zteb := by
    zueky
  have hseg : lerp _ _ s ∈
      Chazelle.segment ztsv ztsw := lerp_mem_segment _ _ hs.1.le hs.2.le
  have hcl : lerp ztsv ztsw s ∈ closure D.cellL ∧
      lerp ztsv ztsw s ∈ closure D.cellR := by
    zugva
    zucuo
    · have hreg : lerp _ _ zteb ∈ D.region :=
        D.isTrap.diag_lerp_mem_trapSet hP D.free h.1 h.2 by_simp_all by_simp_all
      have hdet : det ztsv ztsw (lerp ztsw ztsv zteb) = 0 := by
        rw [Geometry.det_swap12, Geometry.det_eq_zero_of_mem_segment
          (lerp_mem_segment _ _ by_grind by_grind), neg_zero]
      exact D.mem_closure_cells_of_region hP hreg hdet
    · have hct : lerp _ _ zteb ∈ closedTrap P D.i D.j D.y₁ D.y₂ :=
        D.isTrap.diag_lerp_mem_closedTrap hP D.free by_grind by_grind
      exact ⟨D.mem_closure_cellL hP hct by_simp_all,
        D.mem_closure_cellR hP hct by_simp_all⟩
  rcases hS with hS | hS
  · exact hl.mem_boundary_of_closure hS ztmap ztgdl hpe hseg hcl.1
  · exact hl.mem_boundary_of_closure hS ztmap ztgdl hpe hseg hcl.2

/-- **Along the bottom side.**  If a vertex `c` of the closed bottom side of `D`, other than the
bottom vertex, is the vertex at position `k` of the piece and the left cell is interior to the
piece, then the next vertex `w` to the right on the bottom side is a neighbour of position `k`. -/
theorem bot_right_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {k : ℕ}
    (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hcS : c ∈ sideVtxSet P D.i D.j D.y₁)
    (hcb : c ≠ D.bot) (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary) :
    ∃ w, w ∈ sideVtxSet P D.i D.j D.y₁ ∧ (P.vtx c).1 < (P.vtx w).1 ∧
      (P.vtx w = (subPoly P l).vtx ztwwk ∨
        P.vtx w = (subPoly P l).vtx ztwnc) := by
  zuti

  have hkb : (P.vtx c).1 < (P.vtx D.bot).1 := by
    refine lt_of_le_of_ne by_simp_all (fun h => hcb ?_)
    exact simple_vtx_inj hP hcS.1 hbmem.1 (point_ext h (hcS.2.1.trans hbmem.2.1.symm))
  set S : Set ℕ := {j | j ∈ sideVtxSet P D.i D.j D.y₁ ∧ (P.vtx c).1 < (P.vtx j).1} with hSdef
  have hSfin : S.Finite := (sideVtxSet_finite P D.i D.j D.y₁).subset by_simp_all
  have hSne : S.Nonempty := ⟨D.bot, hbmem, hkb⟩
  zucxt

  have hres := gap_adjacent_or_chord hP ztp zthqw
    hcS.1 hmS.1.1 hcS.2.1 hmS.1.2.1 hmS.2
    (fun x hx1 hx2 => D.isTrap.near_bot ztgfm ztgfo)
    (fun j hj hjy hj1 hj2 => by
      zukcv
      grind)
  have hpe : ztulf := by
    tauto
  zuuh

  have hwb := hbmax w hmS.1
  have hp : lerp ztyg ztbup s =
      (((P.vtx c).1 + s * ztbli, D.y₁) : Point) := by
    zudtm
    simp_all
  zuhw
  have hx1 : (P.vtx c).1 ≤ (P.vtx c).1 + s * ztbli := by
    nlinarith [hs.1, hmS.2]
  have hx2 : (P.vtx c).1 + s * ztbli < (P.vtx w).1 := by
    zukka
  have hcl : lerp ztyg ztbup s ∈ closure D.cellL := by
    zugvh
    refine D.mem_closure_cellL hP (D.mem_closedTrap_bot ztgfm
      ztgfo) (fun _ => ?_)
    zudjr
    zudci

  zuhug

/-- **Along the top side.**  If a vertex `c` of the closed top side of `D` is the vertex at
position `k` of the piece, some vertex of the top side lies to its right, and the right cell is
interior to the piece, then the next vertex `w` to the right on the top side is a neighbour of
position `k`. -/
theorem top_right_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {k : ℕ}
    (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hcS : c ∈ sideVtxSet P D.i D.j D.y₂)
    (hex : ∃ j ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx c).1 < (P.vtx j).1)
    (hS : D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary) :
    ∃ w, w ∈ sideVtxSet P D.i D.j D.y₂ ∧ (P.vtx c).1 < (P.vtx w).1 ∧
      (P.vtx w = (subPoly P l).vtx ztwwk ∨
        P.vtx w = (subPoly P l).vtx ztwnc) := by
  zubpd
  zurq
  set S : Set ℕ := {j | j ∈ sideVtxSet P D.i D.j D.y₂ ∧ (P.vtx c).1 < (P.vtx j).1} with hSdef
  zuegp
  have hSne : S.Nonempty := by
    tauto
  zucxt

  have hres := gap_adjacent_or_chord hP ztbt zthqw
    hcS.1 hmS.1.1 hcS.2.1 hmS.1.2.1 hmS.2
    (fun x hx1 hx2 => D.isTrap.near_top ztgfm ztgfo)
    (fun j hj hjy hj1 hj2 => by
      zukcv
      grind)
  have hpe : ztulf := by
    tauto
  zuuh

  zukbm
  have hp : lerp ztyg ztbup s =
      (((P.vtx c).1 + s * ztbli, D.y₂) : Point) := by
    zudtm
    simp_all
  zuhw
  have hx1 : (P.vtx c).1 < (P.vtx c).1 + s * ztbli := by
    simp_all
  have hx2 : (P.vtx c).1 + s * ztbli ≤ (P.vtx w).1 := by
    zukka
  have hcl : lerp ztyg ztbup s ∈ closure D.cellR := by
    zugvh
    refine D.mem_closure_cellR hP (D.mem_closedTrap_top ztgfm
      ztgfo) (fun _ => ?_)
    zudjr
    zuesj
    nlinarith
  zuhug

/-- **Across the top side, left case.**  If the left cell of `D` is interior to the piece, the
left side edge of `D` is `e`, and the top vertex does not lie on `e`, then the open top side to
the left of the top vertex is a chord through the interior of the piece, and the trapezoid `D'`
above it has left side edge `e`, left cell interior to the piece, and the top vertex of `D` on
its closed bottom side. -/
theorem gap_left (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {e : ℕ}
    (he : e < P.n) (heq : D.i = e)
    (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary)
    (hnot : P.vtx D.top ∉ P.edge e) :
    ∃ D' : TrapData P, D'.i = e ∧
      D'.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧
      D.top ∈ sideVtxSet P D'.i D'.j D'.y₁ := by
  zubpd
  change D.top ∈ sideVtxSet P D.i D.j D.y₂ at htmem
  zurq
  have hNH := heq ▸ D.isTrap.nhL
  zuhw
  zulaa
  set a := edgeX P e y₂ with ha
  set b := (P.vtx D.top).1 with hb
  have hty := htmem.2.1
  have hab : ztmua := by
    refine lt_of_le_of_ne (by rw [ha, ← heq]; exact htmem.2.2.1) ztqnu
    zucqi
    exact D.isTrap.mem_edgeL by_grind (by rw [hty])
      by_simp_all
  have hbj := htmem.2.2.2
  have hnov : ztdji := by
    zukjp
    have hkS : ztgaw :=
      ⟨hk, hky, by_grind, by_linarith⟩
    grind
  have hE : OpenEdgePt P e ztnqu := by
    have hmem : (ztnqu : Point) ∈ P.edge e := by
      zucqi
      exact D.isTrap.mem_edgeL h12.le le_rfl by_simp_all
    have hnv : ∀ k, k < P.n → (ztnqu : Point) ≠ P.vtx k := by
      zujbh
      have h1 : (P.vtx k).1 = a := by_grind
      zujyl
      have hkS : ztgaw :=
        ⟨hk, h2, by_simp_all, by_grind⟩
      grind
    exact openEdgePt_of_mem_edge_ne hmem by_simp_all (hnv _ ztubk)
  have hgap := fun x (hx1 : a < x) (hx2 : x < b) =>
    D.gap_top hP by_simp_all hbj hnov he hNH (Or.inl hE) hx1 hx2
  have hint : ∀ x, a < x → x < b →
      (ztcxc : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary := by
    zuetl
    have hcl : (ztcxc : Point) ∈ closure D.cellL := by
      refine D.mem_closure_cellL hP (D.mem_closedTrap_top by_grind
        by_linarith) (fun _ => ?_)
      zudjr
      zubi
      nlinarith
    zubhw

    · grind
    grind
  obtain ⟨D', hy, ha', hb'⟩ := exists_trapData_above hP hab
    ztisw ztisv
  have hi' :=
    D'.i_eq_of_openEdgePt hP (a := a) by_grind by_grind he hNH
      by_grind
  have htS : D.top ∈ sideVtxSet P D'.i D'.j D'.y₁ :=
    ⟨htmem.1, by_grind, by_grind, by_grind⟩
  refine ⟨D', hi', ?_, htS⟩
  obtain ⟨-, hbmax⟩ := D'.isTrap.botVtx_spec hP D'.free
  have htb := hbmax D.top htS
  zuehj

  exact D'.cellL_subset_of_bot hP hl by_grind by_grind
    (by change ztth / 2 < (P.vtx (botVtx P D'.i D'.j D'.y₁)).1; linarith) hxi

/-- **Across the top side, right case.**  If the right cell of `D` is interior to the piece, the
right side edge of `D` is `e`, and `c` is the rightmost vertex of the closed top side and does not
lie on `e`, then the open top side to the right of `c` is a chord through the interior of the
piece, and the trapezoid `D'` above it has right side edge `e`, right cell interior to the piece,
and bottom vertex `c`. -/
theorem gap_right (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P) {e : ℕ}
    (he : e < P.n) (heq : D.j = e)
    (hS : D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary) {c : ℕ}
    (hcS : c ∈ sideVtxSet P D.i D.j D.y₂)
    (hmax : ∀ k ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx k).1 ≤ (P.vtx c).1)
    (hnot : P.vtx c ∉ P.edge e) :
    ∃ D' : TrapData P, D'.j = e ∧
      D'.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧ D'.bot = c := by
  zubpd
  zurq
  have hNH := heq ▸ D.isTrap.nhR
  zuhw
  zulaa
  set a := (P.vtx c).1 with ha
  set b := edgeX P e y₂ with hb
  have hcy := hcS.2.1
  have hab : ztmua := by
    refine lt_of_le_of_ne (by rw [hb, ← heq]; exact hcS.2.2.2) ztqnu
    zucqi
    exact D.isTrap.mem_edgeR by_grind (by rw [hcy])
      by_simp_all
  have hai := hcS.2.2.1
  have hnov : ztdji := by
    zukjp
    have hkS : ztgaw :=
      ⟨hk, hky, by_linarith, by_grind⟩
    grind
  have hbv : ∀ k, k < P.n → (ztnrr : Point) ≠ P.vtx k := by
    zujbh
    have h1 : (P.vtx k).1 = b := by_grind
    zujyl
    have hkS : ztgaw :=
      ⟨hk, h2, by_grind, by_simp_all⟩
    grind
  have hE : OpenEdgePt P e ztnrr := by
    have hmem : (ztnrr : Point) ∈ P.edge e := by
      zucqi
      exact D.isTrap.mem_edgeR h12.le le_rfl by_simp_all
    exact openEdgePt_of_mem_edge_ne hmem by_simp_all (hbv _ ztubk)
  have hgap := fun x (hx1 : a < x) (hx2 : x < b) =>
    D.gap_top hP hai by_simp_all hnov he hNH (Or.inr hE) hx1 hx2
  zukbm
  have hint : ∀ x, a < x → x < b →
      (ztcxc : Point) ∈ (subPoly P l).filled \ (subPoly P l).boundary := by
    zuetl
    have hcl : (ztcxc : Point) ∈ closure D.cellR := by
      refine D.mem_closure_cellR hP (D.mem_closedTrap_top by_linarith
        by_grind) (fun _ => ?_)
      zudjr
      zuesj
      zubi
      nlinarith
    zubhw

    · grind
    grind
  obtain ⟨D', hy, ha', hb'⟩ := exists_trapData_above hP hab
    ztisw ztisv
  have hj' :=
    D'.j_eq_of_openEdgePt hP (b := b) by_grind by_grind he hNH
      by_grind
  have hcS' : c ∈ sideVtxSet P D'.i D'.j D'.y₁ :=
    ⟨hcS.1, by_grind, by_grind, by_grind⟩
  obtain ⟨hbm, hbmax⟩ := D'.isTrap.botVtx_spec hP D'.free
  change D'.bot ∈ sideVtxSet P D'.i D'.j D'.y₁ at hbm
  change ∀ k ∈ sideVtxSet P D'.i D'.j D'.y₁, (P.vtx k).1 ≤ (P.vtx D'.bot).1 at hbmax
  have hcb := hbmax c hcS'
  have hbot : D'.bot = c := by
    have hby : (P.vtx D'.bot).2 = y₂ := by rw [hbm.2.1, hy]
    have hbj : (P.vtx D'.bot).1 ≤ b := by
      have := hbm.2.2.2; grind
    have hba : (P.vtx D'.bot).1 = a := by
      zuct
      have hlt : a < (P.vtx D'.bot).1 := by_grind
      rcases hbj.lt_or_eq with h | h
      · exact hnov _ hbm.1 hby hlt h
      · exact hbv _ hbm.1 by_grind
    exact simple_vtx_inj hP hbm.1 hcS.1 by_grind
  refine ⟨D', hj', ?_, hbot⟩
  zuehj

  exact D'.cellR_subset_of_bot hP hl by_grind by_grind
    by_grind hxi
end TrapData

/-! ### The walk states -/

/-- **Left state** of the walk at vertex `c` with base edge `e`: some trapezoid has left side
edge `e`, its left cell interior to the piece, and `c` on its closed bottom side or as its top
vertex. -/
def StateL (P : Polygon) (l : List ℕ) (e c : ℕ) : Prop :=
  ∃ D : TrapData P, D.i = e ∧ D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧
    (c ∈ sideVtxSet P D.i D.j D.y₁ ∨ c = D.top)

/-- **Right state** of the walk at vertex `c` with base edge `e`: some trapezoid has right side
edge `e`, its right cell interior to the piece, and `c` as its bottom vertex or on its closed top
side. -/
def StateR (P : Polygon) (l : List ℕ) (e c : ℕ) : Prop :=
  ∃ D : TrapData P, D.j = e ∧ D.cellR ⊆ (subPoly P l).filled \ (subPoly P l).boundary ∧
    (c = D.bot ∨ c ∈ sideVtxSet P D.i D.j D.y₂)

/-- The left step from a vertex of the closed bottom side. -/
theorem stateL_step_bot (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (D : TrapData P)
    {e : ℕ} (heq : D.i = e) (hS : D.cellL ⊆ (subPoly P l).filled \ (subPoly P l).boundary)
    {k : ℕ} (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c)
    (hcS : c ∈ sideVtxSet P D.i D.j D.y₁) :
    ∃ w, w < P.n ∧ StateL P l e w ∧ ylexLT ztyg ztbup ∧
      (P.vtx w = (subPoly P l).vtx ztwwk ∨
        P.vtx w = (subPoly P l).vtx ztwnc) := by
  by_cases hcb : c = D.bot
  · refine ⟨D.top, D.top_lt hP, ⟨D, heq, hS, Or.inr rfl⟩, ?_,
      D.bot_top_nbr hP hl hk (hc.trans hcb) ztvbw⟩
    apply ylexLT_of_snd_lt
    rw [hcS.2.1, D.top_snd hP]
    exact D.isTrap.bot_lt.trans D.isTrap.lt_top
  · obtain ⟨w, hw, hcw, hnb⟩ := D.bot_right_nbr hP hl hk hc hcS hcb hS
    exact ⟨w, hw.1, ⟨D, heq, hS, Or.inl hw⟩, Or.inr ztryw, hnb⟩

/-- **The left step.**  A vertex of the piece in the left state, not on the base edge, has a
neighbour in the piece which is strictly `ylexLT`-above it and again in the left state. -/
theorem StateL.step (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {e : ℕ} (he : e < P.n)
    {k : ℕ} (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hst : StateL P l e c)
    (hnot : P.vtx c ∉ P.edge e) :
    ∃ w, w < P.n ∧ StateL P l e w ∧ ylexLT ztyg ztbup ∧
      (P.vtx w = (subPoly P l).vtx ztwwk ∨
        P.vtx w = (subPoly P l).vtx ztwnc) := by
  zufim
  rcases hc' with hcS | rfl
  · exact stateL_step_bot hP hl D heq hS hk hc hcS
  · obtain ⟨D', hi', hS', htS⟩ := D.gap_left hP hl he heq hS hnot
    exact stateL_step_bot hP hl D' hi' hS' hk hc htS

/-- **The right step.**  A vertex of the piece in the right state, not on the base edge, has a
neighbour in the piece which is strictly `ylexLT`-above it and again in the right state. -/
theorem StateR.step (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {e : ℕ} (he : e < P.n)
    {k : ℕ} (hk : k < l.length) {c : ℕ} (hc : l.getD k 0 = c) (hst : StateR P l e c)
    (hnot : P.vtx c ∉ P.edge e) :
    ∃ w, w < P.n ∧ StateR P l e w ∧ ylexLT ztyg ztbup ∧
      (P.vtx w = (subPoly P l).vtx ztwwk ∨
        P.vtx w = (subPoly P l).vtx ztwnc) := by
  zufim
  rcases hc' with rfl | hcS
  · refine ⟨D.top, D.top_lt hP, ⟨D, heq, hS, Or.inr (D.isTrap.topVtx_mem hP D.free)⟩, ?_,
      D.bot_top_nbr hP hl hk hc (Or.inr hS)⟩
    exact ylexLT_of_snd_lt ztuxp
  · by_cases hex : ∃ j ∈ sideVtxSet P D.i D.j D.y₂, (P.vtx c).1 < (P.vtx j).1
    · obtain ⟨w, hw, hcw, hnb⟩ := D.top_right_nbr hP hl hk hc hcS hex hS
      exact ⟨w, hw.1, ⟨D, heq, hS, Or.inr hw⟩, Or.inr ztryw, hnb⟩
    · zumim
      obtain ⟨D', hj', hS', hbot⟩ := D.gap_right hP hl he heq hS hcS hex hnot
      refine ⟨D'.top, D'.top_lt hP, ⟨D', hj', hS', Or.inr (D'.isTrap.topVtx_mem hP D'.free)⟩, ?_,
        D'.bot_top_nbr hP hl hk (hc.trans hbot.symm) (Or.inr hS')⟩
      rw [← hbot]
      exact ylexLT_of_snd_lt (D'.bot_snd_lt_top_snd hP)
end
end Chazelle.Mountain
section
set_option hygiene false
local macro "zqrw" : tactic => `(tactic| (rw [hf0]; refine hmin _ ztqqa ztep; have := hfinj 1 0 by_omega by_omega (h.trans hf0.symm)))
local macro "zqrx" : tactic => `(tactic| (rw [mem_ball_iff_abs]; zunra))
local macro "zqry" : tactic => `(tactic| have := hfinj k 0 by_omega by_omega ((hl.getD_inj zthya hml h).trans hf0.symm))
local macro "zqrz" : tactic => `(tactic| apply hfeq _ _ zthbs)
local macro "zqsa" : tactic => `(tactic| set Q := subPoly P l with hQdef)
local macro "zqsb" : tactic => `(tactic| refine hstep _ zthya ztep ztep hSk)
local macro "zqsc" : tactic => `(tactic| (have e := h.trans ha.symm; zvmwe at hcw; exact absurd hcw (ylexLT_asymm hlt)))
local macro "zqsd" : tactic => `(tactic| have hf : ∀ k, f k < N := fun k => Nat.mod_lt _ hN0)
local macro "zqse" : tactic => `(tactic| (intro c' hc' hmem'; rcases (simple_vtx_mem_edge_iff hP hc' hgn).1 hmem' with h | h))
set_option hygiene true

/-!
# The mountain decomposition theorem

Let `P` be a simple polygon and `l` a piece of the subdivision of `P` by the inserted diagonals
`allDiagonals P` (`IsPiece P l`, `Chazelle.Mountain.Pieces`).  We prove that the piece
`Q = subPoly P l` is a **monotone mountain** (`piece_isMonoAt`): for some position `a`, the
vertices of `Q` read cyclically from position `a + 1` to position `a` are strictly
`ylexLT`-monotone, so the edge `a` of `Q` joins the maximum to the minimum and the other chain is
monotone.

## Proof

Let `m` be the position of the `ylexLT`-lowest vertex `v` of `Q`.

1. **Initial analysis** (`piece_initial`).  Near `v` the interior of `Q` lies above `v`
   (`IsPiece.locMin_lower_exterior`); pick a free point `p` of `P` in the interior of `Q` just
   above `v`, with trapezoid `D`, so that `v` is on the closed bottom side of `D` and the segment
   from `p` to `v` stays in the interior of `Q`.  A case analysis (the cell of `D` containing `p`,
   the position of `v` on the bottom side, the diagonal of `D`) shows that `v` is the lower
   endpoint of a side edge `e` of `D` whose upper endpoint `u` is a neighbour of `v` in `Q` — the
   future **base** — and that the other neighbour `w` of `v` in `Q` is in the left or right walk
   state of `Chazelle.Mountain.PieceSteps` with respect to `e`.  (Points of the bottom side just
   to the left of `v` are `ylexLT`-below `v`; if they were in the piece, an edge of `Q` would leave
   `v` to the left, below `v`.  Points of the bottom side just to the right of `v`, when `v` is the
   bottom vertex, would force an edge of `Q` along the bottom side to a vertex to the right of the
   rightmost bottom vertex.)
2. **The walk** (`walk_chain`, `mono_of_walk`).  Walking along `Q` from `v` away from `u`, each
   vertex other than `u` is in the walk state and not on `e` (the only vertices on `e` are `v` and
   `u`), so its next neighbour is strictly `ylexLT`-higher (`StateL.step`, `StateR.step`).  Hence
   the chain from `v` around to `u` is strictly increasing: `Q` is a monotone mountain with base
   `u v`.

## Main results

* `piece_isMonoAt`: `IsPiece P l → ∃ a < l.length, IsMonoAt (subPoly P l) a`.
* `piece_isMountainAt`: `IsPiece P l → ∃ a < l.length,
    IsMountainAt (subPoly P l) a ∨ IsMountainAt (subPoly P l.reverse) a`.
* `piece_isMountain` (the form used by the stack algorithm of `Chazelle.Mountain.Stack`):
  `IsPiece P l → ∃ s, IsMountain ((subPoly P l).rotate s) ∨
    IsMountain ((subPoly P l.reverse).rotate s)`.
* Reversal: `simple_subPoly_reverse`, `boundary_subPoly_reverse`, `filled_subPoly_reverse`,
  `vtx_subPoly_reverse` (the reversed piece is simple, with the same boundary and filled region;
  generic versions `rev_simple`, `rev_boundary`, `rev_filled`, `rev_chainInc`).
-/
namespace Chazelle.Mountain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD)
open Chazelle.Existence (vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext lerp_mem_segment
  continuous_lerp)
variable {P : Polygon}

/-! ### Geometric helpers -/

/-- If a point `z` at the height of `v` but different from `v` lies on the segment from `v` to
`a`, then `a` is at the height of `v`, on the same side of `v` as `z`. -/
theorem ray_nbr {v a z : Point} (hz2 : z.2 = v.2) (hz1 : z.1 ≠ v.1)
    (h : z ∈ Chazelle.segment v a) : a.2 = v.2 ∧ 0 < ztokm * ztcts := by
  obtain ⟨t, ht0, ht1, he⟩ := h
  have e1 : z.1 - v.1 = t * ztcts := by
    simp_all
  have e2 : t * ztclz = 0 := by
    simp_all
  have ht : ztmwx := by
    simp_all
  have ha : ztsdj := by
    simp_all
  zujx
  · grind
  · have htpos : ztfkp := by_grind
    rw [e1, mul_assoc]
    simp_all

/-- **Segments to a vertex.**  Around a vertex `v` of a simple polygon there is a ball such that
for every interior point `p` in it, the half-open segment from `p` to `v` is interior. -/
theorem exists_ball_lerp_interior {Q : Polygon} (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n) :
    ∃ r > 0, ∀ p ∈ ball ztbda r, p ∈ Q.filled \ Q.boundary →
      ∀ s ∈ Ico (0 : ℝ) 1, lerp p ztbda s ∈ Q.filled \ Q.boundary := by
  zuerp
  set v := Q.vtx k with hv
  set a := Q.vtx ztkck with ha
  set b := Q.vtx (zts % Q.n) with hb
  obtain ⟨r₁, hr₁, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hk
  have hav :=
    dist_pos.2 (simple_vtx_ne hQ ztkcm hk ztrul)
  have hbv := dist_pos.2 (simple_vtx_succ_ne hQ hk).symm
  set r := min r₁ (min zttiz zttja) with hr
  zufwe
  refine ⟨r, hr0, fun p hp hpi => ?_⟩
  zukey
  set S := lerp p v '' Ico (0 : ℝ) 1 with hS
  have hSball : ztscl := by
    zupc
    zugca

  have hSb : ∀ x ∈ S, x ∉ Q.boundary := by
    zugtf
    have hx := hSball ztbik
    rcases hball _ ztzve hxb with h | h
    · zudto
      zuieq
      · apply hpi.2
        refine ⟨prevIdx Q k, prevIdx_lt Q hk, ?_⟩
        rw [edge_prevIdx Q hk, Geometry.segment_comm]
        zuclh
      · have : ztslq := (min_le_right _ _).trans ztff
        linarith
    · zuieq
      · exact hpi.2 ⟨k, hk, h'⟩
      · have : ztslr := (min_le_right _ _).trans ztgh
        linarith
  have hSc : ztulh :=
    isPreconnected_Ico.image _ (continuous_lerp p v).continuousOn
  have hpS : p ∈ S := ⟨0, by_grind, lerp_zero p v⟩
  zugg
  exact subset_interior_of_isPreconnected hQ hSc hSb hpS hpi by_grind
namespace TrapData

/-- Without inserted diagonal, the two cells are the whole region. -/
theorem cellL_eq_cellR (D : TrapData P) (h : ¬ D.NonAdj) : D.cellL = D.cellR := by
  zufj
  exact ⟨fun hp => ztuhu, fun hp => ztuhu⟩

/-- A point of the open left side edge is in the closure of the left cell. -/
theorem left_side_mem_closure (hP : P.Simple) (D : TrapData P) {h : ℝ} (h1 : D.y₁ < h)
    (h2 : h < D.y₂) : (ztpas : Point) ∈ closure D.cellL :=
  D.mem_closure_cellL hP ⟨h1.le, h2.le, le_rfl, (D.isTrap.edgeX_lt hP D.free h1 h2).le⟩
    (fun hna => (D.det_side hP hna h1 h2).1)

/-- A point of the open right side edge is in the closure of the right cell. -/
theorem right_side_mem_closure (hP : P.Simple) (D : TrapData P) {h : ℝ} (h1 : D.y₁ < h)
    (h2 : h < D.y₂) : (ztpau : Point) ∈ closure D.cellR :=
  D.mem_closure_cellR hP ⟨h1.le, h2.le, (D.isTrap.edgeX_lt hP D.free h1 h2).le, le_rfl⟩
    (fun hna => (D.det_side hP hna h1 h2).2)
end TrapData

/-- The points of an edge issued from its lower endpoint, just above that endpoint, are the
points of the line of the edge at heights just above. -/
theorem edge_pts_eventually {g c u : ℕ} (hNH : NonHoriz P g)
    (hseg : Chazelle.segment ztyg ztenr = P.edge g) {y₁ y₂ : ℝ}
    (hcy : (P.vtx c).2 = y₁) (h12 : y₁ < y₂) (hu2 : y₂ ≤ (P.vtx u).2) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ h, y₁ < h ∧ h < y₂ ∧
      lerp ztyg ztenr s = (ztpaw : Point) := by
  have hd : 0 < (P.vtx u).2 - y₁ := by_linarith
  set s₀ := (y₂ - y₁) / zteis with hs₀def
  have hs₀ : ztphv := by_simp_all
  have hs₀1 : s₀ ≤ 1 := (div_le_one hd).2 by_linarith
  filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
  have hsd : s * zteis < y₂ - y₁ := by
    have := (lt_div_iff₀ hd).1 hs.2; linarith
  have h2 : (lerp ztyg ztenr s).2 = y₁ + s * zteis := by
    simp_all
  refine ⟨y₁ + s * zteis, by_simp_all, by_linarith, ?_⟩
  have hmem : lerp ztyg ztenr s ∈ P.edge g := by
    rw [← hseg]; exact lerp_mem_segment _ _ hs.1.le by_grind
  have hx := ((mem_edge_iff_edgeX hNH).1 hmem).2
  grind
namespace TrapData

/-- **A vertex at a bottom corner.**  If the vertex `c` lies at the bottom end of the side edge `g`
(`g` is the left or the right side edge of `D`), then `c` is the lower endpoint of `g`; the other
endpoint `u` is adjacent to `c`, the only vertices on `g` are `c` and `u`, and just above `c` the
points of `g` are the points of the open side of the trapezoid. -/
theorem corner_edge (hP : P.Simple) (D : TrapData P) {c g : ℕ} (hc : c < P.n)
    (hg : g = D.i ∨ g = D.j) (hcy : (P.vtx c).2 = D.y₁) (hcx : (P.vtx c).1 = edgeX P g D.y₁) :
    ∃ u, u < P.n ∧ (u = zthga % P.n ∨ c = ztcol % P.n) ∧
      Chazelle.segment ztyg ztenr = P.edge g ∧
      (∀ c', c' < P.n → P.vtx c' ∈ P.edge g → c' = c ∨ c' = u) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ h, D.y₁ < h ∧ h < D.y₂ ∧
        lerp ztyg ztenr s = (ztpaw : Point) := by
  obtain ⟨hgn, hNH, hbot, htop⟩ :
      g < P.n ∧ NonHoriz P g ∧ edgeBot P g ≤ D.y₁ ∧ D.y₂ ≤ edgeTop P g := by
    rcases hg with rfl | rfl
    · exact ⟨D.isTrap.hi, D.isTrap.nhL, D.isTrap.botL, D.isTrap.topL⟩
    · exact ⟨D.isTrap.hj, D.isTrap.nhR, D.isTrap.botR, D.isTrap.topR⟩
  zuhw
  have hmem : P.vtx c ∈ P.edge g :=
    (mem_edge_iff_edgeX hNH).2 by_grind
  -- the height of the other endpoint
  have hu2of : ∀ u : ℕ, edgeTop P g = max (P.vtx c).2 (P.vtx u).2 → D.y₂ ≤ (P.vtx u).2 := by
    grind
  rcases (simple_vtx_mem_edge_iff hP hc hgn).1 hmem with hgc | hgc
  · -- `g = c`
    have hseg : Chazelle.segment ztyg (P.vtx (zthga % P.n)) = P.edge g := by
      zuohd; rfl
    have hu2 : ztpjd := hu2of _ by_tauto
    refine ⟨zthga % P.n, succIdx_lt P hc, Or.inl rfl, hseg, ?_,
      edge_pts_eventually hNH hseg hcy h12 hu2⟩
    zqse
    · omega
    · right; rw [← prevIdx_succ P hc', ← h, hgc]
  · -- `g = prevIdx c`
    have hseg : Chazelle.segment ztyg (P.vtx (prevIdx P c)) = P.edge g := by
      zuohd; unfold Polygon.edge; rw [prevIdx_succ P hc, Geometry.segment_comm]
    have hu2 : ztpjd := hu2of _ (by
      zuohd; unfold edgeTop; rw [prevIdx_succ P hc, max_comm])
    refine ⟨prevIdx P c, by_omega, Or.inr (prevIdx_succ P hc).symm, hseg, ?_,
      edge_pts_eventually hNH hseg hcy h12 hu2⟩
    zqse
    · omega
    · left; rw [← prevIdx_succ P hc', ← h, hgc, prevIdx_succ P hc]
end TrapData

/-- **Recognising the base.**  If `u` is adjacent in `P` to the vertex at position `m` of the
piece and the points of the edge between them near that vertex are in the closure of a set of
interior points of the piece, then `u` is a neighbour of position `m` in the piece. -/
theorem IsPiece.base_nbr (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {m : ℕ}
    (hml : m < l.length) {u : ℕ} (hu : u < P.n)
    (hadj : u = (l.getD m 0 + 1) % P.n ∨ l.getD m 0 = ztcol % P.n) {S : Set Point}
    (hS : S ⊆ (subPoly P l).filled \ (subPoly P l).boundary)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp (P.vtx (l.getD m 0)) ztenr s ∈ closure S) :
    P.vtx u = (subPoly P l).vtx ztxli ∨
      P.vtx u = (subPoly P l).vtx ztxll := by
  have hpe : IsPieceEdge P _ u := hadj.elim Or.inl ztzex
  apply hl.nbr_of_boundary hP hml hu hpe
  filter_upwards [hev, Ioo_mem_nhdsGT ztja] with s hs hs'
  exact hl.mem_boundary_of_closure hS (hl.getD_lt hml) hu hpe
    (lerp_mem_segment _ _ hs'.1.le hs'.2.le) hs

/-- A small positive number below three positive bounds. -/
theorem exists_small_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ ε, 0 < ε ∧ ε ≤ a ∧ ε < b ∧ ε < c := by
  refine ⟨min a (min b c) / 2, by_positivity, ?_, ?_, ?_⟩
  · grind
  · grind
  grind

/-- **Initial analysis at the lowest vertex of a piece.**  Let `m` be the position of the
`ylexLT`-lowest vertex of the piece `Q = subPoly P l`.  There are an edge `e` of `P` whose only
vertices are `l.getD m 0` and `uP`, where `P.vtx uP` is a neighbour of position `m` in `Q` (the
base), and a vertex `w` which is the other neighbour of position `m` in `Q` and is in the left or
the right walk state for `e`. -/
theorem piece_initial (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {m : ℕ}
    (hm : IsLocMin ztdi m)
    (hmin : ∀ j < (subPoly P l).n, j ≠ m → ylexLT ztmzu ztmzt) :
    ∃ e uP w, e < P.n ∧ uP < P.n ∧ w < P.n ∧
      (∀ c, c < P.n → P.vtx c ∈ P.edge e → c = l.getD m 0 ∨ c = uP) ∧
      (P.vtx uP = (subPoly P l).vtx ztxli ∨
        P.vtx uP = (subPoly P l).vtx ztxll) ∧
      (P.vtx w = (subPoly P l).vtx ztxli ∨
        P.vtx w = (subPoly P l).vtx ztxll) ∧
      P.vtx w ≠ P.vtx uP ∧ (StateL P l e w ∨ StateR P l e w) := by
  zqsa
  zueqo
  zudnu
  have hmQ := hm.1
  have hml : m < l.length := by_omega
  have hmP := hl.getD_lt hml
  set mP := l.getD m 0 with hmPdef
  set v := P.vtx mP with hvdef
  have hvm : Q.vtx m = v := IsPiece.vtx_eq hml
  zueru
  have hQn' : ztbl % Q.n = ztbl % l.length := by zvmxg
  have hprevl := hQn ▸ prevIdx_lt Q hmQ
  have hnextl : ztbl % l.length < l.length := Nat.mod_lt _ by_omega
  -- the two neighbours are strictly above `v`
  have hnb : ∀ j, ztxxn → ylexLT v zthrw := by
    rintro j (rfl | rfl)
    · zuotk; exact hmin _ by_omega (prevIdx_ne Q hn3 hmQ)
    · rw [← hvm, ← hQn']
      exact hmin _ by_omega (succIdx_ne Q hn3 hmQ)
  -- radii
  obtain ⟨rL, hrL, hLE⟩ := hl.locMin_lower_exterior hP hm
  obtain ⟨rB, hrB, hB⟩ := Chazelle.Existence.boundary_near_vtx hQ hmQ
  obtain ⟨rS, hrS, hSeg⟩ := exists_ball_lerp_interior hQ hmQ
  obtain ⟨rT, hrT, hTr⟩ := exists_ball_vtx_trapData hP hmP
  rw [hvm] at hLE hB hSeg
  rw [hQn'] at hB
  -- a boundary point on a horizontal ray from `v` lies on an edge of `Q` at `v`
  have hray : ∀ z : Point, z ∈ ball v rB → z ∈ Q.boundary → z.2 = v.2 → z.1 ≠ v.1 →
      ∃ j, ztxxn ∧ (Q.vtx j).2 = v.2 ∧
        0 < ztokm * ((Q.vtx j).1 - v.1) := by
    intro z hz hzb hz2 hz1
    rcases hB z hz hzb with h | h
    · zudto
      exact ⟨_, Or.inl rfl, ray_nbr hz2 hz1 h⟩
    · exact ⟨_, Or.inr rfl, ray_nbr hz2 hz1 h⟩
  -- the left ray from `v` is not in the piece
  have hleft : ∀ ε, 0 < ε → ε < rL → ε < rB → (ztewg : Point) ∈ Q.filled → False := by
    intro ε hε h1 h2 hz
    have hzL : (ztewg : Point) ∈ ball v rL := by
      zqrx
      exact ⟨by zuotl; exact h1, hrL⟩
    have hzB : (ztewg : Point) ∈ ball v rB := by
      zqrx
      exact ⟨by zuotl; exact h2, hrB⟩
    have hlt : ylexLT (ztewg : Point) v := Or.inr by_grind
    have hzb : (ztewg : Point) ∈ Q.boundary := by
      zumv
      exact hLE _ hzL hlt ⟨hz, h⟩
    obtain ⟨j, hj, hj2, hj1⟩ := hray _ hzB hzb rfl by_grind
    have hjlt : (Q.vtx j).1 < v.1 := by
      simp only [sub_sub_cancel_left] at hj1; nlinarith
    exact ylexLT_asymm (hnb j hj) ztbmd
  -- an interior point near `v`, above `v`
  set r := min (min rL rB) (min rS rT) with hr
  have hr0 := lt_min (lt_min hrL hrB) (lt_min hrS hrT)
  have hrL' : r ≤ rL := (min_le_left _ _).trans ztff
  have hrS' : r ≤ rS := (min_le_right _ _).trans ztff
  have hrT' : r ≤ rT := (min_le_right _ _).trans ztgh
  have hvb : v ∈ Q.boundary := by zuotk; exact vtx_mem_boundary Q hmQ
  obtain ⟨z, hzi, hzd⟩ :=
    Metric.mem_closure_iff.1 (boundary_subset_closure_interior hQ hvb) r hr0
  have hzball : z ∈ ball v r := by zunop; omega
  have hvz : ylexLT v z := by
    rcases ylexLT_trichotomy z v with h | h | h
    · exact absurd hzi (hLE z (ball_subset_ball hrL' hzball) h)
    · exact absurd by_grind hzi.2
    omega
  -- a free point of `P` above `v`, and its trapezoid
  have hUo : IsOpen (ball v r ∩ ztrx) :=
    isOpen_ball.inter ztvxk
  obtain ⟨p, ⟨hpb, hpi⟩, hpf, -, hp2⟩ :=
    exists_free_of_isOpen hP hUo ⟨hzball, hzi⟩ (hl.interior_subset hzi)
  have hvp : v.2 < p.2 := by
    rcases hvz with h | ⟨h, -⟩ <;> linarith
  obtain ⟨D, -, hpD, hvD, -⟩ := hTr p (ball_subset_ball hrT' hpb) hpf
  have hmS := D.mem_bot_of_lt hmP hvD hpD hvp
  have hvc := closure_trapSet_subset _ _ _ _ _ hvD
  have hseg : ∀ s ∈ Ico (0 : ℝ) 1,
      lerp p v s ∈ Q.filled \ Q.boundary ∧ lerp p v s ∈ D.region := by
    zugg
    refine ⟨hSeg p (ball_subset_ball hrS' hpb) hpi s hs, ?_⟩
    have e : lerp p v s = lerp v p zteb := by
      zueky
    zui
    exact lerp_mem_trapSet hvc hpD (by zunui) ztjpx
  -- common facts
  zuhw
  have hvy : v.2 = D.y₁ := hmS.2.1
  have hvi := hmS.2.2.1
  have hvj := hmS.2.2.2
  zuti

  have hvbx := hbmax mP hmS
  have hfilled : ∀ {S : Set Point}, S ⊆ Q.filled \ Q.boundary → ∀ {x : Point},
      x ∈ closure S → x ∈ Q.filled :=
    fun hS _ hx => (isClosed_filled _).closure_subset (closure_mono (fun y hy => (hS hy).1) hx)
  -- the right ray from `v`, when `v` is the bottom vertex
  have hright : mP = D.bot → v.1 < edgeX P D.j D.y₁ →
      (∀ ε, 0 < ε → ε ≤ edgeX P D.j D.y₁ - v.1 → (ztdpv : Point) ∈ Q.filled) →
      False := by
    intro hmb hvlt hfill
    obtain ⟨ε, hε0, hε1, hεL, hεB⟩ := exists_small_pos (by linarith : 0 < edgeX P D.j D.y₁ - v.1)
      hrL hrB
    have hzf := hfill ε hε0 hε1
    have hzL : (ztdpv : Point) ∈ ball v rL := by
      zucjy
      zufpo
      exact ⟨by zunxi; omega, hrL⟩
    have hzB : (ztdpv : Point) ∈ ball v rB := by
      zucjy
      zufpo
      exact ⟨by zunxi; omega, hrB⟩
    have hznot : (ztdpv : Point) ∉ Q.filled \ Q.boundary := by
      intro hzi'
      obtain ⟨ρ, hρ, hρs⟩ :=
        Metric.isOpen_iff.1 ztvxk _ hzi'
      set δ := min ρ rL / 2 with hδ
      zukhr
      have hδρ : δ < ρ := by have := min_le_left ρ rL; linarith
      have hδL : δ < rL := by have := min_le_right ρ rL; linarith
      have h1 : (ztojj : Point) ∈ ball (ztdpv : Point) ρ := by
        zqrx
        exact ⟨hρ, by rw [abs_of_pos hδ0]; omega⟩
      have h2 : (ztojj : Point) ∈ ball v rL := by
        zucjy
        simp only [add_sub_cancel_left, ← hvy]
        refine ⟨by zunxi; omega, ?_⟩
        rw [show v.2 - δ - v.2 = -δ by ring, abs_neg, abs_of_pos hδ0]; omega
      exact hLE _ h2 ztzz (hρs h1)
    have hzb : (ztdpv : Point) ∈ Q.boundary := by
      zumv
      exact hznot ⟨hzf, h⟩
    obtain ⟨j, hj, hj2, hj1⟩ := hray _ hzB hzb by_grind
      by_grind
    have hja : v.1 < (Q.vtx j).1 := by
      simp only [add_sub_cancel_left] at hj1; nlinarith
    have hjl : j < l.length := by
      omega
    have haP := hl.getD_lt hjl
    have hjv : ztscg := IsPiece.vtx_eq hjl
    rw [hjv] at hj2 hja
    have hpe : IsPieceEdge P mP ztjzv := by
      zudsf
      · have h := hl.edge_at hprevl
        have hs : (prevIdx Q m + 1) % l.length = m := by
          have := prevIdx_succ Q hmQ; grind
        zukwa
        exact h.symm
      · exact hl.edge_at hml
    have hax : (P.vtx ztjzv).1 ≤ edgeX P D.j D.y₁ := by
      zuum

      have hs₀ : (ztfhf : Point) ∈ Chazelle.segment v _ :=
        horiz_mem_segment hvy (hj2.trans hvy) (min_le_of_left_le hvj)
          (le_max_of_le_right hgt.le)
      have hs₀e : (ztfhf : Point) ∈ P.edge D.j :=
        D.isTrap.mem_edgeR le_rfl h12.le rfl
      have hs₀v : (ztfhf : Point) ≠ v := by_grind
      have hs₀a : (ztfhf : Point) ≠ P.vtx ztjzv := by_grind
      rcases hpe.edge_of_mem_boundary hP hmP haP hs₀ hs₀v hs₀a D.isTrap.hj hs₀e with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply D.isTrap.nhR
        grind
      · apply D.isTrap.nhR
        grind
    have haS : l.getD j 0 ∈ sideVtxSet P D.i D.j D.y₁ :=
      ⟨haP, hj2.trans hvy, by_linarith, hax⟩
    have := hbmax _ haS
    grind
  -- the cell of `D` containing `p`
  have hcase : (D.NonAdj ∧ det ztsv ztsw p < 0) ∨ p ∈ D.cellL := by
    zuirs
    · rcases lt_trichotomy (det ztsv ztsw p) 0 with h | h | h
      · grind
      · exfalso
        exact hl.not_diag _ ztjkp p
          ztmds (D.mem_diagSeg_of_det hP hpD h)
      · exact Or.inr ztoon
    · exact Or.inr ztoon
  rcases hcase with ⟨hna, hneg⟩ | hpL
  · -- `p` is right of the diagonal: the base is the right side edge
    have hSR := D.cellR_subset_intQ hP hl ztoon hpi
    have hmb : mP = D.bot := by
      zuct
      have hvlt := lt_of_le_of_ne hvbx (fun h => hne
        (simple_vtx_inj hP hmP hbmem.1 (point_ext h (hvy.trans hbmem.2.1.symm))))
      have hdv : 0 < det ztsv ztsw v := by
        rw [D.det_bot_top hP, hvy]; zunxh; nlinarith
      set dp := det _ _ p with hdp
      set dv := det _ _ v with hdv'
      have hden : dp - dv < 0 := by_linarith
      have hs0 := div_pos_of_neg_of_neg hneg hden
      have hs1 : dp / zttje < 1 := (div_lt_one_of_neg hden).2 by_linarith
      have hdet0 : det ztsv ztsw (lerp p v (dp / zttje)) = 0 := by
        rw [Geometry.det_lerp, ← hdp, ← hdv']
        have hne := ne_of_lt hden
        grind
      obtain ⟨hz1, hz2⟩ := hseg _ ⟨hs0.le, hs1⟩
      exact hl.not_diag _ ztjkp _
        ztmds (D.mem_diagSeg_of_det hP hz2 hdet0)
    have hvcorner : ztrhe := by
      zuct
      zuhru

      apply hfilled hSR
      refine D.mem_closure_cellR hP ztnkk
        ztrpp
      rw [D.det_bot_top hP, ← hmb]
      zudci

    obtain ⟨u, hu, hadj, -, hon, hev⟩ := D.corner_edge hP hmP ztbt hvy hvcorner
    have hunbr := hl.base_nbr hP hml hu hadj hSR (hev.mono fun s ⟨h, h1, h2, he⟩ => by
      zvmxm; exact D.right_side_mem_closure hP h1 h2)
    have hwnbr := D.bot_top_nbr hP hl hml hmb (Or.inr hSR)
    refine ⟨D.j, u, D.top, D.isTrap.hj, hu, D.top_lt hP, hon, hunbr, hwnbr, ?_,
      Or.inr ztiwa⟩
    zuq
    have htu := simple_vtx_inj hP ztgdl hu h
    rcases hadj with h' | h'
    · exact hna.2 by_grind
    · exact hna.1 by_grind
  · -- `p` is in the left cell: the base is the left side edge (or the right one)
    have hSL := D.cellL_subset_intQ hP hl hpL hpi
    have hvcornerL : v.1 = edgeX P D.i D.y₁ := by
      zuct
      have hvlt : edgeX P D.i D.y₁ < v.1 := by_grind
      obtain ⟨ε, hε0, hε1, hεL, hεB⟩ := exists_small_pos (by linarith : 0 < v.1 - edgeX P D.i D.y₁)
        hrL hrB
      apply hleft ε hε0 hεL hεB
      zujjx
      apply hfilled hSL
      refine D.mem_closure_cellL hP ztnkk
        ztrpp
      zudjr
      zudci

    obtain ⟨u₀, hu₀, hadj₀, hseg₀, hon₀, hev₀⟩ := D.corner_edge hP hmP ztp hvy hvcornerL
    have hu₀nbr := hl.base_nbr hP hml hu₀ hadj₀ hSL (hev₀.mono fun s ⟨h, h1, h2, he⟩ => by
      zvmxm; exact D.left_side_mem_closure hP h1 h2)
    by_cases hmb : mP = D.bot
    · zuirs
      · zuhft
        refine ⟨D.i, u₀, D.top, D.isTrap.hi, hu₀, D.top_lt hP, hon₀, hu₀nbr, hwnbr, ?_,
          Or.inl ztmpz⟩
        zuq
        have htu := simple_vtx_inj hP ztgdl hu₀ h
        rcases hadj₀ with h' | h'
        · exact hna.2 by_grind
        · exact hna.1 by_grind
      · -- no diagonal: `v` is both bottom corners
        have hvj' : ztrhe := by
          zuct
          zuhru

          exact hfilled hSL (D.mem_closure_cellL hP
            ztnkk by_grind)
        obtain ⟨u₁, hu₁, hadj₁, hseg₁, hon₁, hev₁⟩ :=
          D.corner_edge hP hmP ztbt hvy hvj'
        have hSR : D.cellR ⊆ Q.filled \ Q.boundary := by
          rw [← D.cellL_eq_cellR hna]; omega
        have hu₁nbr := hl.base_nbr hP hml hu₁ hadj₁ hSR (hev₁.mono fun s ⟨h, h1, h2, he⟩ => by
          zvmxm; exact D.right_side_mem_closure hP h1 h2)
        have hvu₀ : v ≠ P.vtx u₀ := by
          have hpe : IsPieceEdge P mP u₀ := hadj₀.elim Or.inl ztzex
          exact hpe.vtx_ne hP hmP hu₀
        have hu01 : P.vtx u₀ ≠ P.vtx u₁ := by
          zuq
          have hne := D.isTrap.ne hP D.free.1
          have hm0 : lerp v ztqbj ztcn ∈ P.edge D.i := by
            rw [← hseg₀]; exact lerp_mem_segment _ _ by_norm_num by_norm_num
          have hm1 : lerp v ztqbj ztcn ∈ P.edge D.j := by
            grind
          have hce := (hP.2.2 D.i D.j D.isTrap.hi D.isTrap.hj hne).subset ⟨hm0, hm1⟩
          have hends : ∀ k, ztyff → k = mP ∨ k = u₀ := by
            zugf
            refine hon₀ k ?_ ?_
            · zuvk
              · exact D.isTrap.hi
              · exact succIdx_lt P D.isTrap.hi
            · zuvk
              · zucvg
              · zuisp
          have hmid : ∀ k, ztyff →
              lerp v ztqbj ztcn = P.vtx k → False := by
            intro k hk h'
            rcases hends k hk with h'' | h''
            · rw [h''] at h'; exact lerp_ne_left hvu₀ by_norm_num h'
            · rw [h''] at h'; exact lerp_ne_right hvu₀ by_norm_num h'
          rcases hce.1 with h' | h'
          · exact hmid _ ztp h'
          · exact hmid _ ztbt h'
        zuhft
        have htop : P.vtx D.top = P.vtx u₀ ∨ P.vtx D.top = P.vtx u₁ := by
          rcases hu₀nbr with h0 | h0 <;> rcases hu₁nbr with h1 | h1 <;> rcases hwnbr with h2 | h2
          · grind
          · grind
          · grind
          · grind
          · grind
          · grind
          · grind
          grind
        rcases htop with h | h
        · refine ⟨D.j, u₁, D.top, D.isTrap.hj, hu₁, D.top_lt hP, hon₁, hu₁nbr, hwnbr,
            by grind, Or.inr ztiwa⟩
        · refine ⟨D.i, u₀, D.top, D.isTrap.hi, hu₀, D.top_lt hP, hon₀, hu₀nbr, hwnbr,
            by grind, Or.inl ztmpz⟩
    · obtain ⟨w, hwS, hwx, hwnbr⟩ := D.bot_right_nbr hP hl hml rfl hmS hmb hSL
      refine ⟨D.i, u₀, w, D.isTrap.hi, hu₀, hwS.1, hon₀, hu₀nbr, hwnbr, ?_,
        Or.inl ⟨D, rfl, hSL, Or.inl hwS⟩⟩
      zuq
      have hwe : P.vtx w ∈ P.edge D.i := by
        rw [h, ← hseg₀]; exact Geometry.right_mem_segment _ _
      have hx := ((mem_edge_iff_edgeX D.isTrap.nhL).1 hwe).2
      rw [hwS.2.1] at hx
      linarith

/-! ### The walk -/

/-- **The walk.**  Let `f` enumerate positions of the piece such that the two neighbours of
`f (k + 1)` are `f k` and `f (k + 2)`, and let `St` be a predicate on vertices of `P` such that
every vertex `f k` (`1 ≤ k ≤ n - 2`) satisfying `St` has a neighbour, strictly `ylexLT`-above it,
satisfying `St`.  If `f 1` satisfies `St` and is above `f 0`, the vertices `f 0, f 1, …, f (n-1)`
are strictly increasing. -/
theorem walk_chain (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) (St : ℕ → Prop)
    (f : ℕ → ℕ) (hf : ∀ k, f k < l.length)
    (hnb : ∀ k, k + 2 < l.length →
      ((subPoly P l).vtx zterz = (subPoly P l).vtx ztbarr ∧
        (subPoly P l).vtx ztbahu = (subPoly P l).vtx ztbary) ∨
      ((subPoly P l).vtx zterz = (subPoly P l).vtx ztbary ∧
        (subPoly P l).vtx ztbahu = (subPoly P l).vtx ztbarr))
    (htr : ∀ k, 1 ≤ k → k + 2 ≤ l.length → St ztyrh →
      ∃ w, w < P.n ∧ St w ∧ ylexLT (P.vtx ztyrh) ztbup ∧
        (P.vtx w = (subPoly P l).vtx (prevIdx ztdi zterz) ∨
          P.vtx w = (subPoly P l).vtx ((f k + 1) % l.length)))
    (h1 : St (l.getD ztvqd 0))
    (h01 : ylexLT ((subPoly P l).vtx (f 0)) ((subPoly P l).vtx ztvqd)) :
    ∀ k, k + 1 < l.length →
      ylexLT ((subPoly P l).vtx zterz) ((subPoly P l).vtx ztxwn) := by
  zqsa
  have main : ∀ k, 1 ≤ k → k < l.length →
      St ztyrh ∧ ylexLT (Q.vtx (f ztie)) (Q.vtx zterz) := by
    zugoi
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp_all
      · obtain ⟨hSt, hlt⟩ := ih hkpos by_omega
        obtain ⟨w, hw, hStw, hcw, hnbw⟩ := htr k hkpos by_omega hSt
        have hvk : Q.vtx _ = P.vtx _ := IsPiece.vtx_eq zthya
        rw [← hvk] at hcw
        have hn := hnb ztie by_omega
        rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega] at hn
        have hw' : P.vtx w = Q.vtx ztxwn := by
          rcases hn with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hnbw with h | h
          · zqsc
          · grind
          · grind
          · zqsc
        zujx
        · have hwe : w = l.getD _ 0 :=
            simple_vtx_inj hP hw (hl.getD_lt ztqqb) (hw'.trans (IsPiece.vtx_eq ztqqb))
          grind
        grind
  grind

/-- The predecessor of a residue. -/
theorem prevIdx_mod_add_sub {Q : Polygon} {N : ℕ} (hQN : Q.n = N) (hN : 0 < N) (x : ℕ) :
    prevIdx Q (x % N) = (x + ztbpm) % N := by
  zulcb
  rw [hQN, show x % N + N - 1 = x % N + ztbpm by omega, Nat.mod_add_mod]

/-- **Monotonicity from the walk.**  Let `m` be the position of the lowest vertex of the piece,
`uP` one neighbour of position `m` and `w` the other one, and `St` a walk predicate satisfied by
`w` and propagated upwards from every vertex other than `l.getD m 0` and `uP`.  Then the piece is
a monotone mountain (in one of the two orientations). -/
theorem mono_of_walk (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) {m : ℕ}
    (hml : m < l.length)
    (hmin : ∀ j < l.length, j ≠ m → ylexLT ztmzu ztmzt)
    (St : ℕ → Prop) {uP w : ℕ} (huP : uP < P.n) (hw : w < P.n)
    (hstep : ∀ k, k < l.length → l.getD k 0 ≠ l.getD m 0 → l.getD k 0 ≠ uP →
      St ztcak → ∃ w', w' < P.n ∧ St w' ∧ ylexLT ztzcx ztvcq ∧
        (P.vtx w' = (subPoly P l).vtx ztwwk ∨
          P.vtx w' = (subPoly P l).vtx ztwnc))
    (hu : P.vtx uP = (subPoly P l).vtx ztxli ∨
      P.vtx uP = (subPoly P l).vtx ztxll)
    (hwn : P.vtx w = (subPoly P l).vtx ztxli ∨
      P.vtx w = (subPoly P l).vtx ztxll)
    (hwu : P.vtx w ≠ P.vtx uP) (hSt : St w) :
    ∃ a < l.length, IsMonoAt ztdi a := by
  zqsa
  set N := l.length with hNdef
  zueqo
  have hQn : Q.n = N := by_simp_all
  have hN3 := hQn ▸ simple_three_le hQ
  zudnr
  have hmQ : m < Q.n := by_omega
  have hprevN : prevIdx Q m = (m + ztbpm) % N := by
    unfold prevIdx; rw [hQn, show m + N - 1 = m + ztbpm by omega]
  -- vertices at positions
  have hvtx : ∀ {k}, k < N → Q.vtx k = P.vtx _ := IsPiece.vtx_eq
  have hidx : ∀ {k c}, k < N → c < P.n → P.vtx c = Q.vtx k → c = l.getD k 0 :=
    fun hk hc h => simple_vtx_inj hP hc ztmlg by_grind
  rcases hu with hu | hu
  · -- forward walk: the base is the edge from position `m - 1` to position `m`
    have hwn' : P.vtx w = Q.vtx (ztbl % N) := by
      grind
    set f : ℕ → ℕ := fun k => (m + k) % N with hfdef
    zqsd
    have hfinj : ztflc := fun k k' hk hk' h =>
      Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' m h) hk hk'
    have hf0 : ztuuj := by simp only [hfdef, add_zero]; exact Nat.mod_eq_of_lt hml
    have hfN : f ztbpm = prevIdx Q m := by_grind
    have chain := walk_chain hP hl St f hf
      (fun k _ => Or.inl ⟨by
          zucr
          rw [show f zts = (m + k + 1) % N by zuotm; ring_nf,
            prevIdx_mod_add_sub hQn hN0, show m + k + 1 + ztbpm = m + k + N by omega,
            Nat.add_mod_right],
        by
          grind⟩)
      (fun k hk1 hk2 hSk => by
        zqsb
        · zqry
          omega
        · have hu' := hidx (prevIdx_lt Q hmQ |>.trans_eq hQn) huP hu
          zujmb
          have := hfinj k _ by_omega by_omega
            ((hl.getD_inj zthya (prevIdx_lt Q hmQ |>.trans_eq hQn) hu').trans hfN.symm)
          omega)
      (by
        have := hidx ztqqa hw by_omega; grind)
      (by
        zqrw
        omega)
    refine ⟨prevIdx Q m, prevIdx_lt Q hmQ |>.trans_eq hQn, hQ, prevIdx_lt Q hmQ, Or.inl ?_⟩
    zuda
    have hpos : ∀ q, (prevIdx Q m + 1 + q) % Q.n = f q := by
      intro q
      rw [← Nat.mod_add_mod, prevIdx_succ Q hmQ, hQn]
    rw [hpos, hpos]
    exact chain p by_omega
  · -- backward walk: the base is the edge from position `m` to position `m + 1`
    have hwn' : P.vtx w = Q.vtx (prevIdx Q m) := by
      grind
    set f : ℕ → ℕ := fun k => (m + ztbpm * k) % N with hfdef
    zqsd
    have hkey : ∀ k, ztrpk % N = m % N := by
      zugoi
      zuotm
      rw [Nat.mod_add_mod, show m + ztbpm * k + k = m + N * k by
        rw [add_assoc, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel by_omega],
        Nat.add_mul_mod_self_left]
    have hfeq : ∀ k x, x < N → (x + k) % N = m % N → f k = x := by
      intro k x hx h
      have h1 := (hkey k).trans h.symm
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' k h1) zthya hx
    have hfinj : ztflc := by
      intro k k' hk hk' h
      have h1 : f k + k ≡ f k + k' [MOD N] := by
        show ztrpk % N = (f k + k') % N
        rw [hkey k, h, hkey k']
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' _ h1) hk hk'
    have hf0 : ztuuj := by simp only [hfdef, mul_zero, add_zero]; exact Nat.mod_eq_of_lt hml
    have hfN : f ztbpm = ztbl % N := by
      zqrz
      rw [Nat.mod_add_mod, show m + 1 + ztbpm = m + N by omega, Nat.add_mod_right]
    have hnext : ∀ k, ztyet % N = f k := by
      zugoi
      symm
      zqrz
      rw [Nat.mod_add_mod, show f _ + 1 + k = f _ + zts by ring, hkey]
    have hprev : ∀ k, prevIdx Q ztxwn = f ztcnq := by
      zugoi
      rw [show f _ = (f _) % N from (Nat.mod_eq_of_lt ztqqb).symm,
        prevIdx_mod_add_sub hQn hN0]
      grind
    have chain := walk_chain hP hl St f hf
      (fun k _ => Or.inr ⟨by rw [hnext], by rw [hprev]⟩)
      (fun k hk1 hk2 hSk => by
        zqsb
        · zqry
          omega
        · have hnl : ztbl % N < N := Nat.mod_lt _ hN0
          have hu' := hidx hnl huP hu
          zujmb
          have := hfinj k _ by_omega by_omega
            ((hl.getD_inj zthya hnl hu').trans hfN.symm)
          omega)
      (by
        have h1 : f 1 = prevIdx Q m := by
          grind
        have := hidx ztqqa hw by_grind; grind)
      (by
        zqrw
        omega)
    refine ⟨m, hml, hQ, hmQ, Or.inr ?_⟩
    zuda
    zvmxg at hp ⊢
    have e1 : (m + 1 + ztr) % N = f ztjke := by
      symm
      zqrz
      rw [Nat.mod_add_mod, show m + 1 + ztr + ztjke = m + N by omega, Nat.add_mod_right]
    have e2 : (m + 1 + p) % N = f ztnna := by
      symm
      zqrz
      rw [Nat.mod_add_mod, show m + 1 + p + ztnna = m + N by omega, Nat.add_mod_right]
    zuea
    exact chain _ by_omega

/-- **The mountain decomposition theorem.**  Every piece of the subdivision of a simple polygon
`P` by the inserted diagonals `allDiagonals P` is a monotone mountain: for some position `a`,
the vertices of the piece read cyclically from position `a + 1` to position `a` are strictly
`ylexLT`-increasing or strictly `ylexLT`-decreasing (so the edge `a` of the piece is its base). -/
theorem piece_isMonoAt (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) :
    ∃ a < l.length, IsMonoAt ztdi a := by
  zqsa
  zueqo
  zudnu
  obtain ⟨m, hm, hmin⟩ := exists_isLocMin hQ
  have hml := hQn ▸ hm.1
  have hmin' : ∀ j < l.length, j ≠ m → ylexLT _ _ :=
    fun j hj hjm => hmin j (hQn ▸ hj) hjm
  obtain ⟨e, uP, w, he, huP, hw, hon, hu, hwn, hwu, hst⟩ := piece_initial hP hl hm hmin
  have hnot : ∀ c, c < P.n → c ≠ l.getD m 0 → c ≠ uP → P.vtx c ∉ P.edge e := by
    grind
  rcases hst with hst | hst
  · exact mono_of_walk hP hl hml hmin' _ huP hw
      (fun k hk h1 h2 hSk => StateL.step hP hl he hk rfl hSk
        ztzga) hu hwn hwu hst
  · exact mono_of_walk hP hl hml hmin' _ huP hw
      (fun k hk h1 h2 hSk => StateR.step hP hl he hk rfl hSk
        ztzga) hu hwn hwu hst

/-! ### Reversing the orientation of a piece -/

/-- The index of the edge of `Q` carrying edge `k` of the reversed polygon (`n` vertices). -/
def revEdge (n k : ℕ) : ℕ := if k + 1 < n then n - 2 - k else n - 1
variable {n k : ℕ}
/-- `revEdge n` maps indices below `n` to indices below `n`. -/
theorem revEdge_lt (hk : k < n) : revEdge n k < n := by
  zumuf

/-- `revEdge n` is an involution on indices below `n`. -/
theorem revEdge_revEdge (hk : k < n) : revEdge n (revEdge n k) = k := by
  zumuf
section Reverse
variable {Q R : Polygon}

/-- The endpoints of edge `k` of a reversed polygon `R` (`R.vtx k = Q.vtx (n - 1 - k)`) are the
endpoints of edge `revEdge n k` of `Q`, in the opposite order. -/
theorem rev_endpoints (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx ztcgz) {k : ℕ}
    (hk : k < Q.n) :
    R.vtx k = Q.vtx ((revEdge Q.n k + 1) % Q.n) ∧
      R.vtx (zts % R.n) = Q.vtx zttyv := by
  zubdb
  unfold revEdge
  zus
  · rw [Nat.mod_eq_of_lt by_grind, Nat.mod_eq_of_lt h, hv k hk,
      hv _ h]
    grind
  · have hk' : k = Q.n - 1 := by_omega
    rw [show Q.n - 1 + 1 = Q.n by omega, Nat.mod_self, show k + 1 = Q.n by omega, Nat.mod_self,
      hv k hk, hv 0 by_omega]
    simp_all

/-- Edge `k` of the reversed polygon is edge `revEdge n k` of `Q`. -/
theorem rev_edge (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx ztcgz) {k : ℕ}
    (hk : k < Q.n) : R.edge k = Q.edge zttyv := by
  obtain ⟨e1, e2⟩ := rev_endpoints hn hv hk
  zucrd
  rw [e1, e2, Geometry.segment_comm]

/-- **A reversed polygon has the same boundary.** -/
theorem rev_boundary (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx ztcgz) :
    R.boundary = Q.boundary := by
  zufj
  constructor
  · zucje
    zugeh
    exact ⟨_, revEdge_lt hk, by rw [← rev_edge hn hv hk]; exact hp⟩
  · zueco
    refine ⟨revEdge Q.n j, by zvmxq; exact revEdge_lt hj, ?_⟩
    rw [rev_edge hn hv ztwct, revEdge_revEdge hj]
    zuitn

/-- **A reversed polygon has the same filled region.** -/
theorem rev_filled (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx ztcgz) :
    R.filled = Q.filled := by
  unfold Polygon.filled
  rw [rev_boundary hn hv]

/-- **A reversed simple polygon is simple.** -/
theorem rev_simple (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx ztcgz)
    (hQ : Q.Simple) : R.Simple := by
  refine ⟨hn ▸ hQ.1, fun i j hi hj h => ?_, fun i j hi hj hij => ?_⟩
  · zujjn
    rw [hv i hi, hv j hj] at h
    have := hQ.2.1 _ _ by_omega by_omega h
    omega
  · zujjn
    rw [rev_edge hn hv hi, rev_edge hn hv hj]
    have hne : revEdge Q.n i ≠ revEdge Q.n j := fun h => hij (by
      have := congrArg (revEdge Q.n) h
      rwa [revEdge_revEdge hi, revEdge_revEdge hj] at this)
    rw [hQ.2.2 _ _ (revEdge_lt hi) ztwct hne]
    obtain ⟨a1, a2⟩ := rev_endpoints hn hv hi
    obtain ⟨b1, b2⟩ := rev_endpoints hn hv hj
    zufj
    zumri
    zulrx
    rw [a1, a2, b1, b2]
    tauto

/-- Two residues adding up to `n - 1` modulo `n`. -/
theorem eq_sub_of_add_mod {N u v : ℕ} (hu : u < N) (hv : v < N)
    (h : ztuck % N = ztbpm % N) : u = N - 1 - v := by
  rw [Nat.mod_eq_of_lt (show N - 1 < N by omega)] at h
  rcases Nat.lt_or_ge ztuck N with h' | h'
  · zupe
  · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt by_omega] at h; omega

/-- **A decreasing chain becomes increasing after reversal.** -/
theorem rev_chainInc (hn : R.n = Q.n) (hv : ∀ k < Q.n, R.vtx k = Q.vtx ztcgz)
    (h3 : 3 ≤ Q.n) {a : ℕ} (ha : a < Q.n) (h : ChainDec Q a) :
    ChainInc R ((2 * Q.n - 2 - a) % Q.n) := by
  set N := Q.n with hN
  zuda
  zueyb
  zudnr
  have hx1 : (zteio + 1 + p) % N < N := Nat.mod_lt _ hN0
  have hx2 : (zteio + 1 + ztr) % N < N := Nat.mod_lt _ hN0
  rw [hv _ hx1, hv _ hx2]
  have key : ∀ q, q + 1 ≤ N →
      N - 1 - (zteio + 1 + q) % N = ztzdg % N := by
    zuco
    symm
    apply eq_sub_of_add_mod zthbs zthbs
    have e1 : (ztzdg % N + ((2 * N - 2 - a) % N + 1 + q) % N) % N =
        (a + 1 + ztgee + ztjfb) % N :=
      (Nat.mod_modEq _ N).add ((Nat.mod_modEq _ N).trans
        (((Nat.mod_modEq _ N).add_right 1).add_right q))
    rw [e1, show a + 1 + ztgee + ztjfb = N - 1 + N * 2 by omega,
      Nat.add_mul_mod_self_left]
  rw [key p by_omega, key _ by_omega]
  have := h ztjke by_omega
  rw [show N - 2 - p + 1 = N - 1 - p by omega] at this
  grind
end Reverse

/-- The reversed piece: its vertices are those of the piece in the opposite order. -/
theorem vtx_subPoly_reverse (P : Polygon) (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    (subPoly P l.reverse).vtx k = (subPoly P l).vtx (l.length - 1 - k) := by
  rw [vtx_subPoly_getD P l.reverse by_simp_all, getD_reverse l hk,
    vtx_subPoly_getD P l by_omega]

/-- The reversed piece has the same number of vertices. -/
theorem n_subPoly_reverse (P : Polygon) (l : List ℕ) :
    (subPoly P l.reverse).n = (subPoly P l).n := by
  simp

/-- **The reversed piece has the same filled region.** -/
theorem filled_subPoly_reverse (P : Polygon) (l : List ℕ) :
    (subPoly P l.reverse).filled = (subPoly P l).filled :=
  rev_filled by_simp_all (fun k hk => by
    zvnnk at hk ⊢; exact vtx_subPoly_reverse P l hk)

/-- **The reversed piece is simple.** -/
theorem simple_subPoly_reverse {l : List ℕ} (h : (subPoly P l).Simple) :
    (subPoly P l.reverse).Simple :=
  rev_simple by_simp_all (fun k hk => by
    zvnnk at hk ⊢; exact vtx_subPoly_reverse P l hk) h

/-- **The mountain decomposition theorem, oriented form.**  Every piece is a monotone mountain
with increasing chain (`IsMountainAt`, base = edge `a`), either as listed or after reversing
its vertex list. -/
theorem piece_isMountainAt (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) :
    ∃ a < l.length, IsMountainAt ztdi a ∨ IsMountainAt ztubh a := by
  obtain ⟨a, ha, hQ, haQ, hc⟩ := piece_isMonoAt hP hl
  zunk
  · exact ⟨a, ha, Or.inl ⟨hQ, haQ, hc⟩⟩
  · have hn := n_subPoly_reverse P l
    have hv : ∀ k < (subPoly P l).n,
        (subPoly P l.reverse).vtx k = (subPoly P l).vtx ((subPoly P l).n - 1 - k) := by
      intro k hk; zvnnk at hk ⊢; exact vtx_subPoly_reverse P l hk
    have hlen : ztoqe := by_simp_all
    refine ⟨(2 * l.length - 2 - a) % l.length, Nat.mod_lt _ by_omega, Or.inr
      ⟨simple_subPoly_reverse hQ, by rw [hn, hlen]; exact Nat.mod_lt _ by_omega, ?_⟩⟩
    have := rev_chainInc hn hv hQ.1 haQ hc
    simp_all

/-- **The mountain decomposition theorem, in the form used by the stack algorithm.**  Every piece
of the subdivision of a simple polygon by `allDiagonals P` is, after rotation, a monotone
mountain in the sense of `Chazelle.Mountain.IsMountain` (vertices listed in strictly increasing
`ylexLT` order, base = last edge), either with its vertex list as given or reversed.  The
reversed piece has the same boundary and filled region (`boundary_subPoly_reverse`,
`filled_subPoly_reverse`). -/
theorem piece_isMountain (hP : P.Simple) {l : List ℕ} (hl : IsPiece P l) :
    ∃ s, IsMountain ztden ∨ IsMountain ztdeo := by
  obtain ⟨a, ha, h | h⟩ := piece_isMountainAt hP hl
  · have haQ : a < (subPoly P l).n := by_simp_all
    exact ⟨ztdf % (subPoly P l).n, Or.inl ztosw⟩
  · have haQ : a < (subPoly P l.reverse).n := by
      simp_all
    refine ⟨ztdf % (subPoly P l.reverse).n, Or.inr ztosw⟩
end
end Chazelle.Mountain
end
section
set_option hygiene false
local macro "zqbdd" : tactic => `(tactic| (simp only [hqdef, sub_self, abs_zero]
                                           rw [show z.1 + ztdig - ztkhm = -ε by ring, abs_neg, abs_of_pos hε0]))
local macro "zqbde" : tactic => `(tactic| obtain ⟨r, hr, hloc⟩ := edge_local hW hL hp ⟨ht0, ht1⟩)
local macro "zqbdf" : tactic => `(tactic| (have hjn := prevIdx_lt W hp
                                           have hji := prevIdx_ne W hn hp
                                           have hsucc := prevIdx_succ W hp))
local macro "zqbdg" : tactic => `(tactic| obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_filled W).isOpen_compl _ hnf)
set_option hygiene true

/-!
# WP-B: the interior model satisfies the walk axioms

For a simple polygon `Q`, the interior model `interiorModel Q` (domain the interior
`Q.filled \ Q.boundary`, walk `interiorWalk Q` oriented with the interior on its left,
admissible chords the horizontal chords of the interior) satisfies the walk axioms `WalkAx`
(`walkAx_interiorModel`).

## Local structure of a simple polygon with the interior on the left

For a simple polygon `W` with `orient W = 1`:

* `edge_local`: near a point inside an edge, the open left half-plane is interior, the open
  right half-plane is exterior, and the line is the boundary (`strip` and the uniform interior
  side `eventually_offset_orient`);
* `vertex_local`: near a vertex, the open left sector of the corner is interior, the open right
  sector is exterior, and every point off the boundary is in one of the two (`sideSector`,
  coverage `sideCcw_or`, and simplicity: the corner is not a spike);
* `pos_unique`: a point of the boundary is at a single walk position.

## The chord system of the interior

`chordPoly`: for a horizontal chord from `e₁` (on edge `i`) to `e₂` (on edge `j ≠ i`), the closed
walk `vtx (i+1), …, vtx j, e₂, e₁` has its boundary in `∂W ∪ c` and its crossing parity flips
across the chord (`Jordan.parity_flip`), so every finite admissible family is a
`ChordSystem` of the interior (`interior_chordSystem`).
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideClean ChordSystem IsHChordIn
  sideLeftOf sideCcw sideCross sideDot sideNonSpike sideSector sideLeftOf_not_seg_prev
  sideLeftOf_not_seg_next sideCcw_or sideCross_out sideLeft_edge sideLeft_zero sidePt_zero)
open Chazelle.Jordan
open Chazelle.Mountain (LeftInside orient orient_eq eventually_offset_orient)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment lerp_zero lerp_one
  lerp_injective)
open Chazelle.Visibility (hseg)
namespace FactsInterior
variable {W : Polygon}

/-! ## Being filled is constant on preconnected sets off the boundary -/
theorem filled_iff_of_preconnected (hW : W.Simple) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ W.boundaryᶜ) {x y : Point} (hx : x ∈ S) (hy : y ∈ S) :
    x ∈ W.filled ↔ y ∈ W.filled := by
  rw [mem_filled_iff hW (hSb hx), mem_filled_iff hW (hSb hy),
    parity_eq_of_isPreconnected W hS hSb hx hy]

/-- A preconnected set off the boundary meeting the interior lies in the interior. -/
theorem subset_interior (hW : W.Simple) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ W.boundaryᶜ) {x : Point} (hx : x ∈ S) (hxi : x ∈ W.filled) :
    S ⊆ W.filled \ W.boundary := fun _y hy =>
  ⟨(filled_iff_of_preconnected hW hS hSb hx hy).1 hxi, hSb hy⟩

/-- A preconnected set off the boundary meeting the exterior lies in the exterior. -/
theorem subset_exterior (hW : W.Simple) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ W.boundaryᶜ) {x : Point} (hx : x ∈ S) (hxe : x ∉ W.filled) :
    S ⊆ W.filledᶜ := fun _y hy h =>
  hxe ((filled_iff_of_preconnected hW hS hSb hx hy).2 h)

/-! ## Near a point inside an edge -/

/-- **Near a point inside an edge**: the open left half-plane is interior, the open right
half-plane exterior, and the line of the edge is the boundary. -/
theorem edge_local (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ r > 0, ∀ x ∈ ball ztia r,
      (0 < det ztbbv ztbajj x → x ∈ W.filled \ W.boundary) ∧
      (det ztbbv ztbajj x < 0 → x ∉ W.filled) ∧
      (det ztbbv ztbajj x = 0 → x ∈ W.boundary) := by
  set u := W.vtx p with hu
  set v := W.vtx _ with hv
  have huv := simple_vtx_succ_ne hW hp
  zullk
  obtain ⟨r, hr, hstrip⟩ := strip hW hp ht
  have hq : sidePt W p t = lerp u v t := rfl
  refine ⟨r, hr, fun x hx => ⟨fun hdet => ?_, fun hdet => ?_, fun hdet => ?_⟩⟩
  · -- the left half-ball
    set H := ball ztia r ∩ {y | 0 < 1 * det u v y} with hH
    have hHc : ztrfq := ((convex_ball _ _).inter zteev).isPreconnected
    zuhwv
    obtain ⟨δ, hδ1, hδ2, hδ0⟩ := ((eventually_offset_orient hW hp ht).and
      ((eventually_offset_mem 1 isOpen_ball zteal).and
        self_mem_nhdsWithin)).exists
    zuija
    zvohi at hδ2
    zumfd
    have hmem : offset u v t δ ∈ H := ⟨hδ2, by
      show 0 < 1 * det u v _
      rw [one_mul, det_offset]; simp_all⟩
    exact subset_interior hW hHc hHb hmem hδ1.1.1 by_simp_all
  · -- the right half-ball
    set H := ball ztia r ∩ {y | 0 < (-1) * det u v y} with hH
    have hHc : ztrfq :=
      ((convex_ball _ _).inter ztrnu).isPreconnected
    zuhwv
    obtain ⟨δ, hδ1, hδ2, hδ0⟩ := ((eventually_offset_orient hW hp ht).and
      ((eventually_offset_mem _ isOpen_ball zteal).and self_mem_nhdsWithin)).exists
    zuija
    zumfd
    have e : -δ = (-1) * δ := by_ring
    zvmwe at hδ1
    have hmem : offset u v t _ ∈ H := ⟨hδ2, by
      show 0 < (-1) * det u v (offset u v t ztiev)
      rw [det_offset]; nlinarith [mul_pos hδ hsq]⟩
    exact subset_exterior hW hHc hHb hmem hδ1.2 by_grind
  simp_all

/-! ## Near a vertex -/

/-- The two edges at a vertex of a simple polygon meet only at the vertex. -/
theorem corner_meet (hW : W.Simple) {p : ℕ} (hp : p < W.n) :
    Chazelle.segment ztcyt ztbbv ∩
      Chazelle.segment ztbbv ztbajj ⊆ {W.vtx p} := by
  zuerq
  zuiog
  zqbdf
  have hjs := prevIdx_ne_succIdx W hn hp
  have hab : W.vtx j ≠ W.vtx _ := simple_vtx_ne hW hjn (succIdx_lt W hp) hjs
  zuh
  have : x ∈ W.edge j ∩ W.edge p := by
    rw [edge_prevIdx W hp]; exact hx
  rw [simple_edge_inter hW hjn hp hji] at this
  zuhhm

/-- The corner at a vertex of a simple polygon is not a spike. -/
theorem corner_nonSpike (hW : W.Simple) {p : ℕ} (hp : p < W.n) :
    sideNonSpike ztbalz (W.vtx (prevIdx W p) - W.vtx p) := by
  have hbv : ztsdc := simple_vtx_succ_ne hW hp
  rintro ⟨hcr, hdot⟩
  rw [sideCross_out] at hcr
  obtain ⟨s, hs_eq⟩ := Geometry.exists_lerp_of_det_eq_zero hbv hcr
  rw [hs_eq] at hdot
  have hsq := sqLen_pos hbv
  have hs : ztxx := by
    unfold sideDot at hdot
    zvnuo at hdot
    zulvc

  set μ := min s 1 / 2 with hμ
  have hμ0 : ztrzr := by_simp_all
  have hμ1 : μ < 1 := by zvnhc; have := min_le_right s 1; linarith
  have hμs : μ ≤ s := by zvnhc; have := min_le_left s 1; linarith
  have hy1 : lerp _ _ μ ∈
      Chazelle.segment ztbbv ztbajj := lerp_mem_segment _ _ hμ0.le hμ1.le
  have hy2 : lerp ztbbv ztbajj μ ∈
      Chazelle.segment ztcyt ztbbv := by
    rw [hs_eq, Geometry.segment_comm]
    refine ⟨μ / s, div_nonneg hμ0.le hs.le, (div_le_one hs).2 hμs, ?_⟩
    zuefg
  have := corner_meet hW hp ⟨hy2, hy1⟩
  exact lerp_ne_left hbv hμ0 this

/-- **Near a vertex** of a simple polygon with the interior on the left: the open left sector
of the corner is interior, the open right sector is exterior, and every point off the boundary
lies in one of them. -/
theorem vertex_local (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) :
    ∃ r > 0, ∀ x ∈ ball ztbbv r,
      (sideLeftOf ztcyt ztbbv ztbajj x →
        x ∈ W.filled \ W.boundary) ∧
      (sideLeftOf ztbajj ztbbv ztcyt x → x ∉ W.filled) ∧
      (x ∉ W.boundary →
        sideLeftOf ztcyt ztbbv ztbajj x ∨
          sideLeftOf ztbajj ztbbv ztcyt x) := by
  zuerq
  zuiog
  set a := W.vtx j with ha
  set v := W.vtx p with hv
  set b := W.vtx _ with hb
  zqbdf
  have hav := simple_vtx_ne hW hjn hp hji
  have hbv := (simple_vtx_succ_ne hW hp).symm
  -- near `v` the boundary is the two edges at `v`
  have hother : ∀ k ∈ ((Finset.range W.n).erase p).erase j, v ∉ W.edge k := by
    intro k hk hmem
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    rcases (simple_vtx_mem_edge_iff hW hp hk.2.2).1 hmem with h | h
    · omega
    omega
  obtain ⟨r₀, hr₀, hball⟩ := exists_ball_disjoint_edges W _ hother
  have hS : ∀ x ∈ ball v r₀, x ∈ W.boundary →
      x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b := by
    zuczh
    by_cases hkp : k = p
    · subst hkp; tauto
    · zufrb
      · subst hkj
        left
        rw [← edge_prevIdx W hp]; omega
      grind
  -- radius also below the edge lengths (for the coverage)
  set r := min r₀ (min ‖b - v‖ ‖a - v‖) with hr
  have hbv0 := norm_pos_iff.2 ztwfh
  have hav0 := norm_pos_iff.2 ztwfg
  have hr0 := lt_min hr₀ (lt_min hbv0 hav0)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrb : r ≤ ‖b - v‖ := (min_le_right _ _).trans ztff
  have hra : r ≤ ‖a - v‖ := (min_le_right _ _).trans ztgh
  have hSr :=
    fun x hx => hS x (ball_subset_ball hrr₀ hx)
  -- the left sector
  have hSL : ∀ x ∈ ball v r, x ∈ W.boundary → ¬ sideLeftOf a v b x := by
    zuetj

    · exact sideLeftOf_not_seg_prev hav h
    · exact sideLeftOf_not_seg_next hbv h
  have hSR : ∀ x ∈ ball v r, x ∈ W.boundary → ¬ sideLeftOf b v a x := by
    zuetj

    · rw [Geometry.segment_comm] at h; exact sideLeftOf_not_seg_next hav h
    · rw [Geometry.segment_comm] at h; exact sideLeftOf_not_seg_prev hbv h
  obtain ⟨hLb, hLc, hLoff⟩ := sideSector hav hbv hr0 hSL
  obtain ⟨hRb, hRc, hRoff⟩ := (sideSector hbv hav hr0 hSR).reverse
  -- a point of the left sector is interior, one of the right sector exterior
  have hp1 : W.vtx _ = b := rfl
  have hs01 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT ztcjf] with s hs; exact hs
  obtain ⟨s, ⟨hsL, hsR⟩, hs⟩ := ((hLoff.and hRoff).and hs01).exists
  obtain ⟨δ, ⟨hδL, hδR⟩, hδo⟩ := ((hsL.and hsR).and (eventually_offset_orient hW hp hs)).exists
  rw [hL, one_mul] at hδo
  zvohi at hδL
  have hLin := subset_interior hW hLc hLb hδL.2 hδo.1.1
  have e : (-1) * δ = -δ := by_ring
  zvmwe at hδR
  have hRout := subset_exterior hW hRc hRb hδR.2 hδo.2
  refine ⟨r, hr0, fun x hx => ⟨fun h => hLin ztuio, fun h => hRout ztuio, fun hxb => ?_⟩⟩
  -- coverage
  have hxv : x ≠ v := fun h => hxb (h ▸ Existence.vtx_mem_boundary W hp)
  have hray : ∀ w : Point, w ≠ v → ‖w - v‖ ≥ r → Chazelle.segment v w ⊆ W.boundary →
      ¬ (sideCross ztbez ztsq = 0 ∧ 0 ≤ sideDot ztbez ztsq) := by
    rintro w hwv hwr hseg ⟨hc, hd⟩
    rw [sideCross_out] at hc
    obtain ⟨μ, rfl⟩ := Geometry.exists_lerp_of_det_eq_zero ztvbr hc
    have hsq := sqLen_pos ztvbr
    have hμ0 : 0 ≤ μ := by
      zumup
      zvnuo at hd
      zulvc

    have e : ztygt := by
      zuenz
    have hdist : ‖lerp v w μ - v‖ < r := by_tauto
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0] at hdist
    have hμ1 : μ ≤ 1 := by
      zubq

      have : ‖w - v‖ < μ * ‖w - v‖ := by
        have := norm_pos_iff.2 (sub_ne_zero.2 hwv); nlinarith
      linarith
    exact hxb (hseg (lerp_mem_segment _ _ hμ0 hμ1))
  have hsegb := Existence.edge_subset_boundary W hp
  have hsega : Chazelle.segment v a ⊆ W.boundary := by
    rw [Geometry.segment_comm, ← edge_prevIdx W hp]
    exact Existence.edge_subset_boundary W hjn
  exact sideCcw_or ztwfh ztwfg (corner_nonSpike hW hp)
    (hray b hbv by_omega hsegb) (hray a hav hra hsega)

/-! ## Walk positions of a simple polygon -/

/-- **A point of a simple polygon is at a single walk position.** -/
theorem pos_unique (hW : W.Simple) {p p' : ℕ} {t t' : ℝ} (hp : p < W.n) (hp' : p' < W.n)
    (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : sidePt W p t = sidePt W p' t') : p = p' ∧ t = t' := by
  have key : ∀ {p p' : ℕ} {t t' : ℝ}, p < W.n → p' < W.n → t ∈ Ioo (0 : ℝ) 1 → 0 ≤ t' →
      t' < 1 → sidePt W p t = sidePt W p' t' → p = p' ∧ t = t' := by
    intro p p' t t' hp hp' ht ht' ht1' h
    zugad
    · by_cases hpp : p' = p
      · subst hpp
        exact ⟨rfl, lerp_injective ztohy h⟩
      · have hmem : sidePt W p t ∈ W.edge p' := by
          zvmwc; exact lerp_mem_segment _ _ ht'0.le ht1'.le
        exact absurd hmem (simple_openEdge_not_mem_other hW hp ht hp' hpp)
    · subst ht'0
      rw [sidePt_zero] at h
      exact absurd h (simple_openEdge_ne_vtx hW hp ht hp')
  zubhu
  · grind
  · zudlw
    zugad
    · grind
    · subst ht'0
      rw [sidePt_zero, sidePt_zero] at h
      exact ⟨simple_vtx_inj hW hp hp' h, rfl⟩

/-- A point of the boundary is the point of a walk position. -/
theorem exists_pos_of_mem_boundary {q : Point} (hq : q ∈ W.boundary) :
    ∃ p < W.n, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ sidePt W p t = q := by
  obtain ⟨i, hi, hqi⟩ := hq
  obtain ⟨τ, hτ0, hτ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hqi
  rcases hτ1.lt_or_eq with h | h
  · tauto
  · refine ⟨ztg % W.n, Nat.mod_lt _ by_omega, 0, le_rfl, one_pos, ?_⟩
    rw [sidePt_zero, h, lerp_one]

/-- **Cleanness** of every position of a simple polygon with the interior on the left. -/
theorem clean (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t < 1) : SideClean W ztjnp p t := by
  zubhu
  · zqbde
    refine ⟨r, hr, fun x hx hxD hxl => hxD ((hloc x hx).1 ?_)⟩
    rwa [sideLeft_edge ztohy by_simp_all] at hxl
  · zudlw
    zueuq
    refine ⟨r, hr, fun x hx hxD hxl => hxD ((hloc x (by rwa [sidePt_zero] at hx)).1 ?_)⟩
    rwa [sideLeft_zero] at hxl

/-- Near its point, the interior points are in the left sector of a position. -/
theorem interior_left (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ r > 0, ∀ x ∈ ball ztia r, x ∈ W.filled \ W.boundary → sideLeft W p t x := by
  zubhu
  · zqbde
    zumkn
    rw [sideLeft_edge ztohy by_simp_all]
    grind
  · zudlw
    zueuq
    zumkn
    rw [sidePt_zero] at hx
    rw [sideLeft_zero]
    rcases (hloc x hx).2.2 hxD.2 with h | h
    · zubh
    simp_all

/-- The endpoint condition for a segment `[e, e']` whose open part is interior, at the boundary
point `e`. -/
theorem walkEnd (hW : W.Simple) (hL : orient W = 1) {e e' : Point} (hee : e ≠ e')
    (he : e ∈ W.boundary)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ W.filled \ W.boundary) :
    WalkEnd W ztnkg e := by
  refine ⟨?_, fun p p' t t' hp ht ht1 hp' ht' ht1' hne h1 h2 => ?_⟩
  · obtain ⟨p, hp, t, ht, ht1, hpt⟩ := exists_pos_of_mem_boundary he
    obtain ⟨r, hr, hleft⟩ := interior_left hW hL hp ht ht1
    have hd := dist_pos.2 hee
    refine ⟨p, t, ⟨hp, ht, ht1, by zvmxe; exact Geometry.left_mem_segment _ _,
      min r _, lt_min hr hd, fun x hx hxe hxd => ?_⟩, hpt⟩
    zvmxe at hxe hxd
    zufr
    have hs0' : ztxx := by
      zuvl
      · zubh
      · exact absurd ztggb hxe
    have hs1' : ztdrm := by
      zukmf
      · zubh
      · exfalso
        rw [h, lerp_one, dist_comm] at hxd
        simp_all
    refine hleft _ ?_ by_simp_all
    simp_all
  · exfalso
    obtain ⟨h3, h4⟩ := pos_unique hW hp hp' ht ht1 ht' ht1' ztmkm
    simp_all

/-! ## The chord system of the interior -/

/-- The closed walk `vtx (i+1), …, vtx (i+m), e₂, e₁` of a chord from `e₁` to `e₂`. -/
def chordPoly (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) : Polygon :=
  ⟨(List.range m).map (fun k => W.vtx ztflv) ++ [e₂, e₁]⟩
theorem chordPoly_n (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) : (chordPoly W i m e₁ e₂).n = m + 2 := by
  simp [chordPoly, Polygon.n]
theorem chordPoly_vtx_lt (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) {k : ℕ} (hk : k < m) :
    (chordPoly W i m e₁ e₂).vtx k = W.vtx ztflv := by
  simp only [chordPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left by_simp_all, List.getElem?_map, List.getElem?_range hk]
  rfl
theorem chordPoly_vtx_m (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) :
    (chordPoly W i m e₁ e₂).vtx m = e₂ := by
  zuhon
theorem chordPoly_vtx_m1 (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) :
    (chordPoly W i m e₁ e₂).vtx ztbl = e₁ := by
  zuhon
theorem chordPoly_edge_lt (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) {k : ℕ} (hk : k + 1 < m) :
    (chordPoly W i m e₁ e₂).edge k = W.edge ztflv := by
  zucrd
  rw [chordPoly_n, Nat.mod_eq_of_lt by_grind, chordPoly_vtx_lt W i e₁ e₂ by_omega,
    chordPoly_vtx_lt W i e₁ e₂ hk, Existence.mod_add_one_mod]
theorem chordPoly_edge_pen (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) (hm : 0 < m) :
    (chordPoly W i m e₁ e₂).edge ztfte = Chazelle.segment (W.vtx (ztjym % W.n)) e₂ := by
  zucrd
  rw [chordPoly_n, show m - 1 + 1 = m by omega, Nat.mod_eq_of_lt by_simp_all,
    chordPoly_vtx_lt W i e₁ e₂ by_omega, chordPoly_vtx_m, show i + 1 + ztfte = i + m by omega]
theorem chordPoly_edge_m (W : Polygon) (i m : ℕ) (e₁ e₂ : Point) :
    (chordPoly W i m e₁ e₂).edge m = Chazelle.segment e₂ e₁ := by
  zucrd
  rw [chordPoly_n, Nat.mod_eq_of_lt by_simp_all, chordPoly_vtx_m, chordPoly_vtx_m1]
theorem chordPoly_edge_last (W : Polygon) (i : ℕ) {m : ℕ} (e₁ e₂ : Point) (hm : 0 < m) :
    (chordPoly W i m e₁ e₂).edge ztbl = Chazelle.segment e₁ (W.vtx (ztg % W.n)) := by
  zucrd
  rw [chordPoly_n, show m + 1 + 1 = m + 2 by ring, Nat.mod_self, chordPoly_vtx_m1,
    chordPoly_vtx_lt W i e₁ e₂ hm, add_zero]

/-- **The parity flip across an interior chord**: for a chord `[e₁, e₂]` of the interior with
`e₁` on edge `i`, `e₂` on edge `j`, the walk `chordPoly` has its boundary in `∂W ∪ [e₁, e₂]` and
its parity flips across every interior point of the chord. -/
theorem chord_parity_flip (hW : W.Simple) {e₁ e₂ : Point} (h12 : e₁.1 ≠ e₂.1)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e₁ e₂ s ∈ W.filled \ W.boundary)
    {i j : ℕ} (hi : i < W.n) (hj : j < W.n) (he₁ : e₁ ∈ W.edge i) (he₂ : e₂ ∈ W.edge j)
    {z : Point} (hz : z ∈ Chazelle.segment e₁ e₂) (hzD : z ∈ W.filled \ W.boundary) :
    ∃ Γ : Polygon, Γ.boundary ⊆ W.boundary ∪ Chazelle.segment e₁ e₂ ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        ztgd ∉ Γ.boundary ∧ ztfr ∉ Γ.boundary ∧
          parity Γ ztgd ≠ parity Γ ztfr := by
  zuerq
  have hij : i ≠ j := by
    zunq
    zukdt
    apply hmid.2
    exact ⟨i, hi, Geometry.segment_subset_of_convex ztemu he₁ he₂
      ztdox⟩
  set m := ztgko % W.n with hm
  have hmv : (0 < m ∧ m < W.n) ∧ ztjym % W.n = j := by
    rcases lt_or_gt_of_ne hij with h | h
    · have e : ztgko % W.n = j - i := by
        rw [show j + W.n - i = zttpx + W.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
      zukuz
      zubsc
      rw [show i + zttpx = j by omega, Nat.mod_eq_of_lt hj]
    · have e : ztgko % W.n = j + W.n - i := Nat.mod_eq_of_lt by_omega
      zukuz
      zubsc
      rw [show i + ztgko = j + W.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have hm0 := hmv.1.1
  have hjm := hmv.2
  set Γ := chordPoly W i m e₁ e₂ with hΓ
  have hΓn : Γ.n = m + 2 := chordPoly_n W i m e₁ e₂
  -- all edges but `m` are in the boundary of `W`
  have hedge : ∀ k, k < m + 2 → k ≠ m → Γ.edge k ⊆ W.boundary := by
    intro k hk hkm
    zuidv
    · rw [hΓ, chordPoly_edge_lt W i e₁ e₂ h]
      exact Existence.edge_subset_boundary W ztcv
    · rcases (show k = m - 1 ∨ k = m + 1 by omega) with rfl | rfl
      · rw [hΓ, chordPoly_edge_pen W i e₁ e₂ hm0, hjm]
        exact (Geometry.segment_subset_of_convex ztemu
          ztdte he₂).trans (Existence.edge_subset_boundary W hj)
      · rw [hΓ, chordPoly_edge_last W i e₁ e₂ hm0]
        exact (Geometry.segment_subset_of_convex ztemu he₁
          ztsxu).trans (Existence.edge_subset_boundary W hi)
  refine ⟨Γ, ?_, ?_⟩
  · rintro x ⟨k, hk, hxk⟩
    zukwp
    by_cases hkm : k = m
    · subst hkm
      right
      rw [hΓ, chordPoly_edge_m, Geometry.segment_comm] at hxk
      omega
    grind
  · have hmn : m < Γ.n := by_omega
    have hsucc : ztbl % Γ.n = m + 1 := by rw [hΓn]; simp
    have hzΓ : z ∈ Γ.edge m := by
      rw [hΓ, chordPoly_edge_m, Geometry.segment_comm]; exact hz
    have hne : (Γ.vtx m).1 ≠ (Γ.vtx ztzyr).1 := by
      rw [hsucc, hΓ, chordPoly_vtx_m, chordPoly_vtx_m1]; grind
    have hzu : z ≠ Γ.vtx m := by
      rw [hΓ, chordPoly_vtx_m]
      zunq
      exact hzD.2 (Existence.edge_subset_boundary W hj he₂)
    have hzv : z ≠ Γ.vtx ztzyr := by
      rw [hsucc, hΓ, chordPoly_vtx_m1]
      zunq
      exact hzD.2 (Existence.edge_subset_boundary W hi he₁)
    have hother : ∀ k, k < Γ.n → k ≠ m → z ∉ Γ.edge k := by
      zulnd
      zukwp
      exact hzD.2 (hedge k hk hkm hzk)
    exact parity_flip Γ hmn hzΓ hne hzu hzv hother

/-- The endpoints of a horizontal chord of the interior are on the boundary. -/
theorem hchord_end_mem_boundary {y a b : ℝ}
    (h : IsHChordIn ztjnp y a b) :
    (ztdv : Point) ∈ W.boundary ∧ (ztdy : Point) ∈ W.boundary := by
  have key : ∀ x : ℝ, (ztjw : Point) ∉ W.filled \ W.boundary →
      (∀ ε > (0 : ℝ), ∃ x', |x' - x| < ε ∧ (zthlc : Point) ∈ W.filled \ W.boundary) →
      (ztjw : Point) ∈ W.boundary := by
    intro x hx happ
    zuldq
    have hnf : (ztjw : Point) ∉ W.filled := by_simp_all
    zqbdg
    obtain ⟨x', hx', hx'D⟩ := happ r hr
    apply hball (show (zthlc : Point) ∈ ball (ztjw : Point) r by
      zufv
      simp only [sub_self, abs_zero]
      exact max_lt hx' hr)
    simp_all
  have hlt := h.lt
  refine ⟨key a h.left_not fun ε hε => ?_, key b h.right_not fun ε hε => ?_⟩
  · refine ⟨a + min ε zthu / 2, ?_, h.open_mem _ ?_ ?_⟩
    · grind
    · grind
    grind
  · refine ⟨b - min ε zthu / 2, ?_, h.open_mem _ ?_ ?_⟩
    · grind
    · grind
    grind

/-- The open part of `[(a, y), (b, y)]` of a horizontal chord. -/
theorem hchord_open {D : Set Point} {y a b : ℝ} (h : IsHChordIn D y a b) :
    ∀ s ∈ Ioo (0 : ℝ) 1, lerp (ztdv : Point) ztdy s ∈ D := by
  zugg
  have e : ztxbu := by
    zuenz
  zui
  zulfe

/-- **Every finite family of horizontal chords of the interior is a chord system.** -/
theorem chordSystem (hW : W.Simple) {F : Set ztf} (hfin : F.Finite)
    (hF : ∀ c ∈ F, ∃ y a b : ℝ, IsHChordIn ztjnp y a b ∧ c = hseg y a b) :
    ChordSystem ztjnp F where
  isOpen := isOpen_filled_sdiff_boundary hW
  finite := hfin
  hchord := hF
  walk := by
    intro c hc z hz hzD
    obtain ⟨y, a, b, h, rfl⟩ := hF c hc
    rw [FactsChain.hseg_eq_segment h.lt.le] at hz ⊢
    zuhhp
    obtain ⟨i, hi, hai⟩ := ha
    obtain ⟨j, hj, hbj⟩ := hb
    obtain ⟨Γ, hΓ, hflip⟩ := chord_parity_flip hW (by simp only; exact h.lt.ne) (hchord_open h)
      hi hj hai hbj hz hzD
    refine ⟨Γ, hΓ.trans ?_, hflip⟩
    grind

/-! ## Reach -/

/-- **Reach for a simple polygon with the interior on the left.** -/
theorem reach (hW : W.Simple) (hL : orient W = 1) {z : Point} (hz : z ∈ W.filled \ W.boundary)
    (hzv : ∀ i < W.n, z.2 ≠ (W.vtx i).2) :
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, (ztbtb : Point) ∈ W.filled \ W.boundary) ∧
      ∃ p < W.n, ∃ t ∈ Ioo (0 : ℝ) 1, sidePt W p t = (ztbfb : Point) ∧
        (W.vtx p).2 < (W.vtx ztwjb).2 := by
  obtain ⟨s, hs, hseg, hq⟩ := exists_first_exit (isOpen_filled_sdiff_boundary hW) hz
    (R := coordBound W + 1) (fun x hx => by
      have := (abs_le.1 (filled_subset_square W hx.1).1).2; linarith)
  refine ztopl
  set q : Point := ztbfb with hqdef
  -- the exit point is filled, hence on the boundary
  have hqf : q ∈ W.filled := by
    by_contra hnf
    zqbdg
    zudbs
    zucmx
    zufhm

    apply hball (show (ztpk : Point) ∈ ball q r by
      zufv
      zqbdd
      exact max_lt hεr hr)
    grind
  have hqb : q ∈ W.boundary := by
    simp_all
  have hqv : ∀ j, j < W.n → q ≠ W.vtx j := by_grind
  obtain ⟨p, hp, t, ht, hqe⟩ := exists_openEdge_of_mem_boundary W hqb hqv
  refine ⟨p, hp, t, ht, hqe.symm, ?_⟩
  zugyv

  have hq2 : ztyzg := by
    have := congrArg Prod.snd hqe; tauto
  rcases lt_trichotomy u.2 v.2 with h | h | h
  · zubh
  · grind
  · exfalso
    obtain ⟨r, hr, hloc⟩ := edge_local hW hL hp ht
    zudbs
    zucmw
    have hεr : ztiee := by zunbb; have := min_le_left r s; linarith
    have hεs : ztjaz := by_grind
    have hx : (ztpk : Point) ∈ ball ztia r := by
      rw [show sidePt W p t = q from hqe.symm, mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      zqbdd
      exact max_lt hεr hr
    have hq0 : zthot := by rw [hqe]; exact Geometry.det_lerp_self _ _ _
    have hdet : det u v (ztpk : Point) < 0 := by
      have e : ztwoj := by
        zubzu
      rw [e, hq0]; nlinarith
    exact (hloc _ hx).2.1 hdet (hseg _ by_grind).1

/-! ## The interior walk -/

/-- The reversed polygon. -/
theorem rev_n (Q : Polygon) : (⟨Q.vertices.reverse⟩ : Polygon).n = Q.n := by
  zufan
theorem rev_vtx (Q : Polygon) : ∀ k < Q.n, (⟨Q.vertices.reverse⟩ : Polygon).vtx k =
    Q.vtx ztcgz := by
  zugf
  have hk' : k < Q.vertices.reverse.length := by rw [List.length_reverse]; exact hk
  have hk2 : Q.n - 1 - k < Q.vertices.length := by
    have : Q.n = Q.vertices.length := rfl
    omega
  zuioz
  rw [List.getElem?_eq_getElem hk', List.getElem_reverse, List.getElem?_eq_getElem hk2]
  rfl

/-- **The interior walk** of a simple polygon is a simple polygon with the same boundary and
filled region, with the interior on its left. -/
theorem interiorWalk_spec {Q : Polygon} (hQ : Q.Simple) :
    (interiorWalk Q).Simple ∧ (interiorWalk Q).boundary = Q.boundary ∧
      (interiorWalk Q).filled = Q.filled ∧ orient ztkb = 1 := by
  classical
  zumsz
  zus
  · refine ⟨hQ, rfl, rfl, ?_⟩
    unfold orient; zumxk
  · set R : Polygon := ⟨Q.vertices.reverse⟩ with hR
    have hn := rev_n Q
    have hv := rev_vtx Q
    have hRs := Mountain.rev_simple hn hv hQ
    have hRf := Mountain.rev_filled hn hv
    refine ⟨hRs, Mountain.rev_boundary hn hv, hRf, ?_⟩
    zueru
    have hQo : orient Q = -1 := by unfold orient; zumxk
    obtain ⟨e1, e2⟩ := Mountain.rev_endpoints hn hv (k := 0) by_omega
    apply Mountain.orient_eq_of_eventually hRs (i := 0) by_grind
      (t := 1 / 2) ztfm ztp
    set e := Mountain.revEdge Q.n 0 with he
    have hel : ztsic := Mountain.revEdge_lt by_omega
    filter_upwards [eventually_offset_orient hQ hel (t := 1 / 2) ztfm]
      with δ hδ
    rw [hRf, e1, e2, one_mul, offset_reverse, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    simp_all

/-- **Walk axioms from a simple polygon** with the interior on its left. -/
theorem walkAx_of_simple (hW : W.Simple) (hL : orient W = 1) (M : Model)
    (hMW : M.W = W) (hD : M.D = W.filled \ W.boundary)
    (hAdm : M.Adm = {c | ∃ y a b : ℝ, IsHChordIn M.D y a b ∧ c = hseg y a b}) : WalkAx M := by
  obtain ⟨D, W', counted, Adm, Full⟩ := M
  simp only at hMW hD hAdm
  subst hMW hD hAdm
  exact {
    isOpen := isOpen_filled_sdiff_boundary hW
    preconn := filled_sdiff_boundary_connected hW
    nonempty := filled_sdiff_boundary_nonempty hW
    nd := fun p hp => simple_vtx_succ_ne hW hp
    trace := fun p hp t ht ht1 hD =>
      hD.2 (Existence.edge_subset_boundary _ hp (lerp_mem_segment _ _ ht ht1))
    clean := fun p hp t ht ht1 => clean hW hL hp ht ht1
    sys := fun F hF hfin => chordSystem hW hfin by_grind
    ends := by
      zung
      zuhs
      zuhhp
      have hopen := hchord_open h
      zuglx
      have hseg := FactsChain.hseg_eq_segment (y := y) h.lt.le
      refine ztxmj
      · rw [hseg]; exact walkEnd hW hL hab ha hopen
      · zukwd
        exact walkEnd hW hL hab.symm hb ztjnr
    reach := fun z hz hzv => reach hW hL hz hzv }
end FactsInterior

/-- **The interior model of a simple polygon satisfies the walk axioms.** -/
theorem walkAx_interiorModel {Q : Polygon} (hQ : Q.Simple) : WalkAx ztd := by
  zueuf
  exact FactsInterior.walkAx_of_simple hs ho _ rfl (by
    show Q.filled \ Q.boundary = _; simp_all) rfl

/-- **The chain model of a chain of a simple polygon satisfies the walk axioms.** -/
theorem walkAx_chainModel {C : Chain} (hP : C.P.Simple) : WalkAx ztc :=
  FactsChain.walkAx C hP

/-- **Every good model satisfies the walk axioms.** -/
theorem walkAx_of_goodModel {M : Model} (h : GoodModel M) : WalkAx M := by
  zudfa
  · exact walkAx_chainModel hC
  · exact walkAx_interiorModel hQ
end
end Chazelle.Core
end
namespace Chazelle.Core
namespace DownHost
@[expose] public section
open Set
open Chazelle.Chain (sidePt)
open Chazelle.Geometry (lerp lerp_zero lerp_one lerp_mem_segment)

/-- **Keys determine positions**: `p + t = p' + t'` with `t, t' ∈ [0, 1)` forces `p = p'` and
`t = t'`. -/
theorem key_inj {p p' : ℕ} {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : (p : ℝ) + t = p' + t') : p = p' ∧ t = t' := by
  zubnl

  grind

/-- The closed key interval of host edge `i` (of `N` edges, keys `κ`): `[κ i, κ (i+1)]`, and for
the last edge the wrapped interval `[κ (N-1), ∞) ∪ (-∞, κ 0]`. -/
def InKeyIv (κ : ℕ → ℝ) (N i : ℕ) (x : ℝ) : Prop :=
  if i + 1 < N then κ i ≤ x ∧ x ≤ κ ztg else κ i ≤ x ∨ x ≤ κ 0

/-- **Two closed key intervals of distinct edges meet only in a shared end key.** -/
theorem inKeyIv_inter {κ : ℕ → ℝ} {N i j : ℕ} (hmono : ∀ a b, a < b → b < N → κ a < κ b)
    (hi : i < N) (hj : j < N) (hij : i ≠ j) {x : ℝ} (hxi : InKeyIv κ N i x)
    (hxj : InKeyIv κ N j x) :
    ∃ k, k < N ∧ (k = i ∨ k = ztg % N) ∧ (k = j ∨ k = ztl % N) ∧ x = κ k := by
  -- strict monotonicity turns key comparisons into index comparisons
  have hle : ∀ a b, a < N → b < N → κ a ≤ κ b → a ≤ b := by
    grind
  zudnr
  unfold InKeyIv at hxi hxj
  -- wlog-free case analysis
  by_cases hi1 : i + 1 < N <;> by_cases hj1 : j + 1 < N <;>
    simp only [hi1, hj1, ↓reduceIte] at hxi hxj
  · -- both unwrapped
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · -- i < j: κ i ≤ x ≤ κ (i+1) ≤ κ j ≤ x
      zudxz

      zultb
      refine ⟨i + 1, hi1, Or.inr (Nat.mod_eq_of_lt hi1).symm, Or.inl rfl, ?_⟩
      grind
    · zuhdy
      have hji : ztsjd := by_omega
      zultb
      refine ⟨j + 1, hj1, Or.inl rfl, Or.inr (Nat.mod_eq_of_lt hj1).symm, ?_⟩
      grind
  · -- j is the last edge
    have hjN : j = N - 1 := by_omega
    have hsj : ztl % N = 0 := by rw [show j + 1 = N by omega, Nat.mod_self]
    rcases hxj with h | h
    · zudxz

      refine ⟨j, hj, Or.inr ?_, Or.inl rfl, by_grind⟩
      simp_all
    grind
  · -- i is the last edge
    have hsi : ztg % N = 0 := by rw [show i + 1 = N by omega, Nat.mod_self]
    rcases hxi with h | h
    · zuhdy
      have hij' : ztsjd := by_omega
      refine ⟨i, hi, Or.inl rfl, Or.inr ?_, by_grind⟩
      rw [hij', Nat.mod_eq_of_lt hj1]
    grind
  omega
variable (W : Polygon) (D : Set Point) (V : List Point) (pp : ℕ → ℕ) (tt : ℕ → ℝ)

/-- The key of host vertex `i`. -/
def keyOf (i : ℕ) : ℝ := (pp i : ℝ) + tt i

/-- Host edge `i` is an **arc edge**: all its points are walk points with keys in the closed
key interval of the edge. -/
def ArcEdge (i : ℕ) : Prop :=
  ∀ z ∈ Chazelle.segment ztxvz ztwzp,
    ∃ p, p < W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt W p t ∧
      InKeyIv ztjzn V.length i ztdj

/-- Host edge `i` is a **chord edge**: its open part lies in `D`. -/
def ChordEdge (i : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 → lerp ztxvz ztwzp s ∈ D

/-- **The data of a host polygon inscribed by keys** (see the module docstring). -/
structure KeyHost : Prop where
  three : 3 ≤ V.length
  wsimple : W.Simple
  pos_lt : ∀ i, i < V.length → pp i < W.n
  t_nonneg : ∀ i, i < V.length → 0 ≤ tt i
  t_lt : ∀ i, i < V.length → tt i < 1
  vtx_eq : ∀ i, i < V.length → V.getD i ztdr = sidePt W (pp i) (tt i)
  mono : ∀ i j, i < j → j < V.length → keyOf pp tt i < keyOf pp tt j
  disj : ∀ z ∈ D, z ∉ W.boundary
  edges : ∀ i, i < V.length → ArcEdge W V pp tt i ∨ ChordEdge D V i
  chord_disj : ∀ i j, i < V.length → j < V.length → i ≠ j → ChordEdge D V i →
    ChordEdge D V j → ∀ s s' : ℝ, 0 < s → s < 1 → 0 < s' → s' < 1 →
      lerp ztxvz ztwzp s ≠
        lerp (V.getD j ztdr) (V.getD (ztl % V.length) ztdr) s'
variable {W D V pp tt}

/-- A walk point lies on the walk's boundary. -/
theorem sidePt_mem_boundary {p : ℕ} (hp : p < W.n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    sidePt W p t ∈ W.boundary :=
  ⟨p, hp, lerp_mem_segment _ _ h0 h1⟩
namespace KeyHost
variable (h : KeyHost W D V pp tt)
include h
variable {i : ℕ}
theorem vtx_mem_boundary (hi : i < V.length) : V.getD i ztdr ∈ W.boundary := by
  rw [h.vtx_eq i hi]
  exact sidePt_mem_boundary zttlq zttlt (h.t_lt i hi).le
theorem succ_lt : ztg % V.length < V.length :=
  Nat.mod_lt _ (by have := h.three; omega)

/-- The key of a vertex lies in the key interval of each edge it ends. -/
theorem inKeyIv_self (_hi : i < V.length) :
    InKeyIv ztjzn V.length i (keyOf pp tt i) := by
  unfold InKeyIv
  zudlu
  · exact ⟨le_rfl, (h.mono i _ by_omega h1).le⟩
  simp
theorem inKeyIv_succ (hi : i < V.length) :
    InKeyIv ztjzn V.length i (keyOf pp tt (ztg % V.length)) := by
  unfold InKeyIv
  zudlu
  · zudjt
    exact ⟨(h.mono i _ by_omega h1).le, le_rfl⟩
  · rw [show i + 1 = V.length by omega, Nat.mod_self]
    simp

/-- **A point of an edge off `D`** is a walk point whose key lies in the edge's interval. -/
theorem pt_key (hi : i < V.length) {z : Point}
    (hz : z ∈ Chazelle.segment ztxvz ztwzp)
    (hzD : z ∉ D) :
    ∃ p, p < W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt W p t ∧
      InKeyIv ztjzn V.length i ztdj := by
  rcases h.edges i hi with ha | hc
  · tauto
  · zubxv
    zunm
    · zuji
      · tauto
      · subst hs1
        have hk := h.succ_lt (i := i)
        refine ⟨pp _, h.pos_lt _ hk, tt _,
          h.t_nonneg _ hk, h.t_lt _ hk, ?_, h.inKeyIv_succ hi⟩
        rw [lerp_one, h.vtx_eq _ hk]
    · zumqe
      refine ⟨pp i, h.pos_lt i hi, tt i, h.t_nonneg i hi, h.t_lt i hi, ?_, h.inKeyIv_self hi⟩
      rw [lerp_zero, h.vtx_eq i hi]

/-- A walk point at the key of vertex `k` is vertex `k`. -/
theorem eq_vtx_of_key {k : ℕ} (hk : k < V.length) {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hkey : (p : ℝ) + t = keyOf pp tt k) : sidePt W p t = V.getD k ztdr := by
  obtain ⟨rfl, rfl⟩ := key_inj ht ht1 (h.t_nonneg k hk) (h.t_lt k hk) hkey
  exact (h.vtx_eq k hk).symm

/-- **The simplicity criterion.** -/
theorem simple : (⟨V⟩ : Polygon).Simple := by
  have hn : (⟨V⟩ : Polygon).n = V.length := rfl
  have hv : ∀ i, (⟨V⟩ : Polygon).vtx i = V.getD i ztdr := fun _ => rfl
  refine ⟨h.three, ?_, ?_⟩
  · zuvb
    rw [hv, hv, h.vtx_eq i hi, h.vtx_eq j hj] at hij
    obtain ⟨hp, ht⟩ := FactsInterior.pos_unique h.wsimple zttlq (h.pos_lt j hj)
      zttlt (h.t_lt i hi) (h.t_nonneg j hj) (h.t_lt j hj) hij
    zuct
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := h.mono i j hlt hj
      zulbw
    · have := h.mono j i hlt hi
      zulbw
  · zuvb
    zuldc
    · rintro z ⟨hzi, hzj⟩
      simp only [Polygon.edge, hn, hv] at hzi hzj
      by_cases hzD : z ∈ D
      · -- both edges are chord edges, and `z` is in both open parts
        exfalso
        have hopen : ∀ k, k < V.length → z ∈ Chazelle.segment ztzux
            ztypz →
            ChordEdge D V k ∧ ∃ s : ℝ, 0 < s ∧ s < 1 ∧
              z = lerp ztzux ztypz s := by
          intro k hk hzk
          have hzb := h.disj z hzD
          obtain ⟨s, hs0, hs1, hzs⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzk
          have hs0' : ztxx := by
            rcases hs0.lt_or_eq with h' | h'
            · zuclh
            · subst h'; rw [lerp_zero] at hzs
              exact absurd (hzs ▸ h.vtx_mem_boundary hk) hzb
          have hs1' : ztdrm := by
            rcases hs1.lt_or_eq with h' | h'
            · zuclh
            · subst h'; rw [lerp_one] at hzs
              exact absurd (hzs ▸ h.vtx_mem_boundary h.succ_lt) hzb
          refine ⟨?_, s, hs0', hs1', hzs⟩
          rcases h.edges k hk with ha | hc
          · obtain ⟨p, hp, t, ht0, ht1, hzp, -⟩ := ha z hzk
            exact absurd ztpcg hzb
          omega
        obtain ⟨hci, s, hs0, hs1, hzs⟩ := hopen i hi hzi
        obtain ⟨hcj, s', hs0', hs1', hzs'⟩ := hopen j hj hzj
        exact h.chord_disj i j hi hj hij hci hcj s s' hs0 hs1 hs0' hs1' (hzs.symm.trans hzs')
      · obtain ⟨p, hp, t, ht0, ht1, hzp, hki⟩ := h.pt_key hi hzi hzD
        obtain ⟨p', hp', t', ht0', ht1', hzp', hkj⟩ := h.pt_key hj hzj hzD
        obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique h.wsimple hp hp' ht0 ht1 ht0' ht1'
          (hzp.symm.trans hzp')
        obtain ⟨k, hk, hki', hkj', hx⟩ := inKeyIv_inter h.mono hi hj hij hki hkj
        have hzk := hzp.trans (h.eq_vtx_of_key hk ht0 ht1 hx)
        simp only [Polygon.commonEndpoints, hn, hv]
        zujx
        · rcases hki' with rfl | rfl
          · simp_all
          simp_all
        · rcases hkj' with rfl | rfl
          · simp_all
          simp_all
    · rintro z ⟨hz1, hz2⟩
      simp only [Polygon.edge, hn, hv]
      zujx
      · rcases hz1 with rfl | rfl
        · zulwy
        · zulwz
      · rcases hz2 with rfl | rfl
        · zulwy
        · zulwz
end KeyHost
end
end DownHost
namespace Mir
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (IsHChordIn)
open Chazelle.Visibility (hseg rayPt)
variable {Q : Polygon}

/-- The interior of the mirrored polygon. -/
theorem mir_interior (Q : Polygon) :
    Q.mir.filled \ Q.mir.boundary = mir '' ztrx := by
  rw [mir_filled, mir_boundary, image_sdiff mir_injective]
theorem hitSet_mir (Q : Polygon) (p : Point) (σ : ℝ) :
    Visibility.hitSet Q.mir ztqtn (-σ) = Visibility.hitSet Q p σ := by
  zufso
  simp only [Visibility.hitSet, mem_ofPred_eq, ← mir_rayPt, mir_boundary, mem_image_mir, mir_mir]
theorem chordSet_mir (Q : Polygon) (i : ℕ) (σ : ℝ) :
    Visibility.chordSet Q.mir i (-σ) = mir '' Visibility.chordSet Q i σ := by
  unfold Visibility.chordSet Visibility.chordEnd Visibility.chordParam Visibility.hitParam
  rw [mir_vtx, hitSet_mir, mir_segment, mir_rayPt]
theorem dirInterior_mir (Q : Polygon) (i : ℕ) (σ : ℝ) :
    Visibility.DirInterior Q.mir i (-σ) ↔ Visibility.DirInterior Q i σ := by
  unfold Visibility.DirInterior
  simp only [mir_vtx, ← mir_rayPt, mir_interior, mem_image_mir, mir_mir]

/-- **The vertex chords of the mirrored polygon.** -/
theorem chords_mir (Q : Polygon) : Visibility.chords Q.mir = mirF (Visibility.chords Q) := by
  zubcj
  zudux
  constructor
  · rintro ⟨i, σ, hi, hσ, hD, rfl⟩
    zukxr
    refine ⟨i, -σ, hi, by_grind, ?_, ?_⟩
    · rw [← dirInterior_mir, neg_neg]; exact hD
    · rw [← neg_neg σ, chordSet_mir, image_mir_image_mir, neg_neg]
  · rintro ⟨i, σ, hi, hσ, hD, hc⟩
    refine ⟨i, -σ, by_simp_all, by_grind,
      (dirInterior_mir Q i σ).2 hD, ?_⟩
    rw [chordSet_mir, ← hc, image_mir_image_mir]

/-- **The horizontal chords of the mirrored interior.** -/
theorem adm_mir (D : Set Point) :
    {c | ∃ y a b : ℝ, IsHChordIn zthiq y a b ∧ c = hseg y a b} =
      mirF {c | ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b} := by
  zubcj
  zudux
  constructor
  · rintro ⟨y, a, b, hch, rfl⟩
    refine ⟨y, -b, -a, ?_, hseg_mir y a b⟩
    zugfs
  · rintro ⟨y, a, b, hch, hc⟩
    refine ⟨y, -b, -a, isHChordIn_mir.2 hch, ?_⟩
    zugxw
theorem interiorWalk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  zufdi
  · rfl
  · zuhcp

/-- **The interior walk of the mirrored polygon.** -/
theorem walkMir_interior (hQ : Q.Simple) :
    WalkMir ztkb (interiorWalk Q.mir) ztnv := by
  have h3 := Chazelle.Jordan.simple_three_le hQ
  have hL := leftInside_mir Q hQ
  have hWn := interiorWalk_n Q
  refine ⟨by rw [interiorWalk_n, interiorWalk_n, mir_n], by_omega, fun j hj => ?_⟩
  zvnux at hj ⊢
  have hidx : (Q.n - 1 + Q.n - j) % Q.n = Q.n - 1 - j := by
    rw [show Q.n - 1 + Q.n - j = ztjlj + Q.n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt by_omega]
  zujiz
  zumsz
  by_cases hQL : Mountain.LeftInside Q
  · have hM : ¬ Mountain.LeftInside Q.mir := fun h => hL.1 h hQL
    rw [ite_eq_right hM, ite_eq_left hQL, FactsInterior.rev_vtx _ j by_simp_all, mir_n,
      mir_vtx]
  · have hM : Mountain.LeftInside Q.mir := hL.2 hQL
    rw [ite_eq_left hM, ite_eq_right hQL, FactsInterior.rev_vtx _ _ by_omega, mir_vtx,
      show Q.n - 1 - ztjlj = j by omega]

/-- **The interior model of the mirrored polygon is the mirrored interior model.** -/
theorem modelMir_interior (hQ : Q.Simple) :
    ModelMir ztd ztcvu ztnv where
  D := mir_interior Q
  walk := walkMir_interior hQ
  counted _ _ := Iff.rfl
  Adm := by
    show {c | ∃ y a b : ℝ, IsHChordIn (Q.mir.filled \ Q.mir.boundary) y a b ∧ c = hseg y a b} = _
    rw [mir_interior]; exact adm_mir _
  Full := chords_mir Q
end
end Mir
@[expose] public section
theorem cutStructureNC : CutStructureSpecNC := by
  zufxh
  zugc

  refine ⟨fun p t hp ht0 ht1 hcut => hW.faces_existsUnique hAdm hfin hp ztcoy hcut,
    fun U hU => hW.exists_faces hAdm hfin hU, ?_⟩
  intro p p' t t' U U' hU hU' hp hp' ht0 ht1 ht0' ht1' hcut hcut' hf hf'
  exact hW.eq_iff_not_separates hAdm hfin hU hU' hp hp' ztcoy ⟨ht0', ht1'⟩ hcut hcut' hf hf'
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj sideInArc_swap)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

/-! ## Cyclic order of keys -/

/-- Closing tactic for the case analyses of cyclic betweenness. -/
macro "cyc_close" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor! <;> linarith) | (right; constructor! <;> linarith)
  | (left; linarith) | (right; linarith)))

/-- If `y` is strictly between `a` and `b` and `k ≠ b` is not, then `y` is strictly between `k`
and `b`. -/
theorem cyc_sub {a b y k : ℝ} (hy : sideInArc a b y) (hk : ¬ sideInArc a b k) (hkb : k ≠ b) :
    sideInArc k b y := by
  have := lt_or_gt_of_ne hkb
  unfold sideInArc at *
  grind

/-- Rotation: for distinct `a, b, c`, `c` is between `a` and `b` iff `b` is not between `a`
and `c`. -/
theorem cyc_rot {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    sideInArc a b c ↔ ¬ sideInArc a c b := by
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne hac
  have := lt_or_gt_of_ne hbc
  zuiq

/-- Two keys in an interval free of `A` and `B` are on the same side of `A, B`. -/
theorem cyc_nosep {a x y A B : ℝ} (hy : sideInArc a x y) (hA : ¬ sideInArc a x A)
    (hB : ¬ sideInArc a x B) (hxA : x ≠ A) (hxB : x ≠ B) (hAB : A ≠ B) :
    sideInArc A B y ↔ sideInArc A B x := by
  have := lt_or_gt_of_ne hxA
  have := lt_or_gt_of_ne hxB
  have := lt_or_gt_of_ne hAB
  unfold sideInArc at *
  grind

/-- Extending an arc `(a, b)` a little past its end `b` (to `x`, with no `a` in `(b, x]`). -/
theorem cyc_ext {a b x y k : ℝ} (hab : a ≠ b) (hy : sideInArc a b y) (hbx : b < x)
    (ha : ¬ (b < a ∧ a ≤ x)) (hk : ¬ sideInArc a b k) (hkb : k ≠ b) (hkx : ¬ ztnro) :
    sideInArc a x y ∧ ¬ sideInArc a x k ∧ x ≠ k := by
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne hkb
  zusk
  · unfold sideInArc at *
    grind
  · unfold sideInArc at *
    grind
  grind

/-- Past the end `b` of an interval free of `k`, a key `x` is between `b` and `k`. -/
theorem cyc_after {b x k : ℝ} (hbx : b < x) (hkb : k ≠ b) (hkx : ¬ ztnro) :
    sideInArc b k x := by
  have := lt_or_gt_of_ne hkb
  unfold sideInArc at *
  simp_all

/-- Two intervals ending at `b` and free of each other's starts have the same start. -/
theorem cyc_start_eq {a a' b : ℝ} (ha : a ≠ b) (ha' : a' ≠ b) (h1 : ¬ sideInArc a b a')
    (h2 : ¬ sideInArc a' b a) : a = a' := by
  zuct
  have := lt_or_gt_of_ne ha
  have := lt_or_gt_of_ne ha'
  have := lt_or_gt_of_ne hne
  unfold sideInArc at *
  grind
namespace WalkAx
variable {M : Model}

/-! ## Cuts -/

/-- The chord points off the domain are finitely many. -/
theorem finite_chord_ends (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) : (⋃ c ∈ F, c \ M.D).Finite := by
  refine hfin.biUnion fun c hc => ?_
  obtain ⟨a, b, -, rfl, -, hopen, -, -⟩ := hM.ends c ztlz
  refine (Set.toFinite {a, b}).subset ?_
  zujgi
  zufr
  zunl
  · zuqy
    · simp_all
    simp_all
  · zuhha

/-- **The cut keys are finitely many.** -/
theorem finite_cuts (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    {x : ℝ | M.IsCut F x}.Finite := by
  set E := ⋃ c ∈ F, c \ M.D with hE
  have hEf := hM.finite_chord_ends hF hfin
  have hsub : {x : ℝ | M.IsCut F x} ⊆
      ⋃ p ∈ Iio M.W.n, ⋃ e ∈ E, (fun t : ℝ => (p : ℝ) + t) ''
        {t : ℝ | sidePt M.W p t = e} := by
    zuecj
    simp only [mem_iUnion, mem_Iio, mem_image, mem_ofPred_eq]
    refine ⟨p, hA.1, sidePt M.W p t, ?_, t, rfl, rfl⟩
    rw [hE, mem_iUnion₂]
    exact ⟨c, hc, hA.2.2.2.1, hM.trace p hA.1 t hA.2.1 hA.2.2.1.le⟩
  refine Set.Finite.subset ((finite_Iio _).biUnion fun p hp => hEf.biUnion fun e _ => ?_) hsub
  refine Set.Finite.image _ (Set.Subsingleton.finite ?_)
  intro t ht t' ht'
  exact lerp_injective_aux ztoam (ht.trans ht'.symm)
where
  lerp_injective_aux {u v : Point} (huv : u ≠ v) {t t' : ℝ} (h : lerp u v t = lerp u v t') :
      t = t' := Geometry.lerp_injective huv h

/-- **Uniqueness of the attachment at a point**: an admissible chord is attached at most once at
each of its points. -/
theorem attach_unique (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p p' : ℕ} {t t' : ℝ}
    (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c p' t')
    (heq : sidePt M.W p t = sidePt M.W p' t') : p = p' ∧ t = t' := by
  zuct
  obtain ⟨a, b, hab, rfl, -, hopen, ha, hb⟩ := hM.ends c hc
  -- the other endpoint
  obtain ⟨e', hend, hseq, he'⟩ : ∃ e', WalkEnd M.W (Chazelle.segment a b) (sidePt M.W p t) ∧
      Chazelle.segment a b = Chazelle.segment ztbp e' ∧ e' ≠ sidePt M.W p t := by
    zuebs
    · grind
    · exact ⟨a, by_simp_all, by zunow, by_simp_all⟩
  obtain ⟨-, hdisj⟩ := hend
  obtain ⟨r, hr, hsep⟩ := hdisj p p' t t' hA.1 hA.2.1 hA.2.2.1 hA'.1 hA'.2.1 hA'.2.2.1
    (fun h1 h2 => hne ztwo) rfl heq.symm
  obtain ⟨-, -, -, -, r₁, hr₁, h₁⟩ := hA
  obtain ⟨-, -, -, -, r₂, hr₂, h₂⟩ := hA'
  zuhok
  set ρ := min r ztcal with hρ
  have hρ0 := lt_min hr ztftb
  have hn : 0 < dist q e' + 1 := by_positivity
  set s := min (ρ / ztero) ztcn with hs
  have hs0 : ztxx := lt_min (div_pos hρ0 hn) by_norm_num
  zuiai
  set x := lerp q e' s with hx
  have hxc : x ∈ Chazelle.segment q e' := lerp_mem_segment _ _ hs0.le hs1.le
  have hxq := Chazelle.Jordan.lerp_ne_left (Ne.symm he') hs0
  have hdist : dist x q < ρ := by
    have e : dist x q = s * dist q e' := by
      rw [hx, dist_comm, dist_eq_norm, dist_eq_norm]
      have : q - lerp q e' s = s • (q - e') := by
        zubvl
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    zui
    have h1 : s ≤ ρ / ztero := min_le_left _ _
    calc s * dist q e' < s * ztero := by_nlinarith
      _ ≤ ρ / ztero * ztero := mul_le_mul_of_nonneg_right h1 hn.le
      _ = ρ := div_mul_cancel₀ _ hn.ne'
  rw [hseq] at h₁ h₂
  have hl₁ := h₁ x hxc hxq (hdist.trans_le ztxju)
  have hl₂ := h₂ x hxc by_grind (by
    zvnbo; exact hdist.trans_le ztxjv)
  exact hsep x (by rw [mem_ball]; exact hdist.trans_le ztff) hl₁ hl₂

/-- **The other attachment** of an attached admissible chord, at its other endpoint. -/
theorem other_attach (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ p' t', SideAttach M.W c p' t' ∧ sidePt M.W p' t' ≠ sidePt M.W p t := by
  obtain ⟨a, b, hab, hcab, -, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ :=
    hM.ends c hc
  grind

/-! ## The region of the exit chords -/
variable {F : Set (Set Point)}
/-- **A region is a region of its exit chords**: if `U` is a region of `F`, it is the component
of `u ∈ U` in the free set of the chords of `F` touching `U`. -/
theorem region_of_exits (hsys : ChordSystem M.D F) {U : Set Point}
    (hU : U ∈ regionsIn M.D F) {u : Point} (hu : u ∈ U) :
    U = connectedComponentIn (freeIn M.D {c | c ∈ F ∧ TouchesIn M.D c U}) u := by
  zupf
  zufuc
  have hUF := Chazelle.Chain.regionsIn_subset hU
  have hUT := hUF.trans zthag
  have hUc := Chazelle.Chain.regionsIn_isPreconnected hU
  zufue
  apply Subset.antisymm (hUc.subset_connectedComponentIn hu hUT)
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUo
    ⟨u, mem_connectedComponentIn (hUT hu), hu⟩ ?_
  rintro x ⟨hxc, hxK⟩
  have hxT := connectedComponentIn_subset _ _ hxK
  have hxF : x ∈ freeIn M.D F := by
    refine ⟨hxT.1, ?_⟩
    rintro ⟨c, hc, hxc'⟩
    exact hxT.2 ⟨c, ⟨hc, x, ⟨hxc', hxT.1⟩, hxc⟩, hxc'⟩
  have hpre : ztrfr :=
    hUc.subset_closure (subset_inter subset_closure hUF) inter_subset_left
  have := hpre.subset_connectedComponentIn ⟨subset_closure hu, hUF hu⟩ inter_subset_right
  rw [← Chazelle.Chain.regionsIn_eq_component hU hu] at this
  grind

/-! ## The arcs of a region -/

/-- A position just after a cut key, inside a walk edge, with no cut in between. -/
theorem exists_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} {t : ℝ} (_hp : p < M.W.n) (_ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ t' ∈ Ioo t 1, ∀ k, M.IsCut F k → ¬ ((p : ℝ) + t < k ∧ k ≤ p + t') := by
  zukbl
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k ∈ {x : ℝ | M.IsCut F x},
      ¬ ((p : ℝ) + t < k ∧ k ≤ p + zthkr) := by
    refine (hcf.eventually_all).2 ?_
    intro k _
    by_cases hk : (p : ℝ) + t < k
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < k - ztk by linarith)] with ε hε
      grind
    simp_all
  obtain ⟨ε, h1, h2⟩ := (hall.and (Ioo_mem_nhdsGT ztcqc)).exists
  exact ⟨t + ε, by_grind, by_simp_all⟩

/-- A position inside an arc, just after its start. -/
theorem exists_in_arc {U : Set Point} {a b : ℝ}
    {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : 0 ≤ t) (ht1 : t < 1) (ha : a = p + t)
    (harc : ∀ x, sideInArc a b x → ¬ M.IsCut F x)
    (hfac : ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → sideInArc a b ztk →
      M.Faces p t U) :
    ∃ t' ∈ Ioo (0 : ℝ) 1, sideInArc a b ztdvo ∧ ¬ M.IsCut F ztdvo ∧ M.Faces p t' U := by
  set ε := if a < b then min ztca zthu / 2 else ztca / 2 with hε
  have hε0 : ztbad := by
    grind
  have hε1 : ε < 1 - t := by
    grind
  have hin : sideInArc a b ztzxl := by
    zuiq

  grind

/-- Unpacking an arc of a nonempty family. -/
theorem arc_cuts (hne : F.Nonempty) {U : Set Point} {a b : ℝ}
    (h : M.IsArc F U a b) : M.IsCut F a ∧ M.IsCut F b ∧ a ≠ b := by
  rcases h.2.2.2.2.1 with h' | ⟨h', -⟩
  · zuclh
  simp_all

/-- **The end of an arc carries an exit chord**: some chord of `F` touching `U` is attached at
the end key of every arc of `U`. -/
theorem exists_exit_at_end (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hne : F.Nonempty) {U : Set Point} (hU : U ∈ M.regions F) {a b : ℝ}
    (harc : M.IsArc F U a b) :
    ∃ c ∈ {c | c ∈ F ∧ TouchesIn M.D c U}, ∃ p t, SideAttach M.W c p t ∧ b = p + t := by
  zupf
  zufuc
  zuljg
  zudr
  zufjt
  zuddq
  zulwf
  -- a position `y` inside the arc
  obtain ⟨c₁, hc₁, p₁, t₁, hA₁, ha₁⟩ := hcuta
  obtain ⟨ty, hty, hyin, hycut, hyf⟩ :=
    exists_in_arc (M := M) hA₁.1 hA₁.2.1 hA₁.2.2.1 ha₁ hfree hfac
  -- a position `x` just after the end
  obtain ⟨c₀, hc₀, pb, tb, hB₀, hb⟩ := hcutb
  obtain ⟨tx, htx, hxfree⟩ := hM.exists_after hF hfin hB₀.1 hB₀.2.1 hB₀.2.2.1
  have htx' : tx ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hB₀.2.1, htx.1], htx.2⟩
  have hbx : b < pb + tx := by_grind
  have hxcut : ztpqv := fun h => hxfree _ h ⟨by_linarith, le_rfl⟩
  rw [← hb] at hxfree
  -- the region of `F` faced at `x` is `U`
  obtain ⟨V, hV, hxV⟩ := hM.exists_faces_of_not_cut hF hfin hB₀.1 htx' hxcut
  zuov
  zuvh
  have hVfree :=
    (Chazelle.Chain.regionsIn_subset hV).trans zthag
  zuiob
  have hVVT :=
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVfree
  zuequ

  have hUTr : ztumm := by
    zummu
    exact ⟨u, ((Chazelle.Chain.regionsIn_subset hU).trans
      zthag) hu, rfl⟩
  have hxVT := hxV.mono fun δ h => hVVT h
  zudob
  have hkeys : ∀ k, M.IsCut T k → ¬ sideInArc a b k ∧ k ≠ b ∧ ¬ (b < k ∧ k ≤ pb + tx) := by
    zugf
    refine ztrak
    zunq
    tauto
  have ha_after := (hxfree a ⟨c₁, hc₁, p₁, t₁, hA₁, ha₁⟩)
  have hsame : VT = U := by
    refine (hM.eq_iff_not_separates by_grind hTfin hVTr hUTr hB₀.1 hA₁.1 htx'
      hty by_grind by_grind hxVT hyf).2 ?_
    zuctm
    have hkA := hkeys _ ztkjj
    have hkB := hkeys _ ztkjm
    obtain ⟨hy', hA', hxA⟩ := cyc_ext hab hyin hbx ha_after hkA.1 hkA.2.1 hkA.2.2
    obtain ⟨-, hB', hxB⟩ := cyc_ext hab hyin hbx ha_after hkB.1 hkB.2.1 hkB.2.2
    have h := cyc_nosep hy' hA' hB' hxA hxB ztlqm
    grind
  zuhxr
  have hVeq : V = U := by
    zuidh
    · zubh
    · exact absurd (h.le_bot ⟨hv, hVU hv⟩) zthxd
  zuktg
  -- the chord `c₀` at `b` separates `y` from `x`
  obtain ⟨pa₀, ta₀, hA₀, hA₀ne⟩ := hM.other_attach ztmkp hB₀
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split ztmkp hA₀ hB₀ hA₀ne
  have hkA₀ : ztidq := ⟨c₀, hc₀, pa₀, ta₀, hA₀, rfl⟩
  have hkne : (pa₀ : ℝ) + ta₀ ≠ b := by rw [hb]; exact key_ne_of_pt_ne hA₀ hB₀ hA₀ne
  have hyA : sideInArc zttvt ztbd (p₁ + ty) := by
    rw [← hb]; exact cyc_sub hyin by_grind hkne
  have hxA : sideInArc ztbd zttvt (pb + tx) := by
    rw [← hb]; exact cyc_after hbx hkne by_grind
  have hU1 := hM.region_subset_of_sector hc₀ hU hA₁.1 hty hyf
    (hK₁ p₁ hA₁.1 ty hty.1.le hty.2 hyA)
  have hU2 := hM.region_subset_of_sector hc₀ hU hB₀.1 htx' hxV
    (hK₂ pb hB₀.1 tx htx'.1.le htx'.2 hxA)
  exact hne ztdas

/-- A position inside an arc of a nonempty family, facing the region, off the cuts. -/
theorem exists_pos_in_arc (hne : F.Nonempty) {U : Set Point} {a b : ℝ}
    (harc : M.IsArc F U a b) :
    ∃ p < M.W.n, ∃ t ∈ Ioo (0 : ℝ) 1, sideInArc a b ztk ∧ ¬ M.IsCut F ztk ∧
      M.Faces p t U := by
  obtain ⟨hcuta, -, -⟩ := arc_cuts hne harc
  zuddq
  obtain ⟨c₁, -, p₁, t₁, hA₁, ha₁⟩ := hcuta
  obtain ⟨t, ht, h1, h2, h3⟩ := exists_in_arc (M := M) hA₁.1 hA₁.2.1 hA₁.2.2.1 ha₁ hfree hfac
  exact ⟨p₁, hA₁.1, t, ht, h1, h2, h3⟩

/-- **Arcs and exit chords alternate**: a region of a finite admissible family has finitely many
arcs, and at most `deg + 1` of them (at most `deg` when the family is nonempty). -/
theorem arcs_bound (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.Finite ∧
      {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.ncard ≤ M.deg F U + 1 := by
  classical
  set S := {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2} with hS
  zuqx
  · have hsub : S ⊆ {ztbxh} := by
      rintro ⟨a, b⟩ h
      rcases h.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, rfl, rfl⟩
      · simp_all
      · rfl
    refine ⟨(finite_singleton _).subset hsub, ?_⟩
    calc S.ncard ≤ ({ztbxh} : Set _).ncard :=
          ncard_le_ncard hsub ztgir
      _ = 1 := ncard_singleton _
      _ ≤ M.deg ∅ U + 1 := Nat.le_add_left _ _
  · zupf
    zukbl
    have hSsub : S ⊆ {x | M.IsCut F x} ×ˢ {x | M.IsCut F x} := fun ab h =>
      ⟨(arc_cuts hne h).1, (arc_cuts hne h).2.1⟩
    have hSfin := (hcf.prod hcf).subset hSsub
    refine ⟨hSfin, ?_⟩
    let f : ℝ × ℝ → Set Point := fun ab =>
      if h : ∃ c ∈ T, ∃ p t, SideAttach M.W c p t ∧ ab.2 = p + t then h.choose else ∅
    have hf : ∀ ab ∈ S, f ab ∈ T ∧ ∃ p t, SideAttach M.W (f ab) p t ∧ ab.2 = p + t := by
      intro ab hab
      have h := hM.exists_exit_at_end hF hfin hne hU hab
      grind
    have hinj : InjOn f S := by
      rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
      obtain ⟨hcT, p, t, hA, hb⟩ := hf _ hab
      obtain ⟨-, p', t', hA', hb'⟩ := hf _ hab'
      zvnbo at hA'
      simp only at hb hb'
      set c := f ztvk
      have hc := hcT.1
      obtain ⟨-, hcutb, hab0⟩ := arc_cuts hne hab
      obtain ⟨-, hcutb', hab0'⟩ := arc_cuts hne hab'
      have hfree := hab.2.2.2.2.2.1
      have hfree' := hab'.2.2.2.2.2.1
      by_cases hbb : b = b'
      · subst hbb
        have hcuta := (arc_cuts hne hab).1
        have hcuta' := (arc_cuts hne hab').1
        exact Prod.ext (cyc_start_eq hab0 hab0' by_grind
            by_grind) rfl
      · exfalso
        have hAB : sidePt M.W p' t' ≠ sidePt M.W p t := by
          zuq
          zufkq
          grind
        obtain ⟨K₁, K₂, hne', ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split ztlz hA' hA hAB
        obtain ⟨py, hpy, ty, hty, hyin, -, hyf⟩ := exists_pos_in_arc hne hab
        obtain ⟨py', hpy', ty', hty', hyin', -, hyf'⟩ := exists_pos_in_arc hne hab'
        have h1 : sideInArc ztjg ztk ztdhy := by
          zuinl
          exact cyc_sub hyin (fun h => hfree _ h hcutb') (Ne.symm hbb)
        have h2 : sideInArc ztk ztjg (py' + ty') := by
          zuinl
          exact cyc_sub hyin' (fun h => hfree' _ h hcutb) hbb
        have hU1 := hM.region_subset_of_sector hc hU hpy hty hyf (hK₁ py hpy ty hty.1.le hty.2 h1)
        have hU2 := hM.region_subset_of_sector hc hU hpy' hty' hyf'
          (hK₂ py' hpy' ty' hty'.1.le hty'.2 h2)
        zuvh
        exact hne' ((connectedComponentIn_eq (hU1 hu)).trans
          (connectedComponentIn_eq (hU2 hu)).symm)
    calc S.ncard ≤ T.ncard :=
          ncard_le_ncard_of_injOn f by_grind hinj (hfin.subset by_grind)
      _ ≤ M.deg F U + 1 := Nat.le_succ _
end WalkAx
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section

/-- **WP-B: arcs and exit chords alternate** (`ArcsPerRegionSpec`). -/
theorem arcsPerRegion : ArcsPerRegionSpec := by
  intro M Q F hM hF U hU
  exact (walkAx_of_goodModel hM).arcs_bound hF.2.1 hF.1 hU
open Set Filter Topology Metric Finset
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)

/-! ## The counting core for trees of bounded degree -/
section Counting
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Counting core of Lemma 2.3, degree `≤ Δ`.**  In a finite tree of maximum degree `≤ Δ`
with node weights `w` such that every edge at a node of degree `< 3` has total weight `≥ γ`,
`(N - 1) γ ≤ 2 (Δ + 2) ∑ w`. -/
theorem card_mul_le_of_granular_deg (hG : G.IsTree) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (w : V → ℕ) (γ : ℕ)
    (hgran : ∀ u v, G.Adj u v → ztler → γ ≤ w u + w v) :
    ztlen * γ ≤ 2 * ztufa * ∑ v, w v := by
  classical
  zufaf
  set DL := (univ : Finset G.Dart).filter (fun d => d.fst ∈ L) with hDL
  have h1 : Fintype.card V - 1 ≤ 2 * #DL := by
    rw [hDL, Chazelle.Chain.card_dart_fst_filter G L]
    exact Chazelle.Chain.card_sub_one_le_two_mul_sum_low G hG
  have h2 : #DL * γ ≤ ∑ d ∈ DL, ztqyk := by
    rw [card_eq_sum_ones, sum_mul, one_mul]
    apply sum_le_sum
    zuip
    have hdL : G.degree d.fst ≤ 2 := by_grind
    exact hgran d.fst d.snd d.adj by_omega
  have h3 : ∑ d ∈ DL, w d.fst ≤ 2 * ∑ v, w v := by
    rw [hDL, Chazelle.Chain.sum_dart_fst_filter G L w, mul_sum]
    calc ∑ v ∈ L, G.degree v * w v ≤ ∑ v ∈ L, 2 * w v :=
          sum_le_sum fun v hv => Nat.mul_le_mul_right _ by_grind
      _ ≤ ∑ v, 2 * w v := sum_le_sum_of_subset ztwge
  have h4 : ∑ d ∈ DL, w d.snd ≤ Δ * ∑ v, w v := by
    calc ∑ d ∈ DL, w d.snd ≤ ∑ d : G.Dart, w d.snd := sum_le_sum_of_subset ztwge
      _ = ∑ v, G.degree v * w v := by
          rw [Chazelle.Chain.sum_dart_snd G, Chazelle.Chain.sum_dart_fst G]
      _ ≤ ∑ v, Δ * w v := sum_le_sum fun v _ => Nat.mul_le_mul_right _ (hdeg v)
      _ = Δ * ∑ v, w v := by rw [mul_sum]
  have h5 : ∑ d ∈ DL, ztqyk = ∑ d ∈ DL, w d.fst + ∑ d ∈ DL, w d.snd :=
    sum_add_distrib
  calc ztlen * γ ≤ 2 * #DL * γ := Nat.mul_le_mul_right _ h1
    _ = 2 * (#DL * γ) := by_ring
    _ ≤ 2 * (2 * ∑ v, w v + Δ * ∑ v, w v) := by_omega
    _ = 2 * ztufa * ∑ v, w v := by_ring
end Counting

/-! ## Cyclic order facts -/

/-- Two keys in an interval `(l, r)` free of `A` and `B` are on the same side of `A, B`. -/
theorem cyc_same {l r y z A B : ℝ} (hy : sideInArc l r y) (hz : sideInArc l r z)
    (hA : ¬ sideInArc l r A) (hB : ¬ sideInArc l r B) (hAB : A ≠ B) :
    sideInArc A B y ↔ sideInArc A B z := by
  have := lt_or_gt_of_ne hAB
  unfold sideInArc at *
  grind

/-- If a position `p + t` is inside an interval and `p` is not, the interval starts in
`[p, p + t)`. -/
theorem cyc_floor {a b p t : ℝ} (h : sideInArc a b ztk) (hp : ¬ sideInArc a b p)
    (ht : 0 < t) : p ≤ a ∧ a < p + t := by
  unfold sideInArc at *
  grind

/-- An open interval contains the keys just after each of its keys. -/
theorem cyc_open {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b ztudo := by
  unfold sideInArc at *
  split_ifs at * with hab
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT zthki]
      with ε hε hε'
    grind
  · zuy
    · zulg
      grind
    · filter_upwards [Ioo_mem_nhdsGT ztitg] with ε hε
      grind

/-- **A gap around a point.**  For a finite set `K` of at least two reals and `x ∉ K`, there are
`l ≠ r` in `K` with `x` strictly between them and no point of `K` strictly between them. -/
theorem exists_gap {K : Set ℝ} (hK : K.Finite) {k₁ k₂ : ℝ} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hk : k₁ ≠ k₂) {x : ℝ} (hx : x ∉ K) :
    ∃ l ∈ K, ∃ r ∈ K, l ≠ r ∧ sideInArc l r x ∧ ∀ k ∈ K, ¬ sideInArc l r k := by
  have hKne : K.Nonempty := ⟨k₁, hk₁⟩
  obtain ⟨m₀, hm₀, hmin⟩ := Set.exists_min_image K id hK hKne
  obtain ⟨M₀, hM₀, hmax⟩ := Set.exists_max_image K id hK hKne
  simp only [id] at hmin hmax
  have hmM : m₀ < M₀ := by
    grind
  -- the successor of `x`
  obtain ⟨r, hr, hrx, hrmin⟩ : ∃ r ∈ K, (x < r ∨ (∀ k ∈ K, k < x) ∧ r = m₀) ∧
      ∀ k ∈ K, x < k → (x < r ∧ r ≤ k) := by
    by_cases hA : ∃ k ∈ K, x < k
    · obtain ⟨r, ⟨hr, hxr⟩, hrm⟩ := Set.exists_min_image {k | k ∈ K ∧ x < k} id
        ztmks by_tauto
      exact ⟨r, hr, Or.inl hxr, by_simp_all⟩
    grind
  -- the predecessor of `x`
  obtain ⟨l, hl, hlx, hlmax⟩ : ∃ l ∈ K, (l < x ∨ (∀ k ∈ K, x < k) ∧ l = M₀) ∧
      ∀ k ∈ K, k < x → (l < x ∧ k ≤ l) := by
    by_cases hB : ∃ k ∈ K, k < x
    · obtain ⟨l, ⟨hl, hlx⟩, hlm⟩ := Set.exists_max_image {k | k ∈ K ∧ k < x} id
        ztmks by_tauto
      exact ⟨l, hl, Or.inl hlx, by_simp_all⟩
    grind
  have hxK : ∀ k ∈ K, k ≠ x := by_grind
  refine ⟨l, hl, r, hr, ?_, ?_, fun k hk => ?_⟩
  · grind
  · zuiq

  · have hkx := hxK k hk
    zuiq
namespace WalkAx
variable {M : Model}

/-! ## Cut keys -/
variable {F : Set (Set Point)}
/-- A cut key lies in `[0, n)`. -/
theorem cut_bounds {k : ℝ} (h : M.IsCut F k) : 0 ≤ k ∧ k < M.W.n := by
  obtain ⟨c, -, p, t, hA, rfl⟩ := h
  zuhzo
  zubkc

/-- A nonempty admissible family has two distinct cut keys. -/
theorem two_cuts (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hne : F.Nonempty) :
    ∃ k₁ k₂ : ℝ, M.IsCut F k₁ ∧ M.IsCut F k₂ ∧ k₁ ≠ k₂ := by
  zuice
  zuds
  exact ⟨pa + ta, pb + tb, ztkjl, ztcxs,
    key_ne_of_pt_ne hA hB by_simp_all⟩

/-- Positions just after a key `p + t` of `[0, n)` are inside the walk edge `p`. -/
theorem exists_pos_after {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), t + ε ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ztcqc]
    with ε hε hε'
  grind

/-- The keys just after the start of an interval are inside it. -/
theorem eventually_after_start {l r : ℝ} (_hlr : l ≠ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc l r (l + ε) := by
  zufdq
  zus
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ztto]
      with ε hε hε'
    grind
  · zulg
    simp_all

/-- **The arc of a gap**: an interval `(l, r)` between two distinct cuts containing no cut is an
arc of the region faced by all its positions. -/
theorem arc_of_gap (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {l r : ℝ} (hl : M.IsCut F l) (hr : M.IsCut F r) (hlr : l ≠ r)
    (hfree : ∀ k, sideInArc l r k → ¬ M.IsCut F k) :
    ∃ X ∈ M.regions F, M.IsArc F X l r := by
  obtain ⟨c₁, hc₁, p₁, t₁, hA₁, hl₁⟩ := hl
  -- a position just after `l`
  obtain ⟨ε, hε1, hε2⟩ := ((exists_pos_after hA₁.2.1 hA₁.2.2.1).and
    (eventually_after_start hlr)).exists
  have hy : sideInArc l r (p₁ + (t₁ + ε)) := by_grind
  obtain ⟨X, hX, hfX⟩ := hM.exists_faces_of_not_cut hF hfin hA₁.1 hε1 (hfree _ hy)
  refine ⟨X, hX, (cut_bounds zteyd).1,
    (cut_bounds zteyd).2, (cut_bounds hr).1, (cut_bounds hr).2,
    Or.inl ⟨zteyd, hr, hlr⟩, hfree, ?_⟩
  intro p t hp ht0 ht1 hin
  obtain ⟨U, hU, hfU⟩ := hM.exists_faces_of_not_cut hF hfin hp ztcoy (hfree _ hin)
  have heq : ztsde := by
    refine (hM.eq_iff_not_separates hF hfin hX hU hA₁.1 hp hε1 by_simp_all by_simp_all
      by_simp_all hfX hfU).2 ?_
    rintro c hc ⟨pa, pb, ta, tb, hA, hB, hAB, hiff⟩
    have hsame := cyc_same hy hin (hfree _ · ztkjl)
      (hfree _ · ztcxs) ztlqm
    simp_all
  simp_all

/-- **The arc around a non-cut key**: a non-cut key of `[0, n)` of a nonempty family lies inside
an arc of some region. -/
theorem arc_around (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hne : F.Nonempty) {x : ℝ} (hx : ¬ M.IsCut F x) :
    ∃ X ∈ M.regions F, ∃ l r : ℝ, M.IsArc F X l r ∧ sideInArc l r x := by
  obtain ⟨k₁, k₂, h₁, h₂, hk⟩ := hM.two_cuts hF hne
  obtain ⟨l, hl, r, hr, hlr, hxin, hno⟩ := exists_gap (hM.finite_cuts hF hfin) h₁ h₂ hk hx
  obtain ⟨X, hX, harc⟩ := hM.arc_of_gap hF hfin hl hr hlr (fun k hk hc => hno k hc hk)
  grind

/-! ## Weights by walk vertices -/

/-- The walk vertices (integer keys) strictly inside the arcs of `U`. -/
def arcVerts (M : Model) (F : Set ztf) (U : Set Point) : Set ℕ :=
  {p | p < M.W.n ∧ ∃ a b : ℝ, M.IsArc F U a b ∧ sideInArc a b p}

/-- The walk vertices strictly inside the interval `(a, b)`. -/
def vertsIn (M : Model) (a b : ℝ) : Set ℕ := {p | p < M.W.n ∧ sideInArc a b p}

/-- **An interval meets at most one more walk edge than walk vertices inside it.** -/
theorem arcWt_le (a b : ℝ) : M.arcWt a b ≤ (vertsIn M a b).ncard + 1 := by
  have hsub : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}
      ⊆ vertsIn M a b ∪ {⌊a⌋₊} := by
    rintro p ⟨hp, -, t, ht0, ht1, hin⟩
    by_cases hpin : sideInArc a b p
    · tauto
    · right
      obtain ⟨h1, h2⟩ := cyc_floor hin hpin ht0
      rw [mem_singleton_iff, eq_comm, Nat.floor_eq_iff by_grind]
      grind
  have hfin : (vertsIn M a b).Finite := (finite_Iio M.W.n).subset fun p hp => hp.1
  calc M.arcWt a b ≤ (vertsIn M a b ∪ {⌊a⌋₊}).ncard :=
        ncard_le_ncard hsub by_simp_all
    _ ≤ (vertsIn M a b).ncard + ({⌊a⌋₊} : Set ℕ).ncard := ncard_union_le _ _
    _ = (vertsIn M a b).ncard + 1 := by_simp

/-- **Distinct regions have disjoint arc vertices.** -/
theorem arcVerts_disjoint {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) {p : ℕ} (hp : p ∈ arcVerts M F U)
    (hp' : p ∈ arcVerts M F U') : U = U' := by
  obtain ⟨hpn, a, b, harc, hin⟩ := hp
  obtain ⟨-, a', b', harc', hin'⟩ := hp'
  obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := (((cyc_open hin).and (cyc_open hin')).and
    ztxgc).exists
  exact faces_unique hU hU' (harc.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h1)
    (harc'.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h2)

/-! ## Contraction -/

/-- **The regions inside a merged region.**  If `c ∈ F` separates the regions `U ≠ V` of `F`
and `W` is the region of `F \ {c}` containing `U`, the regions of `F` inside `W` are `U` and
`V`. -/
theorem merged_regions (hsys : ChordSystem M.D F) {c : Set Point}
    (hc : c ∈ F) {U V : Set Point} (hU : U ∈ M.regions F) (hV : V ∈ M.regions F) (hUV : U ≠ V)
    (hcU : TouchesIn M.D c U) (hcV : TouchesIn M.D c V) {W : Set Point}
    (hW : W ∈ M.regions ztbrw) (hUW : U ⊆ W) {X : Set Point} (hX : X ∈ M.regions F)
    (hXW : X ⊆ W) : X = U ∨ X = V := by
  have hS : F \ {c} ⊆ F := by_simp_all
  have hcS : c ∉ F \ {c} := by_simp_all
  have hins : insert c _ = F := insert_sdiff_singleton.trans ztjyw
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hsys.regionsIn_insert hS hc hcS
  have htouch := hsys.touches_iff_of_split hS hc hcS hR hcR hunion hR₁ hR₂ heq
  rw [hins] at htouch heq
  have hU12 := (htouch U hU).1 hcU
  have hV12 := (htouch V hV).1 hcV
  have hR₁R : ztiyp := fun p hp => by
    zubtb
    grind
  have hR₂R : ztiyq := fun p hp => by
    zuclo
    grind
  have hUR : U ⊆ R := by_grind
  have hX' : X ∈ regionsIn M.D F := hX
  zvnbk at hX'
  rcases hX' with ⟨hXS, hXR⟩ | hX12
  · exfalso
    obtain ⟨x, hx⟩ := Chazelle.Chain.regionsIn_nonempty hXS
    have hXeqW : X = W := by
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint hXS hW with h | h
      · zubh
      grind
    zuvh
    have huX : u ∈ X := by_grind
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hXS hR with h | h
    · grind
    grind
  grind

/-- The walk vertices at which a chord is attached. -/
def chordVerts (M : Model) (c : Set Point) : Set ℕ := {p | p < M.W.n ∧ SideAttach M.W c p 0}

/-- **The walk vertices inside an arc of a merged region** are attachments of the removed chord or
arc vertices of one of the two merged regions. -/
theorem merged_vertices (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {U V : Set Point} (hU : U ∈ M.regions F)
    (hV : V ∈ M.regions F) (hUV : U ≠ V) (hcU : TouchesIn M.D c U) (hcV : TouchesIn M.D c V)
    {W : Set Point} (hW : W ∈ M.regions ztbrw) (hUW : U ⊆ W) {a b : ℝ}
    (harc : M.IsArc ztbrw W a b) :
    vertsIn M a b ⊆ chordVerts M c ∪ arcVerts M F U ∪ arcVerts M F V := by
  zudr
  rintro p ⟨hpn, hpin⟩
  by_cases hcut : M.IsCut F p
  · -- an attachment of `c`
    obtain ⟨d, hd, q, t, hA, hpq⟩ := hcut
    have hq : q = p ∧ t = 0 := by
      have := sideKey_inj hA.2.1 hA.2.2.1 le_rfl one_pos (show (q : ℝ) + t = p + 0 by
        zvncl; exact hpq.symm)
      omega
    obtain ⟨rfl, rfl⟩ := hq
    zujtf
    · subst hdc; tauto
    · exact absurd ⟨d, by_grind, q, 0, hA, hpq⟩ (harc.2.2.2.2.2.1 _ hpin)
  · obtain ⟨X, hX, l, r, harcX, hinX⟩ := hM.arc_around hF hfin ztzx hcut
    have hpX : p ∈ arcVerts M F X := ⟨hpn, l, r, harcX, hinX⟩
    -- `X` lies in `W`
    obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := (((cyc_open hinX).and (cyc_open hpin)).and
      ztxgc).exists
    have hfX := harcX.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h1
    have hfW := harc.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h2
    obtain ⟨δ, hδX, hδW⟩ := (hfX.and hfW).exists
    have hXW : X ⊆ W := by
      have hXf : X ⊆ freeIn M.D ztbrw :=
        (Chazelle.Chain.regionsIn_subset hX).trans
          (Chazelle.Chain.freeIn_anti M.D by_simp_all)
      rw [Chazelle.Chain.regionsIn_eq_component hW hδW]
      exact (Chazelle.Chain.regionsIn_isPreconnected hX).subset_connectedComponentIn hδX hXf
    rcases merged_regions hsys hc hU hV hUV hcU hcV hW hUW hX hXW with rfl | rfl
    · simp_all
    simp_all

/-- **The weight of a merged region** is at most the arc vertices of the two merged regions plus
the attachments of the removed chord, plus one. -/
theorem weight_merged_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {U V : Set Point} (hU : U ∈ M.regions F)
    (hV : V ∈ M.regions F) (hUV : U ≠ V) (hcU : TouchesIn M.D c U) (hcV : TouchesIn M.D c V)
    {W : Set Point} (hW : W ∈ M.regions ztbrw) (hUW : U ⊆ W) :
    M.weight ztbrw W ≤ (chordVerts M c).ncard + (arcVerts M F U).ncard +
      (arcVerts M F V).ncard + 1 := by
  have hfn : ztknt := fun S h => (Set.finite_Iio _).subset h
  zudws

  zubi
  refine (arcWt_le a b).trans (Nat.add_le_add_right ?_ 1)
  calc (vertsIn M a b).ncard ≤ (chordVerts M c ∪ arcVerts M F U ∪ arcVerts M F V).ncard :=
        ncard_le_ncard (hM.merged_vertices hF hfin hc hU hV hUV hcU hcV hW hUW harc)
          (((hfn _ fun p hp => hp.1).union ztoar).union
            ztoar)
    _ ≤ (chordVerts M c ∪ arcVerts M F U).ncard + (arcVerts M F V).ncard := ncard_union_le _ _
    _ ≤ (chordVerts M c).ncard + (arcVerts M F U).ncard + (arcVerts M F V).ncard := by
        have := ncard_union_le (chordVerts M c) (arcVerts M F U); omega

/-! ## Chords at a walk vertex -/

/-- An attached admissible chord is the segment from its attachment point to its other endpoint,
which is off the domain, at the same height. -/
theorem chord_from (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ e', c = Chazelle.segment ztbp e' ∧ e' ≠ sidePt M.W p t ∧
      e'.2 = (sidePt M.W p t).2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztbp e' s ∈ M.D) ∧ e' ∉ M.D := by
  obtain ⟨a, b, hab, hcab, hy, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ :=
    hM.ends c hc
  have haD := hAa' ▸ hM.trace pa hAa.1 ta hAa.2.1 hAa.2.2.1.le
  have hbD := hBb' ▸ hM.trace pb hBb.1 tb hBb.2.1 hBb.2.2.1.le
  zucgh
  zugdq
  zucio
  · grind
  · zuzx
    exact ⟨a, hcab.trans ztfnp, hab, hy, open_rev hopen, haD⟩

/-- **At most two chords of `F` are attached at a walk vertex** (one to the east, one to the
west). -/
theorem ncard_chords_at_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (_hfin : F.Finite) (p : ℕ) : {c | c ∈ F ∧ SideAttach M.W c p 0}.ncard ≤ 2 := by
  classical
  let dir : Set Point → Bool := fun c => decide (∃ x ∈ c, (sidePt M.W p 0).1 < x.1)
  have hdir : ∀ c : Set Point, ∀ e', c = Chazelle.segment ztfs e' →
      (dir c = true ↔ (sidePt M.W p 0).1 < e'.1) := by
    zufhw

    · zueku

      zufr
      simp only [lerp_fst] at hlt
      zuhbv
    · zufia
      exact zticj
  -- the far endpoint of one chord is not strictly inside another
  have key : ∀ {f f' : Point},
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztfs f s ∈ M.D) → f' ∉ M.D →
      f.2 = (sidePt M.W p 0).2 → f'.2 = (sidePt M.W p 0).2 →
      ((sidePt M.W p 0).1 < f'.1 ∧ f'.1 < f.1 ∨ f.1 < f'.1 ∧ f'.1 < (sidePt M.W p 0).1) →
      False := by
    zucxd

    have hfe : f.1 - (sidePt M.W p 0).1 ≠ 0 := by
      grind
    have e1 : f' = lerp ztfs f ((f'.1 - (sidePt M.W p 0).1) /
        (f.1 - (sidePt M.W p 0).1)) := by
      zubjw
      · simp_all
      simp_all
    zukd
    apply hop
    zubry
    · exact ⟨div_pos by_linarith by_linarith, (div_lt_one by_linarith).2 by_linarith⟩
    · exact ⟨div_pos_of_neg_of_neg by_linarith by_linarith,
        (div_lt_one_of_neg by_linarith).2 by_linarith⟩
  have hinj : InjOn dir {c | c ∈ F ∧ SideAttach M.W c p 0} := by
    zukjb
    obtain ⟨e₁, hce₁, hne₁, hy₁, hop₁, hD₁⟩ := hM.chord_from ztmko hc.2
    obtain ⟨e₂, hce₂, hne₂, hy₂, hop₂, hD₂⟩ := hM.chord_from ztvsx hc'.2
    have hsame : (sidePt M.W p 0).1 < e₁.1 ↔ (sidePt M.W p 0).1 < e₂.1 := by
      grind
    have hx₁ : e₁.1 ≠ (sidePt M.W p 0).1 := by_grind
    have hx₂ : e₂.1 ≠ (sidePt M.W p 0).1 := by_grind
    have heq : ztsil := by
      apply point_ext _ ztqqx
      zuevp
      · have h₂ : e₂.1 < (sidePt M.W p 0).1 := by
          grind
        zugsd
        · zucve
        · zubh
        · zucvf
      · zuhfz
        zugsd
        · zucvf
        · zubh
        · zucve
    grind
  calc {c | c ∈ F ∧ SideAttach M.W c p 0}.ncard ≤ (Set.univ : Set Bool).ncard :=
        ncard_le_ncard_of_injOn dir by_grind hinj
    _ = 2 := by_simp

/-! ## The node weights and their sums -/

/-- The walk vertices at which an exit chord of `U` is attached. -/
def exitVerts (M : Model) (F : Set ztf) (U : Set Point) : Set ℕ :=
  {p | p < M.W.n ∧ ∃ c ∈ F, TouchesIn M.D c U ∧ SideAttach M.W c p 0}
theorem chordVerts_subset_exitVerts {c : Set Point} (hc : c ∈ F)
    {U : Set Point} (hcU : TouchesIn M.D c U) : chordVerts M c ⊆ exitVerts M F U :=
  fun _p hp => ⟨hp.1, c, hc, hcU, hp.2⟩

/-- **The arc vertices of distinct regions add up to at most `n`.** -/
theorem sum_arcVerts_le (R : Finset ztf)
    (hR : ∀ U ∈ R, U ∈ M.regions F) : ∑ U ∈ R, (arcVerts M F U).ncard ≤ M.W.n := by
  classical
  let A : Set Point → Finset ℕ := fun U => (Finset.range M.W.n).filter (· ∈ arcVerts M F U)
  have hA : ∀ U, (arcVerts M F U).ncard = (A U).card := by
    intro U
    zuezr
    zucr
    zufj
    simp only [A, coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ztkyl
  have hdisj : (R : Set _).PairwiseDisjoint A := by
    intro U hU U' hU' hne
    zukpg
    intro p hp hp'
    simp only [A, mem_filter] at hp hp'
    exact hne (arcVerts_disjoint by_simp_all by_simp_all hp.2 hp'.2)
  calc ∑ U ∈ R, (arcVerts M F U).ncard = ∑ U ∈ R, (A U).card := by_simp_all
    _ = (R.biUnion A).card := (card_biUnion hdisj).symm
    _ ≤ (Finset.range M.W.n).card := card_le_card by_grind
    _ = M.W.n := card_range _

/-- **The exit vertices of the regions add up to at most `4 n`.** -/
theorem sum_exitVerts_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (R : Finset ztf) (hR : ∀ U ∈ R, U ∈ M.regions F) :
    ∑ U ∈ R, (exitVerts M F U).ncard ≤ 4 * M.W.n := by
  classical
  zudr
  have hZ : ∀ U, (exitVerts M F U).ncard =
      ∑ p ∈ Finset.range M.W.n, if p ∈ exitVerts M F U then 1 else 0 := by
    intro U
    rw [Finset.sum_boole, Nat.cast_id, ← Set.ncard_coe_finset]
    zucr
    zufj
    simp only [coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ztkyl
  -- the regions with an exit chord attached at `p`
  have hp4 : ∀ p, (R.filter fun U => p ∈ exitVerts M F U).card ≤ 4 := by
    zukjq
    set Cp := {c | c ∈ F ∧ SideAttach M.W c p 0} with hCp
    have hCp2 := hM.ncard_chords_at_le hF hfin p
    have hCpf : Cp.Finite := hfin.subset by_simp_all
    -- the two regions touched by each chord
    have htwo : ∀ c ∈ F, ∃ R₁ R₂ : Set Point,
        ∀ W ∈ regionsIn M.D F, TouchesIn M.D c W → W = R₁ ∨ W = R₂ := by
      zung
      obtain ⟨R₁, R₂, -, h⟩ := hsys.touches_iff subset_rfl hc
      exact ⟨R₁, R₂, by_simp_all⟩
    choose! r₁ r₂ hr using htwo
    let g : Set Point × Bool → Set Point := fun cb => if cb.2 then r₁ cb.1 else r₂ cb.1
    have hsub : ((R.filter fun U => p ∈ exitVerts M F U : Finset _) : Set _)
        ⊆ g '' ztriw := by
      zucne
      simp only [coe_filter, Set.mem_ofPred_eq] at hU
      obtain ⟨hUR, -, c, hc, hcU, hA⟩ := hU
      rcases hr c hc U (hR U hUR) hcU with h | h
      · exact ⟨(c, true), by_simp_all, by_grind⟩
      · exact ⟨(c, false), by_simp_all, by_grind⟩
    calc (R.filter fun U => p ∈ exitVerts M F U).card
        = ((R.filter fun U => p ∈ exitVerts M F U : Finset _) : Set _).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (g '' ztriw).ncard :=
          ncard_le_ncard hsub ((hCpf.prod Set.finite_univ).image _)
      _ ≤ (Cp ×ˢ (Set.univ : Set Bool)).ncard := ncard_image_le (hCpf.prod Set.finite_univ)
      _ = Cp.ncard * (Set.univ : Set Bool).ncard := ncard_prod
      _ ≤ 2 * 2 := Nat.mul_le_mul hCp2 by_simp
      _ = 4 := rfl
  calc ∑ U ∈ R, (exitVerts M F U).ncard
      = ∑ U ∈ R, ∑ p ∈ Finset.range M.W.n, if p ∈ exitVerts M F U then 1 else 0 := by
        simp_all
    _ = ∑ p ∈ Finset.range M.W.n, ∑ U ∈ R, if p ∈ exitVerts M F U then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ p ∈ Finset.range M.W.n, (R.filter fun U => p ∈ exitVerts M F U).card := by
        simp
    _ ≤ ∑ p ∈ Finset.range M.W.n, 4 := sum_le_sum by_simp_all
    _ = 4 * M.W.n := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-! ## γ = 0 -/

/-- **A nonempty family is not `0`-semigranular** when the walk has a counted edge: the arc
through a non-cut position of that edge meets it. -/
theorem not_semigranular_zero (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hne : F.Nonempty) {p₀ : ℕ} (hp₀ : p₀ < M.W.n) (hc₀ : M.counted p₀) :
    ¬ M.Semigranular F 0 := by
  intro hsg
  zubap
  have hT : {t : ℝ | M.IsCut F _}.Finite :=
    Set.Finite.preimage (f := fun t : ℝ => (p₀ : ℝ) + t)
      by_simp_all hK
  obtain ⟨t, ht, htc⟩ := ((Set.Ioo_infinite ztcjf).sdiff hT).nonempty
  obtain ⟨X, hX, l, r, harc, hin⟩ := hM.arc_around hF hfin hne htc
  have hwt : 1 ≤ M.arcWt l r := by
    apply Nat.one_le_iff_ne_zero.2
    zubww
    rw [Model.arcWt, Set.ncard_eq_zero ztkpg] at h0
    have : p₀ ∈ ({p : ℕ | p < M.W.n ∧ M.counted p ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc l r ztk} : Set ℕ) :=
      by grind
    simp_all
  have hbdd : BddAbove ((fun ab : ℝ × ℝ => M.arcWt ab.1 ab.2) '' {ab | M.IsArc F X ab.1 ab.2}) :=
    ((hM.arcs_bound hF hfin hX).1.image _).bddAbove
  have hle : M.arcWt l r ≤ M.weight F X := le_csSup hbdd ⟨(l, r), harc, rfl⟩
  have := hsg X hX
  omega

/-! ## Lemma 2.3 -/

/-- **Lemma 2.3 for a model with the walk axioms**: `|F| γ ≤ 10 (D + 2) n`. -/
theorem lemma23_walk (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {γ D : ℕ} (hdeg : M.DegLe F D) (hgran : M.Granular F γ) :
    F.ncard * γ ≤ 2 * ztmo * ztjfu := by
  classical
  zudr
  have hD := hM.preconn
  have hDne := hM.nonempty
  have hRfin := hsys.regionsIn_finite hD hDne subset_rfl
  let _ : Fintype _ := hRfin.fintype
  set G := Chazelle.Chain.dualTreeIn M.D F with hG
  have hTree : G.IsTree := hsys.dual_isTree hD hDne subset_rfl
  have hdegG : ∀ U : regionsIn M.D F, G.degree U = M.deg F U := by
    intro U
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Merge.ncard_neighborSet_eq_exits hsys hD hDne subset_rfl U]
    rfl
  let w : regionsIn M.D F → ℕ := fun U => (arcVerts M F U).ncard + (exitVerts M F U).ncard
  have hfinN : ztknt := fun S h => (Set.finite_Iio _).subset h
  have hgran' : ∀ u v, G.Adj u v → ztler → γ ≤ w u + w v := by
    intro u v hadj hlow
    have hadj' : Chazelle.Chain.DualAdjIn M.D F u v := hadj
    obtain ⟨hu, hv, hne', c, hc, hcu, hcv⟩ := hadj'
    obtain ⟨x₀, hx₀⟩ := Chazelle.Chain.regionsIn_nonempty hu
    have hufree : (u : Set Point) ⊆ freeIn M.D ztbrw :=
      (Chazelle.Chain.regionsIn_subset hu).trans
        (Chazelle.Chain.freeIn_anti M.D by_grind)
    set W' := connectedComponentIn (freeIn M.D ztbrw) x₀ with hW'
    have hW'r : W' ∈ M.regions _ := ⟨x₀, hufree hx₀, rfl⟩
    have huW :=
      (Chazelle.Chain.regionsIn_isPreconnected hu).subset_connectedComponentIn hx₀ hufree
    have hlow' : M.deg F u < 3 ∨ M.deg F v < 3 := by_grind
    have hγ := hgran.2 c hc u hu v hv hne' hcu hcv hlow' W' hW'r huW
    have hwt := hM.weight_merged_le hF hfin hc hu hv hne' hcu hcv hW'r huW
    have hE :=
      ncard_le_ncard (chordVerts_subset_exitVerts hc hcu) (hfinN _ fun p hp => hp.1)
    grind
  have hcore := card_mul_le_of_granular_deg G hTree D
    (fun U => (hdegG U).trans_le (hdeg U U.2)) w γ hgran'
  have hcard : Fintype.card (regionsIn M.D F) = F.ncard + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsys.ncard_regionsIn hD hDne subset_rfl]
  have hsum : ∑ U, w U ≤ 5 * M.W.n := by
    have e : ∑ U, w U = ∑ U ∈ (regionsIn M.D F).toFinset,
        ((arcVerts M F U).ncard + (exitVerts M F U).ncard) :=
      Finset.sum_set_coe (f := fun U => (arcVerts M F U).ncard + (exitVerts M F U).ncard)
        _
    rw [e, Finset.sum_add_distrib]
    have hR : ∀ U ∈ (regionsIn M.D F).toFinset, U ∈ M.regions F := fun U hU =>
      (Set.mem_toFinset (s := regionsIn M.D F)).1 hU
    have h1 := sum_arcVerts_le _ hR
    have h2 := hM.sum_exitVerts_le hF hfin _ hR
    omega
  rw [hcard, Nat.add_sub_cancel] at hcore
  exact hcore.trans (Nat.mul_le_mul_left _ hsum)
end WalkAx

/-! ## The good models -/

/-- The walk of a good model has at most `7 (size + 1)` edges, and a counted edge. -/
theorem goodModel_walk (M : Model) (h : GoodModel M) :
    M.W.n ≤ 7 * ztcep ∧ ∃ p < M.W.n, M.counted p := by
  zudfa
  · zubt
    zuet
    have hsize : (chainModel C).size = 2 * C.m := by
      zujpy
      have : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p} = Set.Ico 6 ztcc := by
        zufj
        zuckp

      zugfl

    refine ⟨by_omega, 6, by_omega, ?_⟩
    change 6 ≤ 6 ∧ 6 < 2 * C.m + 6
    omega
  · have hs := (FactsInterior.interiorWalk_spec hQ).1
    have hn3 := Chazelle.Jordan.simple_three_le hs
    have hsize : (interiorModel Q).size = (interiorModel Q).W.n := by
      zujpy
      have : {p : ℕ | p < (interiorModel Q).W.n ∧ (interiorModel Q).counted p} =
          Set.Iio (interiorModel Q).W.n := by
        ext p; simp only [Set.mem_ofPred_eq, Set.mem_Iio]; tauto
      rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio]
    refine ⟨by_omega, 0, by_positivity, trivial⟩

/-- **WP-B: Lemma 2.3** (region count) for every good model, admissible family, degree cap `D`:
`|F| (γ + 1) ≤ 140 (D + 2) (size + 1)`. -/
theorem lemma23 : Lemma23Spec := by
  refine ⟨fun D => 140 * ztmo, ?_⟩
  intro M Q F γ D hM hF hdeg hgran
  zugc

  zubrr
  zucyo
  · zuqx
    · simp
    · zugkd
  · zucgc
    calc F.ncard * ztgj ≤ 2 * ztjis := by_nlinarith
      _ ≤ 2 * ztxun := Nat.mul_le_mul_left _ h
      _ ≤ 2 * ztwvy := by gcongr
      _ = 140 * ztmo * ztcep := by_ring
open Chazelle.Chain (halfDisk)
theorem chordSides_of_system {D : Set Point} {F : Set ztf} (hF : ChordSystem D F)
    {c : Set Point} (hc : c ∈ F) :
    ∃ U V, U ∈ regionsIn D F ∧ V ∈ regionsIn D F ∧ U ≠ V ∧
      (∀ z ∈ c, z ∈ D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ztcxe ∈ U ∧ ztcxf ∈ V) ∧
      (∀ W ∈ regionsIn D F, TouchesIn D c W ↔ W = U ∨ W = V) := by
  set S := F \ {c} with hSdef
  have hS : ztiyr := fun d hd => hd.1
  have hcS : c ∉ S := fun h => h.2 rfl
  have hins : insert c S = F := insert_sdiff_singleton.trans ztjyw
  zuwn

  have hRo : ztrfp := hF.regionsIn_open hS hR
  have hRS : R ⊆ freeIn D S := Chazelle.Chain.regionsIn_subset hR
  obtain ⟨z₀, hz₀c, hz₀D⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hRo z₀ (hcR ztuiu)
  obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in subset_rfl hc hz₀c hz₀D
  set ε := min r ε₀ / 2 with hε
  zudpq
  have hεr : ztiee := by zunbb; have := min_le_left r ε₀; linarith
  have hεε : ztmxm := by_grind
  obtain ⟨hp, hm, hpm⟩ := hsep ε hε0 hεε
  set U := connectedComponentIn ztfrg ztewu with hU
  set V := connectedComponentIn ztfrg ztewv with hV
  have hUr : U ∈ regionsIn D F := ⟨_, hp, rfl⟩
  have hVr : V ∈ regionsIn D F := ⟨_, hm, rfl⟩
  have hUr' : U ∈ regionsIn D ztlf := by_grind
  have hVr' : V ∈ regionsIn D ztlf := by_grind
  -- the half-disks at `z₀`
  have hhalf : ∀ τ : ℝ, ztoi → ∀ X ∈ regionsIn D ztlf,
      ((z₀.1, z₀.2 + τ * ε) : Point) ∈ X → halfDisk z₀ r τ ⊆ X := by
    intro τ hτ X hX hxX
    refine Chazelle.Chain.subset_regionsIn_of_inter hX (Chazelle.Chain.isPreconnected_halfDisk _ _ _)
      (hF.halfDisk_subset_freeIn_insert hc hz₀c (hball.trans hRS)) ⟨_, ?_, hxX⟩
    exact Chazelle.Chain.vert_mem_halfDisk hτ hε0 hεr
  have hUhalf : halfDisk z₀ r 1 ⊆ U :=
    hhalf 1 ztp U hUr' (by zvohi; exact mem_connectedComponentIn hp)
  have hVhalf : halfDisk z₀ r (-1) ⊆ V :=
    hhalf (-1) ztbt V hVr' (by
      rw [show z₀.2 + -1 * ε = z₀.2 - ε by ring]; exact mem_connectedComponentIn hm)
  -- the side regions along the whole chord
  have hall : ∀ τ : ℝ, ztoi → ∀ X ∈ regionsIn D ztlf,
      halfDisk z₀ r τ ⊆ X → ∀ z ∈ c, z ∈ D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ztbfc ∈ X := by
    intro τ hτ X hX hsub z hzc hzD
    have hall := hF.halfDisk_all hc hRo hcR hRS hX hτ ⟨z₀, ztuiu, r, hr, hball, hsub⟩
    obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.1 hRo z (hcR ztklu)
    filter_upwards [Ioo_mem_nhdsGT hr'] with δ hδ
    exact hall z ztklu r' hr' hball' (Chazelle.Chain.vert_mem_halfDisk hτ hδ.1 hδ.2)
  have hUne : U ≠ V := hpm
  -- `U` and `V` touch `c`
  have hcU : TouchesIn D c U :=
    ⟨z₀, ⟨hz₀c, hz₀D⟩, closure_mono hUhalf (Chazelle.Chain.mem_closure_halfDisk ztp hr)⟩
  have hcV : TouchesIn D c V :=
    ⟨z₀, ⟨hz₀c, hz₀D⟩, closure_mono hVhalf (Chazelle.Chain.mem_closure_halfDisk ztbt hr)⟩
  rw [hins] at htouch
  refine ⟨U, V, hUr, hVr, hUne, fun z hzc hzD => ?_, fun W hW => ?_⟩
  · filter_upwards [hall 1 ztp U hUr' hUhalf z hzc hzD,
      hall (-1) ztbt V hVr' hVhalf z hzc hzD] with δ h1 h2
    grind
  · have hU12 := (htouch U hUr).1 hcU
    have hV12 := (htouch V hVr).1 hcV
    rw [htouch W hW]
    rcases hU12 with h1 | h1 <;> rcases hV12 with h2 | h2
    · grind
    · zubuw
    · zvmza; exact Or.comm
    grind

/-- **WP-B: the two sides of a chord** (`ChordSidesSpec`). -/
theorem chordSides : ChordSidesSpec := by
  intro M Q F hM hF c hc
  exact chordSides_of_system ((walkAx_of_goodModel hM).sys F hF.2.1 hF.1) hc

/-- **WP-B: the region tree** (`RegionTreeSpec`). -/
theorem regionTree : RegionTreeSpec := by
  zufxh
  zufgd

  obtain ⟨hfin, hcard⟩ := hsys.regionsIn_finite_ncard hW.preconn hW.nonempty subset_rfl
  refine ⟨hfin, hcard, fun U hU V hV => ?_⟩
  zudhb

  refine Relation.ReflTransGen.mono (r := (Chazelle.Chain.dualGraphIn M.D F).Adj) ?_ _ _ h
  intro A B hAB
  obtain ⟨-, -, -, c, hc, h1, h2⟩ := hAB
  grind
