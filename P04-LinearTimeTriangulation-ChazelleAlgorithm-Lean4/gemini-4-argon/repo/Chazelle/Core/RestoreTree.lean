module

public import Chazelle.Core.RestoreCounts
public import Chazelle.Core.NFDecompTree

/-!
# WP-E, Lemma 3.2 part 5: the two sides of a chord in the record tree

The descent of the Lemma 3.2 search walks down the tree decomposition (`IsDecomp`) of a canonical
normal form: at the node of chord `k` it must choose the child (`lo` for the regions on the low
side `N.lowSide k`, `hi` for the high side) that contains the region faced by a candidate walk
position.  This file relates the combinatorial sides of the record tree to the walk keys.

* `cover`: every region is on the low or the high side of every chord (record tree connectivity,
  `Dec.RecTree.conn`).
* `low_sub`, `high_sub`: the regions of the low (high) side lie in the component of `D \ c` of
  the region below (above) the chord `c`; `comp_ne`: these two components differ.
* `decide_side`: if a walk position inside an edge faces region `r` and its key is strictly on
  the same side of the chord's two attachment keys as the key of a position facing the region
  below the chord, then `r` is on the low side (and on the high side otherwise).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric Relation
open Chazelle.Chain (ChordSystem SideAttach sideInArc sidePt SideSectorIn freeIn regionsIn
  TouchesIn regionsIn_subset regionsIn_isPreconnected regionsIn_nonempty sideKey_inj)

variable {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point}

/-- **Every region is on one side of every chord** (the record tree is connected). -/
theorem cover {D : ℕ} (hT : Dec.RecTree N D) {k : ℕ} (hk : k < N.nChords) {r : ℕ}
    (hr : r < N.nRegions) : r ∈ N.lowSide k ∨ r ∈ N.highSide k := by
  have hdn := (hT.ends_lt k hk).2
  have hreach := hT.conn _ _ hdn hr
  clear hr
  induction hreach with
  | refl => exact Or.inl ReflTransGen.refl
  | @tail s s' _ hadj ih =>
    obtain ⟨i, hi, hh⟩ := hadj
    by_cases hik : i = k
    · subst hik
      rcases hh with ⟨-, h⟩ | ⟨h, -⟩
      · rw [← h]; exact Or.inl ReflTransGen.refl
      · rw [← h]; exact Or.inr ReflTransGen.refl
    · have hav : N.AdjAvoid k s s' := ⟨i, hi, hik, hh⟩
      rcases ih with h | h
      · exact Or.inl (h.tail hav)
      · exact Or.inr (h.tail hav)

/-- A point of the open part of a chord record. -/
theorem exists_chord_pt (hM : WalkAx M) (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    ∃ z, z ∈ (N.chord i).toSet M Q ∧ z ∈ M.D := by
  have hc : (N.chord i).toSet M Q ∈ M.Adm := hN.1.2.1 ⟨N.chord i, Dec.chord_mem hi, rfl⟩
  obtain ⟨a, b, -, heq, -, hopen, -, -⟩ := hM.ends _ hc
  refine ⟨Geometry.lerp a b (1 / 2), ?_, hopen _ ⟨by norm_num, by norm_num⟩⟩
  rw [heq]; exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)

/-- A preconnected subset of `D \ c` meeting a component of `D \ c` lies in it. -/
theorem sub_comp {A : Set Point} {X : Set Point} (hX : IsPreconnected X) (hXA : X ⊆ A)
    {z w : Point} (hz : z ∈ X) (hzw : z ∈ connectedComponentIn A w) :
    X ⊆ connectedComponentIn A w := by
  rw [connectedComponentIn_eq hzw]
  exact hX.subset_connectedComponentIn hz hXA

/-- **Neighbours through another chord are in the same component.** -/
theorem adj_same_comp (hM : WalkAx M) (hN : IsNF M Q N) (hS : ChordSidesOK M Q N reg)
    (hR : ∀ r, r < N.nRegions → reg r ∈ M.regions (N.F M Q)) {k i : ℕ} (hk : k < N.nChords)
    (hi : i < N.nChords) (_hik : i ≠ k) (hne : (N.chord i).toSet M Q ≠ (N.chord k).toSet M Q)
    {w : Point} :
    reg (N.chord i).up ⊆ connectedComponentIn (M.D \ (N.chord k).toSet M Q) w ↔
      reg (N.chord i).dn ⊆ connectedComponentIn (M.D \ (N.chord k).toSet M Q) w := by
  set c := (N.chord k).toSet M Q
  have hsys := hM.sys _ hN.1.2.1 hN.1.1
  have hci : (N.chord i).toSet M Q ∈ N.F M Q := ⟨N.chord i, Dec.chord_mem hi, rfl⟩
  have hck : c ∈ N.F M Q := ⟨N.chord k, Dec.chord_mem hk, rfl⟩
  obtain ⟨z, hzc, hzD⟩ := exists_chord_pt hM hN hi
  have hzc' : z ∉ c := fun h => hsys.inter_subset_compl hci hck hne ⟨hzc, h⟩ hzD
  have hcl : IsClosed c := hsys.isClosed_chord hck
  have hopen : IsOpen (M.D \ c) := hM.isOpen.sdiff hcl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hzD, hzc'⟩
  obtain ⟨hup, hdn, hside⟩ := hS i hi
  obtain ⟨ε₀, hε₀, hε⟩ := hside z hzc hzD
  set ε := min (ε₀ / 2) (ρ / 2)
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨hu, hd⟩ := hε ε hε0 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hbu : ((z.1, z.2 + ε) : Point) ∈ ball z ρ := by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0]
    rw [max_eq_right hε0.le]; linarith [min_le_right (ε₀ / 2) (ρ / 2)]
  have hbd : ((z.1, z.2 - ε) : Point) ∈ ball z ρ := by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
    rw [max_eq_right hε0.le]; linarith [min_le_right (ε₀ / 2) (ρ / 2)]
  have hregsub : ∀ r, r < N.nRegions → reg r ⊆ M.D \ c := fun r hr x hx =>
    ⟨(regionsIn_subset (hR r hr) hx).1, fun hxc => (regionsIn_subset (hR r hr) hx).2 ⟨c, hck, hxc⟩⟩
  have hballP : IsPreconnected (ball z ρ) := (convex_ball z ρ).isPreconnected
  constructor
  · intro h
    have hb : ball z ρ ⊆ connectedComponentIn (M.D \ c) w := sub_comp hballP hball hbu (h hu)
    exact sub_comp (regionsIn_isPreconnected (hR _ hdn)) (hregsub _ hdn) hd (hb hbd)
  · intro h
    have hb : ball z ρ ⊆ connectedComponentIn (M.D \ c) w := sub_comp hballP hball hbd (h hd)
    exact sub_comp (regionsIn_isPreconnected (hR _ hup)) (hregsub _ hup) hu (hb hbu)

/-- The components of `D \ c` of the regions below and above a chord `c`. -/
theorem comps_of (hM : WalkAx M) (hN : IsNF M Q N) (hS : ChordSidesOK M Q N reg)
    (hR : ∀ r, r < N.nRegions → reg r ∈ M.regions (N.F M Q)) {k : ℕ} (hk : k < N.nChords) :
    ∃ zd zu : Point,
      reg (N.chord k).dn ⊆ connectedComponentIn (M.D \ (N.chord k).toSet M Q) zd ∧
      reg (N.chord k).up ⊆ connectedComponentIn (M.D \ (N.chord k).toSet M Q) zu ∧
      Disjoint (connectedComponentIn (M.D \ (N.chord k).toSet M Q) zd)
        (connectedComponentIn (M.D \ (N.chord k).toSet M Q) zu) := by
  set c := (N.chord k).toSet M Q
  have hsys := hM.sys _ hN.1.2.1 hN.1.1
  have hck : c ∈ N.F M Q := ⟨N.chord k, Dec.chord_mem hk, rfl⟩
  obtain ⟨z, hzc, hzD⟩ := exists_chord_pt hM hN hk
  obtain ⟨hup, hdn, hside⟩ := hS k hk
  obtain ⟨ε₀, hε₀, hε⟩ := hside z hzc hzD
  have hsub : ({c} : Set (Set Point)) ⊆ N.F M Q := singleton_subset_iff.2 hck
  obtain ⟨ε₁, hε₁, hsep⟩ := hsys.chord_separates_in hsub (mem_singleton c) hzc hzD
  set ε := min (ε₀ / 2) (ε₁ / 2)
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨hu, hd⟩ := hε ε hε0 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  obtain ⟨hu', hd', hne⟩ := hsep ε hε0 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hfe : freeIn M.D {c} = M.D \ c := by ext w; simp [freeIn]
  rw [hfe] at hu' hd' hne
  have hregsub : ∀ r, r < N.nRegions → reg r ⊆ M.D \ c := fun r hr x hx =>
    ⟨(regionsIn_subset (hR r hr) hx).1, fun hxc => (regionsIn_subset (hR r hr) hx).2 ⟨c, hck, hxc⟩⟩
  refine ⟨(z.1, z.2 - ε), (z.1, z.2 + ε),
    (regionsIn_isPreconnected (hR _ hdn)).subset_connectedComponentIn hd (hregsub _ hdn),
    (regionsIn_isPreconnected (hR _ hup)).subset_connectedComponentIn hu (hregsub _ hup),
    components_disjoint (Ne.symm hne)⟩

/-- **The regions of the low side lie in the component of the region below the chord** (and
those of the high side in the component of the region above). -/
theorem side_sub (hM : WalkAx M) (hN : IsNF M Q N) (hS : ChordSidesOK M Q N reg)
    (hR : ∀ r, r < N.nRegions → reg r ∈ M.regions (N.F M Q))
    (hinj : ∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i')
    {k : ℕ} (hk : k < N.nChords) {w : Point} {r₀ : ℕ}
    (h₀ : reg r₀ ⊆ connectedComponentIn (M.D \ (N.chord k).toSet M Q) w) {r : ℕ}
    (hr : ReflTransGen (N.AdjAvoid k) r₀ r) :
    reg r ⊆ connectedComponentIn (M.D \ (N.chord k).toSet M Q) w := by
  induction hr with
  | refl => exact h₀
  | @tail s s' _ hadj ih =>
    obtain ⟨i, hi, hik, hh⟩ := hadj
    have hne : (N.chord i).toSet M Q ≠ (N.chord k).toSet M Q := fun e => hik (hinj i k hi hk e)
    have key := adj_same_comp hM hN hS hR hk hi hik hne (w := w)
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h2]; rw [← h1] at ih; exact key.1 ih
    · rw [← h1]; rw [← h2] at ih; exact key.2 ih

/-- **Deciding the side of a region.**  Let the walk position `(p, t)` inside an edge face the
region `reg r`, and the position `(p₀, t₀)` inside an edge face the region below the chord `k`.
If their keys are strictly inside the same one of the two key intervals cut by the attachments
of the chord, `r` is on the low side of `k`; if they are strictly inside different ones, `r` is on
the high side. -/
theorem decide_side (hGM : GoodModel M) (hN : IsNF M Q N) {D : ℕ} (hT : Dec.RecTree N D)
    (hcorr : RegionCorr M Q N reg) (hS : ChordSidesOK M Q N reg)
    {k : ℕ} (hk : k < N.nChords) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W ((N.chord k).toSet M Q) pa ta)
    (hB : SideAttach M.W ((N.chord k).toSet M Q) pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {r : ℕ} (hr : r < N.nRegions) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : 0 < t) (ht1 : t < 1)
    (hf : M.Faces p t (reg r)) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < M.W.n) (ht₀ : 0 < t₀)
    (ht₀1 : t₀ < 1) (hf₀ : M.Faces p₀ t₀ (reg (N.chord k).dn)) :
    ((sideInArc (pa + ta) (pb + tb) (p + t) ∧ sideInArc (pa + ta) (pb + tb) (p₀ + t₀)) ∨
        (sideInArc (pb + tb) (pa + ta) (p + t) ∧ sideInArc (pb + tb) (pa + ta) (p₀ + t₀)) →
      r ∈ N.lowSide k) ∧
    ((sideInArc (pa + ta) (pb + tb) (p + t) ∧ sideInArc (pb + tb) (pa + ta) (p₀ + t₀)) ∨
        (sideInArc (pb + tb) (pa + ta) (p + t) ∧ sideInArc (pa + ta) (pb + tb) (p₀ + t₀)) →
      r ∈ N.highSide k) := by
  have hM := walkAx_of_goodModel hGM
  have hR := hcorr.1
  set c := (N.chord k).toSet M Q
  have hck : c ∈ N.F M Q := ⟨N.chord k, Dec.chord_mem hk, rfl⟩
  have hcA : c ∈ M.Adm := hN.1.2.1 hck
  obtain ⟨K₁, K₂, hK, ⟨c₁, hK₁⟩, ⟨c₂, hK₂⟩, hsec₁, hsec₂⟩ := hM.split hcA hA hB hAB
  obtain ⟨zd, zu, hdK, huK, hdisj⟩ := comps_of hM hN hS hR hk
  have hregsub : ∀ r, r < N.nRegions → reg r ⊆ M.D \ c := fun r hr x hx =>
    ⟨(regionsIn_subset (hR r hr) hx).1, fun hxc => (regionsIn_subset (hR r hr) hx).2 ⟨c, hck, hxc⟩⟩
  obtain ⟨hup, hdn, -⟩ := hS k hk
  -- a region faced at a key strictly inside a side lies in that side's component
  have inK : ∀ r', r' < N.nRegions → ∀ (q : ℕ) (s : ℝ), q < M.W.n → 0 < s → s < 1 →
      M.Faces q s (reg r') → ∀ (K : Set Point) (w : Point), K = connectedComponentIn (M.D \ c) w →
      SideSectorIn M.W K q s → reg r' ⊆ K := by
    intro r' hr' q s hq hs hs1 hfq K w hKw hsec
    obtain ⟨x, hx1, hx2⟩ := hM.faces_meets hq ⟨hs, hs1⟩ hsec hfq
    rw [hKw] at hx2 ⊢
    exact sub_comp (regionsIn_isPreconnected (hR r' hr')) (hregsub r' hr') hx1 hx2
  have hlow := fun r' (h : r' ∈ N.lowSide k) =>
    side_sub hM hN hS hR hN.2.1 hk (w := zd) hdK h
  have hhigh := fun r' (h : r' ∈ N.highSide k) =>
    side_sub hM hN hS hR hN.2.1 hk (w := zu) huK h
  have hne : ∀ r', r' < N.nRegions → (reg r').Nonempty := fun r' hr' =>
    regionsIn_nonempty (hR r' hr')
  -- two regions in a common component `K`: if one is on the low side, so is the other, etc.
  have ceq : ∀ {x w w' : Point}, x ∈ connectedComponentIn (M.D \ c) w →
      x ∈ connectedComponentIn (M.D \ c) w' →
      connectedComponentIn (M.D \ c) w = connectedComponentIn (M.D \ c) w' := fun h h' =>
    (connectedComponentIn_eq h).trans (connectedComponentIn_eq h').symm
  have same : ∀ K : Set Point, ∀ w, K = connectedComponentIn (M.D \ c) w →
      reg r ⊆ K → reg (N.chord k).dn ⊆ K → r ∈ N.lowSide k := by
    intro K w hKw hrK hdK'
    rcases cover hT hk hr with h | h
    · exact h
    · exfalso
      have h1 := hhigh r h
      obtain ⟨x, hx⟩ := hne r hr
      obtain ⟨y, hy⟩ := hne _ hdn
      -- `K` is the component of `zu` (through `x`) and of `zd` (through `y`)
      have e1 : connectedComponentIn (M.D \ c) zu = K :=
        (ceq (h1 hx) (hKw ▸ hrK hx)).trans hKw.symm
      have e2 : connectedComponentIn (M.D \ c) zd = K :=
        (ceq (hdK hy) (hKw ▸ hdK' hy)).trans hKw.symm
      exact hdisj.notMem_of_mem_left (hdK hy) (by rw [e1, ← e2]; exact hdK hy)
  have diff : ∀ K K' : Set Point, ∀ w w', K = connectedComponentIn (M.D \ c) w →
      K' = connectedComponentIn (M.D \ c) w' → Disjoint K K' →
      reg r ⊆ K → reg (N.chord k).dn ⊆ K' → r ∈ N.highSide k := by
    intro K K' w w' hKw hKw' hKK hrK hdK'
    rcases cover hT hk hr with h | h
    · exfalso
      have h1 := hlow r h
      obtain ⟨x, hx⟩ := hne r hr
      obtain ⟨y, hy⟩ := hne _ hdn
      have e1 : connectedComponentIn (M.D \ c) zd = K :=
        (ceq (h1 hx) (hKw ▸ hrK hx)).trans hKw.symm
      have e2 : connectedComponentIn (M.D \ c) zd = K' :=
        (ceq (hdK hy) (hKw' ▸ hdK' hy)).trans hKw'.symm
      exact hKK.notMem_of_mem_left (e1 ▸ hdK hy) (e2 ▸ hdK hy)
    · exact h
  have hdisj12 : Disjoint K₁ K₂ := by
    rw [hK₁, hK₂]; rw [hK₁, hK₂] at hK; exact components_disjoint hK
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact same K₁ c₁ hK₁ (inK r hr p t hp ht ht1 hf K₁ c₁ hK₁ (hsec₁ p hp t ht.le ht1 h1))
        (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₁ c₁ hK₁ (hsec₁ p₀ hp₀ t₀ ht₀.le ht₀1 h2))
    · exact same K₂ c₂ hK₂ (inK r hr p t hp ht ht1 hf K₂ c₂ hK₂ (hsec₂ p hp t ht.le ht1 h1))
        (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₂ c₂ hK₂ (hsec₂ p₀ hp₀ t₀ ht₀.le ht₀1 h2))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact diff K₁ K₂ c₁ c₂ hK₁ hK₂ hdisj12
        (inK r hr p t hp ht ht1 hf K₁ c₁ hK₁ (hsec₁ p hp t ht.le ht1 h1))
        (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₂ c₂ hK₂ (hsec₂ p₀ hp₀ t₀ ht₀.le ht₀1 h2))
    · exact diff K₂ K₁ c₂ c₁ hK₂ hK₁ hdisj12.symm
        (inK r hr p t hp ht ht1 hf K₂ c₂ hK₂ (hsec₂ p hp t ht.le ht1 h1))
        (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₁ c₁ hK₁ (hsec₁ p₀ hp₀ t₀ ht₀.le ht₀1 h2))

end

end Restore

end Chazelle.Core
