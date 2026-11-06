module

public import Chazelle.Core.FuseDegCover

/-!
# The degree bound of the revised fusion (`FusionDegSpec`, WP-D math)

Let `R` be a region of `S' = J.fusion S₁ S₂ ∪ glueChords J`, where `Sᵢ` has degree `≤ D`.

1. **Exceptional exit chords** (at most `49`): the chords through the shared vertex or the tops of
   `C₁`, `C₂` (these include the shared and the top chords; `≤ 6`), the cap chord (`≤ 1`), and
   the exit chords attached on a walk edge of the box block (`≤ 42`, by `edge_two`).
2. **Exit chords faced next to an attachment** (`adjExits`): apart from the exceptions, each is
   attached inside one of four pieces (`side_two_pieces`), next to a position faced by `R`, and is
   of type (I) (`≤ 4 D` per piece: `typeI_ncard_le`, using the one region of `Sᵢ` per piece,
   `one_piece`) or crossing (`≤ 4` per piece: `crossX_ncard_le`).  So there are at most
   `16 D + 65` of them.
3. **All exit chords**: apart from the exceptions, an exit chord is shot from an end of a chord of
   `S₁ ∪ S₂` containing it; by the chains of wedges and the strip argument (`parents_ncard_le`)
   these parents are at most `D (16 D + 65)` per side, each giving at most two fused chords.

Hence `deg R ≤ 7 + 4 D (16 D + 65)`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn freeIn
  regionsIn)
open Chazelle.Geometry (lerp)
open WalkEmbed FuseMath

namespace FuseDeg

variable (J : Merge.Junction)

/-! ## The family and the two sides -/

theorem fuse_adm (hgen : SharedGeneric J) {S₁ S₂ : Set (Set Point)}
    (h₁ : S₁ ⊆ Merge.augChords J.left) (h₂ : S₂ ⊆ Merge.augChords J.right) :
    J.fusion S₁ S₂ ∪ glueChords J ⊆ (chainModel J.whole).Adm :=
  union_subset (J.fusion_subset_augChords h₁ h₂) (glue_subset_aug J hgen)

theorem fuse_fin {S₁ S₂ : Set (Set Point)} (h₁ : S₁.Finite) (h₂ : S₂.Finite) :
    (J.fusion S₁ S₂ ∪ glueChords J).Finite :=
  (J.fusion_finite h₁ h₂).union (glueChords_finite J)

theorem fuse_endm (hP : J.P.Simple) {S₁ S₂ : Set (Set Point)} (h₁ : S₁ ⊆ Merge.augChords J.left)
    (h₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₁ ∪ S₂) :
    (Merge.lend c ≠ J.shared → ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared →
        ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.rend c ∈ e ∧ e ⊆ c) := by
  obtain ⟨hl, hr⟩ := Merge.Junction.end_mem_fusion J hP h₁ h₂ hc
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨e, he, h'⟩ := hl h; exact ⟨e, Or.inl he, h'⟩
  · obtain ⟨e, he, h'⟩ := hr h; exact ⟨e, Or.inl he, h'⟩

theorem sideOK_left (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set (Set Point)} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) :
    SideOK J J.left Q S₁ (J.fusion S₁ S₂ ∪ glueChords J) where
  simple := hP
  fam := hS₁
  endm := fun _c hc => fuse_endm J hP hS₁.2.1 hS₂.2.1 (Or.inl hc)
  ends := fun _c hc => ⟨(J.ends_left (hS₁.2.1 hc)).2.1, (J.ends_left (hS₁.2.1 hc)).2.2.2⟩
  shared := fun _ hc => Or.inl (Or.inr hc)
  adm := fuse_adm J hgen hS₁.2.1 hS₂.2.1
  fin := fuse_fin J hS₁.1 hS₂.1

theorem sideOK_right (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set (Set Point)} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) :
    SideOK J J.right Q S₂ (J.fusion S₁ S₂ ∪ glueChords J) where
  simple := hP
  fam := hS₂
  endm := fun _c hc => fuse_endm J hP hS₁.2.1 hS₂.2.1 (Or.inr hc)
  ends := fun _c hc => ⟨(J.ends_right (hS₂.2.1 hc)).2.1, (J.ends_right (hS₂.2.1 hc)).2.2.2⟩
  shared := fun _ hc => Or.inl (Or.inr hc)
  adm := fuse_adm J hgen hS₁.2.1 hS₂.2.1
  fin := fuse_fin J hS₁.1 hS₂.1

/-- An end of a chord of the other side lying on this side chain is the shared vertex. -/
theorem jend (_hP : J.P.Simple) {C' C'' : Chain} (hR : C'.radius = C''.radius)
    (hinter : C'.set ∩ C''.set ⊆ {J.shared}) {Sj : Set (Set Point)}
    (hj : Sj ⊆ Merge.augChords C'') :
    ∀ c ∈ Sj, ∀ q : Point, (q = Merge.lend c ∨ q = Merge.rend c) → q ∈ C'.set → q = J.shared := by
  intro c hc q hq hqC
  obtain ⟨y, a, b, hH, hy, -, hl, hr⟩ := Merge.augChords_spec (hj hc)
  have hnd : q ∉ C''.dom ∧ q.2 ≤ C''.top.2 := by
    rcases hq with rfl | rfl
    · rw [hl]; exact ⟨hH.left_not, hy⟩
    · rw [hr]; exact ⟨hH.right_not, hy⟩
  rcases (Merge.not_mem_dom_iff C'' hnd.2).1 hnd.1 with h | h
  · exact absurd (hR ▸ C'.set_subset_box hqC) h
  · exact hinter ⟨hqC, h⟩

theorem jend_left (hP : J.P.Simple) {S₂ : Set (Set Point)} (hj : S₂ ⊆ Merge.augChords J.right) :
    ∀ c ∈ S₂, ∀ q : Point, (q = Merge.lend c ∨ q = Merge.rend c) → q ∈ J.left.set →
      q = J.shared :=
  jend J hP (C' := J.left) (C'' := J.right) rfl (by rw [J.left_inter_right hP]) hj

theorem jend_right (hP : J.P.Simple) {S₁ : Set (Set Point)} (hj : S₁ ⊆ Merge.augChords J.left) :
    ∀ c ∈ S₁, ∀ q : Point, (q = Merge.lend c ∨ q = Merge.rend c) → q ∈ J.right.set →
      q = J.shared :=
  jend J hP (C' := J.right) (C'' := J.left) rfl
    (by rw [Set.inter_comm, J.left_inter_right hP]) hj


/-! ## The exceptional exit chords -/

/-- The chord passes through the shared vertex or through the top of `C₁` or of `C₂`. -/
def Thr (f : Set Point) : Prop := J.shared ∈ f ∨ J.left.top ∈ f ∨ J.right.top ∈ f

theorem thr_ncard (hP : J.P.Simple) {F : Set (Set Point)} (hFA : F ⊆ (chainModel J.whole).Adm)
    (hfin : F.Finite) : {f | f ∈ F ∧ Thr J f}.ncard ≤ 6 := by
  have hM : WalkAx (chainModel J.whole) := walkAx_chainModel hP
  have hv : ∀ v ∈ J.whole.set, v ∉ (chainModel J.whole).D := fun v hv h =>
    J.whole.not_mem_set_of_mem_dom h hv
  have h1 := ncard_through_le hM hFA (hv _ (J.left_set_subset J.shared_mem_left))
  have h2 := ncard_through_le hM hFA (hv _ (J.left_set_subset J.left.top_mem_set))
  have h3 := ncard_through_le hM hFA (hv _ (J.right_set_subset J.right.top_mem_set))
  have hsub : {f | f ∈ F ∧ Thr J f} ⊆ ({c | c ∈ F ∧ J.shared ∈ c} ∪
      {c | c ∈ F ∧ J.left.top ∈ c}) ∪ {c | c ∈ F ∧ J.right.top ∈ c} := by
    rintro f ⟨hf, h | h | h⟩
    · exact Or.inl (Or.inl ⟨hf, h⟩)
    · exact Or.inl (Or.inr ⟨hf, h⟩)
    · exact Or.inr ⟨hf, h⟩
  calc {f | f ∈ F ∧ Thr J f}.ncard
      ≤ (({c | c ∈ F ∧ J.shared ∈ c} ∪ {c | c ∈ F ∧ J.left.top ∈ c}) ∪
          {c | c ∈ F ∧ J.right.top ∈ c}).ncard :=
        Set.ncard_le_ncard hsub (hfin.subset (by
          rintro f ((⟨hf, -⟩ | ⟨hf, -⟩) | ⟨hf, -⟩) <;> exact hf))
    _ ≤ 6 := by
        refine (Set.ncard_union_le _ _).trans ?_
        have := Set.ncard_union_le {c | c ∈ F ∧ J.shared ∈ c} {c | c ∈ F ∧ J.left.top ∈ c}
        omega

/-- **The exit chords attached on the box block**: at most `42`. -/
theorem nc_ncard (hP : J.P.Simple) {F : Set (Set Point)} (hFA : F ⊆ (chainModel J.whole).Adm)
    (hfin : F.Finite) {R : Set Point} (hR : R ∈ (chainModel J.whole).regions F) :
    {f | f ∈ exits (chainModel J.whole) F R ∧ ∃ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W f p t ∧ ¬ (chainModel J.whole).counted p}.ncard ≤ 42 := by
  classical
  set M := chainModel J.whole with hMdef
  have hM : WalkAx M := walkAx_chainModel hP
  have hn := cm_n J.whole
  set P0 : Finset ℕ := Finset.range 6 ∪ {2 * J.whole.m + 6} with hP0
  have hP0c : P0.card ≤ 7 := (Finset.card_union_le _ _).trans (by simp)
  set X : ℕ → Set (Set Point) := fun p =>
    {f | f ∈ exits M F R ∧ ∃ t : ℝ, SideAttach M.W f p t} with hX
  have hXp : ∀ p, (X p).ncard ≤ 6 := by
    intro p
    set T := {t : ℝ | 0 < t ∧ ∃ c ∈ exits M F R, SideAttach M.W c p t} with hT
    have hT2 : T.ncard ≤ 2 := edge_two hM hFA hfin hR p
    have hTfin : T.Finite := by
      refine (Set.Finite.image (fun x : ℝ => x - (p : ℝ)) (hM.finite_cuts hFA hfin)).subset ?_
      rintro t ⟨-, c, hc, hA⟩
      exact ⟨p + t, ⟨c, hc.1, p, t, hA, rfl⟩, by ring⟩
    have hsub : X p ⊆ ⋃ t ∈ insert 0 T, {f | f ∈ F ∧ SideAttach M.W f p t} := by
      rintro f ⟨hf, t, hA⟩
      simp only [Set.mem_iUnion]
      rcases hA.2.1.lt_or_eq with h | h
      · exact ⟨t, Or.inr ⟨h, f, hf, hA⟩, hf.1, hA⟩
      · exact ⟨t, Or.inl h.symm, hf.1, hA⟩
    calc (X p).ncard ≤ (⋃ t ∈ insert 0 T, {f | f ∈ F ∧ SideAttach M.W f p t}).ncard :=
          Set.ncard_le_ncard hsub (hfin.subset (by
            intro f hf; simp only [Set.mem_iUnion] at hf; obtain ⟨t, -, hf, -⟩ := hf; exact hf))
      _ ≤ 2 * (insert 0 T).ncard :=
          ncard_biUnion_le_mul (hTfin.insert 0) _ fun t _ => ncard_at_le hM hFA hfin p t
      _ ≤ 6 := by have := Set.ncard_insert_le (0 : ℝ) T; omega
  have hsub : {f | f ∈ exits M F R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ ¬ M.counted p} ⊆
      ⋃ p ∈ (P0 : Set ℕ), X p := by
    rintro f ⟨hf, p, t, hA, hc⟩
    simp only [Set.mem_iUnion]
    refine ⟨p, ?_, hf, t, hA⟩
    have hp := hA.1
    rw [hn] at hp
    have : ¬ (6 ≤ p ∧ p < 2 * J.whole.m + 6) := hc
    simp only [hP0, Finset.coe_union, Finset.coe_range, Finset.coe_singleton, Set.mem_union,
      Set.mem_Iio, Set.mem_singleton_iff]
    omega
  calc _ ≤ (⋃ p ∈ (P0 : Set ℕ), X p).ncard :=
        Set.ncard_le_ncard hsub (hfin.subset (by
          intro f hf; simp only [Set.mem_iUnion] at hf; obtain ⟨p, -, hf, -⟩ := hf; exact hf.1))
    _ ≤ 6 * (P0 : Set ℕ).ncard := ncard_biUnion_le_mul P0.finite_toSet _ fun p _ => hXp p
    _ ≤ 42 := by rw [Set.ncard_coe_finset]; omega

/-- **Glue and shared chords pass through the shared vertex or a top, or are the cap chord.** -/
theorem glue_thr {f : Set Point}
    (hf : f ∈ glueChords J ∨ f ∈ J.sharedChords) : Thr J f ∨ f ∈ capChords J := by
  rcases hf with (⟨k, hk, σ, -, -, rfl⟩ | hcap) | ⟨σ, -, -, rfl⟩
  · left
    simp only [topIdxs, Finset.mem_insert, Finset.mem_singleton] at hk
    have hmem : J.whole.vertex k ∈ J.whole.chordSet k σ := Geometry.left_mem_segment _ _
    rcases hk with rfl | rfl
    · right; left; exact hmem
    · right; right
      rw [Merge.Junction.whole_vertex_add] at hmem
      exact hmem
  · exact Or.inr hcap
  · left; left
    exact Geometry.left_mem_segment _ _

/-- **A fused chord other than a shared chord is shot from an end of its parent.** -/
theorem fused_parent {S₁ S₂ : Set (Set Point)} (h₁ : S₁ ⊆ Merge.augChords J.left)
    (h₂ : S₂ ⊆ Merge.augChords J.right) {f : Set Point} (hf : f ∈ J.fusion S₁ S₂)
    (hsh : f ∉ J.sharedChords) :
    ∃ c ∈ S₁ ∪ S₂, (f = Merge.shoot J.whole (Merge.lend c) 1 ∨
      f = Merge.shoot J.whole (Merge.rend c) (-1)) ∧ f ⊆ c ∧
      (Merge.lend c ∈ f ∨ Merge.rend c ∈ f) := by
  have hc' : ∀ c ∈ S₁ ∪ S₂, c ∈ Merge.augChords J.left ∪ Merge.augChords J.right := by
    rintro c (hc | hc)
    · exact Or.inl (h₁ hc)
    · exact Or.inr (h₂ hc)
  rcases hf with (⟨c, hc, -, rfl⟩ | ⟨c, hc, -, rfl⟩) | hd
  · exact ⟨c, hc, Or.inl rfl, J.shoot_lend_subset (hc' c hc),
      Or.inl (Geometry.left_mem_segment _ _)⟩
  · exact ⟨c, hc, Or.inr rfl, J.shoot_rend_subset (hc' c hc),
      Or.inr (Geometry.left_mem_segment _ _)⟩
  · exact absurd hd hsh


/-! ## The four pieces -/

/-- **The walk of `C` is covered by four pieces** (two along each side chain), each starting at a
copy of the shared vertex or of the top of its side chain. -/
theorem four_pieces (hP : J.P.Simple) :
    ∃ gA gA' LA gB gB' LB gC gC' LC gD gD' LD : ℕ,
      PieceAt J J.left gA gA' LA ∧ PieceAt J J.left gB gB' LB ∧
      PieceAt J J.right gC gC' LC ∧ PieceAt J J.right gD gD' LD ∧
      ((chainModel J.whole).W.vtx gA = J.shared ∨ (chainModel J.whole).W.vtx gA = J.left.top) ∧
      ((chainModel J.whole).W.vtx gB = J.shared ∨ (chainModel J.whole).W.vtx gB = J.left.top) ∧
      ((chainModel J.whole).W.vtx gC = J.shared ∨ (chainModel J.whole).W.vtx gC = J.right.top) ∧
      ((chainModel J.whole).W.vtx gD = J.shared ∨ (chainModel J.whole).W.vtx gD = J.right.top) ∧
      ∀ p : ℕ, p < (chainModel J.whole).W.n → (chainModel J.whole).counted p →
        dOf (chainModel J.whole).W.n gA p < LA ∨ dOf (chainModel J.whole).W.n gB p < LB ∨
          dOf (chainModel J.whole).W.n gC p < LC ∨ dOf (chainModel J.whole).W.n gD p < LD := by
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  have hn := cm_n J.whole
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  obtain ⟨gA, gA', LA, gB, gB', LB, hA, hB, hsA, hsB, hcovL⟩ :=
    side_two_pieces J hP (C' := J.left) rfl (J₀ := J.m₁ + 2 * J.m₂) (J₀' := J.m₁)
      (ℓ := 2 * J.m₁) (fun e he => tourV_left J he)
      (by rw [tourV_left J (by omega), tourV_left_zero]; rfl) (by simp) (by rw [hwm]; omega)
      (left_box_eq J)
  obtain ⟨gC, gC', LC, gD, gD', LD, hC, hD, hsC, hsD, hcovR⟩ :=
    side_two_pieces J hP (C' := J.right) rfl (J₀ := J.m₁) (J₀' := 0)
      (ℓ := 2 * J.m₂) (fun e he => tourV_right J he)
      (by rw [tourV_right J (by omega), tourV_right_zero]; rfl) (by simp) (by rw [hwm]; omega)
      (right_box_eq J)
  refine ⟨gA, gA', LA, gB, gB', LB, gC, gC', LC, gD, gD', LD, hA, hB, hC, hD, hsA, hsB, hsC, hsD,
    fun p hp hc => ?_⟩
  obtain ⟨hc1, hc2⟩ : 6 ≤ p ∧ p < 2 * J.whole.m + 6 := hc
  obtain ⟨i, rfl⟩ : ∃ i, p = 6 + i := ⟨p - 6, by omega⟩
  have hτlt := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  rw [hwm] at hτlt
  have hrel := tpos_rel J
  rw [hwm] at hrel
  rcases cover_arith h1 h2 hτlt hrel (show i < 2 * (J.m₁ + J.m₂) by omega) with hin | hin
  · rcases hcovL _ hp (by rw [hn, hwm]; exact hin) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hcovR _ hp (by rw [hn, hwm]; exact hin) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- An exit chord faced next to an attachment inside a piece is of type (I) or crossing. -/
theorem in_piece (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si Sj S' : Set (Set Point)}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L)
    (hstart : (chainModel J.whole).W.vtx g = J.shared ∨ (chainModel J.whole).W.vtx g = C'.top)
    (hjend : ∀ c ∈ Sj, ∀ q : Point, (q = Merge.lend c ∨ q = Merge.rend c) → q ∈ C'.set →
      q = J.shared)
    (hjnd : ∀ c ∈ Sj, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    {R f : Set Point} (hf : f ∈ exits (chainModel J.whole) S' R)
    (hpar : ∃ c ∈ Si ∪ Sj, f ⊆ c ∧ (Merge.lend c ∈ f ∨ Merge.rend c ∈ f))
    (hcnt : ∀ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W f pb tb →
      (chainModel J.whole).counted pb)
    (hsh : J.shared ∉ f) (htop : C'.top ∉ f) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W f p t) (hadj : Adj (chainModel J.whole) S' R p t)
    (hdp : dOf (chainModel J.whole).W.n g p < L) :
    f ∈ TypeI J C' Si S' R g g' L ∨ f ∈ CrossX (chainModel J.whole) S' R g L := by
  have hpd : (g + dOf (chainModel J.whole).W.n g p) % (chainModel J.whole).W.n = p :=
    add_dOf hpc.1 hA.1
  rw [← hpd] at hA hadj
  by_cases h0 : 0 < (dOf (chainModel J.whole).W.n g p : ℝ) + t
  · exact classify J hP hS hpc hjend hjnd hf hpar hcnt hsh hdp hA.2.1 hA.2.2.1 h0 hA hadj
  · exfalso
    have ht : t = 0 := le_antisymm (by
      have := (Nat.cast_nonneg (dOf (chainModel J.whole).W.n g p) : (0 : ℝ) ≤ _); linarith)
      hA.2.1
    have hd : dOf (chainModel J.whole).W.n g p = 0 := by
      have : (dOf (chainModel J.whole).W.n g p : ℝ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
    rw [hd, ht, add_zero, Nat.mod_eq_of_lt hpc.1] at hA
    have hmem := hA.2.2.2.1
    rw [Chazelle.Chain.sidePt_zero] at hmem
    rcases hstart with h | h
    · exact hsh (h ▸ hmem)
    · exact htop (h ▸ hmem)


theorem cap_ncard : (capChords J).ncard ≤ 1 :=
  (Set.ncard_le_one (capChords_subsingleton J).finite).2
    fun _ ha _ hb => capChords_subsingleton J ha hb

/-- **At most `16 D + 65` exit chords of `R` are faced next to an attachment.** -/
theorem adj_ncard (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set (Set Point)} (hS₁ : (chainModel J.left).ChordFamily Q S₁)
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {D : ℕ}
    (hD₁ : (chainModel J.left).DegLe S₁ D) (hD₂ : (chainModel J.right).DegLe S₂ D)
    {R : Set Point} (hR : R ∈ (chainModel J.whole).regions (J.fusion S₁ S₂ ∪ glueChords J)) :
    (adjExits (chainModel J.whole) (J.fusion S₁ S₂ ∪ glueChords J) R).ncard ≤ 16 * D + 65 := by
  set M := chainModel J.whole with hMdef
  set F := J.fusion S₁ S₂ ∪ glueChords J with hFdef
  have hM : WalkAx M := walkAx_chainModel hP
  have hFA := fuse_adm J hgen hS₁.2.1 hS₂.2.1
  have hfin := fuse_fin J hS₁.1 hS₂.1
  have SL := sideOK_left J hP hgen hS₁ hS₂
  have SR := sideOK_right J hP hgen hS₁ hS₂
  obtain ⟨gA, gA', LA, gB, gB', LB, gC, gC', LC, gD, gD', LD, hA, hB, hC, hD, hsA, hsB, hsC, hsD,
    hcov⟩ := four_pieces J hP
  have hjL := jend_left J hP hS₂.2.1
  have hjR := jend_right J hP hS₁.2.1
  have hndL : ∀ c ∈ S₂, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom := fun c hc =>
    ⟨(J.ends_right (hS₂.2.1 hc)).2.1, (J.ends_right (hS₂.2.1 hc)).2.2.2⟩
  have hndR : ∀ c ∈ S₁, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom := fun c hc =>
    ⟨(J.ends_left (hS₁.2.1 hc)).2.1, (J.ends_left (hS₁.2.1 hc)).2.2.2⟩
  set NC := {f | f ∈ exits M F R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ ¬ M.counted p}
    with hNC
  set E₀ := ({f | f ∈ F ∧ Thr J f} ∪ capChords J) ∪ NC with hE₀
  set PA := TypeI J J.left S₁ F R gA gA' LA ∪ CrossX M F R gA LA
  set PB := TypeI J J.left S₁ F R gB gB' LB ∪ CrossX M F R gB LB
  set PC := TypeI J J.right S₂ F R gC gC' LC ∪ CrossX M F R gC LC
  set PD := TypeI J J.right S₂ F R gD gD' LD ∪ CrossX M F R gD LD
  have hsub : adjExits M F R ⊆ E₀ ∪ ((PA ∪ PB) ∪ (PC ∪ PD)) := by
    rintro f ⟨hf, p, t, hAt, hadj⟩
    by_cases hthr : Thr J f
    · exact Or.inl (Or.inl (Or.inl ⟨hf.1, hthr⟩))
    by_cases hcap : f ∈ capChords J
    · exact Or.inl (Or.inl (Or.inr hcap))
    by_cases hnc : ∃ (p : ℕ) (t : ℝ), SideAttach M.W f p t ∧ ¬ M.counted p
    · exact Or.inl (Or.inr ⟨hf, hnc⟩)
    push Not at hnc
    right
    have hfus : f ∈ J.fusion S₁ S₂ ∧ f ∉ J.sharedChords := by
      rcases hf.1 with h | h
      · refine ⟨h, fun hs => ?_⟩
        rcases glue_thr J (Or.inr hs) with h' | h'
        · exact hthr h'
        · exact hcap h'
      · rcases glue_thr J (Or.inl h) with h' | h'
        · exact absurd h' hthr
        · exact absurd h' hcap
    obtain ⟨c, hc, -, hfc, hnear⟩ := fused_parent J hS₁.2.1 hS₂.2.1 hfus.1 hfus.2
    have hsh : J.shared ∉ f := fun h => hthr (Or.inl h)
    have hlt : J.left.top ∉ f := fun h => hthr (Or.inr (Or.inl h))
    have hrt : J.right.top ∉ f := fun h => hthr (Or.inr (Or.inr h))
    have hparL : ∃ c ∈ S₁ ∪ S₂, f ⊆ c ∧ (Merge.lend c ∈ f ∨ Merge.rend c ∈ f) :=
      ⟨c, hc, hfc, hnear⟩
    have hparR : ∃ c ∈ S₂ ∪ S₁, f ⊆ c ∧ (Merge.lend c ∈ f ∨ Merge.rend c ∈ f) :=
      ⟨c, Set.union_comm S₁ S₂ ▸ hc, hfc, hnear⟩
    rcases hcov p hAt.1 (hnc p t hAt) with h | h | h | h
    · exact Or.inl (Or.inl (in_piece J hP SL hA hsA hjL hndL hf hparL hnc hsh hlt hAt hadj h))
    · exact Or.inl (Or.inr (in_piece J hP SL hB hsB hjL hndL hf hparL hnc hsh hlt hAt hadj h))
    · exact Or.inr (Or.inl (in_piece J hP SR hC hsC hjR hndR hf hparR hnc hsh hrt hAt hadj h))
    · exact Or.inr (Or.inr (in_piece J hP SR hD hsD hjR hndR hf hparR hnc hsh hrt hAt hadj h))
  have hEfin : (E₀ ∪ ((PA ∪ PB) ∪ (PC ∪ PD))).Finite := by
    refine hfin.subset ?_
    rintro f (((⟨hf, -⟩ | hf) | ⟨hf, -⟩) | ((hf | hf) | (hf | hf)))
    · exact hf
    · exact Or.inr (Or.inr hf)
    · exact hf.1
    all_goals rcases hf with hf | hf
    all_goals first | exact hf.1 | exact hf.1.1
  have hPiece : ∀ {C' : Chain} {Si : Set (Set Point)} {g g' L : ℕ},
      SideOK J C' Q Si F → PieceAt J C' g g' L → (chainModel C').DegLe Si D →
      (TypeI J C' Si F R g g' L ∪ CrossX M F R g L).ncard ≤ 4 * D + 4 := by
    intro C' Si g g' L hS hpc hdeg
    have h1 := typeI_ncard_le J hP hS hpc hR hdeg
    have h2 : (CrossX M F R g L).ncard ≤ 4 := crossX_ncard_le hM hFA hfin hpc.1 hpc.2.2.1 hR
    have h3 := Set.ncard_union_le (TypeI J C' Si F R g g' L) (CrossX M F R g L)
    omega
  have hA' : PA.ncard ≤ 4 * D + 4 := hPiece SL hA hD₁
  have hB' : PB.ncard ≤ 4 * D + 4 := hPiece SL hB hD₁
  have hC' : PC.ncard ≤ 4 * D + 4 := hPiece SR hC hD₂
  have hD' : PD.ncard ≤ 4 * D + 4 := hPiece SR hD hD₂
  have hThr : {f | f ∈ F ∧ Thr J f}.ncard ≤ 6 := thr_ncard J hP hFA hfin
  have hCap := cap_ncard J
  have hNCn : NC.ncard ≤ 42 := nc_ncard J hP hFA hfin hR
  have u1 := Set.ncard_union_le ({f | f ∈ F ∧ Thr J f}) (capChords J)
  have u2 : E₀.ncard ≤ ({f | f ∈ F ∧ Thr J f} ∪ capChords J).ncard + NC.ncard :=
    Set.ncard_union_le _ _
  have u3 := Set.ncard_union_le PA PB
  have u4 := Set.ncard_union_le PC PD
  have u5 := Set.ncard_union_le (PA ∪ PB) (PC ∪ PD)
  have u6 := Set.ncard_union_le E₀ ((PA ∪ PB) ∪ (PC ∪ PD))
  have := Set.ncard_le_ncard hsub hEfin
  omega


/-! ## The degree bound -/

/-- **WP-D (math): the degree bound of the revised fusion** (`FusionDegSpec`, finding D4): the
fusion of two submaps of degree `≤ D` plus the glue chords has degree
`≤ 7 + 4 D (16 D + 65)`. -/
theorem fusionDegSpec : FusionDegSpec := by
  refine ⟨fun D => 7 + 4 * D * (16 * D + 65), ?_⟩
  intro J Q S₁ S₂ D hP hgen hS₁ hS₂ hD₁ hD₂ R hR
  set M := chainModel J.whole with hMdef
  set F := J.fusion S₁ S₂ ∪ glueChords J with hFdef
  have hFA := fuse_adm J hgen hS₁.2.1 hS₂.2.1
  have hfin := fuse_fin J hS₁.1 hS₂.1
  have hA : (adjExits M F R).ncard ≤ 16 * D + 65 := adj_ncard J hP hgen hS₁ hS₂ hD₁ hD₂ hR
  have hendsL : ∀ c ∈ S₁, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom := fun c hc =>
    ⟨(J.ends_left (hS₁.2.1 hc)).2.1, (J.ends_left (hS₁.2.1 hc)).2.2.2⟩
  have hendsR : ∀ c ∈ S₂, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom := fun c hc =>
    ⟨(J.ends_right (hS₂.2.1 hc)).2.1, (J.ends_right (hS₂.2.1 hc)).2.2.2⟩
  set P₁ := {c | c ∈ S₁ ∧ ∃ e ∈ exits M F R, e ⊆ c} with hP₁
  set P₂ := {c | c ∈ S₂ ∧ ∃ e ∈ exits M F R, e ⊆ c} with hP₂
  have h₁ : P₁.ncard ≤ D * (adjExits M F R).ncard :=
    parents_ncard_le J hP (C' := J.left) rfl J.left_set_subset hS₁ hFA hfin hendsL hR hD₁
  have h₂ : P₂.ncard ≤ D * (adjExits M F R).ncard :=
    parents_ncard_le J hP (C' := J.right) rfl J.right_set_subset hS₂ hFA hfin hendsR hR hD₂
  set P := P₁ ∪ P₂ with hPdef
  have hPfin : P.Finite := (hS₁.1.union hS₂.1).subset (by
    rintro c (⟨hc, -⟩ | ⟨hc, -⟩)
    · exact Or.inl hc
    · exact Or.inr hc)
  set I₁ := (fun c => Merge.shoot J.whole (Merge.lend c) 1) '' P
  set I₂ := (fun c => Merge.shoot J.whole (Merge.rend c) (-1)) '' P
  set E₀ := {f | f ∈ F ∧ Thr J f} ∪ capChords J
  have hsub : exits M F R ⊆ E₀ ∪ (I₁ ∪ I₂) := by
    intro f hf
    by_cases hthr : Thr J f
    · exact Or.inl (Or.inl ⟨hf.1, hthr⟩)
    by_cases hcap : f ∈ capChords J
    · exact Or.inl (Or.inr hcap)
    right
    have hfus : f ∈ J.fusion S₁ S₂ ∧ f ∉ J.sharedChords := by
      rcases hf.1 with h | h
      · refine ⟨h, fun hs => ?_⟩
        rcases glue_thr J (Or.inr hs) with h' | h'
        · exact hthr h'
        · exact hcap h'
      · rcases glue_thr J (Or.inl h) with h' | h'
        · exact absurd h' hthr
        · exact absurd h' hcap
    obtain ⟨c, hc, hshoot, hfc, -⟩ := fused_parent J hS₁.2.1 hS₂.2.1 hfus.1 hfus.2
    have hcP : c ∈ P := by
      rcases hc with hc | hc
      · exact Or.inl ⟨hc, f, hf, hfc⟩
      · exact Or.inr ⟨hc, f, hf, hfc⟩
    rcases hshoot with rfl | rfl
    · exact Or.inl ⟨c, hcP, rfl⟩
    · exact Or.inr ⟨c, hcP, rfl⟩
  have hfin' : (E₀ ∪ (I₁ ∪ I₂)).Finite :=
    ((hfin.subset (by rintro f (⟨hf, -⟩ | hf); exacts [hf, Or.inr (Or.inr hf)])).union
      ((hPfin.image _).union (hPfin.image _)))
  have hThr : {f | f ∈ F ∧ Thr J f}.ncard ≤ 6 := thr_ncard J hP hFA hfin
  have hCap := cap_ncard J
  have u1 : E₀.ncard ≤ {f | f ∈ F ∧ Thr J f}.ncard + (capChords J).ncard := Set.ncard_union_le _ _
  have u2 := Set.ncard_union_le I₁ I₂
  have u3 := Set.ncard_union_le E₀ (I₁ ∪ I₂)
  have i1 : I₁.ncard ≤ P.ncard := Set.ncard_image_le hPfin
  have i2 : I₂.ncard ≤ P.ncard := Set.ncard_image_le hPfin
  have hPu : P.ncard ≤ P₁.ncard + P₂.ncard := Set.ncard_union_le _ _
  have hsubn := Set.ncard_le_ncard hsub hfin'
  have hDA : D * (adjExits M F R).ncard ≤ D * (16 * D + 65) := Nat.mul_le_mul_left D hA
  show (exits M F R).ncard ≤ 7 + 4 * D * (16 * D + 65)
  rw [show 7 + 4 * D * (16 * D + 65) = 7 + 4 * (D * (16 * D + 65)) by ring]
  generalize D * (16 * D + 65) = Y at hDA ⊢
  generalize D * (adjExits M F R).ncard = Z at hDA h₁ h₂
  omega

end FuseDeg

end

end Chazelle.Core
