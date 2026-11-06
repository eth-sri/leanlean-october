module

public import Chazelle.Core.SweepEvInv

/-!
# The sweep (WP-D), stage 3: regions between non-enclosed positions, and sides of chords

Two facts about the regions of `F₂⁺` faced along the `C₁` part, used by the step lemmas of the
event loop:

* `evGL`: two non-cut positions that are not enclosed (`EvEncl`), with only bracket chords
  (`EvBrk`) attached between them, face the same region (no chord separates them);
* `side_comp` (any model): a region on a side of a chord `Z` attached at a position of one arc of
  a chord `c` is not faced at a position of the other arc (the two arcs have their sectors in the
  two components of `D \ c`, and `Z` lies in the second); `side_comp_off` in offsets.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc SideSectorIn)
open WalkEmbed

namespace Sweep

/-! ## Sides of a chord and the components of the split -/

section Comp

variable {M : Model}

/-- **A region on a side of a chord lies in the component of the chord's attachment** (with
respect to the split by another chord `c`): if `Z ∈ F`, `Z ≠ c`, is attached at `P` and the small
left sector at `P` lies in the component `K` of `D \ c`, every region on a side of `Z` meets `K`. -/
theorem side_meets_comp (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {c Z : Set Point}
    (hZ : Z ∈ F) {pz : ℕ} {tz : ℝ} (hP : SideAttach M.W Z pz tz) {k : Point}
    (hsec : SideSectorIn M.W (connectedComponentIn (M.D \ c) k) pz tz)
    (hcl : IsClosed c) {ρ : ℝ} {R : Set Point} (hRs : SideOf M ρ Z R) :
    (R ∩ connectedComponentIn (M.D \ c) k).Nonempty := by
  obtain ⟨a, b, hab, hZab, -, hopen, -, -⟩ := hM.ends Z (hF hZ)
  have hPZ := hP
  rw [hZab] at hPZ
  obtain ⟨r, hr, hs⟩ := hsec
  obtain ⟨-, -, -, -, r', hr', hleft⟩ := hP
  -- an endpoint `e` of `Z` at `P` and the other endpoint `f`
  obtain ⟨e, f, hef, hZef, hPe, hopen'⟩ : ∃ e f : Point, e ≠ f ∧ Z = Chazelle.segment e f ∧
      sidePt M.W pz tz = e ∧ ∀ s ∈ Ioo (0 : ℝ) 1, Geometry.lerp e f s ∈ M.D := by
    rcases hM.attach_endpoint hopen hPZ with h | h
    · exact ⟨a, b, hab, hZab, h, hopen⟩
    · refine ⟨b, a, hab.symm, by rw [hZab]; exact Chazelle.Jordan.segment_comm a b, h, fun s hs => ?_⟩
      rw [Geometry.lerp_symm]
      exact hopen (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hcont : Tendsto (fun s : ℝ => Geometry.lerp e f s) (𝓝[>] (0 : ℝ)) (𝓝 e) := by
    have := (Geometry.continuous_lerp e f).tendsto 0
    rw [Geometry.lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hball : ∀ᶠ s in 𝓝[>] (0 : ℝ), Geometry.lerp e f s ∈ ball e (min r r') :=
    hcont (ball_mem_nhds e (lt_min hr hr'))
  obtain ⟨s, hsb, hs1⟩ := (hball.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  set z := Geometry.lerp e f s with hz
  have hzZ : z ∈ Z := by
    rw [hZef]; exact Geometry.mem_segment_iff_lerp.2 ⟨s, hs1.1.le, hs1.2.le, rfl⟩
  have hzD : z ∈ M.D := hopen' s hs1
  have hze : z ≠ e := by
    intro h
    have hzD' := hzD
    rw [h] at hzD'
    exact hM.trace pz (by have := hPZ.1; exact this) tz hPZ.2.1 hPZ.2.2.1.le (hPe ▸ hzD')
  have hdist : dist z e < min r r' := hsb
  have hzL : Chazelle.Chain.sideLeft M.W pz tz z :=
    hleft z hzZ (by rw [hPe]; exact hze) (by rw [hPe]; exact lt_of_lt_of_le hdist (min_le_right _ _))
  have hzK : z ∈ connectedComponentIn (M.D \ c) k :=
    hs z (by rw [mem_ball, hPe]; exact lt_of_lt_of_le hdist (min_le_left _ _)) hzL
  -- the component is open, so the points just beside `z` are in it
  have hKo : IsOpen (connectedComponentIn (M.D \ c) k) :=
    (hM.isOpen.sdiff hcl).connectedComponentIn
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + ρ * δ) : Point) ∈ connectedComponentIn (M.D \ c) k := by
    have hc : Continuous (fun δ : ℝ => ((z.1, z.2 + ρ * δ) : Point)) := by fun_prop
    have h0 : ((z.1, z.2 + ρ * 0) : Point) = z := by simp
    have := hc.tendsto 0
    rw [h0] at this
    exact (this.mono_left nhdsWithin_le_nhds) (hKo.mem_nhds hzK)
  obtain ⟨δ, h1, h2⟩ := ((hRs z hzZ hzD).and hev).exists
  exact ⟨_, h1, h2⟩

/-- **A region on a side of a chord attached in one arc of `c` is not faced in the other arc.** -/
theorem side_comp (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) {c Z : Set Point}
    (hc : c ∈ F) (hZ : Z ∈ F) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {pz : ℕ} {tz : ℝ}
    (hP : SideAttach M.W Z pz tz) (hPin : sideInArc (pb + tb) (pa + ta) (pz + tz)) {ρ : ℝ}
    {R : Set Point} (hR : R ∈ M.regions F) (hRs : SideOf M ρ Z R) {py : ℕ} {ty : ℝ}
    (hpy : py < M.W.n) (hty : ty ∈ Ioo (0 : ℝ) 1) (hyin : sideInArc (pa + ta) (pb + tb) (py + ty))
    (hfy : M.Faces py ty R) : False := by
  obtain ⟨K₁, K₂, hne, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, h₁, h₂⟩ := hM.split (hF hc) hA hB hAB
  have hR1 := hM.region_subset_of_sector hc hR hpy hty hfy (h₁ py hpy ty hty.1.le hty.2 hyin)
  have hcl : IsClosed c := by
    obtain ⟨a, b, -, hcab, -⟩ := hM.ends c (hF hc)
    rw [hcab]; exact Chazelle.Geometry.isClosed_segment a b
  obtain ⟨w, hwR, hw2⟩ := side_meets_comp hM hF hZ hP (h₂ pz hP.1 tz hP.2.1 hP.2.2.1 hPin) hcl hRs
  have hw1 := hR1 hwR
  exact hne ((connectedComponentIn_eq hw1).trans (connectedComponentIn_eq hw2).symm)

end Comp

/-! ## The junction: offsets -/

section Junction

variable {J : Merge.Junction}

/-- **`side_comp` in offsets** (from the base `gW`): `c` attached at offsets `oA < oB`, `Z ≠ c`
attached at an offset outside `[oA, oB]`; a region on a side of `Z` is not faced at a position with
offset in `(oA, oB)`. -/
theorem side_comp_off (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c Z : Set Point}
    (hc : c ∈ F₂plus J S₂) (hZ : Z ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W c pa ta) (hB : SideAttach (chainModel J.whole).W c pb tb)
    (hAB : oW J (pa + ta) < oW J (pb + tb)) {pz : ℕ} {tz : ℝ}
    (hPz : SideAttach (chainModel J.whole).W Z pz tz)
    (hPout : oW J (pz + tz) < oW J (pa + ta) ∨ oW J (pb + tb) < oW J (pz + tz)) {ρ : ℝ}
    {R : Set Point} (hR : R ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hRs : SideOf (chainModel J.whole) ρ Z R) {py : ℕ} {ty : ℝ}
    (hpy : py < (chainModel J.whole).W.n) (hty : ty ∈ Ioo (0 : ℝ) 1)
    (hy1 : oW J (pa + ta) < oW J (py + ty)) (hy2 : oW J (py + ty) < oW J (pb + tb))
    (hfy : (chainModel J.whole).Faces py ty R) : False := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  obtain ⟨a0, a1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  obtain ⟨z0, z1⟩ := Corr.key_mem hPz.1 hPz.2.1 hPz.2.2.1
  obtain ⟨y0, y1⟩ := Corr.key_mem hpy hty.1.le hty.2
  have hAB' : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb := by
    intro h
    obtain ⟨rfl, rfl⟩ := hC.hM.attach_unique (hC.hF hc) hA hB h
    exact lt_irrefl _ hAB
  refine side_comp hC.hM hC.hF hc hZ hA hB hAB' hPz
    ((sideInArc_rev_iff_off hg0 hgn a0 a1 b0 b1 z0 z1 hAB).2 hPout) hR hRs hpy hty
    ((sideInArc_iff_off hg0 hgn a0 a1 b0 b1 y0 y1 hAB).2 ⟨hy1, hy2⟩) hfy

/-- Two attachments of a chord with distinct offsets have distinct points. -/
theorem pt_ne_of_off_ne (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {c : Set Point}
    (hc : c ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W c pa ta) (hB : SideAttach (chainModel J.whole).W c pb tb)
    (hne : oW J (pa + ta) ≠ oW J (pb + tb)) :
    sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb := by
  have hC := corr_right0 J hP hS₂ hS₂f
  intro h
  obtain ⟨rfl, rfl⟩ := hC.hM.attach_unique (hC.hF hc) hA hB h
  exact hne rfl

/-- **Regions between two non-enclosed positions** (`GL`): two non-cut positions on the walk, not
enclosed, with only bracket chords attached at offsets strictly between them, face the same
region. -/
theorem evGL (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {p p' : ℕ} {t t' : ℝ} (hp : p < (chainModel J.whole).W.n)
    (hp' : p' < (chainModel J.whole).W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + t))
    (hnc' : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p' + t'))
    (hlt : oW J (p + t) < oW J (p' + t')) (hE : ¬ EvEncl J S₂ (oW J (p + t)))
    (hE' : ¬ EvEncl J S₂ (oW J (p' + t')))
    (hbr : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oW J (p + t) < oW J (q + s) → oW J (q + s) < oW J (p' + t') → EvBrk J e)
    {G G' : Set Point} (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hG' : G' ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hf : (chainModel J.whole).Faces p t G) (hf' : (chainModel J.whole).Faces p' t' G') :
    G = G' := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  refine (hC.hM.eq_iff_not_separates hC.hF hC.hfin hG hG' hp hp' ht ht' hnc hnc' hf hf').2
    fun c hc ⟨pa, pb, ta, tb, hA, hB, hAB, hsep⟩ => ?_
  obtain ⟨a0, a1⟩ := Corr.key_mem hA.1 hA.2.1 hA.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  obtain ⟨x0, x1⟩ := Corr.key_mem hp ht.1.le ht.2
  obtain ⟨y0, y1⟩ := Corr.key_mem hp' ht'.1.le ht'.2
  have hk := WalkAx.key_ne_of_pt_ne (M := chainModel J.whole) hA hB hAB
  have hxy : (p : ℝ) + t ≠ p' + t' := by
    intro h; rw [h] at hlt; exact lt_irrefl _ hlt
  have hxa : (p : ℝ) + t ≠ pa + ta := fun h => hnc ⟨c, hc, pa, ta, hA, h⟩
  have hxb : (p : ℝ) + t ≠ pb + tb := fun h => hnc ⟨c, hc, pb, tb, hB, h⟩
  have hya : (p' : ℝ) + t' ≠ pa + ta := fun h => hnc' ⟨c, hc, pa, ta, hA, h⟩
  have hyb : (p' : ℝ) + t' ≠ pb + tb := fun h => hnc' ⟨c, hc, pb, tb, hB, h⟩
  have hs := (sep_iff_btw hg0 hgn a0 a1 b0 b1 x0 x1 y0 y1 hk hxy hxa hxb hya hyb).1 hsep
  have hne : ∀ {u w : ℝ}, 0 ≤ u → u < (chainModel J.whole).W.n → 0 ≤ w →
      w < (chainModel J.whole).W.n → u ≠ w → oW J u ≠ oW J w :=
    fun hu hun hw hwn huw h => huw (off_inj hg0 hgn hu hun hw hwn h)
  have hoxa := hne x0 x1 a0 a1 hxa
  have hoxb := hne x0 x1 b0 b1 hxb
  have hoya := hne y0 y1 a0 a1 hya
  have hoyb := hne y0 y1 b0 b1 hyb
  -- one attachment strictly inside, the other outside
  have key : ∀ {qa qb : ℕ} {sa sb : ℝ}, SideAttach (chainModel J.whole).W c qa sa →
      SideAttach (chainModel J.whole).W c qb sb →
      sidePt (chainModel J.whole).W qa sa ≠ sidePt (chainModel J.whole).W qb sb →
      oW J (p + t) < oW J (qa + sa) → oW J (qa + sa) < oW J (p' + t') →
      oW J (qb + sb) ≠ oW J (p + t) → oW J (qb + sb) ≠ oW J (p' + t') →
      ¬ (oW J (p + t) < oW J (qb + sb) ∧ oW J (qb + sb) < oW J (p' + t')) → False := by
    intro qa qb sa sb hQA hQB hQAB h1 h2 h3 h4 hout
    have hbrk := hbr c hc qa sa hQA h1 h2
    rcases lt_or_gt_of_ne h4 with h5 | h5
    · rcases lt_or_gt_of_ne h3 with h6 | h6
      · -- the other end before `x`: `x` is enclosed
        exact hE ⟨c, hc, qb, qa, sb, sa, hQB, hQA, hQAB.symm, hbrk qb sb hQB, h6, Or.inl h1⟩
      · exact hout ⟨h6, h5⟩
    · -- the other end after `y`: `y` is enclosed
      exact hE' ⟨c, hc, qa, qb, sa, sb, hQA, hQB, hQAB, hbrk qa sa hQA, h2, Or.inl h5⟩
  unfold Btw at hs
  by_cases ha : oW J (p + t) < oW J (pa + ta) ∧ oW J (pa + ta) < oW J (p' + t')
  · have hnb : ¬ (oW J (p + t) < oW J (pb + tb) ∧ oW J (pb + tb) < oW J (p' + t')) := by
      intro hb
      have := hs.1 (Or.inl ha)
      exact this (Or.inl hb)
    exact key hA hB hAB ha.1 ha.2 hoxb.symm hoyb.symm hnb
  · have hb : oW J (p + t) < oW J (pb + tb) ∧ oW J (pb + tb) < oW J (p' + t') := by
      by_contra hb
      have h1 : ¬ ((oW J (p + t) < oW J (pa + ta) ∧ oW J (pa + ta) < oW J (p' + t')) ∨
          (oW J (p' + t') < oW J (pa + ta) ∧ oW J (pa + ta) < oW J (p + t))) := by
        rintro (h | h)
        · exact ha h
        · linarith [h.1, h.2]
      have h2 : ¬ ((oW J (p + t) < oW J (pb + tb) ∧ oW J (pb + tb) < oW J (p' + t')) ∨
          (oW J (p' + t') < oW J (pb + tb) ∧ oW J (pb + tb) < oW J (p + t))) := by
        rintro (h | h)
        · exact hb h
        · linarith [h.1, h.2]
      exact h1 (hs.2 h2)
    exact key hB hA hAB.symm hb.1 hb.2 hoxa.symm hoya.symm ha

end Junction

end Sweep

end

end Chazelle.Core
