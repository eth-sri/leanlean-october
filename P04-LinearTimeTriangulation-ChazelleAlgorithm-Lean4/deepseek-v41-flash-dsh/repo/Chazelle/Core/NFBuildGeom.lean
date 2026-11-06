module

public import Chazelle.Golf

public import Chazelle.Core.FactsTie

/-!
# WP-C (BuildNF): walk-axiom facts for the region identification

Facts used to identify the regions of a submap with the labels of the stack pass
(`Chazelle.Core.NFBuildStack`):

* `WalkAx.exists_faces_nc`: every region is faced at a **non-cut** position inside a walk edge
  (the proof of `WalkAx.exists_faces`, which picks a position at a generic height, gives it);
* `WalkAx.separates_iff`: a chord separates two keys that are not its attachment keys iff exactly
  one of them lies in the arc from one attachment to the other;
* `WalkAx.not_touches_of_split`: a region faced strictly inside one arc of a chord `j` does not
  touch a chord `i ≠ j` attached strictly inside the other arc of `j`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj sideLeft_edge sideInArc_swap)
open Chazelle.Jordan (offset convex_det_pos)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

namespace WalkAx

variable {M : Model}

/-- **Every region is faced at a non-cut position** inside a walk edge. -/
theorem exists_faces_nc (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ ¬ M.IsCut F (p + t) ∧ M.Faces p t U := by
  have hsys := hM.sys F hF hfin
  have hUo : IsOpen U := hsys.regionsIn_open subset_rfl hU
  obtain ⟨z₀, hz₀⟩ := Chazelle.Chain.regionsIn_nonempty hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo z₀ hz₀
  -- a point of `U` at a generic height
  set B : Set ℝ := {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} ∪ {y | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}
    with hB
  have hBfin : B.Finite := by
    refine Set.Finite.union ?_ (finite_chord_heights hsys)
    have : {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} = (fun i => (M.W.vtx i).2) '' Iio M.W.n := by
      ext y; simp [mem_Iio]
    rw [this]; exact (finite_Iio _).image _
  obtain ⟨y, hyI, hyB⟩ := ((Ioo_infinite (lt_add_of_pos_right z₀.2 hr)).sdiff hBfin).nonempty
  set z : Point := (z₀.1, y) with hz
  have hzU : z ∈ U := by
    apply hball
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [hz, sub_self, abs_zero]
    rw [max_lt_iff, abs_of_pos (by linarith [hyI.1])]
    exact ⟨hr, by linarith [hyI.2]⟩
  have hUfree : U ⊆ freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hzD : z ∈ M.D := (hUfree hzU).1
  have hzv : ∀ i < M.W.n, z.2 ≠ (M.W.vtx i).2 := fun i hi h => hyB (Or.inl ⟨i, hi, h.symm⟩)
  have hzc : ∀ x : Point, x.2 = y → x ∉ ⋃₀ F := by
    rintro x hx ⟨c, hc, hxc⟩
    exact hyB (Or.inr ⟨c, hc, x, hxc, hx⟩)
  obtain ⟨s, hs, hseg, p, hp, t, ht, hq, hup⟩ := hM.reach z hzD hzv
  set q : Point := (z.1 + s, z.2) with hqdef
  -- the segment from `z` to `q` (half-open) is in `U`
  set L := (fun s' : ℝ => ((z.1 + s', z.2) : Point)) '' Ico 0 s with hL
  have hLc : IsPreconnected L :=
    isPreconnected_Ico.image _ (by fun_prop : Continuous fun s' : ℝ => ((z.1 + s', z.2) : Point)).continuousOn
  have hLF : L ⊆ freeIn M.D F := by
    rintro _ ⟨s', hs', rfl⟩
    exact ⟨hseg s' hs', hzc _ rfl⟩
  have hzL : z ∈ L := ⟨0, ⟨le_rfl, hs⟩, by simp [hz]⟩
  have hLU : L ⊆ U := by
    rw [Chazelle.Chain.regionsIn_eq_component hU hzU]
    exact hLc.subset_connectedComponentIn hzL hLF
  -- a half-disk on the left of the edge at `q` is free
  have hqF : q ∉ ⋃₀ F := hzc q rfl
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 (hsys.isClosed_sUnion subset_rfl).isOpen_compl q hqF
  obtain ⟨r₂, hr₂, hcl⟩ := hM.clean p hp t ht.1.le ht.2
  have hne := hM.nd p hp
  set u := M.W.vtx p
  set v := M.W.vtx ((p + 1) % M.W.n)
  set H : Set Point := ball q (min r₁ r₂) ∩ {x | 0 < 1 * det u v x} with hH
  have hHc : IsPreconnected H := ((convex_ball _ _).inter (convex_det_pos _ _ 1)).isPreconnected
  have hHF : H ⊆ freeIn M.D F := by
    rintro x ⟨hx1, hx2⟩
    simp only [mem_ofPred_eq, one_mul] at hx2
    refine ⟨?_, hb₁ (ball_subset_ball (min_le_left _ _) hx1)⟩
    by_contra hxD
    refine hcl x ?_ hxD ?_
    · rw [hq]; exact ball_subset_ball (min_le_right _ _) hx1
    · rw [sideLeft_edge hne ht]; exact hx2
  -- a point of the segment lies in the half-disk
  have hq0 : det u v q = 0 := by
    rw [← hq]; exact Geometry.det_lerp_self _ _ _
  set ε := min (min r₁ r₂) s / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; have := lt_min (lt_min hr₁ hr₂) hs; linarith
  have hεr : ε < min r₁ r₂ := by rw [hε]; have := min_le_left (min r₁ r₂) s; linarith
  have hεs : ε < s := by rw [hε]; have := min_le_right (min r₁ r₂) s; linarith
  have hw : ((z.1 + (s - ε), z.2) : Point) ∈ H := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [hqdef, sub_self, abs_zero]
      rw [max_lt_iff, show z.1 + (s - ε) - (z.1 + s) = -ε by ring, abs_neg, abs_of_pos hε0]
      exact ⟨hεr, lt_of_le_of_lt le_rfl (lt_min (lt_min hr₁ hr₂) hr₂ |>.trans_le (min_le_left _ _))⟩
    · simp only [mem_ofPred_eq, one_mul]
      have e : det u v ((z.1 + (s - ε), z.2) : Point) = det u v q + ε * (v.2 - u.2) := by
        simp only [hqdef, det]; ring
      rw [e, hq0]
      have : 0 < v.2 - u.2 := by linarith
      nlinarith
  have hwL : ((z.1 + (s - ε), z.2) : Point) ∈ L := ⟨s - ε, ⟨by linarith, by linarith⟩, rfl⟩
  have hHU : H ⊆ U := by
    rw [Chazelle.Chain.regionsIn_eq_component hU (hLU hwL)]
    exact hHc.subset_connectedComponentIn hw hHF
  refine ⟨p, t, hp, ht.1, ht.2, ?_, ?_⟩
  · rintro ⟨c, hc, p', t', hA', hk⟩
    obtain ⟨rfl, rfl⟩ := sideKey_inj ht.1.le ht.2 hA'.2.1 hA'.2.2.1 hk
    have hmem := hA'.2.2.2.1
    rw [hq] at hmem
    exact hzc _ rfl ⟨c, hc, hmem⟩
  filter_upwards [hM.eventually_offset_left hp ht (lt_min hr₁ hr₂)] with δ hδ
  apply hHU
  refine ⟨by rw [← hq]; exact hδ.1, ?_⟩
  simp only [mem_ofPred_eq, one_mul]
  rw [← sideLeft_edge hne ht]
  exact hδ.2

/-- **Separation by a chord in terms of one arc.** -/
theorem separates_iff (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {x x' : ℝ} (hxa : x ≠ pa + ta)
    (hxb : x ≠ pb + tb) (hx'a : x' ≠ pa + ta) (hx'b : x' ≠ pb + tb) :
    M.Separates c x x' ↔
      (sideInArc (pa + ta) (pb + tb) x ↔ ¬ sideInArc (pa + ta) (pb + tb) x') := by
  constructor
  · rintro ⟨pa', pb', ta', tb', hA', hB', hAB', hiff⟩
    obtain ⟨e, -, -, -, -, -, hoth⟩ := hM.attach_other_end hc hA
    have hBe : sidePt M.W pb tb = e := hoth pb tb hB (Ne.symm hAB)
    -- every attachment of `c` is `A` or `B`
    have hcase : ∀ (q : ℕ) (τ : ℝ), SideAttach M.W c q τ →
        (q = pa ∧ τ = ta) ∨ (q = pb ∧ τ = tb) := by
      intro q τ hQ
      by_cases h : sidePt M.W q τ = sidePt M.W pa ta
      · exact Or.inl (hM.attach_unique hc hQ hA h)
      · exact Or.inr (hM.attach_unique hc hQ hB (Ρ hoth q τ hQ h, hBe))
    have hkab : (pa : ℝ) + ta ≠ pb + tb := key_ne_of_pt_ne hA hB hAB
    rcases hcase pa' ta' hA' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hcase pb' tb' hB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hAB'
    · exact hiff
    · rw [sideInArc_swap (Ne.symm hkab) hxb hxa, sideInArc_swap (Ne.symm hkab) hx'b hx'a] at hiff
      tauto
    · exact absurd rfl hAB'
  · intro h
    exact ⟨pa, pb, ta, tb, hA, hB, hAB, h⟩

/-- **A region inside one arc of a chord does not touch a chord attached inside the other arc.** -/
theorem not_touches_of_split (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {i j : Set Point} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W j pa ta) (hB : SideAttach M.W j pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hin : sideInArc (pa + ta) (pb + tb) (p + t))
    (hf : M.Faces p t U) {pc : ℕ} {tc : ℝ} (hC : SideAttach M.W i pc tc)
    (hout : sideInArc (pb + tb) (pa + ta) (pc + tc)) : ¬ TouchesIn M.D i U := by
  rintro ⟨z, ⟨hzi, hzD⟩, hzU⟩
  have hsys := hM.sys F hF hfin
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hj) hA hB hAB
  have hUK : U ⊆ connectedComponentIn (M.D \ j) k₁ :=
    hM.region_subset_of_sector hj hU hp ht hf (hK₁ p hp t ht.1.le ht.2 hin)
  -- a point of `i ∩ D` in `K₂`, near its attachment `C`
  obtain ⟨r, hr, hsecr⟩ := hK₂ pc hC.1 tc hC.2.1 hC.2.2.1 hout
  obtain ⟨e, hev, -, hie, hopen, -⟩ := hM.attach_other_end (hF hi) hC
  obtain ⟨s, hs0, hs1, hdist, hleft⟩ := exists_left_on_chord hC hie hev hr
  set x := lerp (sidePt M.W pc tc) e s
  have hxi : x ∈ i ∩ M.D := ⟨by rw [hie]; exact lerp_mem_segment _ _ hs0.le hs1.le,
    hopen s ⟨hs0, hs1⟩⟩
  have hxK : x ∈ connectedComponentIn (M.D \ j) k₂ := hsecr _ (by rw [mem_ball]; exact hdist) hleft
  have hsub : i ∩ M.D ⊆ M.D \ j := fun y hy =>
    ⟨hy.2, fun hyj => hsys.inter_subset_compl hi hj hij ⟨hy.1, hyj⟩ hy.2⟩
  have hcon := (hsys.chord_inter_nonempty_isPreconnected hi).2.subset_connectedComponentIn
    hxi hsub
  have hzK : z ∈ connectedComponentIn (M.D \ j) k₂ := by
    rw [connectedComponentIn_eq hxK]; exact hcon ⟨hzi, hzD⟩
  have hopenK : IsOpen (connectedComponentIn (M.D \ j) k₂) :=
    (hM.isOpen.sdiff (hsys.isClosed_chord hj)).connectedComponentIn
  obtain ⟨u, huK, huU⟩ := mem_closure_iff.1 hzU _ hopenK hzK
  apply hne
  Ξ connectedComponentIn_eq (hUK huU), connectedComponentIn_eq huK

end WalkAx

end

end Chazelle.Core
