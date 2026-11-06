module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseHostKey
public import Chazelle.Core.FactsTie
public import Chazelle.Core.FactsL23
public import Chazelle.Core.FactsTree
public import Chazelle.Core.Facts2TrapDeg

/-!
# WP-M (H1, part 2): the host keys of a region

For a region `U` of a finite admissible family `F` of a model with the walk axioms, the **host
keys** of `U` are the keys of the walk vertices inside the arcs of `U` and the attachment keys of
the exit chords of `U` (`hostKeys`).  Sorted, they are the vertex keys of the host polygon `R*`
of the down phase (design `docs/design-downphase.md` §2.3 (a)).

* `hostKeys_finite`, `hostKeys_bounds`;
* `WalkAx.host_side` (**separation**): if the attachments `A`, `B` of a chord `c ∈ F` split the
  walk so that the positions strictly between `A` and `B` have their small left sectors in a
  component `K` of `D \ c`, then a host key of `U` strictly between `A` and `B` forces `U ⊆ K`.
  (Vertex keys: the positions just after them face `U`; attachment keys of an exit chord `c'`: the
  open part of `c'` starts in the left sector there, lies in one component of `D \ c`, and touches
  `U`.)
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideSectorIn ChordSystem freeIn
  regionsIn TouchesIn)
open Chazelle.Geometry (lerp lerp_mem_segment)

variable (M : Model) (F : Set (Set Point)) (U : Set Point)

/-- The attachment keys of the exit chords of `U`. -/
def exitKeys : Set ℝ :=
  {x | ∃ c ∈ F, TouchesIn M.D c U ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ x = p + t}

/-- The keys of the walk vertices strictly inside the arcs of `U`. -/
def vtxKeys : Set ℝ :=
  {x | ∃ k : ℕ, k < M.W.n ∧ x = k ∧ ∃ a b : ℝ, M.IsArc F U a b ∧ sideInArc a b k}

/-- **The host keys of `U`**. -/
def hostKeys : Set ℝ := exitKeys M F U ∪ vtxKeys M F U

variable {M F U}

theorem exitKeys_subset_cuts : exitKeys M F U ⊆ {x | M.IsCut F x} := by
  rintro x ⟨c, hc, -, p, t, hA, rfl⟩
  exact ⟨c, hc, p, t, hA, rfl⟩

theorem vtxKeys_finite : (vtxKeys M F U).Finite := by
  refine ((Finset.range M.W.n).finite_toSet.image (fun k : ℕ => (k : ℝ))).subset ?_
  rintro x ⟨k, hk, rfl, -⟩
  exact ⟨k, by simpa using hk, rfl⟩

theorem hostKeys_finite (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    (hostKeys M F U).Finite :=
  ((hM.finite_cuts hF hfin).subset exitKeys_subset_cuts).union vtxKeys_finite

/-- Host keys lie in `[0, n)`. -/
theorem hostKeys_bounds {x : ℝ} (hx : x ∈ hostKeys M F U) : 0 ≤ x ∧ x < M.W.n := by
  rcases hx with hx | ⟨k, hk, rfl, -⟩
  · exact WalkAx.cut_bounds (exitKeys_subset_cuts hx)
  · exact ⟨Nat.cast_nonneg k, by exact_mod_cast hk⟩

/-- Distinct chords of a finite admissible family do not meet in the domain. -/
theorem chord_disj (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) (hne : c ≠ c') {z : Point} (hz : z ∈ c) (hz' : z ∈ c')
    (hzD : z ∈ M.D) : False := by
  have hsys := hM.sys F hF hfin
  obtain ⟨y, a, b, h, rfl⟩ := hsys.hchord c hc
  obtain ⟨y', a', b', h', rfl⟩ := hsys.hchord c' hc'
  exact hne (SegObs.eq_of_common ⟨y, a, b, h, rfl⟩ ⟨y', a', b', h', rfl⟩ hz hz' hzD)

/-- Small positive numbers, as an eventual statement. -/
theorem ev_Ioo {a b : ℝ} (h : a < b) : ∀ᶠ ε in 𝓝[>] a, ε ∈ Ioo a b := Ioo_mem_nhdsGT h

/-- Numbers just below `b`, as an eventual statement. -/
theorem ev_Ioo_lt {a b : ℝ} (h : a < b) : ∀ᶠ ε in 𝓝[<] b, ε ∈ Ioo a b := Ioo_mem_nhdsLT h

/-- The start of a cyclic interval is not inside it. -/
theorem not_sideInArc_left (a b : ℝ) : ¬ sideInArc a b a := by
  unfold sideInArc; split_ifs with h
  · exact fun h' => lt_irrefl _ h'.1
  · rintro (h' | h')
    · exact lt_irrefl _ h'
    · exact h h'

/-- The end of a cyclic interval is not inside it. -/
theorem not_sideInArc_right (a b : ℝ) : ¬ sideInArc a b b := by
  unfold sideInArc; split_ifs with h
  · exact fun h' => lt_irrefl _ h'.2
  · rintro (h' | h')
    · exact h h'
    · exact lt_irrefl _ h'

/-- Keys strictly after a key inside an open cyclic interval stay inside it. -/
theorem eventually_in_arc {a b k : ℝ} (hk : sideInArc a b k) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (k + ε) := by
  unfold sideInArc at *
  split_ifs at * with h
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < b - k by linarith)]
      with ε hε hε'
    have : (0 : ℝ) < ε := hε
    exact ⟨by linarith, by linarith [hε'.2]⟩
  · rcases hk with hk | hk
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have : (0 : ℝ) < ε := hε
      left; linarith
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < b - k by linarith)]
        with ε hε hε'
      right; linarith [hε'.2]

/-- **Separation.**  If the positions strictly between the attachments `A`, `B` of `c ∈ F` have
their small left sectors in the component `K` of `D \ c` of `k₁`, a host key of `U` strictly
between `A` and `B` forces `U ⊆ K`. -/
theorem host_side (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hU : U ∈ M.regions F) {c : Set Point} (hc : c ∈ F) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {k₁ : Point}
    (hK : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pa + ta) (pb + tb) (p + t) →
      SideSectorIn M.W (connectedComponentIn (M.D \ c) k₁) p t)
    {x : ℝ} (hx : x ∈ hostKeys M F U) (hxin : sideInArc (pa + ta) (pb + tb) x) :
    U ⊆ connectedComponentIn (M.D \ c) k₁ := by
  set K := connectedComponentIn (M.D \ c) k₁ with hKdef
  have hUfree : U ⊆ M.D \ c := fun y hy =>
    ⟨(Chazelle.Chain.regionsIn_subset hU hy).1,
      fun hyc => (Chazelle.Chain.regionsIn_subset hU hy).2 ⟨c, hc, hyc⟩⟩
  have hUpre := Chazelle.Chain.regionsIn_isPreconnected hU
  have hKo : IsOpen K :=
    (hM.isOpen.sdiff ((hM.sys F hF hfin).isClosed_chord hc)).connectedComponentIn
  -- a point of `U` in `K` suffices
  have hmeet : ∀ u ∈ U, u ∈ K → U ⊆ K := fun u hu huK => by
    rw [hKdef, connectedComponentIn_eq huK]
    exact hUpre.subset_connectedComponentIn hu hUfree
  rcases hx with ⟨c', hc', htouch, p, t, hA', rfl⟩ | ⟨k, hk, rfl, a, b, harc, hkab⟩
  · -- an exit chord `c'` attached strictly between `A` and `B`
    have hcc' : c' ≠ c := by
      rintro rfl
      obtain ⟨hcab, -, hopen, -, -⟩ := hM.attach_seg (hF hc) hA hB hAB
      rcases hM.attach_endpoint hopen (hcab ▸ hA') with h | h
      · obtain ⟨rfl, rfl⟩ := hM.attach_unique (hF hc) hA' hA h
        exact not_sideInArc_left _ _ hxin
      · obtain ⟨rfl, rfl⟩ := hM.attach_unique (hF hc) hA' hB h
        exact not_sideInArc_right _ _ hxin
    obtain ⟨e, he, -, hce, hopen, heD, -⟩ := hM.attach_other_end (hF hc') hA'
    obtain ⟨r, hr, hsec⟩ := hK p hA'.1 t hA'.2.1 hA'.2.2.1 hxin
    obtain ⟨s, hs0, hs1, hsd, hsl⟩ := WalkAx.exists_left_on_chord hA' hce he hr
    have hyK : lerp (sidePt M.W p t) e s ∈ K := hsec _ (by rw [mem_ball]; exact hsd) hsl
    -- the open part of `c'` lies in `K`
    have hopenK : ∀ s' ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W p t) e s' ∈ K := by
      have hpre : IsPreconnected ((lerp (sidePt M.W p t) e) '' Ioo (0 : ℝ) 1) :=
        isPreconnected_Ioo.image _ (Chazelle.Geometry.continuous_lerp _ _).continuousOn
      have hsub : (lerp (sidePt M.W p t) e) '' Ioo (0 : ℝ) 1 ⊆ M.D \ c := by
        rintro _ ⟨s', hs', rfl⟩
        refine ⟨hopen s' hs', fun hmem => chord_disj hM hF hfin hc' hc hcc' ?_ hmem (hopen s' hs')⟩
        rw [hce]; exact lerp_mem_segment _ _ hs'.1.le hs'.2.le
      intro s' hs'
      rw [hKdef, connectedComponentIn_eq hyK]
      exact hpre.subset_connectedComponentIn ⟨s, ⟨hs0, hs1⟩, rfl⟩ hsub ⟨s', hs', rfl⟩
    -- the touching point is in the open part, hence in `K`
    obtain ⟨z, ⟨hzc, hzD⟩, hzcl⟩ := htouch
    rw [hce] at hzc
    obtain ⟨s', hs'0, hs'1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzc
    have hs'0' : 0 < s' := by
      rcases hs'0.lt_or_eq with h | h
      · exact h
      · subst h; rw [Chazelle.Geometry.lerp_zero] at hzD
        exact absurd hzD (hM.trace p hA'.1 t hA'.2.1 hA'.2.2.1.le)
    have hs'1' : s' < 1 := by
      rcases hs'1.lt_or_eq with h | h
      · exact h
      · subst h; rw [Chazelle.Geometry.lerp_one] at hzD
        exact absurd hzD heD
    have hzK := hopenK s' ⟨hs'0', hs'1'⟩
    obtain ⟨u, huK, hu⟩ := mem_closure_iff.1 hzcl K hKo hzK
    exact hmeet u hu huK
  · -- a walk vertex inside an arc of `U`: positions just after it face `U`
    obtain ⟨ε, ⟨hε0, hε1⟩, hin1, hin2⟩ := ((ev_Ioo (show (0 : ℝ) < 1 by norm_num)).and
      ((eventually_in_arc hxin).and (eventually_in_arc hkab))).exists
    have hfac := harc.2.2.2.2.2.2 k ε hk hε0 hε1 hin2
    exact hM.region_subset_of_sector hc hU hk ⟨hε0, hε1⟩ hfac
      (hK k hk ε hε0.le hε1 hin1)
