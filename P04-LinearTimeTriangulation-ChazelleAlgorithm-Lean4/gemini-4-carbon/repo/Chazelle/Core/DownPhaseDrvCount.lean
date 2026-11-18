module

public import Chazelle.Core.DownPhaseHostSimple
public import Chazelle.Core.DownPhaseHostData

/-!
# Down-phase driver, D10 (part 1): the total number of host keys

For a finite admissible family `F` of a model with the walk axioms, the host polygons of all
regions together have at most `n + 4|F|` points (`sum_nk_le`):

* the walk vertex keys inside the arcs of different regions are disjoint (a position just after
  such a key faces a unique region), so they number at most `n` in total;
* a chord has at most two attachment keys (`attachKeys_ncard_le`: one per end, by the uniqueness
  part of the walk axiom `ends`), so the exit keys of a region number at most twice its degree,
  and the degrees sum to at most `2|F|` (`Merge.potential_le`).

This bounds the sizes `m_R` of the region chains, hence (Lemma 2.3) the chords the merges produce
per level (design `docs/design-downphase-driver.md` §4.2, D10).
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft TouchesIn regionsIn)
open DownHost

variable {M : Model} {F : Set (Set Point)}

/-- The attachment keys of a chord. -/
def attachKeys (M : Model) (c : Set Point) : Set ℝ :=
  {x | ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ x = p + t}

/-- Points of a segment arbitrarily close to either end. -/
theorem near_end {a b : Point} (hab : a ≠ b) {ρ : ℝ} (hρ : 0 < ρ) (e : Point)
    (he : e = a ∨ e = b) : ∃ x ∈ Chazelle.segment a b, x ≠ e ∧ dist x e < ρ := by
  set L := |b.1 - a.1| + |b.2 - a.2| + 1 with hL
  have hL0 : 0 < L := by positivity
  set s := min (1 / 2 : ℝ) (ρ / (2 * L)) with hs
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hsL : s * L ≤ ρ / 2 := by
    have := min_le_right (1 / 2 : ℝ) (ρ / (2 * L))
    calc s * L ≤ ρ / (2 * L) * L := mul_le_mul_of_nonneg_right this hL0.le
      _ = ρ / 2 := by field_simp
  have hb1 : |b.1 - a.1| ≤ L := by rw [hL]; have := abs_nonneg (b.2 - a.2); linarith
  have hb2 : |b.2 - a.2| ≤ L := by rw [hL]; have := abs_nonneg (b.1 - a.1); linarith
  have hne : ∀ u : ℝ, u ≠ 0 → (u * (b.1 - a.1), u * (b.2 - a.2)) ≠ ((0 : ℝ), (0 : ℝ)) := by
    intro u hu h
    have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only at h1 h2
    apply hab
    rcases mul_eq_zero.1 h1 with h1 | h1
    · exact absurd h1 hu
    rcases mul_eq_zero.1 h2 with h2 | h2
    · exact absurd h2 hu
    exact Prod.ext (by linarith) (by linarith)
  rcases he with rfl | rfl
  · refine ⟨(e.1 + s * (b.1 - e.1), e.2 + s * (b.2 - e.2)), ⟨s, hs0.le, by linarith, rfl⟩, ?_, ?_⟩
    · intro h
      apply hne s hs0.ne'
      have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      simp only at h1 h2
      exact Prod.ext (by simp only; linear_combination h1) (by simp only; linear_combination h2)
    · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [add_sub_cancel_left, abs_mul, abs_of_pos hs0]
      refine max_lt ?_ ?_
      · nlinarith [abs_nonneg (b.1 - e.1)]
      · nlinarith [abs_nonneg (b.2 - e.2)]
  · refine ⟨(a.1 + (1 - s) * (e.1 - a.1), a.2 + (1 - s) * (e.2 - a.2)),
      ⟨1 - s, by linarith, by linarith, rfl⟩, ?_, ?_⟩
    · intro h
      apply hne s hs0.ne'
      have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
      simp only at h1 h2
      exact Prod.ext (by simp only; linear_combination -h1) (by simp only; linear_combination -h2)
    · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have e1 : a.1 + (1 - s) * (e.1 - a.1) - e.1 = -(s * (e.1 - a.1)) := by ring
      have e2 : a.2 + (1 - s) * (e.2 - a.2) - e.2 = -(s * (e.2 - a.2)) := by ring
      rw [e1, e2, abs_neg, abs_neg, abs_mul, abs_mul, abs_of_pos hs0]
      refine max_lt ?_ ?_
      · nlinarith [abs_nonneg (e.1 - a.1)]
      · nlinarith [abs_nonneg (e.2 - a.2)]

/-- **A chord has at most two attachment keys** (one at each end). -/
theorem attachKeys_sub (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ k₁ k₂ : ℝ, attachKeys M c ⊆ {k₁, k₂} := by
  obtain ⟨a, b, hab, hcab, -, hopen, hEa, hEb⟩ := hM.ends c hc
  obtain ⟨pa, ta, hAa, hPa⟩ := hEa.1
  obtain ⟨pb, tb, hAb, hPb⟩ := hEb.1
  refine ⟨pa + ta, pb + tb, ?_⟩
  rintro x ⟨p, t, hA, rfl⟩
  have hPc : sidePt M.W p t ∈ c := hA.2.2.2.1
  have hend : sidePt M.W p t = a ∨ sidePt M.W p t = b := by
    rw [hcab] at hPc
    obtain ⟨s, hs0, hs1, hs⟩ := hPc
    rcases hs0.lt_or_eq with h0 | h0
    · rcases hs1.lt_or_eq with h1 | h1
      · exfalso
        apply hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
        rw [hs]; exact hopen s ⟨h0, h1⟩
      · right; rw [hs, h1]; simp
    · left; rw [hs, ← h0]; simp
  have key : ∀ (e : Point) (pe : ℕ) (te : ℝ), (e = a ∨ e = b) → WalkEnd M.W c e →
      SideAttach M.W c pe te → sidePt M.W pe te = e → sidePt M.W p t = e → p = pe ∧ t = te := by
    intro e pe te hee hE hAe hPe hP
    by_contra hne
    have hne' : p = pe → t ≠ te := fun h1 h2 => hne ⟨h1, h2⟩
    obtain ⟨r, hr, hdisj⟩ := hE.2 p pe t te hA.1 hA.2.1 hA.2.2.1 hAe.1 hAe.2.1 hAe.2.2.1 hne' hP hPe
    obtain ⟨r1, hr1, hs1⟩ := hA.2.2.2.2
    obtain ⟨r2, hr2, hs2⟩ := hAe.2.2.2.2
    obtain ⟨x, hx, hxe, hxd⟩ := near_end hab (lt_min hr (lt_min hr1 hr2)) e hee
    have hxc : x ∈ c := by rw [hcab]; exact hx
    have h1 := hs1 x hxc (by rw [hP]; exact hxe)
      (by rw [hP]; exact lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _)))
    have h2 := hs2 x hxc (by rw [hPe]; exact hxe)
      (by rw [hPe]; exact lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _)))
    exact hdisj x (lt_of_lt_of_le hxd (min_le_left _ _)) h1 h2
  rcases hend with h | h
  · obtain ⟨rfl, rfl⟩ := key a pa ta (Or.inl rfl) hEa hAa hPa h
    exact Or.inl rfl
  · obtain ⟨rfl, rfl⟩ := key b pb tb (Or.inr rfl) hEb hAb hPb h
    exact Or.inr rfl

theorem attachKeys_ncard_le (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    (attachKeys M c).ncard ≤ 2 := by
  obtain ⟨k₁, k₂, hsub⟩ := attachKeys_sub hM hc
  refine (ncard_le_ncard hsub (toFinite _)).trans ?_
  refine (ncard_insert_le _ _).trans ?_
  rw [ncard_singleton]

/-- A union of sets of at most two elements over a finite index set. -/
theorem ncard_biUnion_le_two {E : Set (Set Point)} (hE : E.Finite) (f : Set Point → Set ℝ)
    (hf : ∀ c ∈ E, (f c).ncard ≤ 2) : (⋃ c ∈ E, f c).ncard ≤ 2 * E.ncard := by
  induction E, hE using Set.Finite.induction_on with
  | empty => simp
  | @insert c E hcE hE ih =>
    rw [Set.biUnion_insert, ncard_insert_of_notMem hcE hE]
    refine (ncard_union_le _ _).trans ?_
    have h1 := hf c (mem_insert c E)
    have h2 := ih fun d hd => hf d (mem_insert_of_mem c hd)
    omega

/-- **The exit keys of a region number at most twice its degree.** -/
theorem exitKeys_ncard_le (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (U : Set Point) :
    (exitKeys M F U).ncard ≤ 2 * M.deg F U := by
  set E := {c | c ∈ F ∧ TouchesIn M.D c U} with hE
  have hEfin : E.Finite := hfin.subset fun c hc => hc.1
  have hsub : exitKeys M F U ⊆ ⋃ c ∈ E, attachKeys M c := by
    rintro x ⟨c, hc, ht, p, t, hA, rfl⟩
    exact mem_iUnion₂.2 ⟨c, ⟨hc, ht⟩, p, t, hA, rfl⟩
  have hfinU : (⋃ c ∈ E, attachKeys M c).Finite := hEfin.biUnion fun c hc => by
    obtain ⟨k₁, k₂, h⟩ := attachKeys_sub hM (hF hc.1)
    exact (toFinite _).subset h
  exact (ncard_le_ncard hsub hfinU).trans
    (ncard_biUnion_le_two hEfin _ fun c hc => attachKeys_ncard_le hM (hF hc.1))

/-- The walk vertices strictly inside the arcs of a region. -/
def vtxIdx (M : Model) (F : Set (Set Point)) (U : Set Point) : Set ℕ :=
  {k | k < M.W.n ∧ ∃ a b : ℝ, M.IsArc F U a b ∧ sideInArc a b k}

theorem vtxKeys_eq (U : Set Point) : vtxKeys M F U = (fun k : ℕ => (k : ℝ)) '' vtxIdx M F U := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl, a, b, harc, hin⟩
    exact ⟨k, ⟨hk, a, b, harc, hin⟩, rfl⟩
  · rintro ⟨k, ⟨hk, a, b, harc, hin⟩, rfl⟩
    exact ⟨k, hk, rfl, a, b, harc, hin⟩

theorem vtxKeys_ncard (U : Set Point) : (vtxKeys M F U).ncard = (vtxIdx M F U).ncard := by
  rw [vtxKeys_eq, ncard_image_of_injective _ Nat.cast_injective]

/-- **The inner vertices of distinct regions are disjoint.** -/
theorem vtxIdx_disjoint {U U' : Set Point} (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F)
    (hne : U ≠ U') : Disjoint (vtxIdx M F U) (vtxIdx M F U') := by
  rw [Set.disjoint_left]
  rintro k ⟨hk, a, b, harc, hin⟩ ⟨-, a', b', harc', hin'⟩
  have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (k + ε) ∧ sideInArc a' b' (k + ε) ∧
      ε ∈ Ioo (0 : ℝ) 1 :=
    (eventually_in_arc hin).and ((eventually_in_arc hin').and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨t, ht1, ht2, ht3⟩ := ev.exists
  have hf := harc.2.2.2.2.2.2 k t hk ht3.1 ht3.2 ht1
  have hf' := harc'.2.2.2.2.2.2 k t hk ht3.1 ht3.2 ht2
  obtain ⟨δ, hδ1, hδ2⟩ := (hf.and hf').exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hU' with h | h
  · exact hne h
  · exact h.le_bot ⟨hδ1, hδ2⟩


/-- **The host keys of a region**: at most its inner vertices plus twice its degree. -/
theorem nk_le (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (U : Set Point) :
    nk M F U ≤ (vtxIdx M F U).ncard + 2 * M.deg F U := by
  have hS := hostKeys_finite (U := U) hM hF hfin
  have e : nk M F U = (hostKeys M F U).ncard := by
    unfold nk
    rw [hostKeyList_eq hS, Finset.length_sort, Set.ncard_eq_toFinset_card _ hS]
  rw [e]
  refine (ncard_union_le _ _).trans ?_
  rw [vtxKeys_ncard]
  have := exitKeys_ncard_le hM hF hfin U
  omega

/-- The inner vertices of any set of regions: disjoint, so their total is the size of the union. -/
theorem sum_vtxIdx_eq {T : Set (Set Point)} (hT : T.Finite) (hTR : T ⊆ M.regions F) :
    ∑ᶠ U ∈ T, (vtxIdx M F U).ncard = (⋃ U ∈ T, vtxIdx M F U).ncard := by
  have hVfin : ∀ U, (vtxIdx M F U).Finite := fun U =>
    (Set.finite_lt_nat M.W.n).subset fun k hk => hk.1
  induction T, hT using Set.Finite.induction_on with
  | empty => simp
  | @insert U T hUT hT ih =>
    rw [finsum_mem_insert _ hUT hT, Set.biUnion_insert,
      ih (fun V hV => hTR (mem_insert_of_mem U hV))]
    rw [ncard_union_eq _ (hVfin U) (hT.biUnion fun V _ => hVfin V)]
    rw [Set.disjoint_iUnion₂_right]
    intro V hV
    exact vtxIdx_disjoint (hTR (mem_insert U T)) (hTR (mem_insert_of_mem U hV))
      (fun e => hUT (e ▸ hV))

/-- **The host polygons of all regions together have at most `n + 4|F|` points.** -/
theorem sum_nk_le (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    ∑ᶠ U ∈ M.regions F, nk M F U ≤ M.W.n + 4 * F.ncard := by
  have hsys := hM.sys F hF hfin
  have hRfin : (M.regions F).Finite := hsys.regionsIn_finite hM.preconn hM.nonempty subset_rfl
  -- the degrees
  have hdeg : ∑ᶠ U ∈ M.regions F, M.deg F U ≤ 2 * F.ncard := by
    have := Merge.potential_le hsys hM.preconn hM.nonempty subset_rfl 0
    unfold Merge.potential at this
    simp only [Nat.sub_zero] at this
    exact this
  -- the inner vertices
  have hvtx : ∑ᶠ U ∈ M.regions F, (vtxIdx M F U).ncard ≤ M.W.n := by
    rw [sum_vtxIdx_eq hRfin subset_rfl]
    calc (⋃ U ∈ M.regions F, vtxIdx M F U).ncard ≤ ((Finset.range M.W.n : Finset ℕ) : Set ℕ).ncard :=
          ncard_le_ncard (fun k hk => by
            obtain ⟨U, -, hk⟩ := mem_iUnion₂.1 hk
            simpa using hk.1) (Finset.finite_toSet _)
      _ = M.W.n := by rw [ncard_coe_finset, Finset.card_range]
  rw [finsum_mem_eq_finite_toFinset_sum _ hRfin] at hdeg hvtx ⊢
  calc ∑ U ∈ hRfin.toFinset, nk M F U
      ≤ ∑ U ∈ hRfin.toFinset, ((vtxIdx M F U).ncard + 2 * M.deg F U) :=
        Finset.sum_le_sum fun U _ => nk_le hM hF hfin U
    _ = ∑ U ∈ hRfin.toFinset, (vtxIdx M F U).ncard + 2 * ∑ U ∈ hRfin.toFinset, M.deg F U := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M.W.n + 4 * F.ncard := by omega

end

end DownDrv

end Chazelle.Core
