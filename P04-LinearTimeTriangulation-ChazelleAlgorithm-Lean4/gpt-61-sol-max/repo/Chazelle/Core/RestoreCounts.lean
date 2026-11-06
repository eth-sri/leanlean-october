module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreSearch

/-!
# WP-E, Lemma 3.2 part 4: a good split is seen by the count test

The search certifies a candidate chord `e` of region `R` by counting the exit chords of `R`
attached strictly on each side of `e` (`splitsWell_of_counts`).  For completeness it needs the
converse: a chord that splits `R` well passes the count test.

* `cyc_cases`: a key is one of two distinct keys or strictly inside one of the two cyclic
  intervals they bound.
* `exit_side`: an exit chord `c ≠ e` of `R` has an attachment strictly inside one side of `e`,
  and every region of `insert e S` it touches lies in that side's component of `D \ e`.
* `counts_of_splitsWell`: if `e` splits `R` well, at least two exit chords of `R` are attached
  strictly on each side of `e`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (ChordSystem SideAttach sideInArc sidePt SideSectorIn freeIn regionsIn
  TouchesIn regionsIn_subset regionsIn_isPreconnected regionsIn_nonempty sideKey_inj)
open Merge (exitsIn)

variable {M : Model}

/-- A key is one of two distinct keys or strictly inside one of the two cyclic intervals. -/
theorem cyc_cases {a b x : ℝ} (hab : a ≠ b) :
    x = a ∨ x = b ∨ sideInArc a b x ∨ sideInArc b a x := by
  core_grind

/-- Two attachment positions with distinct points have distinct keys. -/
theorem key_ne_of_attach {W : Polygon} {c c' : Set Point} {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach W c pa ta) (hB : SideAttach W c' pb tb)
    (hAB : sidePt W pa ta ≠ sidePt W pb tb) : (pa : ℝ) + ta ≠ pb + tb := by
  intro h
  obtain ⟨h1, h2⟩ := sideKey_inj hA.2.1 hA.2.2.1 hB.2.1 hB.2.2.1 h
  simp_all

section
variable (hM : WalkAx M)
include hM
/-- **An admissible chord other than `e` has an attachment off the two attachment keys of
`e`.** -/
theorem exists_attach_off {e c : Set Point} (he : e ∈ M.Adm) (hc : c ∈ M.Adm)
    (hce : c ≠ e) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W e pa ta)
    (hB : SideAttach M.W e pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧
      (sideInArc (pa + ta) (pb + tb) (p + t) ∨ sideInArc (pb + tb) (pa + ta) (p + t)) := by
  have hne := key_ne_of_attach hA hB hAB
  obtain ⟨a, b, hab, hcab, -, hopen, ⟨⟨p₁, t₁, hA₁, h₁⟩, -⟩, ⟨⟨p₂, t₂, hA₂, h₂⟩, -⟩⟩ :=
    hM.ends c hc
  obtain ⟨ea, eb, heab, heq, -, heopen, -, -⟩ := hM.ends e he
  -- the attachment points of `e` are its ends
  have hAe : sidePt M.W pa ta = ea ∨ sidePt M.W pa ta = eb := by
    rw [heq] at hA; exact hM.attach_endpoint heopen hA
  have hBe : sidePt M.W pb tb = ea ∨ sidePt M.W pb tb = eb := by
    rw [heq] at hB; exact hM.attach_endpoint heopen hB
  -- if both attachments of `c` sit at keys of `e`, then `c = e`
  have pos_of : ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      (p : ℝ) + t = pa + ta ∨ (p : ℝ) + t = pb + tb →
      sidePt M.W p t = sidePt M.W pa ta ∨ sidePt M.W p t = sidePt M.W pb tb := by
    intro p t hat hk
    rcases hk with hk | hk
    · obtain ⟨h1, h2⟩ := sideKey_inj hat.2.1 hat.2.2.1 hA.2.1 hA.2.2.1 hk
      grind
    · obtain ⟨h1, h2⟩ := sideKey_inj hat.2.1 hat.2.2.1 hB.2.1 hB.2.2.1 hk
      grind
  by_contra hno
  push Not at hno
  have off : ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      (p : ℝ) + t = pa + ta ∨ (p : ℝ) + t = pb + tb := by
    grind [Chazelle.Core.Restore.cyc_cases]
  have ha := pos_of p₁ t₁ hA₁ (off p₁ t₁ hA₁)
  have hb := pos_of p₂ t₂ hA₂ (off p₂ t₂ hA₂)
  rw [h₁] at ha
  rw [h₂] at hb
  apply hce
  rw [hcab, heq]
  -- `{a, b} = {ea, eb}`
  have hpts : (a = ea ∧ b = eb) ∨ (a = eb ∧ b = ea) := by
    grind
  rcases hpts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Geometry.segment_comm _ _

/-- **A good split is seen by the count test.**  If the admissible chord `e`, attached at two
positions with distinct points, splits the region `R` of `S` well, then at least two exit chords
of `R` are attached strictly inside each of the two key intervals cut by `e`. -/
theorem counts_of_splitsWell {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W e pa ta)
    (hB : SideAttach M.W e pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (hsw : SplitsWell M S R e) :
    2 ≤ (sideExits M S R (pa + ta) (pb + tb)).ncard ∧
      2 ≤ (sideExits M S R (pb + tb) (pa + ta)).ncard := by
  obtain ⟨heS, heR, hP⟩ := hsw
  set F := insert e S with hFdef
  have hF : ChordSystem M.D F := hM.sys F (insert_subset he hS) (hfin.insert e)
  have hSF : S ⊆ F := subset_insert e S
  have heF : e ∈ F := mem_insert e S
  obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hF hSF heF heS hR heR
  obtain ⟨K₁, K₂, hK, ⟨c₁, hK₁⟩, ⟨c₂, hK₂⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
  have hdisj : Disjoint K₁ K₂ := by
    rw [hK₁, hK₂]; rw [hK₁, hK₂] at hK; exact components_disjoint hK
  have hsub : ∀ Q ∈ regionsIn M.D F, Q ⊆ M.D \ e := fun Q hQ z hz =>
    ⟨(regionsIn_subset hQ hz).1, fun hze => (regionsIn_subset hQ hz).2 ⟨e, heF, hze⟩⟩
  -- every exit chord of a half lies on one side, with the half in that side's component
  have hside : ∀ Q ∈ regionsIn M.D F, ∀ c ∈ exitsIn M.D S Q,
      (Q ⊆ K₁ ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ sideInArc (pa + ta) (pb + tb) (p + t)) ∨
      (Q ⊆ K₂ ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ sideInArc (pb + tb) (pa + ta) (p + t)) := by
    intro Q hQ c ⟨hcS, hcQ⟩
    have hce : c ≠ e := fun h => heS (h ▸ hcS)
    obtain ⟨p, t, hat, hin⟩ := exists_attach_off hM he (hS hcS) hce hA hB hAB
    obtain ⟨hp, ht0, ht1, -⟩ := id hat
    rcases hin with hin | hin
    · left
      obtain ⟨x, hx, hxK⟩ := exists_near_attach hM (hS hcS) hat (hsec₁ p hp t ht0 ht1 hin)
      rw [hK₁] at hxK ⊢
      exact ⟨subset_component_of_touches hM.isOpen hF (hSF hcS) heF hce hx hxK (hsub Q hQ)
        (regionsIn_isPreconnected hQ) hcQ, p, t, hat, hin⟩
    · right
      obtain ⟨x, hx, hxK⟩ := exists_near_attach hM (hS hcS) hat (hsec₂ p hp t ht0 ht1 hin)
      rw [hK₂] at hxK ⊢
      exact ⟨subset_component_of_touches hM.isOpen hF (hSF hcS) heF hce hx hxK (hsub Q hQ)
        (regionsIn_isPreconnected hQ) hcQ, p, t, hat, hin⟩
  have hR₁R : R₁ ⊆ R := fun z hz => by
    have h : z ∈ R \ e := by rw [← hs.union]; exact Or.inl hz
    exact h.1
  have hR₂R : R₂ ⊆ R := fun z hz => by
    have h : z ∈ R \ e := by rw [← hs.union]; exact Or.inr hz
    exact h.1
  have hc₁ := hP R₁ hs.mem₁ hR₁R
  have hc₂ := hP R₂ hs.mem₂ hR₂R
  have hfinS : ∀ Q : Set Point, (exitsIn M.D S Q).Finite := fun Q =>
    hfin.subset (Merge.exitsIn_subset S Q)
  have hfinE : ∀ k₁ k₂ : ℝ, (sideExits M S R k₁ k₂).Finite := fun k₁ k₂ =>
    (hfinS R).subset (sideExits_subset S R k₁ k₂)
  -- a half lies in one component
  have hin : ∀ Q ∈ regionsIn M.D F, Q ⊆ R → 2 ≤ (exitsIn M.D S Q).ncard → Q ⊆ K₁ ∨ Q ⊆ K₂ := by
    intro Q hQ _ h2
    obtain ⟨c, hc⟩ := nonempty_of_ncard_ne_zero (s := exitsIn M.D S Q) (by omega)
    rcases hside Q hQ c hc with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  -- the exits of a half in `K₁` are on the first side, and so on
  have hcount : ∀ Q ∈ regionsIn M.D F, Q ⊆ R → 2 ≤ (exitsIn M.D S Q).ncard →
      (Q ⊆ K₁ → 2 ≤ (sideExits M S R (pa + ta) (pb + tb)).ncard) ∧
      (Q ⊆ K₂ → 2 ≤ (sideExits M S R (pb + tb) (pa + ta)).ncard) := by
    intro Q hQ hQR h2
    obtain ⟨z, hz⟩ := regionsIn_nonempty hQ
    have htouch : ∀ c, TouchesIn M.D c Q → TouchesIn M.D c R := by
      rintro c ⟨w, hw, hwc⟩
      exact ⟨w, hw, closure_mono hQR hwc⟩
    constructor
    · intro hQK
      refine h2.trans (ncard_le_ncard (fun c hc => ?_) (hfinE _ _))
      rcases hside Q hQ c hc with h | h
      · exact ⟨⟨hc.1, htouch c hc.2⟩, h.2⟩
      · exact absurd (h.1 hz) (hdisj.notMem_of_mem_left (hQK hz))
    · intro hQK
      refine h2.trans (ncard_le_ncard (fun c hc => ?_) (hfinE _ _))
      rcases hside Q hQ c hc with h | h
      · exact absurd (hQK hz) (hdisj.notMem_of_mem_left (h.1 hz))
      · exact ⟨⟨hc.1, htouch c hc.2⟩, h.2⟩
  -- the two halves are in different components
  have hdiff : ¬ ((R₁ ⊆ K₁ ∧ R₂ ⊆ K₁) ∨ (R₁ ⊆ K₂ ∧ R₂ ⊆ K₂)) := by
    obtain ⟨ea, eb, heab, heq, -, heopen, -, -⟩ := hM.ends e he
    set z := Geometry.lerp ea eb (1 / 2) with hz
    have hzD : z ∈ M.D := heopen _ ⟨by norm_num, by norm_num⟩
    have hze : z ∈ e := by
      rw [heq]; exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)
    have hRo : IsOpen R := hF.regionsIn_open hSF hR
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hRo z (heR ⟨hze, hzD⟩)
    have hsys : ({e} : Set (Set Point)) ⊆ F := singleton_subset_iff.2 heF
    obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in hsys (mem_singleton e) hze hzD
    set ε := min (ε₀ / 2) (ρ / 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    obtain ⟨hu, hd, hne⟩ := hsep ε hε0 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hfe : freeIn M.D {e} = M.D \ e := by
      ext w; simp [freeIn]
    rw [hfe] at hu hd hne
    have hmemR : ∀ w : Point, dist w z < ρ → w ∈ M.D \ e → w ∈ R₁ ∪ R₂ := by
      intro w hw hwe
      rw [hs.union]
      exact ⟨hball hw, hwe.2⟩
    have hdu : dist ((z.1, z.2 + ε) : Point) z < ρ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0]
      rw [max_eq_right hε0.le]
      linarith [min_le_right (ε₀ / 2) (ρ / 2)]
    have hdd : dist ((z.1, z.2 - ε) : Point) z < ρ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [sub_self, abs_zero, sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
      rw [max_eq_right hε0.le]
      linarith [min_le_right (ε₀ / 2) (ρ / 2)]
    have hU12 := hmemR _ hdu hu
    have hD12 := hmemR _ hdd hd
    have same : ∀ K : Set Point, (∃ c₀, K = connectedComponentIn (M.D \ e) c₀) →
        ((z.1, z.2 + ε) : Point) ∈ K → ((z.1, z.2 - ε) : Point) ∈ K → False := by
      rintro K ⟨c₀, rfl⟩ h1 h2
      exact hne ((connectedComponentIn_eq h1).symm.trans (connectedComponentIn_eq h2))
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hu' : ((z.1, z.2 + ε) : Point) ∈ K₁ := hU12.elim (fun h => h1 h) (fun h => h2 h)
      have hd' : ((z.1, z.2 - ε) : Point) ∈ K₁ := hD12.elim (fun h => h1 h) (fun h => h2 h)
      exact same K₁ ⟨c₁, hK₁⟩ hu' hd'
    · have hu' : ((z.1, z.2 + ε) : Point) ∈ K₂ := hU12.elim (fun h => h1 h) (fun h => h2 h)
      have hd' : ((z.1, z.2 - ε) : Point) ∈ K₂ := hD12.elim (fun h => h1 h) (fun h => h2 h)
      exact same K₂ ⟨c₂, hK₂⟩ hu' hd'
  have i1 := hin R₁ hs.mem₁ hR₁R hc₁
  have i2 := hin R₂ hs.mem₂ hR₂R hc₂
  have k1 := hcount R₁ hs.mem₁ hR₁R hc₁
  have k2 := hcount R₂ hs.mem₂ hR₂R hc₂
  rcases i1 with h1 | h1 <;> rcases i2 with h2 | h2
  · exact absurd (Or.inl ⟨h1, h2⟩) hdiff
  · exact ⟨k1.1 h1, k2.2 h2⟩
  · exact ⟨k2.1 h2, k1.2 h1⟩
  · exact absurd (Or.inr ⟨h1, h2⟩) hdiff


end

end

end Restore

end Chazelle.Core
