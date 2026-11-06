module

public import Chazelle.Core.RestoreMath

/-!
# WP-E, part 2: the link lemma — a chord with two exits on each side splits well

Let `R` be a region of a finite admissible family `S` of a walk-axiom model, and `e ∉ S` an
admissible chord whose open part lies in `R`, attached to the walk at two positions `A`, `B` with
distinct points (keys `ka`, `kb`).  The exit chords of `R` attached at some key strictly between
`ka` and `kb` (`sideExits M S R ka kb`) all touch the same one of the two halves of `R` cut by
`e`, and those attached strictly between `kb` and `ka` touch the other one (the side-aware
Lemma 2.1, `WalkAx.split`).  Hence (`splitsWell_of_sideExits`): **if at least two exit chords of
`R` are attached on each side of `e`, then `e` splits `R` well** (`Restore.SplitsWell`).

This is the form used by the restoration driver: the arcs `Aᵢ`, `Aⱼ` joined by the chord found by
Lemma 3.2 need not be nonconsecutive (two chords of `S` can be attached at one walk vertex, the
tie of `Chazelle.Core.FactsTie`); what matters is the number of exit chords of `R` attached on
each side, which the driver counts from the normal form.

* `exists_near_attach`: an attached admissible chord has points in the domain arbitrarily close
  to the attachment, inside the left sector;
* `subset_component_of_touches`: a connected subset of `D \ e` touched by a chord `c ≠ e` of the
  family lies in the component of `D \ e` containing the open part of `c`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Metric
open Chazelle.Chain (ChordSystem regionsIn TouchesIn SideAttach SideSectorIn sideInArc sidePt
  sideLeft freeIn regionsIn_subset regionsIn_isPreconnected regionsIn_nonempty)
open Chazelle.Merge (exitsIn IsSplit)
open Chazelle.Geometry (lerp)

variable {M : Model}

/-- The exit chords of `R` attached (somewhere) at a key strictly between `k₁` and `k₂`. -/
def sideExits (M : Model) (S : Set (Set Point)) (R : Set Point) (k₁ k₂ : ℝ) : Set (Set Point) :=
  {c | c ∈ exitsIn M.D S R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ sideInArc k₁ k₂ (p + t)}

theorem sideExits_subset (S : Set (Set Point)) (R : Set Point) (k₁ k₂ : ℝ) :
    sideExits M S R k₁ k₂ ⊆ exitsIn M.D S R := fun _ h => h.1

/-- Points of a segment close to its start. -/
theorem exists_lerp_near {a b : Point} (hab : a ≠ b) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ lerp a b s ≠ a ∧ dist (lerp a b s) a < ρ := by
  have hd : 0 < dist b a := dist_pos.2 hab.symm
  set s := min (1 / 2) (ρ / (2 * dist b a))
  have hs0 : 0 < s := lt_min (by norm_num) (div_pos hρ (by positivity))
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hdist : dist (lerp a b s) a = s * dist b a := by
    rw [Geometry.lerp_eq_add_smul, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs0, dist_eq_norm]
  refine ⟨s, hs0, hs1, ?_, ?_⟩
  · intro h
    have h' : dist (lerp a b s) a = 0 := by rw [h, dist_self]
    rw [hdist] at h'
    exact (mul_pos hs0 hd).ne' h'
  · rw [hdist]
    have : s ≤ ρ / (2 * dist b a) := min_le_right _ _
    calc s * dist b a ≤ ρ / (2 * dist b a) * dist b a :=
          mul_le_mul_of_nonneg_right this hd.le
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith

/-- **An attached admissible chord enters the left sector**: for every set `K` containing the
small left sector at the attachment, the chord has a point in the domain lying in `K`. -/
theorem exists_near_attach (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {K : Set Point} (hK : SideSectorIn M.W K p t) :
    ∃ x ∈ c ∩ M.D, x ∈ K := by
  obtain ⟨a, b, hab, rfl, -, hopen, -, -⟩ := hM.ends c hc
  have hA' := hA
  obtain ⟨hp, ht, ht1, hmem, r, hr, hsec⟩ := hA
  obtain ⟨r', hr', hK⟩ := hK
  have hend := hM.attach_endpoint hopen hA'
  -- a point of the open part near the attachment point
  have key : ∀ u v : Point, u ≠ v → (∀ s ∈ Ioo (0 : ℝ) 1, lerp u v s ∈ M.D) →
      Chazelle.segment u v = Chazelle.segment a b → sidePt M.W p t = u →
      ∃ x ∈ Chazelle.segment a b ∩ M.D, x ∈ K := by
    intro u v huv hop hseg hpt
    obtain ⟨s, hs0, hs1, hne, hd⟩ := exists_lerp_near huv (lt_min hr hr')
    have hxs : lerp u v s ∈ Chazelle.segment a b := by
      rw [← hseg]; exact Geometry.lerp_mem_segment _ _ hs0.le hs1.le
    have hxD : lerp u v s ∈ M.D := hop s ⟨hs0, hs1⟩
    refine ⟨_, ⟨hxs, hxD⟩, hK _ ?_ ?_⟩
    · rw [mem_ball, hpt]; exact lt_of_lt_of_le hd (min_le_right _ _)
    · apply hsec _ hxs (by rwa [hpt])
      rw [hpt]; exact lt_of_lt_of_le hd (min_le_left _ _)
  rcases hend with h | h
  · exact key a b hab hopen rfl h
  · exact key b a hab.symm (WalkAx.open_rev hopen) (Geometry.segment_comm _ _) h

/-- **A touched connected set lies on the side of the chord.**  If `c ≠ e` are chords of a chord
system, `x` is a point of `c` in the domain lying in the component `K` of `D \ e`, and the
preconnected set `U ⊆ D \ e` is touched by `c`, then `U ⊆ K`. -/
theorem subset_component_of_touches (hD : IsOpen M.D) {F : Set (Set Point)}
    (hF : ChordSystem M.D F) {c e : Set Point} (hc : c ∈ F) (he : e ∈ F) (hce : c ≠ e)
    {x c₀ : Point} (hx : x ∈ c ∩ M.D) (hxK : x ∈ connectedComponentIn (M.D \ e) c₀)
    {U : Set Point} (hU : U ⊆ M.D \ e) (hUc : IsPreconnected U) (ht : TouchesIn M.D c U) :
    U ⊆ connectedComponentIn (M.D \ e) c₀ := by
  have hK := connectedComponentIn_eq hxK
  have hcD : c ∩ M.D ⊆ M.D \ e := fun z hz =>
    ⟨hz.2, fun hze => hF.inter_subset_compl hc he hce ⟨hz.1, hze⟩ hz.2⟩
  have hcK : c ∩ M.D ⊆ connectedComponentIn (M.D \ e) c₀ := by
    rw [hK]
    exact (hF.chord_inter_nonempty_isPreconnected hc).2.subset_connectedComponentIn hx hcD
  have hopen : IsOpen (connectedComponentIn (M.D \ e) c₀) :=
    (hD.sdiff (hF.isClosed_chord he)).connectedComponentIn
  obtain ⟨z, hz, hzU⟩ := ht
  obtain ⟨u, huK, huU⟩ := mem_closure_iff.1 hzU _ hopen (hcK hz)
  rw [connectedComponentIn_eq huK]
  exact hUc.subset_connectedComponentIn huU hU

/-- Two distinct components of one set are disjoint. -/
theorem components_disjoint {A : Set Point} {c₁ c₂ : Point}
    (hne : connectedComponentIn A c₁ ≠ connectedComponentIn A c₂) :
    Disjoint (connectedComponentIn A c₁) (connectedComponentIn A c₂) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  exact hne ((connectedComponentIn_eq h1).trans (connectedComponentIn_eq h2).symm)

theorem pair_cases {X u v a b : Set Point} (hx : X = u ∨ X = v) (ha : a = u ∨ a = v)
    (hb : b = u ∨ b = v) (hab : a ≠ b) : X = a ∨ X = b := by
  rcases hx with rfl | rfl <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hab

/-- **The link lemma.**  Let `R` be a region of the finite admissible family `S`, and `e ∉ S` an
admissible chord with open part in `R`, attached at two positions with distinct points and keys
`ka`, `kb`.  If at least two exit chords of `R` are attached strictly between `ka` and `kb`, and
at least two strictly between `kb` and `ka`, then `e` splits `R` well. -/
theorem splitsWell_of_sideExits (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (h1 : 2 ≤ (sideExits M S R (pa + ta) (pb + tb)).ncard)
    (h2 : 2 ≤ (sideExits M S R (pb + tb) (pa + ta)).ncard) : SplitsWell M S R e := by
  refine ⟨heS, heR, ?_⟩
  set F := insert e S
  have hF : ChordSystem M.D F := hM.sys F (insert_subset he hS) (hfin.insert e)
  have hSF : S ⊆ F := subset_insert e S
  have heF : e ∈ F := mem_insert e S
  obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hF hSF heF heS hR heR
  obtain ⟨K₁, K₂, hK, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
  have hdisj := components_disjoint hK
  -- the halves are connected subsets of `D \ e`
  have hsub : ∀ Q ∈ regionsIn M.D F, Q ⊆ M.D \ e := fun Q hQ z hz =>
    ⟨(regionsIn_subset hQ hz).1, fun hze => (regionsIn_subset hQ hz).2 ⟨e, heF, hze⟩⟩
  have hfinS : ∀ Q : Set Point, (exitsIn M.D S Q).Finite := fun Q =>
    hfin.subset (Merge.exitsIn_subset S Q)
  -- an exit chord attached on a side touches a half, which lies in that side's component
  have side : ∀ (c₀ : Point) (k₁ k₂ : ℝ),
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc k₁ k₂ (p + t) →
        SideSectorIn M.W (connectedComponentIn (M.D \ e) c₀) p t) →
      ∀ c ∈ sideExits M S R k₁ k₂, (TouchesIn M.D c R₁ ∨ TouchesIn M.D c R₂) ∧
        ∀ Q ∈ regionsIn M.D F, TouchesIn M.D c Q → Q ⊆ connectedComponentIn (M.D \ e) c₀ := by
    intro c₀ k₁ k₂ hsec c hc
    obtain ⟨⟨hcS, hcR⟩, p, t, hat, hin⟩ := hc
    have hce : c ≠ e := fun h => heS (h ▸ hcS)
    refine ⟨?_, fun Q hQ hcQ => ?_⟩
    · have hmem : c ∈ exitsIn M.D S R := ⟨hcS, hcR⟩
      rw [hs.exits_eq_union hF hSF heF heS (subset_refl S)] at hmem
      rcases hmem with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    · obtain ⟨hp, ht0, ht1, -⟩ := id hat
      obtain ⟨x, hx, hxK⟩ := exists_near_attach hM (hS hcS) hat (hsec p hp t ht0 ht1 hin)
      exact subset_component_of_touches hM.isOpen hF (hSF hcS) heF hce hx hxK (hsub Q hQ)
        (regionsIn_isPreconnected hQ) hcQ
  have hs1 := side c₁ _ _ hsec₁
  have hs2 := side c₂ _ _ hsec₂
  -- pick one exit chord on each side
  have hne1 : (sideExits M S R (pa + ta) (pb + tb)).Nonempty :=
    nonempty_of_ncard_ne_zero (by omega)
  have hne2 : (sideExits M S R (pb + tb) (pa + ta)).Nonempty :=
    nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨d₁, hd₁⟩ := hne1
  obtain ⟨d₂, hd₂⟩ := hne2
  have hR12 : ∀ Q, Q = R₁ ∨ Q = R₂ → Q ∈ regionsIn M.D F := by
    rintro Q (rfl | rfl)
    · exact hs.mem₁
    · exact hs.mem₂
  -- the half touched by `d₁` lies in `K₁`, the one touched by `d₂` in `K₂`
  obtain ⟨Ra, hRa, hRaK⟩ : ∃ Ra, (Ra = R₁ ∨ Ra = R₂) ∧ TouchesIn M.D d₁ Ra := by
    rcases (hs1 d₁ hd₁).1 with h | h
    · exact ⟨R₁, Or.inl rfl, h⟩
    · exact ⟨R₂, Or.inr rfl, h⟩
  obtain ⟨Rb, hRb, hRbK⟩ : ∃ Rb, (Rb = R₁ ∨ Rb = R₂) ∧ TouchesIn M.D d₂ Rb := by
    rcases (hs2 d₂ hd₂).1 with h | h
    · exact ⟨R₁, Or.inl rfl, h⟩
    · exact ⟨R₂, Or.inr rfl, h⟩
  have hRa1 := (hs1 d₁ hd₁).2 Ra (hR12 Ra hRa) hRaK
  have hRb2 := (hs2 d₂ hd₂).2 Rb (hR12 Rb hRb) hRbK
  have notBoth : ∀ Q ∈ regionsIn M.D F, Q ⊆ connectedComponentIn (M.D \ e) c₁ →
      Q ⊆ connectedComponentIn (M.D \ e) c₂ → False := by
    intro Q hQ h₁ h₂
    obtain ⟨z, hz⟩ := regionsIn_nonempty hQ
    exact hdisj.notMem_of_mem_left (h₁ hz) (h₂ hz)
  have hab : Ra ≠ Rb := by
    rintro rfl
    exact notBoth Ra (hR12 Ra hRa) hRa1 hRb2
  intro P hP hPR
  have hP12 := hs.eq_of_subset hP hPR
  have gen : ∀ (c₀ c₀' : Point) (k₁ k₂ : ℝ) (Rx Ry : Set Point),
      (∀ c ∈ sideExits M S R k₁ k₂, (TouchesIn M.D c R₁ ∨ TouchesIn M.D c R₂) ∧
        ∀ Q ∈ regionsIn M.D F, TouchesIn M.D c Q → Q ⊆ connectedComponentIn (M.D \ e) c₀) →
      (Ry = R₁ ∨ Ry = R₂) → Ry ⊆ connectedComponentIn (M.D \ e) c₀' →
      Disjoint (connectedComponentIn (M.D \ e) c₀) (connectedComponentIn (M.D \ e) c₀') →
      (∀ Q, (Q = R₁ ∨ Q = R₂) → Q = Rx ∨ Q = Ry) →
      2 ≤ (sideExits M S R k₁ k₂).ncard → 2 ≤ (exitsIn M.D S Rx).ncard := by
    intro c₀ c₀' k₁ k₂ Rx Ry hside hRy hRyK hdis hcases hcount
    refine hcount.trans (ncard_le_ncard (fun c hc => ⟨(hside c hc).1.elim
      (fun _ => hc.1.1) (fun _ => hc.1.1), ?_⟩) (hfinS Rx))
    have hQ : ∀ Q, (Q = R₁ ∨ Q = R₂) → TouchesIn M.D c Q → Q = Rx := by
      intro Q hQ12 hcQ
      rcases hcases Q hQ12 with h | h
      · exact h
      · exfalso
        have hQK := (hside c hc).2 Q (hR12 Q hQ12) hcQ
        obtain ⟨z, hz⟩ := regionsIn_nonempty (hR12 Q hQ12)
        rw [h] at hz hQK
        exact hdis.notMem_of_mem_left (hQK hz) (hRyK hz)
    rcases (hside c hc).1 with h | h
    · rwa [← hQ R₁ (Or.inl rfl) h]
    · rwa [← hQ R₂ (Or.inr rfl) h]
  rcases pair_cases hP12 hRa hRb hab with rfl | rfl
  · exact gen c₁ c₂ _ _ P Rb hs1 hRb hRb2 hdisj
      (fun Q hQ => pair_cases hQ hRa hRb hab) h1
  · exact gen c₂ c₁ _ _ P Ra hs2 hRa hRa1 hdisj.symm
      (fun Q hQ => (pair_cases hQ hRa hRb hab).symm) h2

end

end Restore

end Chazelle.Core
