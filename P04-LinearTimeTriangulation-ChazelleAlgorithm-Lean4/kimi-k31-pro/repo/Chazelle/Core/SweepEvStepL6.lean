module

public import Chazelle.Core.SweepEvStepL5
public import Chazelle.Rwx

/-!
# The sweep (WP-D), stage 3: at most four labels at a key (Task L1)

* `stp_addLs_sub`, `stp_mem_stopLabs`, `stp_stopLabs_len`: label lists;
* `stp_two_chords`: at most two chords are attached at a position (`tie_third`);
* `SCtx.stop_unique`, `SCtx.triple_unique`: a chord at the next key determines its skipped stop,
  or the query of its accepted triples;
* `labsOf`, `SCtx.labsOf_card`: the labels a chord at the next key contributes (from its accepted
  triples, or from its skipped stop) are at most two.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The entries of an appended list come from the list or the appended labels. -/
theorem stp_addLs_sub : ∀ (vs l : List ℕ) {x : ℕ}, x ∈ addLs l vs → x ∈ l ∨ x ∈ vs := by
  intro vs
  induction vs using List.reverseRecOn with
  | nil => intro l x hx; exact Or.inl hx
  | append_singleton vs v ih =>
    intro l x hx
    rw [addLs_append'] at hx
    rcases mem_addL (l := addLs l vs) (v := v) hx with h | h
    · rcases ih l h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_append_left _ h')
    · exact Or.inr (List.mem_append_right _ (by rw [h]; exact List.mem_singleton_self _))

/-- **The labels of a stop record.** -/
theorem stp_mem_stopLabs {m : ℕ → ℕ} {A : ℕ} {ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hrec : AuxRecsAt m A ax) {i : ℕ} (hi : i < ax.length) {x : ℕ} :
    x ∈ stopLabs m A i ↔ ax[i].1 = 1 ∧
      ((0 < ax[i].2.1 ∧ x = ax[i].2.2.1) ∨ (1 < ax[i].2.1 ∧ x = ax[i].2.2.2.1)) := by
  obtain ⟨a0, a1, a2, a3, -⟩ := hrec i hi
  rw [List.getD_eq_getElem _ _ hi] at a0 a1 a2 a3
  unfold stopLabs
  rw [a0, a1]
  split_ifs with h
  · simp [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨h, ?_⟩
      have : t = 0 ∨ t = 1 := by omega
      rcases this with rfl | rfl
      · left; exact ⟨by omega, by rw [add_zero, a2]⟩
      · right; exact ⟨by omega, by rw [show A + 5 * i + 2 + 1 = A + 5 * i + 3 by ring, a3]⟩
    · rintro ⟨-, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩
      · exact ⟨0, by omega, by rw [add_zero, a2]⟩
      · exact ⟨1, by omega, by rw [show A + 5 * i + 2 + 1 = A + 5 * i + 3 by ring, a3]⟩
  · simp [List.not_mem_nil, false_iff, not_and]
    intro h'; exact absurd h' h

theorem stp_stopLabs_len (m : ℕ → ℕ) (A i : ℕ) : (stopLabs m A i).length ≤ 2 := by
  unfold stopLabs; split_ifs <;> simp

/-- **At most two chords are attached at a position.** -/
theorem stp_two_chords {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (p : ℕ) (t : ℝ) :
    ∃ e₁ e₂ : Set Point, ∀ e ∈ F, SideAttach M.W e p t → e = e₁ ∨ e = e₂ := by
  classical
  by_cases h : ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ SideAttach M.W a p t ∧ SideAttach M.W b p t
  · obtain ⟨a, ha, b, hb, hab, hAa, hAb⟩ := h
    exact ⟨a, b, fun e he hA => tie_third hM hF ha hb he hab hAa hAb hA⟩
  · push Not at h
    by_cases h' : ∃ a ∈ F, SideAttach M.W a p t
    · obtain ⟨a, ha, hAa⟩ := h'
      refine ⟨a, a, fun e he hA => Or.inl ?_⟩
      by_contra hne
      exact h e he a ha hne hA hAa
    · exact ⟨∅, ∅, fun e he hA => absurd ⟨e, he, hA⟩ h'⟩

/-- **The labels a chord at the next key contributes**: those of its accepted triples at the
offset of the next key, and those of its skipped stop. -/
def labsOf (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c co c' : Config)
    (A : Set (ℕ × ℕ × ℕ)) (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (e : Set Point) : Set ℕ :=
  {x | (∃ t ∈ A, offT P J t = keyOff P J c' ∧
      Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1) = e ∧
      (x = upOf N₂ t.1 ∨ x = dnOf N₂ t.1)) ∨
    (∃ i, ∃ hi : i < rs.length, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
      stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = e ∧
      x ∈ stopLabs co.nmem (co.nreg aB) i)}

namespace SCtx

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set (ℕ × ℕ × ℕ)} {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- **A chord at the next key is the chord of at most one skipped stop.** -/
theorem stop_unique {i i' : ℕ} (hi : i < rs.length) (hi' : i' < rs.length)
    (h1 : c.nreg sP ≤ i) (h2 : i < c'.nreg sP) (h1' : c.nreg sP ≤ i') (h2' : i' < c'.nreg sP)
    (heq : stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 =
      stopSet J (Qof P) N₂ rs[i'].2.2.1 rs[i'].2.2.2.1 rs[i'].2.2.2.2) : i = i' := by
  obtain ⟨hi₀, -, -, -, e1, e2⟩ := S.skip_at h1 h2
  obtain ⟨hi₀', -, -, -, e1', e2'⟩ := S.skip_at h1' h2'
  have hnd := S.hD.2.2.2.2.1.2.2.2
  have hl : (stopsOf J (Qof P) N₂ rs).length = rs.length := by simp [stopsOf]
  exact (List.Nodup.getElem_inj_iff hnd (hi := by rwx [hl])
    (hj := by rwx [hl])).1 (by
      rw [stopsOf_getElem hi, stopsOf_getElem hi', e2, e2', e1, e1', heq])

/-- **A chord determines the query of its accepted triples.** -/
theorem triple_unique {t t' : ℕ × ℕ × ℕ} (ht : t ∈ A) (ht' : t' ∈ A)
    (heq : Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1) =
      Merge.shoot J.whole (endOrigin J (Qof P) N₂ t'.1) (endDir t'.1)) : t.1 = t'.1 := by
  obtain ⟨-, hj, -, -, -, -, -, -, hlt⟩ := S.hBA.acc t ht
  obtain ⟨-, hj', -, -, -, -, -, -, hlt'⟩ := S.hBA.acc t' ht'
  obtain ⟨haR, hav, hat⟩ := S.hval t ht
  obtain ⟨haR', hav', hat'⟩ := S.hval t' ht'
  exact (originTask J (Qof P) N₂ S.E.hP S.E.hNF₂ (F₂plus_chordFamily S.E)).2 t.1 t'.1 hj hj'
    haR hav hat hlt haR' hav' hat' hlt' heq

/-- **A chord at the next key contributes at most two labels.** -/
theorem labsOf_card (e : Set Point) :
    (labsOf P J N₂ c co c' A rs e).Finite ∧ (labsOf P J N₂ c co c' A rs e).ncard ≤ 2 := by
  classical
  by_cases hst : StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e
  · by_cases hex : ∃ i, ∃ hi : i < rs.length, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
        stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = e
    · obtain ⟨i₀, hi₀, g1, g2, g3⟩ := hex
      have hsub : labsOf P J N₂ c co c' A rs e ⊆
          ((stopLabs co.nmem (co.nreg aB) i₀).toFinset : Set ℕ) := by
        rintro x (⟨t, ht, hto, hte, -⟩ | ⟨i, hi, f1, f2, f3, hx⟩)
        · exact absurd (hte ▸ hst) (S.triple_at ht hto).2.2.1
        · have := S.stop_unique hi hi₀ f1 f2 g1 g2 (f3.trans g3.symm)
          subst this
          simpa using hx
      refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
      calc (labsOf P J N₂ c co c' A rs e).ncard
          ≤ (((stopLabs co.nmem (co.nreg aB) i₀).toFinset : Set ℕ)).ncard :=
            ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (stopLabs co.nmem (co.nreg aB) i₀).toFinset.card := ncard_coe_finset _
        _ ≤ (stopLabs co.nmem (co.nreg aB) i₀).length := List.toFinset_card_le _
        _ ≤ 2 := stp_stopLabs_len _ _ _
    · have hemp : labsOf P J N₂ c co c' A rs e = ∅ := by
        ext x
        simp [mem_empty_iff_false, iff_false]
        rintro (⟨t, ht, hto, hte, -⟩ | ⟨i, hi, f1, f2, f3, -⟩)
        · exact (S.triple_at ht hto).2.2.1 (hte ▸ hst)
        · exact hex ⟨i, hi, f1, f2, f3⟩
      rw [hemp]; exact ⟨finite_empty, by simp⟩
  · by_cases hex : ∃ t ∈ A, offT P J t = keyOff P J c' ∧
        Merge.shoot J.whole (endOrigin J (Qof P) N₂ t.1) (endDir t.1) = e
    · obtain ⟨t₀, ht₀, g1, g2⟩ := hex
      have hsub : labsOf P J N₂ c co c' A rs e ⊆ {upOf N₂ t₀.1, dnOf N₂ t₀.1} := by
        rintro x (⟨t, ht, hto, hte, hx⟩ | ⟨i, hi, f1, f2, f3, -⟩)
        · have := S.triple_unique ht ht₀ (hte.trans g2.symm)
          rw [this] at hx
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · obtain ⟨hi₁, -, hs, -⟩ := S.skip_at f1 f2
          exact absurd (f3 ▸ hs) hst
      refine ⟨(toFinite _).subset hsub, (ncard_le_ncard hsub (toFinite _)).trans ?_⟩
      exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])
    · have hemp : labsOf P J N₂ c co c' A rs e = ∅ := by
        ext x
        simp [mem_empty_iff_false, iff_false]
        rintro (⟨t, ht, hto, hte, -⟩ | ⟨i, hi, f1, f2, f3, -⟩)
        · exact hex ⟨t, ht, hto, hte⟩
        · obtain ⟨hi₁, -, hs, -⟩ := S.skip_at f1 f2
          exact hst (f3 ▸ hs)
      rw [hemp]; exact ⟨finite_empty, by simp⟩

end SCtx

end

end SweepEv

end Chazelle.Core
