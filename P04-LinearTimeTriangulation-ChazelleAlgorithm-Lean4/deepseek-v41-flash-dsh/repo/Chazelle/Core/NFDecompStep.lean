module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompRound

/-!
# Tree decomposition (WP-C), part 5: the round invariant is preserved

Facts about one round (`next`), relative to a state satisfying `RInv` and the characterisation of
the top pass, and the preservation theorem `rinv_next`.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

set_option linter.unusedSectionVars false

section step

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable {σ : RS} {top best bestv : ℕ → ℕ}
variable (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u)
variable (hB : ∀ t, t < R → IsTop pch σ.rem t →
      (∀ c, c < R → AncX R prg pch σ.rem t c → c ≠ t → cval R prg pch σ.rem t c ≤ bestv t) ∧
      ((best t = t ∧ ∀ c, c < R → AncX R prg pch σ.rem t c → c = t) ∨
        (best t < R ∧ AncX R prg pch σ.rem t (best t) ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t (best t))))
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)

include h hch hT hB hI

theorem top_of {u t : ℕ} (hu : u < R) (htop : IsTop pch σ.rem t)
    (hanc : AncX R prg pch σ.rem t u) : top u = t := by
  obtain ⟨-, h1, h2⟩ := hT u hu
  exact top_unique h h1 htop h2 hanc

theorem top_self {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) : top t = t :=
  top_of h hch hT hB hI ht htop ReflTransGen.refl

theorem top_iff {u : ℕ} (hu : u < R) : top u = u ↔ IsTop pch σ.rem u := by
  constructor
  · intro e
    have := (hT u hu).2.1
    rwa [e] at this
  · exact top_self h hch hT hB hI hu

theorem chOf_pch {s : ℕ} (hs : s < R) (h0 : s ≠ 0) : chOf (pch s) = s := by
  obtain ⟨h1, h2, h3⟩ := hch (pch s) (h.pch_lt s hs h0)
  exact h.pch_inj h1 hs h2 h0 h3

/-- The facts behind a chosen chord. -/
theorem chosen_facts {e : ℕ} (he : e < K) (hc : Chosen σ top best chOf e) :
    top (chOf e) < R ∧ IsTop pch σ.rem (top (chOf e)) ∧ σ.act (top (chOf e)) = 1 ∧
      best (top (chOf e)) = chOf e ∧ chOf e ≠ top (chOf e) ∧ ¬ IsTop pch σ.rem (chOf e) ∧
      AncX R prg pch σ.rem (top (chOf e)) (chOf e) ∧ chOf e < R ∧ chOf e ≠ 0 ∧
      pch (chOf e) = e ∧ σ.pend e ≠ 1 := by
  obtain ⟨hr, ha, hb⟩ := hc
  obtain ⟨c1, c2, c3⟩ := hch e he
  obtain ⟨t1, t2, t3⟩ := hT (chOf e) c1
  have hnt : ¬ IsTop pch σ.rem (chOf e) := by
    rintro (h0 | h1)
    · exact c2 h0
    · rw [c3] at h1; exact hr h1
  refine ⟨t1, t2, ha, hb, fun e' => hnt (e' ▸ t2), hnt, t3, c1, c2, c3, fun hp => hr (hI.i0 e he hp)⟩

/-- The chord cut in an active component that is not a singleton. -/
theorem cut_chosen {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    best t < R ∧ AncX R prg pch σ.rem t (best t) ∧ best t ≠ 0 ∧ pch (best t) < K ∧
      chOf (pch (best t)) = best t ∧ top (best t) = t ∧ Chosen σ top best chOf (pch (best t)) ∧
      σ.rem (pch (best t)) ≠ 1 := by
  obtain ⟨-, hB2⟩ := hB t ht htop
  rcases hB2 with ⟨e, -⟩ | ⟨b1, b2, b3, -⟩
  · exact absurd e hbt
  have hnt : ¬ IsTop pch σ.rem (best t) := AncX.not_top b2 (Ne.symm b3)
  simp only [IsTop, not_or] at hnt
  have hch' := chOf_pch h hch hT hB hI b1 hnt.1
  have htop' := top_of h hch hT hB hI b1 htop b2
  refine ⟨b1, b2, hnt.1, h.pch_lt _ b1 hnt.1, hch', htop', ⟨hnt.2, ?_, ?_⟩, hnt.2⟩
  · rw [hch', htop']; exact hact
  · Ξ hch', htop'

/-- A chosen chord is the parent chord of the best candidate of its component. -/
theorem chosen_unique {w : ℕ} (hw : w < R) (hw0 : w ≠ 0) (hc : Chosen σ top best chOf (pch w)) :
    best (top w) = w ∧ σ.act (top w) = 1 := by
  have hch' := chOf_pch h hch hT hB hI hw hw0
  obtain ⟨-, ha, hb⟩ := hc
  rw [hch'] at ha hb
  exact ⟨hb, ha⟩

theorem rem_next {e : ℕ} (he : e < K) :
    (next R K prg pch isdn chOf top best σ).rem e = 1 ↔
      σ.rem e = 1 ∨ Chosen σ top best chOf e := by
  ϴ next, ite_eq_left he
  by_cases hp : σ.pend e = 1
  · Ξ ite_eq_left hp
    have := hI.i0 e he hp
    exact ⟨fun h1 => Or.inl h1, fun _ => this⟩
  · Ξ ite_eq_right hp
    by_cases hc : Chosen σ top best chOf e
    · rw [ite_eq_left hc]; exact ⟨fun _ => Or.inr hc, fun _ => rfl⟩
    · rw [ite_eq_right hc]; exact ⟨fun h1 => Or.inl h1, fun h1 => h1.resolve_right hc⟩

theorem rem_mono {e : ℕ} (hr : σ.rem e = 1) : (next R K prg pch isdn chOf top best σ).rem e = 1 := by
  by_cases he : e < K
  · exact (rem_next h hch hT hB hI he).2 (Or.inl hr)
  · simp only [next, ite_eq_right he]; exact hr

theorem pend_next {e : ℕ} (he : e < K) :
    nPend K chOf top best σ e = 1 ↔ Chosen σ top best chOf e := by
  ϴ nPend, ite_eq_left he
  by_cases hp : σ.pend e = 1
  · Ξ ite_eq_left hp
    have := hI.i0 e he hp
    exact ⟨fun h1 => absurd h1 (⊛), fun h1 => absurd this h1.1⟩
  · Ξ ite_eq_right hp
    by_cases hc : Chosen σ top best chOf e
    · rw [ite_eq_left hc]; exact ⟨fun _ => hc, fun _ => rfl⟩
    · rw [ite_eq_right hc]; exact ⟨fun h1 => absurd h1 hp, fun h1 => absurd h1 hc⟩

theorem istop_next {u : ℕ} (hu : u < R) :
    IsTop pch (next R K prg pch isdn chOf top best σ).rem u ↔
      IsTop pch σ.rem u ∨ (u ≠ 0 ∧ Chosen σ top best chOf (pch u)) := by
  by_cases h0 : u = 0
  · subst h0; exact ⟨fun _ => Or.inl (Or.inl rfl), fun _ => Or.inl rfl⟩
  · have hpk := h.pch_lt u hu h0
    ϴ IsTop, h0, false_or, rem_next h hch hT hB hI hpk, ne_eq, not_false_eq_true, true_and

/-- The ancestor relation after the round: the old one, avoiding the chosen chords. -/
theorem ancX_next {a v : ℕ} (hv : v < R) :
    AncX R prg pch (next R K prg pch isdn chOf top best σ).rem a v ↔
      AncX R prg pch σ.rem a v ∧ ∀ w, AncX R prg pch σ.rem a w → AncX R prg pch σ.rem w v →
        w ≠ a → ¬ Chosen σ top best chOf (pch w) := by
  constructor
  · intro hav
    refine ⟨hav.mono (fun e he => rem_mono h hch hT hB hI he), fun w haw hwv hwa hc => ?_⟩
    have hw := (AncX.pos_le h hwv hv).1
    have haw' := hav.upper h hwv.to0 haw.to0 hv
    rcases (AncX.back_iff h).1 haw' with e | ⟨-, hw0, hr, -⟩
    · exact hwa e.symm
    · exact hr ((rem_next h hch hT hB hI (h.pch_lt w hw hw0)).2 (Or.inr hc))
  · rintro ⟨hav, hkeep⟩
    refine hav.of_keep h fun w haw hwv hwa => ?_
    have hw := (AncX.pos_le h hwv hv).1
    rcases (AncX.back_iff h).1 haw with e | ⟨-, hw0, hr, -⟩
    · exact absurd e.symm hwa
    · intro h1
      rcases (rem_next h hch hT hB hI (h.pch_lt w hw hw0)).1 h1 with h2 | h2
      · exact hr h2
      · exact hkeep w haw hwv hwa h2

/-- Within a component that is not cut, no chord is chosen. -/
theorem no_chosen_in {t w : ℕ} (_ht : t < R) (htop : IsTop pch σ.rem t)
    (hncut : σ.act t = 1 → best t = t) (hw : w < R) (htw : AncX R prg pch σ.rem t w) (hwt : w ≠ t) :
    ¬ Chosen σ top best chOf (pch w) := by
  intro hc
  have hw0 : w ≠ 0 := fun e => AncX.not_top htw (Ne.symm hwt) (Or.inl e)
  obtain ⟨hb, ha⟩ := chosen_unique h hch hT hB hI hw hw0 hc
  rw [top_of h hch hT hB hI hw htop htw] at hb ha
  exact hwt (hb.symm.trans (hncut ha))

/-- In a cut component, the only chosen chord is the parent chord of the best candidate. -/
theorem chosen_in_cut {t w : ℕ} (_ht : t < R) (htop : IsTop pch σ.rem t) (hw : w < R)
    (htw : AncX R prg pch σ.rem t w) (hwt : w ≠ t) (hc : Chosen σ top best chOf (pch w)) :
    w = best t := by
  have hw0 : w ≠ 0 := fun e => AncX.not_top htw (Ne.symm hwt) (Or.inl e)
  obtain ⟨hb, -⟩ := chosen_unique h hch hT hB hI hw hw0 hc
  rw [top_of h hch hT hB hI hw htop htw] at hb
  exact hb.symm

theorem sub_uncut {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t)
    (hncut : σ.act t = 1 → best t = t) :
    sub R prg pch (next R K prg pch isdn chOf top best σ).rem t = sub R prg pch σ.rem t := by
  ext v
  Ξ mem_sub, mem_sub
  constructor
  · rintro ⟨hv, hav⟩
    exact ⟨hv, ((ancX_next h hch hT hB hI hv).1 hav).1⟩
  · rintro ⟨hv, hav⟩
    refine ⟨hv, (ancX_next h hch hT hB hI hv).2 ⟨hav, fun w htw hwv hwt => ?_⟩⟩
    exact no_chosen_in h hch hT hB hI ht htop hncut (AncX.pos_le h hwv hv).1 htw hwt

open Classical in
/-- The part of a component below a member `c`. -/
theorem sub_member {t c : ℕ} (htc : AncX R prg pch σ.rem t c) :
    sub R prg pch σ.rem c = (sub R prg pch σ.rem t).filter (fun v => AncX R prg pch rem0 c v) := by
  ext v
  Ξ mem_filter, mem_sub, mem_sub
  constructor
  · rintro ⟨hv, hcv⟩
    exact ⟨⟨hv, (anc_member h htc hv).1 hcv |>.1⟩, ((anc_member h htc hv).1 hcv).2⟩
  · rintro ⟨⟨hv, htv⟩, hcv⟩
    exact ⟨hv, (anc_member h htc hv).2 ⟨htv, hcv⟩⟩

theorem sub_cut_c {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    sub R prg pch (next R K prg pch isdn chOf top best σ).rem (best t) = sub R prg pch σ.rem (best t) := by
  obtain ⟨b1, b2, -, -, -, -, -, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
  ext v
  Ξ mem_sub, mem_sub
  constructor
  · rintro ⟨hv, hav⟩
    exact ⟨hv, ((ancX_next h hch hT hB hI hv).1 hav).1⟩
  · rintro ⟨hv, hav⟩
    refine ⟨hv, (ancX_next h hch hT hB hI hv).2 ⟨hav, fun w hcw hwv hwc hc => ?_⟩⟩
    have hw := (AncX.pos_le h hwv hv).1
    have htw := b2.trans hcw
    have hwt : w ≠ t := by
      intro e
      rw [e] at hcw
      exact hbt (AncX.antisymm h hcw b2 ht)
    exact hwc (chosen_in_cut h hch hT hB hI ht htop hw htw hwt hc)

open Classical in
theorem sub_cut_t {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    sub R prg pch (next R K prg pch isdn chOf top best σ).rem t =
      (sub R prg pch σ.rem t).filter (fun v => ¬ AncX R prg pch rem0 (best t) v) := by
  obtain ⟨b1, b2, -, -, -, -, hcho, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
  ext v
  Ξ mem_filter, mem_sub, mem_sub
  constructor
  · rintro ⟨hv, hav⟩
    obtain ⟨htv, hkeep⟩ := (ancX_next h hch hT hB hI hv).1 hav
    refine ⟨⟨hv, htv⟩, fun hcv => ?_⟩
    have hcv' : AncX R prg pch σ.rem (best t) v := (anc_member h b2 hv).2 ⟨htv, hcv⟩
    exact hkeep (best t) b2 hcv' hbt hcho
  · rintro ⟨⟨hv, htv⟩, hncv⟩
    refine ⟨hv, (ancX_next h hch hT hB hI hv).2 ⟨htv, fun w htw hwv hwt hc => ?_⟩⟩
    have hw := (AncX.pos_le h hwv hv).1
    have := chosen_in_cut h hch hT hB hI ht htop hw htw hwt hc
    rw [this] at hwv
    exact hncv hwv.to0

open Classical in
theorem sz_cut {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1)
    (hbt : best t ≠ t) :
    sz R prg pch (next R K prg pch isdn chOf top best σ).rem (best t) = sz R prg pch σ.rem (best t) ∧
    sz R prg pch (next R K prg pch isdn chOf top best σ).rem t + sz R prg pch σ.rem (best t) =
      sz R prg pch σ.rem t := by
  obtain ⟨b1, b2, -, -, -, -, -, -⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
  refine ⟨by unfold sz; rw [sub_cut_c h hch hT hB hI ht htop hact hbt], ?_⟩
  unfold sz
  Ξ sub_cut_t h hch hT hB hI ht htop hact hbt, sub_member h hch hT hB hI b2
  Ξ Nat.add_comm
  exact Finset.card_filter_add_card_filter_not (fun v => AncX R prg pch rem0 (best t) v)

end step

end

end Chazelle.Core.Dec
