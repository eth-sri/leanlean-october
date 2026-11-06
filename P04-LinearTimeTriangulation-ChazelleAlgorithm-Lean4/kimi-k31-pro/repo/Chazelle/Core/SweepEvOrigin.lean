module

public import Chazelle.Core.SweepEvTasks2
public import Chazelle.Core.SweepEvLabM
public import Chazelle.Core.SweepMachine14
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# The sweep (WP-D), stage 3: the chord seen from a valid origin (Task O, mathematics)

For an endpoint query of `N₂` whose origin `a` is a point of `C₂` other than the shared vertex and
the top of `C₂`, and whose first hit in `C` comes strictly before its first hit in `C₂`, the hit
point `w` lies strictly inside the chord of `S₂` along which the query shoots, hence in the domain
of `C₂`.  This single fact gives everything:

* `start_key_pt`: the point of the start key (offset `Lst`) is the shared vertex;
* `Lst_lt_of_dom`: a position of the walk of `C` whose point is in the domain of `C₂` is strictly
  beyond the start (offset `> Lst`);
* `origin_hit`: the direction is free for `C`, the hit parameter is positive, and `w` is off the
  domain of `C` and in the domain of `C₂`;
* `origin_not_stop`: the chord `shoot J.whole a σ` is not a stop chord (the origin of a stop chord
  is off the domain of `C`, so it would be `a` or `w`);
* `origin_attach`: its attachment at `w`, beyond the start, not at the shared vertex;
* `origin_inj`: the chord determines the origin, the direction and the chord of `S₂`;
* **`originTask : OriginTask`**.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Origin

variable {J : Merge.Junction}

/-- **The point of the start key** (offset `Lst`) is the shared vertex. -/
theorem start_key_pt (hP : J.P.Simple) :
    sidePt (chainModel J.whole).W ((gW J + Lst J) % (chainModel J.whole).W.n) 0 = J.shared := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hτ' := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  by_cases hlt : Lst J < lOff J
  · obtain ⟨hv, -, hτ, hL⟩ := caseB_facts J hlt
    have e : (gW J + Lst J) % (chainModel J.whole).W.n = 2 * J.whole.m + 6 := by
      unfold gW
      rw [hL, hn, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e, (sidePt_top_copies J.whole).2, shared_eq_top J hv]
  · have hlo : lOff J = Lst J := by
      by_cases hv : VNotTop J
      · rw [lOff_of_vnt J hv, Lst_rlen]
      · exact (caseC_facts J hv hlt).2.1
    have := start_pt J hP
    rw [add_zero, Nat.mod_eq_of_lt (by omega), ← gL_eq J, hlo] at this
    exact this

/-- **A position whose point is in the domain of `C₂` is strictly beyond the start.** -/
theorem Lst_lt_of_dom (hP : J.P.Simple) {p : ℕ} {t : ℝ} (hp : p < (chainModel J.whole).W.n)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hD : sidePt (chainModel J.whole).W p t ∈ J.right.dom) :
    (Lst J : ℝ) < oW J (p + t) := by
  have hn  := cm_n J.whole
  have hτw := tpos_lt J.whole J.m₁
  have hg : gW J < (chainModel J.whole).W.n := by ufo gW
  have hvD : J.shared ∉ J.right.dom := fun h =>
    J.right.not_mem_set_of_mem_dom h J.shared_mem_right
  set D := dOf (chainModel J.whole).W.n (gW J) p with hDdef
  have hoW : oW J ((p : ℝ) + t) = (D : ℝ) + t := by rw [oW_def, off_key' hg hp ht0 ht1]
  rw [hoW]
  by_contra hle
  push Not at hle
  rcases (show (0 : ℝ) ≤ (D : ℝ) + t by positivity).lt_or_eq with h0 | h0
  · rcases hle.lt_or_eq with hL | hL
    · -- in the open right stretch: not in the domain of `C₂`
      have e : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((p : ℝ) + t) =
          (D : ℝ) + t := hoW
      exact stretch_not_dom₂ J hP (S₂ := ∅) (empty_subset _) finite_empty hp ht0 ht1
        ⟨by rwx [e], by rwx [e]⟩ hD
    · -- at the start key: the shared vertex
      have hDL : D = Lst J := by
        have h1 : (D : ℝ) ≤ Lst J := by linarith
        have h2 : (Lst J : ℝ) < D + 1 := by linarith
        have h1' : D ≤ Lst J := by exact_mod_cast h1
        have h2' : Lst J < D + 1 := by exact_mod_cast h2
        omega
      have ht : t = 0 := by rwli [hDL] at hL
      have hpD : p = (gW J + Lst J) % (chainModel J.whole).W.n := by
        rw [← hDL, hDdef, add_dOf hg hp]
      rw [hpD, ht, start_key_pt hP] at hD
      exact hvD hD
  · -- at the base: the shared vertex
    have := sidePt_off_zero J hP (S₂ := ∅) (empty_subset _) finite_empty hp ht0 ht1
      (show off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((p : ℝ) + t) = 0
        from hoW.trans h0.symm)
    rw [this] at hD
    exact hvD hD

/-- **The first hit from a valid origin**: the direction is free for `C`, the hit parameter is
positive, the hit point is off the domain of `C` and in the domain of `C₂`, and the points before
it are in the domain of `C`. -/
theorem origin_hit (hP : J.P.Simple) {c : Set Point} (hc : c ∈ Merge.augChords J.right)
    {a : Point} {σ : ℝ} (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) :
    (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole a σ ∧ 0 < J.whole.hitParam a σ ∧
      rayPt a σ (J.whole.hitParam a σ) ∉ J.whole.dom ∧
      (∀ s, 0 < s → s < J.whole.hitParam a σ → rayPt a σ s ∈ J.whole.dom) ∧
      rayPt a σ (J.whole.hitParam a σ) ∈ J.right.dom := by
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨hfr, ha₂, -, -, -, -⟩ := right_hit_end hc ha
  have hfree := whole_free_end hP haR hav hfr
  obtain ⟨hτ, hwD, hint⟩ := Merge.hit_of_freeAt J.whole (le_trans ha₂ J.right_top_le) hσ hfree
  obtain ⟨-, -, hint₂⟩ := Merge.hit_of_freeAt J.right ha₂ hσ hfr
  exact ⟨hσ, hfree, hτ, hwD, hint, hint₂ _ hτ hlt⟩

/-- A point of the chord from a valid origin, off the domain of `C` and other than the origin, is
the hit point. -/
theorem origin_end (hP : J.P.Simple) {c : Set Point} (hc : c ∈ Merge.augChords J.right)
    {a : Point} {σ : ℝ} (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) {b : Point}
    (hb : b ∈ Merge.shoot J.whole a σ) (hbD : b ∉ J.whole.dom) (hba : b ≠ a) :
    b = rayPt a σ (J.whole.hitParam a σ) := by
  obtain ⟨-, -, hτ, -, hint, -⟩ := origin_hit hP hc ha haR hav hlt
  unfold Merge.shoot at hb
  refine seg_end hb hbD (fun s hs => ?_) hba
  rw [lerp_rayPt]
  exact hint _ (mul_pos hs.1 hτ) (by nlinarith [hs.2])

/-- **The chord from a valid origin is not a stop chord.** -/
theorem origin_not_stop (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ Merge.augChords J.right)
    {a : Point} {σ : ℝ} (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hat : a ≠ J.right.top)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) :
    ¬ StopChord2 J S₂ (Merge.shoot J.whole a σ) := by
  obtain ⟨-, -, -, -, -, hwR⟩ := origin_hit hP hc ha haR hav hlt
  have key : ∀ b, b ∈ Merge.shoot J.whole a σ → b ∉ J.whole.dom → b ≠ a → b ∈ J.right.dom :=
    fun b hb hbD hba => by rwx [origin_end hP hc ha haR hav hlt hb hbD hba]
  have hset : ∀ b, b ∈ J.right.set → b ∉ J.whole.dom := fun b hb hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset hb)
  rintro ((⟨σ', -, -, he⟩ | ⟨c', hc', b, σ', hb, hbR, -, he⟩) | ⟨σ', -, -, he⟩)
  · have hm : J.shared ∈ Merge.shoot J.whole a σ := by rw [he]; exact origin_mem J
    exact J.right.not_mem_set_of_mem_dom
      (key _ hm (hset _ J.shared_mem_right) (Ne.symm hav)) J.shared_mem_right
  · have hm : b ∈ Merge.shoot J.whole a σ := by rw [he]; exact origin_mem J
    have hbD : b ∉ J.whole.dom := by
      rcases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (end_not_mem_dom J hS₂ hc').1
      · exact (end_not_mem_dom J hS₂ hc').2
    have hbR' := key b hm hbD (fun h => hbR (h ▸ haR))
    obtain ⟨y, l, r, hH, -, -, hl, hr⟩ := Merge.augChords_spec (hS₂ hc')
    rcases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [hl] at hbR'; exact hH.left_not hbR'
    · rw [hr] at hbR'; exact hH.right_not hbR'
  · have hm : J.right.top ∈ Merge.shoot J.whole a σ := by rw [he]; exact origin_mem J
    exact J.right.not_mem_set_of_mem_dom
      (key _ hm (hset _ J.right.top_mem_set) (Ne.symm hat)) J.right.top_mem_set

/-- **The attachment of the chord from a valid origin at its hit point**, beyond the start, not
at the shared vertex. -/
theorem origin_attach (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₂)
    {a : Point} {σ : ℝ} (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) :
    ∃ (p : ℕ) (t : ℝ), p < (chainModel J.whole).W.n ∧ 0 ≤ t ∧ t < 1 ∧
      SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) p t ∧
      sidePt (chainModel J.whole).W p t = rayPt a σ (J.whole.hitParam a σ) ∧
      (Lst J : ℝ) < oW J (p + t) ∧ sidePt (chainModel J.whole).W p t ≠ J.shared := by
  obtain ⟨-, hfree, -, hwD, -, hwR⟩ := origin_hit hP (hS₂ hc) ha haR hav hlt
  have hM  := FactsChain.walkAx J.whole hP
  have he  := shoot_end_mem hc ha hfree
  have hadm := F₂plus_subset J hS₂ he
  have hw : rayPt a σ (J.whole.hitParam a σ) ∈ Merge.shoot J.whole a σ :=
    Geometry.right_mem_segment _ _
  obtain ⟨p, t, hA, hpt⟩ := endpoint_attach hM hadm hw hwD
  refine ⟨p, t, hA.1, hA.2.1, hA.2.2.1, hA, hpt,
    Lst_lt_of_dom hP hA.1 hA.2.1 hA.2.2.1 (by rwx [hpt]), fun h => ?_⟩
  rw [hpt] at h
  rw [h] at hwR
  exact J.right.not_mem_set_of_mem_dom hwR J.shared_mem_right

/-- **A chord of `C₂` is determined by an end and the direction along it.** -/
theorem chord_of_end {c c' : Set Point} (hc : c ∈ Merge.augChords J.right)
    (hc' : c' ∈ Merge.augChords J.right) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (ha' : (σ = 1 ∧ a = Merge.lend c') ∨ (σ = -1 ∧ a = Merge.rend c')) : c = c' := by
  obtain ⟨-, -, -, hR, -, -⟩ := right_hit_end hc ha
  obtain ⟨-, -, -, hR', -, -⟩ := right_hit_end hc' ha'
  obtain ⟨y, l, r, -, -, rfl, hl, hr⟩ := Merge.augChords_spec hc
  obtain ⟨y', l', r', -, -, rfl, hl', hr'⟩ := Merge.augChords_spec hc'
  rw [hl, hr] at hR
  rw [hl', hr'] at hR'
  simp at hR hR'
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases ha' with ⟨-, h⟩ | ⟨h, -⟩
    · rw [hl, hl'] at h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
      simp at h1 h2
      subst h1 h2
      rw [show r = r' by linarith]
    · norm_num at h
  · rcases ha' with ⟨h, -⟩ | ⟨-, h⟩
    · norm_num at h
    · rw [hr, hr'] at h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
      simp at h1 h2
      subst h1 h2
      rw [show l = l' by linarith]

/-- **The chord from a valid origin determines the origin, the direction and the chord of `C₂`.** -/
theorem origin_inj (hP : J.P.Simple) {c c' : Set Point} (hc : c ∈ Merge.augChords J.right)
    (hc' : c' ∈ Merge.augChords J.right) {a a' : Point} {σ σ' : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (ha' : (σ' = 1 ∧ a' = Merge.lend c') ∨ (σ' = -1 ∧ a' = Merge.rend c'))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ)
    (ha'R : a' ∈ J.right.set) (ha'v : a' ≠ J.shared)
    (hlt' : J.whole.hitParam a' σ' < J.right.hitParam a' σ')
    (heq : Merge.shoot J.whole a σ = Merge.shoot J.whole a' σ') :
    a = a' ∧ σ = σ' ∧ c = c' := by
  obtain ⟨hσ, -, hτ, hwD, -, hwR⟩ := origin_hit hP hc ha haR hav hlt
  obtain ⟨hσ', -, hτ', -, -, hwR'⟩ := origin_hit hP hc' ha' ha'R ha'v hlt'
  have haD : a ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset haR)
  -- the origins
  have haa : a = a' := by
    by_contra hne
    have hm : a ∈ Merge.shoot J.whole a' σ' := by rw [← heq]; exact origin_mem J
    have := origin_end hP hc' ha' ha'R ha'v hlt' hm haD hne
    rw [← this] at hwR'
    exact J.right.not_mem_set_of_mem_dom hwR' haR
  subst haa
  -- the directions: the hit points coincide
  have hwa : rayPt a σ (J.whole.hitParam a σ) ≠ a := fun h => by
    rw [h] at hwR; exact J.right.not_mem_set_of_mem_dom hwR haR
  have hm : rayPt a σ (J.whole.hitParam a σ) ∈ Merge.shoot J.whole a σ' := by
    rw [← heq]; exact Geometry.right_mem_segment _ _
  have hww := origin_end hP hc' ha' ha'R ha'v hlt' hm hwD hwa
  have h1 := congrArg Prod.fst hww
  rw [rayPt_fst, rayPt_fst] at h1
  have hσσ : σ = σ' := by
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · rfl
    · nlinarith
    · nlinarith
    · rfl
  subst hσσ
  exact ⟨rfl, rfl, chord_of_end hc hc' ha ha'⟩

/-- The chord of an endpoint query and the position of its origin on it. -/
theorem query_chord {Q : Polygon} {N : NF} {j : ℕ} (hj : j < 2 * N.nChords) :
    (N.chord (j / 2)).toSet (chainModel J.right) Q ∈ N.F (chainModel J.right) Q ∧
      ((endDir j = 1 ∧ endOrigin J Q N j =
          Merge.lend ((N.chord (j / 2)).toSet (chainModel J.right) Q)) ∨
        (endDir j = -1 ∧ endOrigin J Q N j =
          Merge.rend ((N.chord (j / 2)).toSet (chainModel J.right) Q))) := by
  have hk : j / 2 < N.nChords := by omega
  refine ⟨⟨N.chord (j / 2), ?_, rfl⟩, ?_⟩
  · unfold NF.chord
    rw [NFLoc.getD_of_lt _ hk]
    exact List.getElem_mem _
  · unfold endDir endOrigin
    by_cases h : j % 2 = 0
    · exact Or.inl ⟨by simp [h], by simp [h]⟩
    · exact Or.inr ⟨by simp [h], by simp [h]⟩

end Origin

/-- **Task O: the chord seen from a valid origin.** -/
theorem originTask : SweepEv.OriginTask := by
  intro J Q N hP hN _hF
  have hS₂  := hN.1.2.1
  refine ⟨fun j hj haR hav hat hlt => ?_, fun j j' hj hj' haR hav _hat hlt haR' hav' _hat' hlt'
    heq => ?_⟩
  · obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Q) hj
    exact ⟨origin_not_stop hP hS₂ (hS₂ hc) ha haR hav hat hlt,
      origin_attach hP hS₂ hc ha haR hav hlt⟩
  · obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Q) hj
    obtain ⟨hc', ha'⟩ := query_chord (J := J) (Q := Q) hj'
    obtain ⟨-, hσ, hcc⟩ := origin_inj hP (hS₂ hc) (hS₂ hc') ha ha' haR hav hlt haR' hav' hlt' heq
    have hk := hN.2.1 (j / 2) (j' / 2) (by omega) (by omega) hcc
    have hpar : j % 2 = j' % 2 := by
      have e1 := (endOrigin_eq J hN hj).2
      have e2 := (endOrigin_eq J hN hj').2
      rw [hσ] at e1
      by_cases h : j % 2 = 0
      · have := e2.1 (e1.2 h); omega
      · have h' : j' % 2 ≠ 0 := fun h' => h (e1.1 (e2.2 h'))
        omega
    omega

end Sweep

end

end Chazelle.Core
