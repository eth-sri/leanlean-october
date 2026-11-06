module

public import Chazelle.Core.SweepEvAnchor

/-!
# The sweep (WP-D), stage 3: the invariant after a key with an anchored chord (main lemma)

`evInv_anchor`: at a key `K` of the `C₁` part carrying an anchored chord `Z` (attached also at a
position of the open right stretch), with no chord at `K` attached at offset `0` (no pocket), the
label set made of the side labels of the anchored chords at `K` satisfies `EvInv` at `K`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open WalkEmbed

namespace Sweep

section Anchor2

variable {J : Merge.Junction}

/-- `e` bounds the region faced just after `(pK, tK)`. -/
def AftChord (J : Merge.Junction) (S₂ : Set (Set Point)) (pK : ℕ) (tK : ℝ) (e : Set Point) :
    Prop :=
  ∀ R ∈ (chainModel J.whole).regions (F₂plus J S₂), AfterFaces (chainModel J.whole) pK tK R →
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ SideOf (chainModel J.whole) ρ e R

/-- **Case A**: the position just after `K` is not enclosed: the region after `K` has a valid
label set. -/
theorem anchor_caseA (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J (pK + tK)) {Z : Set Point} (hZ : Z ∈ F₂plus J S₂)
    (hZK : SideAttach (chainModel J.whole).W Z pK tK) {pz : ℕ} {tz : ℝ}
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J (pz + tz) < Lst J)
    {Λ : Set (Set Point)}
    (hlab : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
      (AftChord J S₂ pK tK e ∨ ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
        e' ≠ e → EvBrk J e') → EvSideLab J S₂ Λ e)
    {Ra : Set Point} (hRa : Ra ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hWa : AfterFaces (chainModel J.whole) pK tK Ra) {s : ℝ}
    (hncy : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (pK + (tK + s)))
    (hoy : oW J (pK + (tK + s)) = oW J (pK + tK) + s) (hs0 : 0 < s) (hs1 : tK + s < 1)
    (hgapy : ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
        ¬ (oW J (pK + tK) < oW J x ∧ oW J x < oW J (pK + (tK + s))))
    (hEy : ¬ EvEncl J S₂ (oW J (pK + (tK + s)))) : EvVal J S₂ Λ Ra := by
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  have hC := corr_right0 J hP hS₂a hS₂f
  have hM := hC.hM
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  have hZnb : ¬ EvBrk J Z := fun h => by have := h pz tz hZz; linarith
  obtain ⟨X, Y, dX, dY, hX, hY, hXK, hYK, hdX, hdY, hall, haft, hbef, -, -⟩ :=
    keyStruct hGM hF hZ hZK
  have hRaY := haft Ra hRa hWa
  by_cases hYb : EvBrk J Y
  · exfalso
    have hYZ : Y ≠ Z := fun h => hZnb (h ▸ hYb)
    have hXZ : X = Z := by
      rcases hall Z hZ hZK with h | h
      · exact h.symm
      · exact absurd h.symm hYZ
    obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hC.hF hY) hYK
    have hBL := hYb pb tb hB
    have hBne' : oW J (pb + tb) ≠ oW J (pK + tK) := by
      intro h
      obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hB.1 hpK hB.2.1 hB.2.2.1 htK0 htK1 h
      exact hBne rfl
    rcases lt_or_gt_of_ne hBne' with hlt | hgt
    · -- `Y` closes at `K`: the region before `K` is on a side of `Z`, faced inside `Y`'s arc
      obtain ⟨Rb, hRb, hWb, q, u, hq, hu, -, hfq, h1, h2, -⟩ := before_region_exists' hP hS₂a hS₂f
        hpK htK0 htK1 (by have : (0 : ℝ) ≤ Lst J := Nat.cast_nonneg _; linarith)
        (show 0 < oW J (pK + tK) - oW J (pb + tb) by linarith)
      have hRbZ := hbef Rb hRb hWb
      rw [hXZ] at hRbZ
      exact side_comp_off hP hS₂a hS₂f hY hZ hB hYK hlt hZz (Or.inl (by linarith)) hRb hRbZ hq hu
        (by linarith) h2 hfq
    · -- `Y` opens at `K`: the position just after `K` is enclosed
      have hyB : oW J (pK + (tK + s)) < oW J (pb + tb) := by
        rcases lt_or_ge (oW J (pK + (tK + s))) (oW J (pb + tb)) with h | h
        · exact h
        · exfalso
          rcases h.lt_or_eq with h | h
          · obtain ⟨k0, k1⟩ := attach_key_mem hB
            exact hgapy _ ⟨Y, hY, pb, tb, hB, rfl⟩ k0 k1 ⟨hgt, h⟩
          · obtain ⟨k0, k1⟩ := attach_key_mem hB
            have hk := Corr.key_mem hpK (show 0 ≤ tK + s by linarith) hs1
            have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
            have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
              exact_mod_cast hC.hg
            have hkey := off_inj hg0 hgn hk.1 hk.2 k0 k1 (by rw [← oW_eq, ← oW_eq]; exact h.symm)
            exact hncy ⟨Y, hY, pb, tb, hB, hkey⟩
      exact hEy ⟨Y, hY, pK, pb, tK, tb, hYK, hB, hBne.symm, hLst, by rw [hoy]; linarith,
        Or.inl hyB⟩
  · obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = -dY := ⟨_, rfl⟩
    have hρ : -dY = 1 ∨ -dY = -1 := by rcases hdY.cases with h | h <;> simp [h]
    exact hlab Y hY hYK hYb (Or.inl fun R hR hW => ⟨-dY, hρ, haft R hR hW⟩) Ra hRa (-dY) hρ hRaY

/-- **The second piece is alone at its far end**: `c` and `s'` tie at `B`, `s'` is attached also at
`C`, both beyond the start, `C` not an attachment of `c`; then `s'` is the only chord at `C` (three
chords would be pieces of one chord of `S₂`). -/
theorem alone_far (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) (hNTV : NoTieV J S₂) {c s' : Set Point} (hc : c ∈ F₂plus J S₂)
    (hs' : s' ∈ F₂plus J S₂) (hcs : c ≠ s') {pa qb qc : ℕ} {ta sb sc : ℝ}
    (hcA : SideAttach (chainModel J.whole).W c pa ta) (hcB : SideAttach (chainModel J.whole).W c qb sb)
    (hsB : SideAttach (chainModel J.whole).W s' qb sb)
    (hsC : SideAttach (chainModel J.whole).W s' qc sc) (hLB : (Lst J : ℝ) < oW J (qb + sb))
    (hLC : (Lst J : ℝ) < oW J (qc + sc)) (hCa : oW J (qc + sc) ≠ oW J (pa + ta))
    (hCb : oW J (qc + sc) ≠ oW J (qb + sb)) (hab : oW J (pa + ta) ≠ oW J (qb + sb)) :
    ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e qc sc → e = s' := by
  have hC := corr_right0 J hP hS₂ hS₂f
  intro e he hE
  by_contra hne
  have hout : ∀ {q : ℕ} {u : ℝ}, (Lst J : ℝ) < oW J (q + u) →
      ¬ (0 < oW J (q + u) ∧ oW J (q + u) < Lst J) := fun h h' => by linarith [h'.2]
  have hDC : sidePt (chainModel J.whole).W qc sc ∈ J.right.dom := by
    rcases tie_dom hP hS₂ hS₂f hs' he (Ne.symm hne) hsC hE (hout hLC) with h | h
    · exact h
    · exact (hNTV s' hs' e he (Ne.symm hne) qc sc hsC hE h hLC).elim
  have hDB : sidePt (chainModel J.whole).W qb sb ∈ J.right.dom := by
    rcases tie_dom hP hS₂ hS₂f hc hs' hcs hcB hsB (hout hLB) with h | h
    · exact h
    · exact (hNTV c hc s' hs' hcs qb sb hcB hsB h hLB).elim
  obtain ⟨p₁, hp₁, hs'1, he1⟩ := tie_parent J hP hS₂ hs' he hne hsC hE hDC
  obtain ⟨p₂, hp₂, hc2, hs'2⟩ := tie_parent J hP hS₂ hc hs' (Ne.symm hcs) hcB hsB hDB
  have hpp : p₁ = p₂ := parent_unique hS₂ hp₁ hp₂
    (pt_ne_of_off_ne hP hS₂ hS₂f hs' hsB hsC (Ne.symm hCb)) (hs'1 hsB.2.2.2.1)
    (hs'1 hsC.2.2.2.1) (hs'2 hsB.2.2.2.1) (hs'2 hsC.2.2.2.1)
  subst hpp
  rcases pieces_le_two hP hS₂ hp₁ hc hs' he hc2 hs'1 he1 hcB hsB hE hDB hDB hDC with h | h | h
  · exact hcs h
  · subst h
    rcases key_of_two hC.hM (hC.hF hc) hcA hcB (pt_ne_of_off_ne hP hS₂ hS₂f hc hcA hcB hab) hE with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hCa rfl
    · exact hCb rfl
  · exact hne h.symm

/-- **Case B**: the position just after `K` is enclosed: a bracket `c` opens at `K` (with `Z`, a
tie) and closes before `x`; the region at `x` is the middle region of the tie at `K`, on a side of
`Z`. -/
theorem anchor_caseB (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) (hNTV : NoTieV J S₂) {pK : ℕ}
    {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J (pK + tK)) {Z : Set Point} (hZ : Z ∈ F₂plus J S₂)
    (hZK : SideAttach (chainModel J.whole).W Z pK tK) {pz : ℕ} {tz : ℝ}
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J (pz + tz) < Lst J)
    (hnp : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK →
      ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J (q + s) ≠ 0)
    {Λ : Set (Set Point)}
    (hlab : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
      (AftChord J S₂ pK tK e ∨ ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
        e' ≠ e → EvBrk J e') → EvSideLab J S₂ Λ e)
    {p : ℕ} {t : ℝ} (hp : p < (chainModel J.whole).W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (p + t))
    (hbr : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oW J (pK + tK) < oW J (q + s) → oW J (q + s) < oW J (p + t) → EvBrk J e)
    (hEx : ¬ EvEncl J S₂ (oW J (p + t))) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) (hf : (chainModel J.whole).Faces p t G)
    {s : ℝ} (hs0 : 0 < s) (hs1 : tK + s < 1)
    (hncy : ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (pK + (tK + s)))
    (hoy : oW J (pK + (tK + s)) = oW J (pK + tK) + s) (hyx : oW J (pK + (tK + s)) < oW J (p + t))
    (hgapy : ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
        ¬ (oW J (pK + tK) < oW J x ∧ oW J x < oW J (pK + (tK + s))))
    {Ra : Set Point} (hRa : Ra ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hWa : AfterFaces (chainModel J.whole) pK tK Ra)
    (hfy : (chainModel J.whole).Faces pK (tK + s) Ra)
    (hEy : EvEncl J S₂ (oW J (pK + (tK + s)))) : EvVal J S₂ Λ G := by
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  have hC := corr_right0 J hP hS₂a hS₂f
  have hM := hC.hM
  have hGM : GoodModel (chainModel J.whole) := Or.inl ⟨J.whole, hP, rfl⟩
  have hg0 : (0 : ℝ) ≤ ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgn : ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) < (chainModel J.whole).W.n := by
    exact_mod_cast hC.hg
  have hL0 : (0 : ℝ) ≤ Lst J := Nat.cast_nonneg _
  set o' := oW J (pK + tK) with ho'
  set oy := oW J (pK + (tK + s)) with hoydef
  set ox := oW J (p + t) with hoxdef
  have hZnb : ¬ EvBrk J Z := fun h => by have := h pz tz hZz; linarith
  -- attachments are not at `y` nor at `x`, and offsets determine positions
  have hcg : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      ¬ (o' < oW J (q + u) ∧ oW J (q + u) < oy) := fun e he q u hA => by
    obtain ⟨k0, k1⟩ := attach_key_mem hA
    exact hgapy _ ⟨e, he, q, u, hA, rfl⟩ k0 k1
  have hnex : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      oW J (q + u) ≠ ox := fun e he q u hA h => by
    obtain ⟨k0, k1⟩ := attach_key_mem hA
    obtain ⟨x0, x1⟩ := Corr.key_mem hp ht.1.le ht.2
    exact hnc ⟨e, he, q, u, hA, off_inj hg0 hgn x0 x1 k0 k1 (by rw [← oW_eq, ← oW_eq]; exact h.symm)⟩
  have hposK : ∀ {q : ℕ} {u : ℝ}, q < (chainModel J.whole).W.n → 0 ≤ u → u < 1 →
      oW J (q + u) = o' → q = pK ∧ u = tK := fun hq hu0 hu1 h =>
    pos_eq_of_oW hP hS₂a hS₂f hq hpK hu0 hu1 htK0 htK1 h
  -- the enclosing chord of `y` is a bracket opening at `K`
  obtain ⟨c, hc, qa, qb, sa, sb, hA, hB, hAB, hLa, hay, hby⟩ := hEy
  have hqa : oW J (qa + sa) ≤ o' := by
    by_contra h; push Not at h; exact hcg c hc qa sa hA ⟨h, hay⟩
  rcases hby with hby | hby
  swap
  · -- a pocket
    exfalso
    rcases hqa.lt_or_eq with h | h
    · exact hEx ⟨c, hc, qa, qb, sa, sb, hA, hB, hAB, hLa, by linarith, Or.inr hby⟩
    · obtain ⟨rfl, rfl⟩ := hposK hA.1 hA.2.1 hA.2.2.1 h
      exact hnp c hc hA qb sb hB hby
  have hcZ : c ≠ Z := by
    rintro rfl
    rcases key_of_two hM (hC.hF hc) hA hB hAB hZz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hqa' : oW J (qa + sa) = o' := by
    rcases hqa.lt_or_eq with h | h
    · exact absurd (anchor_not_inside hP hS₂a hS₂f hZ hc hcZ.symm hZK hZz hA hB h (by linarith)
        (by linarith)) id
    · exact h
  obtain ⟨hq1, hq2⟩ := hposK hA.1 hA.2.1 hA.2.2.1 hqa'
  rw [hq1, hq2] at hA hAB
  clear hq1 hq2 hqa hqa' hay hLa
  -- `c` closes before `x`
  have hbx : oW J (qb + sb) < ox := by
    rcases lt_or_ge (oW J (qb + sb)) ox with h | h
    · exact h
    · rcases h.lt_or_eq with h | h
      · exact absurd ⟨c, hc, pK, qb, tK, sb, hA, hB, hAB, hLst, by linarith, Or.inl h⟩ hEx
      · exact absurd h.symm (hnex c hc qb sb hB)
  have hKqb : o' < oW J (qb + sb) := by linarith
  -- the structure at `K`: `X = Z`, `Y = c`
  obtain ⟨X, Y, dX, dY, hX, hY, hXK, hYK, hdX, hdY, hall, haft, hbef, hmid, hXY⟩ :=
    keyStruct hGM hF hZ hZK
  have hRaY := haft Ra hRa hWa
  have hYZ : Y ≠ Z := by
    rintro rfl
    exact side_comp_off hP hS₂a hS₂f hc hY hA hB hKqb hZz (Or.inl (by linarith)) hRa hRaY hpK
      ⟨by linarith, hs1⟩ (by rw [← hoydef, hoy]; linarith) (by rw [← hoydef]; linarith) hfy
  have hXZ : X = Z := by
    rcases hall Z hZ hZK with h | h
    · exact h.symm
    · exact absurd h.symm hYZ
  have hYc : Y = c := by
    rcases hall c hc hA with h | h
    · exact absurd (h.trans hXZ) hcZ
    · exact h.symm
  subst hXZ hYc
  have hXYne : X ≠ Y := fun h => hcZ h.symm
  -- the middle region `M` at `K`, on a side of `Z` (and of `c`)
  obtain ⟨Mk, hMk, hMks⟩ := side_region_exists hM hC.hF hC.hfin hc
    (show dY = 1 ∨ dY = -1 from hdY.cases)
  have hMkZ := (hmid hXYne Mk hMk).1 hMks
  have hcbrk : EvBrk J Y := fun q u hQ => by
    rcases key_of_two hM (hC.hF hc) hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hMval : EvVal J S₂ Λ Mk :=
    hlab X hX hXK hZnb (Or.inr fun e' he' hA' hne => by
      rcases hall e' he' hA' with h | h
      · exact absurd h hne
      · rw [h]; exact hcbrk) Mk hMk (-dX) (by rcases hdX.cases with h | h <;> simp [h]) hMkZ
  suffices hGM' : G = Mk by rw [hGM']; exact hMval
  -- `c` at `qb`
  have hcA := F₂plus_subset J hS₂a hc
  have hdq : DirAt (chainModel J.whole).W Y qb sb (-dY) := dirAt_other hP hcA hA hB hAB hdY
  obtain ⟨X', Y', dX', dY', hX', hY', hXq, hYq, hdX', hdY', hall', haft', hbef', hmid', hXY'⟩ :=
    keyStruct hGM hF hc hB
  have hLq : (Lst J : ℝ) ≤ oW J (qb + sb) := by linarith
  have hqbx : 0 < ox - oW J (qb + sb) := by linarith
  -- the region on a side of `c` near `c`
  obtain ⟨zc, hzc, hzcD⟩ := exists_mem_dom hM hcA hA
  have hMeq : ∀ R ∈ (chainModel J.whole).regions (F₂plus J S₂),
      SideOf (chainModel J.whole) dY Y R → R = Mk :=
    fun R hR hRs => sideOf_eq hR hMk hRs hMks hzc hzcD
  -- the region after `qb` and a position just after it
  obtain ⟨-, -, -, -, Ra', hRa', hWa'⟩ := after_region_exists hM hC.hF hC.hfin hC.hg hB.1 hB.2.1
    hB.2.2.1
  obtain ⟨s₁, hs₁0, hs₁ε, hs₁1, hfy₁, hncy₁, hoy₁, hgapy₁⟩ := after_pos_eps hP hS₂a hS₂f hB.1
    hB.2.1 hB.2.2.1 hWa' hqbx
  have hy₁x : oW J (qb + (sb + s₁)) < ox := by rw [hoy₁]; linarith
  -- the region at `x` from a non-enclosed position before it
  have hGfrom : ∀ {q : ℕ} {u : ℝ} {R : Set Point}, q < (chainModel J.whole).W.n →
      u ∈ Ioo (0 : ℝ) 1 → ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (q + u) →
      o' < oW J (q + u) → oW J (q + u) < ox → ¬ EvEncl J S₂ (oW J (q + u)) →
      R ∈ (chainModel J.whole).regions (F₂plus J S₂) → (chainModel J.whole).Faces q u R → R = G :=
    fun hq hu hncq h1 h2 hE hR hfq => evGL hP hS₂a hS₂f hq hp hu ht hncq hnc h2 hE hEx
      (fun e he q' u' hQ h3 h4 => hbr e he q' u' hQ (by linarith) h4) hR hG hfq hf
  -- chords at `K` other than `Z` and `c`
  have hatK : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      oW J (q + u) = o' → e = X ∨ e = Y := fun e he q u hQ h => by
    obtain ⟨rfl, rfl⟩ := hposK hQ.1 hQ.2.1 hQ.2.2.1 h
    exact hall e he hQ
  -- chords at `qb`
  have hatB : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      oW J (q + u) = oW J (qb + sb) → e = X' ∨ e = Y' := fun e he q u hQ h => by
    obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hQ.1 hB.1 hQ.2.1 hQ.2.2.1 hB.2.1 hB.2.2.1 h
    exact hall' e he hQ
  -- the attachments of `c`
  have hcatt : ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W Y q u →
      oW J (q + u) = o' ∨ oW J (q + u) = oW J (qb + sb) := fun q u hQ => by
    rcases key_of_two hM hcA hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases htie : X' = Y'
  · -- `c` alone at `qb`
    subst htie
    have hYX' : Y = X' := by rcases hall' Y hY hB with h | h <;> exact h
    have hdY' : dY' = -dY := by
      have := hdY'
      rw [← hYX'] at this
      exact dirAt_unique hP hcA hB this hdq
    have hRa'c : SideOf (chainModel J.whole) dY Y Ra' := by
      have := haft' Ra' hRa' hWa'
      rw [hdY', neg_neg, ← hYX'] at this
      exact this
    have hnE : ¬ EvEncl J S₂ (oW J (qb + (sb + s₁))) := by
      refine noEncl_of_closed hP hS₂a hS₂f hZ hZK hZz hzL hLst hKqb.le ?_ (by rw [hoy₁]; linarith)
        hy₁x (fun e he q u hQ h => hgapy₁ _ ⟨e, he, q, u, hQ, rfl⟩ (attach_key_mem hQ).1
          (attach_key_mem hQ).2 h) hEx
      intro e he heZ q u hQ h1 h2 q' u' hQ'
      by_cases hec : e = Y
      · subst hec
        rcases hcatt q' u' hQ' with h | h <;> rw [h] <;> constructor <;> linarith
      rcases h1.lt_or_eq with h1 | h1
      · rcases h2.lt_or_eq with h2 | h2
        · exact closed_nested hP hS₂a hS₂f hc he (Ne.symm hec) hA hB hKqb hQ h1 h2 hQ'
        · rcases hatB e he q u hQ h2 with h | h <;> exact absurd (h.trans hYX'.symm) hec
      · rcases hatK e he q u hQ h1.symm with h | h
        · exact absurd h heZ
        · exact absurd h hec
    rw [← hMeq Ra' hRa' hRa'c]
    exact (hGfrom hB.1 ⟨by linarith [hB.2.1], hs₁1⟩ hncy₁ (by rw [hoy₁]; linarith) hy₁x hnE hRa'
      hfy₁).symm
  · -- a tie at `qb`: `c` and the other chord `s'`
    obtain ⟨s', hs', hs'B, hs'c, hcase⟩ : ∃ s' ∈ F₂plus J S₂,
        SideAttach (chainModel J.whole).W s' qb sb ∧ s' ≠ Y ∧
        ((Y = X' ∧ s' = Y') ∨ (Y = Y' ∧ s' = X')) := by
      rcases hall' Y hY hB with h | h
      · exact ⟨Y', hY', hYq, fun h' => htie (h.symm.trans h'.symm), Or.inl ⟨h, rfl⟩⟩
      · exact ⟨X', hX', hXq, fun h' => htie (h'.trans h), Or.inr ⟨h, rfl⟩⟩
    have hs'brk : EvBrk J s' := hbr s' hs' qb sb hs'B hKqb hbx
    have hs'Z : s' ≠ X := fun h => hZnb (h ▸ hs'brk)
    -- the direction of `s'` at `qb` is `dY`
    have hs'A := F₂plus_subset J hS₂a hs'
    have hds : DirAt (chainModel J.whole).W s' qb sb dY := by
      rcases hM.tie_pair hC.hF hc hs' (Ne.symm hs'c) hB hs'B with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := dirAt_unique hP hcA hB (Or.inl ⟨rfl, h1⟩) hdq
        have hd : dY = -1 := by linarith
        exact Or.inr ⟨hd, h2⟩
      · have := dirAt_unique hP hcA hB (Or.inr ⟨rfl, h1⟩) hdq
        have hd : dY = 1 := by linarith
        exact Or.inl ⟨hd, h2⟩
    -- the other attachment of `s'`
    obtain ⟨qc, sc, hC', hC'ne⟩ := hM.other_attach (hC.hF hs') hs'B
    have hLc := hs'brk qc sc hC'
    have hcb : oW J (qc + sc) ≠ oW J (qb + sb) := by
      intro h
      obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hC'.1 hB.1 hC'.2.1 hC'.2.2.1 hB.2.1 hB.2.2.1 h
      exact hC'ne rfl
    have hcK : o' < oW J (qc + sc) := by
      rcases lt_or_ge o' (oW J (qc + sc)) with h | h
      · exact h
      · exfalso
        rcases h.lt_or_eq with h | h
        · exact anchor_not_inside hP hS₂a hS₂f hZ hs' (Ne.symm hs'Z) hZK hZz hC' hs'B h hKqb
            (by linarith)
        · rcases hatK s' hs' qc sc hC' h with h' | h'
          · exact hs'Z h'
          · exact hs'c h'
    have hcx : oW J (qc + sc) < ox := by
      rcases lt_or_ge (oW J (qc + sc)) ox with h | h
      · exact h
      · exfalso
        rcases h.lt_or_eq with h | h
        · exact hEx ⟨s', hs', qb, qc, sb, sc, hs'B, hC', hC'ne.symm, hLq, hbx, Or.inl h⟩
        · exact hnex s' hs' qc sc hC' h.symm
    -- `s'` is alone at `qc`
    have halone : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e qc sc → e = s' :=
      alone_far hP hS₂a hS₂f hNTV hc hs' (Ne.symm hs'c) hA hB hs'B hC' (by linarith) (by linarith)
        (by linarith) hcb (by linarith)
    have hdsC : DirAt (chainModel J.whole).W s' qc sc (-dY) :=
      dirAt_other hP hs'A hs'B hC' hC'ne.symm hds
    obtain ⟨X'', Y'', dX'', dY'', hX'', hY'', hXc, hYc, hdX'', hdY'', hall'', haft'', hbef'', -,
      -⟩ := keyStruct hGM hF hs' hC'
    have hX''s : X'' = s' := halone X'' hX'' hXc
    have hY''s : Y'' = s' := halone Y'' hY'' hYc
    subst hX''s
    have hdX''e : dX'' = -dY := dirAt_unique hP hs'A hC' hdX'' hdsC
    have hdY''e : dY'' = -dY := dirAt_unique hP hs'A hC' (hY''s ▸ hdY'') hdsC
    obtain ⟨zs, hzs, hzsD⟩ := exists_mem_dom hM hs'A hs'B
    have hs'eq : ∀ {ρ : ℝ} {R R' : Set Point}, R ∈ (chainModel J.whole).regions (F₂plus J S₂) →
        R' ∈ (chainModel J.whole).regions (F₂plus J S₂) → SideOf (chainModel J.whole) ρ X'' R →
        SideOf (chainModel J.whole) ρ X'' R' → R = R' :=
      fun hR hR' h h' => sideOf_eq hR hR' h h' hzs hzsD
    rcases hcase with ⟨hYX', hs'Y'⟩ | ⟨hYY', hs'X'⟩
    · -- (a) `c` bounds the region before `qb`, `s'` the one after
      have hdY'e : dY' = dY := by
        rw [← hs'Y'] at hdY'; exact dirAt_unique hP hs'A hs'B hdY' hds
      have hdX'e : dX' = -dY := by
        rw [← hYX'] at hdX'; exact dirAt_unique hP hcA hB hdX' hdq
      have hRa's : SideOf (chainModel J.whole) (-dY) X'' Ra' := by
        have := haft' Ra' hRa' hWa'
        rw [hdY'e, ← hs'Y'] at this; exact this
      rcases lt_or_gt_of_ne hcb with hlt | hgt
      · -- (iii) `qc` before `qb`: the region before `qc` is the region after `qb`: impossible
        exfalso
        obtain ⟨Rb', hRb', hWb', w, u, hw, hu, -, hfw, h1, h2, -⟩ := before_region_exists' hP hS₂a
          hS₂f hC'.1 hC'.2.1 hC'.2.2.1 (by linarith) (show 0 < oW J (qc + sc) - o' by linarith)
        have hRb's := hbef'' Rb' hRb' hWb'
        rw [hdX''e] at hRb's
        have heq := hs'eq hRb' hRa' hRb's hRa's
        subst heq
        exact faced_both_off hP hS₂a hS₂f hc hA hB hKqb hRb' hw hB.1 hu
          ⟨by linarith [hB.2.1], hs₁1⟩ (by linarith) (by linarith) (Or.inr (by rw [hoy₁]; linarith))
          hfw hfy₁
      · -- (iv) `qc` after `qb`: the region after `qc` is the middle region at `K`
        have hMs : SideOf (chainModel J.whole) dY X'' Mk := by
          have := (hmid' (by rw [← hYX', ← hs'Y']; exact hs'c.symm) Mk hMk).2
          rw [hdY'e, hdX'e, neg_neg, ← hYX', ← hs'Y'] at this
          exact this hMks
        obtain ⟨-, -, -, -, Ra'', hRa'', hWa''⟩ := after_region_exists hM hC.hF hC.hfin hC.hg hC'.1
          hC'.2.1 hC'.2.2.1
        have hRa''s := haft'' Ra'' hRa'' hWa''
        rw [hdY''e, neg_neg, hY''s] at hRa''s
        have hRM : Ra'' = Mk := hs'eq hRa'' hMk hRa''s hMs
        obtain ⟨s₂, hs₂0, hs₂ε, hs₂1, hfy₂, hncy₂, hoy₂, hgapy₂⟩ := after_pos_eps hP hS₂a hS₂f hC'.1
          hC'.2.1 hC'.2.2.1 hWa'' (show 0 < ox - oW J (qc + sc) by linarith)
        have hnE : ¬ EvEncl J S₂ (oW J (qc + (sc + s₂))) := by
          refine noEncl_of_closed hP hS₂a hS₂f hZ hZK hZz hzL hLst (by linarith) ?_
            (by rw [hoy₂]; linarith) (by rw [hoy₂]; linarith)
            (fun e he q u hQ h => hgapy₂ _ ⟨e, he, q, u, hQ, rfl⟩ (attach_key_mem hQ).1
              (attach_key_mem hQ).2 h) hEx
          intro e he heZ q u hQ h1 h2 q' u' hQ'
          by_cases hec : e = Y
          · subst hec
            rcases hcatt q' u' hQ' with h | h <;> rw [h] <;> constructor <;> linarith
          by_cases hes : e = X''
          · subst hes
            rcases key_of_two hM hs'A hs'B hC' hC'ne.symm hQ' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              constructor <;> linarith
          rcases h1.lt_or_eq with h1 | h1
          · rcases lt_trichotomy (oW J (q + u)) (oW J (qb + sb)) with h3 | h3 | h3
            · have := closed_nested hP hS₂a hS₂f hc he (Ne.symm hec) hA hB hKqb hQ h1 h3 hQ'
              constructor <;> linarith [this.1, this.2]
            · rcases hatB e he q u hQ h3 with h | h
              · exact absurd (h.trans hYX'.symm) hec
              · exact absurd (h.trans hs'Y'.symm) hes
            · rcases h2.lt_or_eq with h2 | h2
              · have := closed_nested hP hS₂a hS₂f hs' he (Ne.symm hes) hs'B hC' hgt hQ h3 h2 hQ'
                constructor <;> linarith [this.1, this.2]
              · obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hQ.1 hC'.1 hQ.2.1 hQ.2.2.1 hC'.2.1
                  hC'.2.2.1 h2
                exact absurd (halone e he hQ) hes
          · rcases hatK e he q u hQ h1.symm with h | h
            · exact absurd h heZ
            · exact absurd h hec
        rw [← hRM]
        exact (hGfrom hC'.1 ⟨by linarith [hC'.2.1], hs₂1⟩ hncy₂ (by rw [hoy₂]; linarith)
          (by rw [hoy₂]; linarith) hnE hRa'' hfy₂).symm
    · -- (b) `s'` bounds the region before `qb`, `c` the one after
      have hdY'e : dY' = -dY := by
        rw [← hYY'] at hdY'; exact dirAt_unique hP hcA hB hdY' hdq
      have hdX'e : dX' = dY := by
        rw [← hs'X'] at hdX'; exact dirAt_unique hP hs'A hs'B hdX' hds
      have hRa'c : SideOf (chainModel J.whole) dY Y Ra' := by
        have := haft' Ra' hRa' hWa'
        rw [hdY'e, neg_neg, ← hYY'] at this; exact this
      have hRM : Ra' = Mk := hMeq Ra' hRa' hRa'c
      rcases lt_or_gt_of_ne hcb with hlt | hgt
      · -- (iii) `qc` before `qb`: the position after `qb` is not enclosed
        have hnE : ¬ EvEncl J S₂ (oW J (qb + (sb + s₁))) := by
          refine noEncl_of_closed hP hS₂a hS₂f hZ hZK hZz hzL hLst hKqb.le ?_
            (by rw [hoy₁]; linarith) hy₁x (fun e he q u hQ h => hgapy₁ _ ⟨e, he, q, u, hQ, rfl⟩
              (attach_key_mem hQ).1 (attach_key_mem hQ).2 h) hEx
          intro e he heZ q u hQ h1 h2 q' u' hQ'
          by_cases hec : e = Y
          · subst hec
            rcases hcatt q' u' hQ' with h | h <;> rw [h] <;> constructor <;> linarith
          by_cases hes : e = X''
          · subst hes
            rcases key_of_two hM hs'A hs'B hC' hC'ne.symm hQ' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              constructor <;> linarith
          rcases h1.lt_or_eq with h1 | h1
          · rcases h2.lt_or_eq with h2 | h2
            · exact closed_nested hP hS₂a hS₂f hc he (Ne.symm hec) hA hB hKqb hQ h1 h2 hQ'
            · rcases hatB e he q u hQ h2 with h | h
              · exact absurd (h.trans hs'X'.symm) hes
              · exact absurd (h.trans hYY'.symm) hec
          · rcases hatK e he q u hQ h1.symm with h | h
            · exact absurd h heZ
            · exact absurd h hec
        rw [← hRM]
        exact (hGfrom hB.1 ⟨by linarith [hB.2.1], hs₁1⟩ hncy₁ (by rw [hoy₁]; linarith) hy₁x hnE
          hRa' hfy₁).symm
      · -- (iv) `qc` after `qb`: the region after `qc` is the region before `qb`: impossible
        exfalso
        obtain ⟨Rb, hRb, hWb, w, u, hw, hu, -, hfw, h1, h2, -⟩ := before_region_exists' hP hS₂a
          hS₂f hB.1 hB.2.1 hB.2.2.1 (by linarith) (show 0 < oW J (qb + sb) - o' by linarith)
        have hRbs := hbef' Rb hRb hWb
        rw [hdX'e, ← hs'X'] at hRbs
        obtain ⟨-, -, -, -, Ra'', hRa'', hWa''⟩ := after_region_exists hM hC.hF hC.hfin hC.hg hC'.1
          hC'.2.1 hC'.2.2.1
        have hRa''s := haft'' Ra'' hRa'' hWa''
        rw [hdY''e, neg_neg, hY''s] at hRa''s
        have heq := hs'eq hRa'' hRb hRa''s hRbs
        subst heq
        obtain ⟨s₂, hs₂0, hs₂ε, hs₂1, hfy₂, -, hoy₂, -⟩ := after_pos_eps hP hS₂a hS₂f hC'.1
          hC'.2.1 hC'.2.2.1 hWa'' (show (0 : ℝ) < 1 by norm_num)
        exact faced_both_off hP hS₂a hS₂f hc hA hB hKqb hRa'' hw hC'.1 hu
          ⟨by linarith [hC'.2.1], hs₂1⟩ (by linarith) (by linarith)
          (Or.inr (by rw [hoy₂]; linarith)) hfw hfy₂

/-- **The invariant after a key with an anchored chord.**  At a key `K` of the `C₁` part carrying an
anchored chord `Z` (attached also at offset in `(0, Lst)`) and no chord attached at offset `0`, a
label set containing the side labels of every non-bracket chord at `K` satisfies `EvInv` at `K`. -/
theorem evInv_anchor (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) (hNTV : NoTieV J S₂) {pK : ℕ}
    {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J (pK + tK)) {Z : Set Point} (hZ : Z ∈ F₂plus J S₂)
    (hZK : SideAttach (chainModel J.whole).W Z pK tK) {pz : ℕ} {tz : ℝ}
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J (pz + tz) < Lst J)
    (hnp : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK →
      ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J (q + s) ≠ 0)
    {Λ : Set (Set Point)}
    (hlab : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
      (AftChord J S₂ pK tK e ∨ ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
        e' ≠ e → EvBrk J e') → EvSideLab J S₂ Λ e) :
    EvInv J S₂ (oW J (pK + tK)) Λ := by
  intro p t hp ht hnc ho hbr
  by_cases hEx : EvEncl J S₂ (oW J (p + t))
  · exact Or.inl hEx
  right
  intro G hG hf
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  have hC := corr_right0 J hP hS₂a hS₂f
  obtain ⟨-, -, -, -, Ra, hRa, hWa⟩ := after_region_exists hC.hM hC.hF hC.hfin hC.hg hpK htK0 htK1
  obtain ⟨s, hs0, hsε, hs1, hfy, hncy, hoy, hgapy⟩ := after_pos_eps hP hS₂a hS₂f hpK htK0 htK1 hWa
    (show 0 < oW J (p + t) - oW J (pK + tK) by linarith)
  have hyx : oW J (pK + (tK + s)) < oW J (p + t) := by rw [hoy]; linarith
  by_cases hEy : EvEncl J S₂ (oW J (pK + (tK + s)))
  · exact anchor_caseB hP hS₂ hF hNTV hpK htK0 htK1 hLst hZ hZK hZz hzL hnp hlab hp ht hnc hbr hEx
      hG hf hs0 hs1 hncy hoy hyx hgapy hRa hWa hfy hEy
  · have hRaG : Ra = G := evGL hP hS₂a hS₂f hpK hp ⟨by linarith, hs1⟩ ht hncy hnc hyx hEy hEx
      (fun e he q u hQ h1 h2 => hbr e he q u hQ (by rw [hoy] at h1; linarith) h2) hRa hG hfy hf
    rw [← hRaG]
    exact anchor_caseA hP hS₂ hF hpK htK0 htK1 hLst hZ hZK hZz hzL hlab hRa hWa hncy hoy hs0 hs1
      hgapy hEy

end Anchor2

end Sweep

end

end Chazelle.Core
