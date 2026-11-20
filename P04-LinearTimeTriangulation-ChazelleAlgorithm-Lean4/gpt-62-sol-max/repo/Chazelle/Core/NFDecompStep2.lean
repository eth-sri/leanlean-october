module

public import Chazelle.Core.NFDecompStep

/-!
# Tree decomposition (WP-C), part 6: preservation of the round invariant

`rinv_next`: from `RInv` at round `j` and the characterisation of the top pass, one round
(`next`) gives `RInv` at round `j + 1`, with the ghosts extended by the chords cut in this round
(`gcNext`, `crNext`).
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

set_option linter.unusedSectionVars false

/-- The ghost components after a round. -/
noncomputable def gcNext (R K : ℕ) (prg pch chOf top best : ℕ → ℕ) (σ : RS) (gc : ℕ → Finset ℕ)
    (e : ℕ) : Finset ℕ :=
  if e < K ∧ Chosen σ top best chOf e then sub R prg pch σ.rem (top (chOf e)) else gc e

/-- The ghost cut rounds after round `j`. -/
def crNext (K : ℕ) (chOf top best : ℕ → ℕ) (σ : RS) (j : ℕ) (cr : ℕ → ℕ) (e : ℕ) : ℕ :=
  if e < K ∧ Chosen σ top best chOf e then j else cr e

/-- The arithmetic of a cut: both parts shrink by the factor `(D - 1) / D`. -/
theorem split_bound {D a b : ℕ} (hD : 1 ≤ D) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : a + b - 1 ≤ D * min a b) :
    D * (a - 1) ≤ (D - 1) * (a + b - 1) ∧ D * (b - 1) ≤ (D - 1) * (a + b - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm ⊢
  have e1 : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
  rw [e1] at hm ⊢
  rcases le_total a' b' with hab | hab
  · rw [min_eq_left (by omega)] at hm
    constructor
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp at hm; omega
      · nlinarith
    · nlinarith
  · rw [min_eq_right (by omega)] at hm
    constructor
    · nlinarith
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp at hm; omega
      · nlinarith

section step2

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

local notation "σ'" => next R K prg pch isdn chOf top best σ
local notation "gc'" => gcNext R K prg pch chOf top best σ gc
local notation "cr'" => crNext K chOf top best σ j cr

theorem mem_sideSet {s e v : ℕ} :
    v ∈ sideSet R prg pch isdn chOf s e ↔ v < R ∧ OnSide R prg pch isdn chOf s e v := by
  classical
  simp [sideSet]

theorem gc_old {e : ℕ} (hr : σ.rem e = 1) : gc' e = gc e := by
  unfold gcNext
  rw [ite_eq_right (fun hh => hh.2.1 hr)]

theorem cr_old {e : ℕ} (hr : σ.rem e = 1) : cr' e = cr e := by
  unfold crNext
  rw [ite_eq_right (fun hh => hh.2.1 hr)]

theorem gc_new {e : ℕ} (he : e < K) (hc : Chosen σ top best chOf e) :
    gc' e = sub R prg pch σ.rem (top (chOf e)) := by
  unfold gcNext
  rw [ite_eq_left ⟨he, hc⟩]

theorem cr_new {e : ℕ} (he : e < K) (hc : Chosen σ top best chOf e) : cr' e = j := by
  unfold crNext
  rw [ite_eq_left ⟨he, hc⟩]

/-- After the first round the root code does not change. -/
theorem root_next_pos (hj : 1 ≤ j) : (σ').root = σ.root := by
  simp only [next]
  by_cases ha : σ.act 0 = 1
  · rw [ite_eq_left ha]
    rcases hI.i4 0 h.R_pos (Or.inl rfl) ha with ⟨-, -, hj0⟩ | ⟨hs, -⟩
    · omega
    · rw [ite_eq_right (by omega)]
  · rw [ite_eq_right ha]

/-- The new state at an old top. -/
theorem act_top {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').act t = (if σ.act t = 1 then (if best t = t then 0 else σ.act t) else σ.act t) := by
  simp only [next, ite_eq_left ht, ite_eq_left (top_self h hch hT hB hI ht htop)]

theorem cpar_top {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').cpar t = (if σ.act t = 1 then (if best t = t then σ.cpar t else pch (best t)) else σ.cpar t) := by
  simp only [next, ite_eq_left ht, ite_eq_left (top_self h hch hT hB hI ht htop)]

theorem side_top {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').side t = (if σ.act t = 1 then (if best t = t then σ.side t else
      (if isdn (best t) = 1 then 1 else 0)) else σ.side t) := by
  simp only [next, ite_eq_left ht, ite_eq_left (top_self h hch hT hB hI ht htop)]

theorem lpar_top {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').lpar t = (if σ.act t = 1 then (if best t = t then
      (if σ.side t = 2 then 2 * t + 1 else 2 * σ.cpar t) else σ.lpar t) else σ.lpar t) := by
  simp only [next, ite_eq_left ht, ite_eq_left (top_self h hch hT hB hI ht htop)]

/-- The new state at the child endpoint of a chosen chord. -/
theorem new_top_facts {e : ℕ} (he : e < K) (hc : Chosen σ top best chOf e) :
    (σ').act (chOf e) = 1 ∧ (σ').cpar (chOf e) = e ∧
      (σ').side (chOf e) = (if isdn (chOf e) = 1 then 0 else 1) := by
  obtain ⟨-, -, -, -, -, hnt, -, c1, -, c3, -⟩ := chosen_facts h hch hT hB hI he hc
  have hnt' : top (chOf e) ≠ chOf e := fun e' => hnt ((top_iff h hch hT hB hI c1).1 e')
  have hp : nPend K chOf top best σ e = 1 := (pend_next h hch hT hB hI he).2 hc
  refine ⟨?_, ?_, ?_⟩ <;> simp only [next, ite_eq_left c1, ite_eq_right hnt', c3, ite_eq_left hp]

/-- An old top that is not active stays as it is. -/
theorem valid_next {x : ℕ} (hx : ValidC R K pch σ x) :
    ValidC R K pch (σ') x ∧ compOf gc' x = compOf gc x ∧ pcode (σ') x = pcode σ x := by
  rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · have hnc : ¬ Chosen σ top best chOf (x / 2) := fun hh => hh.1 h3
    refine ⟨Or.inl ⟨h1, h2, rem_mono h hch hT hB hI h3⟩, ?_, ?_⟩
    · simp only [compOf, ite_eq_left h1, gc_old h hch hT hB hI h3]
    · simp only [pcode, ite_eq_left h1, next, ite_eq_left h2, ite_eq_right hnc]
      by_cases hp : σ.pend (x / 2) = 1
      · rw [ite_eq_left hp]
      · rw [ite_eq_right hp]
  · have hx2 : x % 2 ≠ 0 := by omega
    refine ⟨Or.inr ⟨h1, h2, (istop_next h hch hT hB hI h2).2 (Or.inl h3), ?_⟩, ?_, ?_⟩
    · rw [act_top h hch hT hB hI h2 h3, ite_eq_right h4]; exact h4
    · simp only [compOf, ite_eq_right hx2]
    · simp only [pcode, ite_eq_right hx2]
      rw [lpar_top h hch hT hB hI h2 h3, ite_eq_right h4]

/-- The code of an active component after the round. -/
theorem code_next {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1) :
    ValidC R K pch (σ') (code best pch t) ∧ compOf gc' (code best pch t) = sub R prg pch σ.rem t ∧
      pcode (σ') (code best pch t) =
        (if σ.side t = 2 then code best pch t else 2 * σ.cpar t) := by
  by_cases hbt : best t = t
  · have hcode : code best pch t = 2 * t + 1 := by unfold code; rw [ite_eq_left hbt]
    rw [hcode]
    have hm : (2 * t + 1) % 2 = 1 := by omega
    have hd : (2 * t + 1) / 2 = t := by omega
    have hsing : sub R prg pch σ.rem t = {t} := by
      ext v
      rw [mem_sub, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, htv⟩
        rcases (hB t ht htop).2 with ⟨-, b2⟩ | ⟨-, -, b3, -⟩
        · exact b2 v hv htv
        · exact absurd hbt b3
      · rintro rfl; exact ⟨ht, ReflTransGen.refl⟩
    have v1 : (2 * t + 1) / 2 < R := by rw [hd]; exact ht
    have v2 : IsTop pch (σ').rem ((2 * t + 1) / 2) := by
      rw [hd]; exact (istop_next h hch hT hB hI ht).2 (Or.inl htop)
    have v3 : (σ').act ((2 * t + 1) / 2) ≠ 1 := by
      rw [hd, act_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]; norm_num
    refine ⟨Or.inr ⟨hm, v1, v2, v3⟩, ?_, ?_⟩
    · simp only [compOf, hm, hd, hsing]; rfl
    · simp only [pcode, hm, hd, lpar_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]
      norm_num
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := cut_chosen h hch hT hB hI ht htop hact hbt
    have hcode : code best pch t = 2 * pch (best t) := by unfold code; rw [ite_eq_right hbt]
    rw [hcode]
    have hm : (2 * pch (best t)) % 2 = 0 := by omega
    have hd : (2 * pch (best t)) / 2 = pch (best t) := by omega
    have v1 : (2 * pch (best t)) / 2 < K := by rw [hd]; exact b4
    have v2 : (σ').rem ((2 * pch (best t)) / 2) = 1 := by
      rw [hd]; exact (rem_next h hch hT hB hI b4).2 (Or.inr b7)
    refine ⟨Or.inl ⟨hm, v1, v2⟩, ?_, ?_⟩
    · simp only [compOf, hm, hd, gc_new h hch hT hB hI b4 b7, b5, b6]; rfl
    · have hp : σ.pend (pch (best t)) ≠ 1 := fun hp => b8 (hI.i0 _ b4 hp)
      simp only [pcode, hm, hd, next, ite_eq_left b4, ite_eq_right hp, ite_eq_left b7, b5, b6]
      rfl

/-- The pending chord's child tops, as the chord pass computes them. -/
theorem pend_child {e s t : ℕ} (he : e < K) (hp : σ.pend e = 1) (_ht : t < R)
    (htop : IsTop pch σ.rem t)
    (hsub : sub R prg pch σ.rem t = gc e ∩ sideSet R prg pch isdn chOf s e) :
    (if (isdn (chOf e) = 1 ↔ s = 0) then chOf e else top (prg (chOf e))) = t := by
  have hr := hI.i0 e he hp
  obtain ⟨-, hcm, hpm, -⟩ := hI.i1 e he hr
  obtain ⟨c1, c2, c3⟩ := hch e he
  have hctop : IsTop pch σ.rem (chOf e) := Or.inr (by rw [c3]; exact hr)
  have hpR : prg (chOf e) < R := h.prg_lt _ c1 c2
  by_cases hcond : (isdn (chOf e) = 1 ↔ s = 0)
  · rw [ite_eq_left hcond]
    have hmem : chOf e ∈ sub R prg pch σ.rem t := by
      rw [hsub, Finset.mem_inter, mem_sideSet h hch hT hB hI]
      exact ⟨hcm, c1, ⟨fun _ => hcond, fun _ => ReflTransGen.refl⟩⟩
    rw [mem_sub] at hmem
    by_contra hne
    exact AncX.not_top hmem.2 (Ne.symm hne) hctop
  · rw [ite_eq_right hcond]
    have hmem : prg (chOf e) ∈ sub R prg pch σ.rem t := by
      rw [hsub, Finset.mem_inter, mem_sideSet h hch hT hB hI]
      refine ⟨hpm, hpR, ⟨fun hh => absurd ?_ hcond, fun hh => absurd hh hcond⟩⟩
      have h1 := (AncX.pos_le h hh hpR).2.1
      have h2 := h.pos_prg _ c1 c2
      omega
    rw [mem_sub] at hmem
    exact top_of h hch hT hB hI hpR htop hmem.2

theorem loTop_eq (e : ℕ) : loTop prg isdn chOf top e =
    (if (isdn (chOf e) = 1 ↔ (0 : ℕ) = 0) then chOf e else top (prg (chOf e))) := by
  unfold loTop
  by_cases hh : isdn (chOf e) = 1 <;> simp [hh]

theorem hiTop_eq (e : ℕ) : hiTop prg isdn chOf top e =
    (if (isdn (chOf e) = 1 ↔ (1 : ℕ) = 0) then chOf e else top (prg (chOf e))) := by
  unfold hiTop
  by_cases hh : isdn (chOf e) = 1 <;> simp [hh]

open Classical in
/-- The two sides of a chosen chord after the round. -/
theorem sub_new_sides {e s : ℕ} (he : e < K) (hc : Chosen σ top best chOf e) :
    ((isdn (chOf e) = 1 ↔ s = 0) →
      sub R prg pch (σ').rem (chOf e) = gc' e ∩ sideSet R prg pch isdn chOf s e) ∧
    (¬ (isdn (chOf e) = 1 ↔ s = 0) →
      sub R prg pch (σ').rem (top (chOf e)) = gc' e ∩ sideSet R prg pch isdn chOf s e) := by
  obtain ⟨t1, t2, t3, t4, t5, -, t7, c1, -, -, -⟩ := chosen_facts h hch hT hB hI he hc
  have hbt : best (top (chOf e)) ≠ top (chOf e) := by rw [t4]; exact t5
  rw [gc_new h hch hT hB hI he hc]
  constructor
  · intro hcond
    have := sub_cut_c h hch hT hB hI t1 t2 t3 hbt
    rw [t4] at this
    rw [this, sub_member h hch hT hB hI t7]
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter, mem_sideSet h hch hT hB hI, mem_sub]
    unfold OnSide
    constructor
    · rintro ⟨⟨hv, hav⟩, hcv⟩; exact ⟨⟨hv, hav⟩, hv, fun _ => hcond, fun _ => hcv⟩
    · rintro ⟨⟨hv, hav⟩, -, hh⟩; exact ⟨⟨hv, hav⟩, hh.2 hcond⟩
  · intro hcond
    have := sub_cut_t h hch hT hB hI t1 t2 t3 hbt
    rw [t4] at this
    rw [this]
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter, mem_sideSet h hch hT hB hI, mem_sub]
    unfold OnSide
    constructor
    · rintro ⟨⟨hv, hav⟩, hcv⟩; exact ⟨⟨hv, hav⟩, hv, fun hh => absurd hh hcv, fun hh => absurd hh hcond⟩
    · rintro ⟨⟨hv, hav⟩, -, hh⟩; exact ⟨⟨hv, hav⟩, fun hh' => hcond (hh.1 hh')⟩

end step2

end

end Chazelle.Core.Dec
