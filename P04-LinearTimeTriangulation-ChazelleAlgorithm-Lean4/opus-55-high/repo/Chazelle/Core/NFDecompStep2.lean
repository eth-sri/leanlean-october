module
public import Chazelle.MacT

public import Chazelle.Core.Facts2Trap

/-!
# Tree decomposition (WP-C), part 6: preservation of the round invariant

`rinv_next`: from `RInv` at round `j` and the characterisation of the top pass, one round
(`next`) gives `RInv` at round `j + 1`, with the ghosts extended by the chords cut in this round
(`gcNext`, `crNext`).
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

/-- The ghost components after a round. -/
noncomputable def gcNext (R K : ℕ) (prg pch chOf top best : ℕ → ℕ) (σ : RS) (gc : ℕ → Finset ℕ)
    (e : ℕ) : Finset ℕ :=
  if e < K ∧ Chosen σ top best chOf e then sub R prg pch σ.rem ztwoz else gc e

/-- The ghost cut rounds after round `j`. -/
def crNext (K : ℕ) (chOf top best : ℕ → ℕ) (σ : RS) (j : ℕ) (cr : ℕ → ℕ) (e : ℕ) : ℕ :=
  if e < K ∧ Chosen σ top best chOf e then j else cr e

/-- The arithmetic of a cut: both parts shrink by the factor `(D - 1) / D`. -/
theorem split_bound {D a b : ℕ} (hD : 1 ≤ D) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : a + b - 1 ≤ D * min a b) :
    D * (a - 1) ≤ ztdsz * ztqdk ∧ D * zteow ≤ ztdsz * ztqdk := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by_omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by_omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by_omega⟩
  simp only [Nat.add_sub_cancel] at hm ⊢
  have e1 : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by_omega
  zvmxy at hm ⊢
  rcases le_total a' b' with hab | hab
  · rw [min_eq_left by_omega] at hm
    constructor
    · zujcv
      · omega
      · nlinarith
    grind
  · rw [min_eq_right by_omega] at hm
    constructor
    · nlinarith
    · zujcv
      · omega
      · nlinarith

section step2

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable {σ : RS} {top best bestv : ℕ → ℕ}
variable (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u)
variable (hB : ∀ t, t < R → IsTop pch σ.rem t →
      ztpm ∧
      (ztvl ∨
        (best t < R ∧ AncX R prg pch σ.rem t ztmy ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t ztmy)))
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)

include h hch hT hB hI

local notation "σ'" => next R K prg pch isdn chOf top best σ
local notation "gc'" => gcNext R K prg pch chOf top best σ gc
local notation "cr'" => crNext K chOf top best σ j cr

theorem mem_sideSet {s e v : ℕ} :
    v ∈ sideSet R prg pch isdn chOf s e ↔ v < R ∧ OnSide R prg pch isdn chOf s e v := by
  zuldv

variable {e : ℕ} {t : ℕ}
theorem gc_old (hr : σ.rem e = 1) : gc' e = gc e := by
  unfold gcNext
  simp_all

theorem cr_old (hr : σ.rem e = 1) : cr' e = cr e := by
  unfold crNext
  simp_all

theorem gc_new (he : e < K) (hc : Chosen σ top best chOf e) :
    gc' e = sub R prg pch σ.rem ztwoz := by
  unfold gcNext
  simp_all

theorem cr_new (he : e < K) (hc : Chosen σ top best chOf e) : cr' e = j := by
  unfold crNext
  simp_all

/-- After the first round the root code does not change. -/
theorem root_next_pos (hj : 1 ≤ j) : (σ').root = σ.root := by
  simp only [next]
  by_cases ha : σ.act 0 = 1
  · zuhme
    rcases hI.i4 0 h.R_pos ztp ha with ⟨-, -, hj0⟩ | ⟨hs, -⟩
    · omega
    grind
  simp_all

/-- The new state at an old top. -/
theorem act_top (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').act t = (if σ.act t = 1 then (if best t = t then 0 else σ.act t) else σ.act t) := by
  zubit

theorem cpar_top (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').cpar t = (if σ.act t = 1 then (if best t = t then σ.cpar t else pch ztmy) else σ.cpar t) := by
  zubit

theorem side_top (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').side t = (if σ.act t = 1 then (if best t = t then σ.side t else
      ztyfe) else σ.side t) := by
  zubit

theorem lpar_top (ht : t < R) (htop : IsTop pch σ.rem t) :
    (σ').lpar t = (if σ.act t = 1 then (if best t = t then
      ztgrs else σ.lpar t) else σ.lpar t) := by
  zubit

/-- The new state at the child endpoint of a chosen chord. -/
theorem new_top_facts (he : e < K) (hc : Chosen σ top best chOf e) :
    (σ').act ztjk = 1 ∧ (σ').cpar ztjk = e ∧
      (σ').side ztjk = (if isdn ztjk = 1 then 0 else 1) := by
  obtain ⟨-, -, -, -, -, hnt, -, c1, -, c3, -⟩ := chosen_facts h hch hT hB hI he hc
  have hnt' : top ztjk ≠ chOf e := fun e' => hnt ((top_iff h hch hT hB hI c1).1 e')
  have hp : nPend K chOf top best σ e = 1 := (pend_next h hch hT hB hI he).2 hc
  refine ztcg <;> simp only [next, ite_eq_left c1, ite_eq_right hnt', c3, ite_eq_left hp]

/-- An old top that is not active stays as it is. -/
theorem valid_next {x : ℕ} (hx : ValidC R K pch σ x) :
    ValidC R K pch (σ') x ∧ compOf gc' x = compOf gc x ∧ pcode (σ') x = pcode σ x := by
  rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · have hnc : ¬ Chosen σ top best chOf ztbhd := fun hh => hh.1 h3
    refine ⟨Or.inl ⟨h1, h2, rem_mono h hch hT hB hI h3⟩, ?_, ?_⟩
    · simp only [compOf, ite_eq_left h1, gc_old h hch hT hB hI h3]
    · simp only [pcode, ite_eq_left h1, next, ite_eq_left h2, ite_eq_right hnc]
      simp
  · have hx2 : ztmxc := by_omega
    refine ⟨Or.inr ⟨h1, h2, (istop_next h hch hT hB hI h2).2 (Or.inl h3), ?_⟩, ?_, ?_⟩
    · rw [act_top h hch hT hB hI h2 h3, ite_eq_right h4]; exact h4
    · simp only [compOf, ite_eq_right hx2]
    · simp only [pcode, ite_eq_right hx2]
      rw [lpar_top h hch hT hB hI h2 h3, ite_eq_right h4]

/-- The code of an active component after the round. -/
theorem code_next (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1) :
    ValidC R K pch (σ') ztlmd ∧ compOf gc' ztlmd = sub R prg pch σ.rem t ∧
      pcode (σ') ztlmd =
        (if σ.side t = 2 then code best pch t else 2 * σ.cpar t) := by
  by_cases hbt : best t = t
  · have hcode : code best pch t = 2 * t + 1 := by unfold code; simp_all
    zumnb
    have hm : ztbxv % 2 = 1 := by_omega
    have hd : ztbxv / 2 = t := by_omega
    have hsing : ztlyv := by
      zuepb
      zujkt

      · rintro ⟨hv, htv⟩
        rcases (hB t ht htop).2 with ⟨-, b2⟩ | ⟨-, -, b3, -⟩
        · tauto
        omega
      · zudsz
    have v1 : ztbxv / 2 < R := by_omega
    have v2 : IsTop pch (σ').rem ztzyw := by
      zvnej; exact (istop_next h hch hT hB hI ht).2 ztqbe
    have v3 : (σ').act ztzyw ≠ 1 := by
      rw [hd, act_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]; norm_num
    refine ⟨Or.inr ⟨hm, v1, v2, v3⟩, ?_, ?_⟩
    · simp only [compOf, hm, hd, hsing]; rfl
    · simp only [pcode, hm, hd, lpar_top h hch hT hB hI ht htop, ite_eq_left hact, ite_eq_left hbt]
      norm_num
  · zubkv
    have hcode : code best pch t = 2 * pch ztmy := by unfold code; simp_all
    zumnb
    have hm : ztxms % 2 = 0 := by_omega
    have hd : ztxms / 2 = pch ztmy := by_omega
    have v1 : ztxms / 2 < K := by_omega
    have v2 : (σ').rem (ztxms / 2) = 1 := by
      zvnej; exact (rem_next h hch hT hB hI b4).2 (Or.inr b7)
    refine ⟨Or.inl ⟨hm, v1, v2⟩, ?_, ?_⟩
    · simp only [compOf, hm, hd, gc_new h hch hT hB hI b4 b7, b5, b6]; rfl
    · have hp : σ.pend ztyjw ≠ 1 := fun hp => b8 (hI.i0 _ b4 hp)
      simp only [pcode, hm, hd, next, ite_eq_left b4, ite_eq_right hp, ite_eq_left b7, b5, b6]
      rfl

/-- The pending chord's child tops, as the chord pass computes them. -/
theorem pend_child {e s t : ℕ} (he : e < K) (hp : σ.pend e = 1) (_ht : t < R)
    (htop : IsTop pch σ.rem t)
    (hsub : sub R prg pch σ.rem t = gc e ∩ sideSet R prg pch isdn chOf s e) :
    (if ztwpe then chOf e else top ztxom) = t := by
  zuizd
  obtain ⟨-, hcm, hpm, -⟩ := hI.i1 e he hr
  zucdr
  have hctop : IsTop pch σ.rem ztjk := Or.inr by_simp_all
  have hpR : prg ztjk < R := h.prg_lt _ c1 c2
  zulwb
  · rw [ite_eq_left hcond]
    have hmem : ztmuv := by
      zueyj
      exact ⟨hcm, c1, ⟨fun _ => hcond, fun _ => ReflTransGen.refl⟩⟩
    zukxq
    zuct
    exact AncX.not_top hmem.2 ztnr hctop
  · rw [ite_eq_right hcond]
    have hmem : prg ztjk ∈ sub R prg pch σ.rem t := by
      zueyj
      refine ⟨hpm, hpR, ⟨fun hh => absurd ?_ hcond, fun hh => absurd hh hcond⟩⟩
      have h1 := (AncX.pos_le h hh hpR).2.1
      have h2 := h.pos_prg _ c1 c2
      omega
    zukxq
    exact top_of h hch hT hB hI hpR htop hmem.2

theorem loTop_eq (e : ℕ) : loTop prg isdn chOf top e =
    (if (isdn ztjk = 1 ↔ (0 : ℕ) = 0) then chOf e else top ztxom) := by
  unfold loTop
  simp

theorem hiTop_eq (e : ℕ) : hiTop prg isdn chOf top e =
    (if (isdn ztjk = 1 ↔ (1 : ℕ) = 0) then chOf e else top ztxom) := by
  unfold hiTop
  simp

open Classical in
/-- The two sides of a chosen chord after the round. -/
theorem sub_new_sides {e s : ℕ} (he : e < K) (hc : Chosen σ top best chOf e) :
    (ztwpe →
      sub R prg pch (σ').rem ztjk = gc' e ∩ sideSet R prg pch isdn chOf s e) ∧
    (¬ ztwpe →
      sub R prg pch (σ').rem ztwoz = gc' e ∩ sideSet R prg pch isdn chOf s e) := by
  obtain ⟨t1, t2, t3, t4, t5, -, t7, c1, -, -, -⟩ := chosen_facts h hch hT hB hI he hc
  zukbg
  rw [gc_new h hch hT hB hI he hc]
  constructor
  · intro hcond
    have := sub_cut_c h hch hT hB hI t1 t2 t3 hbt
    zukys
    rw [this, sub_member h hch hT hB hI t7]
    zuclk

  · intro hcond
    have := sub_cut_t h hch hT hB hI t1 t2 t3 hbt
    zukys
    zubk
    zuclk

end step2

end

end Chazelle.Core.Dec
