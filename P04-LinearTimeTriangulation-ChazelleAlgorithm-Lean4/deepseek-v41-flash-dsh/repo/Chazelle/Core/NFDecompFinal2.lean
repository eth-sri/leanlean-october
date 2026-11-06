module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompFinal

/-!
# Tree decomposition (WP-C), part 9: the decomposition is valid

`isDecomp_final`: when the rounds stop (no active component), the arrays of the state, attached
to the normal form (`withDec`), form a valid tree decomposition of depth `decDepth D K`.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

set_option linter.unusedSectionVars false

section final2

variable {R K D : ℕ} {ord pos prg pch isdn chOf : ℕ → ℕ}
variable {N : NF} (hK : N.nChords = K) (hRR : N.nRegions = R)
variable (h : Rooted R K (fun i => (N.chord i).up) (fun i => (N.chord i).dn) ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable (hisdn : ∀ s, s < R → s ≠ 0 → (isdn s = 1 ↔ (N.chord (pch s)).dn = s))
variable {j : ℕ} {σ : RS} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)
variable (hna : ∀ t, t < R → IsTop pch σ.rem t → σ.act t ≠ 1)
include hK hRR h hch hisdn hI hna

local notation "N'" => withDec N K R σ

theorem mem_sideSet' {s e v : ℕ} :
    v ∈ sideSet R prg pch isdn chOf s e ↔ v < R ∧ OnSide R prg pch isdn chOf s e v := by
  classical
  Θ sideSet

/-- The two endpoints of a cut chord are on different sides. -/
theorem other_side {k s : ℕ} (hk : k < K) :
    ∃ w, w ∈ gc k ∧ w ∉ sideSet R prg pch isdn chOf s k := by
  obtain ⟨hr, -⟩ := final_cut hK hRR h hch hisdn hI hna hk
  obtain ⟨-, hcm, hpm, -⟩ := hI.i1 k hk hr
  obtain ⟨c1, c2, -⟩ := hch k hk
  have hpR := h.prg_lt _ c1 c2
  have hnp : ¬ AncX R prg pch rem0 (chOf k) (prg (chOf k)) := fun hh => by
    have := (AncX.pos_le h hh hpR).2.1
    have := h.pos_prg _ c1 c2
    omega
  by_cases hcond : (isdn (chOf k) = 1 ↔ s = 0)
  · refine ⟨prg (chOf k), hpm, fun hh => ?_⟩
    Ξ' mem_sideSet' hK hRR h hch hisdn hI hna at hh
    exact hnp (hh.2.2 hcond)
  · refine ⟨chOf k, hcm, fun hh => ?_⟩
    Ξ' mem_sideSet' hK hRR h hch hisdn hI hna at hh
    exact hcond (hh.2.1 ReflTransGen.refl)

/-- **Below a placed code** are exactly the regions of its component. -/
theorem below_iff {r x : ℕ} (hr : r < R) (hx : ValidC R K pch σ x) :
    (∃ i, (N').parentCode^[i] (2 * r + 1) = x) ↔ r ∈ compOf gc x := by
  constructor
  · rintro ⟨i, rfl⟩
    exact (chain_mem hK hRR h hch hisdn hI hna hr i).2
  · intro hrx
    have key : ∀ n, ∀ x, (compOf gc x).card ≤ n → ValidC R K pch σ x → r ∈ compOf gc x →
        ∃ i, (N').parentCode^[i] (2 * r + 1) = x := by
      intro n
      induction n with
      | zero =>
        intro x hc _ hm
        have := Finset.card_pos.2 ⟨r, hm⟩
        omega
      | succ n ih =>
        intro x hc hv hm
        rcases valid_range hK hRR h hch hisdn hI hna hv with ⟨a, b⟩ | ⟨a, b⟩
        · -- a chord node: descend to the child on the side of `r`
          set k := x / 2 with hkdef
          have hxk : x = 2 * k := ⋄
          have hmk : r ∈ gc k := by simpa [compOf, a] using hm
          obtain ⟨s, hs, hrs⟩ : ∃ s, s ≤ 1 ∧ r ∈ sideSet R prg pch isdn chOf s k := by
            by_cases hc0 : OnSide R prg pch isdn chOf 0 k r
            · exact ⟨0, ⊛, (mem_sideSet' hK hRR h hch hisdn hI hna).2 ⟨hr, hc0⟩⟩
            · refine ⟨1, le_rfl, (mem_sideSet' hK hRR h hch hisdn hI hna).2 ⟨hr, ?_⟩⟩
              unfold OnSide at hc0 ⊢
              ϴ' one_ne_zero, iff_false, iff_true at hc0 ⊢
              tauto
          obtain ⟨v1, v2, v3⟩ := slot_facts hK hRR h hch hisdn hI hna b hs
          obtain ⟨w, hw1, hw2⟩ := other_side hK hRR h hch hisdn hI hna (s := s) b
          have hlt : (compOf gc (if s = 0 then σ.dlo k else σ.dhi k)).card < (compOf gc x).card := by
            Ξ v2
            have hck : compOf gc x = gc k := by simp only [compOf, ite_eq_left a]; rfl
            Ξ hck
            apply Finset.card_lt_card
            refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, fun e => ?_⟩
            have : w ∈ gc k ∩ sideSet R prg pch isdn chOf s k := by rw [e]; exact hw1
            exact hw2 (Finset.mem_inter.1 this).2
          obtain ⟨i, hi⟩ := ih _ (⋄) v1 (by rw [v2]; exact Finset.mem_inter.2 ⟨hmk, hrs⟩)
          refine ⟨i + 1, ?_⟩
          Ξ Function.iterate_succ_apply', hi, parentCode_eq hK hRR h hch hisdn hI hna v1, v3, hxk
        · have hmx : r = x / 2 := by simpa [compOf, show x % 2 ≠ 0 by omega] using hm
          exact ⟨0, by simp only [Function.iterate_zero, id]; omega⟩
    exact key _ _ le_rfl hx hrx

/-- Out of range leaves go straight to the root. -/
theorem chain_out {r : ℕ} (hr : R ≤ r) (i : ℕ) (hi : 1 ≤ i) :
    (N').parentCode^[i] (2 * r + 1) = σ.root := by
  have hj := final_j hK hRR h hch hisdn hI hna
  obtain ⟨o1, -, o3⟩ := hI.i8 hj
  have hroot : (N').parentCode σ.root = σ.root := by
    Ξ parentCode_eq hK hRR h hch hisdn hI hna o1, o3
  induction i with
  | zero => omega
  | succ i ih =>
    Ξ Function.iterate_succ_apply'
    rcases Nat.eq_zero_or_pos i with rfl | hi'
    · ϴ Function.iterate_zero, id
      unfold NF.parentCode
      rw [ite_eq_right (⋄), show (2 * r + 1) / 2 = r by omega,
        withDec_lpar_out hK hRR h hch hisdn hI hna hr]
    · Ξ ih hi', hroot

/-- The regions of the low (high) side of a chord in the normal form. -/
theorem side_iff {k r : ℕ} (hk : k < K) (s : ℕ) (_hs : s ≤ 1) :
    ReflTransGen ((N').AdjAvoid k) (if s = 0 then ((N').chord k).dn else ((N').chord k).up) r ↔
      r ∈ sideSet R prg pch isdn chOf s k := by
  obtain ⟨c1, c2, c3⟩ := hch k hk
  have hadj : (N').AdjAvoid k = AdjAv K (fun i => (N.chord i).up) (fun i => (N.chord i).dn) k := by
    funext a b
    ϴ' NF.AdjAvoid, AdjAv, withDec, NF.nChords, NF.chord at hK ⊢
    Ξ hK
  have hchord : (N').chord k = N.chord k := rfl
  Ξ hadj, hchord, mem_sideSet' hK hRR h hch hisdn hI hna
  have hends := h.ends _ c1 c2
  Ξ' c3 at hends
  have hdn := hisdn _ c1 c2
  Ξ' c3 at hdn
  have hpR := h.prg_lt _ c1 c2
  have hnp : ¬ AncX R prg pch rem0 (chOf k) (prg (chOf k)) := fun hh => by
    have := (AncX.pos_le h hh hpR).2.1
    have := h.pos_prg _ c1 c2
    omega
  have hpc : prg (chOf k) ≠ chOf k := fun e => hnp (by rw [e]; exact ReflTransGen.refl)
  have hstart : (if s = 0 then (N.chord k).dn else (N.chord k).up) < R := by
    rcases hends with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> split_ifs <;> simp_all
  Ξ rtg_adjAv_iff h hch hk hstart
  unfold OnSide
  apply and_congr_right
  intro _
  apply iff_congr Iff.rfl
  -- the starting endpoint is in the subtree iff it is the child endpoint
  rcases hends with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · have hd : isdn (chOf k) = 1 := hdn.2 a2
    by_cases hs0 : s = 0
    · Ξ ite_eq_left hs0, a2
      exact ⟨fun _ => ⟨fun _ => hs0, fun _ => hd⟩, fun _ => ReflTransGen.refl⟩
    · Ξ ite_eq_right hs0, a1
      exact ⟨fun hh => absurd hh hnp, fun hh => absurd (hh.1 hd) hs0⟩
  · have hd : isdn (chOf k) ≠ 1 := fun hh => hpc ((hdn.1 hh).symm.trans a2).symm
    by_cases hs0 : s = 0
    · Ξ ite_eq_left hs0, a2
      exact ⟨fun hh => absurd hh hnp, fun hh => absurd (hh.2 hs0) hd⟩
    · Ξ ite_eq_right hs0, a1
      exact ⟨fun _ => ⟨fun hh => absurd hh hd, fun hh => absurd hh hs0⟩, fun _ => ReflTransGen.refl⟩

/-- The chain from a removed chord reaches the root in `cr e` steps. -/
theorem chord_reach {e : ℕ} (he : e < K) :
    (N').parentCode^[cr e] (2 * e) = σ.root := by
  induction hn : cr e using Nat.strong_induction_on generalizing e with
  | _ n ih =>
    obtain ⟨hr, -⟩ := final_cut hK hRR h hch hisdn hI hna he
    obtain ⟨-, -, -, -, -, h6⟩ := hI.i1 e he hr
    have hv : ValidC R K pch σ (2 * e) :=
      Or.inl ⟨⋄, by rw [show 2 * e / 2 = e by omega]; exact he, by
        rw [show 2 * e / 2 = e by omega]; exact hr⟩
    rcases h6 with ⟨-, a2, a3, -⟩ | ⟨p, hp, -, a1, a2, -⟩
    · rw [← hn, a2, a3]; rfl
    · Ξ ← hn, ← a2, Function.iterate_succ_apply, parentCode_eq hK hRR h hch hisdn hI hna hv
      have : pcode σ (2 * e) = 2 * p := by
        unfold pcode; Ξ ite_eq_left (⋄), show 2 * e / 2 = e by omega, a1
      Ξ this
      exact ih (cr p) (⋄) hp rfl

/-- **The final decomposition is valid**, of depth `decDepth D K`. -/
theorem isDecomp_final (hD : K = 0 ∨ 1 ≤ D) : IsDecomp (N') (decDepth D K) := by
  have hj := final_j hK hRR h hch hisdn hI hna
  obtain ⟨o1, o2, o3⟩ := hI.i8 hj
  have hnc : (N').nChords = K := by simp only [NF.nChords, withDec] at hK ⊢; exact hK
  have hnr : (N').nRegions = R := by simp only [NF.nRegions, withDec] at hRR ⊢; exact hRR
  have hrounds : rounds D K ≤ D * Nat.clog 2 (K + 1) := by
    rcases hD with h0 | h1
    · rw [h0, rounds_zero]; exact Nat.zero_le _
    · exact rounds_le h1 K
  -- the children of a chord node
  have hlohi : ∀ k, k < K → (N').dnode k = ⟨σ.dpar k, σ.dlo k, σ.dhi k⟩ :=
    fun k hk => withDec_dnode hK hRR h hch hisdn hI hna hk
  -- `Below` for a placed code other than the root
  have hbelow : ∀ x r, ValidC R K pch σ x → x ≠ σ.root →
      ((N').Below x r ↔ r < R ∧ r ∈ compOf gc x) := by
    intro x r hx hxr
    unfold NF.Below
    by_cases hr : r < R
    · rw [below_iff hK hRR h hch hisdn hI hna hr hx]; exact ⟨fun hh => ⟨hr, hh⟩, fun hh => hh.2⟩
    · rw [not_lt] at hr
      refine ⟨fun ⟨i, hi⟩ => ?_, fun hh => absurd hh.1 (by omega)⟩
      exfalso
      rcases Nat.eq_zero_or_pos i with rfl | hi'
      · simp only [Function.iterate_zero, id] at hi
        rcases valid_range hK hRR h hch hisdn hI hna hx with ⟨a, _⟩ | ⟨_, b⟩
        · omega
        · omega
      · rw [chain_out hK hRR h hch hisdn hI hna hr i hi'] at hi
        exact hxr hi.symm
  -- the slots of a chord are not the root
  have hsne : ∀ k, k < K → ∀ s, s ≤ 1 → (if s = 0 then σ.dlo k else σ.dhi k) ≠ σ.root := by
    intro k hk s hs e
    obtain ⟨-, v2, -⟩ := slot_facts hK hRR h hch hisdn hI hna hk hs
    obtain ⟨w, hw1, hw2⟩ := other_side hK hRR h hch hisdn hI hna (s := s) hk
    obtain ⟨hr, -⟩ := final_cut hK hRR h hch hisdn hI hna hk
    obtain ⟨g1, -⟩ := hI.i1 k hk hr
    have hw : w ∈ compOf gc σ.root := by rw [o2]; exact g1 hw1
    rw [← e, v2] at hw
    exact hw2 (Finset.mem_inter.1 hw).2
  -- the slots of a chord
  have hslot : ∀ k, k < K → ∀ s, s ≤ 1 → ∀ r,
      (N').Below (2 * k) r → ((N').Below (if s = 0 then σ.dlo k else σ.dhi k) r ↔
        ReflTransGen ((N').AdjAvoid k) (if s = 0 then ((N').chord k).dn else ((N').chord k).up) r) := by
    intro k hk s hs r hkr
    obtain ⟨v1, v2, v3⟩ := slot_facts hK hRR h hch hisdn hI hna hk hs
    have hne := hsne k hk s hs
    rw [hbelow _ r v1 hne, v2, side_iff hK hRR h hch hisdn hI hna hk s hs]
    by_cases hr : r < R
    · have hv2k : ValidC R K pch σ (2 * k) :=
        valid_of_range hK hRR h hch hisdn hI hna (Or.inl ⟨by omega, by omega⟩)
      have hmk : r ∈ gc k := by
        have := (below_iff hK hRR h hch hisdn hI hna hr hv2k).1 hkr
        simpa [compOf, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega] using this
      rw [Finset.mem_inter]
      exact ⟨fun hh => hh.2.2, fun hh => ⟨hr, hmk, hh⟩⟩
    · refine ⟨fun hh => absurd hh.1 hr, fun hh => ?_⟩
      rw [mem_sideSet' hK hRR h hch hisdn hI hna] at hh
      exact absurd hh.1 hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [withDec, NF.nChords, List.length_map, List.length_range] at hK ⊢
    exact hK.symm
  · simp only [withDec, NF.nRegions, List.length_map, List.length_range] at hRR ⊢
    exact hRR.symm
  · intro k hk
    rw [hnc] at hk
    rw [hlohi k hk]
    obtain ⟨v1, -, v3⟩ := slot_facts hK hRR h hch hisdn hI hna hk (s := 0) (by norm_num)
    obtain ⟨w1, -, w3⟩ := slot_facts hK hRR h hch hisdn hI hna hk (s := 1) (by norm_num)
    simp only [ite_true, one_ne_zero, ite_false] at v1 v3 w1 w3
    exact ⟨by rw [parentCode_eq hK hRR h hch hisdn hI hna v1, v3],
      by rw [parentCode_eq hK hRR h hch hisdn hI hna w1, w3]⟩
  · intro k hk r hkr
    rw [hnc] at hk
    rw [hlohi k hk]
    have := hslot k hk 0 (by norm_num) r hkr
    simp only [ite_true] at this
    exact this
  · intro k hk r hkr
    rw [hnc] at hk
    rw [hlohi k hk]
    have := hslot k hk 1 le_rfl r hkr
    simp only [one_ne_zero, ite_false] at this
    exact this
  · intro r hr
    rw [hnr] at hr
    unfold NF.Below
    show ∃ i, (N').parentCode^[i] (2 * r + 1) = σ.root
    rw [below_iff hK hRR h hch hisdn hI hna hr o1, o2]
    exact Finset.mem_range.2 hr
  · intro x hx
    rw [hnc] at hx
    show ∃ i, i ≤ decDepth D K ∧ (N').parentCode^[i] x = σ.root
    unfold decDepth
    rcases Nat.even_or_odd x with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm2 : x % 2 = 0 := by omega
      have hmK := hx hm2
      rw [show x / 2 = m by omega] at hmK
      obtain ⟨hr, -⟩ := final_cut hK hRR h hch hisdn hI hna hmK
      obtain ⟨-, -, -, -, h5, -⟩ := hI.i1 m hmK hr
      refine ⟨cr m, by omega, ?_⟩
      rw [show x = 2 * m by omega]
      exact chord_reach hK hRR h hch hisdn hI hna hmK
    · by_cases hmR : m < R
      · have hv : ValidC R K pch σ x :=
          valid_of_range hK hRR h hch hisdn hI hna (Or.inr ⟨by omega, by omega⟩)
        have htop : IsTop pch σ.rem m := by
          rcases hv with ⟨a, -⟩ | ⟨-, -, c, -⟩
          · omega
          · rwa [show x / 2 = m by omega] at c
        obtain ⟨-, l2⟩ := hI.i5 m hmR htop (hna m hmR htop)
        rcases l2 with ⟨a1, a2, -⟩ | ⟨p, hp, hrp, a1, a2, -⟩
        · exact ⟨0, by omega, by rw [hm, a2]; rfl⟩
        · refine ⟨cr p + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, parentCode_eq hK hRR h hch hisdn hI hna hv]
          have : pcode σ x = 2 * p := by
            unfold pcode; rw [ite_eq_right (by omega), show x / 2 = m by omega, a1]
          rw [this]
          exact chord_reach hK hRR h hch hisdn hI hna hp
      · rw [not_lt] at hmR
        refine ⟨1, by omega, ?_⟩
        rw [hm]
        exact chain_out hK hRR h hch hisdn hI hna hmR 1 le_rfl
  · -- only its own region is below a leaf
    intro r r' hr hr' hb
    rw [hnr] at hr hr'
    have hv : ValidC R K pch σ (2 * r + 1) :=
      valid_of_range hK hRR h hch hisdn hI hna (Or.inr ⟨by omega, by omega⟩)
    have := (below_iff hK hRR h hch hisdn hI hna hr' hv).1 hb
    simpa [compOf, show (2 * r + 1) % 2 ≠ 0 by omega, show (2 * r + 1) / 2 = r by omega] using this
  · -- the children of a chord node are valid codes other than the root
    intro k hk x hx
    rw [hnc] at hk
    rw [hnc, hnr]
    rw [hlohi k hk] at hx
    have key : ∀ s, s ≤ 1 → x = (if s = 0 then σ.dlo k else σ.dhi k) →
        x ≠ σ.root ∧ ((x % 2 = 0 ∧ x / 2 < K) ∨ (x % 2 = 1 ∧ x / 2 < R)) := by
      intro s hs e
      obtain ⟨v1, -, -⟩ := slot_facts hK hRR h hch hisdn hI hna hk hs
      rw [e]
      exact ⟨hsne k hk s hs, valid_range hK hRR h hch hisdn hI hna v1⟩
    rcases hx with e | e
    · exact key 0 (by norm_num) (by simpa using e)
    · exact key 1 le_rfl (by simpa using e)
  · -- the root is a valid code
    rw [hnc, hnr]
    exact valid_range hK hRR h hch hisdn hI hna o1

end final2

end

end Chazelle.Core.Dec
