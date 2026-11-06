module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvGenR
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.FuseAsmMain
public import Chazelle.Core.SweepIoGather
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.OracleBook

namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
@[expose] public section
structure SCtx (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF) (c cw cs co c' : Config) (A : Set zte)
    (rs ax : List ztcf) : Prop where
  E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂
  L : LoopInv P J N₁ N₂ c₀ c
  hI : IterRel P J N₁ N₂ c cw cs co c'
  hd : c'.nreg dF = 0
  hBA : BatchA P J N₂ cs
    ztwro
    zthib co A
  hval : ∀ t ∈ A, ValidJ J zta N₂ t.1
  hD : StopData P J N₂ c rs ax
namespace SCtx
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set zte} {rs ax : List ztcf}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- The parameter of the next key. -/
theorem posK : c'.nreg kE < (chainModel J.whole).W.n ∧
    0 ≤ (chainModel J.whole).param zta ztbnz ∧
    (chainModel J.whole).param zta ztbnz < 1 :=
  let h := (stp_next_key S.E S.L S.hI S.hd).2.1
  ⟨h.1, h.2.1.1, h.2.1.2.1⟩

/-- No cut strictly between the key and the next key. -/
theorem gapK : ∀ e ∈ F₂plus J ztwis, ∀ (q : ℕ) (s : ℝ),
    SideAttach (chainModel J.whole).W e q s →
      ¬ (keyOff P J c < oW J ztej ∧ oW J ztej < keyOff P J c') := by
  intro e he q s hA
  exact no_cut_iter S.E S.L S.hI ztej ⟨e, he, q, s, hA, rfl⟩ (by have := hA.2.1; positivity)
    (by have := hA.2.2.1; have : ((q : ℕ) : ℝ) + 1 ≤ (chainModel J.whole).W.n := by
          exact_mod_cast hA.1
        linarith)

/-- A position at the offset of the next key is the next key. -/
theorem posEq {q : ℕ} {s : ℝ} (hq : q < (chainModel J.whole).W.n) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (h : oW J ztej = keyOff P J c') :
    q = c'.nreg kE ∧ s = (chainModel J.whole).param zta ztbnz := by
  obtain ⟨h1, h2, h3⟩ := S.posK
  exact pos_eq_of_oW S.E.hP S.E.hNF₂.1.2.1 S.E.hNF₂.1.1 hq h1 hs0 hs1 h2 h3 h
variable {i : ℕ} {e : Set Point}
/-- The stop offsets read from the records. -/
theorem stopOff_rs (hi : i < rs.length) :
    stopOff P J c i = soff P J rs[i] := by
  obtain ⟨-, -, hrec, -⟩ := S.hD
  zutg

  show offK P J (c.nmem ztpaa) (c.nmem ztmhc) = _
  zucpp
  rfl

/-- **A skipped stop is attached at the next key.** -/
theorem skip_at (h1 : c.nreg sP ≤ i) (h2 : i < c'.nreg sP) :
    ∃ hi : i < rs.length,
      stopSet J zta N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 ∈
        F₂plus J ztwis ∧
      StopChord2 J ztwis
        ztwqu ∧
      SideAttach (chainModel J.whole).W
        ztwqu ztccp
        ztwyy ∧
      rs[i].1 = c'.nreg kE ∧ (chainModel J.whole).param zta ztcyg =
        (chainModel J.whole).param zta ztbnz := by
  obtain ⟨-, hle, -, hk3⟩ := stp_ptr_c' S.E S.L S.hI S.hd
  zuddu
  have hlen := S.hD.1
  zukcm
  refine ztfwp
  obtain ⟨f0, f1, a0, -⟩ := stop_facts S.hD.2.2.2.2.1 hi
  have ho := hk3 i h1 h2
  rw [S.stopOff_rs hi] at ho
  obtain ⟨e1, e2⟩ := S.posEq a0.1 a0.2.1 a0.2.2.1 ho
  simp_all

/-- **A stop chord at the next key is a skipped stop.** -/
theorem stop_idx (he : e ∈ F₂plus J ztwis)
    (hA : SideAttach (chainModel J.whole).W e ztccp
      ztwyy)
    (hs : StopChord2 J ztwis e) :
    ∃ i, ∃ hi : i < rs.length, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
      stopSet J zta N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = e := by
  zueir
  obtain ⟨hlen, -, -, -, hok, -⟩ := S.hD
  have hL : (Lst J : ℝ) ≤ oW J (c'.nreg kE +
      (chainModel J.whole).param zta ztbnz) := by
    have := S.L.keyL
    show (Lst J : ℝ) ≤ keyOff P J c'
    linarith
  have hmem := hok.2.1 e he hs _ _ hA hL
  zucod
  zuep
  zudlk

  have ho : stopOff P J c i = keyOff P J c' := by
    rw [S.stopOff_rs hi]
    unfold soff
    rw [h2, h1]
    rfl
  have hic : ztizv := hlen ▸ hi
  obtain ⟨-, -, hptr, -⟩ := stp_ptr_c' S.E S.L S.hI S.hd
  zuddu
  have hso := (stp_stops_c' S.E S.L S.hI S.hd).2 i hic
  refine ⟨i, hi, ?_, ?_, h3⟩
  · zumv
    have := (S.L.ptrL i hic).1 by_omega
    linarith
  simp_all

/-- **A non-stop chord at the next key** is the chord of an accepted triple at its offset, and
the best candidate is there. -/
theorem nonstop_acc (he : e ∈ F₂plus J ztwis)
    (hA : SideAttach (chainModel J.whole).W e ztccp
      ztwyy)
    (hs : ¬ StopChord2 J ztwis e) :
    ∃ t ∈ A, offT P J t = keyOff P J c' ∧
      Merge.shoot J.whole ztwnl ztdzu = e ∧
      co.nreg bF = 1 ∧ offK P J ztmhl ztmhm = keyOff P J c' := by
  zueir
  obtain ⟨-, -, -, ewX, ewE, ewH⟩ := iter_stops S.L S.hI
  zudpg
  obtain ⟨hW, -, hR, -, hK⟩ := S.hI
  zubrq
  zudmy

  obtain ⟨-, -, hKb, -, hKw, -⟩ := hK.2.2.2 hsome
  obtain ⟨k, hk, a, σ, ha, haR, hav, hat, hfree, rfl, hlt', j, hj, hjk, hjO, hjD, h, hh, hmA⟩ :=
    stp_accepted_of_found S.E S.L hW hR S.hBA he hA hlt S.gapK hs (fun h0 => by
      have := hKw by_omega
      rw [ewE, ewH] at this
      tauto)
  have hoT : offT P J (j, c'.nreg kE, h) = keyOff P J c' := by
    show oW J (_ + (chainModel J.whole).param zta ⟨_, h⟩) = _
    zumnh
    rfl
  obtain ⟨hbF, hle⟩ := S.hBA.bMin _ hmA ztjqd
  have hge := hKb hbF
  exact ⟨_, hmA, hoT, by_simp_all, hbF, le_antisymm (hle.trans hoT.le) hge⟩

/-- **The chord of an accepted triple at the offset of the next key** is attached there, is not
a stop chord and is anchored. -/
theorem triple_at {t : ℕ × ℕ × ℕ} (ht : t ∈ A) (hto : offT P J t = keyOff P J c') :
    Merge.shoot J.whole ztwnl ztdzu ∈
        F₂plus J ztwis ∧
      SideAttach (chainModel J.whole).W
        ztbamt ztccp
        ztwyy ∧
      ¬ StopChord2 J ztwis
        ztbamt ∧
      ¬ EvBrk J ztbamt := by
  zuglt
  obtain ⟨-, hj, hfree, hmemF, hAt, -, -, hpw, hlt'⟩ := S.hBA.acc t ht
  zucdx
  zucst
  zukak
  obtain ⟨e1, e2⟩ := S.posEq hpw.1 hpw.2.1.1 hpw.2.1.2.1 hto
  refine ⟨hmemF, by_simp_all,
    origin_not_stop hP hS₂a ztmkx ha haR hav hat hlt', fun hbr => ?_⟩
  zugb
  have haD : endOrigin J zta N₂ t.1 ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztmbj
  obtain ⟨q, s, hq, hqpt⟩ := endpoint_attach hM (F₂plus_subset J hS₂a hmemF) ztmmv haD
  have := off_right_pt J hP (S₂ := ∅) ztzi finite_empty hq.1 hq.2.1 hq.2.2.1
    by_simp_all by_simp_all
  zudbd
  have := hbr q s hq
  linarith
end SCtx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
theorem stp_addLs_sub : ∀ (vs l : List ℕ) {x : ℕ}, x ∈ addLs l vs → x ∈ l ∨ x ∈ vs := by
  intro vs
  induction vs using List.reverseRecOn with
  | nil => intro l x hx; exact Or.inl hx
  | append_singleton vs v ih =>
    intro l x hx
    rw [addLs_append'] at hx
    rcases mem_addL (l := addLs l vs) (v := v) hx with h | h
    · grind
    · simp_all

/-- **The labels of a stop record.** -/
theorem stp_mem_stopLabs {m : ℕ → ℕ} {A : ℕ} {ax : List ztcf}
    (hrec : AuxRecsAt m A ax) {i : ℕ} (hi : i < ax.length) {x : ℕ} :
    x ∈ stopLabs m A i ↔ ax[i].1 = 1 ∧
      ((0 < ax[i].2.1 ∧ x = ax[i].2.2.1) ∨ (1 < ax[i].2.1 ∧ x = ax[i].2.2.2.1)) := by
  obtain ⟨a0, a1, a2, a3, -⟩ := hrec i hi
  rw [List.getD_eq_getElem _ _ hi] at a0 a1 a2 a3
  zumvb
  rw [a0, a1]
  zus
  · simp only [List.mem_map, List.mem_range]
    constructor
    · grind
    · rintro ⟨-, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩
      · exact ztkij
      grind
  simp_all
theorem stp_stopLabs_len (m : ℕ → ℕ) (A i : ℕ) : (stopLabs m A i).length ≤ 2 := by
  unfold stopLabs; grind

/-- **At most two chords are attached at a position.** -/
theorem stp_two_chords {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (p : ℕ) (t : ℝ) :
    ∃ e₁ e₂ : Set Point, ∀ e ∈ F, SideAttach M.W e p t → e = e₁ ∨ e = e₂ := by
  classical
  by_cases h : ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ SideAttach M.W a p t ∧ SideAttach M.W b p t
  · obtain ⟨a, ha, b, hb, hab, hAa, hAb⟩ := h
    exact ⟨a, b, fun e he hA => tie_third hM hF ha hb he hab hAa hAb hA⟩
  · zubpo
    by_cases h' : ∃ a ∈ F, SideAttach M.W a p t
    · obtain ⟨a, ha, hAa⟩ := h'
      refine ⟨a, a, fun e he hA => Or.inl ?_⟩
      grind
    simp_all

/-- **The labels a chord at the next key contributes**: those of its accepted triples at the
offset of the next key, and those of its skipped stop. -/
def labsOf (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c co c' : Config)
    (A : Set zte) (rs : List ztcf) (e : Set Point) : Set ℕ :=
  {x | (∃ t ∈ A, offT P J t = keyOff P J c' ∧
      Merge.shoot J.whole ztwnl ztdzu = e ∧
      ztcxa) ∨
    (∃ i, ∃ hi : i < rs.length, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
      stopSet J zta N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = e ∧
      x ∈ stopLabs co.nmem ztghr i)}
namespace SCtx
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set zte} {rs ax : List ztcf}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- **A chord at the next key is the chord of at most one skipped stop.** -/
theorem stop_unique {i i' : ℕ} (hi : i < rs.length) (hi' : i' < rs.length)
    (h1 : c.nreg sP ≤ i) (h2 : i < c'.nreg sP) (h1' : c.nreg sP ≤ i') (h2' : i' < c'.nreg sP)
    (heq : stopSet J zta N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 =
      stopSet J zta N₂ rs[i'].2.2.1 rs[i'].2.2.2.1 rs[i'].2.2.2.2) : i = i' := by
  obtain ⟨hi₀, -, -, -, e1, e2⟩ := S.skip_at h1 h2
  obtain ⟨hi₀', -, -, -, e1', e2'⟩ := S.skip_at h1' h2'
  have hnd := S.hD.2.2.2.2.1.2.2.2
  zucwj
  exact (List.Nodup.getElem_inj_iff hnd (hi := by_omega)
    (hj := by_omega)).1 (by
      rw [stopsOf_getElem hi, stopsOf_getElem hi', e2, e2', e1, e1', heq])

/-- **A chord determines the query of its accepted triples.** -/
theorem triple_unique {t t' : ℕ × ℕ × ℕ} (ht : t ∈ A) (ht' : t' ∈ A)
    (heq : Merge.shoot J.whole ztwnl ztdzu =
      Merge.shoot J.whole (endOrigin J zta N₂ t'.1) (endDir t'.1)) : t.1 = t'.1 := by
  obtain ⟨-, hj, -, -, -, -, -, -, hlt⟩ := S.hBA.acc t ht
  obtain ⟨-, hj', -, -, -, -, -, -, hlt'⟩ := S.hBA.acc t' ht'
  zucdx
  zufjn
  exact (originTask J zta N₂ S.E.hP S.E.hNF₂ ztuyv).2 t.1 t'.1 hj hj'
    haR hav hat hlt haR' hav' hat' hlt' heq

/-- **A chord at the next key contributes at most two labels.** -/
theorem labsOf_card (e : Set Point) :
    (labsOf P J N₂ c co c' A rs e).Finite ∧ (labsOf P J N₂ c co c' A rs e).ncard ≤ 2 := by
  classical
  zueog
  · by_cases hex : ∃ i, ∃ hi : i < rs.length, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
        stopSet J zta N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = e
    · obtain ⟨i₀, hi₀, g1, g2, g3⟩ := hex
      have hsub : labsOf P J N₂ c co c' A rs e ⊆
          ((stopLabs co.nmem ztghr i₀).toFinset : Set ℕ) := by
        rintro x (⟨t, ht, hto, hte, -⟩ | ⟨i, hi, f1, f2, f3, hx⟩)
        · exact absurd zttop (S.triple_at ht hto).2.2.1
        · have := S.stop_unique hi hi₀ f1 f2 g1 g2 (f3.trans g3.symm)
          simp_all
      refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
      calc (labsOf P J N₂ c co c' A rs e).ncard
          ≤ (((stopLabs co.nmem ztghr i₀).toFinset : Set ℕ)).ncard :=
            ncard_le_ncard hsub ztgdv
        _ = (stopLabs co.nmem ztghr i₀).toFinset.card := ncard_coe_finset _
        _ ≤ (stopLabs co.nmem ztghr i₀).length := List.toFinset_card_le _
        _ ≤ 2 := stp_stopLabs_len _ _ _
    · have hemp : ztkno := by
        zumx
        zubcg

        · exact (S.triple_at ht hto).2.2.1 zttop
        simp_all
      simp_all
  · by_cases hex : ∃ t ∈ A, offT P J t = keyOff P J c' ∧
        Merge.shoot J.whole ztwnl ztdzu = e
    · obtain ⟨t₀, ht₀, g1, g2⟩ := hex
      have hsub : labsOf P J N₂ c co c' A rs e ⊆ {upOf N₂ t₀.1, dnOf N₂ t₀.1} := by
        rintro x (⟨t, ht, hto, hte, hx⟩ | ⟨i, hi, f1, f2, f3, -⟩)
        · have := S.triple_unique ht ht₀ (hte.trans g2.symm)
          simp_all
        · zueaz

      refine ⟨(toFinite _).subset hsub, (ncard_le_ncard hsub ztcwq).trans ?_⟩
      exact (ncard_insert_le _ _).trans by_simp
    · have hemp : ztkno := by
        zumx
        zubcg

        · grind
        · zueaz

      simp_all
end SCtx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
theorem stp_lblOf_mem {c : Config} {x : ℕ} (hx : x ∈ lblOf c kN kL) :
    ∃ i, i < c.nreg kN ∧ i < 4 ∧ c.nreg ztbuc = x := by
  unfold lblOf at hx
  grind
namespace SCtx
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set zte} {rs ax : List ztcf}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- The auxiliary records after the origins. -/
theorem auxRecs_co : AuxRecsAt co.nmem ztghr ax := by
  obtain ⟨hlen, hax, -, hrecA, -⟩ := S.hD
  have eaB : ztsfj := stp_co_keep S.hI by_omega
  have l1 := S.L.lay1
  have l3 := S.L.lay3
  have l5 := S.L.lay5
  zug
  zubtl

  have hm :=
    fun x h1 h2 => stp_co_mem S.L S.hI x by_omega by_omega
  grind

/-- The label list of the key is kept until the next-key step. -/
theorem lblOf_co : lblOf co kN kL = lblOf c kN kL ∧ co.nreg kN = c.nreg kN := by
  have ekN : ztsfk := stp_co_keep S.hI by_omega
  refine ⟨?_, ekN⟩
  zujqo
  rw [ekN]
  zucfh
  zug
  zucpm
  have := stp_co_keep S.hI (k := 2403 + i) by_omega
  rwa [show sw _ = kL + i by unfold kL sw; omega] at this

/-- The auxiliary facts of a skipped stop. -/
theorem skip_aux {i : ℕ} (h1 : c.nreg sP ≤ i) (h2 : i < c'.nreg sP) :
    ∃ hi : i < rs.length, ∃ hia : i < ax.length,
      co.nmem (co.nreg aB + 5 * i) = ax[i].1 ∧
      AuxOK P J N₂ ztwqu ax[i] := by
  obtain ⟨hi, -⟩ := S.skip_at h1 h2
  have hax := S.hD.2.1
  have hia : i < ax.length := by_omega
  obtain ⟨a0, -⟩ := S.auxRecs_co i hia
  rw [List.getD_eq_getElem _ _ hia] at a0
  have hok := S.hD.2.2.2.2.2.2.1 i hi
  simp_all
set_option maxHeartbeats 4000000 in
/-- **The labels at the next key.** -/
theorem labels :
    (∀ i, i < c'.nreg kN → c'.nreg ztbuc < N₂.nRegions) ∧
    EvInv J ztwis ztcnt ztjsy := by
  classical
  zuglt
  have hS₂ : (chainModel J.right).ChordFamily _ _ :=
    S.E.hNF₂.1
  have hF := F₂plus_chordFamily S.E
  zunw
  zueis
  zudpg
  obtain ⟨esP, -, -, -, -, -⟩ := iter_stops S.L S.hI
  obtain ⟨-, -, -, -, -, -, -, -, -, hkN4, hlab1, hlab2, -⟩ := S.hI.2.2.2.2.2.2.2 hsome
  have hrecA := S.auxRecs_co
  obtain ⟨hLco, ekN⟩ := S.lblOf_co
  have hCS := (regOf_spec S.E.hNF₂).2.1
  set pK := c'.nreg kE with hpK
  set tK := (chainModel J.whole).param _ ztbnz with htK
  -- the label universe at the key
  obtain ⟨e₁, e₂, h12⟩ := stp_two_chords hM hF.2.1 pK tK
  obtain ⟨hf₁, hc₁⟩ := S.labsOf_card e₁
  obtain ⟨hf₂, hc₂⟩ := S.labsOf_card e₂
  set U : Finset ℕ := hf₁.toFinset ∪ hf₂.toFinset with hU
  have hUc : U.card ≤ 4 := by
    refine (Finset.card_union_le _ _).trans ?_
    rw [← ncard_eq_toFinset_card _ hf₁, ← ncard_eq_toFinset_card _ hf₂]
    omega
  have inU : ∀ e ∈ F₂plus J ztwis,
      SideAttach (chainModel J.whole).W e pK tK → ∀ x, x ∈ labsOf P J N₂ c co c' A rs e →
      x ∈ U := by
    intro e he heK x hx
    rcases h12 e he heK with rfl | rfl
    · exact Finset.mem_union_left _ (hf₁.mem_toFinset.2 hx)
    · exact Finset.mem_union_right _ (hf₂.mem_toFinset.2 hx)
  -- the best list and the stop labels
  set Bst := co.nreg bF = 1 ∧
    offK P J _ _ = offK P J _ _ with hBst
  set L0 : List ℕ := if Bst then lblOf co bN bL else [] with hL0
  set vs : List ℕ := (List.range' _ _).flatMap
    _ with hvs
  have mem_vs : ∀ x, x ∈ vs ↔ ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
      x ∈ stopLabs co.nmem ztghr i := by
    zugop
    rw [hvs, List.mem_flatMap]
    grind
  have hL0src : ∀ x ∈ L0, ∃ t ∈ A, offT P J t = keyOff P J c' ∧ ztcxa := by
    zuh
    rw [hL0] at hx
    split_ifs at hx with hb
    · obtain ⟨t, ht, hto, hx'⟩ := S.hBA.lSrc hb.1 x hx
      exact ⟨t, ht, hto.trans hb.2, hx'⟩
    grind
  have hL0U : ∀ x ∈ L0, x ∈ U := by
    zuh
    obtain ⟨t, ht, hto, hx'⟩ := hL0src x hx
    obtain ⟨hmF, hat, -, -⟩ := S.triple_at ht hto
    exact inU _ hmF hat x ztzz
  have hvsU : ∀ x ∈ vs, x ∈ U := by
    zuh
    zudiz
    zudrj
    exact inU _ hmF hat x ztbmd
  have hL0nd : L0.Nodup := by
    rw [hL0]; split_ifs with hb
    · exact S.hBA.lNd hb.1
    simp
  have hL0len : L0.length ≤ 4 := by
    rw [hL0]; split_ifs
    · exact lblOf_len co
    · simp
  obtain ⟨-, -, -, hinL0, hinvs⟩ := stp_addLs_all hUc vs L0 hL0nd hL0len hL0U hvsU
  -- the label set of the next key
  have hΛ' := stp_curLab_eq (P := P) (J := J) (N₂ := N₂) hkN4
  have toΛ : ∀ l, l ∈ lblOf c' kN kL →
      regOf ztj zta N₂ l ∈ curLab P J N₂ c' := fun l hl => by
    grind
  -- the bounds of the stop labels
  have hvs_lt : ∀ x ∈ vs, x < N₂.nRegions := by
    zuh
    zudiz
    obtain ⟨hi, hia, -, hok⟩ := S.skip_aux h1 h2
    obtain ⟨-, -, -, hb0, hb1, -⟩ := hok
    rcases ((stp_mem_stopLabs hrecA hia).1 hx').2 with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · omega
    omega
  have hL0_lt : ∀ x ∈ L0, x < N₂.nRegions := by
    zuh
    obtain ⟨t, ht, -, hx'⟩ := hL0src x hx
    have hj := (S.hBA.acc t ht).2.1
    obtain ⟨hu, hd', -⟩ := hCS (t.1 / 2) by_omega
    rcases hx' with rfl | rfl
    · exact hu
    tauto
  -- the rule of the labels
  set An := Bst ∨ ∃ i, co.nreg sP ≤ i ∧ i < c'.nreg sP ∧ co.nmem _ = 1
    with hAnd
  refine ztonn
  · -- the labels are region indices
    have hmem : c'.nreg _ ∈ lblOf c' kN kL := stp_mem_lblOf hi hkN4
    zulwa
    · rw [hlab1 hAn] at hmem
      rcases stp_addLs_sub vs L0 hmem with h | h
      · grind
      grind
    · obtain ⟨h1, -⟩ := hlab2 hAn
      rw [h1, hLco] at hmem
      obtain ⟨i', hi', -, hx⟩ := stp_lblOf_mem hmem
      zulrg
      exact S.L.labR i' hi'
  · have hLst := le_trans S.L.keyL hlt.le
    refine evInv_step hP hS₂ hF S.L.inv hpw.1 hpw.2.1.1 hpw.2.1.2.1 hLst hlt.le S.gapK ?_
    by_cases hpock : ∃ e ∈ F₂plus J ztwis,
        SideAttach (chainModel J.whole).W e pK tK ∧
        ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J ztej = 0
    · grind
    zujce
    zulwa
    · zuhl
      have hlist := hlab1 hAn
      refine ⟨?_, fun e he heK hnb => ?_⟩
      · -- an anchored chord at the key
        rcases hAn with ⟨hbF, hbo⟩ | ⟨i, h1, h2, hfl⟩
        · obtain ⟨⟨j, hj⟩, -⟩ := S.hBA.bAcc hbF
          obtain ⟨hmF, hat, -, hnb'⟩ := S.triple_at hj hbo
          grind
        · rw [esP] at h1
          zudrj
          obtain ⟨hi', hia, hfl', hok⟩ := S.skip_aux h1 h2
          exact ⟨_, hmF, hat, hok.2.1.1 (hfl'.symm.trans hfl)⟩
      · -- every anchored chord at the key has its labels
        zueog
        · zubhf

          obtain ⟨-, hiff, hnl, -, -, hlab, -⟩ := hok
          rw [hse] at hiff hlab
          have hanc := hiff.2 hnb
          refine evSideLab_mono ?_ (hlab hanc by_grind)
          zuece

          apply hinvs
          rw [mem_vs]
          refine ⟨i, h1, h2, (stp_mem_stopLabs hrecA hia).2 ⟨hanc, ?_⟩⟩
          grind
        · obtain ⟨t, ht, hto, hte, hbF, hbo⟩ := S.nonstop_acc he heK hst
          obtain ⟨-, hj, hfree, -⟩ := S.hBA.acc t ht
          zucdx
          obtain ⟨-, ha⟩ := query_chord hj
          have hlab := evSideLab_fused hP S.E.hNF₂ hF by_omega ha haR hav hat
            hfree
          rw [hte] at hlab
          have hB : Bst := ztuhf
          have hL0e : L0 = lblOf co bN bL := by_grind
          have hinL : ∀ x, ztcxa → x ∈ L0 := by
            zuh
            have hxU := inU _ he heK x ztzz
            obtain ⟨c1, c2⟩ := S.hBA.lCov hbF t ht (hto.trans hbo.symm)
            rw [hL0e]
            zudsl
            · rcases c1 with h | h
              · zubh
              · zuitw
            · rcases c2 with h | h
              · zubh
              · zuitw
          refine evSideLab_mono ?_ hlab
          zuece

          apply hinL0
          zucyr
          · exact hinL _ (Or.inl h.2)
          · exact hinL _ (Or.inr h.2)
          · omega
          omega
    · zulw
      refine ⟨fun e he heK => ?_, ?_⟩
      · by_contra hnb
        zueog
        · zubhf

          rw [hse] at hok
          exact hAn (Or.inr ⟨i, by_omega, h2, hfl.trans (hok.2.1.2 hnb)⟩)
        · obtain ⟨t, -, -, -, hbF, hbo⟩ := S.nonstop_acc he heK hst
          exact hAn (Or.inl ztuhf)
      · obtain ⟨h1, h2⟩ := hlab2 hAn
        rw [hΛ', stp_curLab_eq S.L.labN, h1, hLco]
end SCtx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
theorem stp_le_last {α : Type*} {f : α → ℝ} {l : List α} {y : α}
    (hpw : l.Pairwise (fun a b => f a < f b)) (hy : l.getLast? = some y) :
    ∀ a ∈ l, f a ≤ f y := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hy
  zuge
  rcases List.mem_append.1 ha with h | h
  · exact (List.pairwise_append.1 hpw).2.2 a h y (List.mem_singleton_self y) |>.le
  simp_all
namespace SCtx
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set zte} {rs ax : List ztcf}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S
set_option maxHeartbeats 4000000 in
/-- **The log at the next key.** -/
theorem log' : ∃ ls : List ztck, ls.length = c'.nreg lC ∧
    LogRecsAt c'.nmem (c'.nreg lB) ls ∧ LogWords P J N₂ ls ∧
    LogPre J ztwis ztxxq ∧
    ls.getLast? = some (c'.nreg kE, c'.nreg kH, c'.nreg kN, c'.nreg kL, c'.nreg ztdvf,
      c'.nreg ztdvg, c'.nreg ztdvh) := by
  classical
  zuglt
  have hS₂ : (chainModel J.right).ChordFamily zta ztwis :=
    S.E.hNF₂.1
  zueis
  obtain ⟨-, -, hcap, hlC'⟩ := stp_meas_step S.E S.L S.hI S.hd
  zuicr
  zudpg
  obtain ⟨-, -, -, -, -, -, -, -, -, hkN4, -, -, -, r0, r1, r2, r3, -⟩ :=
    S.hI.2.2.2.2.2.2.2 hsome
  zubte

  have elB' : ztgue := stp_iter_keep S.hI (k := 2430) by_omega
  rw [elB, elC] at r0 r1 r2 r3
  obtain ⟨ls, hlen, hrec, hwords, hpre, hlast⟩ := S.L.log
  zufho

  have hm : ∀ x, c.nreg lB ≤ x → x < c.nreg lB + 7 * c.nreg lC → c'.nmem x = c.nmem x :=
    fun x h1 h2 => stp_c'_mem S.L S.hI S.hd x by_omega by_omega zthrr
  set r' : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := (c'.nreg kE, c'.nreg kH, c'.nreg kN, c'.nreg kL,
    c'.nreg ztdvf, c'.nreg ztdvg, c'.nreg ztdvh) with hr'
  refine ⟨ls ++ [r'], by_simp_all, ?_, ?_, ?_, List.getLast?_concat⟩
  · -- the records
    zug
    zuvw
    rw [elB']
    rcases Nat.lt_or_ge i ls.length with h | h
    · zuhjw
      obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hrec i h
      grind
    · have hil : i = ls.length := by_omega
      rw [List.getD_append_right _ _ _ _ h, show i - ls.length = 0 by omega, hil, hlen]
      zulrq
      refine ztion
      · have := r3 0 by_norm_num; omega
      · have := r3 1 by_norm_num
        omega
      · have := r3 2 by_norm_num
        omega
      · have := r3 3 by_norm_num
        omega
  · -- the word facts
    zuz
    rcases List.mem_append.1 hr with h | h
    · exact hwords r h
    grind
  · -- the log so far
    obtain ⟨hne, hall, hhead, hpwl, hcons, hlab⟩ := hpre
    set es := logOf J zta N₂ ls with hes
    set x' : ℕ × ℝ × Set ztf := (c'.nreg kE,
      (chainModel J.whole).param zta ztbnz, curLab P J N₂ c') with hx'
    have hmap : logOf J zta N₂ (ls ++ [r']) = es ++ [x'] := by
      simp [logOf, hes, hx', hr', curLab]
    rw [hmap]
    -- the last entry of the old log is the key
    set xc : ℕ × ℝ × Set ztf := (c.nreg kE,
      (chainModel J.whole).param zta ⟨c.nreg kE, c.nreg kH⟩, curLab P J N₂ c) with hxc
    have hlastE : es.getLast? = some xc := by
      rw [hes, logOf, List.getLast?_map, hlast]
      rfl
    have hxcoff : oW J (xc.1 + xc.2.1) = keyOff P J c := rfl
    have hx'off : oW J (x'.1 + x'.2.1) = keyOff P J c' := rfl
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hlastE
    refine ⟨by_simp, ?_, ?_, ?_, ?_, ?_⟩
    · zuh
      zucyj
      · grind
      · zugce
        zubst
        exact ⟨hpw.1, hpw.2.1.1, hpw.2.1.2.1, by rw [hx'off]; linarith [S.L.keyL]⟩
    · zuh
      obtain ⟨a, es', hae⟩ := List.exists_cons_of_ne_nil hne
      rw [hae] at hhead
      rw [hae] at hx
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      zultk
      exact hhead a rfl
    · refine List.pairwise_append.2 ⟨hpwl, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      zvojs at hb
      zulsy
      have := stp_le_last (f := fun x : ℕ × ℝ × Set (Set Point) => oW J ztbui) hpwl
        hlastE a ha
      grind
    · zug
      zuvw
      rcases Nat.lt_or_ge ztg es.length with h | h
      · rw [List.getD_append _ _ _ _ by_omega, List.getD_append _ _ _ _ h]
        exact hcons i h
      · have hi' : i + 1 = es.length := by_omega
        have hlen' : es.length = ys.length + 1 := by rw [hys]; simp
        have e1 : (es ++ [x']).getD i ztfj = xc := by
          rw [List.getD_append _ _ _ _ by_omega, hys,
            List.getD_append_right _ _ _ _ by_omega, show i - ys.length = 0 by omega]
          simp
        have e2 : (es ++ [x']).getD ztg ztfj = x' := by
          rw [List.getD_append_right _ _ _ _ by_omega, show i + 1 - es.length = 0 by omega]
          simp
        rw [e1, e2, hxcoff, hx'off]
        exact no_cut_iter S.E S.L S.hI
    · zuh
      zucyj
      · grind
      · zugce
        zubst
        exact labIn_of_evInv hP hS₂.2.1 hS₂.1 hpw.1 hpw.2.1.1 hpw.2.1.2.1 hinv
end SCtx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
@[expose] public section
namespace SCtx
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set zte} {rs ax : List ztcf}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- **A valid query ending beyond the key, not beyond the next key, is accepted.** -/
theorem comp_new {j : ℕ} (hj : j < 2 * N₂.nChords) (hv : ValidJ J zta N₂ j)
    (hlt' : J.whole.hitParam ztwka ztri <
      J.right.hitParam ztwka ztri) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W
      ztbams p t)
    (h1 : keyOff P J c < oW J ztk) (h2 : oW J ztk ≤ keyOff P J c') :
    ∃ t' ∈ A, t'.1 = j := by
  zuglt
  zukak
  zucst
  obtain ⟨haR, hav, hat⟩ := hv
  obtain ⟨-, hfree, -⟩ := origin_hit hP ztmkx ha haR hav hlt'
  zuixw
  have heq : oW J ztk = keyOff P J c' := by
    rcases h2.lt_or_eq with h | h
    · exact absurd ⟨h1, h⟩ (S.gapK _ he p t hA)
    omega
  obtain ⟨e1, e2⟩ := S.posEq hA.1 hA.2.1 hA.2.2.1 heq
  zvmws at hA
  have hns := origin_not_stop hP hS₂a ztmkx ha haR hav hat hlt'
  obtain ⟨t', ht', -, hte, -⟩ := S.nonstop_acc he hA hns
  refine ztrep
  obtain ⟨-, hj', -, -, -, -, -, -, hl'⟩ := S.hBA.acc t' ht'
  zufjn
  exact (originTask J zta N₂ hP S.E.hNF₂ ztuyv).2 t'.1 j hj' hj
    haR' hav' hat' hl' haR hav hat hlt' hte
set_option maxHeartbeats 2000000 in
/-- **The table up to the next key.** -/
theorem tab' : TabInv P J N₂ c' ztcnt := by
  zudpg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmK⟩ :=
    S.hI.2.2.2.2.2.2.2 hsome
  obtain ⟨hW, -, hR, -, -⟩ := S.hI
  obtain ⟨hkp, hmemS, -, -⟩ := stp_pre_frame hW hR
  have eTBs : ztguj := hkp 661 by_omega
  have eTB' : ztgud := stp_iter_keep S.hI (k := 661) by_omega
  zubte

  have hAl := (stp_alloc_mono S.hI).1
  zufho

  have hTc : ∀ x, x < c.nreg cTB + 6 * N₂.nChords → c'.nmem x = co.nmem x := fun x hx =>
    hmK x by_omega ztec
  have hTs : ∀ x, x < c.nreg cTB + 6 * N₂.nChords → cs.nmem x = c.nmem x := fun x hx =>
    hmemS x by_omega
  have hlt := (stp_next_key S.E S.L S.hI S.hd).1
  zun
  rw [eTB']
  obtain ⟨o0, o1, o2⟩ := S.L.tab j hj
  have hslot := S.hBA.slot j hj
  rw [eTBs] at hslot
  have hT0 : c'.nmem ztbwv = co.nmem ztbwv := hTc _ by_omega
  have hT1 : c'.nmem ztghl = co.nmem ztghl :=
    hTc _ by_omega
  have hT2 : c'.nmem ztghm = co.nmem ztghm :=
    hTc _ by_omega
  rw [hT0, hT1, hT2]
  -- a flag of the key stays
  have hkeep : c.nmem ztbwv = 1 → co.nmem ztbwv = 1 := by
    grind
  refine ⟨?_, ?_, fun hv hlt' p t hA hpt hL hle => ?_⟩
  · rcases hslot with ⟨s0, -, -⟩ | ⟨e, h', -, f0, -⟩
    · rw [s0, hTs _ by_omega]; exact o0
    omega
  · zuhgo
    rcases hslot with ⟨s0, s1, s2⟩ | ⟨e, h', hmA, f0, f1, f2⟩
    · rw [s0, hTs _ by_omega] at hf
      rw [s1, s2, hTs _ by_omega, hTs _ by_omega]
      grind
    · rw [f1, f2]
      exact (S.hBA.acc _ hmA).2.2
  · by_cases hc : oW J ztk ≤ keyOff P J c
    · grind
    · obtain ⟨t', ht', rfl⟩ := S.comp_new hj hv hlt' hA (not_le.1 hc) hle
      have := S.hBA.flag t' ht'
      grind
end SCtx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
set_option maxHeartbeats 2000000 in
/-- **Task L1: one iteration that does not finish.** -/
theorem stepTask : StepTask := by
  intro sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E L hI hd
  obtain ⟨-, -, A, hBA⟩ := hI.2.2.2.1
  zucxz
  have S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax :=
    ⟨E, L, hI, hd, hBA, hBA.val, hD⟩
  obtain ⟨hlt, hpw, -⟩ := stp_next_key E L hI hd
  obtain ⟨hmlt, hmeas, -, -⟩ := stp_meas_step E L hI hd
  obtain ⟨hstops, hso⟩ := stp_stops_c' E L hI hd
  obtain ⟨esB, eaB, esC, -, -⟩ := stp_arrays_c' E L hI hd
  obtain ⟨-, hptr, hptrL, -⟩ := stp_ptr_c' E L hI hd
  zuicr
  zukfs
  obtain ⟨-, -, -, -, -, -, -, -, -, hkN4, -⟩ := hI.2.2.2.2.2.2.2 hsome
  have eTB : ztgud := stp_iter_keep hI (k := 661) by_omega
  have elB : ztgue := stp_iter_keep hI (k := 2430) by_omega
  have egN : c'.nreg gN = c.nreg gN := stp_iter_keep hI (k := 2440) by_omega
  have egR : ∀ u, u < 2 → c'.nreg zttle = c.nreg zttle := fun u hu => by
    have := stp_iter_keep hI (k := 2441 + u) by_omega
    rwa [show sw ztssu = gR + u by unfold gR sw; omega] at this
  have hAl := stp_alloc_mono hI
  have hgN := L.gapN
  refine ⟨{
    stops := hstops
    sorted := fun i i' hii hi' => by
      rw [esC] at hi'
      rw [(hso i by_omega).2.2, (hso i' hi').2.2]
      exact L.sorted i i' hii hi'
    two := fun i hi => by
      rw [esC] at hi
      rw [(hso i by_omega).2.2, (hso ztcnn hi).2.2]
      exact L.two i hi
    tab0 := by zupcn; exact L.tab0
    lay1 := by rw [eTB, elB]; exact L.lay1
    lay2 := by rw [elB, esB]; exact L.lay2
    lay3 := by rw [elB, eaB]; exact L.lay3
    lay4 := by rw [esB, esC]; have := L.lay4; omega
    lay5 := by rw [eaB, esC]; have := L.lay5; omega
    key := hpw
    keyL := le_trans L.keyL hlt.le
    labN := hkN4
    labR := hlabR
    inv := hinv
    gapN := by_omega
    gapR := fun i hi => by
      rw [egN] at hi
      rw [egR i by_omega]
      exact L.gapR i hi
    gap := fun V hV => by
      obtain ⟨i, hi, hiV⟩ := L.gap V hV
      grind
    ptr := hptr
    ptrL := hptrL
    log := S.log'
    meas := hmeas
    tab := S.tab'
    done0 := hd }, hmlt⟩
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)
def frLoc (pe ph : ℕ) : Stmt :=
  .seq (locJ ztqm ztbz pe ph lJ)
    (.seq ztyvk
      ztffb)
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The post of the prefix** at the position `(pe, ph)`. -/
def LocOutG (P : Polygon) (J : Merge.Junction) (N₂ : NF) (pe ph : ℕ) (c c' : Config) : Prop :=
  ∃ j, j < N₂.arcs.length ∧
    (¬ (chainModel J.right).IsCut ztwis ztxjr →
      N₂.F ztj zta = ∅ ∨
        sideInArc ztzhd ztzeo
          ztxjr) ∧
    ((chainModel J.right).IsCut ztwis ztxjr →
      sk ztj zta N₂ j = (chainModel J.right).key zta ztpn ∨
        ek ztj zta N₂ j = (chainModel J.right).key zta ztpn) ∧
    c'.nreg lR0 = (N₂.arc ztdih).reg ∧
    c'.nreg lR1 = (N₂.arc ztvt).reg ∧
    c'.nreg lR2 = (N₂.arc ztdii).reg ∧
    c'.nreg fSE = (N₂.arc ztvt).s.edge ∧ c'.nreg fSH = (N₂.arc ztvt).s.hgt ∧
    c'.nreg fEE = (N₂.arc ztvt).e.edge ∧ c'.nreg fEH = (N₂.arc ztvt).e.hgt ∧
    c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
    ∀ r, bandOf r ∉ oracleBands → ztbwb → c'.nreg r = c.nreg r
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The prefix at a general position** `(pe, ph)`. -/
theorem frLoc_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {pe ph : ℕ} (hpr : 240000 ≤ pe ∧ pe < 250000 ∧ 240000 ≤ ph ∧ ph < 250000)
    (hfe : c.nreg pe < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztpn)
    (hroom : c.nreg ALLOC + faceLocK ztdg ≤ W) :
    IRS P W c₀ zttkc c ztbahv (LocOutG P J N₂ pe ph c) := by
  zuiw
  zuch
  zubkh

  zufe

  zudni
  -- 1. locate
  unfold frLoc
  refine IRS.mono (K := ztwzf + ztgxg)
    (IRS.seq (locJ_irs hI E.hG E.hWh
      ⟨by_decide, by_decide, by_decide,
        by decide, hpr.1, hpr.2.1, hpr.2.2.1, hpr.2.2.2⟩
      ⟨by_decide, by_decide⟩ hmd hmwf hP₂ hNA hNF
      hfe hpp htab hbig by_omega by_omega by_omega by_omega
      ztiro) ?_)
    ztksu ztb
  zubyj

  zukid
  have e4 : ztzpo :=
    keep1 _ ztmr
      by_decide
  -- 2. copy the normal form register
  refine IRS.seq (IRS.block [.copyN lNF _] hI₁
    ⟨iscr_sw by_decide by_decide, trivial⟩) ?_
  zubib
  zufvm
  have c2NF : ztzpv := by
    zudua
  have c2r : ztkow := by
    zucni
    zubdg
  zudhh
  -- 3. the header
  refine IRS.seq (IRS.block nbrHead hI₂ (nbrHead_ok _ _ hK₂.2.1 hK₂.2.2.2.1 hK₂.2.2.1
    by_omega)) ?_
  zubsf

  have c3A : ztuso := by
    zuccb

  have c3SB : ztbaqq := by
    simp_all
  have c3AB : ztbaqp := by
    simp_all
  have c3r : ztezj := by
    zucsc
  have c3J : ztpnp := by
    rw [c3r _ by_decide by_decide
      by_decide by_decide,
      c2r _ by_decide]
  -- 4. the neighbouring positions
  zubps

  have c4SB : ztbaqs := by
    zuhmw
  have c4AB : ztbaqr := by
    zuhmu
  have c4J : ztpnv := by
    zuhmv
  zudor
  -- the table reads
  have hseqv : ztjbe :=
    fun p hp => hNA.2.2.2.2.2.2.2.2.1 p ztlgq
  have hsjl : ztkoh := fun p hp =>
    NFLoc.seq_lt hNF hp
  have harcv : ∀ a, a < N₂.arcs.length →
      c.nmem _ = (N₂.arc a).reg ∧
      c.nmem _ = (N₂.arc a).s.edge ∧
      c.nmem _ = (N₂.arc a).s.hgt ∧
      c.nmem _ = (N₂.arc a).e.edge ∧
      c.nmem _ = (N₂.arc a).e.hgt :=
    hNA.2.2.2.2.2.2.1
  zufub
  have hb1 : ∀ v, v < N₂.arcs.length → c.nmem ztwpb + v ≤ W ∧
      c.nmem ztwsm + 5 * c.nmem ztbaqc + 4 ≤ W := by
    zuml
    zugem
    have := b3 _ ztobg
    omega
  have hbound : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      c₄.nreg lSB + c₄.nreg p ≤ W ∧ c₄.nreg lAB + 5 * c₄.nmem ztqkq ≤ W := by
    zuda
    zuiha
    zubyb
    · zufoo
    · zufms
    · zufon
  -- 5. the three regions
  zuciu

  have c5R0 : ztyun := by
    zuzy

  have c5R1 : ztyuo := by
    zuzz

  have c5R2 : ztyup := by
    zubaa

  have c5r : ztdxu := by
    zuchh
  have hm5 : ztlaq := by_grind
  have c5SB : ztbaqu := by
    rw [c5r _ by_decide by_decide
      by_decide by_decide
      by_decide, c4SB]
  have c5AB : ztbaqt := by
    rw [c5r _ by_decide by_decide
      by_decide by_decide
      by_decide, c4AB]
  have c5J : ztpny := by
    rw [c5r _ by_decide by_decide
      by_decide by_decide
      by_decide, c4J]
  zufto
  -- 6. the arc at `j`

  refine (IRS.block faceRead hI₅ (faceRead_ok _ _ hK₅.2.1 by_omega
    ztiig)).mono le_rfl ?_
  zubjs

  have c6r : ztygy := by
    zudqg
  have c6o : ∀ q, q ≠ lX → q ≠ lY → q ≠ fSE → q ≠ fSH → q ≠ fEE → q ≠ fEH →
      c₆.nreg q = c₅.nreg q := by
    zucbb
  have hothers : ∀ r, bandOf r ∉ oracleBands → ztbwb →
      c₆.nreg r = c.nreg r := by
    zubjg

    rw [c6r r hrr,
      c5r r ztpz
        ztpz
        ztpz
        ztpz
        ztpz,
      k4' r ztpz
        ztpz,
      c3r r ztpz
        ztpz
        ztpz
        ztpz,
      c2r r ztrty]
    zulfo
  have hR : ztfdu := by
    rintro q (rfl | rfl | rfl) <;> apply c6o <;>
      zuckm
  refine ⟨j, hj1, hl1, hl2, by zuobo,
    by zuobp, by zuobq,
    ?_, ?_, ?_, ?_, by zunsx; omega,
    hothers _ by_decide ztbuo, hothers⟩
  · zubly

  · zublz

  · zublw

  · zublx
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
def frGE : ℕ := sw 1206
def frGH : ℕ := sw 1207

/-- `dst := src` if `x` (normalised in `frGE, frGH`) is a vertex and equals the end `(ye, yh)`. -/
def frChk (dst ye yh src : ℕ) : Stmt :=
  .ifLtN K0 frGH .skip (.ifLtN ye frGE .skip (.ifLtN frGE ye .skip
    (.ifLtN K0 yh .skip ztihw)))

/-- The tail of one side. -/
def frTail (pe ph dst ye yh src : ℕ) : Stmt :=
  .seq (normS zted ye yh fO) (.seq (block [.copyN dst lR1])
    (.ifLtN pe K6 .skip (.seq (block [.copyN frGE pe, .copyN frGH ph])
      (.seq (normS zted frGE frGH fO) ztqnb))))
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem frChk_irs {dst ye yh src : ℕ} (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0)
    (hd : 240700 ≤ dst ∧ dst < 250000) :
    IRS P W c₀ ztqnb c 9 (fun c' =>
      c'.nreg dst = (if c.nreg frGH = 0 ∧ c.nreg ye = c.nreg frGE ∧ c.nreg yh = 0 then c.nreg src
        else c.nreg dst) ∧
      (∀ r, r ≠ dst → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold frChk
  by_cases h0 : c.nreg K0 < c.nreg frGH
  · refine (IRS.ifT h0 (IRS.skip (K := 0) hI ztdqf)).mono by_omega
      ztb
    grind
  by_cases h1 : c.nreg ye < c.nreg frGE
  · refine (IRS.ifF h0 (IRS.ifT h1 (IRS.skip (K := 0) hI ztdqf))).mono
      by_omega ztb
    grind
  by_cases h2 : c.nreg frGE < c.nreg ye
  · refine (IRS.ifF h0 (IRS.ifF h1 (IRS.ifT h2 (IRS.skip (K := 0) hI ztdqf))))
      |>.mono by_omega (fun _ h => h)
    grind
  by_cases h3 : c.nreg K0 < c.nreg yh
  · refine (IRS.ifF h0 (IRS.ifF h1 (IRS.ifF h2 (IRS.ifT h3
      (IRS.skip (K := 0) hI ⟨?_, by_omega, rfl⟩))))) |>.mono by_omega (fun _ h => h)
    grind
  · refine (IRS.ifF h0 (IRS.ifF h1 (IRS.ifF h2 (IRS.ifF h3 (IRS.block [.copyN dst src] hI
      ⟨iscr_sw hd.1 hd.2, trivial⟩))))).mono by_simp ?_
    zuu
    zuflx
    · zufpt

    · zubdg

/-- `nhgt` vanishes exactly at parameter `0`. -/
theorem nhgt_zero_iff {M : Model} {Q : Polygon} (x : WPos) :
    nhgt M Q x = 0 ↔ M.param Q x = 0 := by
  zulur
  zus
  · zugyx
  · constructor
    · intro hx; simp [Model.param, hx]
    simp_all
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The tail of one side.** -/
theorem frTail_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {pe ph dst ye yh src : ℕ}
    (hpe : sw 4110 ≤ pe ∧ pe ≤ sw 4113) (hph : sw 4110 ≤ ph ∧ ph ≤ sw 4113)
    (hdst : dst = sw 4114 ∨ dst = sw 4115) (hye : sw 1200 ≤ ye ∧ ye ≤ sw 1203)
    (hyh : sw 1200 ≤ yh ∧ yh ≤ sw 1203) (hyy : ye ≠ yh) (hsrc : src = lR0 ∨ src = lR2)
    {Y : WPos} (vye : c.nreg ye = Y.edge) (vyh : c.nreg yh = Y.hgt)
    (hYpp : ProperPos ztj zta P.n Y)
    (hYe : Y.edge < (chainModel J.right).W.n)
    (hYy : Y.edge < 6 → Y.edge ≠ 0 → Y.edge ≠ 2 → Y.edge ≠ 4 →
      |((chainModel J.right).pos (Qof P) Y).2| < J.right.radius)
    (hxe : c.nreg pe < (chainModel J.right).W.n)
    (hxpp : ProperPos ztj zta P.n ztpn)
    (hroom : c.nreg ALLOC + 22100 ≤ W) :
    IRS P W c₀ ztnyi c 22100 (fun c' =>
      c'.nreg dst = (if 6 ≤ c.nreg pe ∧
          nhgt ztj zta ztpn = 0 ∧
          Y.edge = c.nreg pe ∧ nhgt ztj zta Y = 0
        then c.nreg src else c.nreg lR1) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ dst → ztftw → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuljx
  have hfO : fO = sw 1204 := rfl
  have hfrGE : frGE = sw 1206 := rfl
  have hfrGH : frGH = sw 1207 := rfl
  have hd : 240700 ≤ dst ∧ dst < 250000 := by rcases hdst with rfl | rfl <;> unfold sw <;> omega
  unfold frTail
  -- 1. normalise the end
  refine IRS.mono (K := 11015 + (1 + (11015 + 2 + 7 + 9 + 2))) (IRS.seq
    (normS_irs hI (E.hK.fix hI) hctx
      ⟨by_decide, by_decide, by unfold sw at hye; omega,
        by unfold sw at hye; omega, by unfold sw at hyh; omega, by unfold sw at hyh; omega⟩
      ⟨by_decide, by_decide,
        by zunty; unfold sw at hye ⊢; omega, by zunty; unfold sw at hyh ⊢; omega,
        by zunty; unfold sw at hye ⊢; omega, by zunty; unfold sw at hyh ⊢; omega, hyy⟩
      by_omega by_simp_all by_simp_all
      by_omega) ?_) by_norm_num (fun _ h => h)
  rintro c₁ hI₁ - hA₁' ⟨v1e, v1h, k1, hA1, hm1⟩
  rw [vye, vyh] at v1h
  rw [vye] at v1e
  have keep1 : ∀ r, bandOf r ∉ oracleBands → ztftw → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1 r h1 (by unfold sw at hyh h2; omega) ztiij
      ztiij h3
  have nsw : ∀ q, ztltu ∨ ztluc ∨
      ztltp → bandOf q ∉ oracleBands ∧ (q < sw 1200 ∨ sw 1207 < q) ∧
      q ≠ ALLOC := by
    zuco
    refine ⟨not_oracle_sw zteqr zteqr,
      by unfold sw at hq ⊢; omega, by unfold ALLOC; unfold sw at hq; omega⟩
  have kq : ∀ q, ztltu ∨ ztluc ∨
      ztltp → c₁.nreg q = c.nreg q := fun q hq => by
    grind
  zubke
  -- 2. the default
  refine IRS.seq (IRS.block [.copyN dst lR1] hI₁ ⟨iscr_sw hd.1 hd.2, trivial⟩) ?_
  rintro c₂ hI₂ hA₂ hA₂' hc2
  have v2 : c₂.nreg dst = c.nreg lR1 := by
    zumyw; zumxt
    exact kq _ (Or.inr ztbcz)
  have k2 : ∀ r, r ≠ dst → c₂.nreg r = c₁.nreg r := fun r hr => by
    zumyw; zunnd
  have hm2 : ztpna := by zumyw
  have hdpe : pe ≠ dst := by rcases hdst with rfl | rfl <;> unfold sw at hpe ⊢ <;> omega
  have hdph : ph ≠ dst := by rcases hdst with rfl | rfl <;> unfold sw at hph ⊢ <;> omega
  have e2pe : c₂.nreg pe = c.nreg pe := by
    rw [k2 _ hdpe]; exact kq _ (Or.inl (by unfold sw at hpe ⊢; omega))
  have e2ph : c₂.nreg ph = c.nreg ph := by
    rw [k2 _ hdph]; exact kq _ (Or.inl (by unfold sw at hph ⊢; omega))
  have e2K6 := (E.hK.fix hI₂).2.2.1
  have hframe2 : ∀ r, bandOf r ∉ oracleBands → r ≠ dst → ztftw →
      r ≠ ALLOC → c₂.nreg r = c.nreg r := by_grind
  by_cases hb : c₂.nreg pe < c₂.nreg K6
  · -- a box position: the default
    refine (IRS.ifT hb (IRS.skip (K := 0) hI₂ ⟨?_, hframe2, ?_, ?_⟩)).mono by_omega
      ztb
    · grind
    · omega
    grind
  refine IRS.mono ztsyb (K := 2 + (11015 + 9) + 2) by_omega ztb
  rw [e2pe, e2K6] at hb
  -- 3. copy `x` and normalise it
  refine IRS.seq (IRS.block [.copyN frGE pe, .copyN frGH ph] hI₂
    ⟨iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide, trivial⟩) ?_
  zukob
  have hfrGEph : frGE ≠ ph := by zunlf; unfold sw at hph ⊢; omega
  have v3E : c₃.nreg frGE = c.nreg pe := by
    zuktr
  have v3H : c₃.nreg frGH = c.nreg ph := by
    zvnar; zumxt
    grind
  have k3 : ∀ r, r ≠ frGE → r ≠ frGH → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    zvnar; simp only [regB, regI, upd, ite_eq_right h1, ite_eq_right h2]
  zuyu
  refine IRS.seq (normS_irs hI₃
    ztjih (E.ctx2' hI₃)
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide,
      by decide⟩
    ⟨by_decide, by_decide,
      by decide, by_decide,
      by decide, by_decide,
      by decide⟩
    by_omega by_grind
    by_grind by_omega) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨v4E, v4H, k4, hA4, hm4⟩
  rw [v3E] at v4E
  rw [v3E, v3H] at v4H
  have nO : ∀ q, (q < sw 1204 ∨ sw 1207 < q) → q ≠ frGE → q ≠ frGH → bandOf q ∉ oracleBands →
      q ≠ ALLOC → c₄.nreg q = c₂.nreg q := fun q h1 h2 h3 h4 h5 => by
    rw [k4 q h4 h3 ztiii
      ztiii h5, k3 q h2 h3]
  have ry : ∀ q, sw 1200 ≤ q → q ≤ sw 1203 → c₄.nreg q = c₁.nreg q := fun q h1 h2 => by
    rw [nO q (Or.inl (by unfold sw at h2 ⊢; omega)) (by zunlf; unfold sw at h2 ⊢; omega)
      (by zuntz; unfold sw at h2 ⊢; omega) (not_oracle_sw (by unfold sw at h1; omega)
        (by unfold sw at h2; omega)) (by unfold ALLOC; unfold sw at h1; omega)]
    exact k2 q (by rcases hdst with rfl | rfl <;> unfold sw at h2 ⊢ <;> omega)
  have r4ye : c₄.nreg ye = Y.edge := by rw [ry ye hye.1 hye.2, v1e]
  have r4yh : c₄.nreg yh = nhgt ztj zta Y := by rw [ry yh hyh.1 hyh.2, v1h]
  have hsrcR : sw 1109 ≤ src ∧ src ≤ sw 1111 := by
    rcases hsrc with rfl | rfl <;> refine ⟨?_, ?_⟩ <;> simp [lR0, lR2, sw]
  have r4src : c₄.nreg src = c.nreg src := by
    rw [nO src (Or.inl ztmez) (by zunlf; unfold sw at hsrcR ⊢; omega)
      (by zuntz; unfold sw at hsrcR ⊢; omega)
      (not_oracle_sw ztnwb ztnwb)
      (by unfold ALLOC; unfold sw at hsrcR; omega),
      k2 _ (by rcases hdst with rfl | rfl <;> unfold sw at hsrcR ⊢ <;> omega)]
    exact kq _ (Or.inr (Or.inr ztmez))
  have r4dst : c₄.nreg dst = c.nreg lR1 := by
    rw [nO dst (Or.inr (by rcases hdst with rfl | rfl <;> unfold sw <;> omega))
      (by zunlf; rcases hdst with rfl | rfl <;> unfold sw <;> omega)
      (by zuntz; rcases hdst with rfl | rfl <;> unfold sw <;> omega)
      ztbet ztu, v2]
  have hk0 := (E.hK.fix hI₄).1
  refine (frChk_irs hI₄ hk0 hd).mono le_rfl ?_
  rintro c₅ ⟨v5, k5, hm5⟩
  have hA3 : ztbox := k3 _ by_decide
    by_decide
  have hA2 : zteic := k2 _ (by
    rcases hdst with rfl | rfl <;> unfold sw ALLOC <;> omega)
  have hA5 : ztcrj := k5 _ (by
    rcases hdst with rfl | rfl <;> unfold sw ALLOC <;> omega)
  refine ⟨?_, fun r h1 h2 h3 h4 => ?_, by_omega, fun a ha => ?_⟩
  · rw [v5, v4H, r4ye, r4yh, v4E, r4src, r4dst]
    by_cases hc : nhgt ztj zta ztpn = 0 ∧
        Y.edge = c.nreg pe ∧ nhgt ztj zta Y = 0
    · grind
    · rw [ite_eq_right hc, ite_eq_right by_omega]
  · rw [k5 r h2, nO r ztbsm (by zunlf; unfold sw at h3 ⊢; omega)
      (by zuntz; unfold sw at h3 ⊢; omega) h1 h4]
    exact hframe2 r h1 h2 h3 h4
  · rw [hm5, hm4 a by_omega, hm3, hm2, hm1 a ha]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
def frSide (pe ph dst ye yh src : ℕ) : Stmt := .seq zttkc ztnyi

/-- **The procedure of task F.** -/
def frProg : Stmt :=
  .seq ztnyg ztnyh
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The frame of one side. -/
def FrSideFr (dst : ℕ) (c c' : Config) : Prop :=
  zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → r ≠ dst → (r < sw 1100 ∨ sw 1207 < r) → r ≠ ALLOC →
      c'.nreg r = c.nreg r)
variable {r : ℕ}
theorem fr_rA (h : r < sw 1100 ∨ sw 1207 < r) : r < sw 1200 ∨ sw 1207 < r := by
  zugit
theorem fr_rB (h : r < sw 1100 ∨ sw 1207 < r) : r < sw 1102 ∨ sw 1203 < r := by
  zugit
theorem fr_rD (h : ¬ ztgz) : r < sw 1100 ∨ sw 1207 < r := by
  zugit
theorem fr_rC {q : ℕ} (h : sw 4110 ≤ q ∧ q ≤ sw 4113) :
    bandOf q ∉ oracleBands ∧ q ≠ frA ∧ (q < sw 1100 ∨ sw 1207 < q) ∧ q ≠ ALLOC := by
  unfold sw at h
  exact ⟨not_oracle_sw by_omega by_omega, by unfold frA sw; omega,
    Or.inr ztce, by unfold ALLOC; omega⟩
theorem fr_le1 {a K W : ℕ} (h : a + ztsyq ≤ W) : a + K ≤ W :=
  by omega
theorem fr_le2 {a K W : ℕ} (h : a + ztsyq ≤ W) : a + 22100 ≤ W :=
  by grind

/-- The key of a position is its edge plus its parameter. -/
theorem fr_key (M : Model) (Q : Polygon) (x : WPos) : M.key Q x = (x.edge : ℝ) + M.param Q x :=
  rfl

/-- **Non-cut**: a position that is a vertex on the box, or not a vertex, is not a cut. -/
theorem fr_noncut {C : Chain} {N : NF} (hP : C.P.Simple)
    (hN : IsNF ztc zta N) {x : WPos}
    (hpre : (chainModel C).param zta x = 0 ∨
      ¬ (chainModel C).IsCut ztwjq ztwol)
    (hv : ¬ (6 ≤ x.edge ∧ nhgt ztc zta x = 0)) :
    ¬ (chainModel C).IsCut ztwjq ztwol := by
  rcases hpre with h0 | h
  · have hn : nhgt _ _ x = 0 := (nhgt_zero_iff x).2 h0
    have he : x.edge < 6 := by
      omega
    rw [fr_key, h0, add_zero]
    exact frc_box_noncut hP hN he
  omega
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Side A**: the region faced just after `(fpE, fpH)`. -/
theorem frSideA_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fpE < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztcbp)
    (hpre : (chainModel J.right).param zta ztcbp = 0 ∨
      ¬ (chainModel J.right).IsCut ztwis
        ztymz)
    (hroom : c.nreg ALLOC + ztxoc ≤ W) :
    IRS P W c₀ ztnyg c ztxoc (fun c' =>
      c'.nreg frA < N₂.nRegions ∧
      AfterFaces ztj ztvjl
        ztync
        ztxhh ∧ FrSideFr frA c c') := by
  zubkh

  unfold frSide
  refine IRS.seq (frLoc_irs E hI
    ⟨by_decide, by_decide, by_decide, by_decide⟩ hfe hpp
    ztvqq) ?_
  zuwu

  obtain ⟨-, ⟨ppe, hee, hey⟩⟩ := arc_end_facts hP₂ hNF hsj
  have k1e : c₁.nreg fpE = c.nreg fpE := hk1 _ (not_oracle_sw by_decide
    by_decide) (Or.inr by_decide)
  have k1h : c₁.nreg fpH = c.nreg fpH := hk1 _ (not_oracle_sw by_decide
    by_decide) (Or.inr by_decide)
  refine (frTail_irs E hI₁ (dst := frA)
    ⟨by_rfl, by_decide⟩ ⟨by_decide, by_decide⟩
    ztp ztkp
    ⟨by_decide, by_rfl⟩ by_decide ztbt
    vEE vEH ppe hee hey by_omega by_simp_all
    by_grind).mono le_rfl ?_
  zugba
  rw [k1e, k1h, r1, r2] at vd
  set x : WPos := ztcbp with hx
  zuian

  have hR : ztipb := fun p hp =>
    (arc_regOf hNF hp).1
  refine ztfjs
  · zukza
    · exact hR _ ztqbg
    grind
  · zueoh
    · zufwl
      have hk : (chainModel J.right).key zta x = (c.nreg fpE : ℝ) := by
        zuihz
      zujjb
      zubys
      by_cases hY : (N₂.arc ztvt).e.edge = c.nreg fpE ∧
          nhgt ztj zta (N₂.arc ztvt).e = 0
      · zujlu
        exact face_after_eq hP₂ hNF hfe hj ((key_eq_nat_iff ppe _).2 hY)
      · zujlv
        exact face_after_ne hP₂ hNF hfe hj hl1 hl2 (fun h => hY ((key_eq_nat_iff ppe _).1 h))
    · zudyu

      exact frc_after hNF hj hfe ht0 ht1 ztvvl
  · grind
  · zueln
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Side B**: the region faced just before `(fqE, fqH)`. -/
theorem frSideB_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fqE < (chainModel J.right).W.n)
    (hpp : ProperPos ztj zta P.n ztcbq)
    (hpre : (chainModel J.right).param zta ztcbq = 0 ∨
      ¬ (chainModel J.right).IsCut ztwis
        ztyna)
    (hroom : c.nreg ALLOC + ztxoc ≤ W) :
    IRS P W c₀ ztnyh c ztxoc (fun c' =>
      c'.nreg frB < N₂.nRegions ∧
      BeforeFaces ztj ztvjm
        ztynd
        ztwva ∧ FrSideFr frB c c') := by
  zubkh

  unfold frSide
  refine IRS.seq (frLoc_irs E hI
    ⟨by_decide, by_decide, by_decide, by_decide⟩ hfe hpp
    ztvqq) ?_
  zuwu

  obtain ⟨⟨pps, hse, hsy⟩, -⟩ := arc_end_facts hP₂ hNF hsj
  have k1e : c₁.nreg fqE = c.nreg fqE := hk1 _ (not_oracle_sw by_decide
    by_decide) (Or.inr by_decide)
  have k1h : c₁.nreg fqH = c.nreg fqH := hk1 _ (not_oracle_sw by_decide
    by_decide) (Or.inr by_decide)
  refine (frTail_irs E hI₁ (dst := frB)
    ⟨by_decide, by_decide⟩ ⟨by_decide, by_rfl⟩
    ztbt ⟨by_rfl, by_decide⟩
    ⟨by_decide, by_decide⟩ by_decide ztp
    vSE vSH pps hse hsy by_omega by_simp_all
    by_grind).mono le_rfl ?_
  zugba
  rw [k1e, k1h, r1, r0] at vd
  set x : WPos := ztcbq with hx
  zuian

  have hR : ztipb := fun p hp =>
    (arc_regOf hNF hp).1
  refine ztfjs
  · zukza
    · exact hR _ ztqbf
    grind
  · zueoh
    · zufwl
      have hk : (chainModel J.right).key zta x = (c.nreg fqE : ℝ) := by
        zuihz
      zujjb
      zubys
      by_cases hY : (N₂.arc ztvt).s.edge = c.nreg fqE ∧
          nhgt ztj zta (N₂.arc ztvt).s = 0
      · zujlu
        exact face_before_eq hP₂ hNF hfe hj ((key_eq_nat_iff pps _).2 hY)
      · zujlv
        exact face_before_ne hP₂ hNF hfe hj hl1 hl2 (fun h => hY ((key_eq_nat_iff pps _).1 h))
    · zudyu

      exact frc_before hNF hj hfe ht0 ht1 ztvvl
  · grind
  · zueln
set_option maxRecDepth 20000 in
theorem fr_cost (L : ℕ) : zthwp + zthwp ≤ 60000 * ztgt := by
  unfold faceLocK
  omega
set_option maxRecDepth 20000 in
theorem fr_room {a L W : ℕ} (h : a + 60000 * ztgt ≤ W) :
    a + zthwp + zthwp ≤ W := by
  rw [Nat.add_assoc]
  exact le_trans (Nat.add_le_add_left (fr_cost L) a) h
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Task F: the regions of `N₂` faced at two positions of the walk of `C₂`.** -/
theorem faceRTask : FaceRTask := by
  refine ⟨frProg, fun _ => 60000, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hpe hppp hprep hqe hppq hpreq hroom
  replace hroom : c.nreg ALLOC + 60000 * ztgf ≤ W := hroom
  have hr := fr_room hroom
  show IRS P W c₀ frProg c (60000 * ztgf) _
  unfold frProg
  refine IRS.mono (IRS.seq (frSideA_irs E hI hpe hppp hprep
      by_grind) ?_) (fr_cost _)
    ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨vA, hAf, hm1, hAl1, hk1⟩
  have keep : ∀ q, ztlua → c₁.nreg q = c.nreg q := fun q hq => by
    obtain ⟨a, b, d, e⟩ := fr_rC hq
    simp_all
  have e1 := keep fqE ztkp
  have e2 := keep fqH ztomm
  refine (frSideB_irs E hI₁ by_omega by_simp_all
    by_simp_all by_grind).mono
    le_rfl ?_
  rintro c₂ ⟨vB, hBf, hm2, hAl2, hk2⟩
  zvmws at hBf
  have hAA : c₂.nreg frA = c₁.nreg frA := hk2 _ (not_oracle_sw by_decide
    by_decide) by_decide
    ztbcz by_decide
  refine ⟨by_omega, vB, by_grind, hBf, fun a ha => ?_,
    by omega, fun r h1 h2 h3 => ?_⟩
  · grind
  · have hFR := fun h => h2 zteg
    have hrA := fun h => h2 ztwkb
    have hrB : r ≠ frB := fun h => h2 ztbh
    rw [hk2 r h1 hrB ztvqt h3, hk1 r h1 hrA ztvqt h3]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
variable {J : Merge.Junction}
theorem slb_evVal {S₂ : Set ztf} {Λ : Set ztf} {G L : Set Point} (hL : L ∈ Λ)
    (hR : L ∈ (chainModel J.right).regions S₂) (hV : Valid J S₂ G L) : EvVal J S₂ Λ G :=
  ⟨L, Or.inl hL, hR, hV⟩

/-- **A chord inside a chord of `S₂`, away from the split vertex.** -/
theorem slb_part1 (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {e c : Set Point}
    (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c) {d : ℕ} (hd : d < Lst J) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e ztfq t)
    {Vu Vd : Set Point} (hVu : Vu ∈ (chainModel J.right).regions S₂)
    (hVd : Vd ∈ (chainModel J.right).regions S₂) (hsu : SideOf ztj 1 c Vu)
    (hsd : SideOf ztj (-1) c Vd) : EvSideLab J S₂ {Vu, Vd} e := by
  zucnd
  zuvm
  · exact slb_evVal ztfoq hVu
      (sideLabel_fused J hP hS₂ hF he hc hec hd ht0 ht1 hsec hA ztp hVu hsu G hG hS)
  · exact slb_evVal zthco hVd
      (sideLabel_fused J hP hS₂ hF he hc hec hd ht0 ht1 hsec hA ztbt hVd hsd G hG hS)

/-- **A faced region** has the label faced at the counterpart position. -/
theorem slb_faced (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {d : ℕ} (hd : d < Lst J) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hd1 : t = 0 → 1 ≤ d) {ρ dir : ℝ} {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hfac : FacedSide ztbm ztfq t ρ dir G)
    (hρd : ρ * dir = 1 ∨ ρ * dir = -1) {Va Vb : Set Point}
    (hVa : Va ∈ (chainModel J.right).regions S₂) (hVb : Vb ∈ (chainModel J.right).regions S₂)
    (ha : AfterFaces ztj ztbcq t Va)
    (hb0 : 0 < t → BeforeFaces ztj ztbcq t Vb)
    (hb1 : t = 0 → BeforeFaces ztj zterj 0 Vb) :
    EvVal J S₂ {Va, Vb} G := by
  obtain ⟨R1, R2⟩ := rlabel_of_faced J hP hS₂.2.1 hS₂.1 hd ht0 ht1 hfac
  zukmx
  · rcases ht0.lt_or_eq with htp | ht
    · exact slb_evVal zthco hVb
        (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hVb ((R2 h Vb).1 htp (hb0 htp)))
    · zucfb
      exact slb_evVal zthco hVb
        (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hVb ((R2 h Vb).2 rfl (hd1 rfl) ztvur))
  · exact slb_evVal ztfoq hVa
      (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hVa (R1 h Va ha))
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed
@[expose] public section
variable {J : Merge.Junction}

/-- A chord of `F₂⁺` going east (west) from a point `w` of `C₂`, and a chord of `S₂` going the same
way from `w`: the first lies in the second. -/
theorem slb_sub_same_way (_hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e c : Set Point} (he : e ∈ F₂plus J S₂)
    (hc : c ∈ S₂) {w : Point} (hwe : w ∈ e) (hwc : w ∈ c)
    (hdir : (ztmpt ∧ ∀ z ∈ c, w.1 ≤ z.1) ∨
      (ztmpu ∧ ∀ z ∈ c, z.1 ≤ w.1)) : e ⊆ c := by
  obtain ⟨y, a, b, hH, hyt, rfl, -, -⟩ := Merge.augChords_spec ztbac
  obtain ⟨y₁, a₁, b₁, hH₁, -, rfl, -, -⟩ := Merge.augChords_spec ztfnm
  have hy1 : y₁ ≤ J.right.top.2 := by
    have := F₂plus_snd_le J hS₂ he hwe
    rw [hwe.1] at this; omega
  zugpu
  obtain ⟨hwy₁, hwa₁, hwb₁⟩ := hwe
  have hyy : y₁ = y := hwy₁.symm.trans hwy
  zulau
  zuejv
  · have ea : a = w.1 := le_antisymm hwa (h2 (a, y₁) ztreg)
    have ea₁ : a₁ = w.1 := le_antisymm hwa₁ (h1 zttff ⟨rfl, le_rfl, hH₁.lt.le⟩)
    have hbb : b₁ ≤ b := by
      zube

      apply hH.right_not
      exact dom_right J (hH₁.open_mem b ztbzj hlt) hy1
    zugbh

  · have eb : b = w.1 := le_antisymm (h2 (b, y₁) ztred) hwb
    have eb₁ : b₁ = w.1 := le_antisymm (h1 ztthf ⟨rfl, hH₁.lt.le, le_rfl⟩) hwb₁
    have haa : a ≤ a₁ := by
      zube

      apply hH.left_not
      exact dom_right J (hH₁.open_mem a hlt ztbzj) hy1
    zugbh

/-- **One chord of `S₂` at the counterpart of a tie with a stop chord.** -/
theorem slb_U2 (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {e e' c' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hc' : c' ∈ S₂) (he'c' : e' ⊆ c') {d : ℕ} (hd : d < Lst J)
    (hA : SideAttach (chainModel J.whole).W e ztfq 0)
    (hA' : SideAttach (chainModel J.whole).W e' ztfq 0)
    (hcA : SideAttach (chainModel J.right).W c' ztbcq 0) {c'' : Set Point} (hc'' : c'' ∈ S₂)
    (hA'' : SideAttach (chainModel J.right).W c'' ztbcq 0) : c'' = c' := by
  zucf
  zust
  zuglq
  have hw : sidePt (chainModel J.whole).W ztfq 0 =
      sidePt (chainModel J.right).W ztbcq 0 := hC.sidePt_eq hd 0
  set w := sidePt (chainModel J.whole).W ztfq 0 with hwd
  have hwe : w ∈ e := hA.2.2.2.1
  have hwe' : w ∈ e' := hA'.2.2.2.1
  have hwc' : w ∈ c' := by_grind
  have hwc'' : w ∈ c'' := by zunft; exact hA''.2.2.2.1
  have dE := hM.attach_dir ztfhs hA
  have dE' := hM.attach_dir zthxr hA'
  have dC' := hM₂.attach_dir ztqpr hcA
  have dC'' := hM₂.attach_dir (hS₂.2.1 hc'') hA''
  rw [← hw] at dC' dC''
  -- `e`, `e'` go opposite ways
  have hopp : (ztmpt ∧ ∀ z ∈ e', z.1 ≤ w.1) ∨
      (ztmpu ∧ ∀ z ∈ e', w.1 ≤ z.1) := by
    rcases dE with h1 | h1 <;> rcases dE' with h2 | h2
    · exact absurd (hM.attach_east_unique hC.hF he' he hA' hA h2 h1) hne
    · grind
    · grind
    · exact absurd (hM.attach_west_unique hC.hF he' he hA' hA h2 h1) hne
  -- `c'` goes the way of `e'`
  have hc'way : ((∀ z ∈ e', w.1 ≤ z.1) → ∀ z ∈ c', w.1 ≤ z.1) ∧
      ((∀ z ∈ e', z.1 ≤ w.1) → ∀ z ∈ c', z.1 ≤ w.1) := by
    constructor
    · zuq
      zukkh
      · zuclh
      · exact (dir_not_both hM zthxr hA' h ztkwi).elim
    · zuq
      zukkh
      · exact (dir_not_both hM zthxr hA' ztkwi h).elim
      omega
  have hcA' : ztylk := hcA
  rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `e` east, `e'` and `c'` west
    have hc'w := hc'way.2 h2
    zukki
    · exact absurd (slb_sub_same_way hP hS₂.2.1 he hc'' hwe hwc'' (Or.inl ztons))
        zttoc
    · exact hM₂.attach_west_unique hS₂.2.1 hc'' hc' hA'' hcA ztlji
        by_grind
  · have hc'e := hc'way.1 h2
    zukki
    · exact hM₂.attach_east_unique hS₂.2.1 hc'' hc' hA'' hcA ztlji
        by_grind
    · exact absurd (slb_sub_same_way hP hS₂.2.1 he hc'' hwe hwc'' (Or.inr ztons))
        zttoc
theorem slb_cpB_eq {d : ℕ} (hd0 : d ≠ 0) (hdr : d ≠ rL1 J) : cpB J d = cpA J d := by
  have h : dq ztns ztpg ztku + 1 = dq ztns ztpg d := by
    zudcm
  unfold cpA cpB; zvmwc

/-- **The middle region of a tie with a fused partner** (away from the base and the split
vertex): its label is faced at the counterpart position. -/
theorem slb_middle_fused (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {e e' c' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hc' : c' ∈ S₂) (he'c' : e' ⊆ c') {d : ℕ} (hd : d < Lst J)
    (hd0 : d ≠ 0) (hdr : d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e ztfq 0)
    (hA' : SideAttach (chainModel J.whole).W e' ztfq 0)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hS' : SideOf ztbm ρ e' G) {Va Vb : Set Point}
    (hVa : Va ∈ (chainModel J.right).regions S₂) (hVb : Vb ∈ (chainModel J.right).regions S₂)
    (ha : AfterFaces ztj ztbcq 0 Va)
    (hb : BeforeFaces ztj zterj 0 Vb) : EvVal J S₂ {Va, Vb} G := by
  zucf
  have hGM₂ : GoodModel ztj := Or.inl ztkis
  rw [slb_cpB_eq hd0 hdr] at hb
  have hcA : ztylk :=
    attach_counterpart2 J hP hS₂.2.1 hS₂.1 hd le_rfl zero_lt_one (fun _ => ztooc) he'
      ztqpr he'c' hA'
  have huniq : ∀ c'' ∈ S₂, SideAttach (chainModel J.right).W c'' ztbcq 0 → c'' = c' :=
    fun c'' hc'' h => slb_U2 hP hS₂ he he' hne hnf hc' he'c' hd hA hA' hcA hc'' h
  have hsec : zthoa := fun _ => ztooc
  have lab := fun {V : Set Point} (hV : V ∈ (chainModel J.right).regions S₂)
      (hVs : SideOf ztj ρ c' V) =>
    sideLabel_fused J hP hS₂ hF he' hc' he'c' hd le_rfl zero_lt_one hsec hA' hρ hV hVs G hG hS'
  rcases hC.hM₂.attach_dir ztqpr hcA with h | h
  · have sa := after_side hGM₂ hS₂ hc' hcA huniq ztyhv hVa ha
    have sb := before_side hGM₂ hS₂ hc' hcA huniq ztyhv hVb hb
    zuvm
    · zulfu
    · exact slb_evVal ztfoq hVa (lab hVa sa)
  · have sa := after_side hGM₂ hS₂ hc' hcA huniq ztxvs hVa ha
    have sb := before_side hGM₂ hS₂ hc' hcA huniq ztxvs hVb hb
    zuvm
    · exact slb_evVal ztfoq hVa (lab hVa by_simp_all)
    · zulfu
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open WalkEmbed
@[expose] public section
variable {J : Merge.Junction}

/-- A point of a shoot lies on the ray. -/
theorem slb_shoot_pt {C : Chain} {a w : Point} {σ : ℝ} (hw : w ∈ Merge.shoot C a σ) :
    w.2 = a.2 ∧ ∃ s : ℝ, 0 ≤ s ∧ w.1 = a.1 + σ * s := by
  unfold Merge.shoot at hw
  obtain ⟨u, hu0, hu1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hw
  have hT : 0 ≤ C.hitParam a σ := Real.sInf_nonneg fun _ ht => ht.1.le
  refine ⟨by_simp, u * C.hitParam a σ,
    mul_nonneg hu0 hT, ?_⟩
  simp only [Geometry.lerp_fst, Visibility.rayPt_fst]
  ring
variable {S₂ : Set (Set Point)}
/-- A chord of `F₂⁺` in no chord of `S₂`: a shared chord or a top chord. -/
theorem slb_nonfused_kind (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {e : Set Point} (he : e ∈ F₂plus J S₂) (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) :
    ∃ (a : Point) (σ : ℝ), (a = J.shared ∨ a = J.right.top) ∧ ztdd ∧
      e = Merge.shoot J.whole a σ := by
  rcases f2_cases hS₂ he with ⟨c, hc, a, σ, ha, -, rfl⟩ | ⟨σ, hσ, -, rfl⟩ | ⟨σ, hσ, -, rfl⟩
  · exact absurd (shoot_sub_end hS₂ hc ha) (hnf c hc)
  · exact ⟨_, σ, Or.inl rfl, hσ, rfl⟩
  · exact ⟨_, σ, Or.inr rfl, hσ, rfl⟩

/-- **No tie of two non-fused chords** at a point other than the shared vertex and the top of
`C₂`. -/
theorem slb_nonfused_pt (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {e e' : Set Point} (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hnf' : ∀ c ∈ S₂, ¬ e' ⊆ c) {w : Point} (hw : w ∈ e)
    (hw' : w ∈ e') (hwv : w ≠ J.shared) (hwt : w ≠ J.right.top) : False := by
  obtain ⟨a, σ, ha, hσ, rfl⟩ := slb_nonfused_kind hS₂ he hnf
  obtain ⟨a', σ', ha', hσ', rfl⟩ := slb_nonfused_kind hS₂ he' hnf'
  obtain ⟨h2, s, hs, h1⟩ := slb_shoot_pt hw
  obtain ⟨h2', s', hs', h1'⟩ := slb_shoot_pt hw'
  have haa : ztsdh := by
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · rfl
    · exact shared_eq_top_of_snd J by_simp_all
    · exact (shared_eq_top_of_snd J by_simp_all).symm
    · rfl
  subst haa
  have hσσ : σ' ≠ σ := fun h => hne ztbzk
  have hσ' : σ' = -σ := by
    grind
  have hss : σ * (s + s') = 0 := by_grind
  zubat
  have hs0 : s = 0 := by
    have := (mul_eq_zero.1 hss).resolve_left hσ0
    linarith
  grind

/-- **No tie of two non-fused chords** at a vertex position of the open right stretch other than
the split vertex. -/
theorem slb_nonfused_tie (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hnf' : ∀ c ∈ S₂, ¬ e' ⊆ c) {d : ℕ} (hd : d < Lst J)
    (hd0 : d ≠ 0) (hdr : d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e ztfq 0)
    (hA' : SideAttach (chainModel J.whole).W e' ztfq 0) :
    False := by
  zucf
  have hoff := hC.off_M hd le_rfl zero_lt_one
  have h1 : ztpgl := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
  have h2 : ztou := by
    have : d + 1 ≤ rL1 J + rL2 J := hd
    zufc
  have hin : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
      ztwrh ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ztwrh <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
    grind
  have hwv : sidePt (chainModel J.whole).W ztfq 0 ≠
      J.shared := fun h =>
    off_shared_out J hP hS₂.2.1 hS₂.1 ztdtk le_rfl zero_lt_one h hin
  by_cases hwt : sidePt (chainModel J.whole).W ztfq 0 =
      J.right.top
  · exact no_tie_at_top2 J hP hS₂.2.1 hS₂.1 hd ztooc he he' ztnr hA hA' hwt
  · exact slb_nonfused_pt hS₂.2.1 he he' hne hnf hnf' hA.2.2.2.1 hA'.2.2.2.1 hwv hwt

/-- In case G the slit has positive length. -/
theorem slb_rδ_pos (h : rL1 J < Lst J) : 0 < rδ J := by
  unfold Lst at h
  unfold rL2 at h
  unfold rδ
  grind

/-- **The tie at the split vertex leaving the stretch** (`TieOut`). -/
theorem slb_tieOut (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) (hlt : rL1 J < Lst J)
    (hd0 : rL1 J ≠ 0)
    (hA : SideAttach (chainModel J.whole).W e ztmf 0)
    (hA' : SideAttach (chainModel J.whole).W e' ztmf 0)
    (hK : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J ztej)
    (hOff : OffOut J e' ztmf 0)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hS : SideOf ztbm ρ e G) (hS' : SideOf ztbm ρ e' G) :
    TieOut J S₂ G := by
  zucf
  zust
  have hsplit : sidePt (chainModel J.whole).W ztmf 0 =
      J.right.top := sidePt_split J hP hS₂.2.1 hS₂.1 hlt
  have hsplit' := sidePt_split J hP hS₂.2.1 hS₂.1 hlt
  obtain ⟨q, s, hB, hBo⟩ := hK
  obtain ⟨pb', tb', hB', hBne'⟩ := far_attach hM (hF.2.1 he') J.right.top
  have hoff := hC.off_M hlt le_rfl zero_lt_one
  have hBne : sidePt (chainModel J.whole).W q s ≠
      sidePt (chainModel J.whole).W ztmf 0 := by
    zuq
    obtain ⟨rfl, rfl⟩ := hM.attach_unique ztfhs hB hA h
    have : oW J (((gW J + rL1 J) % (chainModel J.whole).W.n : ℕ) + 0) = rL1 J + 0 := hoff
    zvmwk at hBo
    have : (rL1 J : ℝ) < (Lst J : ℝ) := by_simp_all
    linarith
  refine ⟨e, e', rL1 J, q, pb', s, tb', ρ, he, he', hne, hd0, hlt, hA, hA', hB, hB', hBne,
    by simp_all, fun h => ?_, hOff pb' tb' hB' by_simp_all, hρ,
    hS, hS', hsplit ▸ hA.2.2.2.1, hsplit ▸ hA'.2.2.2.1⟩
  have : (Lst J : ℝ) ≤ off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztej :=
    hBo
  have h2 := h.2
  have : ((rL1 J + rL2 J : ℕ) : ℝ) = (Lst J : ℝ) := rfl
  linarith
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
def SplitGapTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set ztf), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → (chainModel J.whole).ChordFamily Q ztbi →
    0 < rδ J →
    ∀ e ∈ F₂plus J S₂, ∀ e' ∈ F₂plus J S₂, e' ≠ e →
    SideAttach (chainModel J.whole).W e ztmf 0 →
    SideAttach (chainModel J.whole).W e' ztmf 0 →
    ztwly →
    (∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e' q s ∧
      sidePt (chainModel J.whole).W q s ≠
        sidePt (chainModel J.whole).W ztmf 0 ∧
      0 < oW J ztej ∧ oW J ztej < Lst J) →
    ∀ ρ : ℝ, ztbtc → ∀ G ∈ (chainModel J.whole).regions ztbi,
      SideOf ztbm ρ e G → SideOf ztbm ρ e' G →
      ∃ Vg, GapLab J S₂ Vg ∧ (RLabel J S₂ G Vg ∨ VLabel J S₂ G Vg)
open Filter Topology Metric
open WalkEmbed
open Chazelle.Chain (freeIn regionsIn)
theorem sg_sep {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {e e' : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (heA : SideAttach M.W e p t) {z : Point}
    (hz : z ∈ e') (hzD : z ∈ M.D) (hze : ∀ w ∈ e, w.1 ≠ z.1) {G U : Set Point}
    (hG : G ∈ M.regions F) (hU : U ∈ M.regions F) (hGe : SideOf M (-1) e G)
    (hUe : SideOf M 1 e U) (hGe' : SideOf M (-1) e' G) (hUe' : SideOf M 1 e' U) : False := by
  have hF1 : ({e} : Set _) ⊆ M.Adm := by_grind
  have hfin1 : ({e} : Set _).Finite := finite_singleton e
  obtain ⟨R₁, hR₁, hS1⟩ := side_region_exists' hM hF1 hfin1 ztkau ztbt
  obtain ⟨R₂, hR₂, hS2⟩ := side_region_exists' hM hF1 hfin1 ztkau ztp
  have hne := side_regions_ne hM hF1 hfin1 ztkau heA hR₂ hR₁ hS2 hS1
  have hsub : freeIn M.D F ⊆ freeIn M.D {e} :=
    sdiff_subset_sdiff_right by_grind
  -- a region of `F` on a side of `e` lies in the region of `{e}` on that side
  have into : ∀ {X R : Set Point} {ρ : ℝ}, X ∈ M.regions F → R ∈ M.regions {e} →
      SideOf M ρ e X → SideOf M ρ e R → X ⊆ R := by
    intro X R ρ hX hR hXs hRs
    obtain ⟨w, hw, hwD⟩ := adm_mem_dom hM ztesz
    obtain ⟨δ, h1, h2⟩ := ((hXs w hw hwD).and (hRs w hw hwD)).exists
    zugqw
    exact subset_region hR isPreconnected_connectedComponentIn
      ztdeh h1 h2
  have hGR := into hG hR₁ hGe hS1
  have hUR := into hU hR₂ hUe hS2
  -- the vertical segment through `z`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hM.isOpen z hzD
  obtain ⟨δ, ⟨hGd, hUd⟩, hδr⟩ := (((hGe' z hz hzD).and (hUe' z hz hzD)).and
    ztmbi).exists
  have hδ0 := hδr.1
  set S := (fun s : ℝ => (ztgnb : Point)) '' Icc (-δ) δ with hSdef
  have hSc : ztulh :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun s : ℝ => (ztgnb : Point)).continuousOn
  have hSf : S ⊆ freeIn M.D {e} := by
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
    refine ⟨hball ?_, ?_⟩
    · zukpt
      zuhpp
      grind
    grind
  have ha : (ztmpk : Point) ∈ S :=
    by grind
  have hb : (ztokn : Point) ∈ S :=
    by grind
  have hSR := subset_region hR₁ hSc hSf ha (hGR hGd)
  have hb1 := hSR hb
  have hb2 := hUR hUd
  exact hne ((Chazelle.Chain.regionsIn_eq_component hR₂ hb2).trans (Chazelle.Chain.regionsIn_eq_component hR₁ hb1).symm)

/-- **A chord tied with `e'` at its far end does not pass through the top of `C₂`.** -/
theorem sg_top_not_mem {J : Merge.Junction} (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {e' f' : Set Point} (he' : e' ∈ F₂plus J S₂)
    (hf' : f' ∈ F₂plus J S₂) (hne : f' ≠ e') {Pu q : ℕ} {s : ℝ}
    (hA1 : SideAttach (chainModel J.whole).W e' Pu 0)
    (hpt1 : sidePt (chainModel J.whole).W Pu 0 = J.right.top)
    (hA2 : SideAttach (chainModel J.whole).W e' q s)
    (hne2 : sidePt (chainModel J.whole).W q s ≠ sidePt (chainModel J.whole).W Pu 0)
    (hf'A : SideAttach (chainModel J.whole).W f' q s) (hu : J.right.top ∈ f') : False := by
  zunw
  have huD := hM.trace _ hA1.1 0 le_rfl zero_le_one
  have hYD := hM.trace _ hA2.1 s hA2.2.1 hA2.2.2.1.le
  have hue := hA1.2.2.2.1
  have hYe := hA2.2.2.2.1
  have hYf := hf'A.2.2.2.1
  rw [hpt1] at hue huD hne2
  set u := J.right.top
  set Y := sidePt (chainModel J.whole).W q s
  have he'A := F₂plus_subset J hS₂ he'
  have hf'Ad := F₂plus_subset J hS₂ hf'
  obtain ⟨y, a, b, hH, -, he'd, -, -⟩ := Merge.augChords_spec he'A
  obtain ⟨y', a', b', -, -, hf'd, -, -⟩ := Merge.augChords_spec hf'Ad
  zudoh
  have hend : ∀ w ∈ e', w ∉ (chainModel J.whole).D → w.1 = a ∨ w.1 = b := by
    intro w hw hwD
    rw [he'd] at hw
    zucxu
    zukmp
    · zukmq
      · exact absurd (show w ∈ (chainModel J.whole).D by
          zunqm; exact hH.open_mem w.1 h1 h2) hwD
      simp_all
    simp_all
  have hu1 := hend u hue huD
  have hY1 := hend Y hYe hYD
  have huy : u.2 = y := by rw [he'd] at hue; exact hue.1
  have hYy : Y.2 = y := by rw [he'd] at hYe; exact hYe.1
  have huY : u.1 ≠ Y.1 := by_grind
  rw [hf'd] at hu hYf
  obtain ⟨huy', hua', hub'⟩ := hu
  obtain ⟨-, hYa', hYb'⟩ := hYf
  have hsub : e' ⊆ f' := by
    rw [he'd, hf'd]
    rintro w ⟨hwy, hwa, hwb⟩
    zujft
    · grind
    grind
  exact hne (augChords_nest he'A hf'Ad hsub).symm
set_option maxHeartbeats 4000000 in
/-- **Task SG: the middle region of a split tie with a partner ending on `C₂`.** -/
theorem splitGapTask : SplitGapTask := by
  intro J Q S₂ hP hS₂ hF hδ e he e' he' hne heA he'A ⟨qe, se, heB, heL⟩
    ⟨q, s, hYA, hYne, hY0, hYL⟩ ρ hρ G hG hGe hGe'
  zucf
  zust
  zuglq
  have hS₂a := hS₂.2.1
  zudnl
  zuiwc
  have hGM₂ : ztebh := Or.inl ztkis
  zudrg
  zubtn
  zunc
  zucgj

  zurn
  zudgi

  have heA' : SideAttach W e Pu 0 := heA
  have he'A' : SideAttach W e' Pu 0 := he'A
  have hinPu : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteiu ∧
      off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteiu < ((rL1 J + rL2 J : ℕ) : ℝ) := by
    zucca

  have hY0' : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) _ := hY0
  have hYL' : off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) _ <
      ((rL1 J + rL2 J : ℕ) : ℝ) := hYL
  have hYne' : sidePt W q s ≠ sidePt W Pu 0 := hYne
  -- `e'` is an augmented chord of `C₂`
  have he'R : e' ∈ Merge.augChords J.right := by
    rcases partner_cases J hP hS₂a hS₂.1 he' he'A' hinPu with h | h
    · zubh
    · exact absurd by_grind (h q s hYA hYne')
  zuvm
  · -- above: a gap label
    have hSx := S₂x_family J hS₂ hF
    have hSs := S₂x_subset J hS₂a
    have hc : e' ∈ S₂x J S₂ := Or.inr ⟨he', he'R⟩
    obtain ⟨U₂, hU₂, hU₂s⟩ := side_region_exists' hM₂ hSs hSx.1 hc ztp
    obtain ⟨V, hV, hU₂V⟩ := super_region ztoip hU₂
    have hVs : SideOf _ 1 e' V := sideOf_mono hU₂s hU₂V
    zuddw
    have hk₂' : ztbpg % W₂.n =
        ztjp % W₂.n := by_grind
    have hgap : ztpke := by
      rcases split_copy J hP hδ ztlep ztjxo subset_rfl he'A' with
        ⟨hcW, hAk⟩ | ⟨hcE, hAk⟩
      · have hdirC : ((-1 : ℝ) = 1 ∧ ∀ z ∈ e',
            (sidePt W₂ (ztuk % W₂.n) 0).1 ≤ z.1) ∨
            ((-1 : ℝ) = -1 ∧ ∀ z ∈ e',
              z.1 ≤ (sidePt W₂ _ 0).1) :=
          Or.inr ztgtd
        have hFV := (faced_or_middle hGM₂ hSx hc hAk ztp hU₂ hU₂s hdirC).1
          (fun c'' hc'' hA'' => oneAt_right J hP zttdh hδ _ ztp
            c'' hc'' e' hc hA'' hAk)
        exact ⟨hδ, hV, Or.inl (afterFaces_mono (hFV.1 by_norm_num) hU₂V)⟩
      · have hdirC : ((1 : ℝ) = 1 ∧ ∀ z ∈ e',
            (sidePt W₂ _ 0).1 ≤ z.1) ∨
            ((1 : ℝ) = -1 ∧ ∀ z ∈ e',
              z.1 ≤ (sidePt W₂ (ztjp % W₂.n) 0).1) :=
          Or.inl ztgte
        have hFV := (faced_or_middle hGM₂ hSx hc hAk ztp hU₂ hU₂s hdirC).1
          (fun c'' hc'' hA'' => oneAt_right J hP zttdh hδ _
            ztbt c'' hc'' e' hc by_grind by_grind)
        exact ⟨hδ, hV, Or.inr (beforeFaces_mono (hFV.2 by_norm_num) hU₂V)⟩
    refine ⟨V, hgap, ?_⟩
    -- at the far end `Y`
    obtain ⟨dY, hdY, hdY0, hqY⟩ := stretch_decomp J hP hS₂a hS₂.1 hYA.1 hYA.2.1 hYA.2.2.1 hY0'
      hYL'
    have hsecY : s = 0 → dY ≠ 0 ∧ dY ≠ rL1 J := by
      grind
    have hYA2 : SideAttach W e' ((6 + tpos J.whole J.m₁ + dY) % W.n) s := by
      grind
    rcases local_step2 J hP hS₂ hF hdY hYA.2.1 hYA.2.2.1 hsecY he' hc subset_rfl hYA2
      ztp hG hV hGe' hVs with hR | ⟨hs0, f', hf', hfne, hf'A, hf'G, hcase⟩
    · grind
    · zumqe
      have hnotu := (sg_top_not_mem hP hS₂a he' hf' hfne he'A' hpt hYA hYne'
          by_grind)
      have hnotv : J.shared ∉ f' := by
        intro hv
        apply hnotu
        obtain ⟨y', a', b', -, -, hf'd, -, -⟩ := Merge.augChords_spec ztrjm
        have hYf : sidePt W q 0 ∈ f' := by rw [hqY]; exact hf'A.2.2.2.1
        have huy : (sidePt W Pu 0).2 = (sidePt W q 0).2 := by
          obtain ⟨y, a, b, -, -, he'd, -, -⟩ :=
            Merge.augChords_spec ztlep
          zumbc
          have h2 := hYA.2.2.2.1
          zujiu
          exact h1.1.trans h2.1.symm
        rw [hf'd] at hv hYf
        have hsh := shared_eq_top_of_snd J (by
          rw [← hpt, huy, hYf.1, hv.1])
        grind
      have vlab : ∀ c ∈ S₂, f' ⊆ c → SideOf _ 1 c V →
          VLabel J S₂ G V := fun c hcS hfc hcV =>
        ⟨f', c, 1, dY, 0, hf', hcS, hfc, Or.inl rfl, hdY, le_rfl, zero_lt_one, hsecY, hf'A,
          hf'G, hcV⟩
      rcases hcase with ⟨c', hc', hfc', hc'V⟩ | ⟨hk, -⟩
      · right
        rcases hc' with hc'S | ⟨hc'F, hc'R⟩
        · exact vlab c' hc'S hfc' hc'V
        · have hfeq :=
            augChords_nest ztrjm (F₂plus_subset J hS₂a hc'F) hfc'
          subst hfeq
          rcases F₂plus_kind J hS₂a hf' with ⟨c, hcS, hfc⟩ | hv | hu
          · have hcc := augChords_nest hc'R (hS₂a hcS) hfc
            zulat
            exact vlab f' hcS subset_rfl hc'V
          · grind
          grind
      grind
  · -- below: impossible
    exfalso
    -- the tie at the split vertex descends
    have hwa : (chainModel J.whole).wa Pu = J.right.top := by
      zuhnw
    zuuy
    have hwb : ((chainModel J.whole).wb Pu).2 ≤ J.right.top.2 := by
      have e0 := hC.sideNext_eq hd
      have edq : ztygr := by
        zumsl
      zuchk
      rw [edq, g2] at e0
      have e7 : Chazelle.Chain.sideNext W₂ 6 = J.right.sideTour J.right.sideBeta 1 := by
        zufdc
      show (Chazelle.Chain.sideNext W Pu).2 ≤ J.right.top.2
      rw [e0, e7]
      have := sideTour_sub_top_snd J.right J.right.sideBeta 1
      zuipa

    obtain ⟨U, hU, hUs⟩ := side_region_exists' hM hFs (F₂plus_finite J hS₂.1) he' ztp
    obtain ⟨de', hde'⟩ := dirAt_exists hM ztmkq he'A'
    obtain ⟨-, hhor, hdn, -⟩ :=
      (faced_or_middle hGM hF he' he'A' ztp hU hUs hde').2 e he hne.symm heA'
    have hdesc : ((chainModel J.whole).wb Pu).2 < ((chainModel J.whole).wa Pu).2 := by
      grind
    have hUe : SideOf _ 1 e U := (hdn hdesc).1 rfl
    -- a point of `e'` in the domain, on a vertical line off `e`
    obtain ⟨z, hz, hzD⟩ := adm_mem_dom hM ztmkq
    have huD := hM.trace _ he'A'.1 0 le_rfl zero_le_one
    obtain ⟨y, a, b, -, -, he'd, -, -⟩ := Merge.augChords_spec ztlep
    have hzy : z.2 = (sidePt W Pu 0).2 := by
      zumbc
      have h2 := hz
      zujiu
      exact h2.1.trans h1.1.symm
    have hzu : z.1 ≠ (sidePt W Pu 0).1 := by_grind
    have hze : ∀ w ∈ e, w.1 ≠ z.1 := by
      rcases hM.tie_pair hFs he he' hne.symm heA' he'A' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · zumhp
        have := h1 w hw
        have := h2 z hz
        grind
      · zumhp
        have := h1 w hw
        have := h2 z hz
        grind
    exact sg_sep hM hFs he heA' hz hzD hze hG hU hGe hUe hGe' hUs
variable {J : Merge.Junction}

/-- **The faced sides, and the middle sides through a handler.** -/
theorem slb_part2_core (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {d : ℕ} (hd : d < Lst J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hd1 : t = 0 → 1 ≤ d)
    (hA : SideAttach (chainModel J.whole).W e ztfq t)
    {Va Vb : Set Point} (hVa : Va ∈ (chainModel J.right).regions S₂)
    (hVb : Vb ∈ (chainModel J.right).regions S₂)
    (ha : AfterFaces ztj ztbcq t Va)
    (hb0 : 0 < t → BeforeFaces ztj ztbcq t Vb)
    (hb1 : t = 0 → BeforeFaces ztj zterj 0 Vb)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hS : SideOf ztbm ρ e G)
    (hmid : ∀ e' ∈ F₂plus J S₂, e' ≠ e →
      SideAttach (chainModel J.whole).W e' ztfq 0 → t = 0 →
      SideOf ztbm ρ e' G → EvVal J S₂ {Va, Vb} G) :
    EvVal J S₂ {Va, Vb} G := by
  zucf
  have hGM : GoodModel ztbm := Or.inl ztexm
  obtain ⟨dir, hdir1, hdir⟩ : ∃ dir : ℝ, (dir = 1 ∨ dir = -1) ∧
      ((dir = 1 ∧ ∀ z ∈ e, (sidePt (chainModel J.whole).W
          ztfq t).1 ≤ z.1) ∨
        (dir = -1 ∧ ∀ z ∈ e, z.1 ≤ (sidePt (chainModel J.whole).W
          ztfq t).1)) := by
    rcases hC.hM.attach_dir ztfhs hA with h | h
    · exact ⟨1, Or.inl rfl, Or.inl ztcfr⟩
    · exact ⟨-1, Or.inr rfl, Or.inr ztcfr⟩
  have hρd : ρ * dir = 1 ∨ ρ * dir = -1 := by
    grind
  have hfo := faced_or_middle hGM hF he hA hρ hG hS hdir
  have faced := fun (hfac : FacedSide (chainModel J.whole)
      ztfq t ρ dir G) =>
    slb_faced hP hS₂ hd ht0 ht1 hd1 hG hfac hρd hVa hVb ha hb0 hb1
  by_cases huniq : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e'
      ztfq t → e' = e
  · exact faced (hfo.1 huniq)
  zumiv
  obtain ⟨e', he', hA', hne⟩ := huniq
  obtain ⟨ht, hne', hdn, hup⟩ := hfo.2 e' he' hne hA'
  zucfb
  rcases lt_or_gt_of_ne hne' with h | h
  · zuvm
    · exact hmid e' he' hne hA' rfl ((hdn h).1 rfl)
    grind
  · zuvm
    · grind
    · exact hmid e' he' hne hA' rfl ((hup h).1 rfl)

/-- **The middle region of a tie at the split vertex.** -/
theorem slb_split_middle (hSG : SplitGapTask) (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) (hlt : rL1 J < Lst J)
    (hd0 : rL1 J ≠ 0)
    (hA : SideAttach (chainModel J.whole).W e ztmf 0)
    (hA' : SideAttach (chainModel J.whole).W e' ztmf 0)
    (hK : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J ztej)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hS : SideOf ztbm ρ e G) (hS' : SideOf ztbm ρ e' G)
    {Λ : Set ztf} {L : Set Point} (hL : L ∈ Λ)
    (hLr : L ∈ (chainModel J.right).regions S₂) : EvVal J S₂ Λ G := by
  by_cases hOff : OffOut J e' ztmf 0
  · exact slb_evVal hL hLr (valid_of_tieOut J hP hS₂ hF hG
      (slb_tieOut hP hS₂ hF he he' hne hlt hd0 hA hA' hK hOff hρ hS hS') L)
  · unfold OffOut at hOff
    push Not at hOff
    obtain ⟨p', t', h1, h2, h3, h4⟩ := hOff
    obtain ⟨Vg, hgap, hRL⟩ := hSG J Q S₂ hP hS₂ hF (slb_rδ_pos hlt) e he e' he' hne hA hA' hK
      ⟨p', t', h1, h2, h3, h4⟩ ρ hρ G hG hS hS'
    rcases hRL with hRL | hVL
    · exact ⟨Vg, Or.inr hgap, hgap.2.1, valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hgap.2.1 hRL⟩
    · exact ⟨Vg, Or.inr hgap, hgap.2.1, valid_of_vlabel J hP hS₂ hF hG hgap.2.1 hVL⟩

/-- **`LabTask` from `SplitGapTask`.** -/
theorem labTask_of (hSG : SplitGapTask) : LabTask := by
  intro J Q S₂ e hP hS₂ hF he _hstop _hnp hK d t hd ht0 ht1 hd0 hA
  have hd1 : ztgaz := fun h => Nat.one_le_iff_ne_zero.2 (hd0 h)
  by_cases hsp : t = 0 ∧ d = rL1 J
  · -- the split vertex
    obtain ⟨rfl, rfl⟩ := hsp
    have hd0' : ztuuu := hd0 rfl
    have hlt : rL1 J < Lst J := hd
    have hδ := slb_rδ_pos hlt
    refine ⟨fun c hc hec Vu hVu Vd hVd hsu hsd => ?_, fun hnf Va hVa Vb hVb ha hb0 hb1 => ?_⟩
    · zucnd
      have key : ∀ V, V ∈ ({Vu, Vd} : Set ztf) → V ∈ (chainModel J.right).regions S₂ →
          SideOf ztj ρ c V → EvVal J S₂ {Vu, Vd} G := by
        intro V hVΛ hV hVs
        rcases split_step J hP hS₂ hF hδ he (subset_S₂x J S₂ hc) hec hA hρ hG hV hS hVs with
          hRL | ⟨-, Vg, hgVg, hRLg⟩ | ⟨-, f', hf', hf'ne, hf'A, hf'S, -⟩
        · exact slb_evVal hVΛ hV (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hV hRL)
        · exact ⟨Vg, Or.inr hgVg, hgVg.2.1, valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hgVg.2.1 hRLg⟩
        · exact slb_split_middle hSG hP hS₂ hF he hf' hf'ne hlt hd0' hA hf'A hK hρ hG hS hf'S
            hVΛ hV
      zuvm
      · simp_all
      simp_all
    · zucnd
      exact slb_part2_core hP hS₂ hF he hd le_rfl zero_lt_one hd1 hA hVa hVb ha hb0 hb1 hρ hG hS
        (fun e' he' hne hA' _ hS' => slb_split_middle hSG hP hS₂ hF he he' hne hlt hd0' hA hA'
          hK hρ hG hS hS' ztfoq hVa)
  · -- away from the split vertex
    have hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J := fun ht => ⟨hd0 ht, fun h => hsp ⟨ht, h⟩⟩
    refine ⟨fun c hc hec Vu hVu Vd hVd hsu hsd =>
      slb_part1 hP hS₂ hF he hc hec hd ht0 ht1 hsec hA hVu hVd hsu hsd,
      fun hnf Va hVa Vb hVb ha hb0 hb1 => ?_⟩
    zucnd
    refine slb_part2_core hP hS₂ hF he hd ht0 ht1 hd1 hA hVa hVb ha hb0 hb1 hρ hG hS ?_
    intro e' he' hne hA' ht hS'
    zucfb
    obtain ⟨hd0', hdr⟩ := hsec rfl
    by_cases hfus : ∃ c' ∈ S₂, e' ⊆ c'
    · obtain ⟨c', hc', he'c'⟩ := hfus
      exact slb_middle_fused hP hS₂ hF he he' hne hnf hc' he'c' hd hd0' hdr hA hA' hρ hG hS'
        hVa hVb ha ztvur
    · push Not at hfus
      exact (slb_nonfused_tie hP hS₂ he he' hne hnf hfus hd hd0' hdr hA hA').elim
theorem labTask : LabTask := labTask_of splitGapTask
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The fixed facts** at a configuration of the run steps. -/
structure Fx (P : Polygon) (W : ℕ) (J : Merge.Junction) (c : Config) : Prop where
  k : Consts c
  r40 : ∀ k, k < 5 → c.nreg ztfit = cstR J k
  r45 : ∀ k, k < 5 → c.nreg ztfiu = cstL J k
  n1 : c.nreg ztna = 2 * J.left.m + 7
  n2 : c.nreg zthy = 2 * J.right.m + 7
  nw : c.nreg zthg = 2 * J.whole.m + 7
  gw : c.nreg cGW = gW J
  mpk : MapK J c
  ctxW : ChainCtx P W c ztjl J.whole
  ctx2 : ChainCtx P W c zted J.right
  ctx1 : ChainCtx P W c CD₁ J.left
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}
theorem EvEnv.fx (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) : Fx P W J c := by
  zubos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, h45, h33, h34, h35, -⟩ := hst
  have fix : ∀ i, i < 700 → c.nreg ztcdy = c₀.nreg ztcdy := fun i hi =>
    hI.hin _ ztze
  refine ⟨E.hK.fix hI, fun k hk => by_grind,
    fun k hk => by_grind, by_simp_all,
    by simp_all, by_simp_all, E.gw' hI,
    E.hM.fix hI, E.ctxW' hI, E.ctx2' hI, E.ctx1' hI⟩

/-! ## Conversions -/

/-- **A position of the model of `C₂` converted to the model of `C`.** -/
theorem convR_irs (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {pe po : ℕ} (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd ∧ 240000 ≤ pe)
    (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd) {h : ℕ}
    (hcl : PosClass J.right zta ztegy) (hW : (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ (convS ztfg zthy pe po) c 22 (fun c' =>
      c'.nreg po < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param zta ztici =
        (chainModel J.right).param zta ztegy ∧
      (chainModel J.whole).pos zta ztici =
        (chainModel J.right).pos zta ztegy ∧
      ztcjo ∧ c'.nmem = c.nmem) := by
  zuery
  zuhf
  have g0 := hfx.r40 0 by_norm_num
  zujxs
  have g2 := hfx.r40 2 by_norm_num
  have g4 := hfx.r40 4 by_norm_num
  simp only [cstR, List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2 g4
  have hpen : c.nreg pe < c.nreg zthy := by
    zupcv
    zubrz
  zubau
  zudpu
  zufgy

  refine (convS_irs ztp ztbt ztrda hpo hI hK hpen
    (by show c.nreg (sw ztngi) < _; rw [g1, hfx.n2]; omega) (by zupcv; omega)
    (by show c.nreg (sw (40 + 0)) < _; zuoot; omega) ztntu).mono
    le_rfl ?_
  zuhjn
  zukaf
  have e0 : ztxbt := g0
  have e1 : ztxpr := g1
  have e2 : c.nreg ztdah = rL1 J := g2
  have e4 : c.nreg ztdai = rδ J := g4
  rw [e0, e1, e2, e4, hfx.n2, hfx.nw, ← hn₂, ← hn] at hv
  obtain ⟨a1, a2, a3⟩ := conv_pos hS zta (e := c.nreg pe) (h := h) (by
    tauto)
  simp_all

/-- **A position of the model of `C₁` converted to the model of `C`.** -/
theorem convL_irs (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {pe po : ℕ} (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd ∧ 240000 ≤ pe)
    (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd) {h : ℕ}
    (hcl : PosClass J.left zta ztegy) (hW : (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ (convS ztbca ztna pe po) c 22 (fun c' =>
      c'.nreg po < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param zta ztici =
        (chainModel J.left).param zta ztegy ∧
      (chainModel J.whole).pos zta ztici =
        (chainModel J.left).pos zta ztegy ∧
      ztcjo ∧ c'.nmem = c.nmem) := by
  zucwn
  zuhf
  have g0 := hfx.r45 0 by_norm_num
  have g1 := hfx.r45 1 by_norm_num
  have g2 := hfx.r45 2 by_norm_num
  have g4 := hfx.r45 4 by_norm_num
  simp only [cstL, List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2 g4
  have hpen : c.nreg pe < c.nreg ztna := by
    zupcw
    zubrz
  zucmz
  zukhu
  zufgy

  refine (convS_irs ztbt ztp ztrda hpo hI hK hpen
    (by show c.nreg (sw ztngs) < _; rw [g1, hfx.n1]; omega) (by zupcw; omega)
    (by show c.nreg (sw (45 + 0)) < _; zuoot; omega) ztntu).mono
    le_rfl ?_
  zuhjn
  have hS := sideConvL J hP
  have e0 : ztxbs := g0
  have e1 : ztxps := g1
  have e2 : c.nreg ztdaj = lL1 J := g2
  have e4 : c.nreg ztdak = lδ J := g4
  rw [e0, e1, e2, e4, hfx.n1, hfx.nw, ← hn₁, ← hn] at hv
  obtain ⟨a1, a2, a3⟩ := conv_pos hS zta (e := c.nreg pe) (h := h) (by
    tauto)
  simp_all

/-! ## The attachment at the origin -/
def oKd : ℕ := sw 4010
def oKk : ℕ := sw 4011
def oB : ℕ := sw 4012
def oNB : ℕ := sw 4013
def oPE : ℕ := sw 4014
def oPH : ℕ := sw 4015
def oXE : ℕ := sw 4018
def oF0 : ℕ := sw 4020

/-- **The origin's position in `M` and its arrival position** (direction code `oB`). -/
def stA : Stmt := .seq (convS ztfg zthy oPE oXE) (callArr ztjl oXE oPH oB oF0)

/-- The registers `stA` writes (besides the oracle bands). -/
def StAW (r : ℕ) : Prop := CvSet oXE r ∨ ztlrk
set_option maxRecDepth 20000 in
theorem stA_irs (hP : J.P.Simple) (hNF : IsNF ztj zta N₂)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {kind k b : ℕ} (hok : StOK P J N₂ kind k b) (hb : c.nreg oB = b)
    (hpos : (chainModel J.right).pos zta zteyc = stOrig J zta N₂ kind k b)
    (hcl : PosClass J.right zta zteyc)
    (hpp : ProperPos ztj zta P.n zteyc)
    (hW : (chainModel J.whole).W.n ≤ W) (hroom : c.nreg ALLOC + 35029 ≤ W) :
    IRS P W c₀ stA c 35029 (fun c' => c'.nreg oF0 ≤ 1 ∧
      (c'.nreg oF0 = 1 ↔ FreeAt J.whole ztwme ztkz) ∧
      (c'.nreg oF0 = 1 → c'.nreg ztjf < (chainModel J.whole).W.n ∧
        ProperPos ztbm zta P.n ztzie ∧
        Arrival (chainModel J.whole).W ztwme ztcrx
          (c'.nreg ztjf)
          ((chainModel J.whole).param zta ztzie)) ∧
      EFr StAW c c') := by
  obtain ⟨-, -, hay, hset, hwall⟩ := stOrig_facts hP hNF hok
  zufpe
  unfold stA
  refine IRS.seq (K₁ := 22) (K₂ := 35007) (convR_irs hP hI hK hfx
    ⟨by_decide, by_decide, by_decide,
      by decide⟩
    ⟨iscr_sw by_decide by_decide, by_decide,
      by decide, by_decide⟩ hcl hW) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hxn, hxpar, hxpos, hr1, hm1⟩
  have k1 : ∀ r, r ≠ oXE → r ≠ cX → r ≠ cT → r ≠ cDd → c₁.nreg r = c.nreg r :=
    fun r a b d e => hr1 r ztqfu
  have hA1 : ztdc := k1 _ by_decide
    by_decide by_decide by_decide
  have hH1 : c₁.nreg oPH = c.nreg oPH := k1 _ by_decide
    by_decide by_decide by_decide
  have hB1 : ztmvh := k1 _ by_decide
    by_decide by_decide by_decide
  have hctx : ChainCtx P W c₁ ztjl J.whole := hfx.ctxW.transport
    (k1 _ by_decide by_decide by_decide
      by_decide) (fun x _ => by zvmxz) (by zvnhf)
  have hposM : (chainModel J.whole).pos zta ⟨c₁.nreg oXE, c₁.nreg oPH⟩ = a := by
    simp_all
  have hR : ztpkl := rfl
  refine (callArr_irs (o := oF0) hI₁ hctx
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩ ⟨by_decide, by_decide⟩ hxn
    ⟨by zuoou; exact hpp.1, by zuoou; exact hpp.2.1,
      by zupcx; exact hpp.2.2⟩ by_simp_all by_omega).mono le_rfl ?_
  rintro c' ⟨⟨hf1, hf2, hf3⟩, hr2, hA2, hm2⟩
  rw [hposM, hB1, hb] at hf2 hf3
  zullv
  have hon : a ∈ J.whole.set ∨ (|a.1| = J.whole.radius ∧ |a.2| < J.whole.radius) := by
    zubsx
    · grind
    · exact Or.inl (J.right_set_subset (hset h1))
  have hiff := freeAt_iff_arr J.whole hP hσ hon
  refine ⟨hf1, ⟨fun h => hiff.2 ⟨_, _, (hf2 h).2.2⟩, fun h => ?_⟩, hf2, ?_⟩
  · grind
  · refine ⟨fun r h1 h2 h3 => ?_, by_omega, fun x hx => by
      grind⟩
    have h2' : ¬ (CvSet oXE r ∨ ztlrk) := h2
    grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **A saved candidate of the first hit** of `C` on the ray from `a` in the direction `σ`. -/
def ResOK (P : Polygon) (C : Chain) (a : Point) (σ : ℝ) (Good : Prop) (F : ℕ) (c : Config) :
    Prop :=
  c.nreg F ≤ 1 ∧
    (c.nreg F = 1 → ∃ τ, 0 < τ ∧ OnCB C ztiu ∧ c.nreg zthap < (chainModel C).W.n ∧
      ProperPos ztc zta P.n ztzig ∧
      (chainModel C).pos zta ztzig = rayPt a σ τ ∧
      AbsRec P c ztnkx (rayPt a σ τ).1 C.radius ∧ (Good → τ = C.hitParam a σ)) ∧
    (Good → c.nreg F = 1)

/-- A saved candidate survives a step keeping its registers. -/
theorem ResOK.transport {C : Chain} {a : Point} {σ : ℝ} {G : Prop} {F : ℕ} {c c' : Config}
    (h : ResOK P C a σ G F c) (hr : ∀ i, i < 7 → c'.nreg ztsxi = c.nreg ztsxi) :
    ResOK P C a σ G F c' := by
  zubpa
  have e0 : c'.nreg F = c.nreg F := hr 0 by_norm_num
  refine ⟨by_omega, fun hf => ?_, fun hg => by_simp_all⟩
  zvokq at hf
  obtain ⟨τ, a1, a2, a3, a4, a5, a6, a7⟩ := h2 hf
  rw [hr 1 by_norm_num, hr 2 by_norm_num]
  exact ⟨τ, a1, a2, a3, a4, a5, absRec_transport a6 (hr 3 by_norm_num) (hr 4 by_norm_num)
    (hr 5 by_norm_num) (hr 6 by_norm_num), a7⟩

/-- The empty result. -/
def noRes (F : ℕ) : Stmt := .instr (.constN F 0)

/-- **Save the accumulator** into `F … F + 6`. -/
def saveL (F : ℕ) : List Instr :=
  [.copyN F accA, .copyN zthap ztbef, .copyN ztjiq ztcma, .copyN ztnkx zthdm,
    .copyN ztsxf ztnre, .copyN ztsxg ztnrf, .copyN ztsxh ztnrg]
theorem save_val (m f : ℕ → ℕ) {F : ℕ} (hF : 244000 ≤ F ∧ F + 6 < 250000) :
    regB m ztddh f F = f accA ∧ regB m ztddh f zthap = f ztbef ∧
    regB m ztddh f ztjiq = f ztcma ∧ regB m ztddh f ztnkx = f zthdm ∧
    regB m ztddh f ztsxf = f ztnre ∧ regB m ztddh f ztsxg = f ztnrf ∧
    regB m ztddh f ztsxh = f ztnrg ∧
    (∀ q, ztlrx → regB m ztddh f q = f q) := by
  have eA : accA = 242000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩ <;>
    simp only [saveL, regB, regI, upd, eA] <;>
    simp (disch := omega) only [ite_true, ite_eq_right]

/-- **Saving a local hit**: a candidate of the first hit. -/
theorem save_irs (hI : IInv W c₀ c) {F : ℕ} (hF : 244000 ≤ F ∧ F + 6 < 250000) {C : Chain}
    {a : Point} {σ : ℝ} {G : Prop} {L : Set ℝ}
    (hacc : AccOK P accA ztlnv C.radius a σ L c)
    (hL : ∀ τ ∈ L, 0 < τ ∧ OnCB C ztiu)
    (hG : G → FreeAt C a σ ∧ C.hitParam a σ ∈ L) (ha : G → a.2 ≤ C.top.2)
    (hσ : σ = 1 ∨ σ = -1) :
    IRS P W c₀ ztbafq c 7 (fun c' => ResOK P C a σ G F c' ∧
      (∀ q, ztlrx → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hok : okB W c.nmem ztddh c.nreg := by
    simp only [saveL, okB, okI]
    exact ⟨iscr_sw by_omega by_omega, iscr_sw by_omega by_omega,
      iscr_sw by_omega by_omega, iscr_sw by_omega by_omega, iscr_sw by_omega by_omega,
      iscr_sw by_omega by_omega, iscr_sw by_omega by_omega, trivial⟩
  zugsj
  zujgc
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, vo⟩ := save_val c.nmem c.nreg hF
  have e : ∀ q v, regB c.nmem ztddh c.nreg q = v → c'.nreg q = v := fun q v h => by
    simp_all
  have hm : c'.nmem = c.nmem := by zumyg
  refine ⟨?_, fun q hq => e q _ (vo q hq), hm⟩
  obtain ⟨hf1, hf0, hf⟩ := hacc
  refine ⟨by_simp_all, fun h1 => ?_, fun hg => ?_⟩
  · rw [e _ _ v0] at h1
    obtain ⟨τ, hτ, hmin, -, hpp, hen, hpos, hrec⟩ := hf h1
    obtain ⟨hτ0, hon⟩ := hL τ hτ
    refine ⟨τ, hτ0, hon, by_simp_all, by_simp_all,
      by simp_all, ?_, fun hg => ?_⟩
    · refine absRec_transport (c := c) hrec (e _ _ v3) ?_ ?_ ?_
      · simp_all
      · simp_all
      simp_all
    · obtain ⟨hfree, hmem⟩ := hG hg
      exact lh_min hσ (ha hg) hL hfree hmem hτ hmin
  grind
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **A local hit, saved** into `F … F + 6`. -/
def lhSave (sh : Stmt) (md cd nf nr F : ℕ) : Stmt :=
  .seq ztpco ztbafq

/-- The registers of `lhSave` (besides the oracle bands). -/
def LHSW (F : ℕ) (r : ℕ) : Prop := LHR r ∨ (F ≤ r ∧ r ≤ F + 6)
theorem lhSave_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {md cd nf nr Fo : ℕ}
    (hd : DR md) (hc : DR cd) (hn : DR nf) (hr : DR nr) (hFo : 244000 ≤ Fo ∧ Fo + 6 < 250000)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hM : MCtx P W C N E md cd nf c) (hPs : C.P.Simple) (hNF : IsNF ztc zta N)
    (hX : X.holds P c₀.nmem ztxj ztdq)
    (hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj)
    (hOk : Ok P ztc)
    (hsg : (chainModel C).Semigranular ztwjq ztq)
    (hdeg : (chainModel C).DegLe ztwjq zto)
    (hnr : c.nreg nr = 2 * C.m + 7) {x : WPos} (hxE : c.nreg lE = x.edge)
    (hxH : c.nreg lH = x.hgt) (hxD : c.nreg lD ≤ 1) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n x) (hcl : PosClass C zta x)
    (hy : |((chainModel C).pos zta x).2| < C.radius)
    (hon : (chainModel C).pos zta x ∈ C.set ∨
      |((chainModel C).pos (Qof P) x).1| = C.radius)
    {Gd : Prop}
    (hGd : Gd → sideLeft (chainModel C).W x.edge ztwte
        ztbaqi ∧
      ((chainModel C).pos zta x).2 ≤ C.top.2)
    (hroom : c.nreg ALLOC + ztbajp ≤ W) :
    IRS P W c₀ (lhSave sh md cd nf nr Fo) c
      ztbajp (fun c' =>
      ResOK P C ztwjd ztmk Gd Fo c' ∧
      EFr (LHSW Fo) c c') := by
  unfold lhSave
  refine IRS.seq (lhRun_irs hsh hBs hXl hd hc hn hr hI hK hG hWh hM hPs hNF hX hcap hOk hsg
    hdeg hnr hxE hxH hxD he hpp hcl hy hon by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨L', hacc, hL, hgeo, hfr⟩
  refine (save_irs hI₁ hFo hacc hL (fun g => hgeo (hGd g)) (fun g => (hGd g).2)
    (SweepStop.dirOf_cases' _)).mono le_rfl ?_
  rintro c' ⟨hres, hk, hm⟩
  have hAl : ztsef := hk ALLOC ztu
  refine ⟨hres, fun r h1 h2 h3 => ?_, hAl ▸ hfr.2.1, fun a ha => ?_⟩
  · have h2' : ¬ (LHR r ∨ (Fo ≤ r ∧ r ≤ Fo + 6)) := h2
    zuoov
    exact hfr.1 r h1 (fun h => h2' zteg) h3
  · zvmwi; exact hfr.2.2 a ha
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
@[expose] public section
noncomputable def ssKey (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (RB i : ℕ) : ℝ × ℕ :=
  rKey P J ztlsf ztruv

/-- **The order of the sort**: the records by key, then the indices `≥ S`. -/
noncomputable def ssLe (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (RB S : ℕ) (a b : ℕ) :
    Bool := by
  classical
  exact decide ztddd
variable {P : Polygon} {J : Merge.Junction} {m : ℕ → ℕ} {RB S a b : ℕ} {W : ℕ}
theorem ssLe_iff :
    ssLe P J m RB S a b = true ↔
      ztddd := by
  unfold ssLe; simp
theorem ssLe_in (ha : a < S)
    (hb : b < S) : ssLe P J m RB S a b = true ↔ KLe (ssKey P J m RB a) (ssKey P J m RB b) := by
  rw [ssLe_iff, ite_eq_left ha]; simp_all
theorem ssLe_trans {RB S : ℕ} (a b d : ℕ)
    (h1 : ssLe P J m RB S a b) (h2 : ssLe P J m RB S b d) : ssLe P J m RB S a d := by
  rw [ssLe_iff] at h1 h2 ⊢
  by_cases ha : a < S <;> by_cases hb : b < S <;> by_cases hd : d < S <;>
    simp only [ha, hb, hd, ite_true, ite_false, true_implies, false_implies] at h1 h2 ⊢ <;>
    first | trivial | omega | exact h1.trans h2
theorem ssLe_total {RB S : ℕ} (a b : ℕ) :
    (ssLe P J m RB S a b || ssLe P J m RB S b a) = true := by
  rw [Bool.or_eq_true, ssLe_iff, ssLe_iff]
  by_cases ha : a < S <;> by_cases hb : b < S <;>
    simp only [ha, hb, ite_true, ite_false, true_implies, false_implies, true_or, or_true] <;>
    first | omega | exact KLe.total _ _

/-! ## Registers -/

/-- The entry allocator of the sort task (a scratch register of stage 2). -/
def srA0 : ℕ := sw 3000

/-- The bands the comparator writes. -/
def ssBc : Finset ℕ := {bSign, bLocate, bOQuery}
theorem bSort_not_ssBc : bSort ∉ ssBc := by_decide
theorem ssBc_oracle : insert bSort ssBc ⊆ oracleBands := by_decide

/-! ## The comparator -/

/-- Load the position `(e, h)` (into `pe`, `ph`) and the direction code (into `pd`) of the raw
record whose index is in `s`: address `gRB + 11 s`. -/
def ssLdA (s pe ph pd : ℕ) : List Instr :=
  [.addN 120903 s s, .addN 120904 120903 120903, .addN 120905 120904 120904,
    .addN 120906 120905 120903, .addN 120906 120906 s, .addN 120906 120906 gRB,
    .loadN pe 120906, .addN 120906 120906 K1, .loadN ph 120906, .addN 120906 120906 K1,
    .loadN pd 120906]

/-- The inputs of `offCmp` (descriptor of `C`, the two positions, the base `gW`), the direction
codes, and the allocator set to the entry allocator (saved in `120900`). -/
def ssLd : List Instr :=
  [.copyN 50200 ztjl, .copyN 50205 cGW] ++ ssLdA 30000 50201 50202 120901 ++
    ssLdA 30001 50203 50204 120902 ++ [.copyN 120900 ALLOC, .copyN ALLOC srA0]

/-- The decision from the two offset bits and the direction codes. -/
def ssDec : Stmt :=
  .ifLtN K0 50210 ztjo
    (.ifLtN K0 50211 ztlr
      (.ifLtN 120902 120901 ztlr ztjo))

/-- Two records. -/
def ssMain : Stmt := .seq (block ssLd) (.seq offCmp (.seq (.instr (.copyN ALLOC 120900)) ssDec))

/-- **The comparator.** -/
def ssCmp : Stmt :=
  .ifLtN 30000 gRC (.ifLtN 30001 gRC ssMain ztjo)
    (.ifLtN 30001 gRC ztlr ztjo)

/-! ## The invariant of the comparator -/

/-- **The invariant of the comparator** (fixed data: the descriptor of `C`, the record array, the
entry allocator `A₀` and the memory below it). -/
def SsCtx (J : Merge.Junction) (d2 RB S A₀ : ℕ) (m₀ : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg ztjl = d2 ∧ d.nreg cGW = gW J ∧ d.nreg gRB = RB ∧ d.nreg gRC = S ∧
    d.nreg K0 = 0 ∧ d.nreg K1 = 1 ∧ d.nreg srA0 = A₀ ∧ ∀ a, a < A₀ → d.nmem a = m₀ a
theorem ssCtx_stable {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ} {A₁ : ℕ}
    (hA : A₀ ≤ A₁) : JStable zteoe A₁ := by
  intro c c' ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hr _ hm _ _
  have k : ∀ i, c'.nreg _ = c.nreg ztcdy := fun i =>
    hr _ (by unfold bandOf sw bSort; omega) ztiiy
  exact ⟨by_simp_all, (k 659).trans h2, (k 4000).trans h3, (k 4001).trans h4,
    (k 610).trans h5, (k 611).trans h6, (k 3000).trans h7,
    by grind⟩
set_option maxRecDepth 20000 in
theorem ssLd_val (m f : ℕ → ℕ) (h1 : f K1 = 1) :
    regB m ssLd f 50200 = f ztjl ∧ regB m ssLd f 50205 = f cGW ∧
    regB m ssLd f 50201 = m (f gRB + 11 * f 30000) ∧
    regB m ssLd f 50202 = m (f gRB + 11 * f 30000 + 1) ∧
    regB m ssLd f 120901 = m (f gRB + 11 * f 30000 + 2) ∧
    regB m ssLd f 50203 = m (f gRB + 11 * f 30001) ∧
    regB m ssLd f 50204 = m (f gRB + 11 * f 30001 + 1) ∧
    regB m ssLd f 120902 = m (f gRB + 11 * f 30001 + 2) ∧
    regB m ssLd f 120900 = f ALLOC ∧ regB m ssLd f ALLOC = f srA0 ∧
    ∀ r, r ≠ 50200 → r ≠ 50205 → r ≠ 50201 → r ≠ 50202 → r ≠ 50203 → r ≠ 50204 →
      r ≠ ALLOC → (r < 120900 ∨ 120906 < r) → regB m ssLd f r = f r := by
  simp only [K1, sw, Nat.reduceAdd] at h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b d e g i j k => ?_⟩
  all_goals simp only [ssLd, ssLdA, List.cons_append, List.nil_append, regB, regI, K1, gRB, cGW,
    srA0, ALLOC, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  all_goals try zvmwp
  all_goals try (congr 1; ring)
  simp only [ALLOC] at j
  zudlr
  grind
set_option maxRecDepth 20000 in
theorem ssLd_ok (m f : ℕ → ℕ) (h1 : f K1 = 1) {S A : ℕ} (ha : f 30000 < S)
    (hb : f 30001 < S) (hRB : f gRB + 11 * S ≤ A) (hAW : A ≤ W) : okW W m ssLd f := by
  simp only [K1, gRB, sw, Nat.reduceAdd] at h1 hRB
  simp only [ssLd, ssLdA, List.cons_append, List.nil_append, okW, okWI, regI, K1, gRB, cGW,
    srA0, ALLOC, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff,
    not_false_eq_true, true_and, and_true]
  omega

/-- A comparator branch setting the bit. -/
theorem ssBit_exec {d : Config} (hw : WordsBounded W d) (v : ℕ)
    (hv : v ≤ 1) (h1 : 1 ≤ W) :
    Exec P W ztotz d { d with nreg := upd d.nreg 30002 v } 1 :=
  Exec.constN hw _ _ by_omega
set_option maxRecDepth 20000 in
/-- **The comparator meets the contract of the sort.** -/
theorem ssCmp_ok {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ}
    {H : Host} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hwf : ChainWF P A₀ m₀ d2)
    (hC : ChainDescAt m₀ d2 zta H J.whole) (hWm : 2 * J.whole.m + 7 ≤ W)
    (hroom : A₀ + 11000 ≤ W) (hRB : RB + 11 * S ≤ A₀)
    (hrec : ∀ i, i < S → PosW P J (m₀ ztqcg) (m₀ ztnon))
    (hgn : gW J < (chainModel J.whole).W.n) :
    CmpOK P W ssCmp ssBc zteoe ztimg 12000 := by
  intro d hw hJ
  have hJ' := hJ
  obtain ⟨j2, jg, jRB, jS, j0, j1, jA, jm⟩ := hJ'
  zudk
  -- the frame of a one-bit branch
  have bit : ∀ v, v ≤ 1 → (v = 1 ↔ ssLe P J m₀ RB S ztqlm ztqln = true) →
      ∃ c' k, Exec P W ztotz d c' k ∧ k ≤ 1 ∧
        SsCtx J d2 RB S A₀ m₀ c' ∧
        c'.nreg 30002 = (if ssLe P J m₀ RB S ztqlm ztqln then 1 else 0) ∧
        (∀ r, r ≠ 30000 → r ≠ 30001 → r ≠ 30002 → ztmcp →
          c'.nreg r = d.nreg r) ∧
        (∀ r, bandOf r ∉ ssBc → c'.rreg r = d.rreg r) ∧
        c'.nmem = d.nmem ∧ c'.rmem = d.rmem ∧ c'.output = d.output := by
    intro v hv hiff
    refine ⟨_, 1, ssBit_exec hw v hv hW1, le_rfl, ?_, ?_, fun r h1 h2 h3 _ => ?_,
      fun _ _ => rfl, rfl, rfl, rfl⟩
    · tauto
    · zufb
      grind
    simp_all
  unfold ssCmp
  by_cases ha : d.nreg 30000 < d.nreg gRC
  · zuhsw
    · -- the main case
      rw [jS] at ha hb
      obtain ⟨a, had⟩ : ∃ a, d.nreg 30000 = a := by_grind
      obtain ⟨b, hbd⟩ : ∃ b, d.nreg 30001 = b := by_grind
      rw [had] at ha
      rw [hbd] at hb
      have hj1 := j1
      have e₁ := exec_regB (P := P) ssLd hw (ssLd_ok d.nmem d.nreg hj1 (by rw [had]; exact ha)
        (by rw [hbd]; exact hb)
        (A := A₀) by_omega by_omega)
      set d₁ : Config := { d with nreg := regB d.nmem ssLd d.nreg } with hd₁
      obtain ⟨v00, v05, v01, v02, vda, v03, v04, vdb, vsv, vA, vo⟩ :=
        ssLd_val d.nmem d.nreg hj1
      rw [jRB, had] at v01 v02 vda
      rw [jRB, hbd] at v03 v04 vdb
      rw [jA] at vA
      have mA : ∀ i, i < S → ∀ t, t < 11 → d.nmem _ = m₀ (RB + 11 * i + t) :=
        fun i hi t ht => jm _ by_omega
      zuka
      have hd1A : ztutt := vA
      have hd1m : ztpod := rfl
      -- the primitive
      have hpre : PrimPre OffIn P W d₁ := by
        refine ⟨hG, hWh, ?_, H, J.whole, ?_, ?_⟩
        · rw [hd1A, show d₁.nreg 50200 = d2 from v00.trans j2]
          exact (chainDesc_keep hwf hC by_omega le_rfl).2
        · zucua

        · obtain ⟨pa1, pa2, pa3⟩ := hrec a ha
          obtain ⟨pb1, pb2, pb3⟩ := hrec b hb
          have ea := mA a ha 0 by_norm_num
          have ha1 := mA a ha 1 by_norm_num
          have eb := mA b hb 0 by_norm_num
          have hb1 := mA b hb 1 by_norm_num
          zvnhg at ea eb
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hWm⟩
          · grind
          · grind
          · grind
          · grind
          · grind
          · grind
          grind
      obtain ⟨d₂, k₂, e₂, hk₂, hpost, -⟩ := offCmp_meets P W d₁ hw₁ hpre by_grind
      have fB := SignK.exec_frameB e₂ wr_offCmp
      have hC₁ : ChainDescAt d₁.nmem (d₁.nreg 50200) zta H J.whole := by
        zucua

      obtain ⟨blt, bgt⟩ := hpost H J.whole hC₁
      -- the keys
      set ka := ssKey P J m₀ RB a with hka
      set kb := ssKey P J m₀ RB b with hkb
      have hoa : off ((chainModel J.whole).W.n : ℝ) ((d₁.nreg 50205 : ℕ) : ℝ)
          ((chainModel J.whole).key zta ⟨d₁.nreg 50201, d₁.nreg 50202⟩) = ka.1 := by
        show off _ ((regB d.nmem ssLd d.nreg 50205 : ℕ) : ℝ) ((chainModel J.whole).key _
          ⟨regB d.nmem ssLd d.nreg 50201, regB d.nmem ssLd d.nreg 50202⟩) = _
        have q0 := mA a ha 0 by_norm_num
        zujnt
        rw [v05, jg, v01, v02, q0, mA a ha 1 by_norm_num]
        rfl
      have hob : off ((chainModel J.whole).W.n : ℝ) ((d₁.nreg 50205 : ℕ) : ℝ)
          ((chainModel J.whole).key zta ⟨d₁.nreg 50203, d₁.nreg 50204⟩) = kb.1 := by
        show off _ ((regB d.nmem ssLd d.nreg 50205 : ℕ) : ℝ) ((chainModel J.whole).key _
          ⟨regB d.nmem ssLd d.nreg 50203, regB d.nmem ssLd d.nreg 50204⟩) = _
        have q0 := mA b hb 0 by_norm_num
        zujnt
        rw [v05, jg, v03, v04, q0, mA b hb 1 by_norm_num]
        rfl
      rw [hoa, hob] at blt bgt
      have hda : d₂.nreg 120901 = ka.2 := by
        zukrj
        show regB d.nmem ssLd d.nreg 120901 = _
        rw [vda, mA a ha 2 by_norm_num]; rfl
      have hdb : d₂.nreg 120902 = kb.2 := by
        zukrj
        show regB d.nmem ssLd d.nreg 120902 = _
        rw [vdb, mA b hb 2 by_norm_num]; rfl
      -- restore the allocator
      zuja
      have e₃ := Exec.copyN (P := P) hw₂ ALLOC 120900
      set d₃ : Config := { d₂ with nreg := upd d₂.nreg ALLOC _ } with hd₃
      have k₃ : ∀ r, r ≠ ALLOC → d₃.nreg r = d₂.nreg r := fun r h => by
        zuote; zuobr
      have hK0 : d₃.nreg K0 = 0 := by
        rw [k₃ _ by_decide, fB.1 _ by_decide]
        show regB d.nmem ssLd d.nreg K0 = 0
        rw [vo _ by_decide by_decide by_decide by_decide by_decide by_decide
          by_decide by_decide]; exact j0
      -- the decision
      have hiff : ssLe P J m₀ RB S a b = true ↔ KLe ka kb := ssLe_in ha hb
      zuboe
      have bl1 := blt.1
      have bg1 := bgt.1
      have dec : ∃ v k₄, v ≤ 1 ∧ (v = 1 ↔ KLe ka kb) ∧ k₄ ≤ 7 ∧
          Exec P W ssDec d₃ { d₃ with nreg := upd d₃.nreg 30002 v } k₄ := by
        unfold ssDec
        have b10 : d₃.nreg 50210 = d₂.nreg 50210 := k₃ _ by_decide
        have b11 : d₃.nreg 50211 = d₂.nreg 50211 := k₃ _ by_decide
        have da := (k₃ _ by_decide).trans hda
        have db := (k₃ _ by_decide).trans hdb
        by_cases t1 : d₃.nreg K0 < d₃.nreg 50210
        · have hlt := blt.2.1 by_omega
          exact ⟨1, 2, le_rfl, ⟨fun _ => Or.inl hlt, by_omega⟩, by_norm_num,
            .ifLtN_true t1 ztqwt⟩
        · have hnlt : ¬ ka.1 < kb.1 := fun h => by
            have := blt.2.2 h; omega
          by_cases t2 : d₃.nreg K0 < d₃.nreg 50211
          · have hgt := bgt.2.1 by_omega
            refine ⟨0, 4, by_omega, ztpfb, by_norm_num,
              .ifLtN_false t1 (.ifLtN_true t2 ztqws)⟩
            zubpp
            · grind
            grind
          · have hngt : ¬ kb.1 < ka.1 := fun h => by
              have := bgt.2.2 h; omega
            have heq : ka.1 = kb.1 := by_grind
            by_cases t3 : d₃.nreg 120902 < d₃.nreg 120901
            · zuihj
              refine ⟨0, 6, by_omega, ztpfb, by_norm_num,
                .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true by_omega
                  ztqws))⟩
              zugro
              · grind
              · omega
            · zuihj
              exact ⟨1, 7, le_rfl, ⟨fun _ => Or.inr by_grind, by_omega⟩, by_norm_num,
                .ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false by_omega
                  ztqwt))⟩
      obtain ⟨v, k₄, hv, hvi, hk₄, e₄⟩ := dec
      -- the frame
      have hA₂ : d₂.nreg 120900 = d.nreg ALLOC := by
        rw [fB.1 _ by_decide]; omega
      have keep : ∀ r, r ≠ 30002 → ztmcp →
          ({ d₃ with nreg := upd d₃.nreg 30002 v } : Config).nreg r = d.nreg r := by
        intro r h2 h3
        zubi
        rw [upd_other _ _ _ h2]
        by_cases hrA : r = ALLOC
        · subst hrA; zuogt; omega
        zujh
        swap
        · omega
        · rw [k₃ _ hrA]
          rw [fB.1 r (by
            zudlb
            simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton,
              bandOf] at h3
            omega)]
          show regB d.nmem ssLd d.nreg r = _
          rw [vo r zthei ztxkl
            zthei ztxkl
            zthei ztxkl
            hrA (by
              zukr
              simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton,
                bandOf] at h3
              omega)]
      refine ⟨_, _, .ifLtN_true by_omega (.ifLtN_true by_omega
        ztwri), by simp only [ssLd, ssLdA] at *; simp; omega,
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r _ _ h2 h3 => keep r h2 h3, fun r hr => ?_,
        ?_, ?_, ?_⟩
      all_goals first
        | (rw [keep _ (by simp [sw, cGW, gRB, gRC, K0, K1, srA0]) (Or.inl by_decide)]; assumption)
        | skip
      · intro a' ha'
        show d₂.nmem a' = _
        rw [fB.2.2.1]; grind
      · zufb
        rw [had, hbd]
        zus
        · grind
        grind
      · show d₂.rreg r = d.rreg r
        rw [fB.2.1 r (by
          zudlb
          simp only [ssBc, bSign, bLocate, bOQuery, Finset.mem_insert, Finset.mem_singleton,
            bandOf] at hr
          omega)]
      · exact fB.2.2.1
      · exact fB.2.2.2.1
      · exact fB.2.2.2.2
    · obtain ⟨c', k, ex, hk, rest⟩ := bit 1 le_rfl ⟨fun _ => by
          rw [ssLe_iff, ite_eq_left by_omega]; omega,
        by omega⟩
      exact ⟨c', _, .ifLtN_true ha ztsoy, by_omega, rest⟩
  · zuhsw
    · obtain ⟨c', k, ex, hk, rest⟩ := bit 0 by_omega ⟨by_omega, fun h => by
          rw [ssLe_iff, ite_eq_right by_omega] at h; omega⟩
      exact ⟨c', _, .ifLtN_false ha (.ifLtN_true hb ex), by_omega, rest⟩
    · obtain ⟨c', k, ex, hk, rest⟩ := bit 1 le_rfl ⟨fun _ => by
          rw [ssLe_iff, ite_eq_right by_omega]; omega, by_omega⟩
      exact ⟨c', _, .ifLtN_false ha ztsoy, by_omega, rest⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
@[expose] public section
def srIB : ℕ := sw 3001
def srI : ℕ := sw 3002
def srA : ℕ := sw 3003
def srSB : ℕ := sw 3004
def srJ : ℕ := sw 3005
def srX : ℕ := sw 3006
def srP : ℕ := sw 3007
def srT : ℕ := sw 3008
def srS : ℕ := sw 3009
def srD : ℕ := sw 3010
def srE : ℕ := sw 3011
def srV : ℕ := sw 3012
def sr1 : ℕ := sw 3013
def sr2 : ℕ := sw 3014
def sr3 : ℕ := sw 3015
def sr4 : ℕ := sw 3016
set_option hygiene false in
/-- Register arithmetic on the named registers of the sort task. -/
macro "ssoSrt" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only [srA0, srIB, srI, srA, srSB, srJ, srX,
                srP, srT, srS, srD, srE, srV, sr1, sr2, sr3, sr4, sB, sC, aB, gRB, gRC, K0, K1, ALLOC,
                sw, Nat.reduceAdd, ne_eq]; omega))

/-! ## The memory after a record write -/

/-- The word of the raw record copied to word `t < 5` of the stop record. -/
def ssOff (t : ℕ) : ℕ := if t < 2 then t else t + 1

/-- The memory after writing `nd` words of the stop record at `D` and `ne` words of the
auxiliary record at `E` from the raw record at `Src`. -/
def ssWM (m : ℕ → ℕ) (Src D E nd ne : ℕ) (a : ℕ) : ℕ :=
  if D ≤ a ∧ a < D + nd then m (Src + ssOff zttej)
  else if E ≤ a ∧ a < E + ne then m (Src + 6 + (a - E)) else m a
theorem ssWM_zero (m : ℕ → ℕ) (Src D E : ℕ) : ssWM m Src D E 0 0 = m := by
  funext a; unfold ssWM; grind
variable {m : ℕ → ℕ} {Src D E nd ne : ℕ} {P : Polygon} {W : ℕ} {d : Config}
theorem ssWM_src (hSD : Src + 11 ≤ D) (hDE : D + 5 ≤ E)
    {u : ℕ} (hu : u < 11) : ssWM m Src D E nd ne zttdc = m zttdc := by
  unfold ssWM; grind
theorem ssWM_stepD (_hDE : D + 5 ≤ E) (hnd : nd < 5) (_hne : ne ≤ 5) :
    upd ztoij (D + nd) (m (Src + ssOff nd)) = ssWM m Src D E zttub ne := by
  funext a
  zujrd
theorem ssWM_stepE (hDE : D + 5 ≤ E) (hnd : nd ≤ 5) (hne : ne < 5) :
    upd ztoij (E + ne) (m (Src + 6 + ne)) = ssWM m Src D E nd zttuc := by
  funext a
  zujrd

/-! ## One copied word -/

/-- Copy the word at `srS` to the address in `R`, advancing both. -/
def ssCw (R : ℕ) : List Instr := [.loadN srV srS, .storeN R srV, .addN srS srS K1, .addN R R K1]
theorem ssCw_exec (hw : WordsBounded W d) {R : ℕ}
    (hK1 : d.nreg K1 = 1) (hR1 : R ≠ srV) (hR2 : R ≠ srS) (_hR3 : R ≠ K1) (hs : d.nreg srS + 1 ≤ W)
    (ht : d.nreg R + 1 ≤ W) :
    ∃ d', Exec P W (block (ssCw R)) d d' 4 ∧ d'.nreg srS = d.nreg srS + 1 ∧
      d'.nreg R = d.nreg R + 1 ∧ (∀ r, r ≠ srV → r ≠ srS → r ≠ R → d'.nreg r = d.nreg r) ∧
      d'.nmem = upd d.nmem (d.nreg R) (d.nmem (d.nreg srS)) ∧ d'.rreg = d.rreg ∧
      d'.rmem = d.rmem ∧ d'.output = d.output := by
  have nK1 : K1 ≠ srV ∧ K1 ≠ srS := by_decide
  have nVS : srS ≠ srV := by ssoSrt
  have e₁ := Exec.loadN (P := P) hw srV srS
  have e₂ := Exec.storeN (P := P) e₁.wb_right R srV
  have e₃ := Exec.addN (P := P) e₂.wb_right srS srS K1 (by
    simp_all)
  have e₄ := Exec.addN (P := P) e₃.wb_right R R K1 (by
    simp_all)
  refine ⟨_, Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃ (Exec.block_cons e₄
    ztpxq))), ?_, ?_, fun r a b c' => ?_, ?_, rfl, rfl, rfl⟩
  · zubi
    rw [upd_other _ _ _ (Ne.symm hR2), upd_same, upd_other _ _ _ nVS, upd_other _ _ _ nK1.1, hK1]
  · simp_all
  · simp_all
  simp_all

/-! ## The record write -/

/-- The source and destination pointers. -/
def ssWrHead : List Instr :=
  [.addN sr1 srX srX, .addN sr2 sr1 sr1, .addN sr3 sr2 sr2, .addN sr4 sr3 sr1, .addN sr4 sr4 srX,
    .addN srS sr4 gRB, .addN sr1 sC sC, .addN sr2 sr1 sr1, .addN sr2 sr2 sC, .addN srD sB sr2,
    .addN srE aB sr2]

/-- **Write the record of `srX`.** -/
def ssWr : Stmt :=
  .seq (block ssWrHead) (.seq ztdln (.seq ztdln
    (.seq (.instr (.addN srS srS K1)) (.seq ztdln (.seq ztdln
      (.seq ztdln (.seq ztdlo (.seq ztdlo
        (.seq ztdlo (.seq ztdlo (.seq ztdlo
          (.instr (.addN sC sC K1)))))))))))))
set_option maxRecDepth 20000 in
theorem ssWrHead_val (m f : ℕ → ℕ) :
    regB m ssWrHead f srS = f srX + f srX + ztjva + (f srX + f srX + ztjva) +
      ztjva + f srX + f gRB ∧
    regB m ssWrHead f srD = f sB + ztgri ∧
    regB m ssWrHead f srE = f aB + ztgri ∧
    ∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE →
      regB m ssWrHead f r = f r := by
  refine ⟨?_, ?_, ?_, fun r a b d e g h i => ?_⟩
  all_goals simp only [ssWrHead, regB, regI, sr1, sr2, sr3, sr4, srS, srD, srE, srX, sC, sB, aB, gRB, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  simp only [sr1, sr2, sr3, sr4, srS, srD, srE, sw, Nat.reduceAdd] at a b d e g h i
  simp_all
set_option maxRecDepth 20000 in
theorem ssWrHead_ok (m f : ℕ → ℕ)
    (h1 : f gRB + 11 * f srX + 11 ≤ f sB + 5 * f sC) (h2 : f aB + 5 * f sC + 6 ≤ W)
    (h3 : f sB ≤ f aB) : okW W m ssWrHead f := by
  simp only [srX, sC, sB, aB, gRB, sw, Nat.reduceAdd] at h1 h2 h3
  simp only [ssWrHead, okW, okWI, regI, sr1, sr2, sr3, sr4, srS, srD, srE, srX, sC, sB, aB, gRB, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true, and_true]
  omega
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **Writing one record**: from the raw record `x` at `Src = gRB + 11 x` (below the destination),
the stop record at `D = sB + 5 sC`, the auxiliary record at `E = aB + 5 sC` (`D + 5 ≤ E`),
`sC := sC + 1`. -/
theorem ssWr_exec (hw : WordsBounded W d)
    (hK1 : d.nreg K1 = 1)
    (hSD : d.nreg gRB + 11 * d.nreg srX + 11 ≤ d.nreg sB + 5 * d.nreg sC)
    (hDE : d.nreg sB + 5 * d.nreg sC + 5 ≤ d.nreg aB + 5 * d.nreg sC)
    (hEW : d.nreg aB + 5 * d.nreg sC + 6 ≤ W) :
    ∃ d' k, Exec P W ssWr d d' k ∧ k = 53 ∧
      d'.nmem = ssWM d.nmem (d.nreg gRB + 11 * d.nreg srX) (d.nreg sB + 5 * d.nreg sC)
        (d.nreg aB + 5 * d.nreg sC) 5 5 ∧
      d'.nreg sC = d.nreg sC + 1 ∧
      (∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE → r ≠ srV → r ≠ sC →
        d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  set Src := d.nreg gRB + 11 * d.nreg srX with hSrc
  set D := d.nreg sB + 5 * d.nreg sC with hD
  set E := d.nreg aB + 5 * d.nreg sC with hE
  set m := d.nmem with hm
  obtain ⟨vS, vD, vE, vo⟩ := ssWrHead_val d.nmem d.nreg
  have e₀ := exec_regB (P := P) ssWrHead hw (ssWrHead_ok d.nmem d.nreg by_omega by_omega by_omega)
  set d₀ : Config := { d with nreg := regB d.nmem ssWrHead d.nreg } with hd₀
  have p0S : d₀.nreg srS = Src := by_grind
  have p0D : d₀.nreg srD = D := by_grind
  have p0E : d₀.nreg srE = E := by_grind
  have p0o := vo
  have p0K : d₀.nreg K1 = 1 := by
    tauto
  have hSDv : Src + 11 ≤ D := by_omega
  have hDEv : D + 5 ≤ E := by_omega
  have hCW : d.nreg sC + 1 ≤ W := by_omega
  -- the state after `nd`, `ne` words, with the source pointer at `u`
  let St : ℕ → ℕ → ℕ → Config → Prop := fun nd ne u d' => WordsBounded W d' ∧
    d'.nreg srS = Src + u ∧ d'.nreg srD = D + nd ∧ d'.nreg srE = E + ne ∧
    d'.nmem = ssWM m Src D E nd ne ∧
    (∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE → r ≠ srV →
      d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output
  have S0 : St 0 0 0 d₀ := ⟨e₀.wb_right, by_omega, by_omega,
    by omega,
    by rw [ssWM_zero], by_grind, rfl, rfl, rfl⟩
  have stepD : ∀ nd ne u d', St nd ne u d' → nd < 5 → ne ≤ 5 → ssOff nd = u →
      ∃ d'', Exec P W ztdln d' d'' 4 ∧ St zttub ne ztcol d'' := by
    intro nd ne u d' ⟨w', s1, s2, s3, s4, s5, s6, s7, s8⟩ hnd hne hu
    have hK : ztuth := by
      rw [s5 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega
    have hu11 : u < 11 := by rw [← hu]; unfold ssOff; grind
    obtain ⟨d'', ex, t1, t2, t3, t4, t5, t6, t7⟩ := ssCw_exec (P := P) (R := srD) w' hK (by ssoSrt)
      (by ssoSrt) (by ssoSrt) by_omega by_omega
    refine ⟨d'', ex, ex.wb_right, by_omega, by_omega, ?_, ?_,
      fun r a b c' e f g h i => ?_, by_grind, by_grind, by_grind⟩
    · rw [t3 srE (by ssoSrt) (by ssoSrt) (by ssoSrt), s3]
    · rw [t4, s4, s2, s1, ssWM_src hSDv hDEv hu11, ← hu]
      exact ssWM_stepD hDEv hnd hne
    grind
  have stepE : ∀ ne u d', St 5 ne u d' → ne < 5 → 6 + ne = u →
      ∃ d'', Exec P W ztdlo d' d'' 4 ∧ St 5 zttuc ztcol d'' := by
    intro ne u d' ⟨w', s1, s2, s3, s4, s5, s6, s7, s8⟩ hne hu
    have hK : ztuth := by
      rw [s5 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega
    obtain ⟨d'', ex, t1, t2, t3, t4, t5, t6, t7⟩ := ssCw_exec (P := P) (R := srE) w' hK (by ssoSrt)
      (by ssoSrt) (by ssoSrt) by_omega by_omega
    refine ⟨d'', ex, ex.wb_right, by_omega, ?_, by_omega, ?_,
      fun r a b c' e f g h i => ?_, by rw [t5, s6], by rw [t6, s7], by rw [t7, s8]⟩
    · rw [t3 srD (by ssoSrt) (by ssoSrt) (by ssoSrt), s2]
    · rw [t4, s4, s3, s1, ssWM_src hSDv hDEv by_omega, ← hu,
        show Src + (6 + ne) = Src + 6 + ne by omega]
      exact ssWM_stepE hDEv le_rfl hne
    · rw [t3 r i f h, s5 r a b c' e f g h i]
  obtain ⟨d₁, x₁, S1⟩ := stepD 0 0 0 d₀ S0 by_norm_num by_norm_num rfl
  obtain ⟨d₂, x₂, S2⟩ := stepD 1 0 1 d₁ S1 by_norm_num by_norm_num rfl
  -- skip word `2`
  obtain ⟨w₂, s21, s22, s23, s24, s25, s26, s27, s28⟩ := S2
  have hK₂ : d₂.nreg K1 = 1 := by
    rw [s25 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega
  have x₃ := Exec.addN (P := P) w₂ srS srS K1 by_omega
  set d₃ : Config := { d₂ with nreg := upd d₂.nreg srS _ } with hd₃
  have S3 : St 2 0 3 d₃ := by
    refine ⟨x₃.wb_right, by zuogt; omega, ?_, ?_, s24,
      fun r a b c' e f g h i => ?_, s26, s27, s28⟩
    · tauto
    · tauto
    · zuote; rw [upd_other _ _ _ f]; exact s25 r a b c' e f g h i
  obtain ⟨d₄, x₄, S4⟩ := stepD 2 0 3 d₃ S3 by_norm_num by_norm_num rfl
  obtain ⟨d₅, x₅, S5⟩ := stepD 3 0 4 d₄ S4 by_norm_num by_norm_num rfl
  obtain ⟨d₆, x₆, S6⟩ := stepD 4 0 5 d₅ S5 by_norm_num by_norm_num rfl
  obtain ⟨d₇, x₇, S7⟩ := stepE 0 6 d₆ S6 by_norm_num rfl
  obtain ⟨d₈, x₈, S8⟩ := stepE 1 7 d₇ S7 by_norm_num rfl
  obtain ⟨d₉, x₉, S9⟩ := stepE 2 8 d₈ S8 by_norm_num rfl
  obtain ⟨d₁₀, x₁₀, S10⟩ := stepE 3 9 d₉ S9 by_norm_num rfl
  obtain ⟨d₁₁, x₁₁, S11⟩ := stepE 4 10 d₁₀ S10 by_norm_num rfl
  obtain ⟨w₁₁, -, -, -, s114, s115, s116, s117, s118⟩ := S11
  have hK₁₁ : d₁₁.nreg K1 = 1 := by
    rw [s115 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; omega
  have hC₁₁ :=
    s115 sC (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have x₁₂ := Exec.addN (P := P) w₁₁ sC sC K1 by_omega
  refine ⟨_, _, .seq e₀ (.seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ (.seq x₇ (.seq x₈
    (.seq x₉ (.seq x₁₀ (.seq x₁₁ x₁₂))))))))))), by_rfl, s114, ?_,
    fun r a b c' e f g h i j => ?_, s116, s117, s118⟩
  · zucac
  · simp only; rw [upd_other _ _ _ j]; exact s115 r a b c' e f g h i
