module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTProg
public import Chazelle.Core.FactsArcs

/-!
# WP-E, the candidate test: the mathematics of a hit

For a valid candidate (`ValidB`), the shot of the test runs on the arcs of its region
(`nArc`), cut by holes near the candidate:

* `arcs_listed`: every arc of the region is listed in the arc array;
* `hit_math`: a first hit is the first exit of the ray, the open stretch before it is in the
  region, the chord to it is admissible, and some position of the far end attaches the chord;
* `noHit_false`: if the ray leaves the domain, the shot hits.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt)
open ShotList ShotListG Machine SweepPrim

variable {P : Polygon} {M : Model} {N : NF}

/-- **A point of a proper position is off the domain.** -/
theorem pos_off (hGM : GoodModel M) {Q : Polygon} {x : WPos} (hxe : x.edge < M.W.n)
    (hx0 : 0 ≤ M.param Q x) (hx1 : M.param Q x ≤ 1) : M.pos Q x ∉ M.D :=
  (walkAx_of_goodModel hGM).trace x.edge hxe _ hx0 hx1

/-- **Every arc of the region is listed** in an array holding the normalised arcs of the
region record. -/
theorem arcs_listed (hNF : IsNF M (Qof P) N) {reg : ℕ → Set Point}
    (hregs : NFRegs M (Qof P) N reg) {r : ℕ} (hr : r < N.nRegions) {m : ℕ → ℕ} {B : ℕ}
    (harr : ∀ j, j < (N.region r).arcs.length → ShotList.arcAt m B j = nArc M (Qof P) N r j) :
    ∀ a b, M.IsArc (N.F M (Qof P)) (reg r) a b →
      ∃ j < (N.region r).arcs.length, M.key (Qof P) (ShotList.arcAt m B j).1 = a ∧
        M.key (Qof P) (ShotList.arcAt m B j).2 = b := by
  intro a b hab
  obtain ⟨-, -, hArcs, -⟩ := hregs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := hNF
  obtain ⟨i, hi, hir, hia, hib⟩ := hArcs.2.2.1 r hr a b hab
  have hmem : i ∈ (N.region r).arcs := (hArcs.2.2.2 r hr i).2 ⟨hi, hir⟩
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hmem
  have hat : arcAt N r j = i := by
    simp_all [arcAt, List.getD_eq_getElem?_getD, Option.getD_some] 
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hps : ProperPos M (Qof P) P.n (N.arc i).s := by simp_all
  have hpe : ProperPos M (Qof P) P.n (N.arc i).e := by simp_all
  refine ⟨j, hj, ?_, ?_⟩
  · rw [harr j hj, nArc, hat, (normOf_facts hps).2.2.2.1, hia]
  · rw [harr j hj, nArc, hat, (normOf_facts hpe).2.2.2.1, hib]

/-- The direction of a bit is `± 1`. -/
theorem dir_pm (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := dirOf_pm v

section
variable (hGM : GoodModel M) (hNF : IsNF M (Qof P) N) {reg : ℕ → Set Point} (hregs : NFRegs M (Qof P) N reg) {r : ℕ} (hr : r < N.nRegions) {x : WPos} {σb : ℕ} (hx : ProperPos M (Qof P) P.n x) (hxe : x.edge < M.W.n) (hv : ValidB M P N r x σb) (htop : ∀ C : Chain, M = chainModel C → (M.pos (Qof P) x).2 ≤ C.top.2) {m : ℕ → ℕ} {B : ℕ} {hs : List (WPos × WPos)} {A : Set Point} (harr : ∀ j, j < (N.region r).arcs.length → ShotList.arcAt m B j = nArc M (Qof P) N r j) (hnear : Near M (Qof P) hs (M.pos (Qof P) x)) (hlo : loSet M (Qof P) m B (N.region r).arcs.length hs ⊆ A)
include hGM hNF reg hregs r hr hx hxe hv htop m B hs harr hnear hlo
/-- **The mathematics of a hit.** -/
theorem hit_math
    (hhi : A ⊆ hiSet M (Qof P) m B (N.region r).arcs.length) {t : ℝ}
    (hfh : FirstHit A (M.pos (Qof P) x) (dirOf σb) t) :
    rayPt (M.pos (Qof P) x) (dirOf σb) t ∉ M.D ∧
      (∀ s, 0 < s → s < t → rayPt (M.pos (Qof P) x) (dirOf σb) s ∈ reg r) ∧
      chordOf (M.pos (Qof P) x) (dirOf σb) t ∈ M.Adm ∧
      (∃ p t', SideAttach M.W (chordOf (M.pos (Qof P) x) (dirOf σb) t) p t' ∧
        sidePt M.W p t' = rayPt (M.pos (Qof P) x) (dirOf σb) t) :=
  firstHit_exit hGM hNF.1 (hregs.1.1 r hr) (dir_pm σb) (pos_off hGM hxe hx.1 hx.2.1.le)
    (valid_sound hGM hNF hregs hr hx hxe hv) htop (arcs_listed hNF hregs hr harr) hnear hlo hhi hfh

/-- **The shot hits** when the ray from a valid candidate leaves the domain. -/
theorem noHit_false {T : ℝ} (hT : 0 < T)
    (hout : rayPt (M.pos (Qof P) x) (dirOf σb) T ∉ M.D)
    (hno : NoHit A (M.pos (Qof P) x) (dirOf σb)) : False :=
  not_noHit hGM hNF.1 (hregs.1.1 r hr) (dir_pm σb) (pos_off hGM hxe hx.1 hx.2.1.le)
    (valid_sound hGM hNF hregs hr hx hxe hv) htop (arcs_listed hNF hregs hr harr) hnear hlo hT
    hout hno


/-! ## Sizes of the region records -/


end

/-- A duplicate-free list mapped injectively into a finite set is no longer than the set. -/
theorem length_le_ncard {α β : Type*} {L : List α} (hL : L.Nodup) {f : α → β} {S : Set β}
    (hS : S.Finite) (hinj : ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) (hmem : ∀ a ∈ L, f a ∈ S) :
    L.length ≤ S.ncard := by
  classical
  have hnd : (L.map f).Nodup := List.Nodup.map_on (fun a ha b hb h => hinj a ha b hb h) hL
  have hlen : L.length = (L.map f).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hlen, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun y hy => by
    grind [Finset.mem_coe, List.mem_toFinset, List.mem_map]) hS

/-- **A region has at most as many exit-chord records as its degree.** -/
theorem chords_le_deg {Q : Polygon} (hNF : IsNF M Q N) {reg : ℕ → Set Point}
    (hregs : NFRegs M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    (N.region r).chords.length ≤ M.deg (N.F M Q) (reg r) := by
  obtain ⟨-, -, -, hRg⟩ := hregs
  obtain ⟨hmem, hnd, -, -⟩ := hRg r hr
  have hfin : {c | c ∈ N.F M Q ∧ Chazelle.Chain.TouchesIn M.D c (reg r)}.Finite :=
    hNF.1.1.subset (fun c hc => hc.1)
  refine length_le_ncard (f := fun i => (N.chord i).toSet M Q) hnd hfin
    (fun a ha b hb h => ?_) (fun a ha => ?_)
  · exact hNF.2.1 a b ((hmem a).1 ha).1 ((hmem b).1 hb).1 h
  · exact ⟨chord_toSet_mem' ((hmem a).1 ha).1, ((hmem a).1 ha).2⟩

/-- **A region has at most one more arc record than its degree.** -/
theorem arcs_le_deg {Q : Polygon} (hGM : GoodModel M) (hNF : IsNF M Q N) {reg : ℕ → Set Point}
    (hregs : NFRegs M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    (N.region r).arcs.length ≤ M.deg (N.F M Q) (reg r) + 1 := by
  obtain ⟨hRC, -, hArcs, hRg⟩ := hregs
  obtain ⟨-, -, hnd, -⟩ := hRg r hr
  obtain ⟨hfin, hcard⟩ := arcsPerRegion M Q (N.F M Q) hGM hNF.1 (reg r) (hRC.1 r hr)
  refine le_trans (length_le_ncard (f := fun j => (M.key Q (N.arc j).s, M.key Q (N.arc j).e))
    hnd hfin (fun a ha b hb h => ?_) (fun a ha => ?_)) hcard
  · obtain ⟨haN, har⟩ := (hArcs.2.2.2 r hr a).1 ha
    obtain ⟨hbN, hbr⟩ := (hArcs.2.2.2 r hr b).1 hb
    exact hArcs.2.1 a b haN hbN (har.trans hbr.symm) (Prod.mk.inj h).1
  · obtain ⟨haN, har⟩ := (hArcs.2.2.2 r hr a).1 ha
    have := (hArcs.1 a haN).2
    simp_all


/-! ## The run of the test -/

/-- The cost of a run of the test for a region with `A` arcs and `D` exit chords. -/
def testK (A D Fg : ℕ) : ℕ :=
  4 + (2 + (validK 11010 20000 5200 A D + ((shotAK Fg A + (postHitK D + 2)) + 2)))

/-- **The facts of a run of the test** from `c₀` at its end `c'`. -/
def TestFacts (P : Polygon) (M : Model) (N : NF) (c₀ c' : Config) : Prop :=
  c'.nreg 83010 ≤ 1 ∧
  (c'.nreg 83010 = 1 ↔ ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧
  c'.nreg 83011 ≤ 1 ∧ c'.nreg 83014 ≤ 1 ∧
  (c'.nreg 83011 = 1 → c'.nreg 83010 = 1) ∧ (c'.nreg 83014 = 1 → c'.nreg 83011 = 1) ∧
  (c'.nreg 83010 = 1 → ∃ (m : ℕ → ℕ) (B : ℕ) (hs : List (WPos × WPos)) (A : Set Point),
    (∀ j, j < (N.region (c₀.nreg 83002)).arcs.length →
      ShotList.arcAt m B j = nArc M (Qof P) N (c₀.nreg 83002) j) ∧
    Near M (Qof P) hs (M.pos (Qof P) (xOf c₀)) ∧
    loSet M (Qof P) m B (N.region (c₀.nreg 83002)).arcs.length hs ⊆ A ∧
    A ⊆ hiSet M (Qof P) m B (N.region (c₀.nreg 83002)).arcs.length ∧
    (c'.nreg 83011 = 1 → ∃ (t : ℝ) (f₀ : WPos),
      FirstHit A (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t ∧
      ProperPos M (Qof P) P.n f₀ ∧ f₀.edge < M.W.n ∧
      M.pos (Qof P) f₀ = rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t ∧
      ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧ c'.nreg 83012 < M.W.n ∧
      M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ = M.pos (Qof P) f₀ ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W (M.pos (Qof P) f₀)
        (dirOf (c₀.nreg 83008)) (c'.nreg 83012)
        (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)) ∧
      (M = interiorModel (Qof P) → c'.nreg 83012 = f₀.edge ∧ c'.nreg 83013 = f₀.hgt) ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀))
          (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) (chordAt N (c₀.nreg 83002) t))
          (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)
          (M.key (Qof P) (xOf c₀)) (chordAt N (c₀.nreg 83002) t))
          (N.region (c₀.nreg 83002)).chords.length) ∧
      (c'.nreg 83014 = 1 → c'.nreg 83015 = c₀.nreg 83007 ∧
        (c₀.nreg 83008 = 1 → c'.nreg 83016 = c₀.nreg 83005 ∧ c'.nreg 83017 = c'.nreg 83012) ∧
        (c₀.nreg 83008 ≠ 1 → c'.nreg 83016 = c'.nreg 83012 ∧ c'.nreg 83017 = c₀.nreg 83005))) ∧
    (c'.nreg 83011 ≠ 1 → NoHit A (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008))))

/-- The candidate of a chain model is at most at the height of the top. -/
theorem TGood.x_top {W : ℕ} {c₀ : Config} (hE : TGood P W M N c₀) :
    ∀ C : Chain, M = chainModel C → (M.pos (Qof P) (xOf c₀)).2 ≤ C.top.2 := fun C hM =>
  C.snd_le_top_of_mem_set (hE.hxC C hM)


/-- A region with an exit chord record has a nonempty chord family. -/
theorem family_ne {Q : Polygon} (hNF : IsNF M Q N) {r : ℕ} (hr : r < N.nRegions)
    (hch : (N.region r).chords ≠ []) : (N.F M Q).Nonempty := by
  obtain ⟨-, -, -, reg, -, -, -, hRg, -⟩ := hNF
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hch
  exact ⟨_, chord_toSet_mem' (((hRg r hr).1 i).1 hi).1⟩

/-- The validity bit of a run: an `NFRegs` correspondence of the normal form. -/
theorem TGood.regs {W : ℕ} {c₀ : Config} (hE : TGood P W M N c₀) :
    ∃ reg : ℕ → Set Point, NFRegs M (Qof P) N reg := by
  obtain ⟨-, -, -, reg, h1, h2, h3, h4, -⟩ := hE.hNF
  exact ⟨reg, h1, h2, h3, h4⟩

/-- **A run of the test.** -/
theorem testS_rsb {X : MemCtx} {Ok : Polygon → Model → Prop} {sh : Stmt} {Bs Bo : Finset ℕ}
    {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hXl : X.CapLocal)
    (hB8 : bRestore ∉ Bo) (hBo : oracleBands ⊆ Bo) {W : ℕ} {c₀ : Config}
    (hw : WordsBounded W c₀) (hE : TGood P W M N c₀)
    (hX : X.holds P c₀.nmem (c₀.nreg 83004) (c₀.nreg ALLOC))
    (hcap : c₀.nreg 83003 ≤ X.cap P c₀.nmem (c₀.nreg 83004)) (hOk : Ok P M)
    (hsg : M.Semigranular (N.F M (Qof P)) (c₀.nreg 83003))
    (hroom : c₀.nreg ALLOC + testK (N.region (c₀.nreg 83002)).arcs.length
      (N.region (c₀.nreg 83002)).chords.length (F (c₀.nreg 83003)) ≤ W) :
    RSB (dBands ∪ Bo) P W c₀ (testS sh) c₀ (testK (N.region (c₀.nreg 83002)).arcs.length
      (N.region (c₀.nreg 83002)).chords.length (F (c₀.nreg 83003))) (TestFacts P M N c₀) := by
  obtain ⟨c₁', k₁', ex₁, hk₁, hI₁', rf₁⟩ := tSetup_exec (P := P) hw hE.hwfMD.1
  have S1 : RSB (dBands ∪ Bo) P W c₀ tSetup c₀ 4 (fun _ => True) :=
    ⟨c₁', k₁', ex₁, by omega, hI₁', rf₁.mono Finset.subset_union_left le_rfl, trivial⟩
  unfold testK at hroom ⊢
  refine RSB.seq S1 (fun c₁ hI₁ hA₁ _ => ?_)
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (tInit_rs hE hI₁)) (fun c₂ hI₂ hA₂ h₂ => ?_)
  obtain ⟨z11, z14, ag₂⟩ := h₂
  refine RSB.seq (RSB.of_RS Finset.subset_union_left
    (valid_rs gKey_ok gLeft_ok turn_ok hE hI₂ (by omega))) (fun c₃ hI₃ hA₃ h₃ => ?_)
  obtain ⟨b10, i10, ag₃⟩ := h₃
  have y11 : c₃.nreg 83011 = 0 := by
    rw [ag₃ _ (by norm_num) (by norm_num) (by simp [validScr]), z11]
  have y14 : c₃.nreg 83014 = 0 := by
    rw [ag₃ _ (by norm_num) (by norm_num) (by simp [validScr]), z14]
  by_cases hv : c₃.nreg 83010 = 1
  · have g : c₃.nreg 83022 < c₃.nreg 83010 := by rw [hI₃.h22, hv]; omega
    have hV : ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008) := i10.1 hv
    have hne := family_ne hE.hNF hE.hr hV.1
    obtain ⟨reg, hregs⟩ := hE.regs
    refine RSB.ifT g (RSB.seq (shotA_rsb hE hI₃ hX hcap hXl hOk hne hsg hsh hBs hB8 hBo
      (by omega)) (fun c₄ hI₄ hA₄ h₄ => ?_))
    obtain ⟨⟨h11, m, B, hs, A, harr, hnear, hlo, hhi, hyes, hno⟩, e10, e14⟩ := h₄
    by_cases hh : c₄.nreg 83011 = 1
    · obtain ⟨t, hfh, hpp, hpe, hpos⟩ := hyes hh
      have g' : c₄.nreg 83022 < c₄.nreg 83011 := by rw [hI₄.h22, hh]; omega
      obtain ⟨-, -, -, p', t', hatt, hw'⟩ := hit_math hE.hGM hE.hNF hregs hE.hr hE.hxp hE.hxe hV
        hE.x_top harr hnear hlo hhi hfh
      have harrival := arrival_of_attach (dir_pm _) hfh.1 hatt hw'
      have hy : ∀ C : Chain, M = chainModel C →
          |(M.pos (Qof P) ⟨c₄.nreg 83012, c₄.nreg 83013⟩).2| < C.radius := fun C hM => by
        rw [hpos, Visibility.rayPt_snd]
        exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set (hE.hxC C hM)).2
          C.coordBound_lt_radius
      have hex : ∀ C : Chain, M = chainModel C → ∃ p t, Sweep.Arrival M.W
          (M.pos (Qof P) ⟨c₄.nreg 83012, c₄.nreg 83013⟩) (dirOf (c₀.nreg 83008)) p t :=
        fun _ _ => ⟨p', t', by rw [hpos]; exact harrival⟩
      refine RSB.ifT g' (RSB.of_RS Finset.subset_union_left
        (postHit_rs hE hI₄ hpp hpe hy hex (by omega))) |>.mono le_rfl (fun c₅ h₅ => ?_)
      obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := h₅
      have v10 : c₅.nreg 83010 = 1 := by omega
      have v11 : c₅.nreg 83011 = 1 := by rw [q10, hh]
      refine ⟨by omega, ⟨fun _ => hV, fun _ => v10⟩, by omega, q6, fun _ => v10, fun _ => v11,
        fun _ => ⟨m, B, hs, A, harr, hnear, hlo, hhi, fun _ => ⟨t, _, hfh, hpp, hpe, hpos, q1, q2,
          q3, q4, q5, q7, q8⟩, fun h => absurd v11 h⟩⟩
    · have h0 : c₄.nreg 83011 = 0 := by omega
      have g' : ¬ c₄.nreg 83022 < c₄.nreg 83011 := by omega
      refine (RSB.ifF g' (RSB.skip (K := postHitK (N.region (c₀.nreg 83002)).chords.length)
        (Q := fun c' => c' = c₄) hI₄ rfl)).mono le_rfl (fun c₅ h₅ => ?_)
      rw [h₅]
      have v10 : c₄.nreg 83010 = 1 := by rw [e10, hv]
      refine ⟨by omega, ⟨fun _ => hV, fun _ => v10⟩, by omega, by omega,
        fun h => absurd h hh, fun h => by omega,
        fun _ => ⟨m, B, hs, A, harr, hnear, hlo, hhi, fun h => absurd h hh, fun _ => hno hh⟩⟩
  · have g : ¬ c₃.nreg 83022 < c₃.nreg 83010 := by omega
    refine (RSB.ifF g (RSB.skip (K := shotAK (F (c₀.nreg 83003))
      (N.region (c₀.nreg 83002)).arcs.length +
        (postHitK (N.region (c₀.nreg 83002)).chords.length + 2))
      (Q := fun c' => c' = c₃) hI₃ rfl)).mono le_rfl (fun c₅ h₅ => ?_)
    rw [h₅]
    refine ⟨b10, i10, by omega, by omega, fun h => by omega,
      fun h => by omega, fun h => absurd h hv⟩

end

end Restore

end Chazelle.Core
