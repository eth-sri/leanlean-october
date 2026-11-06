module

public import Chazelle.Core.DownPhaseDrvRBSort
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 2000000

/-!
# Down-phase driver (RAM side): sorting every bucket

After the bucket distribution (`bktS`), `bsLoop` sorts the segment of every bucket `b ≤ A`
(`[bstart b, bstart (b + 1))` of the array `R`) in place by the event comparator (`sortBack`).
With buckets ordered by the comparator (`b q < b q' → codeLe (base + q) (base + q')`), the whole
array is then sorted (`bsLoop_exec`): a `codeLe`-sorted permutation of the new codes.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-! ## The program -/

/-- One bucket: its start and length, sort in place, next bucket. -/
def bsBody : Stmt :=
  .seq (block [.addN 210057 210037 210050, .loadN 210052 210057, .addN 210057 210036 210050,
      .loadN 210053 210057, .subN 210054 210053 210052, .addN 210055 210048 210052])
    (.seq sortBack (.instr (.addN 210050 210050 210034)))

/-- **Sort every bucket.** -/
def bsLoop : Stmt := .whileLtN 210050 210039 bsBody

/-! ## Lists -/

/-- The array split into its buckets. -/
theorem seg_flat (bk m : ℕ → ℕ) (n R : ℕ) :
    ∀ b, seg m R (bstart bk n b) =
      (List.range b).flatMap fun b' => seg m (R + bstart bk n b') (bcnt bk n b') := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih => rws [bstart_succ, seg_add, ih, List.range_succ, List.flatMap_append]

/-- The bucket segments of `bktList`. -/
theorem seg_bkt {m : ℕ → ℕ} {bk : ℕ → ℕ} {n A base R : ℕ} (hA : ∀ q, q < n → bk q ≤ A)
    (h : seg m R n = bktList bk n A base) {b : ℕ} (hb : b ≤ A) :
    seg m (R + bstart bk n b) (bcnt bk n b) = (bfilt bk n b).map (base + ·) := by
  have hn := bstart_all hA
  have hl := seg_flat bk m n R (A + 1)
  rw [hn, h] at hl
  unfold bktList at hl
  have hle : b + 1 ≤ A + 1 := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  -- split both sides at bucket `b`
  have hsplit : ∀ (f : ℕ → List ℕ), (List.range (A + 1)).flatMap f =
      (List.range b).flatMap f ++ f b ++ ((List.range d).map (b + 1 + ·)).flatMap f := by
    intro f
    rw [hd, List.range_add, List.range_succ, List.flatMap_append, List.flatMap_append]
    simp
  rw [hsplit, hsplit] at hl
  have hlen : ((List.range b).flatMap fun b' => (bfilt bk n b').map (base + ·)).length =
      ((List.range b).flatMap fun b' => seg m (R + bstart bk n b') (bcnt bk n b')).length := by
    rw [← seg_flat, seg_length]
    have := bktPre_length (bk := bk) n b base
    unfold bktPre at this; rw [this]
  have hlen2 : (seg m (R + bstart bk n b) (bcnt bk n b)).length =
      ((bfilt bk n b).map (base + ·)).length := by rwr [seg_length, List.length_map]
  rw [List.append_assoc, List.append_assoc] at hl
  have h1 := List.append_inj hl hlen
  exact (List.append_inj h1.2 hlen2.symm).1.symm

/-! ## The loop -/

/-- The band-`bDownDrv` registers the bucket loop writes. -/
def Bbl (r : ℕ) : Bool := decide (210050 ≤ r ∧ r ≤ 210059)

theorem wrM_bs1 : wrM Bbl (block [.addN 210057 210037 210050, .loadN 210052 210057,
    .addN 210057 210036 210050, .loadN 210053 210057, .subN 210054 210053 210052,
    .addN 210055 210048 210052]) = true := by decide

/-- The fixed data of the bucket loop: the model descriptor, the chord list `L` with its event
records, the arrays of the bucket distribution. -/
structure BsEnv (P : Polygon) (W : ℕ) (m₁ : ℕ → ℕ) (bk : ℕ → ℕ) (n A base Cb Sb Rb D T : ℕ)
    (M : Model) (L : List (ℕ × ℕ × ℕ)) : Prop where
  good : GoodEnv P
  hw : hostWords P.n ≤ W
  bkA : ∀ q, q < n → bk q ≤ A
  hS : Sb = Cb + (A + 1)
  hR : Rb = Sb + (A + 1)
  cnt : ∀ b, b ≤ A → m₁ (Cb + b) = bstart bk n (b + 1)
  st : ∀ b, b ≤ A → m₁ (Sb + b) = bstart bk n b
  wf : ModelDescWF P Cb m₁ D
  desc : ModelDescAt m₁ D (Qof P) M
  ok : ChordTriplesOK M (Qof P) L
  recs : RecsAt m₁ T L
  hT : T + 8 * L.length ≤ Cb
  codes : base + n ≤ 2 * L.length

/-- The invariant of the bucket loop. -/
structure BsI (P : Polygon) (W : ℕ) (c₀ : Config) (m₁ : ℕ → ℕ) (bk : ℕ → ℕ)
    (n A base Cb Sb Rb D T : ℕ) (M : Model) (L : List (ℕ × ℕ × ℕ)) (j : ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  r34 : d.nreg 210034 = 1
  r36 : d.nreg 210036 = Cb
  r37 : d.nreg 210037 = Sb
  r39 : d.nreg 210039 = A + 1
  r48 : d.nreg 210048 = Rb
  r50 : d.nreg 210050 = j
  r40 : d.nreg 40000 = D
  r42 : d.nreg 42000 = T
  r42' : d.nreg 42001 = 2 * L.length
  alloc : Rb + n ≤ d.nreg ALLOC
  low : ∀ a, a < Rb → d.nmem a = m₁ a
  done : ∀ b, b < j → (seg d.nmem (Rb + bstart bk n b) (bcnt bk n b)).Perm
    ((bfilt bk n b).map (base + ·)) ∧
    (seg d.nmem (Rb + bstart bk n b) (bcnt bk n b)).Pairwise (BuildNF.codeLe M (Qof P) L)
  todo : ∀ b, j ≤ b → b ≤ A →
    seg d.nmem (Rb + bstart bk n b) (bcnt bk n b) = (bfilt bk n b).map (base + ·)
  fr : ∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bbl r = false → r ≠ ALLOC →
    d.nreg r = c₀.nreg r
  r43 : ∀ r, 43000 ≤ r → r < 44000 → d.nreg r = c₀.nreg r
  rr : ∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bbl r = false →
    d.rreg r = c₀.rreg r
  rm : ∀ a, a < Rb + n → d.rmem a = c₀.rmem a
  out : d.output = c₀.output

/-- The cost of one bucket. -/
def bsCost (bk : ℕ → ℕ) (n b : ℕ) : ℕ := SortR.sortCost 11010 (bcnt bk n b) + 7 * bcnt bk n b + 12

section exec

variable {P : Polygon} {W : ℕ}

theorem bsBody_exec {c₀ : Config} {m₁ bk : ℕ → ℕ} {n A base Cb Sb Rb D T : ℕ} {M : Model}
    {L : List (ℕ × ℕ × ℕ)} (E : BsEnv P W m₁ bk n A base Cb Sb Rb D T M L) {j : ℕ} (hj : j < A + 1)
    {d : Config} (I : BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L j d)
    (hroom : d.nreg ALLOC + bsCost bk n j + 1 ≤ W) :
    ∃ d' k, Exec P W bsBody d d' k ∧ BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L (j + 1) d' ∧
      k ≤ bsCost bk n j ∧ d'.nreg ALLOC ≤ d.nreg ALLOC + bsCost bk n j := by
  have hst := E.st j (by omega)
  have hcn := E.cnt j (by omega)
  have hSb : Sb + j < Rb := by rwo [E.hR]
  have hCb : Cb + j < Rb := by rwo [E.hR, E.hS]
  have hl1 := I.low _ hSb
  have hl2 := I.low _ hCb
  have hbn := bstart_le (bk := bk) E.bkA (show j + 1 ≤ A + 1 by omega)
  have hsucc := bstart_succ (bk := bk) n j
  have hW : Rb + n + 1 ≤ W := by have := I.alloc; omega
  -- the bucket's segment
  obtain ⟨d₁, k₁, e₁, hk₁, v55, v54, v50, hm₁, hf₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 210057 210037 210050,
      .loadN 210052 210057, .addN 210057 210036 210050, .loadN 210053 210057,
      .subN 210054 210053 210052, .addN 210055 210048 210052]) d d₁ k₁ ∧ k₁ = 6 ∧
      d₁.nreg 210055 = Rb + bstart bk n j ∧ d₁.nreg 210054 = bcnt bk n j ∧
      d₁.nreg 210050 = j ∧ d₁.nmem = d.nmem ∧ FrameM Bbl d d₁ := by
    obtain ⟨d₁, k₁, e₁, hk₁, v55, v54, v50, hm₁⟩ : ∃ d₁ k₁, Exec P W
        (block [.addN 210057 210037 210050,
        .loadN 210052 210057, .addN 210057 210036 210050, .loadN 210053 210057,
        .subN 210054 210053 210052, .addN 210055 210048 210052]) d d₁ k₁ ∧ k₁ = 6 ∧
        d₁.nreg 210055 = Rb + bstart bk n j ∧ d₁.nreg 210054 = bcnt bk n j ∧
        d₁.nreg 210050 = j ∧ d₁.nmem = d.nmem := by
      have w := I.wb
      exec_block
      all_goals try (config_simp; (try simp only [I.r37, I.r50, I.r36, I.r48, hl1, hl2, hst, hcn]); omega)
      refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;>
        simp only [I.r37, I.r50, I.r36, I.r48, hl1, hl2, hst, hcn]; omega
    exact ⟨d₁, k₁, e₁, hk₁, v55, v54, v50, hm₁, exec_frameM e₁ wrM_bs1⟩
  have g₁  := hf₁.1
  have w₁ := e₁.wb_right
  have hlow₁ : ∀ a, a < Rb → d₁.nmem a = m₁ a := fun a ha => by rw [hm₁]; exact I.low a ha
  obtain ⟨hM₁, hwf₁⟩ := desc_agree E.wf E.desc (m' := d₁.nmem) fun a ha => hlow₁ a (by
    rwo [E.hR, E.hS])
  have hrec₁ : RecsAt d₁.nmem T L := fun c hc => by
    obtain ⟨a1, a2, a3, a4⟩ := E.recs c hc
    have hT := E.hT
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hlow₁ _ (by rwo [E.hR, E.hS])] <;> assumption
  have hA₁ : d₁.nreg ALLOC = d.nreg ALLOC := g₁ _ (by decide)
  have hseg₁ : seg d₁.nmem (Rb + bstart bk n j) (bcnt bk n j) = (bfilt bk n j).map (base + ·) := by
    rw [hm₁]; exact I.todo j le_rfl (by omega)
  -- sort the segment
  obtain ⟨d₂, k₂, e₂, hk₂, w₂, hperm, hsort, hm₂, hA₂, hA₂', g₂, rr₂, rm₂, o₂, v40, v42, v42', v43⟩ :=
    sortBack_exec (P := P) (W := W) E.good E.hw d₁ w₁ (X := Rb + bstart bk n j)
      (len := bcnt bk n j) (D := D) (T := T) (M := M) (L := L) v55 v54
      (by rw [g₁ _ (by decide)]; exact I.r34) (by rw [g₁ _ (by decide)]; exact I.r40)
      (by rw [g₁ _ (by decide)]; exact I.r42) (by rw [g₁ _ (by decide)]; exact I.r42')
      (hwf₁.mono (by have := I.alloc; rwo [hA₁, E.hR, E.hS] at *)) hM₁ E.ok hrec₁
      (by have := I.alloc; rw [hA₁]; rw [E.hR, E.hS] at this; have := E.hT; omega)
      (by rw [hA₁]; have := I.alloc; omega)
      (by rw [hseg₁]; intro x hx; rw [List.mem_map] at hx
          obtain ⟨q, hq, rfl⟩ := hx; rw [mem_bfilt] at hq; have := E.codes; omega)
      (by ruo [hA₁] bsCost at hroom)
  -- the next bucket
  have b21 : ∀ r, 210000 ≤ r → r < 220000 → bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) :=
    fun r h1 h2 => by sio [bandOf, bSort, bSign, bBuild]
  have v50₂ : d₂.nreg 210050 = j := by
    rw [g₂ _ (b21 _ (by norm_num) (by norm_num)) (by decide) (by decide), v50]
  have v34₂ : d₂.nreg 210034 = 1 := by
    rw [g₂ _ (b21 _ (by norm_num) (by norm_num)) (by decide) (by decide), g₁ _ (by decide), I.r34]
  have e₃ := Exec.addN (P := P) w₂ 210050 210050 210034 (by rwo [v50₂, v34₂])
  set d₃ : Config := { d₂ with nreg := upd d₂.nreg 210050 (d₂.nreg 210050 + d₂.nreg 210034) }
    with hd₃
  have g₃ : ∀ r, r ≠ 210050 → d₃.nreg r = d₂.nreg r := fun r hr => by rw [hd₃]; simp [hr]
  have bcb : ∀ r, Bbl r = false → Bcb r = false := fun r hb => by
    simp only [Bbl, decide_eq_false_iff_not] at hb
    sio only [Bcb, decide_eq_false_iff_not]
  -- registers of band `bDownDrv` other than the loop's
  have k21 : ∀ r, 210000 ≤ r → r < 220000 → Bbl r = false → d₃.nreg r = d.nreg r := by
    intro r h1 h2 hb
    rw [g₃ r (by intro h; subst h; simp [Bbl] at hb), g₂ r (b21 r h1 h2) (bcb r hb)
      (by ufo ALLOC), g₁ r hb]
  have hst'  := hsucc.symm
  refine ⟨d₃, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), ?_, by ufo bsCost,
    by ruo [show d₃.nreg ALLOC = d₂.nreg ALLOC from g₃ _ (by decide)] bsCost⟩
  refine ⟨e₃.wb_right, by rw [k21 _ (by norm_num) (by norm_num) (by decide)]; exact I.r34,
    by rw [k21 _ (by norm_num) (by norm_num) (by decide)]; exact I.r36,
    by rw [k21 _ (by norm_num) (by norm_num) (by decide)]; exact I.r37,
    by rw [k21 _ (by norm_num) (by norm_num) (by decide)]; exact I.r39,
    by rw [k21 _ (by norm_num) (by norm_num) (by decide)]; exact I.r48, ?_,
    by rwx [g₃ _ (by decide)], by rwx [g₃ _ (by decide)],
    by rwx [g₃ _ (by decide)],
    by rw [show d₃.nreg ALLOC = d₂.nreg ALLOC from g₃ _ (by decide)]; have := I.alloc; omega,
    fun a ha => ?_, fun b hb => ?_, fun b hb1 hb2 => ?_, fun r hr hb hra => ?_,
    fun r h1 h2 => ?_, fun r hr hb => ?_, fun a ha => ?_, ?_⟩
  · rw [hd₃]; simp only [Machine.upd_same]
    rw [v50₂, v34₂]
  · show d₂.nmem a = m₁ a
    rw [hm₂ a (by rw [hA₁]; have := I.alloc; omega) (Or.inl (by omega)), hlow₁ a ha]
  · show (seg d₂.nmem (Rb + bstart bk n b) (bcnt bk n b)).Perm _ ∧ _
    rcases Nat.lt_or_ge b j with hbj | hbj
    · have hcong : seg d₂.nmem (Rb + bstart bk n b) (bcnt bk n b) =
          seg d.nmem (Rb + bstart bk n b) (bcnt bk n b) := by
        apply seg_congr; intro i hi
        have h1 := bstart_mono (bk := bk) n (show b + 1 ≤ j by omega)
        rw [bstart_succ] at h1
        have h2 := bstart_le (bk := bk) E.bkA (show j ≤ A + 1 by omega)
        have h3 := I.alloc
        have h4 : Rb + bstart bk n b + i < d₁.nreg ALLOC := by rwo [hA₁]
        rw [hm₂ _ h4 (Or.inl (by omega)), hm₁]
      rw [hcong]; exact I.done b hbj
    · have hbj' : b = j := by omega
      subst hbj'
      rw [← hseg₁]; exact ⟨hperm, hsort⟩
  · show seg d₂.nmem _ _ = _
    have hcong : seg d₂.nmem (Rb + bstart bk n b) (bcnt bk n b) =
        seg d.nmem (Rb + bstart bk n b) (bcnt bk n b) := by
      apply seg_congr; intro i hi
      have h1 := bstart_mono (bk := bk) n (show j + 1 ≤ b by omega)
      have h2 := bstart_le (bk := bk) E.bkA (show b + 1 ≤ A + 1 by omega)
      rw [bstart_succ] at h2
      have h3 := I.alloc
      have h4 : Rb + bstart bk n b + i < d₁.nreg ALLOC := by rwo [hA₁]
      rw [hm₂ _ h4 (Or.inr (by omega)), hm₁]
    rw [hcong]; exact I.todo b (by omega) hb2
  · have hr50 : r ≠ 210050 := fun h => by subst h; simp [Bbl] at hb
    rw [g₃ r hr50, g₂ r hr (bcb r hb) hra, g₁ r hb]
    exact I.fr r hr hb hra
  · rw [g₃ r (by omega), v43 r h1 h2, g₁ r (by sio [Bbl])]; exact I.r43 r h1 h2
  · show d₂.rreg r = _
    rw [rr₂ r hr (bcb r hb), hf₁.2.1 r hb]
    exact I.rr r hr hb
  · show d₂.rmem a = _
    rw [rm₂ a (by rw [hA₁]; have := I.alloc; omega), hf₁.2.2.1]; exact I.rm a ha
  · show d₂.output = _
    rw [o₂, hf₁.2.2.2]; exact I.out

/-- **The bucket loop.** -/
theorem bsLoop_exec {c₀ : Config} {m₁ bk : ℕ → ℕ} {n A base Cb Sb Rb D T : ℕ} {M : Model}
    {L : List (ℕ × ℕ × ℕ)} (E : BsEnv P W m₁ bk n A base Cb Sb Rb D T M L)
    {d : Config} (I : BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L 0 d)
    (hroom : d.nreg ALLOC + (∑ b ∈ Finset.range (A + 1), bsCost bk n b) + 1 ≤ W) :
    ∃ d' k, Exec P W bsLoop d d' k ∧ BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L (A + 1) d' ∧
      k ≤ (∑ b ∈ Finset.range (A + 1), (bsCost bk n b + 2)) + 2 ∧
      d'.nreg ALLOC ≤ d.nreg ALLOC + ∑ b ∈ Finset.range (A + 1), bsCost bk n b := by
  obtain ⟨d', k, ex, ⟨hI, hA⟩, hk⟩ := forLoopSum (P := P) (W := W) (ir := 210050) (nr := 210039)
    (fun j e => BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L j e ∧
      e.nreg ALLOC ≤ d.nreg ALLOC + ∑ b ∈ Finset.range j, bsCost bk n b)
    (bsCost bk n) (A + 1)
    (fun j e ⟨h, _⟩ => ⟨h.wb, h.r50, h.r39⟩)
    (fun j e hj ⟨h, hA⟩ => by
      have hsum : ∑ b ∈ Finset.range (j + 1), bsCost bk n b ≤
          ∑ b ∈ Finset.range (A + 1), bsCost bk n b :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      rw [Finset.sum_range_succ] at hsum
      obtain ⟨e', k, ex, h', hk, hA'⟩ := bsBody_exec E (by omega) h (by omega)
      exact ⟨e', k, ex, ⟨h', by rwo [Finset.sum_range_succ]⟩, hk⟩)
    (j := 0) ⟨I, by simp⟩ (Nat.zero_le _)
  refine ⟨d', k, ex, hI, by rwx [Finset.range_eq_Ico], hA⟩

/-- **The sorted new codes**: with the buckets ordered by the comparator, the array is a sorted
permutation of the new codes. -/
theorem bs_result {c₀ : Config} {m₁ bk : ℕ → ℕ} {n A base Cb Sb Rb D T : ℕ} {M : Model}
    {L : List (ℕ × ℕ × ℕ)} (E : BsEnv P W m₁ bk n A base Cb Sb Rb D T M L) {d : Config}
    (I : BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L (A + 1) d)
    (hmono : ∀ q q', q < n → q' < n → bk q < bk q' →
      BuildNF.codeLe M (Qof P) L (base + q) (base + q')) :
    (seg d.nmem Rb n).Perm ((List.range n).map (base + ·)) ∧
      (seg d.nmem Rb n).Pairwise (BuildNF.codeLe M (Qof P) L) := by
  have hn := bstart_all E.bkA
  have hflat := seg_flat bk d.nmem n Rb (A + 1)
  rw [hn] at hflat
  rw [hflat]
  constructor
  · -- permutation
    have h1 : ((List.range (A + 1)).flatMap fun b => seg d.nmem (Rb + bstart bk n b) (bcnt bk n b)).Perm
        (bktList bk n A base) :=
      List.Perm.flatMap_left _ fun b hb => (I.done b (List.mem_range.1 hb)).1
    refine h1.trans ?_
    -- `bktList` is a permutation of the codes
    have h2 : (bktList bk n A base).Perm ((List.range n).map (base + ·)) := by
      refine (List.perm_ext_iff_of_nodup ?_ ?_).2 fun x => ?_
      · unfold bktList
        rw [List.nodup_flatMap]
        refine ⟨fun b _ => ?_, ?_⟩
        · exact ((List.nodup_range).filter _).map (fun a b h => by omega)
        · refine List.pairwise_lt_range.imp fun {b b'} hbb => ?_
          show List.Disjoint _ _
          rw [List.disjoint_left]
          intro x hx hx'
          rw [List.mem_map] at hx hx'
          obtain ⟨q, hq, rfl⟩ := hx
          obtain ⟨q', hq', hqq⟩ := hx'
          rw [mem_bfilt] at hq hq'
          have : q' = q := by omega
          subst this; omega
      · exact (List.nodup_range).map (fun a b h => by omega)
      · unfold bktList
        simp only [List.mem_flatMap, List.mem_range, List.mem_map, mem_bfilt]
        constructor
        · rintro ⟨b, -, q, ⟨hq, -⟩, rfl⟩; exact ⟨q, hq, rfl⟩
        · rintro ⟨q, hq, rfl⟩
          exact ⟨bk q, by have := E.bkA q hq; omega, q, ⟨hq, rfl⟩, rfl⟩
    exact h2
  · -- sortedness
    rw [List.pairwise_flatMap]
    refine ⟨fun b hb => (I.done b (List.mem_range.1 hb)).2, ?_⟩
    refine List.pairwise_lt_range.imp_of_mem fun {b b'} hb hb' hbb x hx y hy => ?_
    have hx' := (I.done b (List.mem_range.1 hb)).1.mem_iff.1 hx
    have hy' := (I.done b' (List.mem_range.1 hb')).1.mem_iff.1 hy
    rw [List.mem_map] at hx' hy'
    obtain ⟨q, hq, rfl⟩ := hx'
    obtain ⟨q', hq', rfl⟩ := hy'
    rw [mem_bfilt] at hq hq'
    exact hmono q q' hq.1 hq'.1 (by rwx [hq.2, hq'.2])

end exec

end

end DrvR

end Chazelle.Core
