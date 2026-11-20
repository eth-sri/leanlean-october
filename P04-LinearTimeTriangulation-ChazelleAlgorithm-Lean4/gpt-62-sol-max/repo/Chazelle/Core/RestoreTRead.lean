module

public import Chazelle.Core.RestoreTEnv

/-!
# WP-E, the candidate test on the RAM, part 4: reading the normal form

The candidate test reads the arcs and the exit chords of its region from the normal form (handle
in `83001`, region in `83002`) with the readers of `SweepPrimNF`.

* `nf_bounds`: the words of a normal form readable below `E` lie below `E`.
* `callB`: a copy block followed by a statement with a `Meets … {bLocate}` contract.
* `tRegLen`, `tRegItem`, `tChordF`, `tArcF`: the reads under the run invariant.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc

/-! ## Addresses of a normal form -/

/-- A word reached through the sum of two pointers (the second one below the bound) that robustly
holds a value lies below the bound. -/
theorem robust_addr3' {E : ℕ} {m : ℕ → ℕ} {b₁ p₂ t v : ℕ} (hp₂ : p₂ < E)
    (h : Robust E m fun m' => m' (m' b₁ + m' p₂ + t) = v) : m b₁ + m p₂ + t < E := by
  have hb₁ : b₁ < E := by
    by_contra hge
    set Z := E + b₁ + m p₂ + t + 1 with hZ
    have := h (Function.update (Function.update m b₁ Z) (Z + m p₂ + t) (v + 1))
      (fun a ha => by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
    simp only at this
    rw [Function.update_of_ne (show b₁ ≠ Z + m p₂ + t by omega), Function.update_self,
      Function.update_of_ne (show p₂ ≠ Z + m p₂ + t by omega),
      Function.update_of_ne (show p₂ ≠ b₁ by omega), Function.update_self] at this
    omega
  by_contra hge
  have := h (Function.update m (m b₁ + m p₂ + t) (v + 1)) (fun a ha => by
    rw [Function.update_of_ne (by omega)])
  simp only at this
  rw [Function.update_of_ne (show b₁ ≠ m b₁ + m p₂ + t by omega),
    Function.update_of_ne (show p₂ ≠ m b₁ + m p₂ + t by omega), Function.update_self] at this
  omega

/-- **The words of a normal form readable below `E`** lie below `E`. -/
theorem nf_bounds {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) :
    B + 7 < E ∧
    (∀ i, i < N.nChords → m (B + 3) + 5 * i + 4 < E) ∧
    (∀ j, j < N.arcs.length → m (B + 4) + 5 * j + 4 < E) ∧
    (∀ r, r < N.nRegions → m (B + 5) + 5 * r + 4 < E) ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).arcs.length →
      m (B + 7) + m (m (B + 5) + 5 * r + 1) + t < E) ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      m (B + 7) + m (m (B + 5) + 5 * r + 3) + t < E) := by
  have hB : B + 11 < E := robust_addr (v := N.dec.length) fun m' hm' => (h m' hm').2.2.2.2.1
  have hreg : ∀ r, r < N.nRegions → m (B + 5) + 5 * r + 4 < E := fun r hr => by
    have := robust_addr2 (b := B + 5) (o := 5 * r + 4) (v := (N.region r).wt)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        simpa only [Nat.add_assoc] using this)
    omega
  refine ⟨by omega, fun i hi => ?_, fun j hj => ?_, hreg, fun r hr t ht => ?_,
    fun r hr t ht => ?_⟩
  · have := robust_addr2 (b := B + 3) (o := 5 * i + 4) (v := (N.chord i).dn)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        simpa only [Nat.add_assoc] using this)
    omega
  · have := robust_addr2 (b := B + 4) (o := 5 * j + 4) (v := (N.arc j).e.hgt)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.1 j hj).2.2.2.2
        simpa only [Nat.add_assoc] using this)
    omega
  · have hp := hreg r hr
    exact robust_addr3' (p₂ := m (B + 5) + 5 * r + 1) (by omega)
      (v := (N.region r).arcs.getD t 0) (fun m' hm' => by
        have e := hm' (B + 5) (by omega)
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.1 t ht
        rw [e] at this; exact this)
  · have hp := hreg r hr
    exact robust_addr3' (p₂ := m (B + 5) + 5 * r + 3) (by omega)
      (v := (N.region r).chords.getD t 0) (fun m' hm' => by
        have e := hm' (B + 5) (by omega)
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
        rw [e] at this; exact this)

/-! ## Calls of the readers -/

/-- **A copy block followed by a statement of band `bLocate`.** -/
theorem callB {p : Stmt} {K : ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop}
    (hp : Meets p {bLocate} Pre Post (fun _ _ => K))
    (l : List (ℕ × ℕ)) (hd : ∀ q ∈ l, ∀ r ∈ l, q.1 ≠ r.2) (hnd : (l.map Prod.fst).Nodup)
    (hl : ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hPre : ∀ c₁ : Config, (∀ q ∈ l, c₁.nreg q.1 = c.nreg q.2) →
      (∀ r, r ∉ l.map Prod.fst → c₁.nreg r = c.nreg r) → c₁.nmem = c.nmem → Pre P W c₁)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c₁ c' k, (∀ q ∈ l, c₁.nreg q.1 = c.nreg q.2) ∧
      (∀ r, r ∉ l.map Prod.fst → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      Exec P W (.seq (block (copies l)) p) c c' k ∧ k ≤ l.length + K ∧ Post P c₁ c' ∧
      Frame primBands c c' k := by
  obtain ⟨c₁, e₁, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) l c hw hd hnd
  have hf₁ : Frame {bLocate} c c₁ l.length := frame_copies hl h2 h3 h4 h5 h6
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := h2 ALLOC (by
    intro h
    obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h
    have := hl q hq
    unfold ALLOC at hq'; omega)
  obtain ⟨c', k, e, hk, hpost, hf⟩ := hp P W c₁ e₁.wb_right (hPre c₁ h1 h2 h4)
    (by rw [hA₁]; exact hroom)
  refine ⟨c₁, c', l.length + k, h1, h2, h4, .seq e₁ e, by simp only at hk; omega, hpost, ?_⟩
  exact (hf₁.trans hf).mono (by simp [primBands]) le_rfl

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

theorem hl_loc {l : List (ℕ × ℕ)} (h : ∀ q ∈ l, 50200 ≤ q.1 ∧ q.1 < 50210) :
    ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000 := fun q hq => ⟨by have := h q hq; omega,
  by have := h q hq; omega⟩

/-- **The length of a list of region `83002`**: `f = 0` its arcs, `f = 2` its exit chords. -/
def tRegLen (f : ℕ) : Stmt := .seq (block (copies [(50200, 83001), (50201, 83002)])) (regRd f)

theorem tRegLen_exec {f : ℕ} (hf : f = 0 ∨ f = 2) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hroom : c.nreg ALLOC + 11 ≤ W) :
    ∃ c' k, Exec P W (tRegLen f) c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = rrFld (N.region (c₀.nreg 83002)) f ∧
      TStep W c₀ c c' k := by
  have hN := hI.nfWithin hE
  have hNA := hN.holds
  have hr := hE.hr
  have r02 := hI.hin 83002 (by norm_num) (by norm_num)
  have hb := nf_bounds hN
  have hAW : c₀.nreg ALLOC ≤ W := (hI.hA.trans (hI.hw.1 ALLOC))
  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf⟩ := callB (regRd_meets (f := f)
    (by rcases hf with rfl | rfl <;> simp)) [(50200, 83001), (50201, 83002)]
    (by simp) (by simp) (hl_loc (by simp)) hI.hw (fun c₁ h1 _ hm => by
      have q0 := h1 (50200, 83001) (by simp)
      have q1 := h1 (50201, 83002) (by simp)
      simp only at q0 q1
      unfold NFRdOK
      rw [hm, q0, q1, r02]
      have := hb.2.2.2.1 _ hr
      rcases hf with rfl | rfl <;> omega) hroom
  have q0 := h1 (50200, 83001) (by simp)
  have q1 := h1 (50201, 83002) (by simp)
  simp only at q0 q1
  refine ⟨c', k, ex, by simp at hk; omega, ?_, hI.prim ex.wb_right hf⟩
  rw [hpost N (by rw [hm1, q0]; exact hNA) (by rw [q1, r02]; exact hr), q1, r02]

/-- **Item `t` (register `tr`) of a list of region `83002`**: `f = 1` its arcs, `f = 3` its exit
chords. -/
def tRegItem (f tr : ℕ) : Stmt :=
  .seq (block (copies [(50200, 83001), (50201, 83002), (50202, tr)])) (nfLst f)

theorem nfLst_meets (f : ℕ) : Meets (nfLst f) {bLocate}
    (fun _ W c => NFLstOK f W c)
    (fun _ c c' => c'.nreg 50210 =
      c.nmem (c.nmem (c.nreg 50200 + 7) + nfVal 5 5 f c + c.nreg 50202))
    (fun _ _ => 17) := by
  intro P W c hw h _
  obtain ⟨c', j, e, hj, v, fr⟩ := nfLst_exec (P := P) f c hw h
  exact ⟨c', j, e, by show _ ≤ 17; omega, v, Bidx_frame fr _⟩

theorem tRegItem_exec {f tr : ℕ} (hf : f = 1 ∨ f = 3) (htr : InR tr) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c)
    (ht : c.nreg tr < if f = 1 then (N.region (c₀.nreg 83002)).arcs.length
      else (N.region (c₀.nreg 83002)).chords.length)
    (hroom : c.nreg ALLOC + 17 ≤ W) :
    ∃ c' k, Exec P W (tRegItem f tr) c c' k ∧ k ≤ 20 ∧
      c'.nreg 50210 = (if f = 1 then (N.region (c₀.nreg 83002)).arcs
        else (N.region (c₀.nreg 83002)).chords).getD (c.nreg tr) 0 ∧
      TStep W c₀ c c' k := by
  unfold InR at htr
  have hN := hI.nfWithin hE
  have hNA := hN.holds
  have hr := hE.hr
  have r02 := hI.hin 83002 (by norm_num) (by norm_num)
  have hb := nf_bounds hN
  have hAW : c₀.nreg ALLOC ≤ W := (hI.hA.trans (hI.hw.1 ALLOC))
  have hl : [(50200, 83001), (50201, 83002), (50202, tr)].map Prod.fst = [50200, 50201, 50202] :=
    rfl
  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf'⟩ := callB (nfLst_meets f)
    [(50200, 83001), (50201, 83002), (50202, tr)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro q (rfl | rfl | rfl) s (rfl | rfl | rfl) <;>
        simp only <;> omega)
    (by rw [hl]; decide) (hl_loc (by simp)) hI.hw (fun c₁ h1 _ hm => by
      have q0 := h1 (50200, 83001) (by simp)
      have q1 := h1 (50201, 83002) (by simp)
      have q2 := h1 (50202, tr) (by simp)
      simp only at q0 q1 q2
      unfold NFLstOK NFRdOK nfVal
      rw [hm, q0, q1, q2, r02]
      have h5 := hb.2.2.2.1 _ hr
      rcases hf with rfl | rfl
      · rw [ite_eq_left rfl] at ht
        have := hb.2.2.2.2.1 _ hr _ ht
        refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      · rw [ite_eq_right (by decide)] at ht
        have := hb.2.2.2.2.2 _ hr _ ht
        refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩) hroom
  have q0 := h1 (50200, 83001) (by simp)
  have q1 := h1 (50201, 83002) (by simp)
  have q2 := h1 (50202, tr) (by simp)
  simp only at q0 q1 q2
  refine ⟨c', k, ex, by simp at hk; omega, ?_, hI.prim ex.wb_right hf'⟩
  rw [hpost]
  unfold nfVal
  rw [hm1, q0, q1, q2, r02]
  have hR := hNA.2.2.2.2.2.2.2.1 _ hr
  rcases hf with rfl | rfl
  · rw [ite_eq_left rfl] at ht ⊢
    exact hR.2.2.2.1 _ ht
  · rw [ite_eq_right (by decide)] at ht ⊢
    exact hR.2.2.2.2 _ ht

/-- **Field `f` of chord `i` (register `ir`).** -/
def tChordF (f ir : ℕ) : Stmt := .seq (block (copies [(50200, 83001), (50201, ir)])) (chordRd f)

theorem tChordF_exec {f ir : ℕ} (hf : f < 5) (hir : InR ir) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hi : c.nreg ir < N.nChords) (hroom : c.nreg ALLOC + 11 ≤ W) :
    ∃ c' k, Exec P W (tChordF f ir) c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = crFld (N.chord (c.nreg ir)) f ∧
      TStep W c₀ c c' k := by
  unfold InR at hir
  have hN := hI.nfWithin hE
  have hNA := hN.holds
  have hb := nf_bounds hN
  have hAW : c₀.nreg ALLOC ≤ W := (hI.hA.trans (hI.hw.1 ALLOC))
  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf'⟩ := callB (chordRd_meets hf)
    [(50200, 83001), (50201, ir)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro q (rfl | rfl) s (rfl | rfl) <;>
        simp only <;> omega)
    (by simp) (hl_loc (by simp)) hI.hw (fun c₁ h1 _ hm => by
      have q0 := h1 (50200, 83001) (by simp)
      have q1 := h1 (50201, ir) (by simp)
      simp only at q0 q1
      unfold NFRdOK
      rw [hm, q0, q1]
      have := hb.2.1 _ hi
      omega) hroom
  have q0 := h1 (50200, 83001) (by simp)
  have q1 := h1 (50201, ir) (by simp)
  simp only at q0 q1
  refine ⟨c', k, ex, by simp at hk; omega, ?_, hI.prim ex.wb_right hf'⟩
  rw [hpost N (by rw [hm1, q0]; exact hNA) (by rw [q1]; exact hi), q1]

/-- **Field `f` of arc `j` (register `jr`).** -/
def tArcF (f jr : ℕ) : Stmt := .seq (block (copies [(50200, 83001), (50201, jr)])) (arcRd f)

theorem tArcF_exec {f jr : ℕ} (hf : f < 5) (hjr : InR jr) (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hj : c.nreg jr < N.arcs.length) (hroom : c.nreg ALLOC + 11 ≤ W) :
    ∃ c' k, Exec P W (tArcF f jr) c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = arFld (N.arc (c.nreg jr)) f ∧
      TStep W c₀ c c' k := by
  unfold InR at hjr
  have hN := hI.nfWithin hE
  have hNA := hN.holds
  have hb := nf_bounds hN
  have hAW : c₀.nreg ALLOC ≤ W := (hI.hA.trans (hI.hw.1 ALLOC))
  obtain ⟨c₁, c', k, h1, -, hm1, ex, hk, hpost, hf'⟩ := callB (arcRd_meets hf)
    [(50200, 83001), (50201, jr)]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro q (rfl | rfl) s (rfl | rfl) <;>
        simp only <;> omega)
    (by simp) (hl_loc (by simp)) hI.hw (fun c₁ h1 _ hm => by
      have q0 := h1 (50200, 83001) (by simp)
      have q1 := h1 (50201, jr) (by simp)
      simp only at q0 q1
      unfold NFRdOK
      rw [hm, q0, q1]
      have := hb.2.2.1 _ hj
      omega) hroom
  have q0 := h1 (50200, 83001) (by simp)
  have q1 := h1 (50201, jr) (by simp)
  simp only at q0 q1
  refine ⟨c', k, ex, by simp at hk; omega, ?_, hI.prim ex.wb_right hf'⟩
  rw [hpost N (by rw [hm1, q0]; exact hNA) (by rw [q1]; exact hj), q1]

end

end Restore

end Chazelle.Core
