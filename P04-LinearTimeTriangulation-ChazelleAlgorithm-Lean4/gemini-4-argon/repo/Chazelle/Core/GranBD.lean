module

public import Chazelle.Core.GranOut

/-!
# WP-F, part 17: normal form and decomposition of the result

`bdStmt sB sD` builds the normal form of the chord list at `r28` (length `r95`) with a
normal-form construction `sB` (`BuildNFSpec`) and decomposes it with `sD` (`DecompSpec`); the
handle is left in `r90004` (`bd_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The contract of a normal-form construction (the body of `BuildNFSpec`). -/
def BuildOK (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bBuild 0) ∧
      ∃ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem (rd c bBuild 1) L ∧ ChordTriplesOK M (Qof P) L)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem (rd c bBuild 1) L →
        ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem (rd c' bBuild 3) (c'.nreg ALLOC) N ∧
          IsNF M (Qof P) N ∧ N.chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ N.dec = [])
    (fun _ c => κ * (rd c bBuild 2 * (Nat.clog 2 (rd c bBuild 2) + 1) + 1))

/-- The contract of a decomposition (the body of `DecompSpec`). -/
def DecompOK (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bDecomp}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bDecomp 0) ∧
      ∃ M N, ModelDescAt c.nmem (rd c bDecomp 0) (Qof P) M ∧
      GoodModel M ∧ NFWithin c.nmem (rd c bDecomp 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
      M.DegLe (N.F M (Qof P)) (rd c bDecomp 2))
    (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bDecomp 0) (Qof P) M →
      NFAt c.nmem (rd c bDecomp 1) N → IsNF M (Qof P) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bDecomp 3 ∧
          NFWithin c'.nmem (rd c' bDecomp 3) (c'.nreg ALLOC) N' ∧
          N'.chords = N.chords ∧ N'.arcs = N.arcs ∧ N'.regions = N.regions ∧ N'.seq = N.seq ∧
          IsDecomp N' (decDepth (rd c bDecomp 2) N.nChords))
    (fun _ c => κ * (rd c bDecomp 2 + 1) *
      (c.nmem (rd c bDecomp 1) * (Nat.clog 2 (c.nmem (rd c bDecomp 1)) + 1) + 1))

theorem buildOK_of (h : BuildNFSpec) : ∃ s κ, BuildOK s κ := h

theorem decompOK_of (h : DecompSpec) : ∃ s κ, DecompOK s κ := h

/-- The chords of a list of triples. -/
def lset (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : Set (Set Point) :=
  {c | ∃ x ∈ L, c = (recOf x).toSet M Q}

/-- Validity does not depend on the decomposition. -/
theorem isNF_congr {M : Model} {Q : Polygon} {N N' : NF} (h : IsNF M Q N)
    (h1 : N'.chords = N.chords) (h2 : N'.arcs = N.arcs) (h3 : N'.regions = N.regions)
    (h4 : N'.seq = N.seq) : IsNF M Q N' := by
  obtain ⟨c, a, r, s, d, ro, l⟩ := N
  obtain ⟨c', a', r', s', d', ro', l'⟩ := N'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  exact h

theorem F_congr {M : Model} {Q : Polygon} {N N' : NF} (h : N'.chords = N.chords) :
    N'.F M Q = N.F M Q := by
  unfold NF.F; rw [h]

theorem F_of_map {M : Model} {Q : Polygon} {N : NF} {L : List (ℕ × ℕ × ℕ)}
    (h : N.chords.map (fun r => (r.h, r.lp, r.rp)) = L) : N.F M Q = lset M Q L := by
  subst h
  ext c
  simp only [NF.F, lset, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rfl⟩

/-- A frame from a register-only change. -/
theorem frame_of {B : Finset ℕ} {c c' : Config} {k : ℕ}
    (hr : ∀ r, bandOf r ∉ B → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output)
    (hA : bandOf ALLOC ∉ B) : Frame B c c' k := by
  have := hr ALLOC hA
  exact ⟨fun r h _ => hr r h, fun r _ => by rw [hrr], fun a _ => by rw [hm],
    fun a _ => by rw [hrm], ho, by omega, by omega⟩

/-- Build then decompose. -/
def bdStmt (sB sD : Stmt) : Stmt :=
  .seq (block [.copyN 40000 90000, .copyN 40001 90028, .copyN 40002 90095])
    (.seq sB (.seq (block [.copyN 60000 90000, .copyN 60001 40003, .copyN 60002 90002])
      (.seq sD (block [.copyN 90004 60003]))))

/-- The cost of `bdStmt` for `x` chords. -/
def costBD (κB κD D x : ℕ) : ℕ :=
  7 + κB * (x * (Nat.clog 2 x + 1) + 1) + κD * (D + 1) * (x * (Nat.clog 2 x + 1) + 1)

theorem copy3_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (hb₂ : b₂ ≠ a₁) (hb₃ : b₃ ≠ a₁) (hb₃' : b₃ ≠ a₂) :
    ∃ c' k, Exec P W (block [.copyN a₁ b₁, .copyN a₂ b₂, .copyN a₃ b₃]) c c' k ∧ k = 3 ∧
      c'.nreg a₁ = c.nreg b₁ ∧ c'.nreg a₂ = c.nreg b₂ ∧ c'.nreg a₃ = c.nreg b₃ ∧
      (∀ r, r ≠ a₁ → r ≠ a₂ → r ≠ a₃ → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r x1 x2 x3 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem copy1_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (a b : ℕ) :
    ∃ c' k, Exec P W (block [.copyN a b]) c c' k ∧ k = 1 ∧ c'.nreg a = c.nreg b ∧
      (∀ r, r ≠ a → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, fun r x1 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem band_not {r b : ℕ} {B : Finset ℕ} (hr : bandOf r = b) (hb : b ∈ B) :
    ¬ bandOf r ∉ B := fun h => h (hr ▸ hb)

set_option maxHeartbeats 1000000 in
/-- **Normal form and decomposition of the result.** -/
theorem bd_exec {sB sD : Stmt} {κB κD : ℕ} (hsB : BuildOK sB κB) (hsD : DecompOK sD κD)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) {MD D LB : ℕ} {M : Model} {L : List (ℕ × ℕ × ℕ)}
    (h0 : c.nreg 90000 = MD) (h2 : c.nreg 90002 = D) (h28 : c.nreg 90028 = LB)
    (h95 : c.nreg 90095 = L.length)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD) (hMD : ModelDescAt c.nmem MD (Qof P) M)
    (hGM : GoodModel M) (hL : ChordListAt c.nmem LB L) (hLB : LB + 3 * L.length ≤ c.nreg ALLOC)
    (hok : ChordTriplesOK M (Qof P) L) (hdeg : M.DegLe (lset M (Qof P) L) D)
    (hroom : c.nreg ALLOC + costBD κB κD D L.length ≤ W) :
    ∃ c' k, Exec P W (bdStmt sB sD) c c' k ∧ k ≤ costBD κB κD D L.length ∧
      (∃ N', c.nreg ALLOC ≤ c'.nreg 90004 ∧
        NFWithin c'.nmem (c'.nreg 90004) (c'.nreg ALLOC) N' ∧
        IsNF M (Qof P) N' ∧ N'.F M (Qof P) = lset M (Qof P) L ∧
        IsDecomp N' (decDepth D N'.nChords)) ∧
      Frame granBands c c' k := by
  -- the arguments of the construction
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, R₁, rr₁, m₁, rm₁, o₁⟩ := copy3_exec (P := P) c hw
    40000 90000 40001 90028 40002 90095 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have w₁ := e₁.wb_right
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC :=
    R₁ _ (by decide) (by decide) (by decide)
  have F₁ : Frame {bBuild} c c₁ k₁ := frame_of (fun r hr => R₁ r
    (band_not (r := 40000) rfl (by decide) ∘ fun h => h ▸ hr)
    (band_not (r := 40001) rfl (by decide) ∘ fun h => h ▸ hr)
    (band_not (r := 40002) rfl (by decide) ∘ fun h => h ▸ hr)) rr₁ m₁ rm₁ o₁ (by decide)
  have r0 : rd c₁ bBuild 0 = MD := a0.trans h0
  have r1 : rd c₁ bBuild 1 = LB := a1.trans h28
  have r2 : rd c₁ bBuild 2 = L.length := a2.trans h95
  have hMD₁ : ModelDescAt c₁.nmem MD (Qof P) M := by rwa [m₁]
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, F₂⟩ := hsB P W c₁ w₁
    ⟨hG, hWh, by rwa [r0, A₁, m₁], M, L, by rwa [r0], hGM, r2,
      by rwa [r1, A₁], by rwa [r1, m₁], hok⟩
    (by beta_reduce; rw [A₁, r2]; unfold costBD at hroom; omega)
  beta_reduce at hk₂
  rw [r2] at hk₂
  obtain ⟨N₁, g₁, hNW₁, hNF₁, hmap₁, -⟩ := post₂ M L (by rwa [r0]) r2
    (by rwa [r1, m₁])
  have w₂ := e₂.wb_right
  have hF₁ : N₁.F M (Qof P) = lset M (Qof P) L := F_of_map hmap₁
  have hlen₁ : N₁.chords.length = L.length := by rw [← hmap₁, List.length_map]
  -- the arguments of the decomposition
  obtain ⟨c₃, k₃, e₃, hk₃, b0, b1, b2, R₃, rr₃, m₃, rm₃, o₃⟩ := copy3_exec (P := P) c₂ w₂
    60000 90000 60001 40003 60002 90002 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have w₃ := e₃.wb_right
  have A₃ : c₃.nreg ALLOC = c₂.nreg ALLOC := R₃ _ (by decide) (by decide) (by decide)
  have F₃ : Frame {bDecomp} c₂ c₃ k₃ := frame_of (fun r hr => R₃ r
    (band_not (r := 60000) rfl (by decide) ∘ fun h => h ▸ hr)
    (band_not (r := 60001) rfl (by decide) ∘ fun h => h ▸ hr)
    (band_not (r := 60002) rfl (by decide) ∘ fun h => h ▸ hr)) rr₃ m₃ rm₃ o₃ (by decide)
  have k90000 : c₂.nreg 90000 = MD := by
    rw [F₂.1 _ (by decide) (by decide), R₁ _ (by decide) (by decide) (by decide), h0]
  have k90002 : c₂.nreg 90002 = D := by
    rw [F₂.1 _ (by decide) (by decide), R₁ _ (by decide) (by decide) (by decide), h2]
  have s0 : rd c₃ bDecomp 0 = MD := b0.trans k90000
  have s1 : rd c₃ bDecomp 1 = rd c₂ bBuild 3 := b1
  have s2 : rd c₃ bDecomp 2 = D := b2.trans k90002
  have hA12 : c.nreg ALLOC ≤ c₂.nreg ALLOC := A₁ ▸ F₂.2.2.2.2.2.1
  have hlow : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃, F₂.2.2.1 a (by omega), m₁]
  obtain ⟨hMD₃, hwf₃⟩ := desc_agree' hwf hMD hlow
  have hNW₃ : NFWithin c₃.nmem (rd c₃ bDecomp 1) (c₃.nreg ALLOC) N₁ := by
    rwa [s1, m₃, A₃]
  have hcnt : c₃.nmem (rd c₃ bDecomp 1) = L.length := by
    rw [← hlen₁]; exact hNW₃.nfAt.1
  obtain ⟨c₄, k₄, e₄, hk₄, post₄, F₄⟩ := hsD P W c₃ w₃
    ⟨hG, hWh, by rw [s0]; exact hwf₃.mono (by omega), M, N₁, by rwa [s0], hGM, hNW₃,
      hNF₁, by rwa [s2, hF₁]⟩
    (by
      beta_reduce
      rw [s2, hcnt, A₃]
      have := F₂.2.2.2.2.2.2
      unfold costBD at hroom
      rw [A₁] at this
      nlinarith)
  beta_reduce at hk₄
  rw [s2, hcnt] at hk₄
  obtain ⟨N₂, g₂, hNW₂, hc₂, ha₂, hr₂, hs₂, hdec₂⟩ := post₄ M N₁ (by rwa [s0])
    hNW₃.nfAt hNF₁
  have w₄ := e₄.wb_right
  -- the handle
  obtain ⟨c₅, k₅, e₅, hk₅, d0, R₅, rr₅, m₅, rm₅, o₅⟩ := copy1_exec (P := P) c₄ w₄ 90004 60003
  have A₅ : c₅.nreg ALLOC = c₄.nreg ALLOC := R₅ _ (by decide)
  have F₅ : Frame {bGran} c₄ c₅ k₅ := frame_of (fun r hr => R₅ r
    (band_not (r := 90004) rfl (by decide) ∘ fun h => h ▸ hr)) rr₅ m₅ rm₅ o₅ (by decide)
  have FF := (((F₁.trans F₂).trans F₃).trans F₄).trans F₅
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, ⟨N₂, ?_, ?_, ?_, ?_, ?_⟩,
    FF.mono (by decide) (by omega)⟩
  · unfold costBD; nlinarith
  · have := F₄.2.2.2.2.2.1
    rw [d0]
    show c.nreg ALLOC ≤ rd c₄ bDecomp 3
    omega
  · rwa [d0, m₅, A₅]
  · exact isNF_congr hNF₁ hc₂ ha₂ hr₂ hs₂
  · rw [F_congr hc₂, hF₁]
  · have : N₂.nChords = N₁.nChords := by unfold NF.nChords; rw [hc₂]
    rwa [this, ← s2]

end

end Gran

end Chazelle.Core
