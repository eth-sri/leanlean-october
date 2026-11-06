module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvPList

/-!
# Down-phase pieces (D4), part 12: the build and the granularity enforcement

* `buildS_exec`: `BuildNFSpec`'s procedure on the descriptor `218010` and the chord list
  (`218016`, length `218017`); the normal form into `218018`;
* `granS_exec`: `GranularizeSpec`'s procedure on it, cap `4`, target `γ` (`218007`); the
  canonical normal form into `218011`.
-/


namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs NFLoc SignK WalkKey

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

section
variable (c : Config)
theorem rdBd1 : rd c bBuild 1 = c.nreg 40001 := rfl
theorem rdBd2 : rd c bBuild 2 = c.nreg 40002 := rfl
theorem rdBd3 : rd c bBuild 3 = c.nreg 40003 := rfl
theorem rdG1 : rd c bGran 1 = c.nreg 90001 := rfl
theorem rdG2 : rd c bGran 2 = c.nreg 90002 := rfl
theorem rdG3 : rd c bGran 3 = c.nreg 90003 := rfl
theorem rdG4 : rd c bGran 4 = c.nreg 90004 := rfl


end

theorem build_sub : ({bBuild, bSort, bSign} : Finset ℕ) ⊆ DrvR.drvBands := by decide
theorem gran_sub : granBands ⊆ DrvR.drvBands := by decide
theorem band21_not_build : (21 : ℕ) ∉ ({bBuild, bSort, bSign} : Finset ℕ) := by decide
theorem band21_not_gran : (21 : ℕ) ∉ granBands := by decide

/-- A frame of a block of register copies into one band of the driver. -/
theorem frame_copies {s : Stmt} {c c' : Config} {k : ℕ} (e : Exec P W s c c' k) {lo hi : ℕ}
    (hs : wr (fun r => decide (lo ≤ r ∧ r < hi)) s = true)
    (hband : ∀ r, lo ≤ r → r < hi → bandOf r ∈ DrvR.drvBands) (hA : ¬ (lo ≤ ALLOC ∧ ALLOC < hi)) :
    Frame DrvR.drvBands c c' k :=
  frame_of_wr e hs (fun r hr => by simp_all)
    (by ram_grind)

set_option maxHeartbeats 4000000 in
/-- **The build.** -/
theorem buildS_exec {sBd : Stmt} {κBd : ℕ} (hBd : BuildM sBd κBd) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hD : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 218010)) {M : Model}
    {L : List (ℕ × ℕ × ℕ)} (hM : ModelDescAt c.nmem (c.nreg 218010) (Qof P) M)
    (hGM : GoodModel M) (hK : c.nreg 218017 = L.length)
    (hB : c.nreg 218016 + 3 * L.length ≤ c.nreg ALLOC)
    (hCL : ChordListAt c.nmem (c.nreg 218016) L) (hok : ChordTriplesOK M (Qof P) L)
    (hroom : c.nreg ALLOC + κBd * (L.length * (Nat.clog 2 L.length + 1) + 1) + 4 ≤ W) :
    ∃ c' k, Exec P W (buildS sBd) c c' k ∧
      k ≤ κBd * (L.length * (Nat.clog 2 L.length + 1) + 1) + 4 ∧ Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218018 → c'.nreg r = c.nreg r) ∧
      ∃ N, c.nreg ALLOC ≤ c'.nreg 218018 ∧ NFWithin c'.nmem (c'.nreg 218018) (c'.nreg ALLOC) N ∧
        IsNF M (Qof P) N ∧ N.chords.map (fun r => (r.h, r.lp, r.rp)) = L := by
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 40000 218010, .copyN 40001 218016, .copyN 40002 218017]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 40000 = c.nreg 218010 ∧ c₁.nreg 40001 = c.nreg 218016 ∧
      c₁.nreg 40002 = c.nreg 218017 ∧ (∀ r, (r < 40000 ∨ 40003 ≤ r) → c₁.nreg r = c.nreg r) := by
    exec_block
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun r hr => ?_⟩
    ram_simp <;> omega_nf
  have w₁ := e₁.wb_right
  have G₁ : Frame DrvR.drvBands c c₁ k₁ := frame_copies e₁ (lo := 40000) (hi := 40003)
    (by decide) (fun r h1 h2 => by core_grind [DrvT.mem_drvBands])
    (by omega_nf)
  have hm₁ : c₁.nmem = c.nmem := (exec_frameB e₁ (B := fun r => decide (40000 ≤ r ∧ r < 40003))
    (by decide)).2.2.1
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := r₁ _ (by omega_nf)
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hBd P W c₁ w₁
    ⟨hG, hW, by omega_nf, M, L, by omega_nf, hGM,
      by core_grind, by simp_all [rdBd1] <;> omega_nf, by omega_nf,
      hok⟩
    (by simp_all [rdBd2] <;> omega_nf)
  replace hk₂ : k₂ ≤ κBd * (L.length * (Nat.clog 2 L.length + 1) + 1) := by
    grind [rdBd2]
  obtain ⟨N, hN1, hN2, hN3, hN4, -⟩ := hpost M L (by omega_nf)
    (by grind [rdBd2]) (by omega_nf)
  rw [rdBd3] at hN1 hN2
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, v18, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 218018 40003]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 218018 = c₂.nreg 40003 ∧
      c₃ = { c₂ with nreg := upd c₂.nreg 218018 (c₂.nreg 40003) } := by
    exec_block
    ram_simp
  have G₂ : Frame DrvR.drvBands c₁ c₂ k₂ := F₂.mono build_sub le_rfl
  have G₃ : Frame DrvR.drvBands c₂ c₃ k₃ := frame_of_wr e₃ (B := fun r => r == 218018)
    (by decide) (fun r hr => by simp only [beq_iff_eq] at hr; subst hr; decide) (by decide)
  have hA₃ : c₃.nreg ALLOC = c₂.nreg ALLOC := by ram_simp
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    (G₁.trans (G₂.trans G₃)).mono (by simp) (by omega), fun r hr h18 => ?_, N, ?_, ?_, hN3, hN4⟩
  · rw [r₃]; simp only [upd, ite_eq_right h18]
    rw [F₂.1 r (by rw [hr]; exact band21_not_build) (by grind [ALLOC, bandOf]),
      r₁ r (by grind [bandOf])]
  all_goals ram_grind

set_option maxHeartbeats 4000000 in
/-- **The granularity enforcement** (cap `4`, target `γ` from `218007`). -/
theorem granS_exec {sG : Stmt} {κG : ℕ → ℕ} (hGm : GranM sG κG) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hD : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 218010)) {M : Model} {N : NF}
    (hM : ModelDescAt c.nmem (c.nreg 218010) (Qof P) M) (hGM : GoodModel M)
    (hN : NFWithin c.nmem (c.nreg 218018) (c.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hdeg : M.DegLe (N.F M (Qof P)) 4) (hwt : M.Semigranular (N.F M (Qof P)) (c.nreg 218007))
    (hroom : c.nreg ALLOC + κG 4 * (N.chords.length * (Nat.clog 2 N.chords.length + 1) + 1) + 5
      ≤ W) :
    ∃ c' k, Exec P W (granS sG) c c' k ∧
      k ≤ κG 4 * (N.chords.length * (Nat.clog 2 N.chords.length + 1) + 1) + 5 ∧
      Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218011 → c'.nreg r = c.nreg r) ∧
      ∃ N', c.nreg ALLOC ≤ c'.nreg 218011 ∧
        NFWithin c'.nmem (c'.nreg 218011) (c'.nreg ALLOC) N' ∧
        IsCanonicalNF M (Qof P) N' (c.nreg 218007) 4 := by
  have hW1 : 4 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, v3, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 90000 218010, .copyN 90001 218018, .constN 90002 4, .copyN 90003 218007])
      c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 90000 = c.nreg 218010 ∧ c₁.nreg 90001 = c.nreg 218018 ∧ c₁.nreg 90002 = 4 ∧
      c₁.nreg 90003 = c.nreg 218007 ∧ (∀ r, (r < 90000 ∨ 90004 ≤ r) → c₁.nreg r = c.nreg r) := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, fun r hr => ?_⟩
    simp only [Config.nreg_mk, upd]; ram_grind
  have w₁ := e₁.wb_right
  have G₁ : Frame DrvR.drvBands c c₁ k₁ := frame_copies e₁ (lo := 90000) (hi := 90004)
    (by decide) (fun r h1 h2 => by core_grind [DrvT.mem_drvBands])
    (by omega_nf)
  have hm₁ : c₁.nmem = c.nmem := (exec_frameB e₁ (B := fun r => decide (90000 ≤ r ∧ r < 90004))
    (by decide)).2.2.1
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := r₁ _ (by omega_nf)
  have hK : c₁.nmem (c₁.nreg 90001) = N.chords.length := by
    rw [hm₁, v1]; exact hN.nfAt.1
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hGm P W c₁ w₁
    ⟨hG, hW, by core_grind, by omega_nf, M, N,
      by omega_nf, hGM, by omega_nf, hNF,
      by simp_all [rdG2] <;> omega_nf, by simp_all [rdG3] <;> omega_nf⟩
    (by simp_all [rdG2, rdG1] <;> omega_nf)
  replace hk₂ : k₂ ≤ κG 4 * (N.chords.length * (Nat.clog 2 N.chords.length + 1) + 1) := by
    omega_nf
  obtain ⟨N', hN1, hN2, -, hN3⟩ := hpost M N (by omega_nf)
    (by rw [rdG1, v1, hm₁]; exact hN.nfAt)
  rw [rdG4] at hN1 hN2
  rw [rdG3, rdG2, v3, v2] at hN3
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, v11, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 218011 90004]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 218011 = c₂.nreg 90004 ∧
      c₃ = { c₂ with nreg := upd c₂.nreg 218011 (c₂.nreg 90004) } := by
    exec_block
    ram_simp
  have G₂ : Frame DrvR.drvBands c₁ c₂ k₂ := F₂.mono gran_sub le_rfl
  have G₃ : Frame DrvR.drvBands c₂ c₃ k₃ := frame_of_wr e₃ (B := fun r => r == 218011)
    (by decide) (fun r hr => by simp only [beq_iff_eq] at hr; subst hr; decide) (by decide)
  have hA₃ : c₃.nreg ALLOC = c₂.nreg ALLOC := by ram_simp
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    (G₁.trans (G₂.trans G₃)).mono (by simp) (by omega), fun r hr h11 => ?_, N', ?_, ?_, hN3⟩
  · rw [r₃]; simp only [upd, ite_eq_right h11]
    rw [F₂.1 r (by rw [hr]; exact band21_not_gran) (by grind [ALLOC, bandOf]),
      r₁ r (by grind [bandOf])]
  all_goals ram_grind

end exec

end

end DrvP

end Chazelle.Core
