module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.UpPhase5
public import Chazelle.Core.UpPhaseGran

/-!
# WP-J up phase, part 6: coarsening a short last chain

`granCall`: write the model descriptor `[0, descriptor words]` of the chain described at
`170030` at the allocator, and coarsen the normal form in `170031` (canonical at `γ'_{g-1}`) to
granularity `γ'_g` (`170011`) by `GranularizeSpec` (`granCall_exec`).

Registers: `170070 … 170074` scratch; constants `170020 = 1`, `170025 = 4`, `170026 = 6`,
`170029 = 0`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The model descriptor `[0, d, d+1, …, d+4]` at the allocator. -/
def mdB : Stmt := block [.copyN 170070 9999, .addN 9999 9999 170026, .storeN 170070 170029,
  .copyN 170072 170030, .addN 170073 170070 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074]

/-- **Coarsening.** -/
def granCall (sG : Stmt) : Stmt :=
  .seq mdB (.seq (block [.copyN 90000 170070, .copyN 90001 170031, .copyN 90002 170025,
    .copyN 90003 170011]) (.seq sG (block [.copyN 170031 90004])))

/-- The registers written by `mdB`. -/
def MdRG (r : ℕ) : Prop := 170070 ≤ r ∧ r ≤ 170074

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
theorem mdB_exec {c : Config} (hw : WordsBounded W c) {MD B : ℕ} (hA : c.nreg ALLOC = MD)
    (h30 : c.nreg 170030 = B) (h20 : c.nreg 170020 = 1) (h26 : c.nreg 170026 = 6)
    (h29 : c.nreg 170029 = 0) (hB : B + 5 ≤ MD) (hW : MD + 6 ≤ W) :
    ∃ c' k, Exec P W mdB c c' k ∧ k = 23 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = MD + 6 ∧ c'.nreg 170070 = MD ∧ c'.nmem MD = 0 ∧
      (∀ j, j < 5 → c'.nmem (MD + 1 + j) = c.nmem (B + j)) ∧
      (∀ a, (a < MD ∨ MD + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ MdRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold mdB
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun j hj => ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · ram_simp
  · ram_simp
  · config_simp; simp only [hA, h29, h30, h20, Machine.upd_apply]; ram_grind
  · config_simp
    simp only [hA, h29, h30, h20, Machine.upd_apply]
    grind
  · config_simp; simp only [hA, h30, h20, Machine.upd_apply]; grind
  · unfold MdRG at h1
    simp only
    repeat ram_simp

set_option maxHeartbeats 16000000 in
/-- **Coarsening, called from the up phase.** -/
theorem granCall_exec {sG : Stmt} {κG : ℕ → ℕ}
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bGran 0) ∧
        ∃ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M ∧ GoodModel M ∧
          NFWithin c.nmem (rd c bGran 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
          M.DegLe (N.F M (Qof P)) (rd c bGran 2) ∧
          M.Semigranular (N.F M (Qof P)) (rd c bGran 3))
      (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M →
        NFAt c.nmem (rd c bGran 1) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N' ∧
          N'.F M (Qof P) ⊆ N.F M (Qof P) ∧
          IsCanonicalNF M (Qof P) N' (rd c bGran 3) (rd c bGran 2))
      (fun _ c => κG (rd c bGran 2) *
        (c.nmem (rd c bGran 1) * (Nat.clog 2 (c.nmem (rd c bGran 1)) + 1) + 1)))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {MD B F γ γ0 hp : ℕ} {C : Chain} {N : NF}
    (hA : c.nreg ALLOC = MD) (h30 : c.nreg 170030 = B) (h31 : c.nreg 170031 = F)
    (h11 : c.nreg 170011 = γ) (h20 : c.nreg 170020 = 1) (h25 : c.nreg 170025 = 4)
    (h26 : c.nreg 170026 = 6) (h29 : c.nreg 170029 = 0)
    (hd : ChainDescAt c.nmem B (Qof P) (Host.whole P.n) C) (hBh : c.nmem B = hp)
    (hB5 : B + 5 ≤ MD) (hhp : hp + 7 ≤ MD) (hCP : C.P = Qof P) (hCn : C.s + C.m + 1 ≤ P.n)
    (hNW : NFWithin c.nmem F MD N) (hc : IsCanonicalNF (chainModel C) (Qof P) N γ0 4)
    (hγ : γ0 ≤ γ)
    (hbud : MD + 6 + κG 4 * (c.nmem F * (Nat.clog 2 (c.nmem F) + 1) + 1) ≤ W) :
    ∃ c' k, Exec P W (granCall sG) c c' k ∧
      k ≤ κG 4 * (c.nmem F * (Nat.clog 2 (c.nmem F) + 1) + 1) + 30 ∧
      WordsBounded W c' ∧ MD ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ MD + k ∧
      (∃ N', NFWithin c'.nmem (c'.nreg 170031) (c'.nreg ALLOC) N' ∧
        IsCanonicalNF (chainModel C) (Qof P) N' γ 4) ∧
      (∀ a, a < MD → c'.nmem a = c.nmem a) ∧
      (∀ a, a < MD → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ granBands → ¬ MdRG r → r ≠ 170031 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ granBands → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn1 : 1 ≤ P.n := by omega
  obtain ⟨c1, k1, e1, hk1, hw1, m1A, m170, m1z, m1w, m1out, fr1, hrr1, hrm1, ho1⟩ :=
    mdB_exec (P := P) hw hA h30 h20 h26 h29 hB5 (by omega)
  have g1 : ∀ r, 170000 ≤ r → r < 170070 → c1.nreg r = c.nreg r := fun r a b =>
    fr1 r (by omega_nf) (by omega)
  obtain ⟨c2, k2, e2, hk2, hw2, i0, i1, i2, i3, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      (block [.copyN 90000 170070, .copyN 90001 170031, .copyN 90002 170025,
        .copyN 90003 170011]) c1 c2 k2 ∧ k2 = 4 ∧ WordsBounded W c2 ∧
      c2.nreg 90000 = MD ∧ c2.nreg 90001 = F ∧ c2.nreg 90002 = 4 ∧ c2.nreg 90003 = γ ∧
      (∀ r, r ≠ 90000 → r ≠ 90001 → r ≠ 90002 → r ≠ 90003 → c2.nreg r = c1.nreg r) ∧
      c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    exec_block
    refine ⟨rfl, ‹_›, by ram_simp,
      by ram_simp,
      by ram_simp,
      by ram_simp,
      fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA2 : c2.nreg ALLOC = MD + 6 := by
    grind
  -- memory facts at `c2`
  have mem2 : ∀ a, a < MD → c2.nmem a = c.nmem a := fun a ha => by
    ram_grind
  have hHA : HostAt c.nmem hp (Host.whole P.n) := by have := hd.1; ram_grind
  have hHA2 : HostAt c2.nmem hp (Host.whole P.n) :=
    hostAt_agree hHA rfl (by omega) mem2
  obtain ⟨-, d1, d2, d3, d4, d5⟩ := hd
  have w : ∀ j, j < 5 → c2.nmem (MD + 1 + j) = c.nmem (B + j) := fun j hj => by
    ram_grind
  have hdesc : ChainDescAt c2.nmem (MD + 1) (Qof P) (Host.whole P.n) C := by
    refine ⟨?_, d1, ?_, ?_, ?_, ?_⟩
    · have := w 0 (by norm_num); ram_grind
    · ram_grind
    · ram_grind
    · ram_grind
    grind
  
  have hwf : ModelDescWF P (c2.nreg ALLOC) c2.nmem MD := by
    rw [hA2]
    refine ⟨le_rfl, fun _ => ⟨by omega, fun H C' hC' => ?_⟩⟩
    have e0 : c2.nmem (MD + 1) = hp := by
      have := w 0 (by norm_num); ram_grind
    have hH : H = Host.whole P.n := hostAt_unique hC'.1 (by ram_grind)
    subst hH
    refine ⟨by simp [Host.whole], hostWF_whole hn1, by grind [Host.whole], ?_⟩
    have hs' : C'.s = C.s := by rw [← hC'.2.2.1, ← hdesc.2.2.1]
    have hP' : C'.P = Qof P := by
      rw [hC'.2.1]; ram_grind
    ram_grind
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hNW2 : NFWithin c2.nmem F (c2.nreg ALLOC) N := by
    rw [hA2]; exact (hNW.transport mem2).mono (by omega)
  have hFlt : F < MD := nfWithin_lt hNW
  have q1 : 1 ≤ rd c2 bGran 2 := by omega_nf
  have q2 : ModelDescWF P (c2.nreg ALLOC) c2.nmem (rd c2 bGran 0) := by
    show ModelDescWF P _ c2.nmem (c2.nreg 90000); ram_grind
  have q3 : ModelDescAt c2.nmem (rd c2 bGran 0) (Qof P) (chainModel C) := by
    show ModelDescAt c2.nmem (c2.nreg 90000) (Qof P) (chainModel C)
    grind [Chazelle.Core.ModelDescAt]
  have q4 : NFWithin c2.nmem (rd c2 bGran 1) (c2.nreg ALLOC) N := by
    show NFWithin c2.nmem (c2.nreg 90001) (c2.nreg ALLOC) N; ram_grind
  have q5 : (chainModel C).DegLe (N.F (chainModel C) (Qof P)) (rd c2 bGran 2) := by
    show (chainModel C).DegLe _ (c2.nreg 90002); rw [i2]; exact hc.2.1
  have q6 : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (rd c2 bGran 3) := by
    show (chainModel C).Semigranular _ (c2.nreg 90003)
    rw [i3]; exact Model.Granular.semigranular_of_le _ hc.2.2.1 hγ
  have q7 : c2.nreg ALLOC + κG (rd c2 bGran 2) * (c2.nmem (rd c2 bGran 1) *
      (Nat.clog 2 (c2.nmem (rd c2 bGran 1)) + 1) + 1) ≤ W := by
    show c2.nreg ALLOC + κG (c2.nreg 90002) * (c2.nmem (c2.nreg 90001) *
      (Nat.clog 2 (c2.nmem (c2.nreg 90001)) + 1) + 1) ≤ W
    grind
  obtain ⟨c3, k3, e3, hk3, hpost, fr3⟩ := hGr P W c2 hw2
    ⟨hG, hWh, q1, q2, chainModel C, N, q3, Or.inl ⟨C, by ram_grind, rfl⟩, q4, hc.1, q5,
      q6⟩ q7
  replace hk3 : k3 ≤ κG (c2.nreg 90002) * (c2.nmem (c2.nreg 90001) *
      (Nat.clog 2 (c2.nmem (c2.nreg 90001)) + 1) + 1) := hk3
  have hF2 : c2.nmem F = c.nmem F := by ram_grind
  rw [i1, i2, hF2] at hk3
  obtain ⟨N', -, hNW', -, hc'⟩ := hpost _ N q3 q4.holds
  replace hc' : IsCanonicalNF (chainModel C) (Qof P) N' (c2.nreg 90003) (c2.nreg 90002) := hc'
  rw [i2, i3] at hc'
  obtain ⟨fr3r, fr3rr, fr3m, fr3rm, fr3o, fr3a, fr3b⟩ := fr3
  have hw3 := e3.wb_right
  obtain ⟨c4, k4, e4, hk4, hw4, o31, fr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
      (block [.copyN 170031 90004]) c3 c4 k4 ∧ k4 = 1 ∧ WordsBounded W c4 ∧
      c4.nreg 170031 = c3.nreg 90004 ∧ (∀ r, r ≠ 170031 → c4.nreg r = c3.nreg r) ∧
      c4.nmem = c3.nmem ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hA4 : c4.nreg ALLOC = c3.nreg ALLOC := fr4 _ (by omega)
  have hbb : ∀ r, bandOf r ∉ granBands → r < 90000 ∨ 100000 ≤ r := by
    intro r hr
    by_contra hc
    exact hr (by rw [show bandOf r = bGran by omega_nf]; decide)
  
  refine ⟨c4, k1 + (k2 + (k3 + k4)), .seq e1 (.seq e2 (.seq e3 e4)), by omega, hw4,
    by omega,
    by omega,
    ⟨N', by rw [o31, hm4, hA4]; exact hNW', hc'⟩,
    fun a ha => by ram_simp,
    fun a ha => by ram_simp,
    by ram_grind, fun r h1 h2 h3 h4 => ?_,
    fun r h1 => by ram_simp⟩
  have := hbb r h1
  rw [fr4 r h3, fr3r r h1 h4, fr2 r (by omega) (by omega) (by omega) (by omega), fr1 r h2 h4]

end proofs

end

end Chazelle.Core.Up
