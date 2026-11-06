module

public import Chazelle.Core.GranInitB

/-!
# WP-F, init part 15: the initial machine state

`initStmt = initA; initB` reaches a machine state `MS` of the initial state `initSt` of the
worklist, which satisfies the invariant (`init_exec`), for the environment `envOf` of the run and
the layout `dmOf K A R D b0` at the entry allocator `b0`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- **The initialisation.** -/
def initStmt : Stmt := .seq initA initB

/-- The cost of the initialisation. -/
def costInit (K A R D : ℕ) : ℕ :=
  costA K A R D + (6052 * A + K * (2 * NFLoc.locCost 5100 A + 32) + 12)

/-- The initial state read from the memory after the initialisation. -/
noncomputable def st0 (E : Env) (d : Dm) (m : ℕ → ℕ) : St :=
  initSt E (rdArr m (d.b0 + d.oNd0)) (rdArr m (d.b0 + d.oNd1)) (rdArr m (d.b0 + d.oEg))
    (rdArr m (d.b0 + d.oPz))

set_option maxHeartbeats 4000000 in
theorem init_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {MD NFH D γ : ℕ} {M : Model} {N : NF} {reg : ℕ → Set Point}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = NFH) (h2 : c.nreg 90002 = D)
    (h3 : c.nreg 90003 = γ) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD) (hMD : ModelDescAt c.nmem MD (Qof P) M)
    (hGM : GoodModel M) (hNW : NFWithin c.nmem NFH (c.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hRC : RegionCorr M (Qof P) N reg) (hCS : ChordSidesOK M (Qof P) N reg)
    (hRO : RegionsOK M (Qof P) N reg) (hne : (N.F M (Qof P)).Nonempty)
    (hdeg : M.DegLe (N.F M (Qof P)) D) (hsemi : M.Semigranular (N.F M (Qof P)) γ)
    (hroom : c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd +
      N.nChords * (2 * NFLoc.locCost 5100 N.arcs.length + 30) ≤ W) :
    ∃ c' k, Exec P W initStmt c c' k ∧ k ≤ costInit N.nChords N.arcs.length N.nRegions D ∧
      MS W (envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3)))
        (dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)) (c.nreg ALLOC) c.nmem c'
        (st0 (envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3)))
          (dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)) c'.nmem) ∧
      Inv (envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3)))
        (st0 (envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3)))
          (dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)) c'.nmem) ∧
      (envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3))).Good ∧
      DimOK (envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3)))
        (dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)) W ∧
      c'.nreg 90052 = 0 ∧ c'.nreg 90000 = MD ∧ c'.nreg 90001 = NFH ∧ c'.nreg 90002 = D ∧
      c'.nreg 90003 = γ ∧ c'.nreg 90010 = N.nChords ∧ c'.nreg 90013 = c.nmem (NFH + 3) ∧
      c'.nreg 90028 =
        c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)).oList ∧
      c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)).oEnd ≤
        c'.nreg ALLOC ∧
      GF (c.nreg ALLOC) c c' k := by
  have hK1 : 1 ≤ N.nChords := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi, -⟩ := mem_F_iff.1 hx
    omega
  have hM : WalkAx M := walkAx_of_goodModel hGM
  have hR1 : 1 ≤ N.nRegions := by rw [nRegions_eq hNF hM]; omega
  obtain ⟨c₅, k₅, e₅, hk₅, I₅, G₅⟩ := initA_exec (P := P) hw h0 h1 h2 h3 hWh hwf hMD hNW hNF hRC
    hRO hdeg (by omega) hK1 hR1
  obtain ⟨c₈, k₈, e₈, hk₈, I₈, G₈⟩ := initB_exec (P := P) I₅ hG hWh hwf hMD hGM hNW hNF hne
    (by rw [I₅.alloc]; show c.nreg ALLOC + (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd + _ ≤ W
        omega)
  set E := envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3))
  set d := dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC)
  set st := st0 E d c₈.nmem
  have hE : E.Good := envOf_good hMD hGM hNF hRC hCS hRO hne
  have henc : Enc c₈.nmem d st := by
    refine ⟨fun i hi => (I₈.live i hi).1, fun i hi => (I₈.live i hi).2.1,
      fun i hi => (I₈.live i hi).2.2, fun i _ => rfl, fun i _ => rfl,
      fun x hx => (I₈.cls x hx).1, fun x hx => (I₈.cls x hx).2.1,
      fun x hx => (I₈.cls x hx).2.2.1, fun x t hx ht => (I₈.cls x hx).2.2.2 t ht,
      fun j hj => I₈.cnt j hj, fun j hj => (I₈.ring j hj).1, fun j hj => (I₈.ring j hj).2.1,
      fun j _ => rfl, fun j _ => rfl, fun t ht => I₈.stk t ht⟩
  have hstat : StatOK E st :=
    ⟨fun i hi => I₈.nd0 i hi, fun i hi => I₈.nd1 i hi, fun j hj => (I₈.ring j hj).2.2.1,
      fun j hj => ⟨(I₈.ring j hj).2.2.2.1, (I₈.ring j hj).2.2.2.2⟩⟩
  have hI : Inv E st := Inv.init hE hstat hdeg hsemi
  have hsz : E.sz ≤ W := by rw [envOf_sz hMD]; exact szOf_le hwf hMD hWh
  have hW3 : 3 ≤ W := by unfold hostWords at hWh; omega
  have hEnd : d.oEnd = (dmOf N.nChords N.arcs.length N.nRegions D 0).oEnd := rfl
  have hDim : DimOK E d W := ⟨rfl, rfl, rfl, rfl, by show c.nreg ALLOC + d.oEnd ≤ W; omega, hsz,
    hW3⟩
  have hC : Cst c₈ E d := Cst.of_bases I₈.bases I₈.r14 (by rw [I₈.r18, envOf_sz hMD]) I₈.r19
    I₈.r20 I₈.r21
  refine ⟨c₈, _, .seq e₅ e₈, ?_, ⟨I₈.wb, hC, henc, I₈.r50, I₈.r51, I₈.mem⟩, hI, hE, hDim,
    I₈.r52, I₈.r00, I₈.r01, I₈.r02, I₈.r03, I₈.r10, I₈.r13, I₈.r28, I₈.alloc,
    (G₅.trans G₈).mono le_rfl⟩
  unfold costInit
  omega

end

end Gran

end Chazelle.Core
