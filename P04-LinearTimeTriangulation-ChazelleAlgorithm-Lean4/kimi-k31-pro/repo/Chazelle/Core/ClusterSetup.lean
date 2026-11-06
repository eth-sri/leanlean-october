module

public import Chazelle.Core.ClusterDriverRam
public import Chazelle.Core.ClusterPrimal
public import Chazelle.UnfoldTactics

/-!
# WP-I, part 42: the global registers and the setup

The inputs (`130000 … 130003`: `B`, `μ`, `E`, `k`) are copied to the global registers, then the
constants of the algorithm are computed in registers only (no multiplication: products are
repeated additions):

* `130010 B`, `130011 μ`, `130012 E`, `130013 k`, `130014 N = 2 E`, `130015 k' = min k μ`,
  `130016 s = min (k' k') μ`, `130017 L = clog₂ (N + μ + 1)`, `130018 P = 2 ^ L`,
  `130019 U = N + μ + P + 3`, `130020 A0` (the allocator on entry), `130021 … 130023` the bases of
  the input arrays `opp`, `rot`, `vert`, `130026 L U`;
* `130030 + j = A0 + j U` for `j ≤ 54` (the slots), `130085 = A0 + 54 U + L U` (the dual table),
  `130086 = A0 + 54 U + 2 L U` (the end of the allocated area);
* `130001 = 1`, `130009 = 0`.

Scratch registers `130090 … 130099`.

* `inputFacts`: the robust input map lies below the allocator.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-! ## The input -/

/-- **The input map lies below the allocator**: a planar map robust below `A` is read at
addresses below `A`. -/
theorem inputFacts {m : ℕ → ℕ} {A B μ E : ℕ}
    (h : Robust A m (fun m' => PlanarMapAt m' B μ E)) :
    ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F) (M : CombMap (Fin μ) F (Fin (2 * E))),
      M.Planar ∧ MapArrays m (m B) (m (B + 1)) (m (B + 2)) μ (2 * E) M ∧ 0 < μ ∧ 0 < E ∧
      μ ≤ 2 * E ∧ B + 2 < A ∧ m B + 2 * E ≤ A ∧ m (B + 1) + 2 * E ≤ A ∧ m (B + 2) + 2 * E ≤ A := by
  obtain ⟨F, i1, i2, M, hM, hA⟩ := PlanarMapAt.exists_arrays h.holds
  -- the map has a dart and a vertex
  have hEuler := hM.2
  have hN : 0 < 2 * E := by
    by_contra h0
    have hE0 : 2 * E = 0 := by omega
    have hV : Fintype.card (Fin μ) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun v => by
        obtain ⟨d, -⟩ := M.vert_surj v
        exact absurd d.2 (by omega)⟩
    have hF : Fintype.card F = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun g => by
        obtain ⟨d, -⟩ := M.face_surj g
        exact absurd d.2 (by omega)⟩
    have hE : M.numE = 0 := by
      unfold CombMap.numE
      simp [hE0]
    unfold CombMap.euler at hEuler
    rw [hV, hF, hE] at hEuler
    norm_num at hEuler
  have hμ : 0 < μ := (M.vert ⟨0, hN⟩).pos
  have hμN : μ ≤ 2 * E := by
    have := Fintype.card_le_of_surjective M.vert M.vert_surj
    simpa using this
  -- the bases lie below `A`
  have hbase : B + 2 < A := by
    by_contra hc
    obtain ⟨i, hi, hiA⟩ : ∃ i, i ≤ 2 ∧ A ≤ B + i := ⟨2, le_rfl, by omega⟩
    set Z := B + A + 3
    set X := 2 * E + μ + 1
    let m' : ℕ → ℕ := fun a => if a = B + i then Z else if Z ≤ a then X else m a
    obtain ⟨F', _, _, M', -, hA'⟩ := PlanarMapAt.exists_arrays (h m' (fun a ha => by
      simp only [m']
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]))
    have e1 : m' (B + i) = Z := by simp [m']
    have e2 : m' (Z + 0) = X := by simp only [m']; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · have := hA'.opp hN
      rw [show B + 0 = B by omega] at e1
      rw [e1, e2] at this
      have := (M'.opp ⟨0, hN⟩).2
      omega
    · have := hA'.rot hN
      rw [e1, e2] at this
      have := (M'.rot ⟨0, hN⟩).2
      omega
    · have := hA'.vert hN
      rw [e1, e2] at this
      have := (M'.vert ⟨0, hN⟩).2
      omega
  -- the arrays lie below `A`
  have harr : ∀ i, i ≤ 2 → m (B + i) + 2 * E ≤ A := by
    intro i hi
    by_contra hc
    set d := 2 * E - 1
    set X := 2 * E + μ + 1
    let m' : ℕ → ℕ := fun a => if a = m (B + i) + d then X else m a
    obtain ⟨F', _, _, M', -, hA'⟩ := PlanarMapAt.exists_arrays (h m' (fun a ha => by
      simp only [m']
      rw [ite_eq_right (by omega)]))
    have eB : ∀ j, j ≤ 2 → m' (B + j) = m (B + j) := fun j hj => by
      simp only [m']; rw [ite_eq_right (by omega)]
    have e2 : m' (m (B + i) + d) = X := by simp [m']
    have hd : d < 2 * E := by omega
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · have := hA'.opp hd
      have eB0 := eB 0 (by omega)
      simp only [Nat.add_zero] at e2 eB0
      rw [eB0, e2] at this
      have := (M'.opp ⟨d, hd⟩).2
      omega
    · have := hA'.rot hd
      rw [eB 1 (by omega), e2] at this
      have := (M'.rot ⟨d, hd⟩).2
      omega
    · have := hA'.vert hd
      rw [eB 2 le_rfl, e2] at this
      have := (M'.vert ⟨d, hd⟩).2
      omega
  exact ⟨F, i1, i2, M, hM, hA, hμ, by omega, hμN, hbase, by simpa using harr 0 (by omega),
    harr 1 (by omega), harr 2 le_rfl⟩

/-! ## The global values -/

/-- The input values of the algorithm. -/
structure GV where
  B : ℕ
  μ : ℕ
  E : ℕ
  k : ℕ
  A0 : ℕ
  bO : ℕ
  bR : ℕ
  bV : ℕ

namespace GV

variable (g : GV)

/-- The number of darts. -/
def N : ℕ := 2 * g.E
/-- The slab width. -/
def k' : ℕ := min g.k g.μ
/-- The cluster size. -/
def s : ℕ := min (g.k' * g.k') g.μ
/-- The table length. -/
def L : ℕ := Nat.clog 2 (g.N + g.μ + 1)
/-- The slot size. -/
def U : ℕ := g.N + g.μ + 2 ^ g.L + 3
/-- The base of slot `j`. -/
def base (j : ℕ) : ℕ := g.A0 + j * g.U
/-- The end of the allocated area. -/
def END : ℕ := g.A0 + 54 * g.U + 2 * (g.L * g.U)

end GV

/-- The global registers hold the global values. -/
structure GR (g : GV) (c : Config) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rB : c.nreg 130010 = g.B
  rμ : c.nreg 130011 = g.μ
  rE : c.nreg 130012 = g.E
  rk : c.nreg 130013 = g.k
  rN : c.nreg 130014 = g.N
  rk' : c.nreg 130015 = g.k'
  rs : c.nreg 130016 = g.s
  rL : c.nreg 130017 = g.L
  rP : c.nreg 130018 = 2 ^ g.L
  rU : c.nreg 130019 = g.U
  rA0 : c.nreg 130020 = g.A0
  rO : c.nreg 130021 = g.bO
  rR : c.nreg 130022 = g.bR
  rV : c.nreg 130023 = g.bV
  rLU : c.nreg 130026 = g.L * g.U
  rbase : ∀ j, j ≤ 54 → c.nreg (130030 + j) = g.base j
  rUP : c.nreg 130085 = g.A0 + 54 * g.U + g.L * g.U
  rEND : c.nreg 130086 = g.END

/-- The global registers. -/
def GRReg (r : ℕ) : Prop := r = 130001 ∨ r = 130009 ∨ (130010 ≤ r ∧ r ≤ 130089)

theorem GR.frame {g : GV} {c c' : Config} (h : GR g c)
    (hr : ∀ r, GRReg r → c'.nreg r = c.nreg r) : GR g c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_,
    ?_⟩
  all_goals first
    | (rw [hr _ (by ufo GRReg)]; assumption)
    | (rw [hr _ (by ufo GRReg)]; exact h18 j hj)

end

end Chazelle.Core.Cluster
