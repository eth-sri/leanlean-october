module

public import RequestProject.UnivCoverIncl
public import RequestProject.Pi2DictionaryFinsupp

@[expose] public section

/-! Chains of presentation complexes with arbitrary generator and relator sets.
The two-cycle condition is imposed on actual cellular universal-cover chains. -/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u}

/-- A chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes over the presentation
`⟨α | ρ⟩`, with arbitrary cell sets, together with the topological property used in Section 2:
the inclusions are zero on `π₂`. -/
structure PresChainFS (ρ : J → FreeGroup α) (n : ℕ) where
  /-- The generators of the stage `X_r`. -/
  gen : ℕ → Type u
  /-- The two-cells of the stage `X_r`. -/
  cell : ℕ → Type u
  decGen : ∀ r, DecidableEq (gen r)
  /-- The attaching word of a two-cell of `X_r`. -/
  rel : ∀ r, cell r → FreeGroup (gen r)
  /-- The generators of `X_r` are generators of `X_{r+1}`. -/
  genIncl : ∀ r, gen r ↪ gen (r + 1)
  /-- The two-cells of `X_r` are two-cells of `X_{r+1}`. -/
  cellIncl : ∀ r, cell r ↪ cell (r + 1)
  /-- An old two-cell is attached along the same word. -/
  rel_incl : ∀ r c, rel (r + 1) (cellIncl r c) = FreeGroup.map (genIncl r) (rel r c)
  /-- The generators of `K` are generators of `X₀`. -/
  baseGen : α ↪ gen 0
  /-- The two-cells of `K` are two-cells of `X₀`. -/
  baseCell : J ↪ cell 0
  /-- The two-cells of `K` are attached along the relators of the presentation. -/
  rel_base : ∀ j, rel 0 (baseCell j) = FreeGroup.map baseGen (ρ j)
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`.**  In the combinatorial model
  `π₂(X_r)` is the module of cellular two-cycles of the universal cover `X̃_r`, and the
  inclusion lifts to the universal covers as the map of two-cells `(q, c) ↦ (Ψ q, c)`,
  where `Ψ : π₁(X_r) → π₁(X_{r+1})` is the induced map of fundamental groups.  The
  condition is that every cellular two-cycle of `X̃_r` is carried to zero. -/
  zero_pi2 : ∀ r, r < n →
      ∀ u : ((FreeGroup (gen r) ⧸ relSub (rel r)) × cell r) →₀ ℤ,
        Comb.bdry2 (@Comb.univCover _ (decGen r) _ (rel r)) u = 0 →
        Finsupp.mapDomain (Prod.map
          (Comb.presInclGroupHom (genIncl r) (rel r) (rel (r+1)) (cellIncl r) (rel_incl r))
          (cellIncl r)) u = 0

namespace PresChainFS

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainFS ρ n)

/-- Compose consecutive inclusions as embeddings; no separate injectivity induction is needed. -/
def gmap : ∀ r, α ↪ h.gen r
  | 0 => h.baseGen
  | r + 1 => (gmap r).trans (h.genIncl r)

def cmap : ∀ r, J ↪ h.cell r
  | 0 => h.baseCell
  | r + 1 => (cmap r).trans (h.cellIncl r)

/-- The two-cells of `K` are attached, in `X_r`, along the relators of the presentation. -/
theorem rel_cmap (h : PresChainFS ρ n) : ∀ (r : ℕ) (j : J),
    h.rel r (h.cmap r j) = FreeGroup.map (h.gmap r) (ρ j)
  | 0, j => h.rel_base j
  | r + 1, j => by
      change h.rel (r+1) (h.cellIncl r (h.cmap r j)) = _
      rw [h.rel_incl, rel_cmap h r j, FreeGroup.map.comp]
      rfl

variable (r : ℕ)

def psi := Comb.presInclGroupHom (h.genIncl r) _ _ (h.cellIncl r) (h.rel_incl r)

def phi := Comb.presInclGroupHom (h.gmap r) _ _ (h.cmap r) (h.rel_cmap r)

@[simp] theorem phi_mk (w : FreeGroup α) :
    h.phi r (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map (h.gmap r) w) := rfl

@[simp] theorem psi_mk (w : FreeGroup (h.gen r)) :
    h.psi r (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map (h.genIncl r) w) := rfl

theorem psi_comp_phi : (h.psi r).comp (h.phi r) = h.phi (r + 1) := by
  aesop

/-- **The `π₂`-condition in Fox coordinates.**  The topological hypothesis of the
chain — the inclusion is zero on `π₂` — says, in the coordinates used throughout
Section 2, that a Fox cycle over `ℤ[π₁(X_r)]` has zero image in the chain module of
`X_{r+1}`.  The two forms are equivalent by
`FiniteChains.Comb.fs_univCover_zero_pi2_iff`. -/
theorem zero_pi2_coords (hr : r < n)
    (u : h.cell r →₀ MonoidAlgebra ℤ (PresGroup (h.rel r)))
    (hu : ∀ a : h.gen r, ∑ c ∈ u.support, u c *
        quotRingHom ℤ (relSub (h.rel r)) (@fox _ (h.decGen r) a (h.rel r c)) = 0) :
    Finsupp.mapDomain (h.cellIncl r)
      (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)) (map_zero _) u) = 0 := by
  letI := h.decGen r
  exact (Comb.fs_univCover_zero_pi2_iff (h.rel r) (h.psi r) (h.cellIncl r)
    (h.cellIncl r).injective).1 (h.zero_pi2 r hr) u hu

/-- The Fox boundary matrix of the stage `X_r`. -/
noncomputable def bdry (a : h.gen r) (c : h.cell r) :=
  quotRingHom ℤ (relSub (h.rel r)) (@fox _ (h.decGen r) a (h.rel r c))

/-- Reading a group-ring element of `ℤ[F]` in `ℤ[π₁(X_r)]` through the inclusion of
generating sets agrees with pushing it to `ℤ[π₁(K)]` and then along `π₁(K) → π₁(X_r)`. -/
theorem quot_freeRingMap (x : FreeGroupRing α) :
    letI := h.decGen r
    quotRingHom ℤ (relSub (h.rel r)) (freeRingMap (h.gmap r) x)
      = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (quotRingHom ℤ (relSub ρ) x) := by
  letI := h.decGen r
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show quotRingHom ℤ (relSub (h.rel r))
          (MonoidAlgebra.mapDomain (FreeGroup.map (h.gmap r)) (MonoidAlgebra.single w m)) = _
      simp

variable [DecidableEq α]

/-- **The cell-level data of the chain.**  Everything except the two topological
properties is computed from the presentations. -/
noncomputable def toChainInput :
    ChainInput (foxMatrixPres ρ) n (fun r => PresGroup (h.rel r)) h.gen h.cell where
  phi := h.phi
  psi := h.psi
  phi_succ := h.psi_comp_phi
  genIncl r := h.gmap r
  cellIncl r := h.cmap r
  cellIncl_injective r := (h.cmap r).injective
  cellStep r := h.cellIncl r
  cellStep_injective r := (h.cellIncl r).injective
  bdry := h.bdry
  bdry_old := by
    intro r i j
    letI := h.decGen r
    show quotRingHom ℤ (relSub (h.rel r)) (fox (h.gmap r i) (h.rel r (h.cmap r j))) = _
    rw [h.rel_cmap r j, fox_map (h.gmap r) (h.gmap r).injective i (ρ j), h.quot_freeRingMap r] <;> rfl
  bdry_new := by
    intro r a ha j
    letI := h.decGen r
    show quotRingHom ℤ (relSub (h.rel r)) (fox a (h.rel r (h.cmap r j))) = 0
    simp_all [h.rel_cmap, fox_map_of_not_mem_range, map_zero]
  zero_pi2 := fun r hr u hu => h.zero_pi2_coords r hr u hu

/-- **Cycles lift modulo `m`**: for a chain of presentation complexes this is not a
hypothesis but a theorem, because `H₁` of the universal cover of a stage vanishes. -/
theorem cycleLiftsMod_toChainInput (m : ℕ) : CycleLiftsMod h.toChainInput m := by
  intro r _ u hu
  letI := h.decGen r
  obtain ⟨v, hv, z, hz⟩ := fs_exists_cycle_of_boundary_nsmul (h.rel r) m u
    (fun i => by simpa only [fs_coverSecondBoundary_apply, toChainInput, bdry, foxMatrixPres] using hu i)
  refine ⟨v, ?_, z, hz⟩
  intro i
  have hi := congrArg (fun c => c i) hv
  simpa only [fs_coverSecondBoundary_apply, toChainInput, bdry, foxMatrixPres, Finsupp.zero_apply] using hi

end PresChainFS

/-- **The cell-level chain hypothesis follows from chains of nested presentation
complexes.** -/
theorem hasCellChainsLift_of_presChainsFS [DecidableEq α]
    (ρ : J → FreeGroup α)
    (hchains : ∀ n : ℕ, Nonempty (PresChainFS ρ n)) :
    HasCellChainsLift (foxMatrixPres ρ) := by
  intro n
  obtain ⟨h⟩ := hchains n
  exact ⟨fun r => PresGroup (h.rel r), fun _ => inferInstance, h.gen, h.cell, h.toChainInput,
    h.cycleLiftsMod_toChainInput⟩

end FiniteChains
