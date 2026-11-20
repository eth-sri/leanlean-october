module

public import GS.Shared.CosineSine

public import GS.Shared.BlockCoordinates

public import GS.Shared.OrbitAtlas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS.Shared Set
namespace GS.Shared.Singularity
attribute [local fun_prop] Factor.continuous_matrix
variable {𝕜 : Type*} [RCLike 𝕜] {q n : ℕ}

/-- The shared-factor chart with one physical block is a chart of the full group. -/
def fullPattern (𝕜 : Type*) (n : ℕ) : Pattern 𝕜 n :=
  ⟨n, dvd_rfl, fun _ => 0⟩

abbrev FullU (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := Factor (fullPattern 𝕜 n)

abbrev FullModel (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := Generator (fullPattern 𝕜 n)

theorem full_supported (A : M 𝕜 n) : CSupported (fun i : Fin n => i.val / n) A := by
  intro i j h
  grind [Nat.div_eq_of_lt]

theorem full_tied (A : M 𝕜 n) : TiedEntries (fullPattern 𝕜 n).size (fun _ => 0) A := by
  intro i j i' j' _ _ _ hi hj
  grind [fullPattern, Nat.mod_eq_of_lt, Fin.ext_iff]

def asFull (A : M 𝕜 n) (h : Unitary A) : FullU 𝕜 n :=
  Factor.ofMatrix A ⟨full_supported A, h, full_tied A⟩

def asModel (A : M 𝕜 n) (h : IsSkewHermitian A) : FullModel 𝕜 n :=
  ⟨A, full_supported A, h, full_tied A⟩

abbrev Blocks (𝕜 : Type*) (q : ℕ) := Matrix (Fin q) (Fin q) (M 𝕜 2)

abbrev Anchor (o : Fin q) := Fin q ⊕ {j : Fin q // j ≠ o}

abbrev Outer (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) (o : Fin q) := Anchor o → FullU 𝕜 2

abbrev Parameters (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) :=
  (Fin q → FullU 𝕜 2) × (Fin 2 → FullU 𝕜 q) × (Fin q → FullU 𝕜 2)

def diagTwo (a b : 𝕜) : M 𝕜 2 := diagonal ![a,b]

theorem diagTwo_conjTranspose (a b : 𝕜) : (diagTwo a b)ᴴ = diagTwo (star a) (star b) := by
  simp [diagTwo]

@[simp] theorem diagTwo_equal (a : 𝕜) : diagTwo a a = a • (1 : M 𝕜 2) := by
  ext i j
  fin_cases i, j <;> simp [diagTwo]

theorem diagTwo_eta (v : Fin 2 → 𝕜) : diagTwo (v 0) (v 1) = diagonal v := by
  funext i; fin_cases i <;> rfl

abbrev rawMid (p : Parameters 𝕜 q) (a : Fin 2) : M 𝕜 q := Factor.matrix (p.2.1 a)

def blockImage (p : Parameters 𝕜 q) : Blocks 𝕜 q := fun i j =>
  Factor.matrix (p.1 i) * diagonal (fun a => rawMid p a i j) * Factor.matrix (p.2.2 j)

theorem blockImage_continuous : Continuous (@blockImage 𝕜 _ q) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold blockImage
  refine (Continuous.mul (by fun_prop) ?_).mul (by fun_prop)
  exact (continuous_pi fun a => (Factor.continuous_matrix.comp (by fun_prop)).matrix_elem i j).matrix_diagonal

abbrev pairIndex (q : ℕ) : Fin q × Fin 2 ≃ Fin (q*2) := finProdFinEquiv

abbrev flattenBlocks := ⇑(blockFlatten (𝕜 := 𝕜) (pairIndex q))

theorem continuous_flattenBlocks : Continuous (flattenBlocks (𝕜 := 𝕜) (q := q)) := by
  apply continuous_matrix
  intro i j
  let x := (pairIndex q).symm i
  let y := (pairIndex q).symm j
  exact ((continuous_apply y.1).comp (continuous_apply x.1)).matrix_elem x.2 y.2

abbrev middleIndex (q : ℕ) := shuffleIndex q 2

private theorem sandwich (p : Parameters 𝕜 q) :
    let P := permMatrix (𝕜 := 𝕜) (GS.scalarShuffle q 2)
    flattenBlocks (blockImage p) =
      product3 (packBlocks (pairIndex q) (Factor.matrix ∘ p.1)) Pᴴ
        (packBlocks (middleIndex q) (Factor.matrix ∘ p.2.1)) P
        (packBlocks (pairIndex q) (Factor.matrix ∘ p.2.2)) := by
  dsimp only [product3]
  rw [Matrix.mul_assoc (packBlocks (pairIndex q) _) _ _, Matrix.mul_assoc (packBlocks (pairIndex q) _) _ _]
  apply (blockView (pairIndex q)).injective
  rw [RingEquiv.symm_apply_apply]
  funext i j
  rw [blockView_pack_sandwich, blockView_shuffle]
  rfl

def shuffleFamily (𝕜 : Type*) [RCLike 𝕜] (q : ℕ) : Set (M 𝕜 (q*2)) :=
  let P := permMatrix (𝕜 := 𝕜) (GS.scalarShuffle q 2)
  {X | InA3Unitary 2 q 2 P Pᴴ X}

private theorem supported_full_iff {k b n s : ℕ} (e : Fin k × Fin b ≃ Fin n)
    (he : ∀ x, (e x).val / s = x.1.val) (A : M 𝕜 n) :
    (BlockDiagonal s A ∧ Unitary A) ↔ ∃ D : Fin k → FullU 𝕜 b, A = packBlocks e (Factor.matrix ∘ D) := by
  rw [supported_blocks_iff e he]
  exact ⟨fun ⟨D,hD,h⟩ => ⟨fun i => asFull (D i) (hD i),h⟩,
    fun ⟨D,h⟩ => ⟨_,fun i => Factor.matrix_unitary (D i),h⟩⟩

theorem shuffleFamily_eq_range (q : ℕ) :
    shuffleFamily 𝕜 q = range (flattenBlocks ∘ blockImage) := by
  ext X
  let P := permMatrix (𝕜 := 𝕜) (GS.scalarShuffle q 2)
  change InA3Unitary 2 q 2 P Pᴴ X ↔ _
  have outer := supported_full_iff (𝕜 := 𝕜) (pairIndex q) standard_block_label
  have inner := supported_full_iff (𝕜 := 𝕜) (middleIndex q) shuffleIndex_label
  constructor
  · rintro ⟨R,D,L,hsR,hsD,hsL,huR,huD,huL,hX⟩
    obtain ⟨R,rfl⟩ := (outer R).mp ⟨hsR,huR⟩
    obtain ⟨D,rfl⟩ := (inner D).mp ⟨hsD,huD⟩
    obtain ⟨L,rfl⟩ := (outer L).mp ⟨hsL,huL⟩
    exact ⟨(L,D,R),(sandwich (L,D,R)).trans hX.symm⟩
  · rintro ⟨p,rfl⟩
    have hR := (outer _).mpr ⟨p.2.2,rfl⟩
    have hD := (inner _).mpr ⟨p.2.1,rfl⟩
    have hL := (outer _).mpr ⟨p.1,rfl⟩
    exact ⟨_,_,_,hR.1,hD.1,hL.1,hR.2,hD.2,hL.2,sandwich p⟩

end GS.Shared.Singularity
