module
public import GS.M4Certificate
public import GS.M4Necessary
public import GS.Unitary.RealEmbedding
@[expose] public section
noncomputable section
open Matrix GS.Isometric
namespace GS.M4
variable (𝕜 : Type*) [RCLike 𝕜]
/-- The same real certificate works after any scalar extension: packing,
products and the four determinant moduli are preserved. -/
theorem counterexample : let p := wiring 𝕜; let q := extendReal 𝕜 Q
    In₄ 2 2 2 2 p p p q ∧ IsU q ∧ ¬In₄U 2 2 2 2 p p p q := by
  refine ⟨?_,extend_unitary 𝕜 Q_orthogonal,?_⟩
  · obtain ⟨R,Y,W,L,r,y,w,l,e⟩ := Q_mem_A4
    have side (A : Mat 6) (h : BlockDiagonal 2 A) : DiagonalBlocks 2 (extendReal 𝕜 A) := fun i j h' => by simp [extendReal,h i j h']
    exact ⟨_,_,_,_,side _ r,side _ y,side _ w,side _ l,by simpa [product4,chain4,map_mul] using congrArg (extendReal 𝕜) e⟩
  · rintro ⟨R,Y,W,L,r,y,w,l,ur,uy,uw,ul,e⟩
    have h : minors (extendReal 𝕜 Q) = minors Q := by
      funext i j; simp only [minors,minor_apply,extendReal,RingHom.mapMatrix_apply,Matrix.map_apply,← map_mul,← map_sub]; exact RCLike.norm_ofReal _
    apply violates; rw [← h,e]; exact necessary l w y r ul uw uy ur
end GS.M4
