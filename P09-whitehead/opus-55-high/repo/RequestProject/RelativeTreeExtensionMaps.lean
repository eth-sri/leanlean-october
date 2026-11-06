import RequestProject.RelativeTreeExtension


/-! Cell inclusions between relative tree extensions with the same
extra generators. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.RelativeTreeExtension
open SpanningTree
variable {D : Complex2} (T : SpanningTree D) {Z S R : Type}
  (extra : S → FreeGroup (NonTree T ⊕ Z))
  (extra' : R → FreeGroup (NonTree T ⊕ Z))
  (f : S → R) (hf : ∀ s, extra' (f s) = extra s)

def inclusion : Hom (complex T extra) (complex T extra') where
  onV := id
  onE := id
  onF := Sum.map id f
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF := by rintro (d | s) <;> rfl
  att_onF := by
    intro s
    cases s with
    | inl d => simp [complex]
    | inr s => simp [complex, hf]
