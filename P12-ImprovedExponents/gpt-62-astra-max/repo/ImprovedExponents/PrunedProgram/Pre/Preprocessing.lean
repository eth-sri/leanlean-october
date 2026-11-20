module

public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ImprovedExponents.PrunedProgram.Boxes.Routines

@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents
variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

namespace Build
slots 0 Levels Inner Switch Size Width MatX MatY Base Void
abbrev readDir (k₀ : ℕ) := M (v Base +' k k₀)
end Build

open Build in
def preCorePBody : Stmt :=
  let wd := readDir Dir.sharedEnd
  let cur := wd +' v Levels
  let box := cur +' v Levels
  .call Proc.sharedP [v Levels,v Inner,v Size,v Width,v MatX,v MatY,v Base] Void ;;
  .store (v Base +' k Dir.switch) (v Switch) ;;
  .call Proc.allTiles [readDir Dir.encA,readDir Dir.encB,readDir Dir.bands,readDir Dir.leaves,
    cur,box,box +' v Levels +' v Inner,v Levels,v Inner -' v Switch] Void

private theorem gridSafe (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) :
    (grid p t hmL b0 X Y).Safe lim μ := by
  -- a negative bound U is possible only if there are no entries; then 0 is a bound as well
  obtain ⟨U', hU0, hX', hY', hvalue⟩ : ∃ U' : ℤ, 0 ≤ U' ∧ (∀ i j, |X i j| ≤ U') ∧
      (∀ i j, |Y i j| ≤ U') ∧ 10 ^ p.m * ((7 ^ p.L * U') * (7 ^ p.L * U')) ≤ lim.word := by
    rcases le_or_gt 0 U with h0 | h0
    · exact ⟨U, h0, hX, hY, h.value⟩
    · have hword : 0 ≤ lim.word := le_trans (by norm_num) h.std.const_le
      exact ⟨0, le_rfl, by grind,
        by grind, by assumption⟩
  have hsp := h.space
  have hT : 10^p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  refine ⟨h.std,⟨ht,hmL⟩,?_,⟨7^p.L*U',7^p.L*U',?_,?_,hvalue⟩,hSR.encA,hSR.encB⟩
  · dsimp [grid,BoxTable.Grid.cells,BoxTable.stride]; rw [hT]; unfold pageCells at *; omega
  · exact fun i => (abs_enc_le hmL X Y U' hU0 hX' hY' i i).1
  · exact fun i => (abs_enc_le hmL X Y U' hU0 hX' hY' i i).2

theorem preCoreP_of_tiles {c} (procs : BoxTable.Has P)
    (text : P[Proc.preCoreP]? = some preCorePBody) (hShared : Sec2.SharedSpecP lim P c) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hX hY hMX hMY haX haY
  refine fun d hd => ⟨preCorePBody, text, ?_⟩
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCoreP
  -- the pruned shared stage
  light_call (hShared p hmL aX aY b0 μ X Y U
    { space := by omega, matX := hMX, matY := hMY, belowX := haX, belowY := haY, absX := hX
      absY := hY, seven := hlim.enc, ten := hlim.pow }) with r μ₁ ⟨hSR₁, same₁⟩
  -- dir[31] := t
  light_store (b0 + 31) t
  have hSR₂ : Sec2.SharedReadyP p hmL aX aY b0 X Y (Function.update μ₁ (b0 + 31) t) :=
    by apply hSR₁.of_agree <;> grind
  let x := grid p t hmL b0 X Y
  have safe := gridSafe hlim ht hX hY hSR₂
  let ν := Function.update μ₁ (b0+31) (t:ℤ)
  have step := BoxTable.Grid.spec (BoxTable.passes procs hlim.std) (procs 9 (by decide))
    (procs 10 (by decide)) safe (d:=d+1) (by omega)
  have meets := Meets.of_body (Q:=fun _ τ => x.Done τ (x.n*x.n) ∧ x.Far ν τ) (procs 11 (by decide)) step
  have dir := hSR₂.dirCells
  have room := wd_ge p b0
  have hx := hlim.std.const_le
  have leafVal : (10:ℤ)^p.L = (p.T:ℤ) := by change _ = ((10^p.L:ℕ):ℤ); simp
  have map := areas p t b0
  rcases map with ⟨dirB,maskB,bandB,blockB,digB,aB,bB,curB,boxB,ssB,pageB,topB⟩
  light_call meets using Build.readDir,BoxTable.Grid.args,grid,dir.encA,dir.encB,dir.bands,dir.leaves,dir.sharedEnd,
    curB,boxB,pageB with _ τ ⟨ready,same⟩
  change SameOn (fun b => b < aCUR p b0 ∨ aPage p b0 + pageCells p ≤ b) ν τ at same
  refine ⟨⟨hSR₂.of_agree (fun b hb _ => same b (Or.inl (by omega))),?_,ready⟩,fun b hb => ?_⟩
  · change τ (b0+31) = _; rw [same (b0+31) (by left; omega)]; apply Function.update_self
  · change τ b = _; rw [same b (by omega)]; dsimp [ν]; rw [Function.update_of_ne (by omega), same₁ b (by omega)]

end Light.Sec4
