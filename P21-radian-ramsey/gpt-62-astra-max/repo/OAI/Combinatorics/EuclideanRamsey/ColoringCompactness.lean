/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathSynchronization
public import OAI.Combinatorics.EuclideanRamsey.UltrafilterStrings

public section

namespace OAI.EuclideanRamsey

theorem paths_monochromatic {s : ℕ} (a : Fin s → ℂ)
    (wide : Wide a)
    {κ : Type*} [Finite κ] (coloring : Strings → κ) :
    ∃ l : List Sim, energy l = 1 ∧ ∃ k, ∀ i, coloring (word (a i) l) = k := by
  classical
  obtain ⟨β,hβ,hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) κ
  obtain ⟨W,hW⟩ := unit_shares wide (Fintype.card β)
  obtain ⟨Ψ,hΨ⟩ := exists_profiles a
  let L : List β := Finset.univ.toList
  let w (x : β → Fin s) := (L.map (W ∘ x)).prod
  choose C hC using fun x => Ultrafilter.eq_pure_of_finite ((Ψ (w x)).map coloring)
  obtain ⟨line,k,hline⟩ := hHJ C
  let S : Finset β := Finset.univ.filter (fun j => line.idxFun j=none)
  have hpos : 0 < S.card := Finset.card_pos.mpr (by simpa [S,Finset.Nonempty] using line.proper)
  let u (j : β) : ℝ := if j∈S then (S.card:ℝ)⁻¹ else 0
  have step (j : β) : Path a (fun i => W (line i j)) (u j) := by
    cases he : line.idxFun j with
    | none => simpa [u, S, he] using hW S.card (Finset.card_le_univ _) hpos
    | some k => simpa [u, S, he] using Path.diag (a:=a) (W k)
  have weight : (L.map u).sum = 1 := by simp [L,u,hpos.ne']
  have walk : Path a (fun i => w (line i)) 1 := weight ▸ Path.list L step
  obtain ⟨x,hx,h⟩ := hΨ walk (fun _ => {x | coloring x=k}) (fun i => by
    change {k} ∈ (Ψ (w (line i))).map coloring
    simp [*])
  exact ⟨x,hx,k,h⟩

end OAI.EuclideanRamsey
