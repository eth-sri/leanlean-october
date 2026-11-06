import Solution
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `GSPalomar.two_factor, `GSPalomar.three_factor, `GSPalomar.four_factor_counterexample,
    `GSPalomar.unitary_two_factor, `GSPalomar.unitary_three_factor,
    `GSPalomar.unitary_four_factor_counterexample, `GSPalomar.real_cs_exhaustion,
    `GSPalomar.unitary_cs_exhaustion, `GSPalomar.rank_one_cone_singularity,
    `GSPalomar.real_three_factor_singularity, `GSPalomar.real_singular_point,
    `GSPalomar.unitary_singular_point, `GSPalomar.orthogonal_shared_geometry,
    `GSPalomar.unitary_shared_geometry, `GSPalomar.two_factor_rank_criterion,
    `GSPalomar.orthogonal_shared_block_geodesic]
  let mut seen : NameSet := {}
  let mut stack := targets.toList
  while !stack.isEmpty do
    let some n := stack.head? | unreachable!
    stack := stack.tail
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        stack := ci.type.getUsedConstants.toList ++
          (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants.toList | none => []) ++ stack
  let mods := env.header.moduleData
  let names := env.header.moduleNames
  let mut out := #[]
  for i in [:mods.size] do
    let mn := names[i]!
    if mn.toString.startsWith "GS" then
      let k := (mods[i]!.constNames.filter (fun c => seen.contains c)).size
      out := out.push s!"{mn} {k}"
  IO.FS.writeFile "/tmp/curmods.txt" (String.intercalate "\n" out.toList)
  IO.println out.size
