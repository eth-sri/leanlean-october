# LeanLean October 2026: projects and model submissions

The 32 Lean projects of [LeanLean](https://matharena.ai/) October 2026, and what 5 models made of them. Each agent had 12 hours per project to make the codebase as small as it could, in Lean tokens, while the project still builds, uses only the permitted axioms and keeps every protected theorem's statement.

## Layout

```
P01-DedekindZetaZeroFree/
  problem.json        benchmark entry: upstream repository and commit, license, protected theorems, ...
  base/               baseline source tree
  base-graph.json     declaration dependency graph of base/
  opus-55-high/
    repo/             submitted source tree
    diff.patch        git diff from base/ to repo/
    graph.json        declaration dependency graph of repo/
    result.json       status, tokens, compression, cost and time
  ...
```

Problems are numbered largest first by baseline tokens. Source trees leave out hidden paths (`.lake`, `.gitignore`, agent scratch files), as in scoring. Graphs are created by lean-strip.

A failed submission is scored at its latest saved checkpoint that passes final verification, and `repo/` holds that checkpoint (`result.json` has a `verification_note`). A `failed` status means no checkpoint passed: the submission gets no credit and has no `graph.json`.

## History

Each problem has a baseline commit, which adds the problem and seeds every model's `repo/` with a copy of `base/`. One commit per model follows, turning that copy into the submission, so the model's change is exactly that commit's diff:

```bash
git log --oneline
git show <commit> -- P01-DedekindZetaZeroFree/opus-55-high/repo
git log -p --reverse -- 'P*/kimi-k31-pro/repo'
```

`diff.patch` holds the same diff with paths relative to the project root, so `git apply diff.patch` in a copy of `base/` reproduces `repo/` (outside any git checkout, where `git apply` would skip paths outside the current directory).

## Models

| Folder | Model | Harness |
|---|---|---|
| `gpt-61-sol-max` | GPT-6.1 Sol (max) | Codex 0.159.0 |
| `opus-55-high` | Claude-Opus-5.5 (high) | Claude Code 2.1.280 |
| `gemini-4-argon` | Gemini 4 Argon | Antigravity 1.3.5 |
| `kimi-k31-pro` | Kimi K3.1 Pro | Kimi Code 2.3.1 |
| `deepseek-v41-flash-dsh` | DeepSeek-V4.1-Flash-1017 (Max) | DeepSeek Harness 0.2.1-rc.5 |

## Results

Credited compression in percent (token reduction against the baseline, zero for failed submissions).

| Problem | Baseline tokens | `gpt-61-sol-max` | `opus-55-high` | `gemini-4-argon` | `kimi-k31-pro` | `deepseek-v41-flash-dsh` |
|---|---:|---:|---:|---:|---:|---:|
| [P01-DedekindZetaZeroFree](P01-DedekindZetaZeroFree) | 10,053,215 | 13.3 | 13.9 | 0.0 | 7.0 | 4.7 |
| [P02-zeta-density-39-over-17-lean](P02-zeta-density-39-over-17-lean) | 8,602,200 | 7.1 | 9.8 | 7.3 | 0.0 (failed) | 0.8 |
| [P03-erdos-408](P03-erdos-408) | 6,268,302 | 10.1 | 4.9 | 0.0 | 0.9 | 1.1 |
| [P04-LinearTimeTriangulation-ChazelleAlgorithm-Lean4](P04-LinearTimeTriangulation-ChazelleAlgorithm-Lean4) | 4,338,771 | 12.8 | 27.3 | 1.6 | 1.7 | 1.9 |
| [P05-DOZZ](P05-DOZZ) | 2,992,942 | 15.7 | 12.8 | 11.8 | 0.0 (failed) | 1.2 |
| [P06-hypoelliptic-aleksandrov](P06-hypoelliptic-aleksandrov) | 2,642,100 | 17.3 | 14.3 | 10.3 | 2.3 | 2.1 |
| [P07-PottsDiscontinuity-lean](P07-PottsDiscontinuity-lean) | 1,054,327 | 24.2 | 28.7 | 16.6 | 1.9 | 0.4 |
| [P08-vaught-conjecture-palomar](P08-vaught-conjecture-palomar) | 1,043,844 | 40.5 | 32.4 | 35.8 | 28.7 | 21.8 |
| [P09-whitehead](P09-whitehead) | 975,198 | 20.4 | 25.6 | 13.4 | 4.1 | 2.9 |
| [P10-polya-neumann-simply-connected-formalization-Palomar-version-v2](P10-polya-neumann-simply-connected-formalization-Palomar-version-v2) | 903,891 | 22.0 | 17.5 | 20.3 | 2.8 | 0.0 |
| [P11-ccv-palomar](P11-ccv-palomar) | 854,028 | 12.5 | 39.0 | 16.3 | 1.9 | 3.3 |
| [P12-ImprovedExponents](P12-ImprovedExponents) | 672,860 | 27.5 | 18.5 | 18.0 | 8.0 | 3.8 |
| [P13-MIPStarRE-QPBT](P13-MIPStarRE-QPBT) | 597,369 | 12.0 | 24.8 | 15.2 | 3.4 | 3.6 |
| [P14-ccdn-dimension-growth](P14-ccdn-dimension-growth) | 552,362 | 19.2 | 24.2 | 25.9 | 2.3 | 2.3 |
| [P15-gs_Lean_formalization](P15-gs_Lean_formalization) | 303,700 | 68.2 | 65.3 | 56.2 | 23.6 | 22.7 |
| [P16-compact-albert-recognition](P16-compact-albert-recognition) | 300,239 | 64.6 | 30.2 | 43.7 | 5.8 | 4.0 |
| [P17-lean4-adr11](P17-lean4-adr11) | 175,441 | 85.0 | 59.7 | 64.9 | 7.5 | 13.9 |
| [P18-lean-dual-analytic-ifs](P18-lean-dual-analytic-ifs) | 146,557 | 66.6 | 44.8 | 46.3 | 3.5 | 6.0 |
| [P19-omega_le_nine_quarters_all_rings](P19-omega_le_nine_quarters_all_rings) | 145,127 | 77.0 | 69.6 | 52.3 | 10.1 | 1.2 |
| [P20-palomar-p046-critical-window-shape-law](P20-palomar-p046-critical-window-shape-law) | 101,498 | 59.9 | 48.9 | 33.0 | 3.0 | 5.1 |
| [P21-radian-ramsey](P21-radian-ramsey) | 81,623 | 45.8 | 64.3 | 41.2 | 5.3 | 3.9 |
| [P22-linniks-constant-3.99](P22-linniks-constant-3.99) | 80,635 | 59.9 | 53.0 | 36.7 | 7.2 | 6.7 |
| [P23-cell-attachment-lean](P23-cell-attachment-lean) | 80,254 | 93.4 | 93.2 | 86.6 | 9.9 | 5.0 |
| [P24-bergman-weak-type](P24-bergman-weak-type) | 77,810 | 67.2 | 63.0 | 41.5 | 15.9 | 14.3 |
| [P25-normalizer-lean](P25-normalizer-lean) | 34,716 | 82.3 | 73.4 | 65.6 | 20.9 | 17.2 |
| [P26-hk-heterogeneous-lean](P26-hk-heterogeneous-lean) | 27,736 | 78.1 | 63.8 | 68.8 | 30.5 | 28.2 |
| [P27-triangle-group-growth](P27-triangle-group-growth) | 25,916 | 83.0 | 76.4 | 60.3 | 25.2 | 14.6 |
| [P28-semigroup-betti](P28-semigroup-betti) | 19,921 | 87.0 | 81.9 | 75.6 | 16.8 | 15.7 |
| [P29-goldbach-lean](P29-goldbach-lean) | 17,726 | 90.2 | 83.4 | 74.8 | 26.9 | 21.5 |
| [P30-alcs](P30-alcs) | 15,133 | 80.2 | 79.9 | 60.5 | 25.7 | 16.5 |
| [P31-kkp-connected-spectral-counterexamples](P31-kkp-connected-spectral-counterexamples) | 14,983 | 86.0 | 87.2 | 84.2 | 46.7 | 47.7 |
| [P32-galvin-dinitz](P32-galvin-dinitz) | 10,465 | 85.4 | 83.0 | 69.6 | 30.1 | 18.8 |
| **Mean** | | **50.5** | **47.3** | **39.2** | **11.9** | **9.8** |

## Licenses

Each project keeps its upstream license (Apache-2.0, MIT or AGPL-3.0; see `license` in `problem.json` and the license file in `base/`). Please abide by the license of each project when using its code.
