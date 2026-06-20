#!/usr/bin/env bash
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

mkdir -p results

GOAL=$(cat <<'EOF'
Analyze the verified obstruction in results/energy_functional_report_verified.md and then start a second-stage constructive search.

The previous run showed that the original eight-variable 2D Maxwell--PML model admits an edge-PML linear-growth obstruction for arbitrary auxiliary-variable initial data. Therefore, do not stop at re-verifying that obstruction.

Main goal:
Construct or propose a modified 2D Maxwell--PML formulation, auxiliary-variable transformation, compatibility condition, damping design, MPML/CFS-type modification, or equivalent PML model that admits a monotone decreasing energy functional or a genuinely dissipative long-time bounded energy estimate.

Allowed changes:
1. You may introduce new auxiliary variables or shifted variables.
2. You may impose physically meaningful compatibility conditions on PML auxiliary variables.
3. You may modify the PML equations if the modified model still behaves as an absorbing layer for 2D Maxwell waves.
4. You may consider MPML-type multi-axial damping, CFS-PML-type frequency shifted damping, or Baffet-type time-integrated variables.
5. You may first work with alpha = 1, then discuss whether 0 < alpha < 1 can be added later.
6. You may first solve edge PML, then corner PML.

Do not treat "the old model has an obstruction" as final success. That is already known.

Work plan:
1. Identify exactly which old-model term causes edge-PML linear growth.
2. Propose at least three possible repairs:
   - compatibility restriction on auxiliary initial data;
   - shifted-variable reformulation eliminating the free growing mode;
   - modified damping/PML equation such as CFS-PML, MPML, or equivalent Berenger-type model.
3. For each repair, derive the candidate energy functional.
4. Test positivity of the candidate energy.
5. Compute the energy derivative.
6. Decide whether the energy is:
   - monotone decreasing;
   - dissipative with lower-order controlled terms;
   - uniformly bounded;
   - only Gronwall bounded;
   - or invalid.
7. Select the most promising repaired model and write a detailed derivation.

Required final artifact:
write the final report to results/energy_design_v2_report.md.

The final report must include:
- the obstruction from the previous run;
- proposed modified model(s);
- exact equations of the best candidate model;
- proposed energy functional;
- positivity proof or positivity conditions;
- energy identity or inequality;
- whether the result is monotone, dissipative, uniformly bounded, or only Gronwall;
- remaining open problems.
EOF
)

iteris run . \
  --goal "$GOAL" \
  --target-artifact results/energy_design_v2_report.md \
  --foreground \
  --new-session
