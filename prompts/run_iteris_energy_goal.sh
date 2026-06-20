#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if [ ! -d ".iteris" ]; then
  iteris new --allow-non-empty --source sources/energy_functional_problem.tex .
fi

GOAL=$(cat <<'EOF'
Analyze sources/energy_functional_problem.tex.

Main objective: analyze the 2D Maxwell--PML system stated in sources/energy_functional_problem.tex, including the polarization variable P and the PML auxiliary variables P_{z,1}, P_{z,2}, Q_x, Q_y. The primary goal is to find a monotone decreasing energy functional in two dimensions. If no monotone energy can be found, find the strongest bounded-energy/no-abnormal-growth estimate possible, in the spirit of MPML long-time stability.

Important convention:
The non-fractional case is the alpha = 1 case of the polarization law
P + tau^alpha partial_t^alpha P = chi E.
Do not replace the model by one with P removed.

Work in the following order:

1. First verify the algebra of the displayed model, including the P equation, P_{z,1}, P_{z,2}, Q_x, Q_y, and the PEC boundary condition E_z = 0 on the boundary.
2. Start with alpha = 1, so that P + tau partial_t P = chi E. Use this identity to see whether the P contribution can be included as a positive polarization energy plus dissipation.
3. Verify the electromagnetic energy balance and isolate the problematic terms involving P, P_{z,1}, P_{z,2}, Q_x, Q_y.
4. Verify the shifted magnetic auxiliary variables
   M_x = Q_x - mu a_x H_x,
   M_y = Q_y - mu a_y H_y,
   and determine whether this shift simplifies the sign-indefinite magnetic damping terms.
5. Start with constant absorption parameters sigma_x, sigma_y.
6. Separately analyze edge PML cases:
   sigma_x > 0, sigma_y = 0;
   sigma_x = 0, sigma_y > 0.
7. Then analyze the corner PML case:
   sigma_x > 0, sigma_y > 0,
   including both sigma_x = sigma_y and sigma_x != sigma_y.
8. Try to construct a positive quadratic energy functional, allowing shifted variables, cross terms, polarization energy, and time-integrated auxiliary variables inspired by Baffet et al.
9. If a monotone energy identity cannot be obtained, identify the precise algebraic obstruction and derive the strongest bounded-energy, dissipative, or Gronwall-type estimate possible.
10. Only after the alpha = 1 model is understood, examine whether the fractional case 0 < alpha < 1 can be added as a positive memory energy.

Required final artifact:
write the final report to results/energy_functional_report.md.

The report must state:
- exact model equations used;
- whether alpha = 1 or 0 < alpha < 1 is considered;
- boundary assumptions;
- assumptions on sigma_x, sigma_y;
- proposed energy functional;
- proof of positivity or explanation of why positivity fails;
- exact energy identity or inequality;
- whether the result is monotone, bounded/no-abnormal-growth, Gronwall-type, or an obstruction result;
- whether the fractional case is included or postponed.
EOF
)

iteris run . \
  --goal "$GOAL" \
  --target-artifact results/energy_functional_report.md \
  --attach
