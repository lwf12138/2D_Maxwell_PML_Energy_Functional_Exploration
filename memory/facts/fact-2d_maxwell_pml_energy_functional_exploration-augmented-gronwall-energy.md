---
fact_id: fact:2d_maxwell_pml_energy_functional_exploration:augmented-gronwall-energy
problem_id: 2d_maxwell_pml_energy_functional_exploration
source_project: 2d_maxwell_pml_energy_functional_exploration
source_task: task-alpha1-pml-cases
predecessors:
  - fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance
status: verified
fact_type: energy_estimate
review_level: verified
claim_policy: stable_claim
claim_summary: "A positive augmented zeroth-order energy gives a Gronwall estimate for bounded nonnegative time-independent absorptions in the alpha=1 source model."
verification: verify-20260619T181650715321Z-fact-a-positive-augmented-zeroth-order-e
---

## statement

For the alpha=1 source Maxwell-PML system with PEC boundary condition and bounded nonnegative time-independent sigma_x,sigma_y, the positive augmented energy E_0(t)=1/2 int_Omega (epsilon_0 epsilon_infty E^2+mu H_x^2+mu H_y^2+chi^{-1}P^2+P_{z,1}^2+P_{z,2}^2+Q_x^2+Q_y^2) dxdy satisfies dE_0/dt <= C_G E_0. The finite constant C_G depends only on the positive material parameters and the L_infty sizes of sigma_x, sigma_y, sigma_x sigma_y, sigma_x(sigma_y-sigma_x), and sigma_y(sigma_x-sigma_y). The estimate follows by adding the L2 derivatives of P_{z,1}, P_{z,2}, Q_x, Q_y to the verified alpha=1 electromagnetic-plus-polarization balance, dropping nonpositive terms, and applying Young's inequality to EP, EP_{z,1}, EP_{z,2}, H_xQ_x, H_yQ_y, and the sign-indefinite H-square terms. Hence E_0(t) <= exp(C_G t) E_0(0). This is a Gronwall-type estimate, not a monotone or uniform long-time boundedness result. Detailed proof is in artifacts/proofs/alpha1_constant_pml_cases.md.

## notes

Closed zeroth-order estimate; no sampling evidence used.
