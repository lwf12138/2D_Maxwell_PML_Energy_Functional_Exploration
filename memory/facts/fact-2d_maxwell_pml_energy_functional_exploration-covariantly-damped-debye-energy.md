---
fact_id: fact:2d_maxwell_pml_energy_functional_exploration:covariantly-damped-debye-energy
problem_id: 2d_maxwell_pml_energy_functional_exploration
source_project: 2d_maxwell_pml_energy_functional_exploration
source_task: task-stage2-repair-design
predecessors:
  - fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance
  - fact:2d_maxwell_pml_energy_functional_exploration:edge-pml-linear-obstruction
status: verified
fact_type: energy_identity
review_level: verified
claim_policy: stable_claim
claim_summary: "The covariantly damped alpha=1 Maxwell-Debye absorbing-layer model has a positive monotone energy identity."
verification: verify-20260620T022411192181Z-fact-the-covariantly-damped-alpha-1-maxw
---

## statement

For nonnegative time-independent layer profiles rho_x,rho_y in L-infinity(Omega), rho=rho_x+rho_y, and D_rho=partial_t+rho, the modified alpha=1 Maxwell-Debye absorbing-layer model epsilon0 epsilon_infty D_rho E = partial_x H_y - partial_y H_x - D_rho P, mu(partial_t+rho_y)H_x=-partial_y E, mu(partial_t+rho_x)H_y=partial_x E, and P+tau D_rho P=chi E with PEC E=0 has the positive energy E_rho=1/2 int_Omega (epsilon0 epsilon_infty E^2 + mu H_x^2 + mu H_y^2 + chi^{-1} P^2). Smooth solutions satisfy dE_rho/dt = - int_Omega (epsilon0 epsilon_infty rho E^2 + mu rho_y H_x^2 + mu rho_x H_y^2 + rho chi^{-1} P^2 + tau chi^{-1} |D_rho P|^2) <= 0. The identity follows by multiplying the field equations by E,H_x,H_y, using PEC cancellation of the Maxwell principal flux, and using E D_rho P = (2 chi)^{-1} partial_t(P^2) + rho chi^{-1} P^2 + tau chi^{-1}|D_rho P|^2.

## notes

Proof artifact: artifacts/proofs/stage2_repair_design.md
