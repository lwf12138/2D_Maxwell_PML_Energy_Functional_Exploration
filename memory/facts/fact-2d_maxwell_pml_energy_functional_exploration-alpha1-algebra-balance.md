---
fact_id: fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance
problem_id: 2d_maxwell_pml_energy_functional_exploration
source_project: 2d_maxwell_pml_energy_functional_exploration
source_task: task-alpha1-algebra-energy-balance
predecessors:
  - fact:2d_maxwell_pml_energy_functional_exploration:run-20260619T173930696222Z:source-problem
status: verified
fact_type: energy_identity
review_level: verified
claim_policy: stable_claim
claim_summary: "Alpha=1 PEC balance and shifted magnetic identities are valid for the source Maxwell-PML system."
verification: verify-20260619T180514214437Z-fact-alpha-1-pec-balance-and-shifted-mag
---

## statement

For the source 2D TM Maxwell-PML system with alpha=1 polarization law P + tau P_t = chi E and PEC boundary condition E=0 on dOmega, multiplying the first three equations by E,H_x,H_y and integrating gives the electromagnetic balance displayed in the source: the principal Maxwell contribution is the boundary flux integral int_dOmega E(H_y n_x - H_x n_y) ds and vanishes under PEC. The alpha=1 identity E P_t = (1/(2 chi)) d_t ||P||_2^2 + (tau/chi)||P_t||_2^2 makes E_em + (1/(2 chi))||P||_2^2 positive and adds dissipation (tau/chi)||P_t||_2^2. With a_x=(sigma_y-sigma_x)/epsilon_0, a_y=(sigma_x-sigma_y)/epsilon_0, b_x=sigma_x/epsilon_0, b_y=sigma_y/epsilon_0, and M_x=Q_x-mu a_x H_x, M_y=Q_y-mu a_y H_y, the shifted equations are mu H_{x,t}=-partial_y E+M_x, mu H_{y,t}=partial_x E+M_y, M_{x,t}=a_x partial_y E-b_y M_x, and M_{y,t}=-a_y partial_x E-b_x M_y. Substituting Q_x=M_x+mu a_x H_x and Q_y=M_y+mu a_y H_y cancels the sign-indefinite magnetic square terms in the E_em+P balance and leaves the magnetic coupling H_x M_x+H_y M_y. Detailed derivation is in artifacts/proofs/alpha1_algebra_balance.md.

## notes

Produced by inline algebra verification; artifact indexed at artifacts/proofs/alpha1_algebra_balance.md.
