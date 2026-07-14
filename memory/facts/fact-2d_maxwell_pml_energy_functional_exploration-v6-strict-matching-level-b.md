---
fact_id: fact:2d_maxwell_pml_energy_functional_exploration:v6-strict-matching-level-b
problem_id: 2d_maxwell_pml_energy_functional_exploration
source_project: 2d_maxwell_pml_energy_functional_exploration
source_task: task-v6-terminal-assembly
predecessors:
  - fact:2d_maxwell_pml_energy_functional_exploration:standard-stretched-pml-matching-and-1d-energy
  - fact:2d_maxwell_pml_energy_functional_exploration:baffet-primitive-stretched-debye-2d-energy
  - fact:2d_maxwell_pml_energy_functional_exploration:variable-baffet-remainder-small-gradient
status: verified
fact_type: energy_estimate
review_level: verified
claim_policy: stable_claim
claim_summary: "Strict variable-profile Maxwell-Debye PML is perfectly matched and has a Level-B pointwise-Schur monotone Baffet energy on uniformly positive corner layers."
verification: verify-20260714T112741879698Z-fact-reverify-fact-2d_maxwell_pml_energy
---

## statement

For separated nonnegative W^{1,infinity} profiles, the causal Baffet primitive system is Laplace-equivalent to the strict stretched-coordinate Maxwell-Debye PML. At a flat x-interface with S_y=1, fixing the causal outgoing square-root branch gives Y_+=Y_0 and R=0 for every Re s>0 and real k_y, including arbitrary normal sigma_x(x). On a corner subdomain where sigma_x and sigma_y have positive lower bounds, with compatible state and nonpositive boundary flux, the Baffet energy is equivalent to the primitive natural norm and satisfies E_B prime plus theta D_0 <=0 whenever (grad a)^T C_lambda^{-1}(grad a) <= 4(1-delta)c_u uniformly for some delta>0, where c_u=mu epsilon a b. This is conditional Level B, not an unconditional all-profile theorem, and it does not assert zero finite-truncation reflection.

## notes

Evidence: results/v6_tex/nonlocal_memory_strict_pml_report.md sections 2-4; TeX theorem; Lean/SymPy outputs.
