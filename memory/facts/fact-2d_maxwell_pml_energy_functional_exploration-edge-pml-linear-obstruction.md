---
fact_id: fact:2d_maxwell_pml_energy_functional_exploration:edge-pml-linear-obstruction
problem_id: 2d_maxwell_pml_energy_functional_exploration
source_project: 2d_maxwell_pml_energy_functional_exploration
source_task: task-alpha1-pml-cases
predecessors:
  - fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance
status: verified
fact_type: obstruction
review_level: verified
claim_policy: stable_claim
claim_summary: "The alpha=1 source model has exact edge-PML solutions with linear H-Q growth, ruling out an unconditional positive monotone or uniformly bounded energy for all eight variables."
verification: verify-20260619T181255226823Z-fact-the-alpha-1-source-model-has-exact-
---

## statement

For the alpha=1 source Maxwell-PML system with arbitrary initial data for all eight displayed unknowns, constant edge absorptions produce exact linearly growing solutions. If sigma_x=s>0 and sigma_y=0, set E=P=P_{z,1}=P_{z,2}=H_y=Q_y=0 and take H_x,Q_x spatially constant. Then the equations reduce to H_{x,t}=b H_x+Q_x/mu and Q_{x,t}=-b Q_x-mu b^2 H_x with b=s/epsilon_0. The shifted quantity M_x=Q_x+mu b H_x is constant, so H_x(t)=H_x(0)+M_x(0)t/mu and Q_x(t)=Q_x(0)-b M_x(0)t. If M_x(0) is nonzero, H_x and Q_x grow linearly while the PEC condition is satisfied because E=0. The symmetric construction with sigma_x=0,sigma_y=s>0 gives linear growth of H_y,Q_y through constant M_y=Q_y+mu b H_y. Therefore no positive coercive energy controlling the displayed H_i,Q_i variables can be monotone decreasing or uniformly bounded for all source-system data under the full edge-PML assumptions as stated. Detailed proof is in artifacts/proofs/alpha1_constant_pml_cases.md.

## notes

Exact counterexample, not numerical evidence; relies on the verified alpha=1 algebra and the source equations.
