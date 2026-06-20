#!/usr/bin/env bash
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

if [ ! -d results ]; then
  echo "Error: expected existing results/ directory in $PROJECT_DIR" >&2
  exit 1
fi

GOAL=$(cat <<'EOF'
Stage-3 goal for the 2D Maxwell--PML energy-functional project.

Context:
The previous report results/energy_design_v2_report.md proposed a modified
covariantly damped Maxwell--Debye absorbing-layer model and verified
\[
\mathcal E_\rho(t)\le \mathcal E_\rho(0),\qquad t\ge0.
\]
This is useful, but it is not enough for the next research step.

The next goal is not merely to re-state that the energy is bounded or
non-increasing.  The next goal is:

1. Verify whether the proposed modified PML model is actually perfectly
   matched.
2. If it is perfectly matched, give a complete formula-level proof.
3. If it is not perfectly matched, identify the exact mismatch and propose a
   repaired PML model that is closer to a standard stretched-coordinate,
   Berenger, CFS-PML, MPML, or Baffet-type construction.
4. For the accepted or repaired model, construct a genuinely monotone
   decreasing/dissipative energy functional and show the full derivation of its
   energy identity.
5. If no such monotone energy can exist for the model under consideration,
   provide a formula-level obstruction, not just a qualitative statement.

Important distinction:
- "Non-increasing" means dE/dt <= 0.
- "Strictly decreasing" or "genuinely dissipative" should mean
  dE/dt = -D(t) with D(t) >= 0 and with a clear explanation of when D(t)=0.
- If strict decay of the total energy on the whole computational domain is
  impossible because waves may remain in the undamped physical region, state
  this precisely and prove the obstruction with a concrete class of solutions.
- In that case, the acceptable target is a sharp dissipative identity plus a
  no-abnormal-growth/long-time-boundedness result, and the report must explain
  why this is the strongest possible statement.

Required sources to read before drawing conclusions:
1. sources/energy_functional_problem.tex
2. results/energy_functional_report_verified.md
3. results/energy_design_v2_report.md
4. results/energy_design_v2_report_verified.md
5. references/references.bib
6. The local PDFs in references/, especially:
   - references/Joly - 2012 - An elementary introduction to the construction and the analysis of perfectly matched layers for time.pdf
   - references/Baffet ... Energy Decay and Stability of a Perfectly Matched Layer For the Wave Equation.pdf
   - references/Be*cache ... Convergence analysis of time-domain PMLS for 2D electromagnetic wave propagation in dispersive waveg.pdf
   - references/Be*cache ... On a surprising instability result of Perfectly Matched Layers for Maxwell's equations in 3D media w.pdf
   - references/Huang ... explicit unconditionally stable finite element scheme for an equivalent Berenger's PML model.pdf
   - references/A_Nonconvolutional_Split-Field_Perfectly_Matched_L.pdf
   - references/Correia*Jin ... regular PML, CFS-PML, and second-order PML.pdf
   - references/Feng ... higher-order perfectly matched layer based on ADE method.pdf
   - references/Ping ... multiaxial perfectly matched layer M-PML.pdf
   - references/main.pdf
   - references/Super.pdf
   - references/Thesis.pdf

Do not claim that a reference supports a conclusion unless you actually inspect
the relevant model, theorem, proof idea, or formula.  The final report must
include a "Literature reading record" table listing each cited reference, the
sections/pages/formulas inspected, and exactly how it was used.

Main technical tasks:

A. Define a precise perfect-matching test.
Start with a planar interface and constant PML coefficients:
- physical half-space: rho_x=rho_y=0 or sigma_x=sigma_y=0;
- PML half-space, for example x>0 with rho_x>0, rho_y=0;
- tangential Fourier mode exp(i k_y y);
- Laplace or time-harmonic ansatz in time.

Derive the transformed algebraic system, dispersion relation, normal wave
number, and wave impedance/admittance on both sides of the interface.

Perfect matching should mean that for every outgoing physical mode entering
the layer, the interface conditions admit a transmitted PML mode with zero
reflected amplitude.  Equivalently, the PML model should be representable as a
complex/stretched-coordinate continuation of the physical Maxwell--Debye
system without changing the interface impedance.

B. Test the covariantly damped Maxwell--Debye model from v2.
Use the model
\[
\epsilon_0\epsilon_\infty D_\rho E
=\partial_xH_y-\partial_yH_x-D_\rho P,
\]
\[
\mu(\partial_t+\rho_y)H_x=-\partial_yE,\qquad
\mu(\partial_t+\rho_x)H_y=\partial_xE,
\]
\[
P+\tau D_\rho P=\chi E,\qquad D_\rho=\partial_t+\rho,\quad
\rho=\rho_x+\rho_y.
\]

Check whether this model is exactly matched in the sense of Task A.
In particular, determine whether replacing the Debye law
\[
P+\tau\partial_t P=\chi E
\]
by
\[
P+\tau(\partial_t+\rho)P=\chi E
\]
preserves the correct transformed material law or changes the interface
impedance.  If it changes the impedance, compute the mismatch explicitly.

C. If the v2 covariantly damped model is not perfectly matched, construct or
propose a repaired model.
Allowed approaches include:
1. Standard stretched-coordinate PML for Maxwell--Debye:
   derive it in the Laplace domain first, then introduce auxiliary variables
   for the time-domain model.
2. Berenger split-field PML or an equivalent unsplit auxiliary-variable form.
3. CFS-PML/ADE-PML if frequency shifting is needed for long-time behavior.
4. MPML-type damping if standard PML is unstable or not dissipative.
5. Baffet-type time-integrated variables or augmented variables to obtain a
   positive energy.

The repaired model must state:
- exact PDE system;
- boundary/interface conditions;
- assumptions on sigma_x, sigma_y or rho_x, rho_y;
- whether coefficients are constant, piecewise constant, or spatially varying;
- whether the model is perfect matching, stable only, or merely absorbing.

D. Construct a monotone/dissipative energy functional.
For each serious candidate model, give:
1. the exact candidate energy functional;
2. positivity proof, including conditions on coefficients and cross terms;
3. step-by-step multiplication/integration-by-parts calculation;
4. all boundary terms and why they vanish or have a sign;
5. final identity
   \[
   \frac{d}{dt}\mathcal E(t)=-\mathcal D(t)
   \]
   or final inequality with every remainder term displayed;
6. classification:
   - strictly decreasing;
   - non-increasing with characterized nullspace;
   - dissipative but only after adding time-integrated variables;
   - uniformly bounded/no abnormal growth;
   - Gronwall only;
   - impossible, with formula-level obstruction.

E. Address the relation to the old eight-variable model.
Use the verified old-model obstruction:
\[
M_x=Q_x+\mu\frac{\sigma_x}{\epsilon_0}H_x=\text{constant}
\]
on the x-edge zero-transverse mode and the resulting linear growth.  Explain
whether the repaired model removes this mode, restricts it by compatibility
conditions, or changes the PML equations.

F. Discuss Cole--Cole/fractional extension only after the alpha=1 perfect
matching and energy questions are settled.
For the fractional case, do not claim a theorem unless a positive memory
representation is explicitly written.  State whether the fractional law helps
or cannot help with any electromagnetic/PML obstruction independent of P.

Required final artifact:
Write the final report to:
results/energy_design_v3_perfect_matching_report.md

The report should be written in Chinese, with formulas in LaTeX.

Required report structure:

1. Executive summary
   - Is the v2 covariantly damped model perfectly matched?
   - Is a monotone/dissipative energy obtained?
   - What is the strongest verified conclusion?

2. Literature reading record
   - Table: reference, inspected pages/sections/formulas, relevant result,
     how it affects the present problem.

3. Perfect matching criterion
   - Planar interface setup;
   - Laplace/Fourier ansatz;
   - dispersion relation;
   - impedance/reflection coefficient criterion.

4. Perfect matching test for the v2 model
   - full algebra;
   - conclusion;
   - if not matched, exact mismatch.

5. Candidate repaired PML models
   - at least two candidates if the v2 model fails;
   - exact equations and matching/stability status.

6. Energy functional construction
   - candidate energy;
   - positivity;
   - detailed derivative calculation;
   - final identity or inequality.

7. Obstructions and impossibility statements
   - include explicit modes or algebraic blocks if monotone strict decay is
     impossible.

8. Recommendation for the next manuscript step
   - which model to pursue;
   - what theorem statement looks feasible;
   - what remains open.

Verification requirements:
- Use facts already verified by Iteris where applicable, but do not let them
  replace the new perfect-matching derivation.
- Verify any new algebraic claim needed for the final conclusion.
- If a reference PDF cannot be parsed or read, say so explicitly and mark the
  corresponding claim as unverified.
- Do not fabricate references, DOI numbers, theorem numbers, or page numbers.
EOF
)

iteris run . \
  --goal "$GOAL" \
  --target-artifact results/energy_design_v3_perfect_matching_report.md \
  --foreground \
  --new-session
