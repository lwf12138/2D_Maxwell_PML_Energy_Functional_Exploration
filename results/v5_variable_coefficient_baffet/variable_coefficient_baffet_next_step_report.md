# Variable-Coefficient Baffet Next-Step Report

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Terminal artifact: `results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md`

## Original Goal Summary

The v5 goal asks whether the new PDF
`references/variable_coefficient_baffet_energy.pdf` completes the construction of
a positive monotone energy for the two-dimensional Maxwell--Debye--PML problem,
or whether it only gives a conditional variable-coefficient result or a stable
non-PML absorbing layer. It also requires a formula-level audit of the
variable-coefficient Baffet remainder, a separate port-layer matching test,
Lean/SymPy algebra files, a Chinese TeX/PDF report, and Iteris verification.

## Short Answer

The new PDF is useful but not sufficient for the final strict PML goal.

For the strict stretched-coordinate Baffet--Debye model, the variable damping
profiles create the internal term

```text
R_sigma(t) = - int u grad(a) dot lambda,   a = sigma_x + sigma_y.
```

This term has no sign, even when the damping profiles are monotone. It can be
absorbed only under an additional coercivity and small-gradient condition such as

```text
D0 >= m_u ||u||^2 + m_lambda ||lambda||^2 + nonnegative terms,
||grad a||_infty^2 < 4 m_u m_lambda.
```

The port model has a clean monotone energy for arbitrary nonnegative damping,
but its planar-interface admittance is generally mismatched for oblique modes.
It should be called a stable absorbing layer, not a strict PML.

## Fact Index

| fact id | status | verification |
|---|---:|---|
| `fact:2d_maxwell_pml_energy_functional_exploration:baffet-primitive-stretched-debye-2d-energy` | verified | `verification/results/verify-20260620T072508563237Z-fact-a-baffet-type-time-primitive-standa.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:variable-baffet-remainder-small-gradient` | verified | `verification/results/verify-20260709T035701313438Z-fact-verify-the-variable-coefficient-baf.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:port-layer-energy-not-pml` | verified | `verification/results/verify-20260709T040228930557Z-fact-verify-the-port-layer-energy-identi.json` |

## Required Judgments

1. The new PDF has not constructed an unconditional monotone energy for the
   original final target, namely the variable-coefficient strict
   stretched-coordinate Maxwell--Debye PML.
2. The strict Baffet primitive model remains the correct final PML mainline
   because it is Laplace-equivalent to stretched-coordinate PML in the constant
   coefficient interface test.
3. The variable-coefficient Baffet identity is
   `E_B' = -D0 + R_sigma + B`; under nonpositive boundary flux, monotonicity
   follows only if `R_sigma` is absorbed.
4. `sigma_i' >= 0` does not control `R_sigma`, because the sign of `lambda_i`
   is a dynamical state variable and can oppose or align with `sigma_i'`.
5. The port model reduces to Maxwell--Debye when all damping vanishes and has a
   positive energy identity, but its x-PML admittance satisfies

```text
Y_port^2 - Y_0^2
  = (epsilon sigma_E - sigma_x epsilon_D(s))/(mu (s + sigma_x))
    - sigma_x k_y^2/(mu^2 s^2 (s + sigma_x)).
```

   No scalar local `sigma_E` removes the `k_y` term for all oblique modes.

## Produced Artifacts

- `tex/variable_coefficient_baffet_energy_analysis.tex`
- `tex/variable_coefficient_baffet_energy_analysis.pdf`
- `tex/variable_coefficient_baffet_energy_analysis_build.log`
- `verification/algebra/VariableCoefficientBaffet.lean`
- `verification/algebra/variable_coefficient_baffet_sympy.py`
- `results/v5_variable_coefficient_baffet/verification_outputs.md`

## Local Verification Summary

`python3 verification/algebra/variable_coefficient_baffet_sympy.py` passed. It
checks the Debye primitive expansion, the `P,q` determinant, the `2a^2-b`
expansion, the variable-gradient product term, the small-gradient Schur
complement, the port energy cross-term cancellation, strict stretched-coordinate
matching, and the port admittance mismatch.

`lean verification/algebra/VariableCoefficientBaffet.lean` was attempted and
failed honestly because this machine has no `lean` executable:

```text
zsh:1: command not found: lean
```

The TeX artifact compiled successfully to PDF. The final captured build log has
no TeX errors, undefined-reference warnings, rerun warnings, or overfull boxes.

## Assembly

The previously verified constant-coefficient Baffet fact establishes the strict
stretched-coordinate/Baffet primitive model as the matched constant-coefficient
baseline. The new variable-coefficient audit adds two conclusions:

First, the same Baffet energy acquires the exact remainder
`R_sigma = - int u grad(a) dot lambda`. This blocks unconditional monotonicity
and gives a precise theorem only under small-gradient absorption.

Second, the port model is a separate passive absorbing layer. Its energy identity
is valid, but the admittance computation gives nonzero reflection for oblique
modes, so it cannot be used as the final strict PML theorem.

Therefore the next manuscript theorem should state variable-coefficient
monotonicity only under explicit small-gradient/coercivity assumptions. If the
port model is used in numerics, it should be advertised as a stable absorbing
layer rather than a perfectly matched layer. The report does not relabel a
Gronwall bound as monotone decay.
