# Verification Outputs: V5 Variable-Coefficient Baffet

Problem id: `2d_maxwell_pml_energy_functional_exploration`

## Local algebra: SymPy

Command:

```sh
python3 verification/algebra/variable_coefficient_baffet_sympy.py
```

Result: passed.

Key output:

```text
Debye primitive product identity: 0
P,q determinant identity: 0
2*a^2-b nonnegative expansion: 0
component product-rule expansion for grad(u_t+a*u): 0
absorption sum-of-squares identity: 0
port Maxwell cross terms equal div(E*W_y, -E*W_x): 0
Debye port product identity: 0
strict stretched-coordinate admittance: 0
port squared-admittance mismatch: 0
port normal-incidence matching with dispersive sigma_E: 0
oblique residual after normal-incidence sigma_E choice =
  -k_y**2*sigma/(mu**2*s**2*(s + sigma))
All variable-coefficient Baffet SymPy checks passed.
```

## Local algebra: Lean

Original Iteris command:

```sh
lean verification/algebra/VariableCoefficientBaffet.lean
```

Result in the Iteris run: failed because that run's `PATH` did not include the
local elan directory.

Output:

```text
zsh:1: command not found: lean
```

Current local check:

```sh
/Users/wcli/.elan/bin/lean verification/algebra/VariableCoefficientBaffet.lean
```

Result: Lean is installed, but Mathlib is not available from the current
directory's Lean search path.

```text
error: unknown module prefix 'Mathlib'
```

Conclusion: rerun Lean verification inside a Lake/Mathlib project or rewrite the
Lean file to avoid `import Mathlib`.

## TeX build

Commands:

```sh
xelatex -interaction=nonstopmode -halt-on-error -output-directory=tex tex/variable_coefficient_baffet_energy_analysis.tex
```

The command was rerun until references and outlines stabilized.

Result: passed. The captured build log
`tex/variable_coefficient_baffet_energy_analysis_build.log` contains no TeX
errors, undefined-reference warnings, rerun warnings, or overfull boxes. The PDF
was produced at `tex/variable_coefficient_baffet_energy_analysis.pdf`.

## Iteris verification

Fact verification passed:

- `fact:2d_maxwell_pml_energy_functional_exploration:variable-baffet-remainder-small-gradient`
  passed as `verify-20260709T035701313438Z-fact-verify-the-variable-coefficient-baf`.
  The verifier accepted the exact `R_sigma` derivation, the sign obstruction, and
  the small-gradient absorption theorem under the stated hypotheses.
- `fact:2d_maxwell_pml_energy_functional_exploration:port-layer-energy-not-pml`
  passed as `verify-20260709T040228930557Z-fact-verify-the-port-layer-energy-identi`.
  The verifier accepted the port energy identity and the oblique-mode admittance
  mismatch.

Assembly verification passed:

- `verify-20260709T040717291493Z-assembly-assemble-the-verified-v5-facts-`
  accepted `results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md`
  as a correct assembly of the verified v5 facts and artifacts.

Goal-success verification passed:

- `verify-20260709T041310547987Z-goal_success-read-.iteris-goal_prompt.tx`
  accepted the terminal artifact as satisfying the complete v5 contract.
