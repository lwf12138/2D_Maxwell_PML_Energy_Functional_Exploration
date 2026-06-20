# New Energy Functional 2D Debye PML Report

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Terminal artifact:

- `tex/new_energy_functional_2d_debye_pml.tex`
- `tex/new_energy_functional_2d_debye_pml.pdf`
- build log: `tex/new_energy_functional_2d_debye_pml_build.log`

## Result Summary

The TeX artifact gives a conservative Chinese report for the alpha `=1`
Maxwell-Debye case.  It separates three models:

- the original eight-variable source PML, which has a verified edge-PML linear-growth obstruction;
- the v2 covariantly damped Maxwell-Debye layer, which has a monotone energy but is not perfectly matched;
- the selected standard stretched-coordinate Maxwell-Debye PML with Baffet-type primitive variables.

The selected result is a constant-coefficient 2D Baffet-Debye energy identity:

```text
d/dt E_BD(t) = -D_BD(t) + boundary flux,  D_BD >= 0.
```

Under PEC or canceling transmission flux this gives monotonicity and integral
dissipation.  The report does not claim variable-coefficient monotonicity,
full-domain strict exponential decay, or a completed `0<alpha<1` Cole-Cole
memory theorem.

## Verification Commands

SymPy dependency setup:

```sh
python3 -m pip install sympy
```

SymPy algebra verification:

```sh
python3 verification/algebra/new_energy_functional_sympy.py
```

Result: passed.  The script checked the Debye primitive energy matrix, Schur
complement, completed-square identity, Debye cross-term cancellation, dissipation
matrix entries, v2 admittance mismatch, and stretched-coordinate admittance
matching.

Lean attempt:

```sh
lean verification/algebra/NewEnergyFunctional.lean
```

Result: failed because the local environment has no `lean` executable:

```text
zsh:1: command not found: lean
```

LaTeX compile:

```sh
xelatex -interaction=nonstopmode -halt-on-error -output-directory=tex tex/new_energy_functional_2d_debye_pml.tex
xelatex -interaction=nonstopmode -halt-on-error -output-directory=tex tex/new_energy_functional_2d_debye_pml.tex
```

Result: passed.  The final build log has no TeX errors, no undefined references,
and no overfull boxes.  It has one harmless underfull hbox warning in the abstract.

## Files Created

- `verification/algebra/new_energy_functional_sympy.py`
- `verification/algebra/NewEnergyFunctional.lean`
- `tex/new_energy_functional_2d_debye_pml.tex`
- `tex/new_energy_functional_2d_debye_pml.pdf`
- `tex/new_energy_functional_2d_debye_pml_build.log`
- `results/new_energy_functional_2d_debye_pml_report.md`
