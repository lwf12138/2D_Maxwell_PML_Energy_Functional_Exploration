# V6 machine-verification outputs

All commands were run from the project root on 2026-07-14 (Asia/Shanghai).

## Toolchain

```text
$ command -v lake
/Users/wcli/.elan/bin/lake

$ cd lean_verification && lake --version
Lake version 5.0.0-src+68218e8 (Lean version 4.31.0)

$ cd lean_verification && lake env lean --version
Lean (version 4.31.0, arm64-apple-darwin24.6.0,
commit 68218e876d2a38b1985b8590fff244a83c321783, Release)
```

## SymPy

Command and exit code:

```text
$ python3 results/v6_tex/nonlocal_memory_strict_pml_sympy.py
exit code: 0
```

Complete key output:

```text
=== strict stretched-coordinate dispersion and admittance ===
x-PML dispersion reduces to physical dispersion: 0
outgoing-branch admittance Yplus-Y0: 0
reflection coefficient: 0
corner/cross-damped squared-admittance defect: -k_y**2*sigma_y*(2*s + sigma_y)/(mu**2*s**2*(s + sigma_y)**2)

=== Baffet product rule and Debye/Schur identities ===
grad(u_t+a*u) product rule: 0
Schur/completing-square identity: 0
Debye primitive product: 0
Debye Pq determinant expansion: 0

=== proposed elliptic nonlocal correction: complete proxy derivative ===
nonlocal correction derivative: 0
Baffet remainder plus proposed correction derivative: g*(-ell*lambda*u + eta*g*u*u_t - eta*lambda*u_t - eta*lambda_t*u)/ell

=== two attempted repairs ===
temporal primitive cancels target but leaves g*u_t*r: 0
second elliptic variable derivative: 0

=== local cross-term route ===
local c*u*lambda derivative: 0
residual after choosing c=-g/sigma_i to create +g*u*lambda: -g*(lambda*u_t + sigma_j*u*u_x + u*u_xt)/sigma_i

=== finite-dimensional M and Q tests ===
det(M_schur) = -(g**2 - 4*m_lambda*m_u)/4
M/Q determinant identity: 0

=== exact adversarial and random eigenvalue checks ===
adversarial high-gradient eigenvalues (g=3, mu=ml=1): [-1/2, 5/2]
random Schur case 00: min_eig=1.320551e+00, factor=0.5
random Schur case 01: min_eig=6.613999e-01, factor=0.2
random Schur case 02: min_eig=5.918963e-02, factor=0.9
random Schur case 03: min_eig=5.914804e-01, factor=0.1
random Schur case 04: min_eig=8.000000e-01, factor=0.2
random Schur case 05: min_eig=1.380698e+00, factor=0.3
random Schur case 06: min_eig=9.696194e-01, factor=0.7
random Schur case 07: min_eig=1.500000e+00, factor=0.1
random Schur case 08: min_eig=2.470435e-01, factor=0.1
random Schur case 09: min_eig=1.737652e+00, factor=0.2
random Schur case 10: min_eig=5.914804e-01, factor=0.1
random Schur case 11: min_eig=7.834475e-01, factor=0.4
baseline/control: the adversarial matrix violates Schur and has a negative eigenvalue;
falsifier: any sampled in-condition matrix with min_eig<=0, or adversarial min_eig>=0.
All v6 SymPy checks passed.
```

The random checks are smoke tests only.  The exact determinant/completing-square
identity and the exact rational adversarial eigenvalues are the certificates.

## Lean/Mathlib

Command and exit code:

```text
$ cd lean_verification
$ lake env lean ../results/v6_tex/NonlocalMemoryStrictPML.lean
exit code: 0
stdout/stderr: empty
```

The file contains no `sorry`, `admit`, or custom axioms.  It checks:

1. the v5 Schur absorption sum-of-squares identity and inequality;
2. the scalar elliptic proxy energy expansion;
3. the full proxy derivative and its exact uncancelled remainder;
4. temporal-primitive and second-elliptic-variable residual identities;
5. a sufficient `2 x 2` positive-definiteness theorem;
6. `Y_+=Y_0` implies zero reflection coefficient;
7. the local-cross-term derivative residual.

Reproducibility note: the first adversarial Iteris fact verification exposed
three Lean proof-script defects (`No goals to be solved` after two
`field_simp` calls and a disjunction mismatch in the positivity proof).  Those
defects were repaired.  The exact final-file rerun shown above then returned
`EXIT_CODE=0` with empty Lean stdout/stderr.  The rejected verification is
retained at
`verification/results/verify-20260714T105405079580Z-fact-verify-fact-2d_maxwell_pml_energy_f.json`.
