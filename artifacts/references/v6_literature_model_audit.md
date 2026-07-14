# V6 Literature And Model Audit

Task: `task-v6-literature-model-audit`

Run: `execute-20260714T103423926402Z-task-v6-literature-model-audit`

Mode: foundation. This artifact freezes source scope, notation, model assumptions, and audit obligations for the next proof tasks. It does not claim a new monotone-energy proof.

## Reading Ledger

All thirteen mandated materials in `.iteris/goal_prompt.txt` were read or text-extracted in full. The six PDFs were extracted with `pdfminer` into the run workspace because Poppler commands were not installed in the shell.

| # | material | read evidence | pages/lines | use in v6 |
|---:|---|---:|---:|---|
| 1 | `references/nonlocal_memory_energy_strict_pml.pdf` | `pdf_text/nonlocal_memory_energy_strict_pml.txt` | 10 PDF pages, 1153 lines | Candidate nonlocal/Gramian route; strict PML matching derivation; claim firewall. |
| 2 | `references/variable_coefficient_baffet_energy.pdf` | `pdf_text/variable_coefficient_baffet_energy.txt` | 11 PDF pages, 1380 lines | Baffet variable-coefficient identity, boundary terms, assumptions, port-layer mismatch. |
| 3 | `results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md` | direct full read | 129 lines | Verified v5 scope and fact ledger. |
| 4 | `results/v5-tex/variable_coefficient_baffet_energy_analysis.tex` | direct full read | 508 lines | Formula source for `E_B`, `D0`, `R_sigma`, port model, and small-gradient Schur condition. |
| 5 | `references/Baffet ... 2019 ... Wave Equation.pdf` | `pdf_text/baffet_2019.txt` | 37 PDF pages, 5623 lines | Baffet primitive energy method and constant-damping auxiliary-variable structure. |
| 6 | `references/Joly - 2012 ... PMLs ...pdf` | `pdf_text/joly_2012.txt` | 44 PDF pages, 4972 lines | Stretched-coordinate/impedance matching, boundary truncation distinction, stability caveats. |
| 7 | `references/Becache ... 2023 ... dispersive waveg.pdf` | `pdf_text/becache_2023.txt` | 41 PDF pages, 5327 lines | Dispersive time-domain PML convergence, assumptions, waveguide instability warnings. |
| 8 | `references/Becache ... 2021 ... diagonal anisotropy.pdf` | `pdf_text/becache_2021.txt` | 9 PDF pages, 911 lines | Backward-mode instability criterion and multi-axial/cross-damping caution. |
| 9 | `sources/energy_functional_problem.tex` | direct full read | 330 lines | Original source problem, PEC condition, alpha=1 Debye reduction, auxiliary-variable notation. |
| 10 | `sources/energy_ansatz_notes.tex` | direct full read | 112 lines | Non-proof brainstorming; finite-dimensional Lyapunov and memory directions. |
| 11 | `verification/algebra/VariableCoefficientBaffet.lean` | direct full read | 98 lines | Existing Lean algebra: Debye primitive product, determinant, product rule, Schur absorption. |
| 12 | `verification/algebra/variable_coefficient_baffet_sympy.py` | direct full read | 134 lines | Existing SymPy checks: strict matching, port mismatch, Baffet remainder source. |
| 13 | `lean_verification/PMLVerification/VariableCoefficientBaffet.lean` | direct full read | 98 lines | Lake/Mathlib mirror of v5 Lean algebra targets. |

## Bibliographic Trace

Local bibliographic metadata was checked against `references/references.bib` and the local PDF title pages. DOI/source fields for formal literature:

| source | formal citation | DOI or source |
|---|---|---|
| Baffet 2019 | Daniel H. Baffet, Marcus J. Grote, Sebastien Imperiale, Maryna Kachanovska, "Energy decay and stability of a perfectly matched layer for the wave equation", Journal of Scientific Computing 81(3), 2237-2270 (2019). | `10.1007/s10915-019-01089-9`; local BibTeX also lists `https://doi.org/10.1007/s10915-019-01089-9`. |
| Joly 2012 | Patrick Joly, "An elementary introduction to the construction and the analysis of perfectly matched layers for time domain wave propagation", SeMA Journal 57, 5-48 (2012). | `10.1007/BF03322599` from Springer page. |
| Becache-Kachanovska-Wess 2023 | Eliane Becache, Maryna Kachanovska, Markus Wess, "Convergence analysis of time-domain PMLs for 2D electromagnetic wave propagation in dispersive waveguides", ESAIM: M2AN 57(4), 2451-2491 (2023). | `10.1051/m2an/2023060`; local PDF title page and BibTeX agree. |
| Becache-Fliss-Kachanovska-Kazakova 2021 | Eliane Becache, Sonia Fliss, Maryna Kachanovska, Maria Kazakova, "On a surprising instability result of Perfectly Matched Layers for Maxwell's equations in 3D media with diagonal anisotropy", Comptes Rendus Mathematique 359(3), 249-256 (2021). | `10.5802/crmath.165`; local PDF title page and BibTeX agree. |

The local PDFs `nonlocal_memory_energy_strict_pml.pdf` and `variable_coefficient_baffet_energy.pdf` are project research notes, not peer-reviewed external literature. Their claims must be rederived before fact promotion.

## Source-To-Use Traceability

| source | page/formula anchor | formula or conclusion | v6 use |
|---|---|---|---|
| nonlocal PDF | pp. 3, eqs. (9)-(15) | Strict stretched-coordinate PML uses `S_i=1+sigma_i/s`, `partial_i -> S_i^{-1} partial_i`, Debye law unchanged; planar x-interface yields `Y_+=Y_0`, hence `R=0`. | Freeze strict model and matching test. |
| nonlocal PDF | p. 4, eqs. (16)-(17) | If an x-PML also changes tangential stretch `S_y`, then oblique admittance generally changes. | Firewall for multi-axial/cross damping. |
| nonlocal PDF | pp. 4-6, eqs. (24)-(28), (33)-(40) | Baffet primitive has `W=u_t+a u`; variable coefficients produce `R_sigma=-int u grad(a).lambda`; ratio kernels may change sign. | Do not treat temporal memory alone as sufficient. |
| nonlocal PDF | pp. 7-8, eqs. (42)-(50) | Elliptic/Gramian nonlocal corrections are candidates; they require domain, invertibility, Schur positivity, and time-derivative control. | Next proof task must expand derivatives and test positivity. |
| variable PDF | pp. 3-4, eqs. (5)-(14) | Primitive variables `u_t=E`, `q_t=P`, `q+tau P=kappa u`, `lambda=grad u+phi`, `phi_t+Gamma_1 phi=Gamma_2 grad u`. | Canonical time-domain strict PML realization. |
| variable PDF | pp. 4-5 | `sigma_x in W^{1,infty}(I_x)`, `sigma_y in W^{1,infty}(I_y)`, nonnegative; continuity/interface terms are required for monotonicity. | Boundary and coefficient assumptions. |
| variable PDF | pp. 5-7 | `E_B'=-D0+R_sigma+B`, with `R_sigma=-int u grad(a).lambda`; `R_sigma` has no fixed sign. | Recheck and reuse as verified v5 baseline. |
| variable PDF | pp. 7-8 | Small-gradient Schur condition can absorb `R_sigma`; otherwise only Gronwall-type bound. | Distinguish Level B from Level A. |
| variable PDF | pp. 9-10 | Port model has monotone energy but x-interface admittance mismatch for oblique `k_y`. | Port layer excluded as strict PML terminal model. |
| Baffet 2019 | pp. 4-11, Sec. 2 | For constant damping, the wave-equation PML energy uses shifted `partial_t u+a u`, flux `grad u+phi`, and auxiliary compatibility. | Methodological source for Baffet primitive, not a Maxwell-Debye theorem by itself. |
| Baffet 2019 | pp. 17-24, Sec. 3 | Discrete/continuous stability proofs rely on auxiliary lemmas and constant damping. | Do not extrapolate to arbitrary variable coefficients without rederivation. |
| Joly 2012 | pp. 7-21 | PML construction by impedance adaptation and complex coordinate/stretching; reflectionless interface is separate from finite truncation error. | Perfect matching calculation and external-boundary caveat. |
| Joly 2012 | pp. 29-39 | Stability/well-posedness can fail depending on hyperbolicity and perturbation structure. | Energy existence is not implied by matching alone. |
| Becache et al. 2023 | pp. 2456-2461 | Time-domain dispersive PML well-posedness/convergence under admissibility, boundary, and constitutive assumptions. | Supports use of Laplace-domain dispersive assumptions, but not the v6 energy identity. |
| Becache et al. 2023 | pp. 2472-2480 | PMLs can be unstable with localized heterogeneities; convergence is conditional on stability. | Do not use a Gramian without independent stability. |
| Becache et al. 2021 | pp. 249-253, Thm. 1 | Backward modes in 3D diagonal anisotropy imply PML instability; 2D Maxwell/scalar cases are different. | Warning for multi-axial/cross damping and backward-mode routes. |
| source TeX | Secs. 2-4 | Original alpha=1 Maxwell-PML model and PEC `E=0` boundary; natural energy defects. | Project source context; v6 strict model intentionally replaces older nonmatched source equations. |
| ansatz TeX | all | Brainstorming only; finite-dimensional Lyapunov and memory suggestions are not proofs. | Route checklist only. |
| Lean/SymPy files | all | Algebra checks for Debye primitive product, `R_sigma` product rule, Schur absorption, port mismatch. | Reuse as predecessor algebra; extend in v6 machine task. |

## Frozen Notation And Strict Model

Use the physical Maxwell-Debye system

```text
epsilon E_t + P_t = partial_x H_y - partial_y H_x,
mu H_{x,t} = -partial_y E,
mu H_{y,t} =  partial_x E,
tau P_t + P = kappa E,
epsilon, mu, tau, kappa > 0.
```

In the Laplace domain, with `Re s>0`,

```text
epsilon_D(s) = epsilon + kappa/(1+tau s),
S_i(s,x_i) = 1 + sigma_i(x_i)/s.
```

The strict stretched-coordinate Maxwell-Debye PML is

```text
s epsilon_D(s) Ehat = S_x^{-1} partial_x Hhat_y - S_y^{-1} partial_y Hhat_x,
mu s Hhat_x = - S_y^{-1} partial_y Ehat,
mu s Hhat_y =   S_x^{-1} partial_x Ehat,
(1+tau s) Phat = kappa Ehat.
```

This is the only model that can be called strict PML in v6 unless a replacement passes the same admittance test. Damping the Debye law as `(1+tau(s+sigma))P=kappa E`, adding scalar `sigma_E E`, or adding tangential stretch in an x-interface changes the model and must be retested.

## Time-Domain Primitive Realization

For energy work use the Baffet primitive variables on the PML subdomain:

```text
u_t = E,
q_t = P,
q + tau P = kappa u,
a = sigma_x + sigma_y,
b = sigma_x sigma_y,
Gamma_1 = diag(sigma_x, sigma_y),
Gamma_2 = diag(sigma_y-sigma_x, sigma_x-sigma_y),
lambda = grad u + phi,
phi_t + Gamma_1 phi = Gamma_2 grad u.
```

The primitive field equation is

```text
mu { epsilon (u_tt + a u_t + b u) + P_t + a P + b q } - div lambda = 0.
```

For constant coefficients this is Laplace-equivalent to the strict stretched-coordinate second-order scalar Maxwell-Debye equation because

```text
lambda_x = (S_y/S_x) partial_x u,
lambda_y = (S_x/S_y) partial_y u,
P = kappa s u/(1+tau s),
q = P/s.
```

Magnetic reconstruction, when needed, is

```text
H_y = (1/mu) S_x^{-1} partial_x u = lambda_x/(mu S_y),
H_x = -(1/mu) S_y^{-1} partial_y u = -lambda_y/(mu S_x)
```

in Laplace variables, with the corresponding ADE relation interpreted using zero or compatible initial histories.

## Initial, Boundary, Interface, And Coefficient Assumptions

Minimum assumptions for the v6 proof route:

1. `sigma_x=sigma_x(x)`, `sigma_y=sigma_y(y)`, `sigma_i >= 0`, time independent, at least `W^{1,infty}` on layer subintervals; smoother if integration by parts or elliptic traces require it.
2. `sigma_i=0` in the physical region. At physical/PML interfaces the trace should vanish or be handled as an explicit interface flux/distribution term. A jump in `sigma_i` creates extra interface terms and cannot be ignored.
3. On the inner physical/PML interface, impose physical continuity of tangential fields (`E`, tangential `H`) or the equivalent primitive continuity of `u` and normal flux consistent with the strict Laplace model.
4. On the outer truncation boundary, impose PEC or another condition giving nonpositive boundary flux. This is not the same as perfect matching at the inner interface.
5. Primitive compatibility: `u_t(0)=E(0)`, `q_t(0)=P(0)`, `q(0)+tau P(0)=kappa u(0)`, and ADE histories such as `phi(0)` chosen to match the Laplace-domain zero-history realization unless explicitly studying spurious initial layers.
6. When `a=0`, quantities such as `a^{-1} Gamma_1` and `b/a` must be interpreted by continuous extension or by splitting physical and PML subdomains. The Baffet primitive energy does not by itself control all gauge directions in the physical region.

## Perfect-Matching Calculation For An x-Interface

Take a flat interface `x=0`, physical side `x<0`, x-PML side `x>0`, `S_y=1`, `S_x=1+sigma_x(x)/s`, and `Re s>0`. Let tangential Fourier number be `k_y`. The physical dispersion is

```text
nu_0^2 = k_y^2 + mu s^2 epsilon_D(s),
Y_0 = H_y/E = nu_0/(mu s),
```

with the outgoing square-root branch fixed by continuity from the physical side and decay/radiation orientation.

In the PML, choose the transmitted phase with stretched coordinate

```text
E_+(x,y,s) = T exp(i k_y y + nu_0 int_0^x S_x(s,xi) dxi).
```

Then

```text
S_x^{-1} partial_x E_+ = nu_0 E_+,
H_{y,+}/E_+ = (S_x^{-1} partial_x E_+)/(mu s E_+) = nu_0/(mu s) = Y_0.
```

With interface conditions

```text
1+R = T,
Y_0(1-R) = Y_+ T,
```

the reflection coefficient is

```text
R = (Y_0 - Y_+)/(Y_0 + Y_+) = 0.
```

This argument covers arbitrary normal variable `sigma_x(x)` because only the integral stretched phase and the interface admittance are used. It does not prove that a finite outer boundary is reflectionless; the outer boundary creates truncation error unless another exact boundary condition is imposed.

Corner and multi-axial caution: if an x-interface model also changes tangential stretch (`S_y != 1`) then

```text
Y_+^2 = (mu s^2 epsilon_D(s) + k_y^2/S_y^2)/(mu^2 s^2),
Y_0^2 = (mu s^2 epsilon_D(s) + k_y^2)/(mu^2 s^2),
```

so oblique modes are generally mismatched. Cross or multi-axial damping must be retested before being called PML.

## Baffet Remainder Baseline

For

```text
W = u_t + a u,
grad W = grad u_t + a grad u + u grad a,
```

the v5 identity is

```text
dE_B/dt = -D0 + R_sigma + B,
R_sigma = - int_{Omega_+} u grad(a).lambda dxdy,
B = int_{partial Omega_+} (u_t+a u) lambda.n ds.
```

`D0` contains the nonnegative terms

```text
lambda^T Gamma_1(I+a^{-1}Gamma_1)lambda,
(b/a)|grad u|^2,
mu epsilon a b u^2,
(mu/kappa)[tau P_t^2 + tau(a^2-b)P^2 + a b q^2].
```

The sign firewall is strict: `R_sigma` has no fixed sign. Monotone damping profiles do not control the sign of the state variable `lambda`. Small-gradient absorption gives a conditional theorem only when `D0` coercively controls `u` and `lambda` and `||grad a||_infty^2 < 4 m_u m_lambda` (or the corresponding matrix Schur condition). Otherwise the available estimate is Gronwall-type at best.

## Nonlocal Candidate Firewall

The new nonlocal proposal should be treated as a candidate calculation:

```text
L v = -div(C_lambda grad v) + c_u v,
z = L^{-1} div(u grad a),
E_nl = E_B + eta (lambda, grad z)
       + eta/2 [(C_lambda grad z, grad z) + (c_u z,z)].
```

Before any proof claim, the next task must fix:

1. domain `Omega_+`, boundary conditions for `z`, and whether constants belong to the kernel;
2. scalar or matrix status of `C_lambda`, with uniform ellipticity;
3. weak form sign:

```text
(C_lambda grad z, grad v) + (c_u z,v)
  = -(u grad a, grad v) + boundary terms
```

under the displayed definition of `L z = div(u grad a)`;
4. time derivative:

```text
z_t = L^{-1} div(u_t grad a),
d/dt (lambda, grad z) = (lambda_t, grad z) + (lambda, grad z_t),
d/dt 1/2 (Lz,z) = (Lz,z_t).
```

These terms do not automatically cancel `R_sigma`; they introduce `u_t`, `lambda_t`, and boundary contributions. A static Schur complement is necessary for positivity but insufficient for monotonicity.

## Candidate Facts For Later Verification

No durable facts were added by this foundation task. Candidate claims worth later proof/verification:

1. Under the stated strict x-interface assumptions, the stretched-coordinate Maxwell-Debye PML has `R(s,k_y)=0` for all `Re s>0` and all real `k_y`.
2. The Baffet primitive system above is Laplace-equivalent to the strict stretched-coordinate model for constant or frozen coefficients with compatible zero histories.
3. The displayed nonlocal energy candidate does not yield a closed monotone identity until its `z_t`, `lambda_t`, and boundary terms are controlled or canceled.

## Frontier Suggestion

The next proof task should start from this frozen model and perform the requested route audit:

1. Re-derive the Baffet remainder from the primitive system in full detail.
2. Expand the nonlocal correction derivative and decide whether it cancels `R_sigma` or leaves a precise residual.
3. Compare local cross terms, elliptic nonlocal corrections, and Gramian/memory routes using finite-dimensional necessary tests before any PDE-level theorem claim.
