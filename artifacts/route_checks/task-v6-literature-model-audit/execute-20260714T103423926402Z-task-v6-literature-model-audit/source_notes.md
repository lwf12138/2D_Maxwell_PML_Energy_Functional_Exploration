# Source Notes

This run extracted the six mandated PDFs into `pdf_text/` with `pdfminer` after `pdfinfo` and `pdftotext` were unavailable.

PDF extraction records:

- `nonlocal_memory_energy_strict_pml.pdf`: 10 pages, 12306 characters, 1153 lines.
- `variable_coefficient_baffet_energy.pdf`: 11 pages, 13504 characters, 1380 lines.
- `Baffet ... 2019 ... Wave Equation.pdf`: 37 pages, 85788 characters, 5623 lines.
- `Joly ... 2012 ... PMLs.pdf`: 44 pages, 93995 characters, 4972 lines.
- `Becache ... 2023 ... dispersive waveg.pdf`: 41 pages, 106808 characters, 5327 lines.
- `Becache ... 2021 ... diagonal anisotropy.pdf`: 9 pages, 22761 characters, 911 lines.

Key page anchors:

- Strict stretched-coordinate model and matching: nonlocal PDF pp. 3-4.
- Baffet primitive and variable remainder: nonlocal PDF pp. 4-6; variable PDF pp. 3-7.
- Nonlocal/Gramian candidate: nonlocal PDF pp. 7-9.
- Port model mismatch: variable PDF pp. 9-10.
- Baffet 2019 constant-damping energy method: local extracted PDF pp. 4-11 and pp. 17-24.
- Joly 2012 matching/stability/truncation background: local extracted PDF pp. 7-21 and pp. 29-39.
- Becache et al. 2023 dispersive waveguide assumptions and convergence/stability caveats: local extracted PDF pp. 2456-2461 and pp. 2472-2480.
- Becache et al. 2021 backward-mode instability criterion: local extracted PDF pp. 249-253.

Firewall notes:

- `nonlocal_memory_energy_strict_pml.pdf` is a project research note, not a verified literature result.
- The elliptic nonlocal correction is a candidate until the `z_t`, `lambda_t`, and boundary terms are fully expanded.
- The port model remains excluded as strict PML because of verified oblique admittance mismatch.
- Perfect matching at the inner interface is not finite-thickness truncation exactness.
