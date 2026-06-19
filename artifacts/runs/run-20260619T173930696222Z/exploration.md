# Iteris Bootstrap Exploration

Run: `run-20260619T173930696222Z`

Source: `sources/energy_functional_problem.tex`

## Problem Statement

\documentclass[UTF8,a4paper,12pt]{ctexart} \input{macros} \title{Problem Sheet for Iteris: Energy Functionals for 2D Maxwell--PML} \author{Prepared source problem} \date{\today} \begin{document} \maketitle \begin{abstract} This note is a self-contained source problem for an Iteris run. The system to be analyzed is the two-dimensional TM Maxwell--PML model with polarization \(P\), PML auxiliary variables \(P_{z,1},P_{z,2},Q_x,Q_y\), and perfectly conducting boundary condition. The first target is to find a genuinely monotone decreasing energy functional in two space dimensions. If such a monotone energy cannot be found, the fallback target is to find a positive energy functional that proves boundedness/no abnormal long-time growth, in the same spirit as the long-time-stability role of MPML.

## Detected Structure

- Keywords: frac, energy, item, alpha, epsilon_0, begin, qquad, terms, partial_tP, task, variables, epsilon
- Primary object: source problem recorded from the project input.
- Initial route: source and foundation audit before strong claims.

## Next Candidate Tasks

1. Freeze the exact statement, assumptions, and target artifact path.
2. Identify definitions, known results, and missing proof or implementation gates.
3. Create durable facts only for reusable claims with explicit evidence.
