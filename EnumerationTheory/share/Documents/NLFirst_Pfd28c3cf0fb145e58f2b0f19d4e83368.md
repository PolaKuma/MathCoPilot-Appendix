# Documented prior result for Chapter 2

## Peter--Weyl completeness, compact abelian case (prior retired)

Source: Lynn H. Loomis, *An Introduction to Abstract Harmonic Analysis*,
Van Nostrand, 1953, §38C, pp. 154--155 (PDF pp. 161--162).

Stable copy:
https://people.math.harvard.edu/~shlomo/212a/loomis.pdf

The source states that for a compact abelian group, with Haar measure
normalized to total mass one, the continuous circle characters form a complete
orthonormal set in `L²(G)`.  Section 38D additionally states uniform density of
finite character combinations in `C(G)`.

Lean declaration:

`MathCopilotPrior.compactAbelian_character_span_dense`

This declaration is no longer an axiom.  It is now a checked theorem proved
internally by `Chapter02.PontryaginSeparation.character_span_dense`.
The proof constructs Pontryagin point-separating characters using Haar
translations and compact convolution operators, then applies
Stone--Weierstrass and density of continuous functions in `L²`.

The current Mathlib version defines the general Pontryagin dual but has no
checked general compact-group Peter--Weyl/Pontryagin completeness theorem;
the missing argument is supplied by the project without `axiom`, `sorry`,
`admit`, or `unsafe`.

## Torus dual and the matrix root-of-unity criterion

Primary source:

Michel Waldschmidt, “Algebraic Dynamics and Transcendental Numbers”, §2,
pp. 4–5:
https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/adtn.pdf

Explicit Fourier proof:

T. Feng, *Ergodic Theory* lecture notes, Theorem 4.9, pp. 16–17:
https://math.berkeley.edu/~fengt/ergodic_theory.pdf

Lean declaration:

`MathCopilotPrior.torus_rootOfUnity_iff_periodic_nontrivial_character`

The torus dual is the integer frequency lattice.  The matrix transpose acts on
that lattice, and the cited proof identifies a finite nonzero frequency orbit
with a root-of-unity eigenvalue of the complexified integer matrix.  The Lean
declaration states exactly this dual/algebraic bridge and assumes no dynamical
property.

## Bergelson–Host–Kra multiple Khintchine recurrence

Primary source:

Vitaly Bergelson, Bernard Host, and Bryna Kra, “Multiple recurrence and
nilsequences”, *Inventiones Mathematicae* 160 (2005), 261–303, Theorem 1.2,
pp. 263–264:
https://people.math.osu.edu/bergelson.1/BHK.pdf

DOI: 10.1007/s00222-004-0428-6

Lean declaration:

`MathCopilotPrior.bergelsonHostKra_multipleKhintchine`

It records exactly the two syndeticity conclusions for three-term and
four-term multiple intersections in an ergodic probability-preserving system.
The source proof uses the Host–Kra nilfactor/nilsequence machinery, which is
not present in the current Mathlib library.
