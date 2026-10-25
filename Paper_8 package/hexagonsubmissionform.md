# Hexagon submission fields

Submit a replacement version of 2610.00460v1; do not create a duplicate work.
The new version identifier is assigned by Hexagon after submission and is not
asserted in advance. Existing record: https://hexagonmath.org/2610.00460v1

## Title

Two conjectures of Wormald on Hamilton cycles in tournaments

## Abstract - copy the complete block

For a regular tournament on $d$ vertices with skew adjacency matrix $S$, the Hessian determinant $H$ that Wormald attached to its random blow-ups equals $d\det(d^2I+S^2)/\det(d^2I-S^2)$. Hence $H\neq0$ and $d/H$ is the square of a rational number, as Wormald conjectured. For the cyclic tournament it gives $\sqrt{d/H}=\bigl((d+1)^d+(d-1)^d\bigr)/\bigl((d+i)^d+(d-i)^d\bigr)$, so the associated constants tend to $\cosh 1/\cos 1=2.8559578925\ldots$; this proves a second conjecture of Wormald and identifies his numerical constant.

The block uses explicit TeX commands rather than macros defined only in main.tex.

## Subjects, tags and MSC2020

Primary subject: math.CO
Cross-list subjects: math.RA, math.PR
Tags: regular tournaments, Hamilton cycles, Hessian determinants, random blow-ups, rational-square identities, spectral bounds
MSC2020 primary code: 05C20
MSC2020 additional codes: 05C45, 05C50, 05C80, 15A15
arXiv identifier: leave blank. No arXiv identifier is asserted.

## Contributors - preserve this order

Contributor 1: Deep Bhattacharjee
Affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
ORCID: 0000-0003-0466-750X

The affiliations are former affiliations, not assertions of current employment.

## Authorship and understanding selections

Text: A mix of human-written and AI-generated.
Human understanding: All parts of this contribution have been checked and understood by a human.
The user explicitly supplied both declarations specifically for Paper 8 on 25 October 2026.

## Provenance statement - copy this paragraph

Claude through Claude Code assisted the original literature search, calculations, verification programs, Lean development, figure-generation code and text. OpenAI Codex assisted this revision's proof and literature audit, explicit analytic derivatives, quantitative nondegeneracy corollary, direct spectral-radius proof, exact matrix checker and submission files. The author retains responsibility for the mathematics, references and final submission decisions. The submitting author declares that all parts have been
checked and understood by a human and takes responsibility for the content.
The unchanged Lean proof tree has a complete successful build and 23 axiom reports using only propext, Classical.choice and Quot.sound. It formalizes the determinant algebra and cyclic limit after identifying H with det(E^T F E). The analytic identification, asymptotic expansion, spectral bounds and new quantitative corollary have written proofs and are not claimed as Lean-formalized. Fresh exact checks verify 41 full Hessian matrices (3136 entries) and their bounds, and 142 manuscript values; numerical checks complement the universal proofs.

## Tools used

- Anthropic Claude / Claude Code
- OpenAI Codex
- Lean 4.34.1 / Mathlib
- Python
- C
- PARI/GP
- LaTeX / pdfLaTeX
- Shell

Use the corresponding system/tool entry if available and Other for an unlisted
tool. Do not invent a model version for an entry that is not documented.

## Formalisation links

https://github.com/creelie/Breakthrough-problems-1/tree/v1.1.0/lean
https://github.com/creelie/Breakthrough-problems-1/blob/v1.1.0/lean/Check.lean

Scope: The unchanged Lean proof tree has a complete successful build and 23 axiom reports using only propext, Classical.choice and Quot.sound. It formalizes the determinant algebra and cyclic limit after identifying H with det(E^T F E). The analytic identification, asymptotic expansion, spectral bounds and new quantitative corollary have written proofs and are not claimed as Lean-formalized. Fresh exact checks verify 41 full Hessian matrices (3136 entries) and their bounds, and 142 manuscript values; numerical checks complement the universal proofs.
If the portal rejects a host/path, leave it for manual review rather than
uploading Lean material in the article source ZIP.

## Files and licence

Required source ZIP: Two_conjectures_of_Wormald_on_Hamilton_cycles_in_tournamentstex.zip
Reference PDF: Two_conjectures_of_Wormald_on_Hamilton_cycles_in_tournaments.pdf
AI provenance upload: AI_PROVENANCE.md (outside the source ZIP).
Licence selection: CC BY 4.0, matching the existing Hexagon manuscript record.
The manuscript source ZIP contains the article, bibliography and required
figures only. It excludes Lean developments, executables, journal correspondence,
other manuscripts and private model traces. Standard TeX Live classes/packages
are build dependencies rather than relicensed files in this ZIP.

## Review before submitting

Use pdfLaTeX, main document main.tex. The extracted ZIP was rebuilt locally and
its full extracted text and page count matched the supplied PDF. Confirm the
rendered title, abstract, byline, references and final portal preview. This
packet does not press the portal's Process or Submit button on the author's behalf.


Confirmed package archive: https://doi.org/10.5281/zenodo.23631103 .
Release: https://github.com/creelie/Breakthrough-problems-1/releases/tag/v1.1.0 .
The DOI receipt was added after the archived release; see ARCHIVE-DOI.md.
