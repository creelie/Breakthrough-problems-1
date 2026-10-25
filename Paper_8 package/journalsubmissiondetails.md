# Journal submission details

Paper: Two conjectures of Wormald on Hamilton cycles in tournaments
Selected journal: **European Journal of Combinatorics**.
Recommended article type: original research article (editorial classification may differ).
Scope assessment: The exact tournament invariant, cyclic formulas and algebraic proof fit the journal's combinatorial and algebraic scope. The newer global Hamilton-cycle asymptotic of Divoux and Wang is explicitly credited; the manuscript does not claim that broader theorem as its contribution.

The selection is based on subject fit and the present contribution. It is not
a guarantee of editorial suitability or acceptance. The manuscript is an amsart author version. Journal production formatting can be applied if requested; an unread journal-specific guide is not asserted as satisfied.
No journal submission has been performed by preparing these files.

Official scope: https://shop.elsevier.com/journals/european-journal-of-combinatorics/0195-6698
Author guide: https://www.sciencedirect.com/journal/european-journal-of-combinatorics/publish/guide-for-authors
Submission entry point: https://www.sciencedirect.com/journal/european-journal-of-combinatorics
Requirements checked on: 25 October 2026.
Access note: The journal-specific guide returned HTTP 403 to automated retrieval. The publisher scope page and current general Elsevier AI policy were accessible. Recheck the live guide and portal before submission; no assertion is made that an unread journal-specific requirement was satisfied.

## Upload files

- Manuscript PDF: Two_conjectures_of_Wormald_on_Hamilton_cycles_in_tournaments.pdf
- Editable manuscript source: Two_conjectures_of_Wormald_on_Hamilton_cycles_in_tournamentstex.zip; main document main.tex, pdfLaTeX.
- Cover letter PDF: coverletterjournal.pdf; editable source: coverlettertex.zip.
- AI disclosure: journalaideclarationform.pdf, an author-prepared declaration,
  not an official signed publisher form; its editable TeX is included separately.
- Provenance: AI_PROVENANCE.md / aiprovinance.md (identical content).
- Verification and data: https://github.com/creelie/Breakthrough-problems-1 .

## Disclosure and scope

The manuscript proves Wormald's Conjectures 2 and 6: a determinant formula for every regular tournament gives the rational-square property, and an exact cyclic formula gives the limit cosh(1)/cos(1). This revision details the analytic Hessian identification, proves quantitative positive-definiteness and supplies a direct spectral-radius argument.

Formal-check scope: The unchanged Lean proof tree has a complete successful build and 23 axiom reports using only propext, Classical.choice and Quot.sound. It formalizes the determinant algebra and cyclic limit after identifying H with det(E^T F E). The analytic identification, asymptotic expansion, spectral bounds and new quantitative corollary have written proofs and are not claimed as Lean-formalized. Fresh exact checks verify 41 full Hessian matrices (3136 entries) and their bounds, and 142 manuscript values; numerical checks complement the universal proofs.

Existing preprint: https://hexagonmath.org/2610.00460v1
Existing manuscript/source DOI: https://doi.org/10.5281/zenodo.23567153
No arXiv identifier is supplied or invented. No journal acceptance or existing
journal publication is asserted. The new package archive DOI is recorded in
release-verification.json after Zenodo actually publishes it.

## AI disclosure

Claude through Claude Code assisted the original literature search, calculations, verification programs, Lean development, figure-generation code and text. OpenAI Codex assisted this revision's proof and literature audit, explicit analytic derivatives, quantitative nondegeneracy corollary, direct spectral-radius proof, exact matrix checker and submission files. The author retains responsibility for the mathematics, references and final submission decisions.

The author has stated that all parts are checked and understood by a human.
This is recorded as the user's declaration, not a substitute for the journal's
editorial review. The standalone disclosure is provided in addition to the
manuscript's existing AI section; it does not replace any declaration required
within the article. For Elsevier journals, the general policy asks for a
tool-and-purpose declaration in the manuscript before the references, and
separate research-method disclosure where AI is used in research.

Official general AI policy (Elsevier journals): https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals
AMS publication entry point (Paper 5): https://www.ams.org/publications

Before submission, the author confirms coauthor approval where applicable,
current correspondence details, funding/competing interests, figure rights,
and the journal's current declarations in the live portal. The cover letter
does not certify exclusivity, financial disclosures, reviewer suggestions or
signatures that the author has not supplied. Submit to one journal at a time.


Confirmed package archive: https://doi.org/10.5281/zenodo.23631103 .
Release: https://github.com/creelie/Breakthrough-problems-1/releases/tag/v1.1.0 .
The DOI receipt was added after the archived release; see ARCHIVE-DOI.md.
