# Jordan–Brouwer separation arc (ledger)

Goal: discharge the connectedness hypotheses `isPreconnected_interior` / `isPreconnected_exterior`
of `ClosedSurface.OutwardBoundary` (`Section6GaussOrientation.lean`) from geometric hypotheses on
the surface, and prove the Jordan–Brouwer separation theorem for closed surfaces.

Route (Lima, "The Jordan–Brouwer separation theorem for smooth hypersurfaces", 1988, for the
"at most two" half; the solid angle winding number for the "at least two" half).

| Step | Content | File | Status |
| --- | --- | --- | --- |
| JB1 | Abstract: `K` closed, connected, nonempty in a connected locally connected space, locally at most two sides ⇒ every component of `Kᶜ` has `K` in its closure; among three points of `Kᶜ` two share a component | `Section6JordanBrouwer.lean` | DONE |
| JB2 | Locally a graph (chart + continuous function) ⇒ local two-sides model | `Section6JordanBrouwer.lean` | DONE |
| JB3 | `ℝⁿ`: compact connected locally-graph `K` ⇒ at most two components, frontier of each is `K`, exactly one unbounded | `Section6JordanBrouwer.lean` | DONE |
| JB4 | Regular level sets are locally graphs (implicit function theorem) | `Section6JordanBrouwer.lean` | DONE |
| JB5 | `ℝ³` closed surfaces: exactly two components (winding number `0` / `1`) | `Section6JordanBrouwer.lean` | DONE |
| JB6 | `OutwardBoundary` from geometric hypotheses (`outwardBoundary_of_isLocallyGraph`), `dlmf_1_6_58_jordanBrouwer` | `Section6GaussSeparation.lean` | DONE |
| JB7 | Example: the sphere satisfies all hypotheses, `Sphere3.jordanBrouwer` | `Section6GaussSeparation.lean` | DONE |

Status: COMPLETE (2026-10-30).  Scope note: "at least two components" is proven for closed surfaces in `ℝ³` (solid angle); for general locally flat hypersurfaces in `ℝⁿ` only "at most two" (plus a unique unbounded component) is proven — the converse needs degree theory / homology.
