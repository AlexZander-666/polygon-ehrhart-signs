# The signs of all Ehrhart coefficients for face lattices of polygons

For every convex polygon with $n\ge3$ sides, the order polytope of its complete face lattice has exactly $\max(n-12,0)$ negative ordinary Ehrhart coefficients. Put $D=2n+2$. For $1\le r\le D$, the coefficient of degree $r$ is negative exactly when $D-r\ge27$ and $D-r\equiv0,3\pmod4$. All other coefficients through degree $D$ are positive. The constant term is one.

The first example is the convex hull of $(j,j^2)$ for $j=0,\ldots,12$. Use every face, including the empty face and the polygon. The resulting order polytope has dimension 28 and ordinary linear Ehrhart coefficient $-298495711/35302608$. The October 2026 Open Problems Catalog calculation and Mantra Patel's manuscript documented this exact example and minimality through $n=13$. This release gives the classification for all sizes and degrees, uniform estimates, and formal proofs. [Catalog computation](https://github.com/10m-u/open-problems-catalog/blob/ca8d4d44ba3db527f19f28928c240168f545ecfe/solutions/seven-more-2026-10-09/discrete/Q3499-proof.md) · [Patel's manuscript](https://github.com/mantrakp04/research-papers/blob/c0505c4261045f1ab5760a024f1dfc4fb8f725a8/polygon_ehrhart.md)

The archived v1.0.0 release contains the paper, the Lean project and reproducibility materials. [Version DOI](https://doi.org/10.5281/zenodo.24554683) · [GitHub release](https://github.com/AlexZander-666/polygon-ehrhart-signs/releases/tag/v1.0.0)

## Mathematical question and proof

Lundström and Saud Maia Leite ask whether all ordinary Ehrhart coefficients in this family are nonnegative. The question concerns the order polytope of the **full face lattice**. A point of its $q$-th integer dilation is an order-preserving assignment of integers from 0 through $q$ to those faces. [Journal Question 6.4](https://doi.org/10.1016/j.ejc.2025.104304) · [Preprint v5 Question 6.5](https://arxiv.org/html/2504.05123v5#S6)

The proof fixes the labels of the two endpoint faces and counts the labels of the intervening crown using traces of matrix powers. Extracting coefficients along a fixed distance from the leading degree yields a sign rule with an explicit error bound. Exact rational interpolation connects the finite initial range with the analytic tail. The paper proves the estimates uniformly in the coefficient degree and includes the exceptional boundary cases. [Paper](paper/main.pdf) · [LaTeX source](paper/main.tex)

## Formalization and reproduction

The main classification starts from the unordered extreme points of an arbitrary full-dimensional convex polygon in the real plane. The Lean sources identify its full face poset, its order-polytope lattice counts, the signs and multiplicities of the negative coefficients, and the least negative degree. The explicit thirteen-gon also has a separate theorem identifying its exact rational coefficient. [Public declaration audit](formal/PublicAudit.lean) · [Explicit geometric witness](formal/Polygon/Counterexample.lean) · [Build evidence](verification/)

Use the pinned Lean toolchain and Mathlib revision in the lock. The Python checks use the standard library. The last command builds project sources in a fresh directory, verifies the external dependency revisions, audits transitive axioms and replays the project modules with the independent kernel checker.

```sh
sha256sum -c SHA256SUMS
python3 -BIu verify_finite.py
python3 -BIu verification/check-kernel.py
python3 -BIu research/next-candidates/polygon_witness.py --sides 13
python3 -Bu verify_lean.py formal PublicAudit --jobs 2
```

To rebuild the paper with TeX Live, run `bash paper/build-pdf.sh /tmp/polygon-ehrhart-signs.pdf`. The versions are Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

## Author and version

Bowen Zuo, East China University of Science and Technology. ChatGPT assisted with derivations, independent checks, certificate preparation and drafting. Version 1.0.0, 26 November 2026. Original proof sources and scripts use Apache-2.0. The manuscript has a separate copyright notice. [Citation](CITATION.cff) · [License scope](LICENSE-SCOPE.md)

## Authorship

The tagged release v1.0.0 lists Bowen Zuo as sole author. It remains unchanged and may be cited as it is. The manuscript prepared for journal submission is joint work of Bowen Zuo and Xiaojuan Luo (corresponding author), both of East China University of Science and Technology.
