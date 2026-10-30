# QuadraticFloorII

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23794942.svg)](https://doi.org/10.5281/zenodo.23794942)

Software archive: version v1.0 is [doi:10.5281/zenodo.23794943](https://doi.org/10.5281/zenodo.23794943);
all versions are [doi:10.5281/zenodo.23794942](https://doi.org/10.5281/zenodo.23794942).

Lean 4 / Mathlib formalization of the remaining floor-sum results of J. S. Farland, *Quadratic Floor
Sums, Class Numbers, and the Trace of a Quartic Bernoulli Number* (manuscript, 2026), and of one
formula of Paper III of the author's series. It is the sequel of
[QuadraticFloor](https://github.com/jkfarland-bot/QuadraticFloor) (software
[doi:10.5281/zenodo.23726773](https://doi.org/10.5281/zenodo.23726773); companion paper
[doi:10.5281/zenodo.23752229](https://doi.org/10.5281/zenodo.23752229)), whose files are copied here and
renamed into the namespace `QuadraticFloorII`.

The companion paper is J. S. Farland, *Quadratic floor sums II: fibre sums and quartic traces at
conductor 8ℓp, formalized in Lean* (preprint, Zenodo, 2026; v1.0
[doi:10.5281/zenodo.23797606](https://doi.org/10.5281/zenodo.23797606), all versions
[doi:10.5281/zenodo.23797605](https://doi.org/10.5281/zenodo.23797605)).

For an odd prime `p`, put `𝒮_{A,B,C}(p) = ∑_{n<p} (-1)^⌊(An² + Bn + C)/p⌋`, `η_p = χ_{-8p}`,
`ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ` for a character `ψ` modulo `A`, and `B_{1,f}^{(q)} = (1/q) ∑_{x≤q} x f(x)`.
A pair `(B, C)` is admissible for odd `A` if `B` is odd, prime to `A`, and `1 ≤ B² - 4AC < 4A`.
This repository proves:

- **Fibre sums** (Corollary 3.5). For a character `ψ₀` modulo an odd `A` and admissible lifts
  `(B_b, C_b)` of the units `b`:
  `∑_b ψ₀(b)² (𝒮_{A,B_b,C_b}(p) - (-1)^{C_b}) = -∑_{ψ² = ψ₀²} B_{1,ϑ_{p,ψ}}^{(8Ap)}`; if `ψ₀⁴ = 1` the
  fibre sum is real (Corollary 3.6).
- **Quartic traces at conductor `8ℓp`** (Theorem 5.1). For a prime `ℓ ≡ 1 (mod 4)`, a quartic `ξ` modulo
  `ℓ`, `Θ_{ℓ,p} = ϑ_{p,ξ}` and admissible `(B_s, C_s)` with `B_s² ≡ s` for the square classes `s`:
  `Re B_{1,Θ_{ℓ,p}} = -∑_s (B_s/ℓ)(𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s})` and
  `-B_{1,η_p(·/ℓ)} = 2 ∑_s (𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s}) - (1 - (2p/ℓ))(𝒮_{1,1,0}(p) - 1)`; the case
  `ℓ = 13` displayed in the manuscript; and the facts used about quartic characters (`ξ² = (·/ℓ)`, the
  fibres `{ξ, ξ⁻¹}` and `{1, ξ²}`, existence).
- **The Euler factor** (equation (12)): `B_{1,f·1_{ℓ∤·}}^{(mℓ)} = (1 - f(ℓ)) B_{1,f}^{(m)}`, and the resulting
  class-number shapes of Theorem 4.2, Corollary 4.3 and equation (24) of Corollary 4.5.
- **The quarter-range formula** `B_{1,ϑ_{p,ψ}}^{(8Ap)} = -∑_{0<x≤2Ap} ϑ_{p,ψ}(x)`, and an elementary proof that
  both coordinates of `B_{1,Θ_{ℓ,p}}` are even integers (for `ℓ = 5`, the parity part of Corollary 4.8).
- **The half-range triangular sum** (Paper III, Theorem 4.4):
  `2 ∑_{n=1}^{(p-1)/2} (-1)^⌊n(n+1)/p⌋ = 𝒮_{1,1,0}(p) - 2 + (-2/p)`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. The export of `Solution` is accepted by the Lean kernel, nanoda and con-ron.

## Scope, hypotheses and limitations

- **No class numbers.** As in QuadraticFloor, every statement is in Bernoulli form; Dirichlet's formula
  `B_{1,χ_D} = -h(D)` is quoted, not proved. `χ_{-8ℓp}` is the function `η_p (·/ℓ)`, `χ_{-24p}` is
  `η_p χ_{-4} (·/3)` and `χ_{-40p}` is `η_p (·/5)`.
- **Fibre sums over units.** Corollary 3.5 is stated summed over all residues `b` (the weight vanishes off
  the units) with admissible lifts `B_b ≡ b`, rather than over square-class representatives with the factor
  `2^{-ω(A)}`; the two differ by the number of square roots of each class. For prime `ℓ` the representative
  form is proved inside Theorem 5.1.
- **Quartic characters.** `ξ` is any `DirichletCharacter ℂ ℓ` with `orderOf ξ = 4`, and `Θ_{ℓ,p}` is
  `vartheta p ξ`, which carries `χ_{-4}` exactly when `ℓ ≡ 5 (mod 8)`. The primitivity, order and conductor
  `8ℓp` of `Θ_{ℓ,p}` are not formalized. `Q_ℓ` is `sqClasses ℓ`, the squares of nonzero residues.
- **Strengthenings.** The Euler factor holds for every function of period `m` with vanishing period sum
  and every `ℓ ≥ 1`; Corollary 3.6 needs only `ψ₀⁴ = 1`; the quarter-range formula holds for every
  character modulo every odd `A`; the evenness of both coordinates holds without `p ≠ ℓ` (so
  `quartic_trace_even` includes `p = 5`). `conductor_quadratic` has no character among its hypotheses; its
  proof chooses a quartic character.
- Not formalized from Corollaries 3.5 and 3.6: the converse (the fibre sums determine the individual floor
  sums) and the remark that the fibre contains no real character.
- **Not formalized:** the quartic field `K_p`, `h(K_p) = |B_{1,Θ_p}|²/2` and the formula for `|Im B_{1,Θ_p}|`
  (Proposition 4.7, Corollary 4.8 apart from parity); the non-elimination results of Section 6 (class numbers
  near `1.3 × 10⁷` and large determinants); the sextic cases of Remark 5.2.

## Sources and novelty

Corollary 3.5 is one step from the square-class decomposition and character orthogonality; the fibre
formulation itself was not found stated. The Euler factor is classical (Washington, *Introduction to
Cyclotomic Fields*). Class number formulas for imaginary cyclic quartic fields through short character sums
and coset counts are classical (Hudson, Pacific J. Math. 115 (1984); Hardy, Hudson, Richman, Williams and
Holtz, Math. Comp. 49 (1987); K. S. Williams, RIMS Kôkyûroku 603 (1987)), and the second identity of
Theorem 5.1 is of the classical Dirichlet type (Hudson and Williams, Math. Comp. 39 (1982)). What the
manuscript claims, and what was found in none of the sources searched, is the first identity of Theorem 5.1:
the real part of a quartic Bernoulli number of conductor `8ℓp` as a signed combination of floor sums. The
quarter-range formula is a classical manipulation (Berndt, Enseign. Math. 22 (1976)). The evenness of both
coordinates of `B_{1,Θ_{ℓ,p}}` is weaker than what genus theory gives (the field has three ramified primes,
so `4 ∣ h`); what is new here is only the elementary route, which replaces the class number formula for
`K_p` used in the manuscript. The half-range triangular sum follows from `𝒮_{1,1,0}(p) = 1 + h(-8p)` by the
symmetry `n ↦ p - 1 - n`; it was not found in Sun (2019), Petrov and Sun (2020) or Chamberland and Dilcher
(arXiv:2510.04387). Novelty is claimed only relative to these sources.

## Authorship, AI assistance and licence

The mathematics, the statements and the manuscripts are by Joseph S. Farland. The Lean code was drafted
and repaired by Claude (Anthropic) against the manuscripts' statements and proofs. The code is released
under the Apache License 2.0 (`LICENSE`); the papers are CC BY 4.0.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface to audit. It restates the definitions exactly as the
  development has them and states the 16 results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `QuadraticFloorII/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the Palomar starter template.
- `check/statements.py` recomputes every formalized statement numerically.

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Manuscript | Challenge declaration |
|---|---|
| Equation (12), the Euler factor | `euler_factor`, `euler_factor_eta` |
| Theorem 4.2, Corollary 4.3, Corollary 4.5 (24) | `floorSum_three_class`, `class_twentyfour`, `class_forty` |
| Corollary 3.5 | `fibre_sum` |
| Corollary 3.6 | `fibre_sum_real` |
| proof of Theorem 5.1 | `quartic_fibres`, `quartic_exists` |
| Theorem 5.1 | `conductor_trace`, `conductor_quadratic` |
| display after Theorem 5.1 (`ℓ = 13`) | `conductor_thirteen` |
| quarter-range formula | `quarter_range` |
| Corollary 4.8 (parity) | `conductor_even`, `quartic_trace_even` |
| Paper III, Theorem 4.4 | `half_range_triangular` |

## Files

| File | Contents |
|---|---|
| `Defs`, `RootCount`, `Eta`, `HalfPeriod`, `SquareClass`, `Corollaries`, `CoefficientFive` | copied from QuadraticFloor v1.0; `Defs` adds `fibre` and `sqClasses` |
| `Euler` | the Euler factor |
| `Reduced` | the coefficients three and five in class-number shape |
| `Fibre` | Corollaries 3.5 and 3.6 |
| `Quartic` | quartic characters modulo a prime `ℓ ≡ 1 (mod 4)` |
| `Conductor` | Theorem 5.1 |
| `Parity` | the quarter-range formula and the parity of both coordinates |
| `Examples` | `ℓ = 5` and `ℓ = 13` |
| `HalfRange` | Paper III, Theorem 4.4 |
