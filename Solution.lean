module

public import QuadraticFloorII

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `QuadraticFloorII/`. The definitions used in the statements come
from `QuadraticFloorII/Defs.lean` and are compared with the copies in `Challenge.lean`.
-/

namespace QuadraticFloorII

open Finset

section Statements

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Euler factor** (manuscript, equation (12)). For `f` of period `m` with vanishing period
sum and `f(ℓy) = f(ℓ) f(y)`: `B_{1,f·1_{ℓ∤·}}^{(mℓ)} = (1 - f(ℓ)) B_{1,f}^{(m)}`. -/
theorem euler_factor (f : ℕ → ℂ) {m ℓ : ℕ} (hℓ : 0 < ℓ) (hper : ∀ x, f (x + m) = f x)
    (hsum : ∑ x ∈ Icc 1 m, f x = 0) (hmul : ∀ y, f (ℓ * y) = f ℓ * f y) :
    bern (m * ℓ) (fun x => f x * (if ℓ ∣ x then 0 else 1)) = (1 - f ℓ) * bern m f :=
  bern_euler f hℓ hper hsum hmul

/-- **The Euler factor for `η_p`**: `B_{1,η_p}^{(8ℓp)} = (1 - η_p(ℓ)) B_{1,η_p}^{(8p)}`, with `η_p`
induced to modulus `8ℓp` on the left. -/
theorem euler_factor_eta (hp2 : p ≠ 2) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    bern (8 * ℓ * p) (fun x => (eta p x : ℂ) * (if ℓ ∣ x then 0 else 1)) =
      (1 - (eta p ℓ : ℂ)) * bern (8 * p) (fun x => (eta p x : ℂ)) :=
  bern_eta_euler hp2 hℓ

/-- **Theorem 4.2 in class-number shape.**
`𝒮_3(p) = 1 - B_{1,χ_{-24p}}/2 - (1 - (p/3)) B_{1,η_p}^{(8p)}/2`, which is `1 + h(-24p)/2 + (1 - (p/3)) h(-8p)/2`
by Dirichlet's formula (not formalized). -/
theorem floorSum_three_class (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) -
      (1 / 2) * (1 - (legendreSym 3 p : ℂ)) * bern (8 * p) (fun x => (eta p x : ℂ)) :=
  floorSum_three_euler hp2 hp3

/-- **Corollary 4.3, Bernoulli form.** `-B_{1,χ_{-24p}}` (which is `h(-24p)`) is `2(𝒮_3(p) - 1)`
for `p ≡ 1 (mod 3)` and `2(𝒮_3(p) - 𝒮_1(p))` for `p ≡ 2 (mod 3)`. -/
theorem class_twentyfour (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (p % 3 = 1 → -bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) = 2 * ((floorSum 3 1 0 p : ℂ) - 1)) ∧
      (p % 3 = 2 → -bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) = 2 * ((floorSum 3 1 0 p : ℂ) - floorSum 1 1 0 p)) :=
  recover_twentyfour hp2 hp3

/-- **Corollary 4.5, equation (24), Bernoulli form.**
`-B_{1,χ_{-40p}} = 2(𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2) - (1 + (p/5))(𝒮_1(p) - 1)`; the left side is `h(-40p)`. -/
theorem class_forty (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    -bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ)) =
      2 * ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) -
        (1 + (jacobiSym p 5 : ℂ)) * ((floorSum 1 1 0 p : ℂ) - 1) :=
  by have h := recover_forty hp2 hp5; rwa [jacobiSym.legendreSym.to_jacobiSym] at h

/-- **Corollary 3.5 (fibre sums), summed over units.** For admissible `(B_b, C_b)` with
`B_b ≡ b (mod A)` for every unit `b`:
`∑_{b mod A} ψ₀(b)² (𝒮_{A,B_b,C_b}(p) - (-1)^{C_b}) = -∑_{ψ² = ψ₀²} B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem fibre_sum (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A)
    (ψ₀ : DirichletCharacter ℂ A) (Bs Cs : ZMod A → ℤ)
    (hBC : ∀ b : ZMod A, IsUnit b → Admissible A (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod A) = b) :
    ∑ b : ZMod A, ψ₀ b ^ 2 *
        ((floorSum A (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      -∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) :=
  fibre_sum' hp2 hA hpA ψ₀ Bs Cs hBC

/-- **Corollary 3.6.** If `ψ₀⁴ = 1`, the fibre sum is real: it is `∑_{ψ² = ψ₀²} Re B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem fibre_sum_real {A : ℕ} [NeZero A] (ψ₀ : DirichletCharacter ℂ A) (h4 : ψ₀ ^ 4 = 1) :
    ∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) =
      ((∑ ψ ∈ fibre ψ₀, (bern (8 * A * p) (vartheta p ψ)).re : ℝ) : ℂ) :=
  fibre_sum_real' ψ₀ h4

/-- A character of order `4` exists modulo every prime `ℓ ≡ 1 (mod 4)`. -/
theorem quartic_exists {ℓ : ℕ} [Fact ℓ.Prime] (h4 : ℓ % 4 = 1) :
    ∃ ξ : DirichletCharacter ℂ ℓ, orderOf ξ = 4 :=
  exists_quartic h4

/-- For a quartic `ξ` modulo an odd prime `ℓ`: `ξ(a)² = (a/ℓ)`, the fibre of `ξ` under squaring is
`{ξ, ξ⁻¹}`, and the fibre of `1` is `{1, ξ²}`. -/
theorem quartic_fibres {ℓ : ℕ} [Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ} (hξ : orderOf ξ = 4) (hℓ2 : ℓ ≠ 2) :
    (∀ a : ℤ, ξ (a : ZMod ℓ) ^ 2 = (legendreSym ℓ a : ℂ)) ∧ fibre ξ = {ξ, ξ⁻¹} ∧
      fibre (1 : DirichletCharacter ℂ ℓ) = {1, ξ ^ 2} :=
  ⟨xi_sq_eq_legendre hξ hℓ2, fibre_xi hξ, fibre_one hξ⟩

/-- **Theorem 5.1, the quartic trace.** For a prime `ℓ ≡ 1 (mod 4)`, a quartic `ξ` modulo `ℓ`, an odd
prime `p ≠ ℓ`, and admissible `(B_s, C_s)` with `B_s² ≡ s` for the square classes `s`:
`Re B_{1,Θ_{ℓ,p}}^{(8ℓp)} = -∑_s (B_s/ℓ)(𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s})`, where `Θ_{ℓ,p} = ϑ_{p,ξ}`. -/
theorem conductor_trace (hp2 : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ} (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ)
    (hξ : orderOf ξ = 4) (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s) :
    (bern (8 * ℓ * p) (vartheta p ξ)).re =
      -∑ s ∈ sqClasses ℓ, ((legendreSym ℓ (Bq s) *
        (floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℝ) :=
  conductor_trace' hp2 h4 hpℓ hξ Bq Cq hq

/-- **Theorem 5.1, the quadratic part.**
`-B_{1,χ_{-8ℓp}} = 2 ∑_s (𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s}) - (1 - (2p/ℓ))(𝒮_1(p) - 1)`, with
`χ_{-8ℓp} = η_p (·/ℓ)`; the left side is `h(-8ℓp)` and `𝒮_1(p) - 1` is `h(-8p)` by Dirichlet's formula. -/
theorem conductor_quadratic (hp2 : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ) (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s) :
    -bern (8 * ℓ * p) (fun x => (eta p x : ℂ) * (legendreSym ℓ x : ℂ)) =
      2 * ∑ s ∈ sqClasses ℓ, (((floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℂ) -
        (1 - (legendreSym ℓ (2 * p) : ℂ)) * ((floorSum 1 1 0 p : ℂ) - 1) :=
  by
    obtain ⟨ξ, hξ⟩ := exists_quartic h4
    exact conductor_quadratic' hp2 h4 hpℓ hξ Bq Cq hq

/-- **The case `ℓ = 13` of Theorem 5.1** (display after Theorem 5.1). -/
theorem conductor_thirteen (hp2 : p ≠ 2) (hp13 : p ≠ 13) {ξ : DirichletCharacter ℂ 13}
    (hξ : orderOf ξ = 4) :
    (bern (8 * 13 * p) (vartheta p ξ)).re =
      -((floorSum 13 1 0 p + floorSum 13 3 0 p - floorSum 13 5 0 p - floorSum 13 7 0 p +
        floorSum 13 9 1 p - floorSum 13 11 2 p + 2 : ℤ) : ℝ) :=
  trace_thirteen hp2 hp13 hξ

/-- **The quarter-range formula.** For odd `A` and any `ψ` modulo `A`:
`B_{1,ϑ_{p,ψ}}^{(8Ap)} = -∑_{x=1}^{2Ap} ϑ_{p,ψ}(x)`. -/
theorem quarter_range (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (ψ : DirichletCharacter ℂ A) :
    bern (8 * A * p) (vartheta p ψ) = -∑ x ∈ Icc 1 (2 * A * p), vartheta p ψ x :=
  bern_quarter hp2 hA ψ

/-- **Both coordinates of `B_{1,Θ_{ℓ,p}}` are even integers**, for every prime `ℓ ≡ 1 (mod 4)`, quartic
`ξ` modulo `ℓ` and odd prime `p`. -/
theorem conductor_even (hp2 : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ} (h4 : ℓ % 4 = 1) (hξ : orderOf ξ = 4) :
    ∃ a b : ℤ, bern (8 * ℓ * p) (vartheta p ξ) = 2 * a + 2 * b * Complex.I :=
  bern_even hp2 h4 hξ

/-- **Corollary 4.8, parity part.** Both coordinates of `B_{1,Θ_p}` (conductor `40p`) are even integers. -/
theorem quartic_trace_even (hp2 : p ≠ 2) :
    ∃ a b : ℤ, bern (40 * p) (Theta p) = 2 * a + 2 * b * Complex.I :=
  theta_even hp2

/-- **The half-range triangular sum** (Paper III, Theorem 4.4):
`2 ∑_{n=1}^{(p-1)/2} (-1)^{⌊n(n+1)/p⌋} = 𝒮_1(p) - 2 + (-2/p)`. -/
theorem half_range_triangular (hp2 : p ≠ 2) :
    2 * ∑ n ∈ Icc 1 ((p - 1) / 2), ((((n : ℤ) * (n + 1)) / p).negOnePow : ℤ) =
      floorSum 1 1 0 p - 2 + legendreSym p (-2) :=
  half_range_one' hp2

end Statements

end QuadraticFloorII
