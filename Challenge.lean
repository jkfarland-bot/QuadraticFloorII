module

public import Mathlib

public section

/-!
# Quadratic floor sums II: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `QuadraticFloorII/`. The numbering follows the manuscript (Farland, *Quadratic Floor Sums, Class
Numbers, and the Trace of a Quartic Bernoulli Number*), and, for the last result, Paper III of the
author's series.

Throughout `p` is an odd prime, `𝒮_{A,B,C}(p) = floorSum A B C p`, `η_p = eta p`,
`B_{1,f}^{(q)} = bern q f`, `ϑ_{p,ψ} = vartheta p ψ`, `Θ_p = Theta p`, `𝓕(ψ₀) = fibre ψ₀` and `Q_ℓ = sqClasses ℓ`.
-/

namespace QuadraticFloorII

open Finset

/-! ### Definitions -/

section Defs

open Finset

theorem ite_of_pos {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_of_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- **The quadratic floor sum** `𝒮_{A,B,C}(p) = ∑_{n=0}^{p-1} (-1)^{⌊(A n² + B n + C)/p⌋}`.
Integer division `/` by the positive integer `p` rounds down. -/
def floorSum (A B C : ℤ) (p : ℕ) : ℤ :=
  ∑ n ∈ range p, (((A * n ^ 2 + B * n + C) / (p : ℤ)).negOnePow : ℤ)

/-- **Admissibility** (Definition 2.2): `B` is odd, `gcd(B, A) = 1`, and
`1 ≤ B² - 4AC < 4A`. -/
def Admissible (A : ℕ) (B C : ℤ) : Prop :=
  Odd B ∧ Int.gcd B A = 1 ∧ 1 ≤ B ^ 2 - 4 * A * C ∧ B ^ 2 - 4 * A * C < 4 * A

/-- `η_p = χ_{-8p}`: the Jacobi symbol `(-8p / x)` for odd `x`, and `0` for even `x`. -/
def eta (p x : ℕ) : ℤ := if Even x then 0 else jacobiSym (-8 * p) x

/-- The first Bernoulli number `B_{1,f}^{(q)} = (1/q) ∑_{x=1}^{q} x f(x)`. -/
noncomputable def bern (q : ℕ) (f : ℕ → ℂ) : ℂ :=
  (1 / (q : ℂ)) * ∑ x ∈ Icc 1 q, (x : ℂ) * f x

open Classical in
/-- `ϑ_{p,ψ} = η_p χ_{-4}^{δ_ψ} ψ`, where `ψ(-1) = (-1)^{δ_ψ}`; here `χ_{-4}^1 = χ_{-4}` and
`χ_{-4}^0 = χ_{-4}²` is the principal character modulo `4`. -/
noncomputable def vartheta {A : ℕ} (p : ℕ) (ψ : DirichletCharacter ℂ A) (x : ℕ) : ℂ :=
  (eta p x : ℂ) *
    (if ψ (-1) = -1 then (ZMod.χ₄ (x : ZMod 4) : ℂ) else (ZMod.χ₄ (x : ZMod 4) : ℂ) ^ 2) *
    ψ (x : ZMod A)

/-- The index of a nonzero residue modulo `5` to the base `2`: `2^{lg x} = x`. -/
def lg5 (x : ZMod 5) : ℕ := if x = 2 then 1 else if x = 4 then 2 else if x = 3 then 3 else 0

/-- The values of the quartic character modulo `5` with `ξ(2) = i`: `ξ(x) = i^{lg x}` for
`x ≠ 0`. -/
noncomputable def xiFun (x : ZMod 5) : ℂ := if x = 0 then 0 else Complex.I ^ lg5 x

/-- **The quartic character `ξ` modulo `5` with `ξ(2) = i`**: `ξ(1) = 1`, `ξ(2) = i`,
`ξ(4) = -1`, `ξ(3) = -i`. -/
noncomputable def xi : DirichletCharacter ℂ 5 where
  toFun := xiFun
  map_one' := by
    simp only [xiFun, show (1 : ZMod 5) ≠ 0 by decide, ite_false, show lg5 1 = 0 by decide,
      pow_zero]
  map_mul' := by
    intro a b
    by_cases ha : a = 0
    · simp [xiFun, ha]
    by_cases hb : b = 0
    · simp [xiFun, hb]
    have hab : a * b ≠ 0 := by revert a b; decide
    have hlg : lg5 (a * b) % 4 = (lg5 a + lg5 b) % 4 := by revert a b; decide
    simp only [xiFun, ha, hb, hab, ite_false, ← pow_add]
    rw [← Nat.mod_add_div (lg5 (a * b)) 4, ← Nat.mod_add_div (lg5 a + lg5 b) 4, hlg, pow_add,
      pow_add, pow_mul, pow_mul, Complex.I_pow_four, one_pow, one_pow]
  map_nonunit' := by
    intro a ha
    by_cases h0 : a = 0
    · simp [xiFun, h0]
    · exfalso
      apply ha
      obtain ⟨b, hb⟩ : ∃ b : ZMod 5, a * b = 1 := by revert a; decide
      exact IsUnit.of_mul_eq_one b hb

/-- `Θ_p = η_p χ_{-4} ξ`, the quartic character of conductor `40p`. -/
noncomputable def Theta (p x : ℕ) : ℂ :=
  (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) * xi (x : ZMod 5)

/-- `z_B = 1` if some `j` with `0 ≤ j ≤ (p-1)/2` has `p ∣ B² + 40 j`, and `0` otherwise. -/
def zB (B : ℤ) (p : ℕ) : ℤ :=
  if ∃ j ∈ range ((p + 1) / 2), (p : ℤ) ∣ B ^ 2 + 40 * j then 1 else 0

/-- The oriented sum `∑*_{j=0}^{t-1} g(j)`: `∑_{j=0}^{t-1} g(j)` for `t ≥ 0`, and
`-∑_{j=t}^{-1} g(j)` for `t < 0`. -/
def osum (t : ℤ) (g : ℤ → ℤ) : ℤ :=
  if 0 ≤ t then ∑ j ∈ Ico 0 t, g j else -∑ j ∈ Ico t 0, g j

open Classical in
/-- The fibre `𝓕(ψ₀) = {ψ : ψ² = ψ₀²}` of the squaring map on characters modulo `A`. -/
noncomputable def fibre {A : ℕ} [NeZero A] (ψ₀ : DirichletCharacter ℂ A) : Finset (DirichletCharacter ℂ A) :=
  Finset.univ.filter fun ψ => ψ ^ 2 = ψ₀ ^ 2

/-- The square classes of nonzero residues modulo `ℓ`: `Q_ℓ = {b² : b ≠ 0}` (for a prime `ℓ` the
nonzero residues are the units). -/
noncomputable def sqClasses (ℓ : ℕ) [NeZero ℓ] : Finset (ZMod ℓ) :=
  (Finset.univ.filter fun b : ZMod ℓ => b ≠ 0).image fun b => b ^ 2

end Defs

/-! ### Statements -/

section Statements

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Euler factor** (manuscript, equation (12)). For `f` of period `m` with vanishing period
sum and `f(ℓy) = f(ℓ) f(y)`: `B_{1,f·1_{ℓ∤·}}^{(mℓ)} = (1 - f(ℓ)) B_{1,f}^{(m)}`. -/
theorem euler_factor (f : ℕ → ℂ) {m ℓ : ℕ} (hℓ : 0 < ℓ) (hper : ∀ x, f (x + m) = f x)
    (hsum : ∑ x ∈ Icc 1 m, f x = 0) (hmul : ∀ y, f (ℓ * y) = f ℓ * f y) :
    bern (m * ℓ) (fun x => f x * (if ℓ ∣ x then 0 else 1)) = (1 - f ℓ) * bern m f := by
  sorry

/-- **The Euler factor for `η_p`**: `B_{1,η_p}^{(8ℓp)} = (1 - η_p(ℓ)) B_{1,η_p}^{(8p)}`, with `η_p`
induced to modulus `8ℓp` on the left. -/
theorem euler_factor_eta (hp2 : p ≠ 2) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    bern (8 * ℓ * p) (fun x => (eta p x : ℂ) * (if ℓ ∣ x then 0 else 1)) =
      (1 - (eta p ℓ : ℂ)) * bern (8 * p) (fun x => (eta p x : ℂ)) := by
  sorry

/-- **Theorem 4.2 in class-number shape.**
`𝒮_3(p) = 1 - B_{1,χ_{-24p}}/2 - (1 - (p/3)) B_{1,η_p}^{(8p)}/2`, which is `1 + h(-24p)/2 + (1 - (p/3)) h(-8p)/2`
by Dirichlet's formula (not formalized). -/
theorem floorSum_three_class (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) -
      (1 / 2) * (1 - (legendreSym 3 p : ℂ)) * bern (8 * p) (fun x => (eta p x : ℂ)) := by
  sorry

/-- **Corollary 4.3, Bernoulli form.** `-B_{1,χ_{-24p}}` (which is `h(-24p)`) is `2(𝒮_3(p) - 1)`
for `p ≡ 1 (mod 3)` and `2(𝒮_3(p) - 𝒮_1(p))` for `p ≡ 2 (mod 3)`. -/
theorem class_twentyfour (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (p % 3 = 1 → -bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) = 2 * ((floorSum 3 1 0 p : ℂ) - 1)) ∧
      (p % 3 = 2 → -bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) = 2 * ((floorSum 3 1 0 p : ℂ) - floorSum 1 1 0 p)) := by
  sorry

/-- **Corollary 4.5, equation (24), Bernoulli form.**
`-B_{1,χ_{-40p}} = 2(𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2) - (1 + (p/5))(𝒮_1(p) - 1)`; the left side is `h(-40p)`. -/
theorem class_forty (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    -bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ)) =
      2 * ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) -
        (1 + (jacobiSym p 5 : ℂ)) * ((floorSum 1 1 0 p : ℂ) - 1) := by
  sorry

/-- **Corollary 3.5 (fibre sums), summed over units.** For admissible `(B_b, C_b)` with
`B_b ≡ b (mod A)` for every unit `b`:
`∑_{b mod A} ψ₀(b)² (𝒮_{A,B_b,C_b}(p) - (-1)^{C_b}) = -∑_{ψ² = ψ₀²} B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem fibre_sum (hp2 : p ≠ 2) {A : ℕ} [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A)
    (ψ₀ : DirichletCharacter ℂ A) (Bs Cs : ZMod A → ℤ)
    (hBC : ∀ b : ZMod A, IsUnit b → Admissible A (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod A) = b) :
    ∑ b : ZMod A, ψ₀ b ^ 2 *
        ((floorSum A (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      -∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) := by
  sorry

/-- **Corollary 3.6.** If `ψ₀⁴ = 1`, the fibre sum is real: it is `∑_{ψ² = ψ₀²} Re B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem fibre_sum_real {A : ℕ} [NeZero A] (ψ₀ : DirichletCharacter ℂ A) (h4 : ψ₀ ^ 4 = 1) :
    ∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) =
      ((∑ ψ ∈ fibre ψ₀, (bern (8 * A * p) (vartheta p ψ)).re : ℝ) : ℂ) := by
  sorry

/-- A character of order `4` exists modulo every prime `ℓ ≡ 1 (mod 4)`. -/
theorem quartic_exists {ℓ : ℕ} [Fact ℓ.Prime] (h4 : ℓ % 4 = 1) :
    ∃ ξ : DirichletCharacter ℂ ℓ, orderOf ξ = 4 := by
  sorry

/-- For a quartic `ξ` modulo an odd prime `ℓ`: `ξ(a)² = (a/ℓ)`, the fibre of `ξ` under squaring is
`{ξ, ξ⁻¹}`, and the fibre of `1` is `{1, ξ²}`. -/
theorem quartic_fibres {ℓ : ℕ} [Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ} (hξ : orderOf ξ = 4) (hℓ2 : ℓ ≠ 2) :
    (∀ a : ℤ, ξ (a : ZMod ℓ) ^ 2 = (legendreSym ℓ a : ℂ)) ∧ fibre ξ = {ξ, ξ⁻¹} ∧
      fibre (1 : DirichletCharacter ℂ ℓ) = {1, ξ ^ 2} := by
  sorry

/-- **Theorem 5.1, the quartic trace.** For a prime `ℓ ≡ 1 (mod 4)`, a quartic `ξ` modulo `ℓ`, an odd
prime `p ≠ ℓ`, and admissible `(B_s, C_s)` with `B_s² ≡ s` for the square classes `s`:
`Re B_{1,Θ_{ℓ,p}}^{(8ℓp)} = -∑_s (B_s/ℓ)(𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s})`, where `Θ_{ℓ,p} = ϑ_{p,ξ}`. -/
theorem conductor_trace (hp2 : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ} (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ)
    (hξ : orderOf ξ = 4) (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s) :
    (bern (8 * ℓ * p) (vartheta p ξ)).re =
      -∑ s ∈ sqClasses ℓ, ((legendreSym ℓ (Bq s) *
        (floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℝ) := by
  sorry

/-- **Theorem 5.1, the quadratic part.**
`-B_{1,χ_{-8ℓp}} = 2 ∑_s (𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s}) - (1 - (2p/ℓ))(𝒮_1(p) - 1)`, with
`χ_{-8ℓp} = η_p (·/ℓ)`; the left side is `h(-8ℓp)` and `𝒮_1(p) - 1` is `h(-8p)` by Dirichlet's formula. -/
theorem conductor_quadratic (hp2 : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ) (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s) :
    -bern (8 * ℓ * p) (fun x => (eta p x : ℂ) * (legendreSym ℓ x : ℂ)) =
      2 * ∑ s ∈ sqClasses ℓ, (((floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℂ) -
        (1 - (legendreSym ℓ (2 * p) : ℂ)) * ((floorSum 1 1 0 p : ℂ) - 1) := by
  sorry

/-- **The case `ℓ = 13` of Theorem 5.1** (display after Theorem 5.1). -/
theorem conductor_thirteen (hp2 : p ≠ 2) (hp13 : p ≠ 13) {ξ : DirichletCharacter ℂ 13}
    (hξ : orderOf ξ = 4) :
    (bern (8 * 13 * p) (vartheta p ξ)).re =
      -((floorSum 13 1 0 p + floorSum 13 3 0 p - floorSum 13 5 0 p - floorSum 13 7 0 p +
        floorSum 13 9 1 p - floorSum 13 11 2 p + 2 : ℤ) : ℝ) := by
  sorry

/-- **The quarter-range formula.** For odd `A` and any `ψ` modulo `A`:
`B_{1,ϑ_{p,ψ}}^{(8Ap)} = -∑_{x=1}^{2Ap} ϑ_{p,ψ}(x)`. -/
theorem quarter_range (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (ψ : DirichletCharacter ℂ A) :
    bern (8 * A * p) (vartheta p ψ) = -∑ x ∈ Icc 1 (2 * A * p), vartheta p ψ x := by
  sorry

/-- **Both coordinates of `B_{1,Θ_{ℓ,p}}` are even integers**, for every prime `ℓ ≡ 1 (mod 4)`, quartic
`ξ` modulo `ℓ` and odd prime `p`. -/
theorem conductor_even (hp2 : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ} (h4 : ℓ % 4 = 1) (hξ : orderOf ξ = 4) :
    ∃ a b : ℤ, bern (8 * ℓ * p) (vartheta p ξ) = 2 * a + 2 * b * Complex.I := by
  sorry

/-- **Corollary 4.8, parity part.** Both coordinates of `B_{1,Θ_p}` (conductor `40p`) are even integers. -/
theorem quartic_trace_even (hp2 : p ≠ 2) :
    ∃ a b : ℤ, bern (40 * p) (Theta p) = 2 * a + 2 * b * Complex.I := by
  sorry

/-- **The half-range triangular sum** (Paper III, Theorem 4.4):
`2 ∑_{n=1}^{(p-1)/2} (-1)^{⌊n(n+1)/p⌋} = 𝒮_1(p) - 2 + (-2/p)`. -/
theorem half_range_triangular (hp2 : p ≠ 2) :
    2 * ∑ n ∈ Icc 1 ((p - 1) / 2), ((((n : ℤ) * (n + 1)) / p).negOnePow : ℤ) =
      floorSum 1 1 0 p - 2 + legendreSym p (-2) := by
  sorry

end Statements

end QuadraticFloorII
