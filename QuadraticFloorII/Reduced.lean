module

public import QuadraticFloorII.Euler

@[expose] public section

/-!
# The coefficients three and five in class-number shape

With the Euler factor, the Bernoulli forms of Theorems 4.2 and 4.4 take exactly the shape of the
manuscript's class-number formulas, with `-B_{1,η_p}^{(8p)}`, `-B_{1,χ_{-24p}}` and `-B_{1,χ_{-40p}}`
in place of `h(-8p)`, `h(-24p)` and `h(-40p)` (Dirichlet's formula `B_{1,χ_D} = -h(D)`, which is not
formalized). This gives Corollary 4.3 and equation (24) of Corollary 4.5.
-/

namespace QuadraticFloorII

open Finset

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma eta_odd_prime {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) :
    eta p ℓ = legendreSym ℓ (-8 * p) := by
  have hodd : ¬ Even ℓ := by
    rw [Nat.not_even_iff_odd]; exact (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  unfold eta
  rw [ite_of_neg hodd, jacobiSym.legendreSym.to_jacobiSym]

omit hp in
lemma eta_three : eta p 3 = legendreSym 3 p := by
  rw [eta_odd_prime (by norm_num), legendreSym.mod, legendreSym.mod 3 (p : ℤ)]
  congr 1
  push_cast
  omega

omit hp in
lemma eta_five : eta p 5 = -legendreSym 5 p := by
  rw [eta_odd_prime (by norm_num), show (-8 * (p : ℤ)) = (-8) * p by ring, legendreSym.mul,
    show legendreSym 5 (-8) = -1 by
      rw [legendreSym.mod, show (-8 : ℤ) % ((5 : ℕ) : ℤ) = 2 by decide,
        legendreSym.at_two (by norm_num)]
      decide]
  ring

/-- **Theorem 4.2 with the Euler factor at `3`.**
`𝒮_3(p) = 1 - B_{1,χ_{-24p}}/2 - (1 - (p/3)) B_{1,η_p}^{(8p)}/2`; by Dirichlet's formula this is
`1 + h(-24p)/2 + (1 - (p/3)) h(-8p)/2`. -/
theorem floorSum_three_euler (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) -
      (1 / 2) * (1 - (legendreSym 3 p : ℂ)) * bern (8 * p) (fun x => (eta p x : ℂ)) := by
  rw [floorSum_three' hp2 hp3, show 24 * p = 8 * 3 * p by ring, bern_eta_euler hp2 (by norm_num),
    eta_three]
  ring

/-- **Corollary 4.3, Bernoulli form.** With `S₁ = 𝒮_{1,1,0}(p)` and `S₃ = 𝒮_{3,1,0}(p)`,
`-B_{1,χ_{-24p}} = 2(S₃ - 1)` if `p ≡ 1 (mod 3)` and `2(S₃ - S₁)` if `p ≡ 2 (mod 3)`; the left side
is `h(-24p)` by Dirichlet's formula. -/
theorem recover_twentyfour (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (p % 3 = 1 → -bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) = 2 * ((floorSum 3 1 0 p : ℂ) - 1)) ∧
      (p % 3 = 2 → -bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
        (legendreSym 3 x : ℂ)) = 2 * ((floorSum 3 1 0 p : ℂ) - floorSum 1 1 0 p)) := by
  have h3 := floorSum_three_euler hp2 hp3
  have h1 := floorSum_one' hp2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hl : legendreSym 3 p = 1 := by
      rw [legendreSym.mod]
      have : (p : ℤ) % ((3 : ℕ) : ℤ) = 1 := by push_cast; omega
      rw [this]; rfl
    rw [h3, hl]; push_cast; ring
  · have hl : legendreSym 3 p = -1 := by
      rw [legendreSym.mod]
      have : (p : ℤ) % ((3 : ℕ) : ℤ) = 2 := by push_cast; omega
      rw [this]; rfl
    rw [h3, h1, hl]; push_cast; ring

/-- **Corollary 4.5, equation (24), Bernoulli form.** With `S₁ = 𝒮_{1,1,0}(p)`,
`-B_{1,χ_{-40p}} = 2(𝒮_{5,1,0}(p) + 𝒮_{5,3,0}(p) - 2) - (1 + (p/5))(S₁ - 1)`; the left side is
`h(-40p)` and `S₁ - 1` is `h(-8p)` by Dirichlet's formula. -/
theorem recover_forty (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    -bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ)) =
      2 * ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) -
        (1 + (legendreSym 5 p : ℂ)) * ((floorSum 1 1 0 p : ℂ) - 1) := by
  rw [quadratic_half' hp2 hp5, floorSum_one' hp2, show 40 * p = 8 * 5 * p by ring,
    bern_eta_euler hp2 (by norm_num), eta_five]
  push_cast
  ring

end QuadraticFloorII
