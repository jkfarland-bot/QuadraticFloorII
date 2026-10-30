module

public import QuadraticFloorII.Parity

@[expose] public section

/-!
# The cases `ℓ = 5` and `ℓ = 13`

* `xi` has order `4`, so at `ℓ = 5` the parity theorem says that both coordinates of
  `B_{1,Θ_p}` are even integers (Corollary 4.8, parity part).
* At `ℓ = 13` the square classes `1, 9, 12, 10, 3, 4` have the admissible representatives
  `(1,0), (3,0), (5,0), (7,0), (9,1), (11,2)`, and Theorem 5.1 reads
  `Re B_{1,Θ_{13,p}} = -(𝒮_{13,1,0} + 𝒮_{13,3,0} - 𝒮_{13,5,0} - 𝒮_{13,7,0} + 𝒮_{13,9,1} - 𝒮_{13,11,2} + 2)`.
-/

namespace QuadraticFloorII

open Finset Complex

variable {p : ℕ} [hp : Fact p.Prime]

lemma xi_pow_four_eq : xi ^ 4 = 1 := by
  apply char5_ext
  rw [MulChar.pow_apply' _ (by norm_num), xi_two, Complex.I_pow_four,
    MulChar.one_apply (IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide))]

lemma orderOf_xi : orderOf xi = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := xi) ?_ ?_
  · rw [h]; norm_num
  · intro h2
    have := DFunLike.congr_fun h2 2
    rw [MulChar.pow_apply' _ (by norm_num), xi_two, pow_one, Complex.I_sq,
      MulChar.one_apply (IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide))] at this
    norm_num at this
  · simpa using xi_pow_four_eq

/-- **Corollary 4.8, parity part.** Both coordinates of `B_{1,Θ_p}` are even integers. -/
theorem theta_even (hp2 : p ≠ 2) :
    ∃ a b : ℤ, bern (40 * p) (Theta p) = 2 * a + 2 * b * I := by
  obtain ⟨a, b, h⟩ := bern_even (ℓ := 5) hp2 (by norm_num) orderOf_xi
  refine ⟨a, b, ?_⟩
  rw [← vartheta_xi, show 40 * p = 8 * 5 * p by ring, h]

instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

lemma sqClasses_thirteen : sqClasses 13 = {1, 9, 12, 10, 3, 4} := by
  unfold sqClasses; decide

/-- The representatives of the square classes modulo `13`. -/
def B13 (s : ZMod 13) : ℤ :=
  if s = 1 then 1 else if s = 9 then 3 else if s = 12 then 5 else if s = 10 then 7 else
    if s = 3 then 9 else 11

def C13 (s : ZMod 13) : ℤ := if s = 3 then 1 else if s = 4 then 2 else 0

lemma admissible_thirteen : ∀ s ∈ sqClasses 13,
    Admissible 13 (B13 s) (C13 s) ∧ ((B13 s : ℤ) : ZMod 13) ^ 2 = s := by
  rw [sqClasses_thirteen]
  intro s hs
  simp only [mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [B13, C13] <;> decide

/-- **The case `ℓ = 13` of Theorem 5.1.** -/
theorem trace_thirteen (hp2 : p ≠ 2) (hp13 : p ≠ 13) {ξ : DirichletCharacter ℂ 13}
    (hξ : orderOf ξ = 4) :
    (bern (8 * 13 * p) (vartheta p ξ)).re =
      -((floorSum 13 1 0 p + floorSum 13 3 0 p - floorSum 13 5 0 p - floorSum 13 7 0 p +
        floorSum 13 9 1 p - floorSum 13 11 2 p + 2 : ℤ) : ℝ) := by
  rw [conductor_trace' hp2 (by norm_num) hp13 hξ B13 C13 admissible_thirteen,
    sqClasses_thirteen]
  have l1 : legendreSym 13 1 = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have l3 : legendreSym 13 3 = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have l5 : legendreSym 13 5 = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have l7 : legendreSym 13 7 = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have l9 : legendreSym 13 9 = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have l11 : legendreSym 13 11 = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  rw [show B13 1 = 1 by decide, show B13 9 = 3 by decide, show B13 12 = 5 by decide,
    show B13 10 = 7 by decide, show B13 3 = 9 by decide, show B13 4 = 11 by decide,
    show C13 1 = 0 by decide, show C13 9 = 0 by decide, show C13 12 = 0 by decide,
    show C13 10 = 0 by decide, show C13 3 = 1 by decide, show C13 4 = 2 by decide,
    l1, l3, l5, l7, l9, l11]
  simp only [Int.negOnePow_zero, Int.negOnePow_one, show (2 : ℤ).negOnePow = 1 by decide]
  push_cast
  ring

end QuadraticFloorII
