module

public import QuadraticFloorII.Examples

@[expose] public section

/-!
# The triangular sum over a half period (Paper III, Theorem 4.4)

The terms `n` and `p - 1 - n` of `𝒮_{1,1,0}(p) = ∑_{n<p} (-1)^{⌊n(n+1)/p⌋}` agree, the end terms are
`+1` and the middle term `n = (p-1)/2` is `(-1)^{⌊(p-1)/4⌋} = (-2/p)`. Hence

  `2 ∑_{n=1}^{(p-1)/2} (-1)^{⌊n(n+1)/p⌋} = 𝒮_{1,1,0}(p) - 2 + (-2/p)`,

which with `𝒮_{1,1,0}(p) = 1 + h(-8p)` is `h(-8p)/2 - (1 - (-2/p))/2` for the half sum.
-/

namespace QuadraticFloorII

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- The sign `(-1)^{⌊n(n+1)/p⌋}`. -/
def triSign (p n : ℕ) : ℤ := ((((n : ℤ) * (n + 1)) / p).negOnePow : ℤ)

omit hp in
lemma floorSum_one_eq (p : ℕ) : floorSum 1 1 0 p = ∑ n ∈ range p, triSign p n := by
  unfold floorSum triSign
  apply sum_congr rfl
  intro n _
  congr 3
  ring

lemma triSign_reflect (hp2 : p ≠ 2) {n : ℕ} (hn : n < p) : triSign p (p - 1 - n) = triSign p n := by
  unfold triSign
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h : ((p - 1 - n : ℕ) : ℤ) * ((p - 1 - n : ℕ) + 1) =
      (n : ℤ) * (n + 1) + ((p : ℤ) - 1 - 2 * n) * p := by
    push_cast [show n ≤ p - 1 by omega, show 1 ≤ p from hp.out.one_le]; ring
  rw [h, Int.add_mul_ediv_right _ _ hpz, Int.negOnePow_add]
  have he : Even ((p : ℤ) - 1 - 2 * n) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - n, by push_cast [hk]; ring⟩
  rw [Int.negOnePow_even _ he, mul_one]

lemma triSign_middle (hp2 : p ≠ 2) : triSign p ((p - 1) / 2) = legendreSym p (-2) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hp1 : p % 2 = 1 := Nat.odd_iff.1 hodd
  rw [legendreSym.at_neg_two hp2, ZMod.χ₈'_nat_eq_if_mod_eight]
  unfold triSign
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  set q := (p - 1) / 4 with hq
  have hdiv : (((p - 1) / 2 : ℕ) : ℤ) * ((((p - 1) / 2 : ℕ) : ℤ) + 1) / p = q := by
    rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4
    · have hm : (((p - 1) / 2 : ℕ) : ℤ) = 2 * q := by push_cast; omega
      have hpq : (p : ℤ) = 4 * q + 1 := by omega
      rw [hm, show (2 * (q : ℤ)) * (2 * q + 1) = q + q * p by rw [hpq]; ring,
        Int.add_mul_ediv_right _ _ hpz.ne', Int.ediv_eq_zero_of_lt (by positivity) (by omega),
        zero_add]
    · have hm : (((p - 1) / 2 : ℕ) : ℤ) = 2 * q + 1 := by push_cast; omega
      have hpq : (p : ℤ) = 4 * q + 3 := by omega
      rw [hm, show (2 * (q : ℤ) + 1) * (2 * q + 1 + 1) = (3 * q + 2) + q * p by rw [hpq]; ring,
        Int.add_mul_ediv_right _ _ hpz.ne', Int.ediv_eq_zero_of_lt (by positivity) (by omega),
        zero_add]
  rw [hdiv, ite_of_neg (by omega)]
  rcases (show p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 by omega) with h | h | h | h
  · rw [ite_of_pos (Or.inl h), Int.negOnePow_even _ ⟨((p - 1) / 8 : ℕ), by push_cast; omega⟩]; rfl
  · rw [ite_of_pos (Or.inr h), Int.negOnePow_even _ ⟨((p - 1) / 8 : ℕ), by push_cast; omega⟩]; rfl
  · rw [ite_of_neg (by omega), Int.negOnePow_odd _ ⟨((p - 1) / 8 : ℕ), by push_cast; omega⟩]; rfl
  · rw [ite_of_neg (by omega), Int.negOnePow_odd _ ⟨((p - 1) / 8 : ℕ), by push_cast; omega⟩]; rfl

/-- **The half-range triangular sum** (Paper III, Theorem 4.4, second formula):
`2 ∑_{n=1}^{(p-1)/2} (-1)^{⌊n(n+1)/p⌋} = 𝒮_{1,1,0}(p) - 2 + (-2/p)`. -/
theorem half_range_one' (hp2 : p ≠ 2) :
    2 * ∑ n ∈ Icc 1 ((p - 1) / 2), ((((n : ℤ) * (n + 1)) / p).negOnePow : ℤ) =
      floorSum 1 1 0 p - 2 + legendreSym p (-2) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by have := Nat.odd_iff.1 hodd; omega⟩
  have hmid : (p - 1) / 2 = m := by omega
  rw [← triSign_middle hp2, floorSum_one_eq, hmid]
  change 2 * ∑ n ∈ Icc 1 m, triSign p n = _
  have h0 : triSign p 0 = 1 := by unfold triSign; simp
  -- split the full period
  have hsplit : ∑ n ∈ range p, triSign p n =
      ∑ n ∈ range (m + 1), triSign p n + ∑ k ∈ range m, triSign p (m + 1 + k) := by
    rw [hm, show 2 * m + 1 = (m + 1) + m by ring, sum_range_add]
  have hrefl : ∑ k ∈ range m, triSign p (m + 1 + k) = ∑ k ∈ range m, triSign p k := by
    have : ∀ k ∈ range m, triSign p (m + 1 + k) = triSign p (m - 1 - k) := by
      intro k hk
      rw [mem_range] at hk
      rw [← triSign_reflect hp2 (show m - 1 - k < p by omega)]
      congr 1; omega
    rw [sum_congr rfl this, sum_range_reflect (fun k => triSign p k) m]
  have hIcc : ∑ n ∈ Icc 1 m, triSign p n = ∑ k ∈ range m, triSign p (k + 1) := sum_Icc_one _ _
  rw [hsplit, hrefl, hIcc]
  have e1 := sum_range_succ (fun k => triSign p k) m
  have e2 := sum_range_succ' (fun k => triSign p k) m
  linear_combination e1 - 2 * e2 - 2 * h0

end QuadraticFloorII
