module

public import QuadraticFloorII.CoefficientFive

@[expose] public section

/-!
# Euler factors

For a function `f` of period `m` whose sum over a period vanishes, `B_{1,f}^{(km)} = B_{1,f}^{(m)}`,
and if `f` is multiplicative along multiples of `ℓ`, removing the multiples of `ℓ` multiplies the
Bernoulli number by the Euler factor:
`B_{1,f·1_{ℓ∤·}}^{(mℓ)} = (1 - f(ℓ)) B_{1,f}^{(m)}` (manuscript, equation (12)). For `η_p` this gives
`B_{1,η_p}^{(8ℓp)} = (1 - η_p(ℓ)) B_{1,η_p}^{(8p)}`, which turns the Bernoulli forms of the cases
`A = 3` and `A = 5` into the shape of the manuscript's class-number formulas.
-/

namespace QuadraticFloorII

open Finset

lemma periodic_mul (f : ℕ → ℂ) {m : ℕ} (hper : ∀ x, f (x + m) = f x) (x k : ℕ) :
    f (x + k * m) = f x := by
  induction k with
  | zero => simp
  | succ k ih => rw [show x + (k + 1) * m = (x + k * m) + m by ring, hper, ih]

/-- `∑_{x=1}^{km} x f(x) = k ∑_{x=1}^{m} x f(x)` when `f` has period `m` and vanishing period sum. -/
lemma sum_mul_period (f : ℕ → ℂ) {m : ℕ} (hper : ∀ x, f (x + m) = f x)
    (hsum : ∑ x ∈ Icc 1 m, f x = 0) (k : ℕ) :
    ∑ x ∈ Icc 1 (k * m), (x : ℂ) * f x = k * ∑ x ∈ Icc 1 m, (x : ℂ) * f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 := sum_Icc_one (fun x => (x : ℂ) * f x) ((k + 1) * m)
    have e2 := sum_Icc_one (fun x => (x : ℂ) * f x) (k * m)
    have e3 := sum_Icc_one (fun x => (x : ℂ) * f x) m
    have e4 := sum_Icc_one f m
    rw [e1, show (k + 1) * m = k * m + m by ring, sum_range_add, ← e2, ih]
    have h : ∀ j ∈ range m, ((k * m + j + 1 : ℕ) : ℂ) * f (k * m + j + 1) =
        ((k * m : ℕ) : ℂ) * f (j + 1) + ((j + 1 : ℕ) : ℂ) * f (j + 1) := by
      intro j _
      rw [show k * m + j + 1 = (j + 1) + k * m by ring, periodic_mul f hper]
      push_cast; ring
    rw [sum_congr rfl h, sum_add_distrib, ← mul_sum, ← e3, ← e4, hsum]
    push_cast; ring

/-- `B_{1,f}^{(km)} = B_{1,f}^{(m)}`. -/
lemma bern_mul_period (f : ℕ → ℂ) {m : ℕ} (hper : ∀ x, f (x + m) = f x)
    (hsum : ∑ x ∈ Icc 1 m, f x = 0) {k : ℕ} (hk : 0 < k) : bern (k * m) f = bern m f := by
  unfold bern
  rw [sum_mul_period f hper hsum k]
  by_cases hm : m = 0
  · subst hm; simp
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp

lemma filter_dvd_Icc {m ℓ : ℕ} (hℓ : 0 < ℓ) :
    (Icc 1 (m * ℓ)).filter (fun x => ℓ ∣ x) = (Icc 1 m).image (fun y => ℓ * y) := by
  ext x
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨y, rfl⟩⟩
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos y with h | h
      · subst h; omega
      · exact h
    · rw [mul_comm] at h2; exact Nat.le_of_mul_le_mul_right h2 hℓ
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right ℓ y⟩
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hℓ.ne' (by omega))
    · rw [mul_comm m]; exact Nat.mul_le_mul_left ℓ h2

/-- **The Euler factor** (manuscript, equation (12)):
`B_{1,f·1_{ℓ∤·}}^{(mℓ)} = (1 - f(ℓ)) B_{1,f}^{(m)}`. -/
theorem bern_euler (f : ℕ → ℂ) {m ℓ : ℕ} (hℓ : 0 < ℓ) (hper : ∀ x, f (x + m) = f x)
    (hsum : ∑ x ∈ Icc 1 m, f x = 0) (hmul : ∀ y, f (ℓ * y) = f ℓ * f y) :
    bern (m * ℓ) (fun x => f x * (if ℓ ∣ x then 0 else 1)) = (1 - f ℓ) * bern m f := by
  have hsplit : ∀ x, f x * (if ℓ ∣ x then 0 else 1) = f x - (if ℓ ∣ x then f x else 0) := by
    intro x; split_ifs <;> ring
  have hfull : bern (m * ℓ) f = bern m f := by
    rw [mul_comm]; exact bern_mul_period f hper hsum hℓ
  have hmult : ∑ x ∈ Icc 1 (m * ℓ), (x : ℂ) * (if ℓ ∣ x then f x else 0) =
      (ℓ : ℂ) * f ℓ * ∑ y ∈ Icc 1 m, (y : ℂ) * f y := by
    have : ∀ x ∈ Icc 1 (m * ℓ), (x : ℂ) * (if ℓ ∣ x then f x else 0) =
        if ℓ ∣ x then (x : ℂ) * f x else 0 := fun x _ => by split_ifs <;> ring
    rw [sum_congr rfl this, ← sum_filter, filter_dvd_Icc hℓ, sum_image (fun a _ b _ h =>
      Nat.eq_of_mul_eq_mul_left hℓ h), mul_sum]
    apply sum_congr rfl
    intro y _
    rw [hmul]; push_cast; ring
  unfold bern at hfull ⊢
  simp only [hsplit, mul_sub, sum_sub_distrib]
  rw [hmult, hfull]
  by_cases hm : m = 0
  · subst hm; simp
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  field_simp

variable {p : ℕ} [hp : Fact p.Prime]

lemma eta_periodic (hp2 : p ≠ 2) (x : ℕ) : (eta p (x + 8 * p) : ℂ) = eta p x := by
  have h := eta_add_half hp2 (A := 1) odd_one
  rw [show x + 8 * p = (x + 4 * 1 * p) + 4 * 1 * p by ring, h, h, neg_neg]

lemma eta_sum_zero (hp2 : p ≠ 2) : ∑ x ∈ Icc 1 (8 * p), (eta p x : ℂ) = 0 := by
  rw [sum_Icc_one, show 8 * p = 4 * p + 4 * p by ring, sum_range_add]
  have : ∀ k ∈ range (4 * p), (eta p (4 * p + k + 1) : ℂ) = -(eta p (k + 1) : ℂ) := by
    intro k _
    rw [show 4 * p + k + 1 = (k + 1) + 4 * 1 * p by ring, eta_add_half hp2 odd_one]
    push_cast; ring
  rw [sum_congr rfl this, sum_neg_distrib, add_neg_cancel]

omit hp in
/-- `η_p(ℓ y) = η_p(ℓ) η_p(y)`. -/
lemma eta_mul (ℓ y : ℕ) : eta p (ℓ * y) = eta p ℓ * eta p y := by
  unfold eta
  by_cases hl : Even ℓ
  · simp [hl, hl.mul_right]
  by_cases hy : Even y
  · simp [hy, hy.mul_left]
  have hly : ¬ Even (ℓ * y) := by
    rw [Nat.not_even_iff_odd] at *; exact hl.mul hy
  have hl0 : NeZero ℓ := ⟨fun h => hl (h ▸ ⟨0, rfl⟩)⟩
  have hy0 : NeZero y := ⟨fun h => hy (h ▸ ⟨0, rfl⟩)⟩
  rw [ite_of_neg hl, ite_of_neg hy, ite_of_neg hly, jacobiSym.mul_right]

/-- **The Euler factor for `η_p`**: `B_{1,η_p}^{(8ℓp)} = (1 - η_p(ℓ)) B_{1,η_p}^{(8p)}`, where on
the left `η_p` is induced to modulus `8ℓp`. -/
theorem bern_eta_euler (hp2 : p ≠ 2) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    bern (8 * ℓ * p) (fun x => (eta p x : ℂ) * (if ℓ ∣ x then 0 else 1)) =
      (1 - (eta p ℓ : ℂ)) * bern (8 * p) (fun x => (eta p x : ℂ)) := by
  rw [show 8 * ℓ * p = 8 * p * ℓ by ring]
  exact bern_euler (fun x => (eta p x : ℂ)) hℓ (eta_periodic hp2) (eta_sum_zero hp2)
    (fun y => by rw [eta_mul]; push_cast; ring)

end QuadraticFloorII
