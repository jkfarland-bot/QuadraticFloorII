module

public import QuadraticFloorII.Reduced

@[expose] public section

/-!
# Fibre sums (Corollaries 3.5 and 3.6)

Multiplying the square-class decomposition by `ψ₀(b)²` and summing over `b` modulo `A`, orthogonality
of the characters `(ψ₀ψ⁻¹)²` leaves exactly the characters `ψ` with `ψ² = ψ₀²`:

  `∑_{b mod A} ψ₀(b)² (𝒮_{A,B_b,C_b}(p) - (-1)^{C_b}) = -∑_{ψ² = ψ₀²} B_{1,ϑ_{p,ψ}}^{(8Ap)}`,

where `(B_b, C_b)` is any admissible pair with `B_b ≡ b (mod A)`. This is Corollary 3.5 summed over
units rather than over a system of square-class representatives (each square class is counted once
for each of its square roots). If `ψ₀⁴ = 1` the fibre is closed under `ψ ↦ ψ⁻¹ = ψ̄`, so the fibre sum
is real (Corollary 3.6).
-/

namespace QuadraticFloorII

open Finset

variable {p : ℕ} [hp : Fact p.Prime] {A : ℕ}

lemma sum_char_sq_mul_inv_sq [NeZero A] (ψ₀ ψ : DirichletCharacter ℂ A) :
    ∑ b : ZMod A, ψ₀ b ^ 2 * (starRingEnd ℂ (ψ b)) ^ 2 =
      if ψ ^ 2 = ψ₀ ^ 2 then (A.totient : ℂ) else 0 := by
  have hpt : ∀ b : ZMod A, ψ₀ b ^ 2 * (starRingEnd ℂ (ψ b)) ^ 2 = ((ψ₀ * ψ⁻¹) ^ 2) b := by
    intro b
    rw [← RCLike.star_def, MulChar.star_apply', MulChar.pow_apply' _ two_ne_zero,
      MulChar.mul_apply, mul_pow]
  rw [Fintype.sum_congr _ _ hpt]
  have hiff : (ψ₀ * ψ⁻¹) ^ 2 = 1 ↔ ψ ^ 2 = ψ₀ ^ 2 := by
    rw [mul_pow, inv_pow, mul_inv_eq_one, eq_comm]
  split_ifs with h
  · rw [hiff.2 h, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one (fun h' => h (hiff.1 h'))

/-- **Corollary 3.5 (fibre sums), summed over units.** For a positive odd `A`, an odd prime
`p ∤ A`, a character `ψ₀` modulo `A`, and admissible pairs `(B_b, C_b)` with `B_b ≡ b (mod A)` for
every unit `b`:
`∑_{b mod A} ψ₀(b)² (𝒮_{A,B_b,C_b}(p) - (-1)^{C_b}) = -∑_{ψ² = ψ₀²} B_{1,ϑ_{p,ψ}}^{(8Ap)}`.
(The weight `ψ₀(b)²` vanishes when `b` is not a unit.) -/
theorem fibre_sum' (hp2 : p ≠ 2) [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A)
    (ψ₀ : DirichletCharacter ℂ A) (Bs Cs : ZMod A → ℤ)
    (hBC : ∀ b : ZMod A, IsUnit b → Admissible A (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod A) = b) :
    ∑ b : ZMod A, ψ₀ b ^ 2 *
        ((floorSum A (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      -∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) := by
  have htot : (A.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hA.pos).ne'
  have hpt : ∀ b : ZMod A, ψ₀ b ^ 2 *
      ((floorSum A (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      -(1 / (A.totient : ℂ)) * ∑ ψ : DirichletCharacter ℂ A,
        (ψ₀ b ^ 2 * (starRingEnd ℂ (ψ b)) ^ 2) * bern (8 * A * p) (vartheta p ψ) := by
    intro b
    by_cases hb : IsUnit b
    · obtain ⟨hadm, hcast⟩ := hBC b hb
      rw [square_class_decomposition' hp2 hA hpA hadm, hcast, mul_sum, mul_sum]
      simp only [sub_sub_cancel_left, mul_sum, neg_mul, sum_neg_distrib, mul_neg, neg_inj]
      apply sum_congr rfl; intro ψ _; ring
    · rw [MulChar.map_nonunit _ hb]; simp
  rw [Fintype.sum_congr _ _ hpt, ← mul_sum, sum_comm]
  simp only [← sum_mul, sum_char_sq_mul_inv_sq, ite_mul, zero_mul]
  rw [← sum_filter]
  unfold fibre
  rw [mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro ψ _
  field_simp

omit hp in
/-- `B_{1,ϑ_{p,ψ⁻¹}} = conj B_{1,ϑ_{p,ψ}}`. -/
lemma bern_vartheta_inv {A : ℕ} [NeZero A] (ψ : DirichletCharacter ℂ A) :
    bern (8 * A * p) (vartheta p ψ⁻¹) = starRingEnd ℂ (bern (8 * A * p) (vartheta p ψ)) := by
  rw [← bern_conj]
  congr 1
  funext x
  unfold vartheta
  have hneg : ψ⁻¹ (-1) = ψ (-1) := by
    rcases psi_neg_one ψ with h | h
    · rw [← MulChar.star_apply', h]; simp
    · rw [← MulChar.star_apply', h]; simp
  rw [hneg, ← MulChar.star_apply', map_mul, map_mul, map_intCast]
  split_ifs
  · rw [map_intCast]; rfl
  · rw [map_pow, map_intCast]; rfl

omit hp in
/-- **Corollary 3.6 (characters of order four are seen through their traces).** If `ψ₀⁴ = 1`, the
fibre `{ψ : ψ² = ψ₀²}` is closed under `ψ ↦ ψ⁻¹ = ψ̄`, so the fibre sum of Corollary 3.5 is real:
it equals `∑_{ψ² = ψ₀²} Re B_{1,ϑ_{p,ψ}}^{(8Ap)}`. -/
theorem fibre_sum_real' [NeZero A] (ψ₀ : DirichletCharacter ℂ A) (h4 : ψ₀ ^ 4 = 1) :
    ∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) =
      ((∑ ψ ∈ fibre ψ₀, (bern (8 * A * p) (vartheta p ψ)).re : ℝ) : ℂ) := by
  set S := ∑ ψ ∈ fibre ψ₀, bern (8 * A * p) (vartheta p ψ) with hS
  have hinv : ∀ ψ ∈ fibre ψ₀, ψ⁻¹ ∈ fibre ψ₀ := by
    intro ψ hψ
    unfold fibre at *
    rw [mem_filter] at *
    refine ⟨mem_univ _, ?_⟩
    rw [inv_pow, hψ.2]
    have : ψ₀ ^ 2 * ψ₀ ^ 2 = 1 := by rw [← pow_add]; exact h4
    exact inv_eq_of_mul_eq_one_right this
  have hconj : starRingEnd ℂ S = S := by
    rw [hS, map_sum]
    refine sum_nbij' (fun ψ => ψ⁻¹) (fun ψ => ψ⁻¹) hinv hinv (fun ψ _ => inv_inv ψ)
      (fun ψ _ => inv_inv ψ) ?_
    intro ψ _
    rw [bern_vartheta_inv]
  have him : S.im = 0 := by
    have := congrArg Complex.im hconj
    rw [Complex.conj_im] at this
    linarith
  exact Complex.ext (by simp [hS, Complex.re_sum]) (by simp [him])

end QuadraticFloorII
