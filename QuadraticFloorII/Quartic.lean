module

public import QuadraticFloorII.Fibre

@[expose] public section

/-!
# Quartic characters modulo a prime `ℓ ≡ 1 (mod 4)`

For a prime `ℓ` and a character `ξ` of order `4` modulo `ℓ`:

* `ξ² = (·/ℓ)`, so `ξ(b)² = (b/ℓ)` (`xi_sq_eq_legendre`);
* the fibre of `ξ` under squaring is `{ξ, ξ⁻¹}` and the fibre of `1` is `{1, ξ²}`;
* `ξ(-1) = 1` exactly when `ℓ ≡ 1 (mod 8)`;
* a quartic character exists modulo every prime `ℓ ≡ 1 (mod 4)` (`exists_quartic`).
-/

namespace QuadraticFloorII

open Finset

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The Legendre symbol modulo `ℓ` as a complex multiplicative character. -/
noncomputable def legChar (ℓ : ℕ) [Fact ℓ.Prime] : DirichletCharacter ℂ ℓ :=
  (quadraticChar (ZMod ℓ)).ringHomComp (Int.castRingHom ℂ)

lemma legChar_apply (a : ℤ) : legChar ℓ (a : ZMod ℓ) = (legendreSym ℓ a : ℂ) := by
  simp [legChar, legendreSym]

lemma legChar_apply_nat (x : ℕ) : legChar ℓ (x : ZMod ℓ) = (legendreSym ℓ x : ℂ) := by
  have := legChar_apply (ℓ := ℓ) (x : ℤ); push_cast at this; exact this

lemma card_units_prime : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hℓ.out]

lemma generator_not_square {g : (ZMod ℓ)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) (hℓ2 : ℓ ≠ 2) :
    ¬ IsSquare (g : ZMod ℓ) := by
  rintro ⟨y, hy⟩
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [card_units_prime] at hord
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨k, hk⟩ : 2 ∣ ℓ - 1 := by
    rcases hℓ.out.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hℓ2
    · exact ⟨k, by omega⟩
  have hgk : g ^ k = 1 := by
    ext
    push_cast
    rw [hy, ← pow_two, ← pow_mul, ← hk]
    exact ZMod.pow_card_sub_one_eq_one hy0
  have hdvd := orderOf_dvd_of_pow_eq_one hgk
  rw [hord] at hdvd
  have h2 := hℓ.out.two_le
  have hk0 : 0 < k := by omega
  have := Nat.le_of_dvd hk0 hdvd
  omega

lemma legChar_generator {g : (ZMod ℓ)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) (hℓ2 : ℓ ≠ 2) :
    legChar ℓ (g : ZMod ℓ) = -1 := by
  simp only [legChar, MulChar.ringHomComp_apply]
  rw [quadraticChar_neg_one_iff_not_isSquare.2 (generator_not_square hg hℓ2)]
  simp

variable {ξ : DirichletCharacter ℂ ℓ}

lemma generator_value (hξ : orderOf ξ = 4) {g : (ZMod ℓ)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : ξ (g : ZMod ℓ) ^ 2 = -1 := by
  have h4 : ξ ^ 4 = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ
  have h2 : ξ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hξ]; norm_num)
  have hz4 : ξ (g : ZMod ℓ) ^ 4 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), h4, MulChar.one_apply g.isUnit]
  have hz2 : ξ (g : ZMod ℓ) ^ 2 ≠ 1 := by
    intro h
    apply h2
    rw [MulChar.eq_iff hg, MulChar.pow_apply' _ (by norm_num), h, MulChar.one_apply g.isUnit]
  have : (ξ (g : ZMod ℓ) ^ 2 - 1) * (ξ (g : ZMod ℓ) ^ 2 + 1) = 0 := by
    linear_combination hz4
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hz2
  · linear_combination h

theorem xi_sq_eq_leg (hξ : orderOf ξ = 4) (hℓ2 : ℓ ≠ 2) : ξ ^ 2 = legChar ℓ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  rw [MulChar.eq_iff hg, MulChar.pow_apply' _ (by norm_num), generator_value hξ hg,
    legChar_generator hg hℓ2]

/-- `ξ(b)² = (b/ℓ)` for a quartic `ξ`. -/
theorem xi_sq_eq_legendre (hξ : orderOf ξ = 4) (hℓ2 : ℓ ≠ 2) (a : ℤ) :
    ξ (a : ZMod ℓ) ^ 2 = (legendreSym ℓ a : ℂ) := by
  rw [← MulChar.pow_apply' _ (by norm_num), xi_sq_eq_leg hξ hℓ2, legChar_apply]

omit hℓ in
lemma xi_pow_four (hξ : orderOf ξ = 4) : ξ ^ 4 = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ

/-- The fibre of a quartic `ξ` under squaring is `{ξ, ξ⁻¹}`. -/
theorem fibre_xi (hξ : orderOf ξ = 4) : fibre ξ = {ξ, ξ⁻¹} := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  have hz := generator_value hξ hg
  set z := ξ (g : ZMod ℓ)
  have h4 := xi_pow_four hξ
  ext ψ
  unfold fibre
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro h
    have hw : ψ (g : ZMod ℓ) ^ 2 = z ^ 2 := by
      rw [← MulChar.pow_apply' _ (by norm_num), h, MulChar.pow_apply' _ (by norm_num)]
    have : (ψ (g : ZMod ℓ) - z) * (ψ (g : ZMod ℓ) + z) = 0 := by linear_combination hw
    rcases mul_eq_zero.1 this with h1 | h1
    · left; rw [MulChar.eq_iff hg]; exact sub_eq_zero.1 h1
    · right
      rw [MulChar.eq_iff hg, MulChar.inv_apply_eq_inv']
      exact eq_inv_of_mul_eq_one_left (by linear_combination z * h1 - hz)
  · rintro (rfl | rfl)
    · rfl
    · rw [inv_pow]
      have : ξ ^ 2 * ξ ^ 2 = 1 := by rw [← pow_add]; exact h4
      exact (inv_eq_of_mul_eq_one_right this)

omit hℓ in
theorem xi_ne_inv (hξ : orderOf ξ = 4) : ξ ≠ ξ⁻¹ := by
  intro h
  have : ξ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel ξ
  exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hξ]; norm_num) this

/-- The fibre of the trivial character is `{1, ξ²}`. -/
theorem fibre_one (hξ : orderOf ξ = 4) :
    fibre (1 : DirichletCharacter ℂ ℓ) = {1, ξ ^ 2} := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  have hz := generator_value hξ hg
  have h4 := xi_pow_four hξ
  ext ψ
  unfold fibre
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, one_pow]
  constructor
  · intro h
    have hw : ψ (g : ZMod ℓ) ^ 2 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), h, MulChar.one_apply g.isUnit]
    have : (ψ (g : ZMod ℓ) - 1) * (ψ (g : ZMod ℓ) + 1) = 0 := by linear_combination hw
    rcases mul_eq_zero.1 this with h1 | h1
    · left; rw [MulChar.eq_iff hg, MulChar.one_apply g.isUnit]; exact sub_eq_zero.1 h1
    · right
      rw [MulChar.eq_iff hg, MulChar.pow_apply' _ (by norm_num), hz]
      linear_combination h1
  · rintro (rfl | rfl)
    · exact one_pow 2
    · rw [← pow_mul]; exact h4

omit hℓ in
lemma one_ne_xi_sq (hξ : orderOf ξ = 4) : (1 : DirichletCharacter ℂ ℓ) ≠ ξ ^ 2 :=
  fun h => pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hξ]; norm_num) h.symm

/-- A character of order `4` exists modulo every prime `ℓ ≡ 1 (mod 4)`. -/
theorem exists_quartic (h4 : ℓ % 4 = 1) : ∃ ξ : DirichletCharacter ℂ ℓ, orderOf ξ = 4 := by
  have hdvd : 4 ∣ Fintype.card (ZMod ℓ) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod ℓ) hdvd
    (Complex.isPrimitiveRoot_exp 4 (by norm_num))
  exact ⟨χ, hχ⟩

end QuadraticFloorII
