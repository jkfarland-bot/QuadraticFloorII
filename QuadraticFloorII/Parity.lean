module

public import QuadraticFloorII.Conductor

@[expose] public section

/-!
# The quarter-range formula and the parity of both coordinates

For every positive odd `A` and character `ψ` modulo `A`, the odd character `ϑ = ϑ_{p,ψ}` modulo
`8Ap` satisfies `ϑ(x + 4Ap) = -ϑ(x)` and `ϑ(4Ap - x) = ϑ(x)`, so

  `B_{1,ϑ}^{(8Ap)} = -∑_{0<x≤2Ap} ϑ(x)`        (`bern_quarter`).

For a prime `ℓ ≡ 1 (mod 4)` and a quartic `ξ`, the values of `Θ_{ℓ,p} = ϑ_{p,ξ}` lie in
`{0, ±1, ±i}`, and the numbers of `x ∈ (0, 2ℓp]` with `Θ(x) = ±1`, and with `Θ(x) = ±i`, are even by
the symmetry `x ↦ 2ℓp - x`. Hence both coordinates of `B_{1,Θ_{ℓ,p}}` are even integers
(`bern_even`). At `ℓ = 5` this is the parity statement of Corollary 4.8, proved here without the
quartic field `K_p` or its class number.
-/

set_option linter.unusedSimpArgs false

namespace QuadraticFloorII

open Finset Complex

/-- If `K(2n - x) = K(x)` for `x ≤ 2n`, `K(0) = 0` and `K(n) = 0`, then
`∑_{x=1}^{2n} K(x) = 2 ∑_{x=1}^{n} K(x)`. -/
lemma sum_Icc_double {M : Type*} [AddCommMonoid M] (K : ℕ → M) (n : ℕ)
    (hsym : ∀ x ≤ 2 * n, K (2 * n - x) = K x) (h0 : K 0 = 0) (hn : K n = 0) :
    ∑ x ∈ Icc 1 (2 * n), K x = 2 • ∑ x ∈ Icc 1 n, K x := by
  rw [sum_Icc_one, sum_Icc_one, two_mul, sum_range_add, two_nsmul]
  congr 1
  have h1 : ∀ k ∈ range n, K (n + k + 1) = K (n - 1 - k) := by
    intro k hk
    rw [mem_range] at hk
    rw [← hsym (n - 1 - k) (by omega)]
    congr 1; omega
  rw [sum_congr rfl h1, sum_range_reflect (fun k => K k) n]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_range_succ' (fun k => K k), sum_range_succ (fun k => K (k + 1)), h0, hn]

variable {p : ℕ} [hp : Fact p.Prime] {A : ℕ}

omit hp in
lemma vartheta_zero (ψ : DirichletCharacter ℂ A) : vartheta p ψ 0 = 0 := by
  unfold vartheta; simp [eta_of_even (⟨0, rfl⟩ : Even 0)]

omit hp in
lemma vartheta_of_even (ψ : DirichletCharacter ℂ A) {x : ℕ} (hx : Even x) :
    vartheta p ψ x = 0 := by
  unfold vartheta; simp [eta_of_even hx]

/-- `ϑ_{p,ψ}` is odd: `ϑ(8Ap - x) = -ϑ(x)`. -/
lemma vartheta_reflect (hp2 : p ≠ 2) (ψ : DirichletCharacter ℂ A) {x : ℕ}
    (hx : x ≤ 8 * A * p) : vartheta p ψ (8 * A * p - x) = -vartheta p ψ x := by
  unfold vartheta
  rw [eta_reflect hp2 ⟨A, by ring⟩ hx, chi4_reflect A p hx, psi_reflect ψ hx ⟨8 * p, by ring⟩]
  rcases psi_neg_one ψ with h | h
  · have h' : ψ (-1) ≠ -1 := by rw [h]; norm_num
    rw [ite_of_neg h', ite_of_neg h', h]; push_cast; ring
  · rw [ite_of_pos h, ite_of_pos h, h]; push_cast; ring

/-- `ϑ(4Ap - x) = ϑ(x)`. -/
lemma vartheta_quarter_sym (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) {x : ℕ}
    (hx : x ≤ 4 * A * p) : vartheta p ψ (4 * A * p - x) = vartheta p ψ x := by
  have e : 8 * A * p = 4 * A * p + 4 * A * p := by ring
  have h := vartheta_reflect hp2 ψ (show 4 * A * p + x ≤ 8 * A * p by omega)
  rw [show 8 * A * p - (4 * A * p + x) = 4 * A * p - x by omega, add_comm,
    vartheta_add_half hp2 hA, neg_neg] at h
  exact h

/-- **The quarter-range formula.** `B_{1,ϑ_{p,ψ}}^{(8Ap)} = -∑_{x=1}^{2Ap} ϑ_{p,ψ}(x)`. -/
theorem bern_quarter (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) :
    bern (8 * A * p) (vartheta p ψ) = -∑ x ∈ Icc 1 (2 * A * p), vartheta p ψ x := by
  have hh : 0 < 4 * A * p := by have := hA.pos; have := hp.out.pos; positivity
  rw [show 8 * A * p = 2 * (4 * A * p) by ring,
    bern_antiperiodic' _ hh (vartheta_add_half hp2 hA ψ)]
  rw [show 4 * A * p = 2 * (2 * A * p) by ring, sum_Icc_double _ _ (fun x hx => by
      have e : 2 * (2 * A * p) = 4 * A * p := by ring
      rw [e]
      exact vartheta_quarter_sym hp2 hA ψ (by omega))
    (vartheta_zero ψ) (vartheta_of_even ψ ⟨A * p, by ring⟩)]
  rw [two_nsmul]; ring

/-! ### Integer parts -/

/-- The real coordinate of a value in `{0, ±1, ±i}`. -/
noncomputable def reZ (z : ℂ) : ℤ := by
  classical exact if z = 1 then 1 else if z = -1 then -1 else 0

/-- The imaginary coordinate of a value in `{0, ±1, ±i}`. -/
noncomputable def imZ (z : ℂ) : ℤ := by
  classical exact if z = I then 1 else if z = -I then -1 else 0

lemma four_values {z : ℂ} (h : z ^ 4 = 1) : z = 1 ∨ z = -1 ∨ z = I ∨ z = -I := by
  have : (z - 1) * (z + 1) * (z - I) * (z + I) = 0 := by
    linear_combination h - (z ^ 2 - 1) * I_sq
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · left; exact sub_eq_zero.1 h3
      · right; left; exact eq_neg_of_add_eq_zero_left h3
    · right; right; left; exact sub_eq_zero.1 h2
  · right; right; right; exact eq_neg_of_add_eq_zero_left h1

lemma I_ne_one' : I ≠ 1 := by intro h; simpa using congrArg Complex.im h
lemma I_ne_neg_one : I ≠ -1 := by intro h; simpa using congrArg Complex.im h
lemma neg_I_ne_one : -I ≠ 1 := by intro h; simpa using congrArg Complex.im h
lemma neg_I_ne_neg_one : -I ≠ -1 := by intro h; simpa using congrArg Complex.im h
lemma neg_one_ne_one' : (-1 : ℂ) ≠ 1 := by norm_num
lemma I_ne_neg_I : I ≠ -I := by intro h; have := congrArg Complex.im h; simp at this; linarith

lemma decomp {z : ℂ} (h : z = 0 ∨ z ^ 4 = 1) : z = (reZ z : ℂ) + (imZ z : ℂ) * I := by
  unfold reZ imZ
  rcases h with rfl | h
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  rcases four_values h with rfl | rfl | rfl | rfl
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]

lemma reZ_sq {z : ℂ} (h : z = 0 ∨ z ^ 4 = 1) : reZ z ^ 2 = if z ^ 2 = 1 then 1 else 0 := by
  unfold reZ
  rcases h with rfl | h
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  rcases four_values h with rfl | rfl | rfl | rfl
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]

lemma imZ_sq {z : ℂ} (h : z = 0 ∨ z ^ 4 = 1) : imZ z ^ 2 = if z ^ 2 = -1 then 1 else 0 := by
  unfold imZ
  rcases h with rfl | h
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  rcases four_values h with rfl | rfl | rfl | rfl
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]
  · simp [I_ne_one', I_ne_neg_one, neg_I_ne_one, neg_I_ne_neg_one, neg_one_ne_one', I_ne_neg_I, I_ne_one'.symm, I_ne_neg_one.symm, neg_I_ne_one.symm, neg_I_ne_neg_one.symm, neg_one_ne_one'.symm, I_ne_neg_I.symm, I_ne_zero, I_ne_zero.symm, neg_ne_zero.2 I_ne_zero, (neg_ne_zero.2 I_ne_zero).symm]

/-! ### Squares of the integer factors -/

omit hp in
lemma kap_sq_odd {x : ℕ} (hx : Odd x) : kap p (x : ZMod 8) ^ 2 = 1 := by
  have hx2 : x % 2 = 1 := Nat.odd_iff.1 hx
  have h8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  unfold kap
  split_ifs <;>
    simp only [ZMod.χ₈'_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight] <;>
    rcases h8 with h | h | h | h <;> simp [h, hx2]

lemma eta_sq (hp2 : p ≠ 2) (x : ℕ) : eta p x ^ 2 = if Odd x ∧ ¬ p ∣ x then 1 else 0 := by
  by_cases hx : Even x
  · rw [eta_of_even hx, ite_of_neg (by rintro ⟨h, _⟩; exact (Nat.not_even_iff_odd.2 h) hx)]; ring
  have hxo : Odd x := Nat.not_even_iff_odd.1 hx
  by_cases hpx : p ∣ x
  · rw [eta_of_dvd hp2 hpx, ite_of_neg (by rintro ⟨_, h⟩; exact h hpx)]; ring
  rw [ite_of_pos ⟨hxo, hpx⟩, eta_eq' hp2, mul_pow, kap_sq_odd hxo, one_mul]
  apply legendreSym.sq_one
  rw [Ne, Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hpx

lemma chi4_sq (x : ℕ) : (ZMod.χ₄ (x : ZMod 4)) ^ 2 = if Odd x then 1 else 0 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  by_cases hx : Odd x
  · have : x % 2 = 1 := Nat.odd_iff.1 hx
    rw [ite_of_pos hx, ite_of_neg (by omega)]
    split_ifs <;> norm_num
  · have : x % 2 = 0 := by rw [Nat.not_odd_iff] at hx; exact hx
    rw [ite_of_neg hx, ite_of_pos (by omega)]; ring

/-! ### Both coordinates are even -/

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {ξ : DirichletCharacter ℂ ℓ}

/-- The integer factor `η_p χ_{-4}^{δ}` of `Θ_{ℓ,p} = ϑ_{p,ξ}`. -/
noncomputable def efac (p : ℕ) (ξ : DirichletCharacter ℂ ℓ) (x : ℕ) : ℤ := by
  classical exact eta p x *
    (if ξ (-1) = -1 then ZMod.χ₄ (x : ZMod 4) else ZMod.χ₄ (x : ZMod 4) ^ 2)

omit hp in
lemma vartheta_eq_efac (x : ℕ) : vartheta p ξ x = (efac p ξ x : ℂ) * ξ (x : ZMod ℓ) := by
  unfold vartheta efac
  split_ifs <;> push_cast <;> ring

lemma efac_sq (hp2 : p ≠ 2) (x : ℕ) : efac p ξ x ^ 2 = if Odd x ∧ ¬ p ∣ x then 1 else 0 := by
  unfold efac
  rw [mul_pow, eta_sq hp2]
  split_ifs with h1 h2 h2
  · rw [chi4_sq, ite_of_pos h1.1]; ring
  · rw [← pow_mul, show ZMod.χ₄ (x : ZMod 4) ^ (2 * 2) = (ZMod.χ₄ (x : ZMod 4) ^ 2) ^ 2 by ring,
      chi4_sq, ite_of_pos h1.1]; ring
  · ring
  · ring

omit hp in
lemma xi_value (hξ : orderOf ξ = 4) (a : ZMod ℓ) : ξ a = 0 ∨ ξ a ^ 4 = 1 := by
  by_cases ha : IsUnit a
  · right; rw [← MulChar.pow_apply' _ (by norm_num), xi_pow_four hξ, MulChar.one_apply ha]
  · left; exact MulChar.map_nonunit _ ha

omit hp hℓ in
lemma int_sum_even {s : Finset ℕ} {t : ℕ → ℤ} (h : 2 ∣ ∑ x ∈ s, t x ^ 2) : 2 ∣ ∑ x ∈ s, t x := by
  have hd : 2 ∣ ∑ x ∈ s, (t x ^ 2 - t x) := by
    apply dvd_sum
    intro x _
    rw [show t x ^ 2 - t x = t x * (t x - 1) by ring]
    exact Int.even_mul_pred_self (t x) |>.two_dvd
  rw [sum_sub_distrib] at hd
  have := dvd_sub h hd
  simpa using this

omit hp hℓ in
/-- A sum over `(0, 2n]` of a function symmetric under `x ↦ 2n - x` vanishing at `0` and `n`
is even. -/
lemma sym_sum_even (n : ℕ) (K : ℕ → ℤ) (hsym : ∀ x ≤ 2 * n, K (2 * n - x) = K x)
    (h0 : K 0 = 0) (hn : K n = 0) : 2 ∣ ∑ x ∈ Icc 1 (2 * n), K x := by
  rw [sum_Icc_double K n hsym h0 hn, two_nsmul, ← two_mul]
  exact dvd_mul_right 2 _

omit hp in
lemma xi_reflect_sq {n x : ℕ} (hℓn : ℓ ∣ n) (hx : x ≤ n) :
    ξ ((n - x : ℕ) : ZMod ℓ) ^ 2 = ξ (x : ZMod ℓ) ^ 2 := by
  rw [Nat.cast_sub hx, (ZMod.natCast_eq_zero_iff n ℓ).2 hℓn, zero_sub, neg_eq_neg_one_mul,
    map_mul, mul_pow, ← map_pow, neg_one_sq, map_one, one_mul]

omit hp hℓ in
lemma odd_reflect {n x : ℕ} (hn : Even n) (hx : x ≤ n) : Odd (n - x) ↔ Odd x := by
  rw [Nat.odd_iff, Nat.odd_iff]; obtain ⟨k, rfl⟩ := hn; omega

omit hp hℓ in
lemma reZ_zero : reZ 0 = 0 := by unfold reZ; simp

omit hp hℓ in
lemma imZ_zero : imZ 0 = 0 := by
  unfold imZ; simp [I_ne_zero.symm, (neg_ne_zero.2 I_ne_zero).symm]

lemma efac_sq_reflect (hp2 : p ≠ 2) {n x : ℕ} (hn : Even n) (hpn : p ∣ n) (hx : x ≤ n) :
    efac p ξ (n - x) ^ 2 = efac p ξ x ^ 2 := by
  rw [efac_sq hp2, efac_sq hp2]
  have ho := odd_reflect hn hx
  have : p ∣ n - x ↔ p ∣ x := by
    constructor
    · intro h
      have := Nat.dvd_sub hpn h
      rwa [Nat.sub_sub_self hx] at this
    · intro h; exact Nat.dvd_sub hpn h
  simp only [ho, this]

/-- The symmetric integer functions whose sums give the coordinates of `B_{1,Θ_{ℓ,p}}`. -/
lemma coord_sum_even (hp2 : p ≠ 2) (hξ : orderOf ξ = 4) (f : ℂ → ℤ)
    (hf : ∀ z w : ℂ, (z = 0 ∨ z ^ 4 = 1) → (w = 0 ∨ w ^ 4 = 1) → z ^ 2 = w ^ 2 →
      f z ^ 2 = f w ^ 2) (hf0 : f 0 = 0) :
    2 ∣ ∑ x ∈ Icc 1 (2 * (ℓ * p)), efac p ξ x * f (ξ (x : ZMod ℓ)) := by
  apply int_sum_even
  apply sym_sum_even (ℓ * p)
  · intro x hx
    rw [mul_pow, mul_pow, efac_sq_reflect hp2 ⟨ℓ * p, by ring⟩ ⟨2 * ℓ, by ring⟩ hx]
    congr 1
    exact hf _ _ (xi_value hξ _) (xi_value hξ _) (xi_reflect_sq ⟨2 * p, by ring⟩ hx)
  · have : efac p ξ 0 = 0 := by unfold efac; rw [eta_of_even ⟨0, rfl⟩]; simp
    rw [this]; ring
  · have : ξ ((ℓ * p : ℕ) : ZMod ℓ) = 0 := by
      apply MulChar.map_nonunit
      rw [(ZMod.natCast_eq_zero_iff _ ℓ).2 (dvd_mul_right ℓ p)]; exact not_isUnit_zero
    rw [this, hf0]; ring

/-- **Both coordinates of `B_{1,Θ_{ℓ,p}}` are even integers** (for `ℓ = 5`, the parity statement of
Corollary 4.8). For a prime `ℓ ≡ 1 (mod 4)`, a quartic `ξ` modulo `ℓ` and an odd prime `p ≠ ℓ`,
`B_{1,ϑ_{p,ξ}}^{(8ℓp)} = 2a + 2bi` with `a, b ∈ ℤ`. -/
theorem bern_even (hp2 : p ≠ 2) (h4 : ℓ % 4 = 1) (hξ : orderOf ξ = 4) :
    ∃ a b : ℤ, bern (8 * ℓ * p) (vartheta p ξ) = 2 * a + 2 * b * I := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hℓ2
  have hsplit : ∀ x, vartheta p ξ x = ((efac p ξ x * reZ (ξ (x : ZMod ℓ)) : ℤ) : ℂ) +
      ((efac p ξ x * imZ (ξ (x : ZMod ℓ)) : ℤ) : ℂ) * I := by
    intro x
    rw [vartheta_eq_efac]
    nth_rewrite 1 [decomp (xi_value hξ (x : ZMod ℓ))]
    push_cast; ring
  have hre : 2 ∣ ∑ x ∈ Icc 1 (2 * (ℓ * p)), efac p ξ x * reZ (ξ (x : ZMod ℓ)) :=
    coord_sum_even hp2 hξ reZ (fun z w hz hw h => by rw [reZ_sq hz, reZ_sq hw, h]) reZ_zero
  have him : 2 ∣ ∑ x ∈ Icc 1 (2 * (ℓ * p)), efac p ξ x * imZ (ξ (x : ZMod ℓ)) :=
    coord_sum_even hp2 hξ imZ (fun z w hz hw h => by rw [imZ_sq hz, imZ_sq hw, h]) imZ_zero
  obtain ⟨a, ha⟩ := hre
  obtain ⟨b, hb⟩ := him
  refine ⟨-a, -b, ?_⟩
  rw [bern_quarter hp2 hodd ξ, show 2 * ℓ * p = 2 * (ℓ * p) by ring]
  simp only [hsplit, sum_add_distrib, ← sum_mul]
  rw [← Int.cast_sum, ← Int.cast_sum, ha, hb]
  push_cast; ring

end QuadraticFloorII
