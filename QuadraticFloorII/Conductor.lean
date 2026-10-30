module

public import QuadraticFloorII.Quartic

@[expose] public section

/-!
# Quartic traces at conductor `8ℓp` (Theorem 5.1)

Let `ℓ ≡ 1 (mod 4)` be prime, `ξ` a character of order `4` modulo `ℓ`, `p ≠ ℓ` an odd prime and
`Θ_{ℓ,p} = ϑ_{p,ξ} = η_p χ_{-4}^{δ_ℓ} ξ`. For each square class `s` of units modulo `ℓ` fix an admissible
pair `(B_s, C_s)` with `B_s² ≡ s`, and put `σ(s) = 𝒮_{ℓ,B_s,C_s}(p)` and `ε_s = (-1)^{C_s}`. Then

  `Re B_{1,Θ_{ℓ,p}} = -∑_s (B_s/ℓ)(σ(s) - ε_s)`,
  `-B_{1,χ_{-8ℓp}} = 2 ∑_s (σ(s) - ε_s) - (1 - (2p/ℓ))(𝒮_{1,1,0}(p) - 1)`,

where `χ_{-8ℓp} = η_p (·/ℓ)`; by Dirichlet's formula the left side of the second identity is
`h(-8ℓp)` and `𝒮_{1,1,0}(p) - 1` is `h(-8p)`.
-/

namespace QuadraticFloorII

open Finset

variable {p : ℕ} [hp : Fact p.Prime] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Admissible lifts of every unit residue class modulo an odd `A`. -/
lemma exists_lifts {A : ℕ} (hA : Odd A) : ∃ Bs Cs : ZMod A → ℤ, ∀ b : ZMod A, IsUnit b →
    Admissible A (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod A) = b := by
  have : ∀ b : ZMod A, ∃ B C : ℤ, IsUnit b → Admissible A B C ∧ ((B : ℤ) : ZMod A) = b := by
    intro b
    by_cases hb : IsUnit b
    · have : NeZero A := ⟨by have := hA.pos; omega⟩
      have hcop : Int.gcd (b.val : ℤ) A = 1 := by
        have := ZMod.val_coe_unit_coprime hb.unit
        rw [IsUnit.unit_spec] at this
        rw [Int.gcd_natCast_natCast]; exact this
      obtain ⟨B, C, hadm, hmod⟩ := exists_admissible' hA hcop
      refine ⟨B, C, fun _ => ⟨hadm, ?_⟩⟩
      rw [(ZMod.intCast_eq_intCast_iff _ _ A).2 hmod]
      simp
    · exact ⟨0, 0, fun h => absurd h hb⟩
  choose Bs Cs h using this
  exact ⟨Bs, Cs, h⟩

lemma legendre_neg_one (h4 : ℓ % 4 = 1) : legendreSym ℓ (-1) = 1 := by
  rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_one_mod_four h4]

lemma legChar_neg (h4 : ℓ % 4 = 1) (b : ZMod ℓ) : legChar ℓ (-b) = legChar ℓ b := by
  rw [neg_eq_neg_one_mul, map_mul, show (-1 : ZMod ℓ) = ((-1 : ℤ) : ZMod ℓ) by simp,
    legChar_apply, legendre_neg_one h4]
  simp

/-- `∑_{b ≠ 0} H(b²) = 2 ∑_{s ∈ Q_ℓ} H(s)`. -/
lemma sum_sq_classes (hℓ2 : ℓ ≠ 2) (H : ZMod ℓ → ℂ) :
    ∑ b ∈ univ.filter (fun b : ZMod ℓ => b ≠ 0), H (b ^ 2) = 2 * ∑ s ∈ sqClasses ℓ, H s := by
  rw [sum_comp (fun s => H s) (fun b : ZMod ℓ => b ^ 2), mul_sum]
  unfold sqClasses
  apply sum_congr rfl
  intro s hs
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hs
  rw [mem_filter] at hc
  have hc0 := hc.2
  have hcard : (#{b ∈ univ.filter (fun b : ZMod ℓ => b ≠ 0) | b ^ 2 = c ^ 2}) = 2 := by
    have hset : {b ∈ univ.filter (fun b : ZMod ℓ => b ≠ 0) | b ^ 2 = c ^ 2} = {c, -c} := by
      ext b
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨_, hb⟩
        have : (b - c) * (b + c) = 0 := by linear_combination hb
        rcases mul_eq_zero.1 this with h | h
        · left; exact sub_eq_zero.1 h
        · right; linear_combination h
      · rintro (rfl | rfl)
        · exact ⟨hc0, rfl⟩
        · exact ⟨neg_ne_zero.2 hc0, by ring⟩
    have hne : c ≠ -c := by
      intro h
      have h2 : (2 : ZMod ℓ) * c = 0 := by linear_combination h
      rcases mul_eq_zero.1 h2 with h' | h'
      · have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h'
        rw [ZMod.natCast_eq_zero_iff] at this
        exact (hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 this)).elim
      · exact hc0 h'
    rw [hset, card_pair hne]
  rw [hcard]
  simp [two_mul]

variable {ξ : DirichletCharacter ℂ ℓ}

/-- The weighted unit sum of Corollary 3.5 for `ψ₀ = ξ` is `-2 Re B_{1,Θ_{ℓ,p}}`. -/
lemma unit_sum_xi (hp2 : p ≠ 2) (hℓ2 : ℓ ≠ 2) (hpℓ : p ≠ ℓ) (hξ : orderOf ξ = 4)
    (Bs Cs : ZMod ℓ → ℤ)
    (hBC : ∀ b : ZMod ℓ, IsUnit b → Admissible ℓ (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod ℓ) = b) :
    ∑ b : ZMod ℓ, ξ b ^ 2 * ((floorSum ℓ (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      -2 * (((bern (8 * ℓ * p) (vartheta p ξ)).re : ℝ) : ℂ) := by
  have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hℓ2
  have hpA : ¬ p ∣ ℓ := fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 h)
  rw [fibre_sum' hp2 hodd hpA ξ Bs Cs hBC, fibre_xi hξ, sum_pair (xi_ne_inv hξ),
    bern_vartheta_inv, Complex.add_conj]
  push_cast; ring

/-- The admissible floor sum of a unit `b` is that of its square class. -/
lemma floor_term (hp2 : p ≠ 2) (hℓ2 : ℓ ≠ 2) (hpℓ : p ≠ ℓ) (Bs Cs : ZMod ℓ → ℤ)
    (hBC : ∀ b : ZMod ℓ, IsUnit b → Admissible ℓ (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod ℓ) = b)
    (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s)
    {b : ZMod ℓ} (hb : b ≠ 0) :
    floorSum ℓ (Bs b) (Cs b) p = floorSum ℓ (Bq (b ^ 2)) (Cq (b ^ 2)) p ∧
      (Cs b).negOnePow = (Cq (b ^ 2)).negOnePow := by
  have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hℓ2
  have hpA : ¬ p ∣ ℓ := fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 h)
  obtain ⟨hadm, hcast⟩ := hBC b (isUnit_iff_ne_zero.2 hb)
  have hmem : b ^ 2 ∈ sqClasses ℓ := mem_image.2 ⟨b, mem_filter.2 ⟨mem_univ _, hb⟩, rfl⟩
  obtain ⟨hadm', hcast'⟩ := hq _ hmem
  have hsq : (Bs b) ^ 2 ≡ (Bq (b ^ 2)) ^ 2 [ZMOD ℓ] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [hcast, hcast']
  exact floorSum_eq_of_sq_modEq' hp2 hodd hpA hadm hadm' hsq

/-- Each term of the weighted unit sum depends only on the square class of `b`. -/
lemma term_eq (hp2 : p ≠ 2) (hℓ2 : ℓ ≠ 2) (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ) (hξ : orderOf ξ = 4)
    (Bs Cs : ZMod ℓ → ℤ)
    (hBC : ∀ b : ZMod ℓ, IsUnit b → Admissible ℓ (Bs b) (Cs b) ∧ ((Bs b : ℤ) : ZMod ℓ) = b)
    (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s)
    {b : ZMod ℓ} (hb : b ≠ 0) :
    ξ b ^ 2 * ((floorSum ℓ (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      (legendreSym ℓ (Bq (b ^ 2)) : ℂ) *
        ((floorSum ℓ (Bq (b ^ 2)) (Cq (b ^ 2)) p : ℂ) - (((Cq (b ^ 2)).negOnePow : ℤ) : ℂ)) := by
  obtain ⟨hS, hC⟩ := floor_term hp2 hℓ2 hpℓ Bs Cs hBC Bq Cq hq hb
  obtain ⟨hadm, hcast⟩ := hBC b (isUnit_iff_ne_zero.2 hb)
  have hmem : b ^ 2 ∈ sqClasses ℓ := mem_image.2 ⟨b, mem_filter.2 ⟨mem_univ _, hb⟩, rfl⟩
  obtain ⟨hadm', hcast'⟩ := hq _ hmem
  have hw : ξ b ^ 2 = (legendreSym ℓ (Bq (b ^ 2)) : ℂ) := by
    rw [← hcast, xi_sq_eq_legendre hξ hℓ2, ← legChar_apply, ← legChar_apply, hcast]
    have : ((Bq (b ^ 2) : ℤ) : ZMod ℓ) = b ∨ ((Bq (b ^ 2) : ℤ) : ZMod ℓ) = -b := by
      have : (((Bq (b ^ 2) : ℤ) : ZMod ℓ) - b) * (((Bq (b ^ 2) : ℤ) : ZMod ℓ) + b) = 0 := by
        linear_combination hcast'
      rcases mul_eq_zero.1 this with h | h
      · left; exact sub_eq_zero.1 h
      · right; linear_combination h
    rcases this with h | h <;> rw [h]
    rw [legChar_neg h4]
  rw [hw, hS, hC]

/-- **Theorem 5.1, the quartic trace.** With admissible pairs `(B_s, C_s)`, `B_s² ≡ s`, for the
square classes `s` of units modulo `ℓ`:
`Re B_{1,Θ_{ℓ,p}}^{(8ℓp)} = -∑_s (B_s/ℓ)(𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s})`, where `Θ_{ℓ,p} = ϑ_{p,ξ}`. -/
theorem conductor_trace' (hp2 : p ≠ 2) (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ) (hξ : orderOf ξ = 4)
    (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s) :
    (bern (8 * ℓ * p) (vartheta p ξ)).re =
      -∑ s ∈ sqClasses ℓ, ((legendreSym ℓ (Bq s) *
        (floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℝ) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hℓ2
  obtain ⟨Bs, Cs, hBC⟩ := exists_lifts hodd
  have hU := unit_sum_xi hp2 hℓ2 hpℓ hξ Bs Cs hBC
  set H : ZMod ℓ → ℂ := fun s => (legendreSym ℓ (Bq s) : ℂ) *
        ((floorSum ℓ (Bq s) (Cq s) p : ℂ) - (((Cq s).negOnePow : ℤ) : ℂ)) with hH
  have hsplit : ∑ b : ZMod ℓ, ξ b ^ 2 *
      ((floorSum ℓ (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      ∑ b ∈ univ.filter (fun b : ZMod ℓ => b ≠ 0), H (b ^ 2) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro b _
    by_cases hb : b = 0
    · rw [ite_of_neg (not_not.2 hb), hb, MulChar.map_nonunit _ not_isUnit_zero]; simp
    · rw [ite_of_pos hb, term_eq hp2 hℓ2 h4 hpℓ hξ Bs Cs hBC Bq Cq hq hb]
  rw [hsplit, sum_sq_classes hℓ2 H] at hU
  have hre := congrArg Complex.re hU
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, Complex.neg_re] at hre
  rw [Complex.re_sum] at hre
  have : ∀ s ∈ sqClasses ℓ, ((legendreSym ℓ (Bq s) : ℂ) *
      ((floorSum ℓ (Bq s) (Cq s) p : ℂ) - (((Cq s).negOnePow : ℤ) : ℂ))).re =
      ((legendreSym ℓ (Bq s) * (floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℝ) := by
    intro s _
    have key : ∀ a b c : ℤ, ((a : ℂ) * ((b : ℂ) - (c : ℂ))).re = ((a * (b - c) : ℤ) : ℝ) := by
      intro a b c
      rw [show ((a : ℂ) * ((b : ℂ) - (c : ℂ))) = ((a * (b - c) : ℤ) : ℂ) by push_cast; ring]
      exact Complex.intCast_re _
    exact key _ _ _
  rw [sum_congr rfl this] at hre
  linarith

omit hp in
/-- `η_p(ℓ) = (2p/ℓ)` for a prime `ℓ ≡ 1 (mod 4)`. -/
lemma eta_ell (h4 : ℓ % 4 = 1) : eta p ℓ = legendreSym ℓ (2 * p) := by
  rw [eta_odd_prime (by omega), show (-8 * (p : ℤ)) = (-1) * (2 ^ 2 * (2 * p)) by ring,
    legendreSym.mul, legendreSym.mul, legendre_neg_one h4,
    legendreSym.sq_one' ℓ (a := 2) (by
      intro h
      have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      have := hℓ.out.two_le
      omega)]
  ring

omit hp in
lemma one_apply_nat_prime (x : ℕ) :
    (1 : DirichletCharacter ℂ ℓ) (x : ZMod ℓ) = if ℓ ∣ x then 0 else 1 := by
  by_cases h : ℓ ∣ x
  · rw [ite_of_pos h, MulChar.map_nonunit]
    rw [(ZMod.natCast_eq_zero_iff x ℓ).2 h]; exact not_isUnit_zero
  · rw [ite_of_neg h, MulChar.one_apply]
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hℓ.out).2 h).symm

omit hp in
lemma vartheta_one_ell : vartheta p (1 : DirichletCharacter ℂ ℓ) =
    fun x => (eta p x : ℂ) * (if ℓ ∣ x then 0 else 1) := by
  funext x
  unfold vartheta
  have h1 : (1 : DirichletCharacter ℂ ℓ) (-1) ≠ -1 := by
    rw [MulChar.one_apply (IsUnit.neg isUnit_one)]; norm_num
  rw [ite_of_neg h1, eta_mul_chi4_sq, one_apply_nat_prime]

omit hp in
lemma vartheta_xi_sq (h4 : ℓ % 4 = 1) (hξ : orderOf ξ = 4) : vartheta p (ξ ^ 2) =
    fun x => (eta p x : ℂ) * (legendreSym ℓ x : ℂ) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  funext x
  unfold vartheta
  rw [xi_sq_eq_leg hξ hℓ2]
  have h1 : legChar ℓ (-1) ≠ -1 := by
    rw [show (-1 : ZMod ℓ) = ((-1 : ℤ) : ZMod ℓ) by simp, legChar_apply, legendre_neg_one h4]
    norm_num
  rw [ite_of_neg h1, eta_mul_chi4_sq, legChar_apply_nat]

/-- **Theorem 5.1, the quadratic part.**
`-B_{1,χ_{-8ℓp}} = 2 ∑_s (𝒮_{ℓ,B_s,C_s}(p) - (-1)^{C_s}) - (1 - (2p/ℓ))(𝒮_{1,1,0}(p) - 1)`, where
`χ_{-8ℓp} = η_p (·/ℓ)`. -/
theorem conductor_quadratic' (hp2 : p ≠ 2) (h4 : ℓ % 4 = 1) (hpℓ : p ≠ ℓ) (hξ : orderOf ξ = 4)
    (Bq Cq : ZMod ℓ → ℤ)
    (hq : ∀ s ∈ sqClasses ℓ, Admissible ℓ (Bq s) (Cq s) ∧ ((Bq s : ℤ) : ZMod ℓ) ^ 2 = s) :
    -bern (8 * ℓ * p) (fun x => (eta p x : ℂ) * (legendreSym ℓ x : ℂ)) =
      2 * ∑ s ∈ sqClasses ℓ, (((floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℂ) -
        (1 - (legendreSym ℓ (2 * p) : ℂ)) * ((floorSum 1 1 0 p : ℂ) - 1) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hℓ2
  have hpA : ¬ p ∣ ℓ := fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).1 h)
  obtain ⟨Bs, Cs, hBC⟩ := exists_lifts hodd
  have hU := fibre_sum' hp2 hodd hpA (1 : DirichletCharacter ℂ ℓ) Bs Cs hBC
  rw [fibre_one hξ, sum_pair (one_ne_xi_sq hξ), vartheta_one_ell, vartheta_xi_sq h4 hξ,
    bern_eta_euler hp2 hℓ.out.pos, eta_ell h4] at hU
  set G : ZMod ℓ → ℂ := fun s =>
        (((floorSum ℓ (Bq s) (Cq s) p - (Cq s).negOnePow) : ℤ) : ℂ) with hG
  have hsplit : ∑ b : ZMod ℓ, (1 : DirichletCharacter ℂ ℓ) b ^ 2 *
      ((floorSum ℓ (Bs b) (Cs b) p : ℂ) - (((Cs b).negOnePow : ℤ) : ℂ)) =
      ∑ b ∈ univ.filter (fun b : ZMod ℓ => b ≠ 0), G (b ^ 2) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro b _
    by_cases hb : b = 0
    · rw [ite_of_neg (not_not.2 hb), hb, MulChar.map_nonunit _ not_isUnit_zero]; simp
    · obtain ⟨hS, hC⟩ := floor_term hp2 hℓ2 hpℓ Bs Cs hBC Bq Cq hq hb
      rw [ite_of_pos hb, MulChar.one_apply (isUnit_iff_ne_zero.2 hb), hS, hC]
      simp only [hG]; push_cast; ring
  rw [hsplit, sum_sq_classes hℓ2 G] at hU
  have h1 := floorSum_one' hp2
  rw [h1]
  linear_combination (-1 : ℂ) * hU

end QuadraticFloorII
