module

public import Mathlib.FieldTheory.AlgebraicClosure

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]
  (h : finrank F K = 2)

lemma divisor_by_finrank {f : Polynomial F} (hf : f.natDegree ≠ 0) :
  ∃ (d : Polynomial F), d.Monic ∧ d.natDegree ∣ finrank F K ∧ d ∣ f := by
  have hf1 := Polynomial.degree_ne_of_natDegree_ne hf
  obtain ⟨c, hc⟩ :=
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    have := FaithfulSMul.algebraMap_injective F K
    IsAlgClosed.exists_aeval_eq_zero_of_injective K this f hf1
  use minpoly F c
  have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  open minpoly in exact ⟨monic h_int, degree_dvd h_int, dvd_iff.mpr hc⟩

include h in
lemma quadratic_algebraic_closure : ∀ (a b : F), IsSquare (a*a+b) ∨ IsSquare (-b) := by
  intro a b
  let g1 := monomial 4 (1 : F)
  let g2 := monomial 2 (-2*a)
  let g3 := monomial 0 (a^2+b)
  let g := g1 + g2 + g3
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧
    g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0 ∧ g.coeff 4 = 1 ∧ ∀ (n : ℕ), n > 4 → g.coeff n = 0 := by
    have : ∀ n : ℕ, g1.coeff n = (if 4 = n then 1 else 0) ∧ g2.coeff n = (if 2 = n then (-2*a) else 0) ∧
      g3.coeff n = (if 0 = n then (a^2+b) else 0) := by
      intro n
      grind [coeff_monomial]
    have : ∀ n : ℕ, n > 4 → g.coeff n = 0 := by aesop
    simp_all [g]
  have h1 := natDegree_le_iff_coeff_eq_zero.mpr hg5
  have h_gmon := monic_of_natDegree_le_of_coeff_eq_one 4 h1 hg4
  have h_gdeg := natDegree_eq_of_le_of_coeff_ne_zero h1 (ne_zero_of_eq_one hg4)
  obtain ⟨f, hf1, hf2, hf3⟩ : ∃ f0 : Polynomial F, f0.Monic ∧ f0.natDegree = 2 ∧ f0 ∣ g := by
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    have hg0 : g.natDegree ≠ 0 := by simp_all
    have h_divh : ∀ h : Polynomial F, h.natDegree ≠ 0 → ∃ (f : Polynomial F),
      f.Monic ∧ (f.natDegree = 1 ∨ f.natDegree = 2) ∧ f ∣ h := by
      intro p h0
      obtain ⟨f, h1, h2, h3⟩ := divisor_by_finrank F K h0
      use f
      rw [h] at h2
      exact ⟨h1, (Nat.dvd_prime Nat.prime_two).mp h2, h3⟩
    obtain ⟨f, h_fmon, h_fdeg, h_div⟩ := h_divh g hg0
    cases h_fdeg
    · obtain ⟨e, h_ef1, h_emonic, _⟩ := polynomial_monic_divisor h_fmon h_gmon h_div
      have h_div1a := dvd_of_mul_right_eq f h_ef1
      have he0 : e.natDegree ≠ 0 := by simp_all only [ne_eq, not_false_eq_true, Nat.reduceEqDiff]
      obtain ⟨f, h_fmon, h_fdeg, h_div⟩ := h_divh e he0
      cases h_fdeg with
      | inl =>
        obtain ⟨d, h_d1, h_dmonic, _⟩ := polynomial_monic_divisor h_fmon h_emonic h_div
        use d
        have h_div4 := dvd_of_mul_right_eq f h_d1
        refine ⟨h_dmonic, ?_, dvd_trans h_div4 h_div1a⟩
        linarith
      | inr h_fdeg =>
        use f
        exact ⟨h_fmon, h_fdeg, dvd_trans h_div h_div1a⟩
    · use f
  obtain ⟨e, h_ftimese, h_emon, _⟩ := polynomial_monic_divisor hf1 h_gmon hf3
  have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 := by
    have : f.coeff f.natDegree = f.leadingCoeff := coeff_natDegree
    have : f.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → f.coeff N = 0 := natDegree_le_iff_coeff_eq_zero
    simp_all
  have : e.coeff 2 = 1 ∧ e.coeff 3 = 0 ∧ e.coeff 4 = 0 := by
    have : e.coeff e.natDegree = e.leadingCoeff := coeff_natDegree
    have : e.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → e.coeff N = 0 := natDegree_le_iff_coeff_eq_zero
    simp_all
  have h_prod := coeff_mul e f
  have : e.coeff 0 * f.coeff 0 = a^2 + b ∧ e.coeff 0 * f.coeff 1 + e.coeff 1 * f.coeff 0 = 0 := by
    rw [←hg0, ←hg1, ←h_ftimese]
    exact ⟨(mul_coeff_zero e f).symm, (mul_coeff_one e f).symm⟩
  have : f.coeff 0 + e.coeff 1 * f.coeff 1 + e.coeff 0 = -2*a := by
    specialize h_prod 2
    simp [Finset.antidiagonal] at h_prod
    grind only
  have : e.coeff 1 + f.coeff 1 = 0 := by
    specialize h_prod 3
    simp [Finset.antidiagonal] at h_prod
    simp_all
  unfold IsSquare
  if f.coeff 1 = 0 then
    right
    use f.coeff 0 + a
    have : e.coeff 0 = - f.coeff 0 - 2*a := by grind => ring
    simp_all only
    grind => ring
  else
    left
    use f.coeff 0
    simp_all only
    grind => ring

include h in
lemma quadratic_algebraic_closure_no_i : ∀ (a : F), IsSquare a ∨ IsSquare (-a) := by
  intro a
  have : IsSquare (0 * 0 + a) ∨ IsSquare (-a) := quadratic_algebraic_closure F K h 0 a
  simp_all
