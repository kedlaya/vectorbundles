module

public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma divisor_by_finrank {f : Polynomial F} (hf : f.degree ≠ 0) :
  ∃ (d : Polynomial F), d.Monic ∧ d.natDegree ∣ finrank F K ∧ d ∣ f := by
  have := IsAlgClosure.isAlgClosed F (K := K)
  have := FaithfulSMul.algebraMap_injective F K
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective K this f hf
  use minpoly F c
  have h_int := Algebra.IsIntegral.isIntegral c (R := F) (A := K)
  open minpoly in exact ⟨monic h_int, degree_dvd h_int, dvd_iff.mpr hc⟩

lemma quadratic_algebraic_closure (h : finrank F K = 2) (a b : F) : IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g1 := monomial 4 (1 : F)
  let g2 := monomial 2 (-2*a)
  let g3 := monomial 0 (a^2+b)
  let g := g1 + g2 + g3
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧
    g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0 ∧ g.coeff 4 = 1 ∧ ∀ n : ℕ, n > 4 → g.coeff n = 0 := by
    have : ∀ n, g1.coeff n = (if 4 = n then 1 else 0) ∧ g2.coeff n = (if 2 = n then (-2*a) else 0) ∧
      g3.coeff n = (if 0 = n then (a^2+b) else 0) := by grind [coeff_monomial]
    have : ∀ n, n > 4 → g.coeff n = 0 := by aesop
    simp_all [g]
  have h1 := natDegree_le_iff_coeff_eq_zero.mpr hg5
  have h_gmon := monic_of_natDegree_le_of_coeff_eq_one 4 h1 hg4
  have h_gdeg := natDegree_eq_of_le_of_coeff_ne_zero h1 (ne_zero_of_eq_one hg4)
  obtain ⟨f, hf1, hf2, hf3⟩ : ∃ f, f.Monic ∧ (f.natDegree = 1 ∨ f.natDegree = 2) ∧ f ∣ g := by
    have := IsAlgClosure.isAlgClosed F (K := K)
    have hg0 : g.natDegree ≠ 0 := by simp_all
    obtain ⟨f, h1, h2, h3⟩ := divisor_by_finrank F K (degree_ne_of_natDegree_ne hg0)
    use f
    rw [h] at h2
    exact ⟨h1, (Nat.dvd_prime Nat.prime_two).mp h2, h3⟩
  cases hf2 with
  | inl hf2 =>
    obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_succ 0)).mpr hf2)
    have := IsRoot.dvd hx hf3
    right
    use x^2 - a
    simp_all [g, g1, g2, g3]
    grind
  | inr hf2 =>
    obtain ⟨e, h_ftimese⟩ := exists_eq_mul_left_of_dvd hf3
    have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 := by
      have := coeff_natDegree (p := f)
      have := natDegree_le_iff_coeff_eq_zero (n := 2) (p := f)
      simp_all
    have : e.coeff 2 = 1 ∧ e.coeff 3 = 0 ∧ e.coeff 4 = 0 := by
      have : e ≠ 0 := by aesop
      have := Monic.natDegree_mul' hf1 this
      rw [Monic.natDegree_mul_comm hf1, ←h_ftimese, h_gdeg, hf2] at this
      have : e.natDegree = 2 := by linarith
      have := natDegree_le_iff_coeff_eq_zero.mp (Nat.le_of_eq this)
      have : e.coeff e.natDegree = 1 := by
        rw [coeff_natDegree, ←leadingCoeff_mul_monic hf1, ←h_ftimese, Monic.def.mp h_gmon]
      grind
    have : e.coeff 0 * f.coeff 0 = a^2 + b ∧ e.coeff 0 * f.coeff 1 + e.coeff 1 * f.coeff 0 = 0 := by
      rw [←hg0, ←hg1, h_ftimese]
      exact ⟨(mul_coeff_zero e f).symm, (mul_coeff_one e f).symm⟩
    have : f.coeff 0 + e.coeff 1 * f.coeff 1 + e.coeff 0 = -2*a ∧ e.coeff 1 + f.coeff 1 = 0 := by
      have := coeff_mul e f 2
      have := coeff_mul e f 3
      simp [Finset.antidiagonal] at *
      grind only
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
