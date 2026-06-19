module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma divisor_by_finrank {f : F[X]} (hf : f.degree ≠ 0) : ∃ d : F[X], d.Monic ∧
  d.natDegree ∣ finrank F K ∧ d ∣ f := by
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
  have : ∀ n, g1.coeff n = (if 4 = n then 1 else 0) ∧ g2.coeff n = (if 2 = n then (-2*a) else 0) ∧
    g3.coeff n = (if 0 = n then (a^2+b) else 0) := by grind [coeff_monomial]
  let g := g1 + g2 + g3
  obtain ⟨hg0, hg1, hg2, hg3, hg4⟩ : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧
    g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0 ∧ g.coeff 4 = 1 := by simp_all [g]
  have hg5 : ∀ n, n > 4 → g.coeff n = 0 := by aesop
  have h1 := natDegree_le_iff_coeff_eq_zero.mpr hg5
  have h_gdeg := natDegree_eq_of_le_of_coeff_ne_zero h1 (ne_zero_of_eq_one hg4)
  obtain ⟨f, hf1, hf2, hf3⟩ : ∃ f, f.Monic ∧ (f.natDegree = 1 ∨ f.natDegree = 2) ∧ f ∣ g := by
    have : g.natDegree ≠ 0 := by simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    obtain ⟨f, h1, h2, h3⟩ := divisor_by_finrank F K (degree_ne_of_natDegree_ne this)
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
    have h1 : g.IsMonicOfDegree 4 := { natDegree_eq := h_gdeg, monic :=
      monic_of_natDegree_le_of_coeff_eq_one 4 h1 hg4 }
    rw [h_ftimese] at hg0 h1
    have := coeff_natDegree (p := f)
    have := natDegree_le_iff_coeff_eq_zero (n := 2) (p := f)
    have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 := by simp_all
    obtain ⟨h3a, h3b⟩ := IsMonicOfDegree.of_mul_right { natDegree_eq := hf2, monic := hf1 } h1
    have := Monic.def.mp h3b
    rw [←coeff_natDegree, h3a] at this
    have := natDegree_le_iff_coeff_eq_zero.mp (le_of_eq h3a) 3 (Nat.lt_succ_self 2)
    have := coeff_mul e f 1
    have := coeff_mul e f 2
    have := coeff_mul e f 3
    simp [Finset.antidiagonal] at *
    if f.coeff 1 = 0 then
      right
      use f.coeff 0 + a
      simp_all only
      grind => ring
    else
      left
      use f.coeff 0
      grind => ring
