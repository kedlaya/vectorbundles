module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma pol_splits (p : F[X]) : (map (algebraMap F K) p).Splits :=
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  IsAlgClosed.splits (map (algebraMap F K) p)

lemma divisor_by_finrank {f : F[X]} (hf : 0 < f.natDegree) : ∃ d : F[X], d.Monic ∧
  d.natDegree ∣ finrank F K ∧ d ∣ f :=
  have ⟨c, hc1, hc2, hc3⟩ := exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hf)
  ⟨c, hc1, Irreducible.natDegree_dvd_finrank hc2 (pol_splits F K c), hc3⟩

lemma quadratic_algebraic_closure (h : finrank F K = 2) (a b : F) :
  IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g1 := monomial 4 (1 : F); let g2 := monomial 2 (-2*a); let g3 := monomial 0 (a^2+b)
  have : ∀ n, g1.coeff n = (if 4 = n then 1 else 0) ∧ g2.coeff n = (if 2 = n then (-2*a) else 0) ∧
    g3.coeff n = (if 0 = n then (a^2+b) else 0) := by grind [coeff_monomial]
  let g := g1 + g2 + g3
  have ⟨hg0, hg1, hg2, hg3, hg4⟩ : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧
    g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0 ∧ g.coeff 4 = 1 := by simp_all [g]
  have hg5 : ∀ n, n > 4 → g.coeff n = 0 := by aesop
  have h1 := natDegree_le_iff_coeff_eq_zero.mpr hg5
  have h_gdeg := natDegree_eq_of_le_of_coeff_ne_zero h1 (ne_zero_of_eq_one hg4)
  have ⟨f, hf1, h2, hf3⟩ := divisor_by_finrank F K (Nat.lt_of_sub_eq_sub_one h_gdeg)
  rw [h] at h2
  cases (Nat.dvd_prime Nat.prime_two).mp h2 with
  | inl hf2 =>
    have ⟨x, hx⟩ := exists_root_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_succ 0)).mpr hf2)
    have := IsRoot.dvd hx hf3
    right
    simp_all only [IsRoot.def, eval_add, eval_monomial, g1, g2, g3, g]
    use x^2 - a
    grind
  | inr hf2 =>
    have ⟨e, h_ftimese⟩ := exists_eq_mul_left_of_dvd hf3
    have h1 : g.IsMonicOfDegree 4 := { natDegree_eq := h_gdeg, monic :=
      monic_of_natDegree_le_of_coeff_eq_one 4 h1 hg4 }
    rw [h_ftimese] at hg0 h1
    have := coeff_natDegree (p := f)
    have := natDegree_le_iff_coeff_eq_zero (n := 2) (p := f)
    have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 := by simp_all
    have ⟨h3a, h3b⟩ := IsMonicOfDegree.of_mul_right { natDegree_eq := hf2, monic := hf1 } h1
    have := (congr_arg e.coeff h3a.symm).trans (Monic.coeff_natDegree h3b)
    have := coeff_mul e f 1; have := coeff_mul e f 2; have := coeff_mul e f 3
    simp [Finset.antidiagonal] at *
    by_cases f.coeff 1 = 0
    · right
      use f.coeff 0 + a
      simp_all only
      grind => ring
    · left
      use f.coeff 0
      have := natDegree_le_iff_coeff_eq_zero.mp (le_of_eq h3a) 3 (Nat.lt_succ_self 2)
      grind => ring
