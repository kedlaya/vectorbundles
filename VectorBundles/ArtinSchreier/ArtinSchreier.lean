module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma pol_splits (p : F[X]) : (map (algebraMap F K) p).Splits :=
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F; IsAlgClosed.splits (map (algebraMap F K) p)

lemma divisor_by_finrank {f : F[X]} {p : ℕ} (hr : finrank F K = p) (hp : Nat.Prime p) (hf : 0 <
  f.natDegree) : (∃ x : F, f.IsRoot x) ∨ ∃ d : F[X], d.Monic ∧ d.natDegree = p ∧ d ∣ f := by
  have ⟨c, hc1, hc2, hc3⟩ := exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hf)
  have hd := Irreducible.natDegree_dvd_finrank hc2 (pol_splits F K c)
  rw [hr] at hd; cases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with
  | inl h =>
    have := (degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).mpr h
    have ⟨x, hx⟩ := exists_root_of_degree_eq_one this
    left; exact ⟨x, IsRoot.dvd hx hc3⟩
  | inr h => right; exact ⟨c, hc1, h, hc3⟩

lemma quadratic_algebraic_closure (h : finrank F K = 2) (a b : F) :
  IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g1 := monomial 4 (1 : F); let g2 := monomial 2 (-2*a); let g3 := monomial 0 (a^2+b)
  have : ∀ n, g1.coeff n = (if 4 = n then 1 else 0) ∧ g2.coeff n = (if 2 = n then (-2*a) else 0)
    ∧ g3.coeff n = (if 0 = n then (a^2+b) else 0) := by grind [coeff_monomial]
  let g := g1 + g2 + g3
  have ⟨hg0, _, hg2, _, hg4⟩ : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧
    g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0 ∧ g.coeff 4 = 1 := by simp_all [g]
  have hg5 : ∀ n, n > 4 → g.coeff n = 0 := by aesop
  have h_gdeg : g.natDegree = 4 := by dsimp [g, g1, g2, g3]; compute_degree!
  rcases divisor_by_finrank F K h Nat.prime_two (f := g) (by grind)
    with ⟨x, hx⟩ | ⟨f, hf1, hf2, hf3⟩
  · simp_all only [IsRoot.def, eval_add, eval_monomial, g1, g2, g3, g]
    right; use x^2 - a; grind only
  · have ⟨e, h_ftimese⟩ := exists_eq_mul_left_of_dvd hf3
    have h1 : g.IsMonicOfDegree 4 := { natDegree_eq := h_gdeg, monic :=
      monic_of_natDegree_le_of_coeff_eq_one 4 h_gdeg.le hg4 }
    rw [h_ftimese] at hg0 h1
    have := coeff_natDegree (p := f)
    have := natDegree_le_iff_coeff_eq_zero (n := 2) (p := f)
    have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 := by simp_all
    have ⟨h3a, h3b⟩ := IsMonicOfDegree.of_mul_right { natDegree_eq := hf2, monic := hf1 } h1
    have := coeff_natDegree (p := e); rw [h3b.leadingCoeff, h3a] at this
    have h1 := coeff_mul e f 1; have h2 := coeff_mul e f 2; have h3 := coeff_mul e f 3
    by_cases f.coeff 1 = 0
    · right; use f.coeff 0 + a; simp [Finset.antidiagonal] at *; simp_all; grind => ring
    · left
      have := natDegree_le_iff_coeff_eq_zero.mp h3a.le 3 (by simp)
      use f.coeff 0; simp [Finset.antidiagonal] at *; grind => ring
