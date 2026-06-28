module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma pol_splits (p : F[X]) : (map (algebraMap F K) p).Splits :=
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F; IsAlgClosed.splits (map (algebraMap F K) p)

lemma divisor_by_finrank {f : F[X]} {p : ℕ} (hr : finrank F K = p) (hp : Nat.Prime p) (hf : 0 <
    f.natDegree) : (∃ x, f.IsRoot x) ∨ ∃ d, d.IsMonicOfDegree p ∧ d ∣ f := by
  have ⟨c, hc1, hc2, hc3⟩ := exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hf)
  have hd := Irreducible.natDegree_dvd_finrank hc2 (pol_splits F K c)
  rw [hr] at hd; rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with h | h
  · have := (degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).mpr h
    have ⟨x, hx⟩ := exists_root_of_degree_eq_one this; left; exact ⟨x, IsRoot.dvd hx hc3⟩
  · right; exact ⟨c, ⟨h, hc1⟩, hc3⟩

lemma quadratic_algebraic_closure (h : finrank F K = 2) (a b : F) :
    IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g := monomial 4 1 + monomial 2 (-2 * a) + monomial 0 (a^2 + b)
  have h1 : g.IsMonicOfDegree 4 := by dsimp [g]; exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank F K h Nat.prime_two (f := g) (by grind [h1.1])
    with ⟨x, hx⟩ | ⟨f, hf2, ⟨e, he⟩⟩
  · right; use x^2 - a; simp only [IsRoot.def, eval_add, eval_monomial, g] at hx; grind only
  · let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀*e₀ = a^2 + b ∧ 0 = f₀*e₁ + f₁*e₀ ∧ -2*a = f₀ + (f₁*e₁ + e₀) ∧ 0 = f₁ + e₁ := by
      have hm := coeff_mul f e; rw [←he] at hm; rw [he] at h1
      have hm' := And.intro (hm 0).symm (And.intro (hm 1) (And.intro (hm 2) (hm 3)))
      simp only [g, coeff_add, coeff_monomial, Finset.antidiagonal] at hm'
      have h : ∀ {t : F[X]}, IsMonicOfDegree t 2 → t.coeff 2 = 1 ∧ t.coeff 3 = 0 := by
        intro t ⟨ht1, ht2⟩; rw [←ht1, ←ht2]; simp [natDegree_le_iff_coeff_eq_zero.mp ht1.le]
      simp [h hf2, h (IsMonicOfDegree.of_mul_left hf2 h1)] at hm'; ring_nf at hm' ⊢; exact hm'
    clear h1 g he; by_cases f₁ = 0
    · right; use f₀ + a; grind only
    · left; use f₀; grind only
