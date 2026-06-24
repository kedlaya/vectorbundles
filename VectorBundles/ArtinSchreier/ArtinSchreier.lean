module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma pol_splits (p : F[X]) : (map (algebraMap F K) p).Splits :=
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F; IsAlgClosed.splits (map (algebraMap F K) p)

lemma divisor_by_finrank {f : F[X]} {p : ℕ} (hr : finrank F K = p) (hp : Nat.Prime p) (hf : 0 <
  f.natDegree) : (∃ x : F, f.IsRoot x) ∨ ∃ d : F[X], d.IsMonicOfDegree p ∧ d ∣ f := by
  have ⟨c, hc1, hc2, hc3⟩ := exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hf)
  have hd := Irreducible.natDegree_dvd_finrank hc2 (pol_splits F K c)
  rw [hr] at hd; cases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with
  | inl h =>
    have := (degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).mpr h
    have ⟨x, hx⟩ := exists_root_of_degree_eq_one this
    left; exact ⟨x, IsRoot.dvd hx hc3⟩
  | inr h => right; exact ⟨c, ⟨h, hc1⟩, hc3⟩

lemma quadratic_algebraic_closure (h : finrank F K = 2) (a b : F) :
    IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g := monomial 4 1 + monomial 2 (-2 * a) + monomial 0 (a^2 + b)
  have h1 : g.IsMonicOfDegree 4 := by dsimp [g]; exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank F K h Nat.prime_two (f := g) (by grind [h1.1])
    with ⟨x, hx⟩ | ⟨f, ⟨hf2, hf1⟩, ⟨e, he⟩⟩
  · simp only [IsRoot.def, eval_add, eval_monomial, g] at hx
    right; use x^2 - a; grind only
  · rw [he] at h1
    have ⟨he2, he1⟩ : e.IsMonicOfDegree 2 := IsMonicOfDegree.of_mul_left ⟨hf2, hf1⟩ h1
    let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀ * e₀ = a^2 + b ∧ 0 = f₀*e₁ + f₁*e₀ ∧ -2*a = f₀ + (f₁*e₁ + e₀) ∧
        0 = f₁ + e₁ := by
      have hf₂ : f.coeff 2 = 1 := by rw [←hf2, ←hf1.leadingCoeff, coeff_natDegree]
      have he₂ : e.coeff 2 = 1 := by rw [←he2, ←he1.leadingCoeff, coeff_natDegree]
      have he₃ : e.coeff 3 = 0 := by grind [natDegree_le_iff_coeff_eq_zero.mp he2.le]
      have hf₃ : f.coeff 3 = 0 := by grind [natDegree_le_iff_coeff_eq_zero.mp hf2.le]
      have hm := coeff_mul f e; rw [←he] at hm
      have hm₀ := (hm 0).symm; have hm₁ := hm 1; have hm₂ := hm 2; have hm₃ := hm 3
      simp only [g, coeff_add, coeff_monomial, Finset.antidiagonal] at hm₀ hm₁ hm₂ hm₃
      simp [hf₂, he₂, he₃, hf₃] at hm₀ hm₁ hm₂ hm₃ ⊢
      ring_nf at hm₀ hm₁ hm₂ hm₃ ⊢; exact ⟨hm₀, hm₁, hm₂, hm₃⟩
    by_cases f.coeff 1 = 0
    · right; use f.coeff 0 + a; clear he; grind only
    · left; use f.coeff 0; grind only
