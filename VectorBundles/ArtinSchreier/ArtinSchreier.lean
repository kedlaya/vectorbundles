module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

/- If a field admits a Galois extension of prime degree p which is algebraically closed, then
   its characteristic cannot equal p. -/
lemma finite_algebraic_closure_cyclic_prime {p : ℕ} [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : ¬CharP F p := by
  by_contra; open IntermediateField IsAlgClosed Nat Polynomial in
  have hp1 := Prime.pos hp; have hp1' := Prime.one_lt hp; have := fact_iff.mpr hp
  have h_a (E : Type) [Field E] (x : E) := (artinSchreierPoly_isMonicOfDegree x hp1').1
  have ⟨a, x, ha⟩ := cyclic_char_p_as_param F K hp hrank; have h_deg := h_a F a
  let t := (algebraMap F K) a * x^(p-1); have ⟨y, hy⟩ : ∃ y, y^p = y + t := by
    have := IsAlgClosure.isAlgClosed F (K := K); have h := (h_a K t).trans_ne hp1.ne'
    have ⟨y, hy⟩ := exists_aeval_eq_zero K _ (degree_ne_of_natDegree_ne h)
    rw [artinSchreierPoly_aeval, sub_sub, sub_eq_zero] at hy; exact ⟨y, hy⟩
  subst t; rw [←ha] at h_deg; obtain ⟨y₀, h₀⟩ : ∃ y₀ : F⟮x⟯, y₀ = y := by
    subst hrank; have := FiniteDimensional.of_finrank_pos hp1
    rw [(Field.primitive_element_iff_minpoly_natDegree_eq F x).mpr h_deg]
    exact CanLift.prf y (Subfield.mem_top y)
  have h_int := Algebra.IsIntegral.isIntegral x (R := F)
  obtain ⟨f, h_pb, rfl⟩ := PowerBasis.exists_eq_aeval (adjoin.powerBasis h_int) y₀
  let c := f.coeff (p-1); have : c^p = c + a := by
    rw [adjoin.powerBasis_dim h_int, h_deg] at h_pb; let m := f.map (frobenius F p)
    have h : m.taylor a = f + monomial (p-1) a := by
      have hx := minpoly.aeval F x; rw [ha, artinSchreierPoly_aeval, sub_sub, sub_eq_zero] at hx
      have h : aeval x f = y := (by rw [←h₀, ←aeval_coe]; rfl); rw [←h, ←map_pow] at hy
      refine sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt (minpoly.dvd_iff (x := x).mpr ?_) ?_)
      · rw [aeval_sub, sub_eq_zero,  aeval_add, aeval_monomial, ←hy, ←map_frobenius_expand,
          map_expand, expand_aeval,  taylor_apply, aeval_comp, aeval_add, aeval_X, aeval_C, ←hx]
      · rw [h_deg]; compute_degree!; rw [natDegree_map]; exact ⟨h_pb, h_pb, hp1⟩
    have h1 : (m.taylor a).coeff (p-1) = c^p := by
      have h := (natDegree_taylor m a).trans (natDegree_map _); by_cases h0 : f.natDegree = p-1
      · rw [←h0, ←h, ←leadingCoeff, leadingCoeff_taylor, leadingCoeff_map, leadingCoeff, h0]; rfl
      · subst c; (repeat rw [coeff_eq_zero_of_natDegree_lt]); rw [zero_pow]; repeat grind only
    rw [←h1, h, coeff_add, coeff_monomial_same]
  have hirr := minpoly.irreducible h_int; rw [←h_deg] at hp1'
  have := Irreducible.not_isRoot_of_natDegree_ne_one hirr hp1'.ne' (x := c); simp_all

/- Given a polynomial over a field, its base change to an algebraic closure splits. -/
lemma pol_splits (f : F[X]) : (map (algebraMap F K) f).Splits :=
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F; IsAlgClosed.splits (map (algebraMap F K) f)

/- If a field admits an algebraically closed extension of finite prime degree p, then a polynomial
   over this field of positive degree has either a root or an irreducible divisor of degree p. -/
lemma divisor_by_finrank {f : F[X]} {p : ℕ} (hr : finrank F K = p) (hp : Nat.Prime p) (hf : 0 <
    f.natDegree) : (∃ x, f.IsRoot x) ∨ ∃ d, d.IsMonicOfDegree p ∧ Irreducible d ∧ d ∣ f := by
  have ⟨c, hc1, hc2, hc3⟩ := exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hf)
  have hd := Irreducible.natDegree_dvd_finrank hc2 (pol_splits F K c); rw [hr] at hd
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with h | h
  · left; have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h; exact ⟨x, IsRoot.dvd hx hc3⟩
  · right; exact ⟨c, ⟨h, hc1⟩, hc2, hc3⟩

/- If a and b belong to a field which admits an algebraically closed quadratic extension,
   then one of a^2+b or -b is a square. -/
lemma quadratic_algebraic_closure (h : finrank F K = 2) (a b : F) :
    IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g := monomial 4 1 + monomial 2 (-2 * a) + monomial 0 (a^2 + b); let h2 := Nat.prime_two
  have h1 : g.IsMonicOfDegree 4 := by subst g; exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank F K h h2 (f := g) (by grind [h1.1]) with ⟨x, hx⟩ | ⟨f, hf, _, ⟨e, he⟩⟩
  · right; use x^2 - a; simp only [IsRoot.def, g, eval_add, eval_monomial] at hx; grind only
  · let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀*e₀ = a^2 + b ∧ 0 = f₀*e₁ + f₁*e₀ ∧ -2*a = f₀ + f₁*e₁ + e₀ ∧ 0 = f₁ + e₁ := by
      have hm := coeff_mul f e; rw [←he] at hm; rw [he] at h1
      have hm' := And.intro (hm 0).symm (And.intro (hm 1) (And.intro (hm 2) (hm 3)))
      simp only [g, coeff_add, coeff_monomial, Finset.antidiagonal] at hm'
      have h : ∀ {t : F[X]}, IsMonicOfDegree t 2 → t.coeff 2 = 1 ∧ t.coeff 3 = 0 := by
        intro t ⟨ht1, ht2⟩; rw [←ht1]; simp [ht2, natDegree_le_iff_coeff_eq_zero.mp ht1.le 3]
      simp [h hf, h (IsMonicOfDegree.of_mul_left hf h1)] at hm'; ring_nf at hm' ⊢; exact hm'
    clear h1 g he; by_cases f₁ = 0; right; use f₀ + a; grind only; left; use f₀; grind only
