module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.AlgebraicClosure
public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]

lemma pol_splits (f : F[X]) : (map (algebraMap F K) f).Splits :=
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F; IsAlgClosed.splits (map (algebraMap F K) f)

lemma divisor_by_finrank {f : F[X]} {p : ℕ} (hr : finrank F K = p) (hp : Nat.Prime p) (hf : 0 <
    f.natDegree) : (∃ x, f.IsRoot x) ∨ ∃ d, d.IsMonicOfDegree p ∧ d ∣ f := by
  have ⟨c, hc1, hc2, hc3⟩ := exists_monic_irreducible_factor f (not_isUnit_of_natDegree_pos f hf)
  have hd := Irreducible.natDegree_dvd_finrank hc2 (pol_splits F K c)
  rw [hr] at hd; rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with h | h
  · left; have h := (degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).mpr h
    have ⟨x, hx⟩ := exists_root_of_degree_eq_one h; exact ⟨x, IsRoot.dvd hx hc3⟩
  · right; exact ⟨c, ⟨h, hc1⟩, hc3⟩

lemma quadratic_algebraic_closure (hr2 : finrank F K = 2) (a b : F) :
    IsSquare (a*a+b) ∨ IsSquare (-b) := by
  let g := monomial 4 1 + monomial 2 (-2 * a) + monomial 0 (a^2 + b)
  have h1 : g.IsMonicOfDegree 4 := by dsimp [g]; exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank F K hr2 Nat.prime_two (f := g) (by grind [h1.1]) with
    ⟨x, hx⟩ | ⟨f, hf2, ⟨e, he⟩⟩
  · right; use x^2 - a; simp only [IsRoot.def, eval_add, eval_monomial, g] at hx; grind only
  · let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀*e₀ = a^2 + b ∧ 0 = f₀*e₁ + f₁*e₀ ∧ -2*a = f₀ + f₁*e₁ + e₀ ∧ 0 = f₁ + e₁ := by
      have hm := coeff_mul f e; rw [←he] at hm; rw [he] at h1
      have hm' := And.intro (hm 0).symm (And.intro (hm 1) (And.intro (hm 2) (hm 3)))
      simp only [g, coeff_add, coeff_monomial, Finset.antidiagonal] at hm'
      have h : ∀ {t : F[X]}, IsMonicOfDegree t 2 → t.coeff 2 = 1 ∧ t.coeff 3 = 0 := by
        intro t ⟨ht1, ht2⟩; rw [←ht1, ←ht2]; simp [natDegree_le_iff_coeff_eq_zero.mp ht1.le 3]
      simp [h hf2, h (IsMonicOfDegree.of_mul_left hf2 h1)] at hm'; ring_nf at hm' ⊢; exact hm'
    clear h1 g he; by_cases f₁ = 0
    · right; use f₀ + a; grind only
    · left; use f₀; grind only

lemma finite_algebraic_closure_cyclic_prime {p : ℕ} [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : ¬CharP F p := by
  open IntermediateField IsAlgClosed Nat Polynomial Subfield in
  have hp1 := Prime.pos hp; have hp1' := Prime.one_lt hp; have := fact_iff.mpr hp
  by_contra
  have ⟨a, x, ha⟩ := cyclic_char_p_as_param F K hp hrank
  have h_deg := (artinSchreierPoly_isMonicOfDegree a hp1').1; rw [←ha] at h_deg
  have h_int := Algebra.IsIntegral.isIntegral x (R := F); let pb := adjoin.powerBasis h_int
  have ⟨y, hy⟩ : ∃ y : F⟮x⟯, ↑y^p = ↑y + ((algebraMap F K) a) * x^(p-1) := by
    have : IsAlgClosed F⟮x⟯ := by
      have := FiniteDimensional.of_finrank_pos (by rw [hrank]; exact hp1)
      have h1 := (topEquiv (F := F) (E := K)).symm
      have := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_deg; rw [←hrank] at this
      rw [←(Field.primitive_element_iff_minpoly_degree_eq F x).mpr this] at h1
      have := IsAlgClosure.isAlgClosed F (K := K); exact of_ringEquiv K ↥F⟮x⟯ h1
    let t := a * pb.gen ^ (p-1)
    have := (artinSchreierPoly_isMonicOfDegree t hp1').1.trans_ne hp1.ne'
    have ⟨y, hy⟩ := exists_aeval_eq_zero F⟮x⟯ _ (degree_ne_of_natDegree_ne this)
    rw [artinSchreierPoly_aeval, sub_sub, sub_eq_zero] at hy
    use y; rw [←IntermediateField.coe_pow]; aesop
  obtain ⟨y_rep, h_pb1, rfl⟩ := PowerBasis.exists_eq_aeval pb y
  let c := y_rep.coeff (p-1); have : c^p = c + a := by
    have h : aeval x y_rep = aeval pb.gen y_rep := (by aesop); rw [←h] at hy
    let m := map (frobenius F p) y_rep; have hd := (natDegree_taylor m a).trans (natDegree_map _)
    rw [adjoin.powerBasis_dim h_int, h_deg] at h_pb1
    have h : m.taylor a = y_rep + monomial (p-1) a := by
      have hx := minpoly.aeval F x; rw [ha, artinSchreierPoly_aeval, sub_sub, sub_eq_zero] at hx
      have hdiv := calc
        aeval x (m.taylor a) = aeval x (expand F p m) := by simp [taylor_apply, aeval_comp, hx]
        _ = aeval x (y_rep + monomial (p-1) a) := by simp [m, ←map_expand, map_frobenius_expand, hy]
      rw [←sub_eq_zero, ←aeval_sub] at hdiv; have h := minpoly.dvd_iff.mpr hdiv
      refine sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt h ?_)
      grind only [!natDegree_add_le, !natDegree_sub_le, !natDegree_monomial_le, =max_def]
    have h1 : (m.taylor a).coeff (p-1) = c^p := by
      by_cases hf0 : y_rep.natDegree = p-1
      · rw [←hf0, ←hd, ←leadingCoeff, leadingCoeff_taylor, leadingCoeff_map, leadingCoeff]; aesop
      · subst c; (repeat' rw [coeff_eq_zero_of_natDegree_lt]); rw [zero_pow]; repeat grind only
    rw [←h1, h, coeff_add, coeff_monomial_same]
  have hirr := minpoly.irreducible h_int; rw [←h_deg] at hp1'
  have := Irreducible.not_isRoot_of_natDegree_ne_one hirr hp1'.ne' (x := c); simp_all
