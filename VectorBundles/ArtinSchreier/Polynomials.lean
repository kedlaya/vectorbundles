module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

lemma monomial_coeffs {F : Type} [Field F] (n : ℕ) (c : F) :
  (Polynomial.monomial n c).coeff n = c ∧ ∀ (m : ℕ), m ≠ n → (Polynomial.monomial n c).coeff m = 0 := by
  constructor
  exact Polynomial.coeff_monomial_same n c
  intro m hm
  exact Polynomial.coeff_monomial_of_ne c hm

lemma polynomial_monic_divisor {F : Type} [Field F] {f : Polynomial F} {g: Polynomial F}
  (h1 : f.Monic) (h2 : g.Monic) (h3 : f ∣ g):
  ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
  ∧ e.degree = e.natDegree := by
  let e := g /ₘ f
  use e
  have h_ftimese : e * f = g := by
    have h4 : g %ₘ f + f * (g /ₘ f) = g :=
      Polynomial.modByMonic_add_div g f
    have h5 : g %ₘ f = 0 := by
      exact (Polynomial.modByMonic_eq_zero_iff_dvd h1).mpr h3
    subst e
    grind
  constructor
  exact h_ftimese
  have h6 : e.Monic := by
    have h7 : e.leadingCoeff = g.leadingCoeff := by
      refine Polynomial.leadingCoeff_divByMonic_of_monic h1 ?_
      apply Polynomial.degree_le_of_dvd h3
      exact Polynomial.Monic.ne_zero h2
    refine Polynomial.Monic.def.mpr ?_
    simp_all
  constructor
  exact h6
  constructor
  have _ : (e * f).natDegree = e.natDegree + f.natDegree := by
    exact Polynomial.Monic.natDegree_mul h6 h1
  simp_all
  refine Polynomial.degree_eq_natDegree ?_
  exact Polynomial.Monic.ne_zero h6

lemma monic_divisor_of_same_degree {F : Type} [Field F] (f g : Polynomial F)
  (h1: f.Monic) (h2 : g.Monic) (hdiv: f ∣ g) (hdeg: f.natDegree = g.natDegree) : f = g := by
  have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
  ∧ e.degree = e.natDegree :=
    polynomial_monic_divisor h1 h2 hdiv
  obtain ⟨res, _, h_resmonic, _, _⟩ := h_e
  have h_resdeg : res.natDegree = 0 := by
    have _ : (res * f).natDegree = res.natDegree + f.natDegree := by
      exact Polynomial.Monic.natDegree_mul h_resmonic h1
    grind
  have _ : res = Polynomial.C 1 := by
    have _ : res.natDegree = 0 ↔ ∃ x : F, Polynomial.C x = res := by
      apply Polynomial.natDegree_eq_zero
    simp
    exact (Polynomial.Monic.natDegree_eq_zero h_resmonic).mp h_resdeg
  simp_all

lemma divisor_of_irreducible_poly {F : Type} [Field F] (f g : Polynomial F)
  (hdiv: f ∣ g) (hirr: Irreducible g) : f.natDegree = 0 ∨ f.natDegree = g.natDegree := by
  let f0 := f * Polynomial.C (1 / f.leadingCoeff)
  let g0 := g * Polynomial.C (1 / g.leadingCoeff)
  have _ : g ≠ 0 := by
    exact Irreducible.ne_zero hirr
  have h_gmon : g0.Monic := by
    refine Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    have _ : g.leadingCoeff ≠ 0 := by
      (expose_names; exact Polynomial.leadingCoeff_ne_zero.mpr h)
    simp_all
  have _ : f ≠ 0 := by
    (expose_names; exact ne_zero_of_dvd_ne_zero h hdiv)
  have h_fmon : f0.Monic := by
    refine Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    have _ : f.leadingCoeff ≠ 0 := by
      (expose_names; exact Polynomial.leadingCoeff_ne_zero.mpr h_1)
    simp_all
  have h_div : f0 ∣ g0 := by
    refine mul_dvd_mul hdiv ?_
    simp_all
  have _ : f0.natDegree = f.natDegree := by
    apply Polynomial.natDegree_mul_C
    simp_all
  have _ : g0.natDegree = g.natDegree := by
    apply Polynomial.natDegree_mul_C
    simp_all
  have h_e:  ∃ (e : Polynomial F), e * f0 = g0 ∧ e.Monic ∧ e.natDegree + f0.natDegree = g0.natDegree
  ∧ e.degree = e.natDegree :=
    polynomial_monic_divisor h_fmon h_gmon h_div
  obtain ⟨e, _, h_resmonic, h_degs, _⟩ := h_e
  have _ : Irreducible g0 := by
    subst g0
    have _ : IsUnit (Polynomial.C (1 / g.leadingCoeff)) := by
      refine Polynomial.isUnit_C.mpr ?_
      simp_all
    (expose_names; exact (irreducible_mul_isUnit h_4).mpr hirr)
  have h_isunit : IsUnit e ∨ IsUnit f0 := by
    (expose_names; exact h_4.isUnit_or_isUnit (id (Eq.symm left)))
  cases h_isunit
  · right
    have h_edeg : e.natDegree = 0 := by
      (expose_names; exact Polynomial.natDegree_eq_zero_of_isUnit h_5)
    simp_all
  · left
    have _ : f0.natDegree = 0 := by
      (expose_names; exact Polynomial.natDegree_eq_zero_of_isUnit h_5)
    simp_all

lemma odd_irreducible_factor {F : Type} [Field F] (f : Polynomial F)
  (h : Odd f.natDegree) : ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
    have _ : f ≠ 0 := by
      unfold Odd at h
      obtain ⟨k, _⟩ := h
      have t : f.natDegree > 0 := by
        grind
      exact Polynomial.ne_zero_of_natDegree_gt t
    let S := UniqueFactorizationMonoid.factors f
    have h_prod : Associated S.prod f := by
      (expose_names; exact UniqueFactorizationMonoid.factors_prod h_1)
    have _ : 0 ∉ S := by
      by_contra
      have hS : S.prod = 0 := by
        exact Multiset.prod_eq_zero this
      have _ : Associated 0 f := by
        simp_all
      have _ : Associated f 0 := by
        grind [Associated.symm]
      have _ : Associated f 0 ↔ f = 0 :=
        associated_zero_iff_eq_zero f
      grind
    have _ : S.prod.degree = f.degree := by
      exact Polynomial.degree_eq_degree_of_associated h_prod
    have _ : S.prod.natDegree = f.natDegree := by
      (expose_names; exact Polynomial.natDegree_eq_of_degree_eq h_3)
    have _ : Odd S.prod.natDegree := by
      grind
    have hg : ∃ g ∈ S, Odd g.natDegree := by
      by_contra
      let T := S.map Polynomial.natDegree
      have _ : S.prod.natDegree = T.sum := by
        apply Polynomial.natDegree_multiset_prod
        grind
      have h_even : ∀ g ∈ S, Even g.natDegree := by
        grind
      have ht : ∀ t : ℕ, t ∈ T → Even t := by
        by_contra
        push Not at this
        obtain ⟨t, ht1, ht2⟩ := this
        unfold Multiset.map at T
        have hg : ∃ g ∈ S, g.natDegree = t := by
          exact Multiset.mem_map.mp ht1
        obtain ⟨g, hg⟩ := hg
        grind
      have _ : 2 ∣ T.sum := by
        apply Multiset.dvd_sum
        unfold Even at ht
        intro x hx
        specialize ht x
        simp_all
        obtain ⟨r, ht⟩ := ht
        have _ : x = 2*r := by
          grind
        (expose_names; exact dvd_of_mul_right_eq r (id (Eq.symm h_6)))
      grind
    obtain ⟨g, hg1, hg2⟩ := hg
    use g
    constructor
    · unfold S at hg1
      exact UniqueFactorizationMonoid.irreducible_of_factor g hg1
    constructor
    · exact UniqueFactorizationMonoid.dvd_of_mem_factors hg1
    apply hg2
