module

public import Mathlib.Algebra.Polynomial.Splits

@[expose] public section

open Polynomial

lemma congruence_low_degree {F : Type} [Field F] {f g h : Polynomial F}
  (h1 : h ∣ (f-g)) (h2 : f.natDegree < h.natDegree) (h3 : g.natDegree < h.natDegree) (h4: h.Monic) :
    f = g := by
    by_cases h = 0
    · have _ : 0 ∣ (f-g) → f-g = 0 := by aesop
      simp_all
    rename_i h0
    have h5 : (f-g).natDegree < h.natDegree := by
      calc
        (f-g).natDegree ≤ max f.natDegree g.natDegree := by apply natDegree_sub_le
        _ < h.natDegree := by
          refine max_lt_iff.mpr ?_
          constructor
          exact h2
          exact h3
    have h6 : (f-g).degree < h.degree := by
      exact degree_lt_degree h5
    have _ : (f-g) /ₘ h = 0 := (divByMonic_eq_zero_iff h4).mpr h6
    have _ : (f-g) %ₘ h + h * ((f-g) /ₘ h) = f-g := modByMonic_add_div (f-g) h
    have _ : (f-g) %ₘ h = 0 := by
      exact (modByMonic_eq_zero_iff_dvd h4).mpr h1
    grind

lemma artin_schreier_poly {F : Type} [Field F] (p : ℕ) (c : F) (hp : Nat.Prime p):
  let pol := X ^ p + (- X - C c);
  pol.natDegree = p ∧ pol.Monic := by
    have h1 : (- X - C c).natDegree ≤ 1 := by
      refine (natDegree_sub_le_iff_right ?_).mpr ?_
      · refine natDegree_neg_le_of_le ?_
        exact natDegree_X_le
      · have h2 : (C c).natDegree = 0 := by
          exact natDegree_C c
        exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a_1 => a_1) h2 1
    have h3 : (- X - C c).natDegree < p := by
      calc
        (- X - C c).natDegree ≤ 1 := h1
        _ < p := by exact Nat.Prime.one_lt hp
    have h2   : ( X ^ p + (- X - C c)).natDegree ≤ p := by
      refine natDegree_add_le_of_degree_le ?_ ?_
      exact natDegree_X_pow_le p
      exact Nat.le_of_succ_le h3
    let pol := X ^ p + (- X - C c)
    have h4 : pol.coeff p = 1 := by
      have _ : (( X : Polynomial F)^ p ).coeff p = 1 := by
        exact coeff_X_pow_self p
      subst pol
      have _ : (- X - C c).coeff p = 0 := by
        refine coeff_eq_zero_of_natDegree_lt ?_
        exact Nat.lt_of_lt_of_eq h3 rfl
      simp_all

    constructor
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    exact String.Pos.Raw.mk_le_mk.mp h2
    exact ne_zero_of_eq_one h4
    exact monic_of_natDegree_le_of_coeff_eq_one p h2 h4

lemma monomial_coeffs {F : Type} [Field F] (n : ℕ) (c : F) :
  (monomial n c).coeff n = c ∧ ∀ (m : ℕ), m ≠ n → (monomial n c).coeff m = 0 := by
  constructor
  exact coeff_monomial_same n c
  intro m hm
  exact coeff_monomial_of_ne c hm

lemma polynomial_monic_divisor {F : Type} [Field F] {f : Polynomial F} {g: Polynomial F}
  (h1 : f.Monic) (h2 : g.Monic) (h3 : f ∣ g):
  ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
  ∧ e.degree = e.natDegree := by
  let e := g /ₘ f
  use e
  have h_ftimese : e * f = g := by
    have h4 : g %ₘ f + f * (g /ₘ f) = g :=
      modByMonic_add_div g f
    have h5 : g %ₘ f = 0 := by
      exact (modByMonic_eq_zero_iff_dvd h1).mpr h3
    subst e
    grind
  constructor
  exact h_ftimese
  have h6 : e.Monic := by
    have h7 : e.leadingCoeff = g.leadingCoeff := by
      refine leadingCoeff_divByMonic_of_monic h1 ?_
      apply degree_le_of_dvd h3
      exact Monic.ne_zero h2
    refine Monic.def.mpr ?_
    simp_all
  constructor
  exact h6
  constructor
  have _ : (e * f).natDegree = e.natDegree + f.natDegree := by
    exact Monic.natDegree_mul h6 h1
  simp_all
  refine degree_eq_natDegree ?_
  exact Monic.ne_zero h6

lemma monic_divisor_of_same_degree {F : Type} [Field F] (f g : Polynomial F)
  (h1: f.Monic) (h2 : g.Monic) (hdiv: f ∣ g) (hdeg: f.natDegree = g.natDegree) : f = g := by
  have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
  ∧ e.degree = e.natDegree :=
    polynomial_monic_divisor h1 h2 hdiv
  obtain ⟨res, _, h_resmonic, _, _⟩ := h_e
  have h_resdeg : res.natDegree = 0 := by
    have _ : (res * f).natDegree = res.natDegree + f.natDegree := by
      exact Monic.natDegree_mul h_resmonic h1
    grind
  have _ : res = C 1 := by
    have _ : res.natDegree = 0 ↔ ∃ x : F, C x = res := by
      apply natDegree_eq_zero
    simp
    exact (Monic.natDegree_eq_zero h_resmonic).mp h_resdeg
  simp_all

lemma divisor_of_irreducible_poly {F : Type} [Field F] (f g : Polynomial F)
  (hdiv: f ∣ g) (hirr: Irreducible g) : f.natDegree = 0 ∨ f.natDegree = g.natDegree := by
  let f0 := f * C (1 / f.leadingCoeff)
  let g0 := g * C (1 / g.leadingCoeff)
  have hg0 : g ≠ 0 := by
    exact Irreducible.ne_zero hirr
  have h_gmon : g0.Monic := by
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    have _ : g.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr hg0
    simp_all
  have hf0 : f ≠ 0 :=
    ne_zero_of_dvd_ne_zero hg0 hdiv
  have h_fmon : f0.Monic := by
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    have _ : f.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr hf0
    simp_all
  have h_div : f0 ∣ g0 := by
    refine mul_dvd_mul hdiv ?_
    simp_all
  have _ : f0.natDegree = f.natDegree := by
    apply natDegree_mul_C
    simp_all
  have _ : g0.natDegree = g.natDegree := by
    apply natDegree_mul_C
    simp_all
  have h_e:  ∃ (e : Polynomial F), e * f0 = g0 ∧ e.Monic ∧ e.natDegree + f0.natDegree = g0.natDegree
  ∧ e.degree = e.natDegree :=
    polynomial_monic_divisor h_fmon h_gmon h_div
  obtain ⟨e, _, h_resmonic, h_degs, _⟩ := h_e
  have _ : Irreducible g0 := by
    subst g0
    have h_unit : IsUnit (C (1 / g.leadingCoeff)) := by
      refine isUnit_C.mpr ?_
      simp_all
    exact (irreducible_mul_isUnit h_unit).mpr hirr
  have h_isunit : IsUnit e ∨ IsUnit f0 := by
    (expose_names; exact h_2.isUnit_or_isUnit (id (Eq.symm left)))
  cases h_isunit with
  | inl h_isunit =>
    have h_edeg : e.natDegree = 0 :=
      natDegree_eq_zero_of_isUnit h_isunit
    simp_all
  | inr h_isunit =>
    have _ : f0.natDegree = 0 :=
      natDegree_eq_zero_of_isUnit h_isunit
    simp_all

lemma odd_irreducible_factor {F : Type} [Field F] (f : Polynomial F)
  (h : Odd f.natDegree) : ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
    have hf0 : f ≠ 0 := by
      unfold Odd at h
      obtain ⟨k, _⟩ := h
      have t : f.natDegree > 0 := by
        grind
      exact ne_zero_of_natDegree_gt t
    let S := UniqueFactorizationMonoid.factors f
    have h_prod : Associated S.prod f :=
      UniqueFactorizationMonoid.factors_prod hf0
    have h0S : 0 ∉ S := by
      by_contra
      have hS : S.prod = 0 := by
        exact Multiset.prod_eq_zero this
      have _ : Associated 0 f := by
        rw [hS] at h_prod
        exact h_prod
      have _ : Associated f 0 := by
        grind [Associated.symm]
      have _ : Associated f 0 ↔ f = 0 :=
        associated_zero_iff_eq_zero f
      simp_all
    have _ : S.prod.natDegree = f.natDegree :=
      have h1 : S.prod.degree = f.degree := by
        exact degree_eq_degree_of_associated h_prod
      natDegree_eq_of_degree_eq h1
    have hg : ∃ g ∈ S, Odd g.natDegree := by
      have _ : Odd S.prod.natDegree := by
        grind
      by_contra
      push Not at this
      let T := S.map natDegree
      have _ : S.prod.natDegree = T.sum := by
        apply natDegree_multiset_prod
        exact h0S
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
        have hx2r : x = 2*r := by
          grind
        exact dvd_of_mul_right_eq r (id (Eq.symm hx2r))
      grind
    obtain ⟨g, hg1, hg2⟩ := hg
    use g
    constructor
    · unfold S at hg1
      exact UniqueFactorizationMonoid.irreducible_of_factor g hg1
    constructor
    · exact UniqueFactorizationMonoid.dvd_of_mem_factors hg1
    apply hg2
