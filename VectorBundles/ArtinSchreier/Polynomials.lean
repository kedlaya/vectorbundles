module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

@[expose] public section

open Polynomial

variable {F : Type} [Field F]

lemma monic_division {f g : Polynomial F} (h1: f.Monic) (h2 : f ∣ g) : (g /ₘ f) * f = g := by
  let e := g /ₘ f
  calc
    e * f = f * e := CommMonoid.mul_comm e f
    _ = 0 + f * e := Eq.symm (AddZeroClass.zero_add (f * e))
    _ = g %ₘ f + f * e := by
      refine add_right_cancel_iff.mpr ?_
      symm
      exact (modByMonic_eq_zero_iff_dvd h1).mpr h2
    _ = g := modByMonic_add_div g f

lemma polynomial_monic_divisor {f g: Polynomial F} (h1 : f.Monic) (h2 : g.Monic) (h3 : f ∣ g):
    ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧
      e.natDegree + f.natDegree = g.natDegree ∧ e.degree = e.natDegree := by
  let e := g /ₘ f
  use e
  have h_ftimese : e * f = g := monic_division h1 h3
  have h6 : e.Monic := by
    refine Monic.def.mpr ?_
    calc
    e.leadingCoeff = g.leadingCoeff := by
      refine leadingCoeff_divByMonic_of_monic h1 ?_
      apply degree_le_of_dvd h3
      exact Monic.ne_zero h2
    _ = 1 := Monic.def.mp h2
  refine ⟨h_ftimese, h6, ?_, ?_⟩
  · rw [← h_ftimese]
    exact (Monic.natDegree_mul h6 h1).symm
  · refine degree_eq_natDegree ?_
    exact Monic.ne_zero h6

lemma congruence_low_degree {f g h : Polynomial F} (h1 : h ∣ (f-g)) (h2 : f.natDegree < h.natDegree)
  (h3 : g.natDegree < h.natDegree) (h4: h.Monic) : f = g := by
  have h5 : (f-g).natDegree < h.natDegree := by
    calc
      (f-g).natDegree ≤ max f.natDegree g.natDegree := natDegree_sub_le f g
      _ < h.natDegree := max_lt_iff.mpr ⟨h2, h3⟩
  have h6 : (f-g).degree < h.degree := degree_lt_degree h5
  have h7 : (f-g) /ₘ h = 0 := (divByMonic_eq_zero_iff h4).mpr h6
  have h9 : (f-g) %ₘ h = 0 := (modByMonic_eq_zero_iff_dvd h4).mpr h1
  have _ : f - g = 0 := by
    calc
    f - g = (f-g) %ₘ h + h * ((f-g) /ₘ h) := (modByMonic_add_div (f-g) h).symm
    _ = h * ((f-g) /ₘ h) := add_eq_right.mpr h9
    _ = h * 0 := by rw [h7]
    _ = 0 := (Monic.mul_right_eq_zero_iff h4).mpr rfl
  grind

lemma artin_schreier_poly {p : ℕ} (c : F) (hp : Nat.Prime p):
  (X ^ p - X - C c).natDegree = p ∧ (X ^ p - X - C c).Monic := by
  let lin := - X - C c
  have h1 : lin.natDegree ≤ 1 := by
    refine (natDegree_sub_le_iff_right ?_).mpr ?_
    · exact natDegree_neg_le_of_le natDegree_X_le
    · calc
      (C c).natDegree = 0 := natDegree_C c
      _ ≤ 1 := Nat.zero_le 1
  have h3 : lin.natDegree < p := by
    calc
      lin.natDegree ≤ 1 := h1
      _ < p := Nat.Prime.one_lt hp
  have h2 : (X ^ p + lin).natDegree ≤ p := by
    refine natDegree_add_le_of_degree_le ?_ ?_
    · exact natDegree_X_pow_le p
    · exact Nat.le_of_succ_le h3
  have h4 : (X ^ p + lin).coeff p = 1 := by
    have : ( ( X : Polynomial F) ^ p ).coeff p = 1 := coeff_X_pow_self p
    have : lin.coeff p = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      exact Nat.lt_of_lt_of_eq h3 rfl
    aesop
  have h_eq: X ^ p + lin = X^p - X - C c := by grind
  rw [← h_eq]
  constructor
  · refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · exact String.Pos.Raw.mk_le_mk.mp h2
    · exact ne_zero_of_eq_one h4
  · exact monic_of_natDegree_le_of_coeff_eq_one p h2 h4

lemma monic_divisor_of_same_degree {f g : Polynomial F} (h1: f.Monic) (h2 : g.Monic)
  (hdiv: f ∣ g) (hdeg: f.natDegree = g.natDegree) : f = g := by
  have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
    ∧ e.degree = e.natDegree :=
      polynomial_monic_divisor h1 h2 hdiv
  obtain ⟨e, h3, h_emonic, h4, _⟩ := h_e
  subst h3
  simp_all only [dvd_mul_left, Nat.add_eq_right, Monic.natDegree_eq_zero, one_mul]

lemma divisor_of_irreducible_poly {f g : Polynomial F} (hdiv: f ∣ g) (hirr: Irreducible g) :
  f.natDegree = 0 ∨ f.natDegree = g.natDegree := by
  have hg0 : g ≠ 0 := Irreducible.ne_zero hirr
  let g0 := g * C (1 / g.leadingCoeff)
  have h_gmon : g0.Monic := by
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    have : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    simp_all
  have hf0 : f ≠ 0 := ne_zero_of_dvd_ne_zero hg0 hdiv
  let f0 := f * C (1 / f.leadingCoeff)
  have h_fmon : f0.Monic := by
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    simp_all
  have h_div : f0 ∣ g0 := by
    apply mul_dvd_mul hdiv
    simp_all
  have h_e:  ∃ (e : Polynomial F), e * f0 = g0 ∧ e.Monic ∧
    e.natDegree + f0.natDegree = g0.natDegree ∧ e.degree = e.natDegree :=
    polynomial_monic_divisor h_fmon h_gmon h_div
  obtain ⟨e, h_mul, h_resmonic, h_degs, _⟩ := h_e
  have h_g0_irr : Irreducible g0 :=
    have h_unit : IsUnit (C (1 / g.leadingCoeff)) := by
      refine isUnit_C.mpr ?_
      simp_all
    (irreducible_mul_isUnit h_unit).mpr hirr
  have h_f0deg : f0.natDegree = f.natDegree := by
    apply natDegree_mul_C
    simp_all only [ne_eq, one_div, inv_eq_zero, leadingCoeff_eq_zero, not_false_eq_true]
  have h_g0deg : g0.natDegree = g.natDegree := by
    apply natDegree_mul_C
    simp_all only [ne_eq, one_div, inv_eq_zero, leadingCoeff_eq_zero, not_false_eq_true]
  have h_isunit : IsUnit e ∨ IsUnit f0 :=
    h_g0_irr.isUnit_or_isUnit (id (Eq.symm h_mul))
  cases h_isunit with
  | inl h_isunit =>
    right
    calc
      f.natDegree = f0.natDegree := h_f0deg.symm
      _ = 0 + f0.natDegree := (Nat.zero_add f0.natDegree).symm
      _ = e.natDegree + f0.natDegree := by
        refine ((fun {m k n} => Nat.add_right_cancel_iff.mpr) ?_).symm
        exact natDegree_eq_zero_of_isUnit h_isunit
      _ = g0.natDegree := h_degs
      _ = g.natDegree := h_g0deg
  | inr h_isunit =>
    left
    rw [← h_f0deg]
    exact natDegree_eq_zero_of_isUnit h_isunit

lemma odd_irreducible_factor {f : Polynomial F} (h : Odd f.natDegree) :
  ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  have hf0 : f ≠ 0 := by
    unfold Odd at h
    obtain ⟨k, _⟩ := h
    have t : f.natDegree > 0 := by linarith
    exact ne_zero_of_natDegree_gt t
  let S := UniqueFactorizationMonoid.factors f
  have h_prod : Associated f S.prod := Associated.symm (UniqueFactorizationMonoid.factors_prod hf0)
  have h0S : 0 ∉ S := by
    by_contra
    have hS : S.prod = 0 := Multiset.prod_eq_zero this
    have h0 : Associated f 0 := by
      rw [hS] at h_prod
      exact h_prod
    aesop
  have h_deg : f.natDegree = S.prod.natDegree :=
    have h1 : f.degree = S.prod.degree := degree_eq_degree_of_associated h_prod
    natDegree_eq_of_degree_eq h1
  have hg : ∃ g ∈ S, Odd g.natDegree := by
    have : Odd S.prod.natDegree := by
      rw [h_deg] at h
      exact h
    by_contra
    push Not at this
    let T := S.map natDegree
    have : S.prod.natDegree = T.sum := natDegree_multiset_prod S h0S
    have ht : ∀ t : ℕ, t ∈ T → Even t := by
      by_contra
      push Not at this
      obtain ⟨t, ht1, ht2⟩ := this
      unfold Multiset.map at T
      have hg : ∃ g ∈ S, g.natDegree = t := Multiset.mem_map.mp ht1
      obtain ⟨g, hg⟩ := hg
      grind
    have : 2 ∣ T.sum := by
      apply Multiset.dvd_sum
      intro x hx
      specialize ht x hx
      exact Even.two_dvd ht
    grind
  obtain ⟨g, hg1, hg2⟩ := hg
  use g
  refine ⟨?_, ?_, hg2⟩
  · unfold S at hg1
    exact UniqueFactorizationMonoid.irreducible_of_factor g hg1
  · exact UniqueFactorizationMonoid.dvd_of_mem_factors hg1

lemma linear_substitution {p : ℕ} [ExpChar F p] {d : ℕ} (a : F)
  (y0_rep : Polynomial F) (hp: Nat.Prime p) (hd: 1 < d) (hdeg: y0_rep.natDegree < d) :
    let y0p_rep := (map (frobenius F p) y0_rep).comp (X + C a);
      y0p_rep.natDegree < d ∧ y0p_rep.coeff (d-1) = (y0_rep.coeff (d-1)) ^ p := by
  let frob := frobenius F p
  let m := map frob
  let y0_high := (monomial (d-1)) (y0_rep.coeff (d-1))
  let y0_low := y0_rep.erase (d-1)
  have h_sum: y0_high + y0_low = y0_rep := monomial_add_erase y0_rep (d-1)
  have h_deg1 : y0_rep.natDegree ≤ d-1 := Nat.le_sub_one_of_lt hdeg
  let lin := X + C a
  have h_deg2 : ∀ (f : Polynomial F), ((m f).comp lin).natDegree ≤ f.natDegree := by
    intro f
    calc
    ((m f).comp lin).natDegree ≤ (m f).natDegree * lin.natDegree := natDegree_comp_le
    _ = (m f).natDegree * 1 := by rw [natDegree_X_add_C a]
    _ = (m f).natDegree := Nat.mul_one (m f).natDegree
    _ ≤ f.natDegree := natDegree_map_le
  let y0p_rep := (m y0_rep).comp lin
  constructor
  · calc
    y0p_rep.natDegree ≤ y0_rep.natDegree := h_deg2 y0_rep
    _ ≤ d-1 := h_deg1
    _ < d := Nat.sub_one_lt_of_lt hdeg
  let y0p_high := (m y0_high).comp lin
  let y0p_low := (m y0_low).comp lin
  have h_add : y0p_rep = y0p_high + y0p_low := by
    have h_map: m y0_rep = m y0_high + m y0_low := by
      calc
      m y0_rep = m (y0_high + y0_low) := by rw [← h_sum]
      _ = m y0_high + m y0_low := Polynomial.map_add frob
    calc
    y0p_rep = (m y0_rep).comp lin := by rfl
    _ = (m y0_high + m y0_low).comp lin := by rw [h_map]
    _ = y0p_high + y0p_low := add_comp
  let c := y0_rep.coeff (d-1)
  have h_highcoeff : y0p_high.coeff (d-1) = c^p := by
    have : y0p_high = (C (c^p)) * lin ^ (d-1) := by
      calc
      y0p_high = (m y0_high).comp lin := by rfl
      _ = (m (monomial (d-1) (y0_rep.coeff (d-1)))).comp lin := by rfl
      _ = (monomial (d-1) (frob c)).comp lin := by aesop
      _ = (monomial (d-1) (c^p)).comp lin := ext (congrFun rfl)
      _ = (C (c^p)) * lin ^ (d-1) := monomial_comp (d-1)
    have : (lin ^ (d - 1)).coeff (d-1) = 1 := by
      calc
      (lin ^ (d - 1)).coeff (d-1) = a^(d-1-(d-1)) * ((d-1).choose (d-1) : F) :=
        coeff_X_add_C_pow a (d-1) (d-1)
      _ = (1 : F) := by simp
    calc
    y0p_high.coeff (d-1)
    _ = ((m y0_high).comp lin).coeff (d-1) := by rfl
    _ = ( (C (c^p)) * lin ^ (d-1)).coeff (d-1) := by grind
    _ = c^p * ( lin ^ (d-1)).coeff (d-1) := coeff_C_mul (lin ^ (d - 1))
    _ = c^p := by aesop
  calc
    y0p_rep.coeff (d-1) = (y0p_high + y0p_low).coeff (d-1) := by aesop
    _ = y0p_high.coeff (d-1) + y0p_low.coeff (d-1) := coeff_add y0p_high y0p_low (d-1)
    _ = y0p_high.coeff (d-1) + 0 := by
      refine add_left_cancel_iff.mpr ?_
      refine coeff_eq_zero_of_natDegree_lt ?_
      have h_deg : y0_low.natDegree ≤ d-2 := by
        have : p ≥ 2 := Nat.Prime.two_le hp
        refine natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro N hN
        by_cases N = d - 1
        · subst N
          exact erase_same y0_rep (d-1)
        · rename_i h
          calc
          y0_low.coeff N = y0_rep.coeff N := erase_ne y0_rep (d-1) N h
          _ = 0 := by
            refine coeff_eq_zero_of_natDegree_lt ?_
            calc
              y0_rep.natDegree ≤ d-1 := h_deg1
              _ < N := by grind
      have h_deglow : y0p_low.natDegree ≤ d-2 := by calc
        y0p_low.natDegree ≤ y0_low.natDegree := h_deg2 y0_low
        _ ≤ d-2 := h_deg
      refine (Nat.le_pred_iff_lt ?_).mp h_deglow
      refine Nat.zero_lt_sub_of_lt ?_
      exact hd
    _ = y0p_high.coeff (d-1) := by simp
    _ = c^p := h_highcoeff
