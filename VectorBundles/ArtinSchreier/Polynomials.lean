module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

open Polynomial

variable {F : Type} [Field F] {f g h: Polynomial F}

lemma polynomial_monic_divisor (h1 : f.Monic) (h2 : g.Monic) (h3 : f ∣ g) :
  ∃ e : Polynomial F, e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree := by
  obtain ⟨e, h3⟩ := exists_eq_mul_left_of_dvd h3
  use e
  have := calc
    e.leadingCoeff = (e * f).leadingCoeff := (leadingCoeff_mul_monic h1).symm
    _ = g.leadingCoeff := by rw [h3]
    _ = 1 := Monic.def.mp h2
  have h4 := Monic.def.mpr this
  refine ⟨h3.symm, h4, ?_⟩
  rw [h3]
  exact (Monic.natDegree_mul' h4 (Monic.ne_zero h1)).symm

lemma artin_schreier_poly {p : ℕ} (c : F) (hp : Nat.Prime p) :
  (X ^ p - X - C c).natDegree = p ∧ (X ^ p - X - C c).Monic := by
  let lin := - X - C c
  have h := calc
    lin.natDegree ≤ 1 := by
      refine (natDegree_sub_le_iff_right ?_).mpr ?_
      · exact natDegree_neg_le_of_le natDegree_X_le
      · simp only [natDegree_C, zero_le]
    _ < p := Nat.Prime.one_lt hp
  have h2 := natDegree_add_le_of_degree_le (natDegree_X_pow_le p) (Nat.le_of_succ_le h)
  have h3 : (X ^ p + lin).coeff p = 1 := by aesop
  have : X ^ p + lin = X^p - X - C c := by grind only
  rw [← this]
  constructor
  · exact natDegree_eq_of_le_of_coeff_ne_zero h2 (ne_zero_of_eq_one h3)
  · exact monic_of_natDegree_le_of_coeff_eq_one p h2 h3

lemma divisor_of_irreducible_poly (hdiv: f ∣ g) (hirr: Irreducible g) :
  f.natDegree = 0 ∨ f.natDegree = g.natDegree := by
  obtain ⟨e, h3⟩ := exists_eq_mul_left_of_dvd hdiv
  have := Irreducible.isUnit_or_isUnit hirr h3
  cases this with
  | inl h_isunit =>
    right
    rw [h3]
    have : e * f ≠ 0 := by aesop
    have := mul_ne_zero_iff.mp this
    calc
      f.natDegree = 0 + f.natDegree := (Nat.zero_add f.natDegree).symm
      _ = e.natDegree + f.natDegree :=
        Nat.add_left_inj.mpr (natDegree_eq_zero_of_isUnit h_isunit).symm
      _ = (e * f).natDegree := (natDegree_mul this.1 this.2).symm
  | inr h_isunit =>
    left
    exact natDegree_eq_zero_of_isUnit h_isunit

lemma odd_irreducible_factor (h : Odd f.natDegree) :
  ∃ g : Polynomial F, Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  obtain ⟨_, h⟩ := h
  have : f.natDegree > 0 := by linarith
  have := ne_zero_of_natDegree_gt this
  open UniqueFactorizationMonoid in
  let S := factors f
  have h_prod := Associated.symm (factors_prod this)
  have h0S : 0 ∉ S := by
    by_contra
    rw [Multiset.prod_eq_zero this] at h_prod
    simp_all only [ne_eq, associated_zero_iff_eq_zero]
  have := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h_prod)
  have : ∃ g ∈ S, Odd g.natDegree := by
    rw [this] at h
    by_contra
    push Not at this
    have := fun g a => (fun {n} => Nat.not_odd_iff_even.mp) (this g a)
    let T := S.map natDegree
    have := natDegree_multiset_prod S h0S
    have : 2 ∣ T.sum := by
      apply Multiset.dvd_sum
      intro x hx
      have : ∀ t : ℕ, t ∈ T → Even t := by aesop
      exact Even.two_dvd (this x hx)
    grind only [= Nat.odd_iff]
  obtain ⟨g, hg1, hg2⟩ := this
  use g
  exact ⟨irreducible_of_factor g hg1, dvd_of_mem_factors hg1, hg2⟩
