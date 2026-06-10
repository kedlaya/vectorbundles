module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

open Polynomial

variable {F : Type} [Field F] {f g h: Polynomial F}

lemma polynomial_monic_divisor (h1 : f.Monic) (h2 : g.Monic) (h3 : f ∣ g):
  ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree := by
  obtain ⟨e, h3⟩ := exists_eq_mul_left_of_dvd h3
  use e
  have := calc
    e.leadingCoeff = (e * f).leadingCoeff := (leadingCoeff_mul_monic h1).symm
    _ = g.leadingCoeff := by rw [h3]
    _ = 1 := Monic.def.mp h2
  have h4 : e.Monic := Monic.def.mpr this
  refine ⟨h3.symm, h4, ?_⟩
  rw [h3]
  exact (Monic.natDegree_mul h4 h1).symm

lemma artin_schreier_poly {p : ℕ} (c : F) (hp : Nat.Prime p):
  (X ^ p - X - C c).natDegree = p ∧ (X ^ p - X - C c).Monic := by
  let lin := - X - C c
  have h := calc
    lin.natDegree ≤ 1 := by
      refine (natDegree_sub_le_iff_right ?_).mpr ?_
      · exact natDegree_neg_le_of_le natDegree_X_le
      · simp only [natDegree_C, zero_le]
    _ < p := Nat.Prime.one_lt hp
  have h2 :=
    natDegree_add_le_of_degree_le (natDegree_X_pow_le p) (Nat.le_of_succ_le h)
  have h4 : (X ^ p + lin).coeff p = 1 := by
    have : lin.coeff p = 0 := coeff_eq_zero_of_natDegree_lt h
    aesop
  have : X ^ p + lin = X^p - X - C c := by grind only
  rw [← this]
  constructor
  · exact natDegree_eq_of_le_of_coeff_ne_zero h2 (ne_zero_of_eq_one h4)
  · exact monic_of_natDegree_le_of_coeff_eq_one p h2 h4

lemma divisor_of_irreducible_poly (hdiv: f ∣ g) (hirr: Irreducible g) :
  f.natDegree = 0 ∨ f.natDegree = g.natDegree := by
  obtain ⟨e, h3⟩ := exists_eq_mul_left_of_dvd hdiv
  have := Irreducible.isUnit_or_isUnit hirr h3
  cases this with
  | inl h_isunit =>
    right
    have : e * f ≠ 0 := by
      rw [← h3]
      exact Irreducible.ne_zero hirr
    have := mul_ne_zero_iff.mp this
    calc
      f.natDegree = 0 + f.natDegree := (Nat.zero_add f.natDegree).symm
      _ = e.natDegree + f.natDegree :=
        Nat.add_left_inj.mpr (natDegree_eq_zero_of_isUnit h_isunit).symm
      _ = (e * f).natDegree := (natDegree_mul this.1 this.2).symm
      _ = g.natDegree := by rw [h3]
  | inr h_isunit =>
    left
    exact natDegree_eq_zero_of_isUnit h_isunit

lemma odd_irreducible_factor (h : Odd f.natDegree) :
  ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  open UniqueFactorizationMonoid in
  have : f ≠ 0 := by
    obtain ⟨_, _⟩ := h
    have : f.natDegree > 0 := by linarith
    exact ne_zero_of_natDegree_gt this
  let S := factors f
  have h_prod : Associated f S.prod := Associated.symm (factors_prod this)
  have h0S : 0 ∉ S := by
    by_contra
    rw [Multiset.prod_eq_zero this] at h_prod
    simp_all only [ne_eq, associated_zero_iff_eq_zero]
  have : f.natDegree = S.prod.natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h_prod)
  have : ∃ g ∈ S, Odd g.natDegree := by
    rw [this] at h
    by_contra
    push Not at this
    have h1 : ∀ g ∈ S, Even g.natDegree :=
      fun g a => (fun {n} => Nat.not_odd_iff_even.mp) (this g a)
    let T := S.map natDegree
    have : S.prod.natDegree = T.sum := natDegree_multiset_prod S h0S
    have : ∀ t : ℕ, t ∈ T → Even t := by aesop
    have : 2 ∣ T.sum := by
      apply Multiset.dvd_sum
      intro x hx
      exact Even.two_dvd (this x hx)
    grind only [= Nat.odd_iff]
  obtain ⟨g, hg1, hg2⟩ := this
  use g
  exact ⟨irreducible_of_factor g hg1, dvd_of_mem_factors hg1, hg2⟩

lemma linear_substitution {p : ℕ} [ExpChar F p] {d : ℕ} (a : F) (hd: 1 < d) (hdeg: f.natDegree < d) :
  let fp := (map (frobenius F p) f).comp (X + C a);
    fp.natDegree < d ∧ fp.coeff (d-1) = (f.coeff (d-1)) ^ p := by
  let frob := frobenius F p
  let m := map frob
  let c := f.coeff (d-1)
  let f_high := monomial (d-1) c
  let f_low := f.erase (d-1)
  have h_sum := monomial_add_erase f (d-1)
  have h_deg1 := Nat.le_sub_one_of_lt hdeg
  let lin := X + C a
  have h_deg2 : ∀ g : Polynomial F, ((m g).comp lin).natDegree ≤ g.natDegree := by
    intro g
    calc
    ((m g).comp lin).natDegree ≤ (m g).natDegree * lin.natDegree := natDegree_comp_le
    _ = (m g).natDegree * 1 := by rw [natDegree_X_add_C a]
    _ = (m g).natDegree := Nat.mul_one (m g).natDegree
    _ ≤ g.natDegree := natDegree_map_le
  let fp := (m f).comp lin
  constructor
  · calc
    fp.natDegree ≤ f.natDegree := h_deg2 f
    _ ≤ d-1 := h_deg1
    _ < d := Nat.sub_one_lt_of_lt hdeg
  let fp_high := (m f_high).comp lin
  let fp_low := (m f_low).comp lin
  have h_add :=
    have := calc
      m f = m (f_high + f_low) := by rw [← h_sum]
      _ = m f_high + m f_low := Polynomial.map_add frob
    calc
    fp = (m f).comp lin := by rfl
    _ = (m f_high + m f_low).comp lin := by rw [this]
    _ = fp_high + fp_low := add_comp
  have h_highcoeff :=
    have h := calc
      fp_high = (m (monomial (d-1) c)).comp lin := by rfl
      _ = (monomial (d-1) (frob c)).comp lin := by aesop
      _ = (monomial (d-1) (c^p)).comp lin := ext (congrFun rfl)
      _ = C (c^p) * lin ^ (d-1) := monomial_comp (d-1)
    have h1 := calc
      (lin ^ (d-1)).coeff (d-1) = a^(d-1-(d-1)) * ((d-1).choose (d-1) : F) :=
        coeff_X_add_C_pow a (d-1) (d-1)
      _ = (1 : F) := by simp
    calc
    fp_high.coeff (d-1) = (C (c^p) * lin ^ (d-1)).coeff (d-1) := by rw [h]
    _ = c^p * (lin ^ (d-1)).coeff (d-1) := coeff_C_mul (lin ^ (d-1))
    _ = c^p := by simp [h1]
  calc
  fp.coeff (d-1) = (fp_high + fp_low).coeff (d-1) := by aesop
  _ = fp_high.coeff (d-1) + fp_low.coeff (d-1) := coeff_add fp_high fp_low (d-1)
  _ = fp_high.coeff (d-1) + 0 := by
    refine add_left_cancel_iff.mpr (coeff_eq_zero_of_natDegree_lt ?_)
    have h_deg : f_low.natDegree ≤ d-2 := by
      refine natDegree_le_iff_coeff_eq_zero.mpr ?_
      intro N hN
      if h : N = d - 1 then
        subst N
        exact erase_same f (d-1)
      else calc
        f_low.coeff N = f.coeff N := erase_ne f (d-1) N h
        _ = 0 := by
          refine coeff_eq_zero_of_natDegree_lt ?_
          calc
          f.natDegree ≤ d-1 := h_deg1
          _ < N := by grind only
    calc
    fp_low.natDegree ≤ f_low.natDegree := h_deg2 f_low
    _ ≤ d-2 := h_deg
    _ < d-1 := Nat.sub_succ_lt_self d 1 hd
  _ = fp_high.coeff (d-1) := by simp
  _ = c^p := h_highcoeff
