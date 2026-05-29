module

public import Mathlib.FieldTheory.AlgebraicClosure

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

variable (F : Type) (K : Type) [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]

lemma quadratic_algebraic_closure (h : Module.finrank F K = 2) :
  ∀ (a b : F), IsSquare (a^2+b) ∨ IsSquare (-b) := by
  intro a b
  have h_ac: IsAlgClosed K := IsAlgClosure.isAlgClosed F
  let g := Polynomial.monomial 4 1 + Polynomial.monomial 2 (-2*a) + Polynomial.monomial 0 (a^2+b)
  have hg_all : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧ g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0
    ∧ g.coeff 4 = 1 ∧ ∀ (n : ℕ), n > 4 → g.coeff n = 0 := by
    let g1 := Polynomial.monomial 4 (1 : F)
    let g2 := Polynomial.monomial 2 (-2*a)
    let g3 := Polynomial.monomial 0 (a^2+b)
    have : ∀ n : ℕ, g1.coeff n = if 4 = n then 1 else 0 := by
      intro n
      apply Polynomial.coeff_monomial
    have : ∀ n : ℕ, g2.coeff n = if 2 = n then (-2*a) else 0 := by
      intro n
      apply Polynomial.coeff_monomial
    have : ∀ n : ℕ, g3.coeff n = if 0 = n then (a^2+b) else 0 := by
      intro n
      apply Polynomial.coeff_monomial
    have : g = g1 + g2 + g3 := by
      grind
    have : ∀ n : ℕ, g.coeff n = g1.coeff n + g2.coeff n + g3.coeff n := by
      intro n
      aesop
    constructor
    · simp_all
    constructor
    · simp_all
    constructor
    · simp_all
    constructor
    · simp_all
    constructor
    · simp_all
    · grind
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hg_all
  have h_gdeg: g.natDegree = 4 ∧ g ≠ 0 ∧ g.degree = 4 := by
    have h1 : g.natDegree ≤ 4 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hg5
    have h2 : g.coeff 4 ≠ 0 := ne_zero_of_eq_one hg4
    have hdeg : g.natDegree = 4 :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h1 h2
    constructor
    · exact hdeg
    have h0 : g ≠ 0 := by
      by_contra
      simp_all
    constructor
    · apply h0
    · have _ : Polynomial.degree g = Polynomial.natDegree g :=
        Polynomial.degree_eq_natDegree h0
      simp_all
  obtain ⟨_, _, h_gdeg⟩ := h_gdeg
  have h_gmon : g.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one 4 ?_ ?_
    · aesop
    · simp_all
  have hf : ∃ f0 : Polynomial F, f0.Monic ∧ f0.natDegree = 2 ∧ f0 ∣ g := by
    have hc : ∃ c : K, Polynomial.aeval c g = 0 := by
      refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ g ?_
      · exact FaithfulSMul.algebraMap_injective F K
      · simp_all
    obtain ⟨c, hc⟩ := hc
    let f := minpoly F c
    have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
    have h_fmon: f.Monic := minpoly.monic h_int
    have h_div : f ∣ g := minpoly.dvd_iff.mpr hc
    have h_fdeg : f.natDegree = 1 ∨ f.natDegree = 2 := by
      have _ : f.natDegree > 0 := minpoly.natDegree_pos h_int
      have _ : f.natDegree ≤ g.natDegree := by
        refine Polynomial.natDegree_le_of_dvd h_div ?_
        exact Polynomial.Monic.ne_zero h_gmon
      have _ : (minpoly F c).natDegree ≤ Module.finrank F K := minpoly.natDegree_le  c
      grind
    cases h_fdeg
    · have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
        ∧ e.degree = e.natDegree := polynomial_monic_divisor h_fmon h_gmon h_div
      obtain ⟨e, h_ef1, h_emonic, h_ef2, _⟩ := h_e
      have _ : e.natDegree = 3 := by grind
      have h_div1a : e ∣ g := dvd_of_mul_right_eq f h_ef1
      have hc : ∃ c : K, Polynomial.aeval c e = 0 := by
        refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ e ?_
        · exact FaithfulSMul.algebraMap_injective F K
        · simp_all
      obtain ⟨c, hc⟩ := hc
      let f := minpoly F c
      have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
      have h_fmon: f.Monic := minpoly.monic h_int
      have h_div2 : f ∣ e := minpoly.dvd_iff.mpr hc
      have h_fdeg : f.natDegree = 1 ∨ f.natDegree = 2 := by
        have _ : f.natDegree > 0 := minpoly.natDegree_pos h_int
        have _ : f.natDegree ≤ e.natDegree := by
          refine Polynomial.natDegree_le_of_dvd h_div2 ?_
          exact Polynomial.Monic.ne_zero h_emonic
        have _ : (minpoly F c).natDegree ≤ Module.finrank F K := minpoly.natDegree_le c
        grind
      have h_div3 : f ∣ g := dvd_trans h_div2 h_div1a
      cases h_fdeg
      · have h_d : ∃ (d : Polynomial F), d * f = e ∧ d.Monic
          ∧ d.natDegree + f.natDegree = e.natDegree ∧ d.degree = d.natDegree :=
            polynomial_monic_divisor h_fmon h_emonic h_div2
        obtain ⟨d, h_d1, h_dmonic, h_d2, h_d3⟩ := h_d
        use d
        constructor
        · exact h_dmonic
        constructor
        · linarith
        · have h_div4 : d ∣ e := dvd_of_mul_right_eq f h_d1
          exact dvd_trans h_div4 h_div1a
      · use f
    · use f
  obtain ⟨f, hf1, hf2, hf3⟩ := hf
  have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
    ∧ e.degree = e.natDegree := polynomial_monic_divisor hf1 h_gmon hf3
  obtain ⟨e, h_ftimese, h_emon, _, _⟩ := h_e
  have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 := by
    have : Polynomial.coeff f (Polynomial.natDegree f) = Polynomial.leadingCoeff f :=
      Polynomial.coeff_natDegree
    have : f.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → f.coeff N = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero
    simp_all
  have : e.coeff 2 = 1 ∧ e.coeff 3 = 0 ∧ e.coeff 4 = 0 := by
    have : Polynomial.coeff e (Polynomial.natDegree e) = Polynomial.leadingCoeff e :=
      Polynomial.coeff_natDegree
    have : e.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → e.coeff N = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero
    simp_all
  have h_prod: ∀ (n : ℕ), (e * f).coeff n =
    ∑ x ∈ Finset.antidiagonal n, e.coeff x.1 * f.coeff x.2 :=
    Polynomial.coeff_mul e f
  have : (e.coeff 0) * (f.coeff 0) = a^2 + b := by
    rw [←hg0, ←h_ftimese]
    apply (Polynomial.mul_coeff_zero e f).symm
  have : (e.coeff 0) * (f.coeff 1) + (e.coeff 1) * (f.coeff 0) = 0 := by
    rw [←hg1, ←h_ftimese]
    apply (Polynomial.mul_coeff_one e f).symm
  have : (f.coeff 0) + (e.coeff 1) * (f.coeff 1) + (e.coeff 0) = -2*a := by
    specialize h_prod 2
    unfold Finset.antidiagonal at h_prod
    unfold Finset.Nat.instHasAntidiagonal at h_prod
    simp_all
    ring
  have : (e.coeff 1) + (f.coeff 1) = 0 := by
    specialize h_prod 3
    unfold Finset.antidiagonal at h_prod
    unfold Finset.Nat.instHasAntidiagonal at h_prod
    simp_all
  by_cases f.coeff 1 = 0
  · right
    unfold IsSquare
    use f.coeff 0 + a
    have : e.coeff 0 = - (f.coeff 0) - 2*a := by grind
    have : (- (f.coeff 0) - 2*a) * (f.coeff 0) = a^2 + b := by grind
    simp_all
    grind
  · left
    have _ : e.coeff 0 = f.coeff 0 := by grind
    unfold IsSquare
    use (f.coeff 0)
    grind

lemma quadratic_algebraic_closure_no_i (h : Module.finrank F K = 2) :
  ∀ (a : F), IsSquare a ∨ IsSquare (-a) := by
  intro a
  have _ : IsSquare (0 ^ 2 + a) ∨ IsSquare (-a) := by
    apply quadratic_algebraic_closure F K h 0 a
  simp_all
