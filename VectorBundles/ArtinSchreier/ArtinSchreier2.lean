module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
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
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

lemma quadratic_algebraic_closure (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : Module.finrank F K = 2) :
  ∀ (a b : F), IsSquare (a^2+b) ∨ IsSquare (-b) := by
  intro a b
  have h_ac: IsAlgClosed K :=
    IsAlgClosure.isAlgClosed F
  let g := Polynomial.monomial 4 1 + Polynomial.monomial 2 (-2*a) + Polynomial.monomial 0 (a^2+b)
  have hg_all : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧ g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0
    ∧ g.coeff 4 = 1 ∧ ∀ (n : ℕ), n > 4 → g.coeff n = 0 := by
    let g1 := Polynomial.monomial 4 (1 : F)
    let g2 := Polynomial.monomial 2 (-2*a)
    let g3 := Polynomial.monomial 0 (a^2+b)
    have h_coeffg1 : g1.coeff 4 = 1 ∧  ∀ (n : ℕ), n ≠ 4 → g1.coeff n = 0 := by
      apply monomial_coeffs 4 1
    have h_coeffg2 : g2.coeff 2 = -2*a ∧  ∀ (n : ℕ), n ≠ 2 → g2.coeff n = 0 := by
      apply monomial_coeffs 2 (-2*a)
    have h_coeffg3 : g3.coeff 0 = a^2 + b ∧  ∀ (n : ℕ), n ≠ 0 → g3.coeff n = 0 := by
      apply monomial_coeffs 0 (a^2 + b)
    have _ : g = g1 + g2 + g3 := by
      grind
    have h_coeff : ∀ n : ℕ, g.coeff n = g1.coeff n + g2.coeff n + g3.coeff n := by
      intro n
      aesop
    obtain ⟨h_coeffg1a, h_coeffg1b⟩ := h_coeffg1
    obtain ⟨h_coeffg2a, h_coeffg2b⟩ := h_coeffg2
    obtain ⟨h_coeffg3a, h_coeffg3b⟩ := h_coeffg3
    constructor
    · specialize h_coeff 0
      specialize h_coeffg1b 0
      specialize h_coeffg2b 0
      simp_all
    constructor
    · specialize h_coeff 1
      specialize h_coeffg1b 1
      specialize h_coeffg2b 1
      specialize h_coeffg3b 1
      simp_all
    constructor
    · specialize h_coeff 2
      specialize h_coeffg1b 2
      specialize h_coeffg3b 2
      simp_all
    constructor
    · specialize h_coeff 3
      specialize h_coeffg1b 3
      specialize h_coeffg2b 3
      specialize h_coeffg3b 3
      simp_all
    constructor
    · specialize h_coeff 4
      specialize h_coeffg2b 4
      specialize h_coeffg3b 4
      simp_all
    intro n hn
    specialize h_coeff n
    specialize h_coeffg1b n
    specialize h_coeffg2b n
    specialize h_coeffg3b n
    grind
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hg_all
  have h_gdeg: g.natDegree = 4 ∧ g ≠ 0 ∧ g.degree = 4 := by
    have _ : g.natDegree ≤ 4 := by
      exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hg5
    have _ : g.coeff 4 ≠ 0 := by
      exact ne_zero_of_eq_one hg4
    have hdeg : g.natDegree = 4 := by
      (expose_names; exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h_1 h_2)
    constructor
    · exact hdeg
    have h0 : g ≠ 0 := by
      by_contra
      have h0 : (0 : Polynomial K).natDegree = 0 := Polynomial.natDegree_zero
      simp_all
    constructor
    · apply h0
    have _ : Polynomial.degree g = Polynomial.natDegree g := by
        apply Polynomial.degree_eq_natDegree
        exact h0
    simp_all
  obtain ⟨h_gnatdeg, h_gnonzero, h_gdeg⟩ := h_gdeg
  have h_gmon : g.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one 4 ?_ ?_
    simp_all
    exact hg4
  have hf : ∃ f0 : Polynomial F, f0.Monic ∧ f0.natDegree = 2 ∧ f0 ∣ g := by
    have hc : ∃ c : K, Polynomial.aeval c g = 0 := by
      refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ g ?_
      exact FaithfulSMul.algebraMap_injective F K
      simp_all
    obtain ⟨c, hc⟩ := hc
    let f := minpoly F c
    have h_int : IsIntegral F c := by
      exact Algebra.IsIntegral.isIntegral c
    have h_fmon: f.Monic := by
      refine minpoly.monic ?_
      exact h_int
    have h_div : f ∣ g := by
      exact minpoly.dvd_iff.mpr hc
    have h_fdeg : f.natDegree = 1 ∨ f.natDegree = 2 := by
      have _ : f.natDegree > 0 := by
        refine minpoly.natDegree_pos ?_
        exact h_int
      have _ : f.natDegree ≤ g.natDegree := by
        refine Polynomial.natDegree_le_of_dvd h_div ?_
        exact Polynomial.Monic.ne_zero h_gmon
      have _ : (minpoly F c).natDegree ≤ Module.finrank F K := by
        apply minpoly.natDegree_le
      grind
    cases h_fdeg
    · have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
  ∧ e.degree = e.natDegree :=
        polynomial_monic_divisor h_fmon h_gmon h_div
      obtain ⟨e, _, h_emonic, _, _⟩ := h_e
      have _ : e.natDegree = 3 := by
        grind
      have hc : ∃ c : K, Polynomial.aeval c e = 0 := by
        refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ e ?_
        exact FaithfulSMul.algebraMap_injective F K
        simp_all
      obtain ⟨c, hc⟩ := hc
      let f := minpoly F c
      have h_int : IsIntegral F c := by
        exact Algebra.IsIntegral.isIntegral c
      have h_fmon: f.Monic := by
        refine minpoly.monic ?_
        exact h_int
      have h_div2 : f ∣ e := by
        exact minpoly.dvd_iff.mpr hc
      have h_fdeg : f.natDegree = 1 ∨ f.natDegree = 2 := by
        have _ : f.natDegree > 0 := by
          refine minpoly.natDegree_pos ?_
          exact h_int
        have _ : f.natDegree ≤ e.natDegree := by
          refine Polynomial.natDegree_le_of_dvd h_div2 ?_
          exact Polynomial.Monic.ne_zero h_emonic
        have _ : (minpoly F c).natDegree ≤ Module.finrank F K := by
          apply minpoly.natDegree_le
        grind
      have h_div1a : e ∣ g := by
        (expose_names; exact dvd_of_mul_right_eq f_1 left)
      have h_div3 : f ∣ g := by
        apply dvd_trans h_div2 h_div1a
      cases h_fdeg
      · have h_d : ∃ (d : Polynomial F), d * f = e ∧ d.Monic
          ∧ d.natDegree + f.natDegree = e.natDegree ∧ d.degree = d.natDegree :=
          polynomial_monic_divisor h_fmon h_emonic h_div2
        obtain ⟨d, _, h_dmonic, _, _⟩ := h_d
        use d
        constructor
        exact h_dmonic
        constructor
        simp_all
        have h_div4 : d ∣ e := by
          (expose_names; exact dvd_of_mul_right_eq f left_2)
        exact dvd_trans h_div4 h_div1a
      · use f
    · use f
  obtain ⟨f, hf1, hf2, hf3⟩ := hf
  have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
  ∧ e.degree = e.natDegree :=
    polynomial_monic_divisor hf1 h_gmon hf3
  obtain ⟨e, h_ftimese, h_emon, _, _⟩ := h_e
  have _ : f.coeff 2 = 1 := by
    have _ :  Polynomial.coeff f (Polynomial.natDegree f) = Polynomial.leadingCoeff f :=
      Polynomial.coeff_natDegree
    simp_all
  have _ : f.coeff 3 = 0 := by
    have _ : f.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → f.coeff N = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero
    simp_all
  have _ : f.coeff 4 = 0 := by
    have _ : f.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → f.coeff N = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero
    simp_all
  have _ : e.coeff 2 = 1 := by
    have _ :  Polynomial.coeff e (Polynomial.natDegree e) = Polynomial.leadingCoeff e :=
      Polynomial.coeff_natDegree
    simp_all
  have _ : e.coeff 3 = 0 := by
    have _ : e.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → e.coeff N = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero
    simp_all
  have _ : e.coeff 4 = 0 := by
    have _ : e.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → e.coeff N = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero
    simp_all
  have h_prod: ∀ (n : ℕ), (e * f).coeff n =
    ∑ x ∈ Finset.antidiagonal n, e.coeff x.1 * f.coeff x.2 :=
    Polynomial.coeff_mul e f
  have h_prod0 : (e.coeff 0) * (f.coeff 0) = a^2 + b := by
    specialize h_prod 0
    unfold Finset.antidiagonal at h_prod
    unfold Finset.Nat.instHasAntidiagonal at h_prod
    simp_all
  have h_prod1 : (e.coeff 0) * (f.coeff 1) + (e.coeff 1) * (f.coeff 0) = 0 := by
    specialize h_prod 1
    unfold Finset.antidiagonal at h_prod
    unfold Finset.Nat.instHasAntidiagonal at h_prod
    simp_all
  have h_prod2 : (f.coeff 0) + (e.coeff 1) * (f.coeff 1) + (e.coeff 0) = -2*a := by
    specialize h_prod 2
    unfold Finset.antidiagonal at h_prod
    unfold Finset.Nat.instHasAntidiagonal at h_prod
    simp_all
    ring
  have h_prod3 : (e.coeff 1) + (f.coeff 1) = 0 := by
    specialize h_prod 3
    unfold Finset.antidiagonal at h_prod
    unfold Finset.Nat.instHasAntidiagonal at h_prod
    simp_all
  by_cases f.coeff 1 = 0
  · right
    unfold IsSquare
    use f.coeff 0 + a
    have _ : e.coeff 0 = - (f.coeff 0) - 2*a := by
      grind
    have _ : (- (f.coeff 0) - 2*a) * (f.coeff 0) = a^2 + b := by
      grind
    simp_all
    grind
  · left
    have _ : e.coeff 0 = f.coeff 0 := by
      grind
    unfold IsSquare
    use (f.coeff 0)
    grind

lemma quadratic_algebraic_closure_no_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : Module.finrank F K = 2) :
  ∀ (a : F), IsSquare a ∨ IsSquare (-a) := by
  intro a
  have _ : IsSquare (0 ^ 2 + a) ∨ IsSquare (-a) := by
    apply quadratic_algebraic_closure F K h 0 (a)
  simp_all
