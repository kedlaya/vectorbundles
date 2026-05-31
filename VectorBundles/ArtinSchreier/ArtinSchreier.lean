module

public import Mathlib.FieldTheory.AlgebraicClosure

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

open Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]  [IsAlgClosure F K]
  (h : finrank F K = 2)

lemma divisor_by_finrank {f : Polynomial F} (hf : f.natDegree ≠ 0) :
  ∃ (d : Polynomial F), d.Monic ∧ d.natDegree ∣ finrank F K ∧ d ∣ f := by
  have hf1 : f.degree ≠ 0 := by
    exact Ne.symm (ne_of_apply_ne (WithBot.unbotD 0) fun a => hf (id (Eq.symm a)))
  have hc : ∃ c : K, aeval c f = 0 := by
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ f hf1
    exact FaithfulSMul.algebraMap_injective F K
  obtain ⟨c, hc⟩ := hc
  use minpoly F c
  have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  refine ⟨?_, ?_, ?_⟩
  · exact minpoly.monic h_int
  · exact minpoly.degree_dvd h_int
  · exact minpoly.dvd_iff.mpr hc

include h in
lemma quadratic_algebraic_closure : ∀ (a b : F), IsSquare (a^2+b) ∨ IsSquare (-b) := by
  intro a b
  let g := monomial 4 1 + monomial 2 (-2*a) + monomial 0 (a^2+b)
  have hg_all : g.coeff 0 = (a^2 + b) ∧ g.coeff 1 = 0 ∧ g.coeff 2 = - 2 * a ∧ g.coeff 3 = 0
    ∧ g.coeff 4 = 1 ∧ ∀ (n : ℕ), n > 4 → g.coeff n = 0 := by
    let g1 := monomial 4 (1 : F)
    let g2 := monomial 2 (-2*a)
    let g3 := monomial 0 (a^2+b)
    have : ∀ n : ℕ, g1.coeff n = if 4 = n then 1 else 0 := by
      intro n
      apply coeff_monomial
    have : ∀ n : ℕ, g2.coeff n = if 2 = n then (-2*a) else 0 := by
      intro n
      apply coeff_monomial
    have : ∀ n : ℕ, g3.coeff n = if 0 = n then (a^2+b) else 0 := by
      intro n
      apply coeff_monomial
    have : ∀ (n : ℕ), n > 4 → g.coeff n = 0 := by aesop
    have : g = g1 + g2 + g3 := by grind
    simp_all
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hg_all
  have h1 : g.natDegree ≤ 4 := natDegree_le_iff_coeff_eq_zero.mpr hg5
  have h_gmon : g.Monic := monic_of_natDegree_le_of_coeff_eq_one 4 h1 hg4
  have h_gdeg: g.natDegree = 4 :=
    have h2 : g.coeff 4 ≠ 0 := ne_zero_of_eq_one hg4
    natDegree_eq_of_le_of_coeff_ne_zero h1 h2
  have hf : ∃ f0 : Polynomial F, f0.Monic ∧ f0.natDegree = 2 ∧ f0 ∣ g := by
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    have h_divh: ∀ (h : Polynomial F), h.natDegree ≠ 0 → ∃ (f : Polynomial F),
      f.Monic ∧ (f.natDegree = 1 ∨ f.natDegree = 2) ∧ f ∣ h := by
      intro h h0
      have hf : ∃ (f : Polynomial F), f.Monic ∧ f.natDegree ∣ finrank F K ∧ f ∣ h :=
        divisor_by_finrank F K h0
      obtain ⟨f, _, _, _⟩ := hf
      have h_fdeg : f.natDegree = 1 ∨ f.natDegree = 2 := by
        have : f.natDegree ∣ 2 := by grind
        refine (Nat.dvd_prime ?_).mp this
        exact Nat.prime_two
      use f
    have hg0 : g.natDegree ≠ 0 := by simp_all
    obtain ⟨f, h_fmon, h_fdeg, h_div⟩ := h_divh g hg0
    cases h_fdeg
    · have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
        ∧ e.degree = e.natDegree := polynomial_monic_divisor h_fmon h_gmon h_div
      obtain ⟨e, h_ef1, h_emonic, _, _⟩ := h_e
      have h_div1a : e ∣ g := dvd_of_mul_right_eq f h_ef1
      have he0 : e.natDegree ≠ 0 := by simp_all
      obtain ⟨f, h_fmon, h_fdeg, h_div⟩ := h_divh e he0
      cases h_fdeg with
      | inl =>
        have h_d : ∃ (d : Polynomial F), d * f = e ∧ d.Monic
          ∧ d.natDegree + f.natDegree = e.natDegree ∧ d.degree = d.natDegree :=
            polynomial_monic_divisor h_fmon h_emonic h_div
        obtain ⟨d, h_d1, h_dmonic, _, _⟩ := h_d
        use d
        refine ⟨h_dmonic, ?_, ?_⟩
        · linarith
        · have h_div4 : d ∣ e := dvd_of_mul_right_eq f h_d1
          exact dvd_trans h_div4 h_div1a
      | inr h_fdeg =>
        use f
        refine ⟨h_fmon, h_fdeg, ?_⟩
        exact dvd_trans h_div h_div1a
    · use f
  obtain ⟨f, hf1, hf2, hf3⟩ := hf
  have h_e : ∃ (e : Polynomial F), e * f = g ∧ e.Monic ∧ e.natDegree + f.natDegree = g.natDegree
    ∧ e.degree = e.natDegree := polynomial_monic_divisor hf1 h_gmon hf3
  obtain ⟨e, h_ftimese, h_emon, _, _⟩ := h_e
  have : f.coeff 2 = 1 ∧ f.coeff 3 = 0 ∧ f.coeff 4 = 0 := by
    have : f.coeff f.natDegree = f.leadingCoeff := coeff_natDegree
    have : f.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → f.coeff N = 0 := natDegree_le_iff_coeff_eq_zero
    simp_all
  have : e.coeff 2 = 1 ∧ e.coeff 3 = 0 ∧ e.coeff 4 = 0 := by
    have : e.coeff e.natDegree = e.leadingCoeff := coeff_natDegree
    have : e.natDegree ≤ 2 ↔ ∀ (N : ℕ), 2 < N → e.coeff N = 0 := natDegree_le_iff_coeff_eq_zero
    simp_all
  have h_prod: ∀ (n : ℕ), (e * f).coeff n = ∑ x ∈ Finset.antidiagonal n, e.coeff x.1 * f.coeff x.2
    := coeff_mul e f
  have : e.coeff 0 * f.coeff 0 = a^2 + b := by
    rw [←hg0, ←h_ftimese]
    apply (mul_coeff_zero e f).symm
  have : e.coeff 0 * f.coeff 1 + e.coeff 1 * f.coeff 0 = 0 := by
    rw [←hg1, ←h_ftimese]
    apply (mul_coeff_one e f).symm
  have : f.coeff 0 + e.coeff 1 * f.coeff 1 + e.coeff 0 = -2*a := by
    specialize h_prod 2
    simp [Finset.antidiagonal] at h_prod
    grind
  have : e.coeff 1 + f.coeff 1 = 0 := by
    specialize h_prod 3
    simp [Finset.antidiagonal] at h_prod
    simp_all
  if f.coeff 1 = 0 then
    right
    unfold IsSquare
    use f.coeff 0 + a
    have : e.coeff 0 = - f.coeff 0 - 2*a := by grind
    simp_all
    grind
  else
    left
    unfold IsSquare
    use f.coeff 0
    grind

include h in
lemma quadratic_algebraic_closure_no_i : ∀ (a : F), IsSquare a ∨ IsSquare (-a) := by
  intro a
  have : IsSquare (0 ^ 2 + a) ∨ IsSquare (-a) := by
    apply quadratic_algebraic_closure F K h 0 a
  simp_all
