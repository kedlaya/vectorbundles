module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) {p : ℕ} [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K] [IsGalois F K] (hp : Nat.Prime p)
  (hrank : Module.finrank F K = p) : p = 2 ∧ ∃ a : F, ¬ IsSquare a := by
  open Nat Polynomial in
  have h_char := finite_algebraic_closure_cyclic_prime F K hp hrank
  have hK : (primitiveRoots (Module.finrank F K) F).Nonempty := by
    have hp1 := Prime.pos hp
    let cyclo := cyclotomic p F
    have := Std.ne_of_lt (degree_cyclotomic_pos p F hp1)
    obtain ⟨f, h_fmonic, hf1, h_divcyclo⟩ := divisor_by_finrank F K this.symm
    rw [hrank] at *
    have := Prime.eq_one_or_self_of_dvd hp f.natDegree hf1
    have : f.degree = 1 := by cases this with
      | inl h => exact (degree_eq_iff_natDegree_eq_of_pos one_pos).mpr h
      | inr h =>
        have := natDegree_le_of_dvd h_divcyclo (cyclotomic_ne_zero p F)
        rw [h, natDegree_cyclotomic p F, totient_prime hp] at this
        grind only
    obtain ⟨z, hz⟩ := exists_root_of_degree_eq_one this
    use z
    have : ¬CharP F p := ringChar.eq_iff.mpr.mt h_char
    have : NeZero (p : F) := { out := (CharP.charP_iff_prime_eq_zero hp).mpr.mt this }
    exact (mem_primitiveRoots hp1).mpr (isRoot_cyclotomic_iff.mp (IsRoot.dvd hz h_divcyclo))
  obtain ⟨a, h2, _⟩ : ∃ a, Irreducible (X ^ p - C a) ∧ IsSplittingField F K (X ^ p - C a) := by
    have h := (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    have := fact_iff.mpr hp
    have := IsGalois.card_aut_eq_finrank F K
    rw [hrank] at *
    (expose_names; exact h ⟨inst_5, isCyclic_of_prime_card this⟩)
  have hp : p = 2 := by
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    by_contra
    have h_irr: ∀ n, n ≠ 0 → (Irreducible (X ^ p ^ n - C a) ↔ ∀ b : F, b ^ p ≠ a) := by
      intro _ hn
      exact X_pow_sub_C_irreducible_iff_of_prime_pow hp this hn
    have : Irreducible (X ^ p ^ 1 - C a) := by simp_all only [pow_one]
    have := (h_irr 2 (zero_ne_add_one 1).symm).mpr ((h_irr 1 one_ne_zero).mp this)
    let pol := map (algebraMap F K) (X ^ p ^ 2 - C a)
    have := Irreducible.natDegree_dvd_finrank this (IsAlgClosed.splits pol)
    rw [natDegree_X_pow_sub_C, hrank] at this
    simp_all only [not_pos_pow_dvd, Prime.one_lt hp, one_lt_two]
  refine ⟨hp, ?_⟩
  use a
  by_contra
  obtain ⟨c, hc⟩ := IsSquare.exists_sq a this
  have : eval c (X ^ 2 - C a) = 0 := by simp [eval_sub, eval_X_pow 2, eval_C, hc]
  rw [hp] at hrank h2
  have := degree_eq_one_of_irreducible_of_root h2 (IsRoot.def.mpr this)
  have := degree_X_pow_sub_C two_pos a
  aesop
