module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.Relrank

public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField Polynomial UniqueFactorizationMonoid

lemma odd_irreducible_factor {F : Type} [Field F] {f : F[X]} (h : Odd f.natDegree) :
  ∃ g : F[X], Irreducible g ∧ g ∣ f ∧ Odd g.natDegree :=
  let S := factors f
  have h_prod := Associated.symm (factors_prod (ne_zero_of_natDegree_gt (Odd.pos h)))
  have : 0 ∉ S := by
    have := ne_zero_of_natDegree_gt (Odd.pos h)
    by_contra
    rw [Multiset.prod_eq_zero this] at h_prod
    simp_all only [associated_zero_iff_eq_zero]
  have ⟨g, hg1, hg2⟩ : ∃ g ∈ S, Odd g.natDegree := by
    have := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h_prod)
    by_contra
    let T := S.map natDegree
    have : ∀ t : ℕ, t ∈ T → Even t := by aesop
    have : 2 ∣ T.sum := Multiset.dvd_sum (fun x hx => Even.two_dvd (this x hx))
    grind only [= Nat.odd_iff, = natDegree_multiset_prod]
  ⟨g, irreducible_of_factor g hg1, dvd_of_mem_factors hg1, hg2⟩

lemma RealClosed_from_quadratic (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsAlgClosure F K] (h1 : ¬IsSquare (-1 : F))
    (h2 : ∃ i : K, -1 = i^2 ∧ F⟮i⟯ = ⊤) : IsRealClosed F := by
  have h_alg := IsAlgClosure.isAlgClosed F (K := K)
  have ⟨i, h2a, h2b⟩ := h2; symm at h2a
  have h_int := Algebra.IsIntegral.isIntegral i (R := F)
  have hi_pol : (minpoly F i).natDegree = 2 := by open minpoly in
    have : aeval i (X ^ 2 + C (1 : F)) = 0 := by aesop
    have := natDegree_le_of_dvd (dvd_iff.mpr this) (X_pow_add_C_ne_zero Nat.two_pos 1)
    have : (minpoly F i).natDegree ≠ 1 := by
      by_contra
      have ⟨i₀, _⟩ := natDegree_eq_one_iff.mp this
      have : (algebraMap F K) (i₀ ^ 2) = (algebraMap F K) (-1) := by grind
      have := (isSquare_iff_exists_sq (-1)).mpr.mt h1
      grind only [= map_pow, = map_neg, = map_one, = map_mul, = map_sub]
    grind only [natDegree_pos h_int, = natDegree_X_pow_add_C]
  have h_rank2 : Module.finrank F K = 2 := by
    rw [←finrank_bot', ←relfinrank_mul_finrank_top (OrderBot.bot_le F⟮i⟯), relfinrank_bot_left,
      adjoin.finrank h_int, hi_pol, finrank_eq_one_iff_eq_top.mpr h2b, Nat.mul_one]
  have issquare := quadratic_algebraic_closure F K h_rank2 0
  simp only [mul_zero, zero_add] at issquare
  have odd_deg : ∀ {f : F[X]}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    intro f h_odd
    have ⟨g, hg, h_div, h_oddg⟩ := odd_irreducible_factor h_odd
    have := Irreducible.natDegree_dvd_finrank hg (pol_splits F K g)
    rw [h_rank2] at this
    have := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two g.natDegree this
    have : g.natDegree = 1 := by grind
    have := (degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_succ 0)).mpr this
    have ⟨x, hx⟩ := exists_root_of_degree_eq_one this
    exact ⟨x, IsRoot.dvd hx h_div⟩
  have neg : ∀ x : F, 0 ≠ x → IsSquare x → ¬ IsSquare (-x) := by
    intro x hx hs
    by_contra
    have := IsSquare.div this hs; rw [neg_div_self hx.symm] at this
    contradiction
  have semi : IsSemireal F :=
    have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
      apply IsSumSq.rec'
      · exact IsSquare.zero
      · intro a b ha _ hb
        by_cases hb0 : 0 = b
        · simp [←hb0, ha]
        · have := neg b hb0 hb
          have ⟨y, _⟩ := ha
          have := quadratic_algebraic_closure F K h_rank2 y b
          simp_all
    isSemireal_iff_not_isSumSq_neg_one.mpr ((hssq (-1)).mt (neg 1 zero_ne_one IsSquare.one))
  exact { toIsSemireal := semi, isSquare_or_isSquare_neg :=
    issquare, exists_isRoot_of_odd_natDegree := odd_deg }
