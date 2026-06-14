module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.Relrank
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField Module Polynomial

lemma odd_irreducible_factor {F : Type} [Field F] {f: Polynomial F} (h : Odd f.natDegree) :
  ∃ g : Polynomial F, Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
  open UniqueFactorizationMonoid in
  let S := factors f
  have h_prod := Associated.symm (factors_prod (ne_zero_of_natDegree_gt (Odd.pos h)))
  have h0S : 0 ∉ S := by
    by_contra
    rw [Multiset.prod_eq_zero this] at h_prod
    have := ne_zero_of_natDegree_gt (Odd.pos h)
    simp_all only [associated_zero_iff_eq_zero]
  obtain ⟨g, hg1, hg2⟩ : ∃ g ∈ S, Odd g.natDegree := by
    have := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h_prod)
    by_contra
    let T := S.map natDegree
    have := natDegree_multiset_prod S h0S
    have : 2 ∣ T.sum := by
      apply Multiset.dvd_sum
      intro x hx
      have : ∀ t : ℕ, t ∈ T → Even t := by aesop
      exact Even.two_dvd (this x hx)
    grind only [= Nat.odd_iff]
  use g
  exact ⟨irreducible_of_factor g hg1, dvd_of_mem_factors hg1, hg2⟩

lemma RealClosed_from_quadratic (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsAlgClosure F K] (h1 : ∀ i : F, -1 ≠ i^2)
    (h2 : ∃ i : K, -1 = i^2 ∧ F⟮i⟯ = ⊤) : IsRealClosed F := by
  have h_alg : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  obtain ⟨i, h2a, h2b⟩ := h2
  symm at h2a
  have h_int : IsIntegral F i := Algebra.IsIntegral.isIntegral i
  have hi_pol : (minpoly F i).natDegree = 2 := by open minpoly in
    have : aeval i (X ^ 2 + C (1 : F)) = 0 := by aesop
    have := natDegree_le_of_dvd (dvd_iff.mpr this) (X_pow_add_C_ne_zero Nat.two_pos 1)
    rw [natDegree_X_pow_add_C] at this
    have : (minpoly F i).natDegree ≠ 1 := by
      by_contra
      obtain ⟨i₀, hi₀⟩ := natDegree_eq_one_iff.mp this
      have : (algebraMap F K) (i₀ ^ 2) = (algebraMap F K) (-1) := by grind
      grind only [= map_pow, = map_neg, = map_one, = map_mul, = map_sub]
    grind only [natDegree_pos h_int]
  have h_rank2 := calc
    finrank F K = finrank (⊥: IntermediateField F K) K := finrank_bot'.symm
    _ = relfinrank ⊥ F⟮i⟯ * finrank F⟮i⟯ K :=
      (relfinrank_mul_finrank_top (OrderBot.bot_le F⟮i⟯)).symm
    _ = 2 := by rw [relfinrank_bot_left F⟮i⟯, adjoin.finrank h_int, hi_pol,
      finrank_eq_one_iff_eq_top.mpr h2b, Nat.mul_one 2]
  have issquare := quadratic_algebraic_closure F K h_rank2 0
  simp only [mul_zero, zero_add] at issquare
  have odd_deg : ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    intro f h_odd
    obtain ⟨g, hg, h_div, h_oddg⟩ := odd_irreducible_factor h_odd
    have := Irreducible.natDegree_dvd_finrank hg (IsAlgClosed.splits (map (algebraMap F K) g))
    rw [h_rank2] at this
    have := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two g.natDegree this
    have : g.natDegree = 1 := by grind
    have := (degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_succ 0)).mpr this
    obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one this
    use x
    exact IsRoot.dvd hx h_div
  have semi : IsSemireal F := by
    have hs : ∀ x y : F, ∃ z : F, x * x + y * y = z * z := by
      intro x y
      have hssq := quadratic_algebraic_closure F K h_rank2 x (y * y)
      cases hssq with
      | inl hssq => exact hssq
      | inr hssq =>
        by_cases y = 0
        · use x
          grind only
        · obtain ⟨r, _⟩ := hssq
          grind only [h1 (r/y)]
    have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
      intro x hx
      induction hx with
      | zero =>
        use 0
        simp only [mul_zero]
      | sq_add y _ hz =>
          rcases hz with ⟨z, hz⟩
          subst hz
          exact hs y z
    rw [isSemireal_iff_not_isSumSq_neg_one]
    by_contra
    obtain ⟨r, _⟩ := IsSquare.exists_sq (-1) (hssq (-1) this)
    grind only [h1 r]
  exact
  { toIsSemireal := semi, isSquare_or_isSquare_neg := issquare,
    exists_isRoot_of_odd_natDegree := odd_deg }
