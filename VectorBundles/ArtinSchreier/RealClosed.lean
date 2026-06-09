module

public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.Relrank

public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField Module Polynomial

lemma RealClosed_from_quadratic (F : Type) (K : Type) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsAlgClosure F K] (h1 : ∀ i : F, i^2 ≠ -1)
    (h2 : ∃ i : K, i^2 = -1 ∧ F⟮i⟯ = ⊤) : IsRealClosed F := by
  have h_alg : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  obtain ⟨i, h2a, h2b⟩ := h2
  have h_int : IsIntegral F i := Algebra.IsIntegral.isIntegral i
  let i_pol := minpoly F i
  have hi_pol : i_pol.natDegree = 2 := by
    have : i_pol.natDegree ≤ 2 :=
      let pol := X ^ 2 + C (1 : F)
      have : aeval i pol = 0 := by aesop
      have h_div := minpoly.dvd_iff.mpr this
      calc
      i_pol.natDegree ≤ pol.natDegree :=
        natDegree_le_of_dvd h_div (X_pow_add_C_ne_zero Nat.two_pos 1)
      _ = 2 := natDegree_X_pow_add_C
    have : 0 < i_pol.natDegree := minpoly.natDegree_pos h_int
    have : i_pol.natDegree ≠ 1 :=
      let iota := algebraMap F K
      have hi : ¬ i ∈ iota.range := by
        by_contra
        obtain ⟨j, hj⟩ := this
        have : j^2 = -1 := by
          have : iota (j ^ 2) = iota (-1) := by grind only [= map_pow, = map_neg, = map_one]
          have : Function.Injective iota := FaithfulSMul.algebraMap_injective F K
          grind only
        simp_all only
      minpoly.natDegree_eq_one_iff.mp.mt hi
    grind only
  have h_rank2 :=
    have h_rel := calc
      relfinrank ⊥ F⟮i⟯ = finrank F F⟮i⟯ := relfinrank_bot_left F⟮i⟯
      _ = i_pol.natDegree := adjoin.finrank h_int
      _ = 2 := hi_pol
    calc
    finrank F K = finrank (⊥: IntermediateField F K) K := finrank_bot'.symm
    _ = relfinrank ⊥ F⟮i⟯ * finrank F⟮i⟯ K :=
      (relfinrank_mul_finrank_top (OrderBot.bot_le F⟮i⟯)).symm
    _ = 2 * 1 := by rw [h_rel, finrank_eq_one_iff_eq_top.mpr h2b]
    _ = 2 := by simp
  have issquare := quadratic_algebraic_closure_no_i F K h_rank2
  have odd_deg : ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    intro f h_odd
    obtain ⟨g, hg, h_div, h_oddg⟩ := odd_irreducible_factor h_odd
    obtain ⟨x, h_x⟩ : ∃ x : F, g.IsRoot x := by
      apply exists_root_of_degree_eq_one
      have h_natgdeg : g.natDegree = 1 := by
        have : g.natDegree ≤ 2 := by
          obtain ⟨h, _, h_gdeg, hdiv⟩ : ∃ h : Polynomial F, h.Monic
            ∧ h.natDegree ∣ finrank F K ∧ h ∣ g := by
            apply divisor_by_finrank
            exact Nat.ne_zero_iff_zero_lt.mpr (Irreducible.natDegree_pos hg)
          cases divisor_of_irreducible_poly hdiv hg with
          | inl => aesop
          | inr h1 => calc
            g.natDegree = h.natDegree := h1.symm
            _ ≤ finrank F K := Nat.le_of_dvd finrank_pos h_gdeg
            _ = 2 := h_rank2
        grind only [= Nat.odd_iff]
      exact (Polynomial.degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_succ 0)).mpr h_natgdeg
    use x
    exact IsRoot.dvd h_x h_div
  have semi: IsSemireal F := by
    have hs: ∀ x y: F, ∃ z : F, x^2 + y^2 = z^2 := by
      intro x y
      have hssq := quadratic_algebraic_closure F K h_rank2 x (y^2)
      unfold IsSquare at hssq
      cases hssq with
      | inl hssq =>
        obtain ⟨z, _⟩ := hssq
        use z
        grind only
      | inr hssq =>
        by_cases y = 0
        · use x
          grind only
        · obtain ⟨r, _⟩ := hssq
          specialize h1 (r/y)
          grind => ring
    have hssq: ∀ x : F, IsSumSq x → IsSquare x := by
      intro x hx
      unfold IsSquare
      induction hx with
      | zero =>
        use 0
        simp only [mul_zero]
      | sq_add y _ hz =>
          rcases hz with ⟨z, hz⟩
          subst hz
          obtain ⟨r, hr⟩ := hs y z
          use r
          ring_nf
          exact hr
    rw [isSemireal_iff_not_isSumSq_neg_one]
    by_contra
    have h2 := hssq (-1) this
    unfold IsSquare at h2
    obtain ⟨r, _⟩ := h2
    specialize h1 r
    grind only
  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := issquare,
       exists_isRoot_of_odd_natDegree := odd_deg }
