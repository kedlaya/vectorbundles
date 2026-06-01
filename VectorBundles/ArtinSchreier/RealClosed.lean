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
      have h_eval : aeval i pol = 0 := by
        calc
        aeval i pol = aeval i ((X : Polynomial F) ^ 2) + aeval i (C (1 : F)) := aeval_add i
        _ = i^2 + aeval i (C (1 : F)) := by rw [aeval_X_pow i]
        _ = i^2 + 1 := by
          refine (add_right_inj (i^2)).mpr ?_
          simp only [map_one]
        _ = 0 := add_eq_zero_iff_eq_neg.mpr h2a
      have h_div : i_pol ∣ pol := minpoly.dvd_iff.mpr h_eval
      have h_mon : pol.Monic := by
        refine monic_X_pow_add_C 1 ?_
        simp
      have h_leq : i_pol.natDegree ≤ pol.natDegree := by
        apply natDegree_le_of_dvd h_div
        exact Monic.ne_zero h_mon
      have h_poldeg : pol.natDegree = 2 := natDegree_X_pow_add_C
      le_of_le_of_eq h_leq h_poldeg
    have h_deg0 : 0 < i_pol.natDegree := minpoly.natDegree_pos h_int
    have : i_pol.natDegree ≠ 1 :=
      let iota := algebraMap F K
      have hi : ¬ i ∈ iota.range := by
        by_contra
        obtain ⟨j, hj⟩ := this
        have : j^2 = -1 := by
          have : iota (j ^ 2) = iota (-1) := by grind
          have : Function.Injective iota := FaithfulSMul.algebraMap_injective F K
          grind
        simp_all only
      minpoly.natDegree_eq_one_iff.mp.mt hi
    grind
  have h_rank2 : finrank F K = 2 := by
    have h_rel : relfinrank ⊥ F⟮i⟯ = 2 := by
      calc
      relfinrank ⊥ F⟮i⟯ = finrank F F⟮i⟯ := relfinrank_bot_left F⟮i⟯
      _ = i_pol.natDegree := adjoin.finrank h_int
      _ = 2 := hi_pol
    calc
    finrank F K = finrank (⊥: IntermediateField F K) K := finrank_bot'.symm
    _ = relfinrank ⊥ F⟮i⟯ * finrank F⟮i⟯ K :=
      (relfinrank_mul_finrank_top (OrderBot.bot_le F⟮i⟯)).symm
    _ = 2 * finrank F⟮i⟯ K := by rw [h_rel]
    _ = 2 * 1 := by rw [finrank_eq_one_iff_eq_top.mpr h2b]
    _ = 2 := by simp
  have issquare: ∀ (x : F), IsSquare x ∨ IsSquare (-x) :=
    quadratic_algebraic_closure_no_i F K h_rank2
  have odd_deg : ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    have h_ftog : ∀ f : Polynomial F, Irreducible f → f.natDegree ≤ 2 := by
      intro f h_irr
      have hg : ∃ (g : Polynomial F), g.Monic ∧ g.natDegree ∣ finrank F K ∧ g ∣ f := by
        apply divisor_by_finrank
        refine Nat.ne_zero_iff_zero_lt.mpr ?_
        exact Irreducible.natDegree_pos h_irr
      obtain ⟨g, _, h_gdeg, hdiv⟩ := hg
      have : g.natDegree ≤ 2 := by
        calc
        g.natDegree ≤ finrank F K := Nat.le_of_dvd finrank_pos h_gdeg
        _ = 2 := h_rank2
      rw [h_rank2] at h_gdeg
      have hg1 : g.natDegree = 0 ∨ g.natDegree = f.natDegree :=
        divisor_of_irreducible_poly hdiv h_irr
      cases hg1
      · aesop
      · simp_all
    intro f h_odd
    have hg : ∃ g : Polynomial F, Irreducible g ∧ g ∣ f ∧ Odd g.natDegree :=
      odd_irreducible_factor h_odd
    obtain ⟨g, hg, h_div, h_oddg⟩ := hg
    have h_x : ∃ x : F, g.IsRoot x := by
      refine exists_root_of_degree_eq_one ?_
      have h_natgdeg : g.natDegree = 1 := by
        have : g.natDegree ≤ 2 := h_ftog g hg
        grind
      calc
      g.degree = g.natDegree := degree_eq_natDegree (Irreducible.ne_zero hg)
      _ = 1 := Nat.cast_eq_one.mpr h_natgdeg
    obtain ⟨x, h_x⟩ := h_x
    use x
    exact IsRoot.dvd h_x h_div
  have semi: IsSemireal F := by
    have hs: ∀ (x y: F), ∃ z : F, x^2 + y^2 = z^2 := by
      intro x y
      have hssq : IsSquare (x ^ 2 + y^2) ∨ IsSquare (-y^2) :=
        quadratic_algebraic_closure F K h_rank2 x (y^2)
      unfold IsSquare at hssq
      cases hssq with
      | inl hssq =>
        obtain ⟨z, hssq⟩ := hssq
        use z
        grind
      | inr hssq =>
        by_cases y = 0
        · use x
          grind
        · obtain ⟨r, hssq⟩ := hssq
          specialize h1 (r/y)
          grind
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
    have h2 : IsSquare (-1 : F) := hssq (-1) this
    unfold IsSquare at h2
    obtain ⟨r, h2⟩ := h2
    specialize h1 r
    grind
  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := issquare,
       exists_isRoot_of_odd_natDegree := odd_deg }
