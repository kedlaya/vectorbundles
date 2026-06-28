module

public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) {p : ℕ} [Field F] [Field K]
    [Algebra F K] [IsAlgClosure F K] [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : ¬CharP F p := by
  open IntermediateField IsAlgClosed Nat Polynomial Subfield in
  have hp1 := Prime.pos hp; have hp1' := Prime.one_lt hp; have := fact_iff.mpr hp
  by_contra
  have ⟨a, x, ha⟩ := cyclic_char_p_as_param F K hp hrank
  have h_deg := (artinSchreierPoly_isMonicOfDegree a hp1').1; rw [←ha] at h_deg
  have h_int := Algebra.IsIntegral.isIntegral x (R := F)
  let pb := adjoin.powerBasis h_int; let iota := algebraMap F K
  have ⟨y, hy⟩ : ∃ y : F⟮x⟯, ↑y^p - (↑y + (iota a) * pb.gen^(p-1)) = 0 := by
    have : IsAlgClosed F⟮x⟯ := by
      have := FiniteDimensional.of_finrank_pos (by rw [hrank]; exact hp1)
      have h1 := (topEquiv (F := F) (E := K)).symm
      have := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_deg; rw [←hrank] at this
      rw [←(Field.primitive_element_iff_minpoly_degree_eq F x).mpr this] at h1
      have := IsAlgClosure.isAlgClosed F (K := K); exact of_ringEquiv K ↥F⟮x⟯ h1
    let t := a * pb.gen ^ (p-1)
    have := (artinSchreierPoly_isMonicOfDegree t hp1').1.trans_ne hp1.ne'
    have ⟨y, hy⟩ := exists_aeval_eq_zero F⟮x⟯ (X ^ p - X - C t) (degree_ne_of_natDegree_ne this)
    rw [coe_aeval_eq_eval, eval_sub, eval_sub, eval_pow, eval_X, eval_C, sub_sub, sub_eq_zero]
      at hy; use y; rw [←IntermediateField.coe_pow]; aesop
  have ⟨y_rep, h_pb1, h_pb2⟩ := PowerBasis.exists_eq_aeval pb y
  let c := y_rep.coeff (p-1); have : c^p = c + a := by
    rw [adjoin.powerBasis_dim h_int, h_deg] at h_pb1
    let m := map (frobenius F p) y_rep; let yp_rep := m.taylor a
    have hd := (natDegree_taylor m a).trans (natDegree_map _)
    let y1p_rep := y_rep + monomial (p-1) a; have h : yp_rep = y1p_rep := by
      have h_eval : aeval x yp_rep = aeval x (expand F p m) := by
        have := minpoly.aeval F x; have hx : x^p - x - iota a = 0 := by aesop
        rw [sub_sub, sub_eq_zero] at hx; simp [yp_rep, taylor_apply, aeval_comp, hx, iota]
      have hdiv : aeval x (yp_rep - y1p_rep) = 0 := by
        have h : aeval x y_rep = y := by aesop
        rw [aeval_sub, h_eval, ←map_expand, map_frobenius_expand, map_pow, aeval_add, h,
          aeval_monomial]; exact hy
      refine sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt (minpoly.dvd_iff.mpr hdiv) ?_)
      grind only [!natDegree_add_le, !natDegree_sub_le, !natDegree_monomial_le, =max_def]
    have : yp_rep.coeff (p-1) = c^p := by
      by_cases hf0 : y_rep.natDegree = p-1
      · rw [←hf0, ←hd, ←leadingCoeff, leadingCoeff_taylor, leadingCoeff_map, leadingCoeff]; aesop
      · subst c; rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt, zero_pow]
        repeat grind only
    rw [←this, h, coeff_add y_rep, coeff_monomial_same]
  have hirr := minpoly.irreducible h_int; rw [←h_deg] at hp1'
  have := Irreducible.not_isRoot_of_natDegree_ne_one hirr hp1'.ne' (x := c); simp_all
