module

public import Mathlib.FieldTheory.Finite.Basic
public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) {p : ℕ} [Field F] [Field K]
    [Algebra F K] [IsAlgClosure F K] [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : ¬CharP F p := by
  open IntermediateField IsAlgClosed Nat Polynomial Subfield in
  have hp1 := Prime.pos hp; have hp1' := Prime.one_lt hp; have := fact_iff.mpr hp
  have := FiniteDimensional.of_finrank_pos (by rw [hrank]; exact hp1)
  by_contra
  have ⟨a, x, ha⟩ := cyclic_char_p_as_param F K hp hrank
  have h_natdeg := (artinSchreierPoly_isMonicOfDegree a hp1').1; rw [←ha] at h_natdeg
  have h_int := Algebra.IsIntegral.isIntegral x (R := F)
  let pb := adjoin.powerBasis h_int; let iota := algebraMap F K
  have ⟨y, hy⟩ : ∃ y : F⟮x⟯, y^p = y + a * pb.gen^(p-1) := by
    have : IsAlgClosed F⟮x⟯ := by
      have h1 := topEquiv (F := F) (E := K)
      have := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_natdeg; rw [←hrank] at this
      rw [←(Field.primitive_element_iff_minpoly_degree_eq F x).mpr this] at h1
      have := IsAlgClosure.isAlgClosed F (K := K); exact of_ringEquiv K ↥F⟮x⟯ h1.symm
    let t := pb.gen ^ (p-1) * a; let pol := X ^ p - X - C t
    have := (artinSchreierPoly_isMonicOfDegree t hp1').1.trans_ne hp1.ne'
    have ⟨y, hy⟩ := exists_aeval_eq_zero F⟮x⟯ pol (degree_ne_of_natDegree_ne this)
    use y
    simp_all only [map_pow, aeval_sub, coe_aeval_eq_eval, aeval_X, eval_C, pol]; grind only
  have ⟨y_rep, h_pb1, _⟩ := PowerBasis.exists_eq_aeval pb y
  rw [adjoin.powerBasis_dim h_int, h_natdeg] at h_pb1
  let c := y_rep.coeff (p-1); let y1p_rep := y_rep + monomial (p-1) a
  have : x^p - x - iota a = 0 := by have := minpoly.aeval F x; aesop
  have h_matchcoeff : y1p_rep.coeff (p-1) = c^p := by
    have hlin := natDegree_X_add_C a
    let m := map (frobenius F p) y_rep; let yp_rep := m.comp (X + C a)
    have h_deg2 : yp_rep.natDegree = y_rep.natDegree := by
      rw [natDegree_comp, hlin, natDegree_map, mul_one]
    have h : yp_rep = y1p_rep := by
      have h : aeval x y_rep = y := by aesop
      have hx : x^p = x + iota a := by grind only
      have h_eval := calc
        aeval x yp_rep = aeval (aeval x ((X : F[X]) ^ p)) m := by
          rw [aeval_comp, aeval_add, aeval_X, aeval_C, ←hx, aeval_X_pow]
        _ = aeval x (expand F p m) := (aeval_comp x).symm
      have hdiv : minpoly F x ∣ yp_rep - y1p_rep := by
        apply minpoly.dvd_iff.mpr
        rw [aeval_sub, aeval_add, h_eval, ←map_expand, map_frobenius_expand, map_pow, h,
          ←IntermediateField.coe_pow F⟮x⟯ y p, hy, aeval_monomial, sub_eq_zero]; rfl
      refine sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdiv ?_)
      grind only [!natDegree_add_le, !natDegree_sub_le, !natDegree_monomial_le, =max_def]
    by_cases hf0 : y_rep.natDegree = p-1
    · have := leadingCoeff_comp (ne_zero_of_eq_one hlin) (p := m)
      rw [leadingCoeff, leadingCoeff, leadingCoeff_X_add_C, h_deg2] at this; aesop
    · have h2 : c = 0 := coeff_eq_zero_of_natDegree_lt (by grind)
      rw [←h, coeff_eq_zero_of_natDegree_lt (by grind), h2, zero_pow (by grind)]
  have : x ∈ (algebraMap F K).range := by
    have : c^p = c + a := by rw [←h_matchcoeff, coeff_add y_rep, coeff_monomial_same]
    have := (Algebra.charP_iff F K p).mp ‹CharP F p›
    have : (x - iota c)^p = x - iota c := by grind [sub_pow_char, add_sub_cancel_left]
    have ⟨n, _⟩ := (mem_bot_iff_intCast p K).mp ((mem_bot_iff_pow_eq_self K p).mpr this)
    use n + c; aesop
  rw [←h_natdeg, minpoly.natDegree_eq_one_iff.mpr this] at hp1'; contradiction
