module

public import Mathlib.FieldTheory.Finite.Basic
public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) {p : ℕ} [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K] [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : ¬ ringChar F = p := by
  open IntermediateField IsAlgClosed Nat Polynomial in
  by_contra
  obtain ⟨a, x, ha⟩ := cyclic_char_p_as_artin_schreier F K hp hrank this
  have hFp := ringChar.of_eq this
  have := ExpChar.prime hp (R := F)
  have hp1 := Prime.pos hp
  have hp1' := Prime.one_lt hp
  have h_natdeg := (artin_schreier_poly a hp1').1
  rw [←ha] at h_natdeg
  have h_int := Algebra.IsIntegral.isIntegral x (R := F)
  let pb := adjoin.powerBasis h_int
  have : IsAlgClosed F⟮x⟯ := by
    have := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_natdeg
    rw [←hrank] at this
    have h1 := topEquiv (F := F) (E := K)
    rw [←(Field.primitive_element_iff_minpoly_degree_eq F x).mpr this] at h1
    have := IsAlgClosure.isAlgClosed F (K := K)
    exact of_ringEquiv K ↥F⟮x⟯ h1.symm
  obtain ⟨y, hy4⟩ : ∃ y0 : F⟮x⟯, y0^p = y0 + a * pb.gen^(p-1) := by
    let pol := X ^ p - X - C (pb.gen ^ (p-1) * a)
    have := Nat.ne_of_lt' hp1
    rw [←(artin_schreier_poly (pb.gen ^ (p-1) * a) hp1').1] at this
    obtain ⟨y, hy⟩ := exists_aeval_eq_zero F⟮x⟯ pol (degree_ne_of_natDegree_ne this)
    use y
    simp_all [pol]
    grind only
  have h_pbdim := adjoin.powerBasis_dim h_int
  rw [h_natdeg] at h_pbdim
  obtain ⟨y_rep, h_pb1, _⟩ := PowerBasis.exists_eq_aeval pb y
  let c := y_rep.coeff (p-1)
  let y1p_rep := y_rep + monomial (p-1) a
  let iota := algebraMap F K
  have := minpoly.aeval F x
  have : x^p - x - iota a = 0 := by aesop
  have h_matchcoeff : y1p_rep.coeff (p-1) = c^p := by
    let lin := X + C a
    have hlin := natDegree_X_add_C a
    let m := map (frobenius F p) y_rep
    let yp_rep := m.comp lin
    have hf3 := natDegree_map (frobenius F p) (p := y_rep)
    have h_deg2 := natDegree_comp (p := m) (q := lin)
    have h := by
      have h7 : aeval x y_rep = y := by aesop
      have h_rwx : x^p = x + iota a := by grind only
      have h_eval := calc
        aeval x yp_rep = aeval (x + iota a) m := by rw [aeval_comp, aeval_add, aeval_X, aeval_C]
        _ = aeval (aeval x ((X : F[X]) ^ p)) m := by rw [←h_rwx, aeval_X_pow]
        _ = aeval x (expand F p m) := (aeval_comp x).symm
      have hdiv : minpoly F x ∣ yp_rep - y1p_rep := by
        apply minpoly.dvd_iff.mpr
        rw [aeval_sub, aeval_add, ←sub_sub, h_eval, ←map_expand, map_frobenius_expand, map_pow,
          h7, ←IntermediateField.coe_pow F⟮x⟯ y p, hy4, aeval_monomial, sub_eq_zero]
        exact sub_eq_of_eq_add' rfl
      refine sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdiv ?_)
      rw [h_natdeg]
      grind [natDegree_add_le, natDegree_sub_le, natDegree_monomial_le]
    by_cases hf0 : y_rep.natDegree = p-1
    · have := leadingCoeff_comp (ne_zero_of_eq_one hlin) (p := m)
      rw [leadingCoeff, leadingCoeff, leadingCoeff_X_add_C, hf3, h_deg2, hf0] at this
      aesop
    · have hf1 : y_rep.natDegree < p-1 := by grind only
      have h2 : c = 0 := coeff_eq_zero_of_natDegree_lt hf1
      rw [hlin, hf3, mul_one] at h_deg2
      rw [←h, coeff_eq_zero_of_natDegree_lt (lt_of_eq_of_lt h_deg2 hf1), h2, zero_pow]
      exact expChar_ne_zero F p
  have h_range : x ∈ (algebraMap F K).range := by
    have : c^p - c = a := by
      rw [←h_matchcoeff, coeff_add y_rep, add_sub_cancel_left, coeff_monomial_same]
    have := (Algebra.charP_iff F K p).mp hFp
    obtain ⟨n, hn⟩ :=
      have := fact_iff.mpr hp
      have : (x - iota c)^p = x - iota c := by grind [sub_pow_char]
      (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr this)
    have : iota (n + c) = x := by aesop
    use n + c
  have := Prime.one_lt hp
  rw [←h_natdeg, minpoly.natDegree_eq_one_iff.mpr h_range] at this
  contradiction
