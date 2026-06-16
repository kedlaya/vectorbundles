module

public import Mathlib.FieldTheory.Finite.Basic

public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

open IntermediateField IsAlgClosed Nat Polynomial

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) {p : ℕ} [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K] [IsGalois F K] (hp : Nat.Prime p)
    (hrank : Module.finrank F K = p) : ¬ ringChar F = p := by
  by_contra
  obtain ⟨a, x, ha⟩ := cyclic_char_p_as_artin_schreier F K hp hrank this
  have hFp := ringChar.of_eq this
  have : ExpChar F p := ExpChar.prime hp
  have h_natdeg := (artin_schreier_poly a hp).1
  rw [←ha] at h_natdeg
  have hp1 := Prime.pos hp
  have : IsAlgClosed F⟮x⟯ := by
    have := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_natdeg
    rw [←hrank] at this
    have h1 : (⊤ : IntermediateField F K) ≃ₐ[F] K := topEquiv
    rw [←(Field.primitive_element_iff_minpoly_degree_eq F x).mpr this] at h1
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    exact of_ringEquiv K ↥F⟮x⟯ h1.symm
  have h_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  let pb := adjoin.powerBasis h_int
  let x₀ := pb.gen
  obtain ⟨y, hy4⟩ : ∃ y0 : F⟮x⟯, y0^p = y0 + a * x₀^(p-1) := by
    let pol := X ^ p - X - C (x₀ ^ (p-1) * a)
    have := Nat.ne_of_lt' hp1
    rw [←(artin_schreier_poly (x₀^(p-1) * a) hp).1] at this
    obtain ⟨y, hy⟩ := exists_aeval_eq_zero F⟮x⟯ pol (degree_ne_of_natDegree_ne this)
    use y
    have : y^p - y - x₀ ^ (p-1) * a = 0 := by aesop
    grind only
  let iota := algebraMap F K
  have h_pbdim := adjoin.powerBasis_dim h_int
  rw [h_natdeg] at h_pbdim
  obtain ⟨y_rep, h_pb_rep_y01, h_pb_rep_y02⟩ := PowerBasis.exists_eq_aeval pb y
  rw [h_pbdim] at h_pb_rep_y01
  let c := y_rep.coeff (p-1)
  let y1p_rep := y_rep + monomial (p-1) a
  have h_rwx : x^p = x + iota a := by
    have := minpoly.aeval F x
    have : x^p - x - iota a = 0 := by aesop
    grind only
  have h_matchcoeff : y1p_rep.coeff (p-1) = c^p := by
    let lin := X + C a
    have hlin : lin.natDegree = 1 := natDegree_X_add_C a
    let m := map (frobenius F p) y_rep
    let yp_rep := m.comp lin
    have hf3 : m.natDegree = y_rep.natDegree := natDegree_map (frobenius F p)
    have h_deg2 : yp_rep.natDegree = m.natDegree * lin.natDegree := natDegree_comp
    rw [hlin, hf3, mul_one] at h_deg2
    have :=
      let iota₀ := algebraMap F F⟮x⟯
      have : x₀ ^ p = x₀ + iota₀ a := SetLike.coe_eq_coe.mp h_rwx
      have h_eval := calc
        aeval x₀ yp_rep = aeval (aeval x₀ lin) m := aeval_comp x₀
        _ = aeval (x₀ + iota₀ a) m := by rw [aeval_add x₀, aeval_X x₀, aeval_C x₀ a]
        _ = aeval (aeval x₀ (X ^ p)) m := by rw [←this, aeval_X_pow x₀]
        _ = aeval x₀ (expand F p m) := (aeval_comp x₀).symm
        _ = aeval x₀ (y_rep ^ p) := by rw [←map_expand, map_frobenius_expand p y_rep]
        _ = y ^ p := by rw [map_pow (aeval x₀) y_rep p, h_pb_rep_y02]
      have : aeval x (yp_rep - y1p_rep) = 0 := by
        have h7 : ∀ f : Polynomial F, aeval x f = (aeval x₀) f := by aesop
        rw [h7, aeval_sub x₀, aeval_add x₀, h_eval, ←h_pb_rep_y02, aeval_monomial x₀, hy4]
        aesop
      have hdiv := minpoly.dvd_iff.mpr this
      have := calc
        (yp_rep - y1p_rep).natDegree ≤ max yp_rep.natDegree y1p_rep.natDegree :=
            natDegree_sub_le yp_rep y1p_rep
        _ ≤ max y_rep.natDegree (monomial (p-1) a).natDegree :=
            max_le_iff.mpr ⟨le_max_of_le_left (le_of_eq h_deg2),
              natDegree_add_le y_rep (monomial (p-1) a)⟩
        _ ≤ max y_rep.natDegree (p-1) := max_le_max_left y_rep.natDegree (natDegree_monomial_le a)
        _ < p := max_lt_iff.mpr ⟨h_pb_rep_y01, sub_one_lt_of_lt hp1⟩
        _ = (minpoly F x).natDegree := h_natdeg.symm
      eq_zero_of_dvd_of_natDegree_lt hdiv this
    rw [←sub_eq_zero.mp this]
    by_cases hf0 : y_rep.natDegree = p-1
    · have : yp_rep.coeff (yp_rep.natDegree) = m.coeff m.natDegree *
        lin.leadingCoeff ^ m.natDegree := leadingCoeff_comp (ne_zero_of_eq_one hlin)
      rw [leadingCoeff_X_add_C a, hf3, h_deg2, hf0] at this
      aesop
    · have hf1 : y_rep.natDegree < p-1 := by grind only
      have h1 := coeff_eq_zero_of_natDegree_lt (lt_of_eq_of_lt h_deg2 hf1)
      have h2 : c = 0 := coeff_eq_zero_of_natDegree_lt hf1
      rw [h1, h2]
      exact (zero_pow (expChar_ne_zero F p)).symm
  have h_range : x ∈ (algebraMap F K).range := by
    have h_fieldeq := calc
      c^p - c = y_rep.coeff (p-1) + (monomial (p-1) a).coeff (p-1) - c := by
        rw [←h_matchcoeff, coeff_add y_rep (monomial (p-1) a) (p-1)]
      _ = (monomial (p-1) a).coeff (p-1) := by ring
      _ = a := coeff_monomial_same (p-1) a
    have : CharP K p := (Algebra.charP_iff F K p).mp hFp
    obtain ⟨n, hn⟩ :=
      have := fact_iff.mpr hp
      have : iota (c^p - c) = iota (c^p) - iota c := algebraMap.coe_sub (c ^ p) c
      have := calc
        (x - iota c)^p = x^p - iota c ^ p := sub_pow_char x (iota c)
        _ = x + (iota (c^p) - iota c) - iota c ^ p := by rw [h_rwx, ←h_fieldeq, this]
        _ = x - iota c := by grind
      (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr this)
    have : iota (n + c) = x := by aesop
    use n + c
  have := Prime.one_lt hp
  rw [←h_natdeg, minpoly.natDegree_eq_one_iff.mpr h_range] at this
  contradiction
