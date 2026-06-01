module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.Polynomials
public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField Module Polynomial

variable (F : Type) (K : Type) {p : ℕ} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] [IsGalois F K] (hp: Nat.Prime p) (hrank: finrank F K = p)

include K hp hrank in
lemma finite_algebraic_closure_cyclic_prime : ¬ ringChar F = p := by
  by_contra
  have : ∃ (a : F), ∃ (x : K), minpoly F x = X ^ p -  X - C a :=
    cyclic_char_p_as_artin_schreier F K hp hrank this
  obtain ⟨a, x, ha⟩ := this
  have hp1 : 0 < p := Nat.Prime.pos hp
  have hFp : CharP F p := ringChar.of_eq this
  have : ExpChar F p := ExpChar.prime hp
  have h_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  let aspol := X ^ p -  X -  C a
  have h_natdeg: aspol.natDegree = p := (artin_schreier_poly a hp).1
  have h_minpoly : minpoly F x = aspol := by rw [ha]
  let iota := algebraMap F K
  have h_rwx : x^p = x + iota a := by
    have h_evalx : aspol.aeval x = 0 := by
      rw [← h_minpoly]
      exact minpoly.aeval F x
    simp [aspol, aeval, aevalEquiv] at h_evalx
    grind
  let pb := adjoin.powerBasis h_int
  let x₀ := pb.gen
  have h_pbdim : pb.dim = p := by
    calc
    pb.dim = (minpoly F x).natDegree := adjoin.powerBasis_dim h_int
    _ = aspol.natDegree := by rw [ha]
    _ = p := h_natdeg
  have : ∃ y0 : F⟮x⟯, y0^p = y0 + x^(p-1) * iota a := by
    let pol := X ^ p -  X -  C (x ^ (p-1) * iota a)
    have : ∃ y : K, aeval y pol = 0 := by
      have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      have : pol.natDegree = p := (artin_schreier_poly (x^(p-1) * iota a) hp).1
      have : pol.degree = p :=
        (degree_eq_iff_natDegree_eq_of_pos hp1).mpr this
      apply IsAlgClosed.exists_aeval_eq_zero K pol
      rw [this]
      exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp)
    obtain ⟨y, hy⟩ := this
    have : (minpoly F x).degree = ↑(finrank F K) := by
      calc
      (minpoly F x).degree = aspol.degree := by rw [ha]
      _ = p := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_natdeg
      _ = ↑(finrank F K) := Nat.cast_inj.mpr hrank.symm
    have : F⟮x⟯ = ⊤ :=
      (Field.primitive_element_iff_minpoly_degree_eq F x).mpr this
    have : y ∈ F⟮x⟯ := (IntermediateField.ext_iff.mp this y).mpr mem_top
    have : ∃ y0 : F⟮x⟯, y0 = y := CanLift.prf y this
    obtain ⟨y0, _⟩ := this
    have : y^p - y - x^(p-1) * iota a = 0 := by aesop
    use y0
    grind
  obtain ⟨y, hy4⟩ := this
  have : ∃ (f : Polynomial F), f.natDegree < pb.dim ∧ y = aeval x₀ f :=
    PowerBasis.exists_eq_aeval pb y
  obtain ⟨y_rep, h_pb_rep_y01, h_pb_rep_y02⟩ := this
  let c := y_rep.coeff (p-1)
  let yp_rep := (map (frobenius F p) y_rep).comp (X + C a)
  have : yp_rep.natDegree < p ∧ yp_rep.coeff (p-1) = c ^ p := by
    rw [h_pbdim] at h_pb_rep_y01
    exact linear_substitution a (Nat.Prime.one_lt hp) h_pb_rep_y01
  obtain ⟨h_y0rep1, h_y0rep2⟩ := this
  let y1p_rep := y_rep + X ^ (p-1) *  C a
  have h_matchcoeff : yp_rep.coeff (p-1) = y1p_rep.coeff (p-1) :=
    let frob := frobenius F p
    let m := map frob
    let lin := X + C a
    have h_power: aeval x₀ ((m y_rep).comp lin) = y ^ p := by
      let exp := expand F p
      let iota₀ := algebraMap F F⟮x⟯
      calc
      aeval x₀ ((m y_rep).comp lin) = aeval (aeval x₀ lin) (m y_rep) := aeval_comp x₀
      _ = aeval (x₀ + iota₀ a) (m y_rep) := by rw [aeval_add x₀, aeval_X x₀, aeval_C x₀ a]
      _ = aeval (x₀^p) (m y_rep) := by
        have h_rwx_bp : x₀ ^ p = x₀ + iota₀ a := SetLike.coe_eq_coe.mp h_rwx
        rw [h_rwx_bp]
      _ = aeval (aeval x₀ (X ^ p)) (m y_rep) := by rw [aeval_X_pow x₀]
      _ = aeval x₀ ((m y_rep).comp (X ^ p)) := (aeval_comp x₀).symm
      _ = aeval x₀ (exp (m y_rep)) := by rfl
      _ = aeval x₀ (y_rep ^ p) := by rw [← map_expand, map_frobenius_expand p y_rep]
      _ = (aeval x₀ y_rep) ^ p := map_pow (aeval x₀) y_rep p
      _ = y ^ p := by rw [h_pb_rep_y02]
    have h : yp_rep = y1p_rep :=
      have : aeval x (yp_rep - y1p_rep) = 0 := by
        calc
        aeval x (yp_rep - y1p_rep) = aeval x yp_rep - aeval x y1p_rep := aeval_sub x
        _ = 0 := by
          have h7 : ∀ f : Polynomial F, aeval x f = ((algebraMap F⟮x⟯ K) ∘ (aeval x₀)) f := by
            intro f
            aesop
          have h5 : aeval x yp_rep = y ^ p := by
            calc
            aeval x yp_rep = aeval x₀ yp_rep := h7 yp_rep
            _ = ↑ (y ^ p) := by rw [h_power]
            _ = y ^ p := IntermediateField.coe_pow F⟮x⟯ y p
          have h4 : aeval x y1p_rep = y + x^(p-1) * iota a := by
            calc
            aeval x y1p_rep = aeval x y_rep + aeval x (X^(p-1) * (C a)) := aeval_add x
            _ = aeval x₀ y_rep + aeval x (X^(p-1) * (C a)) := by simp [h7 y_rep]
            _ = y + aeval x (X^(p-1) * (C a)) := by rw [h_pb_rep_y02]
            _ = y + aeval x (monomial (p-1) a) := by simp
            _ = y + iota a * x ^ (p-1) := add_left_cancel_iff.mpr (aeval_monomial x)
            _ = y + x ^ (p-1) * iota a := by ring
          rw [h5, h4]
          exact sub_eq_zero.mpr hy4
      have h3 : (minpoly F x) ∣ (yp_rep - y1p_rep) := minpoly.dvd_iff.mpr this
      have h1 : yp_rep.natDegree < (minpoly F x).natDegree :=
        Nat.lt_of_lt_of_eq h_y0rep1 h_pbdim.symm
      have h2 : y1p_rep.natDegree < (minpoly F x).natDegree :=
        calc
        y1p_rep.natDegree ≤ max y_rep.natDegree (C a * X ^ (p - 1)).natDegree := by
          apply natDegree_add_le_of_le
          · exact Nat.le_refl y_rep.natDegree
          · apply Nat.le_of_eq
            refine Monic.natDegree_mul_comm ?_ (C a)
            exact monic_X_pow (p - 1)
        _ < p := by
          refine Nat.max_lt.mpr ?_
          constructor
          · exact Nat.lt_of_lt_of_eq h_pb_rep_y01 h_pbdim
          · refine (Nat.le_sub_one_iff_lt ?_).mp ?_
            · exact Nat.zero_lt_of_lt h_y0rep1
            · apply natDegree_C_mul_X_pow_le a (p-1)
        _ = (minpoly F x).natDegree := by rw [h_minpoly, h_natdeg]
      congruence_low_degree h3 h1 h2 (minpoly.monic h_int)
    ext_iff.mp h (p-1)
  have h_deg1 : (minpoly F x).natDegree = 1 := by
    have h_fieldeq: c^p - c = a := by
      calc
      c^p - c = yp_rep.coeff (p-1) - c := by rw [h_y0rep2]
      _ = y1p_rep.coeff (p-1) - c := by rw [h_matchcoeff]
      _ = y_rep.coeff (p-1) + (X ^ (p-1) * C a).coeff (p-1) - c := by
        rw [coeff_add y_rep (X ^ (p-1) * C a) (p - 1)]
      _ = (X ^ (p-1) * C a).coeff (p-1) := by ring
      _ = a := by
        have : ((monomial (p-1)) a).coeff (p-1) = if (p-1) = (p-1) then a else 0 :=
          coeff_monomial
        unfold monomial at this
        simp
    have : Fact (Nat.Prime p) := fact_iff.mpr hp
    have : CharP K p := (Algebra.charP_iff F K p).mp hFp
    let x1 := x - iota c
    have : ∃ n : ℤ, ↑n = x1 :=
      have fieldeq : x1^p = x1 := by
        calc
        x1^p = (x - iota c)^p := by rfl
        _ = x^p - iota c ^ p := sub_pow_char x (iota c)
        _ = x + iota a - iota c ^ p := sub_left_inj.mpr h_rwx
        _ = x + iota (c^p - c) - iota c ^ p := by rw [h_fieldeq]
        _ = x + iota (c^p) - iota c - iota c ^ p := by
          have hsub : iota (c^p - c) = iota (c^p) - iota c := algebraMap.coe_sub (c ^ p) c
          rw [hsub]
          ring
        _ = x + iota c ^ p - iota c - iota c ^ p := by simp
        _ = x1 := by ring
      have h_bot : x1 ∈ (⊥ : Subfield K) := (Subfield.mem_bot_iff_pow_eq_self K p).mpr fieldeq
      (mem_bot_iff_intCast p K).mp h_bot
    obtain ⟨n, hn⟩ := this
    apply minpoly.natDegree_eq_one_iff.mpr
    use n + c
    aesop
  have : 1 < 1 := by
    calc
    1 < p := Nat.Prime.one_lt hp
    _ = aspol.natDegree := h_natdeg.symm
    _ = (minpoly F x).natDegree := (natDegree_eq_of_degree_eq (congrArg degree ha)).symm
    _ = 1 := h_deg1
  exact (lt_self_iff_false 1).mp this

include K p hp hrank in
lemma finite_algebraic_closure_cyclic_quadratic : p = 2 := by
  have h_char : ¬ ringChar F = p :=
    finite_algebraic_closure_cyclic_prime F K hp hrank
  have hK : (primitiveRoots (finrank F K) F).Nonempty := by
    let cyclo := cyclotomic p F
    have : cyclo.natDegree = p - 1 := by
      calc
      cyclo.natDegree = p.totient := natDegree_cyclotomic p F
      _ = p - 1 := Nat.totient_prime hp
    have : ∃ (f : Polynomial F), f.Monic ∧ f.natDegree ∣ finrank F K ∧ f ∣ cyclo := by
      apply divisor_by_finrank
      simp_all only [ne_eq]
      refine Nat.sub_ne_zero_of_lt ?_
      exact Nat.Prime.one_lt hp
    obtain ⟨f, h_fmonic, hf1, h_divcyclo⟩ := this
    rw [hrank] at hf1
    have : f.natDegree = 1 := by
      have : f.natDegree = 1 ∨ f.natDegree = p :=
        Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree hf1
      cases this with
      | inl h => exact h
      | inr =>
        have : p > 0 := Nat.Prime.pos hp
        simp_all only [dvd_refl]
        have : f.natDegree ≤ cyclo.natDegree := by
          refine natDegree_le_of_dvd h_divcyclo ?_
          exact cyclotomic_ne_zero p F
        grind
    have : ∃ z : F, f.IsRoot z := by
      refine exists_root_of_degree_eq_one ?_
      calc
      f.degree = f.natDegree := degree_eq_natDegree (Monic.ne_zero h_fmonic)
      _ = 1 := Nat.cast_eq_one.mpr this
    obtain ⟨z, hz⟩ := this
    refine Finset.nonempty_def.mpr ?_
    use z
    have : IsPrimitiveRoot z p :=
      have : NeZero (p: F) :=
        have h2 : ¬CharP F p := by
          by_contra
          have : ringChar F = p := ringChar.eq F p
          simp_all
        { out := (CharP.charP_iff_prime_eq_zero hp).mpr.mt h2 }
      have : cyclo.IsRoot z := IsRoot.dvd hz h_divcyclo
      isRoot_cyclotomic_iff.mp this
    subst p
    exact (mem_primitiveRoots finrank_pos).mpr this
  let G := Gal(K/F)
  have h1 : ∃ (a : F), Irreducible (X ^ p - C a) ∧ IsSplittingField F K (X ^ p - C a) := by
    rw [←hrank]
    apply (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    have : IsCyclic G :=
      have : Fact p.Prime := fact_iff.mpr hp
      have : Nat.card G = p := by
        calc
        Nat.card G = finrank F K := IsGalois.card_aut_eq_finrank F K
        _ = p := hrank
      isCyclic_of_prime_card this
    (expose_names; exact ⟨inst_5, this⟩)
  obtain ⟨a, h4, h5⟩ := h1
  by_contra
  have h_irr: ∀ (n : ℕ), n ≠ 0 → (Irreducible (X ^ p ^ n - C a) ↔ ∀ (b : F), b ^ p ≠ a) := by
    intro n hn
    exact X_pow_sub_C_irreducible_iff_of_prime_pow hp this hn
  let pol := X ^ p ^ 2 - C a
  have h13 : pol.natDegree = p ^ 2 := natDegree_X_pow_sub_C
  have : ∃ (f : Polynomial F), f.Monic ∧ f.natDegree ∣ Module.finrank F K ∧ f ∣ pol := by
    apply divisor_by_finrank
    rw [h13]
    aesop
  obtain ⟨f, hf, h_fdeg, h_div⟩ := this
  have h_deg : f.natDegree = pol.natDegree := by
    have : Irreducible pol :=
      have h6 : ∀ (b : F), b ^ p ≠ a :=
        have h9 : Irreducible (X ^ p ^ 1 - C a) := by simp_all only [pow_one]
        (h_irr 1 Nat.one_ne_zero).mp h9
      have : 2 ≠ 0 := (Nat.zero_ne_add_one 1).symm
      (h_irr 2 this).mpr h6
    have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree :=
      divisor_of_irreducible_poly h_div this
    aesop
  have h : p < p := by
    calc
      p < p * p := Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hp)
      _ = p^2 := by ring
      _ = pol.natDegree := h13.symm
      _ = f.natDegree := h_deg.symm
      _ ≤ finrank F K := Nat.le_of_dvd finrank_pos h_fdeg
      _ = p := hrank
  exact (lt_self_iff_false p).mp h
