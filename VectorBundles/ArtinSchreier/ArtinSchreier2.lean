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
  obtain ⟨a, x, ha⟩ := cyclic_char_p_as_artin_schreier F K hp hrank this
  have hFp := ringChar.of_eq this
  have : ExpChar F p := ExpChar.prime hp
  have h_int : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h_natdeg := (artin_schreier_poly a hp).1
  rw [←ha] at h_natdeg
  let iota := algebraMap F K
  have h_rwx : x^p = x + iota a := by
    have := minpoly.aeval F x
    simp [ha, aeval, aevalEquiv] at this
    grind only
  let pb := adjoin.powerBasis h_int
  let x₀ := pb.gen
  have h_pbdim := calc
    pb.dim = (minpoly F x).natDegree := adjoin.powerBasis_dim h_int
    _ = p := h_natdeg
  obtain ⟨y, hy4⟩ : ∃ y0 : F⟮x⟯, y0^p = y0 + iota a * x^(p-1) := by
    have hp1 := Nat.Prime.pos hp
    let pol := X ^ p -  X -  C (x ^ (p-1) * iota a)
    obtain ⟨y, hy⟩ : ∃ y : K, aeval y pol = 0 := by
      have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      apply IsAlgClosed.exists_aeval_eq_zero K pol
      have := (artin_schreier_poly (x^(p-1) * iota a) hp).1
      calc
      pol.degree = p := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr this
      _ ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp)
    have : y^p - y - x^(p-1) * iota a = 0 := by aesop
    have := calc
      (minpoly F x).degree = p := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_natdeg
      _ = ↑(finrank F K) := Nat.cast_inj.mpr hrank.symm
    have := (Field.primitive_element_iff_minpoly_degree_eq F x).mpr this
    have := (IntermediateField.ext_iff.mp this y).mpr mem_top
    obtain ⟨y0, _⟩ : ∃ y0 : F⟮x⟯, y0 = y := CanLift.prf y this
    use y0
    grind only
  obtain ⟨y_rep, h_pb_rep_y01, h_pb_rep_y02⟩ := PowerBasis.exists_eq_aeval pb y
  rw [h_pbdim] at h_pb_rep_y01
  let c := y_rep.coeff (p-1)
  let yp_rep := (map (frobenius F p) y_rep).comp (X + C a)
  obtain ⟨h_y0rep1, h_y0rep2⟩ : yp_rep.natDegree < p ∧ yp_rep.coeff (p-1) = c ^ p :=
    linear_substitution a (Nat.Prime.one_lt hp) h_pb_rep_y01
  let y1p_rep := y_rep + monomial (p-1) a
  have h_matchcoeff : yp_rep.coeff (p-1) = y1p_rep.coeff (p-1) :=
    let frob := frobenius F p
    let m := map frob
    let lin := X + C a
    let exp := expand F p
    let iota₀ := algebraMap F F⟮x⟯
    have h_power := calc
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
      have h7 : ∀ f : Polynomial F, aeval x f = ((algebraMap F⟮x⟯ K) ∘ (aeval x₀)) f := by
        intro f
        aesop
      have := calc
        aeval x (yp_rep - y1p_rep) = aeval x yp_rep - aeval x y1p_rep := aeval_sub x
        _ = 0 := by
          have h5 := calc
            aeval x yp_rep = aeval x₀ yp_rep := h7 yp_rep
            _ = ↑ (y ^ p) := by rw [h_power]
            _ = y ^ p := IntermediateField.coe_pow F⟮x⟯ y p
          have h4 := calc
            aeval x y1p_rep = aeval x y_rep + aeval x (monomial (p-1) a) := aeval_add x
            _ = aeval x₀ y_rep + aeval x (monomial (p-1) a) := by simp [h7 y_rep]
            _ = y + aeval x (monomial (p-1) a) := by rw [h_pb_rep_y02]
            _ = y + iota a * x ^ (p-1) := add_left_cancel_iff.mpr (aeval_monomial x)
          rw [h5, h4]
          exact sub_eq_zero.mpr hy4
      have h3 : (minpoly F x) ∣ (yp_rep - y1p_rep) := minpoly.dvd_iff.mpr this
      have h1 : yp_rep.natDegree < (minpoly F x).natDegree :=
        Nat.lt_of_lt_of_eq h_y0rep1 h_pbdim.symm
      have h2 := calc
        y1p_rep.natDegree ≤ max y_rep.natDegree (monomial (p-1) a).natDegree :=
          Polynomial.natDegree_add_le y_rep (monomial (p-1) a)
        _ < p := by
          refine Nat.max_lt.mpr ⟨h_pb_rep_y01, ?_⟩
          calc
          (monomial (p - 1) a).natDegree ≤ p-1 := natDegree_monomial_le a
          _ < p := Nat.sub_one_lt_of_lt h_pb_rep_y01
        _ = (minpoly F x).natDegree := by rw [h_natdeg]
      congruence_low_degree h3 h1 h2 (minpoly.monic h_int)
    ext_iff.mp h (p-1)
  have h_deg1 : (minpoly F x).natDegree = 1 := by
    have h_fieldeq := calc
      c^p - c = yp_rep.coeff (p-1) - c := by rw [h_y0rep2]
      _ = y1p_rep.coeff (p-1) - c := by rw [h_matchcoeff]
      _ = y_rep.coeff (p-1) + (monomial (p-1) a).coeff (p-1) - c := by
        rw [coeff_add y_rep (monomial (p-1) a) (p - 1)]
      _ = (monomial (p-1) a).coeff (p-1) := by ring
      _ = a := coeff_monomial_same (p-1) a
    have : Fact (Nat.Prime p) := fact_iff.mpr hp
    have : CharP K p := (Algebra.charP_iff F K p).mp hFp
    let x1 := x - iota c
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ↑n = x1 :=
      have fieldeq := calc
        x1^p = x^p - iota c ^ p := sub_pow_char x (iota c)
        _ = x + iota a - iota c ^ p := sub_left_inj.mpr h_rwx
        _ = x + iota (c^p - c) - iota c ^ p := by rw [h_fieldeq]
        _ = x + (iota (c^p) - iota c) - iota c ^ p := by
          have hsub : iota (c^p - c) = iota (c^p) - iota c := algebraMap.coe_sub (c ^ p) c
          rw [hsub]
        _ = x + (iota c ^ p - iota c) - iota c ^ p := by simp
        _ = x1 := by ring
      have : x1 ∈ (⊥ : Subfield K) := (Subfield.mem_bot_iff_pow_eq_self K p).mpr fieldeq
      (mem_bot_iff_intCast p K).mp this
    apply minpoly.natDegree_eq_one_iff.mpr
    use n + c
    aesop
  have := calc
    1 < p := Nat.Prime.one_lt hp
    _ = (minpoly F x).natDegree := h_natdeg.symm
    _ = 1 := h_deg1
  exact (lt_self_iff_false 1).mp this

include K p hp hrank in
lemma finite_algebraic_closure_cyclic_quadratic : p = 2 := by
  have h_char := finite_algebraic_closure_cyclic_prime F K hp hrank
  have hK : (primitiveRoots (finrank F K) F).Nonempty := by
    let cyclo := cyclotomic p F
    have := calc
      cyclo.natDegree = p.totient := natDegree_cyclotomic p F
      _ = p - 1 := Nat.totient_prime hp
    obtain ⟨f, h_fmonic, hf1, h_divcyclo⟩ : ∃ (f : Polynomial F), f.Monic
      ∧ f.natDegree ∣ finrank F K ∧ f ∣ cyclo := by
      apply divisor_by_finrank
      simp_all only [ne_eq]
      refine Nat.sub_ne_zero_of_lt ?_
      exact Nat.Prime.one_lt hp
    rw [hrank] at hf1
    have : f.natDegree = 1 := by
      have : f.natDegree = 1 ∨ f.natDegree = p :=
        Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree hf1
      cases this with
      | inl h => exact h
      | inr =>
        have : p > 0 := Nat.Prime.pos hp
        simp_all only [dvd_refl]
        have : f.natDegree ≤ cyclo.natDegree :=
          natDegree_le_of_dvd h_divcyclo (cyclotomic_ne_zero p F)
        grind only
    obtain ⟨z, hz⟩ : ∃ z : F, f.IsRoot z := by
      refine exists_root_of_degree_eq_one ?_
      calc
      f.degree = f.natDegree := degree_eq_natDegree (Monic.ne_zero h_fmonic)
      _ = 1 := Nat.cast_eq_one.mpr this
    apply Finset.nonempty_def.mpr
    use z
    apply (mem_primitiveRoots finrank_pos).mpr
    rw [hrank]
    have : NeZero (p: F) :=
      have : ¬CharP F p := ringChar.eq_iff.mpr.mt h_char
      { out := (CharP.charP_iff_prime_eq_zero hp).mpr.mt this }
    have : cyclo.IsRoot z := IsRoot.dvd hz h_divcyclo
    exact isRoot_cyclotomic_iff.mp this
  obtain ⟨a, _, h5⟩ : ∃ a : F, Irreducible (X ^ p - C a) ∧ IsSplittingField F K (X ^ p - C a) := by
    rw [←hrank]
    apply (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    (expose_names; refine ⟨inst_5, ?_⟩)
    have : Fact p.Prime := fact_iff.mpr hp
    have := calc
      Nat.card Gal(K/F) = finrank F K := IsGalois.card_aut_eq_finrank F K
      _ = p := hrank
    exact isCyclic_of_prime_card this
  by_contra
  have h_irr: ∀ n : ℕ, n ≠ 0 → (Irreducible (X ^ p ^ n - C a) ↔ ∀ (b : F), b ^ p ≠ a) := by
    intro n hn
    exact X_pow_sub_C_irreducible_iff_of_prime_pow hp this hn
  let pol := X ^ p ^ 2 - C a
  have h_irr2 :=
    have irr2 : Irreducible (X ^ p ^ 1 - C a) := by simp_all only [pow_one]
    have : 2 ≠ 0 := (Nat.zero_ne_add_one 1).symm
    (h_irr 2 this).mpr ((h_irr 1 Nat.one_ne_zero).mp irr2)
  have h13 : pol.natDegree = p ^ 2 := natDegree_X_pow_sub_C
  obtain ⟨f, hf, h_fdeg, h_div⟩ : ∃ (f : Polynomial F), f.Monic ∧ f.natDegree ∣ finrank F K
    ∧ f ∣ pol := by
    apply divisor_by_finrank
    rw [h13]
    aesop
  have h_deg : f.natDegree = pol.natDegree := by
    have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree :=
      divisor_of_irreducible_poly h_div h_irr2
    aesop
  have h := calc
    p < p * p := Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hp)
    _ = p^2 := by ring
    _ = pol.natDegree := h13.symm
    _ = f.natDegree := h_deg.symm
    _ ≤ finrank F K := Nat.le_of_dvd finrank_pos h_fdeg
    _ = p := hrank
  exact (lt_self_iff_false p).mp h
