module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
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
    have : x^p - x - iota a = 0 := by aesop
    grind only
  let pb := adjoin.powerBasis h_int
  let x₀ := pb.gen
  have h_pbdim := calc
    pb.dim = (minpoly F x).natDegree := adjoin.powerBasis_dim h_int
    _ = p := h_natdeg
  obtain ⟨y, hy4⟩ : ∃ y0 : F⟮x⟯, y0^p = y0 + iota a * x^(p-1) := by
    have hp1 := Nat.Prime.pos hp
    have := calc
      (minpoly F x).degree = p := (degree_eq_iff_natDegree_eq_of_pos hp1).mpr h_natdeg
      _ = ↑(finrank F K) := Nat.cast_inj.mpr hrank.symm
    have h := (Field.primitive_element_iff_minpoly_degree_eq F x).mpr this
    let pol := X ^ p - X - C (x ^ (p-1) * iota a)
    obtain ⟨y, hy⟩ : ∃ y : K, aeval y pol = 0 := by
      have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      have := Nat.ne_of_lt' hp1
      rw [←(artin_schreier_poly (x^(p-1) * iota a) hp).1] at this
      exact IsAlgClosed.exists_aeval_eq_zero K pol (degree_ne_of_natDegree_ne this)
    have := (IntermediateField.ext_iff.mp h y).mpr mem_top
    obtain ⟨y0, _⟩ : ∃ y0 : F⟮x⟯, y0 = y := CanLift.prf y this
    use y0
    have : y^p - y - x^(p-1) * iota a = 0 := by aesop
    grind only
  obtain ⟨y_rep, h_pb_rep_y01, h_pb_rep_y02⟩ := PowerBasis.exists_eq_aeval pb y
  rw [h_pbdim] at h_pb_rep_y01
  let c := y_rep.coeff (p-1)
  let yp_rep := (map (frobenius F p) y_rep).comp (X + C a)
  obtain ⟨h_y0rep1, h_y0rep2⟩ : yp_rep.natDegree < p ∧ yp_rep.coeff (p-1) = c ^ p :=
    linear_substitution a (Nat.Prime.one_lt hp) h_pb_rep_y01
  let y1p_rep := y_rep + monomial (p-1) a
  have h_matchcoeff :=
    let m := map (frobenius F p) y_rep
    let iota₀ := algebraMap F F⟮x⟯
    have := calc
      aeval x₀ (m.comp (X + C a)) = aeval (aeval x₀ (X + C a)) m := aeval_comp x₀
      _ = aeval (x₀ + iota₀ a) m := by rw [aeval_add x₀, aeval_X x₀, aeval_C x₀ a]
      _ = aeval (x₀ ^ p) m := by
        have : x₀ ^ p = x₀ + iota₀ a := SetLike.coe_eq_coe.mp h_rwx
        rw [this]
      _ = aeval (aeval x₀ (X ^ p)) m := by rw [aeval_X_pow x₀]
      _ = aeval x₀ (expand F p m) := (aeval_comp x₀).symm
      _ = aeval x₀ (y_rep ^ p) := by rw [←map_expand, map_frobenius_expand p y_rep]
      _ = (aeval x₀ y_rep) ^ p := map_pow (aeval x₀) y_rep p
      _ = y ^ p := by rw [h_pb_rep_y02]
    have :=
      have h7 : ∀ f : Polynomial F, aeval x f = (aeval x₀) f := by aesop
      have := calc
        aeval x (yp_rep - y1p_rep) = aeval x yp_rep - aeval x y1p_rep := aeval_sub x
        _ = 0 := by
          have h1 := calc
            aeval x yp_rep = aeval x₀ yp_rep := h7 yp_rep
            _ = y ^ p := by rw [this, IntermediateField.coe_pow F⟮x⟯ y p]
          have h2 := calc
            aeval x y1p_rep = aeval x y_rep + aeval x (monomial (p-1) a) := aeval_add x
            _ = aeval x₀ y_rep + aeval x (monomial (p-1) a) := by simp [h7 y_rep]
            _ = y + iota a * x ^ (p-1) := by rw [h_pb_rep_y02, aeval_monomial x]
          rw [h1, h2, sub_eq_zero.mpr hy4]
      have hdiv : (minpoly F x) ∣ (yp_rep - y1p_rep) := minpoly.dvd_iff.mpr this
      have := calc
        (yp_rep - y1p_rep).natDegree ≤ max yp_rep.natDegree y1p_rep.natDegree :=
          natDegree_sub_le yp_rep y1p_rep
        _ ≤ max yp_rep.natDegree (max y_rep.natDegree (monomial (p-1) a).natDegree) :=
          max_le_max_left yp_rep.natDegree (natDegree_add_le y_rep (monomial (p-1) a))
        _ < p :=
          have := calc
            (monomial (p - 1) a).natDegree ≤ p-1 := natDegree_monomial_le a
            _ < p := Nat.sub_one_lt_of_lt h_pb_rep_y01
          Nat.max_lt.mpr ⟨h_y0rep1, Nat.max_lt.mpr ⟨h_pb_rep_y01, this⟩⟩
        _ = (minpoly F x).natDegree := h_natdeg.symm
      have := eq_zero_of_dvd_of_natDegree_lt hdiv this
      sub_eq_zero.mp this
    ext_iff.mp this (p-1)
  have h_deg1 : (minpoly F x).natDegree = 1 := by
    have h_fieldeq := calc
      c^p - c = y_rep.coeff (p-1) + (monomial (p-1) a).coeff (p-1) - c := by
        rw [←h_y0rep2, h_matchcoeff, coeff_add y_rep (monomial (p-1) a) (p-1)]
      _ = (monomial (p-1) a).coeff (p-1) := by ring
      _ = a := coeff_monomial_same (p-1) a
    have : CharP K p := (Algebra.charP_iff F K p).mp hFp
    let x1 := x - iota c
    obtain ⟨n, hn⟩ :=
      have : Fact (Nat.Prime p) := fact_iff.mpr hp
      have fieldeq := calc
        x1^p = x^p - iota c ^ p := sub_pow_char x (iota c)
        _ = x + (iota (c^p) - iota c) - iota c ^ p := by
          have : iota (c^p - c) = iota (c^p) - iota c := algebraMap.coe_sub (c ^ p) c
          rw [h_rwx, ←h_fieldeq, this]
        _ = x1 := by grind
      (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr fieldeq)
    apply minpoly.natDegree_eq_one_iff.mpr
    use n + c
    aesop
  have := calc
    1 < p := Nat.Prime.one_lt hp
    _ = 1 := by rw [←h_natdeg, h_deg1]
  exact (lt_self_iff_false 1).mp this

include K hp hrank in
lemma finite_algebraic_closure_cyclic_quadratic : p = 2 := by
  have h_char := finite_algebraic_closure_cyclic_prime F K hp hrank
  have hK : (primitiveRoots (finrank F K) F).Nonempty := by
    let cyclo := cyclotomic p F
    have := calc
      cyclo.natDegree = p.totient := natDegree_cyclotomic p F
      _ = p - 1 := Nat.totient_prime hp
    obtain ⟨f, h_fmonic, hf1, h_divcyclo⟩ : ∃ f, f.Monic ∧ f.natDegree ∣ p ∧ f ∣ cyclo := by
      rw [←hrank]
      apply divisor_by_finrank
      rw [this]
      exact Nat.sub_ne_zero_of_lt (Nat.Prime.one_lt hp)
    have : f.degree = 1 := by
      have := Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree hf1
      cases this with
      | inl h => calc
        f.degree = f.natDegree := degree_eq_natDegree (Monic.ne_zero h_fmonic)
        _ = 1 := Nat.cast_eq_one.mpr h
      | inr =>
        have := Nat.Prime.pos hp
        have := natDegree_le_of_dvd h_divcyclo (cyclotomic_ne_zero p F)
        grind only
    obtain ⟨z, hz⟩ := exists_root_of_degree_eq_one this
    use z
    apply (mem_primitiveRoots finrank_pos).mpr
    rw [hrank]
    have : NeZero (p : F) :=
      have : ¬CharP F p := ringChar.eq_iff.mpr.mt h_char
      { out := (CharP.charP_iff_prime_eq_zero hp).mpr.mt this }
    exact isRoot_cyclotomic_iff.mp (IsRoot.dvd hz h_divcyclo)
  obtain ⟨a, _, h5⟩ : ∃ a, Irreducible (X ^ p - C a) ∧ IsSplittingField F K (X ^ p - C a) := by
    rw [←hrank]
    apply (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    (expose_names; refine ⟨inst_5, ?_⟩)
    have : Fact p.Prime := fact_iff.mpr hp
    have := IsGalois.card_aut_eq_finrank F K
    rw [hrank] at this
    exact isCyclic_of_prime_card this
  by_contra
  have h_irr: ∀ n, n ≠ 0 → (Irreducible (X ^ p ^ n - C a) ↔ ∀ b : F, b ^ p ≠ a) := by
    intro _ hn
    exact X_pow_sub_C_irreducible_iff_of_prime_pow hp this hn
  let pol := X ^ p ^ 2 - C a
  have h_irr2 :=
    have irr2 : Irreducible (X ^ p ^ 1 - C a) := by simp_all only [pow_one]
    have : 2 ≠ 0 := (Nat.zero_ne_add_one 1).symm
    (h_irr 2 this).mpr ((h_irr 1 Nat.one_ne_zero).mp irr2)
  have h13 : pol.natDegree = p ^ 2 := natDegree_X_pow_sub_C
  obtain ⟨f, _, h_fdeg, h_div⟩ : ∃ f, f.Monic ∧ f.natDegree ∣ p ∧ f ∣ pol := by
    rw [←hrank]
    apply divisor_by_finrank
    rw [h13]
    aesop
  have h_deg : f.natDegree = pol.natDegree := by
    have := divisor_of_irreducible_poly h_div h_irr2
    aesop
  have h := calc
    p < p * p := Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hp)
    _ = p^2 := by ring
    _ = f.natDegree := by rw [←h13, h_deg]
    _ ≤ p := Nat.le_of_dvd (Nat.Prime.pos hp) h_fdeg
  exact (lt_self_iff_false p).mp h
