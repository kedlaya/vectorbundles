module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Relrank
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField
open Module

variable (F : Type) (K : Type) [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]

lemma finite_algebraic_closure_cyclic_quadratic {p : ℕ}
  (hp: Nat.Prime p) (hrank: finrank F K = p) (hgal: IsGalois F K): p = 2 := by
  have h_char : ¬ ringChar F = p :=
    finite_algebraic_closure_cyclic_prime F K p hp hrank hgal
  have hK : (primitiveRoots (finrank F K) F).Nonempty := by
    let cyclo := Polynomial.cyclotomic p F
    have _ : cyclo.degree = p.totient := Polynomial.degree_cyclotomic p F
    have _ : p.totient = p - 1 := Nat.totient_prime hp
    have h_cycloroot : ∃ y : K, Polynomial.aeval y cyclo = 0 := by
      have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      refine IsAlgClosed.exists_aeval_eq_zero K cyclo ?_
      simp_all
      refine Nat.sub_ne_zero_of_lt ?_
      exact Nat.Prime.one_lt hp
    obtain ⟨y, h_cycloroot⟩ := h_cycloroot
    let f := minpoly F y
    have _ : f.natDegree ∣ finrank F K := by
      refine minpoly.degree_dvd ?_
      exact Algebra.IsIntegral.isIntegral y
    have h_divcyclo : f ∣ cyclo := minpoly.dvd_iff.mpr h_cycloroot
    have _ : f.natDegree ≤ cyclo.natDegree := by
      (expose_names; refine Polynomial.natDegree_le_of_dvd h_divcyclo ?_)
      exact Polynomial.cyclotomic_ne_zero p F
    have _ : f.natDegree = 1 := by
      have _ : f.natDegree ∣ p := by simp_all
      have hfd : f.natDegree = 1 ∨ f.natDegree = p := by
        (expose_names; exact Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree h_4)
      cases hfd
      · simp_all
      · exfalso
        simp_all
        have _ : cyclo.natDegree = p - 1 := by
          (expose_names; exact Polynomial.natDegree_eq_of_degree_eq_some h)
        simp_all
        have _ : p > 0 := Nat.Prime.pos hp
        grind
    have hz : ∃ z : F, f.IsRoot z := by
      refine Polynomial.exists_root_of_degree_eq_one ?_
      have _ : f.degree = f.natDegree := by
        refine Polynomial.degree_eq_natDegree ?_
        exact minpoly.ne_zero_of_finite F y
      simp_all
    obtain ⟨z, hz⟩ := hz
    have hprim : IsPrimitiveRoot z p := by
      have hnz : NeZero (p: F) := by
        have hnon : Nontrivial F := Field.toSemifield.toCommGroupWithZero.toNontrivial
        have h1 : (p : F) = 0 → CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr
        have h2 : ¬CharP F p := by
          by_contra
          have _ : ringChar F = p := ringChar.eq F p
          simp_all
        have _ : (p : F) ≠ 0 := Ne.symm (Ne.symm fun a => h2 (h1 a))
        (expose_names; exact { out := h_5 })
      have h_cycloroot : cyclo.IsRoot z := Polynomial.IsRoot.dvd hz h_divcyclo
      exact Polynomial.isRoot_cyclotomic_iff.mp h_cycloroot
    refine Finset.nonempty_def.mpr ?_
    use z
    refine (mem_primitiveRoots ?_).mpr ?_
    · exact finrank_pos
    · subst p
      exact hprim
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    calc
      Nat.card G = finrank F K := IsGalois.card_aut_eq_finrank F K
      _ = p := hrank
  have h_cyc : IsCyclic G := by
    have _ : Fact p.Prime := fact_iff.mpr hp
    exact isCyclic_of_prime_card h_ord
  by_contra
  have hpp : p^2 > p := by
    have h : p > 1 := by
      exact Nat.Prime.one_lt hp
    calc
      p^2 = p*p := by ring
      _ > p := Nat.lt_mul_self_iff.mpr h
  have h1 :
    ∃ (a : F), Irreducible (Polynomial.X ^ finrank F K - Polynomial.C a)
          ∧ Polynomial.IsSplittingField F K (Polynomial.X ^ finrank F K - Polynomial.C a) := by
    apply (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    constructor
    exact hgal
    exact h_cyc
  obtain ⟨a, h4, h5⟩ := h1
  have h_irr: ∀ (n : ℕ), n ≠ 0 → (Irreducible (Polynomial.X ^ p ^ n - Polynomial.C a) ↔ ∀ (b : F), b ^ p ≠ a) := by
    intro n hn
    apply X_pow_sub_C_irreducible_iff_of_prime_pow hp
    push Not at this
    exact this
    exact hn
  have h6 : ∀ (b : F), b ^ p ≠ a := by
    have h7 : 1 ≠ 0 := Nat.one_ne_zero
    obtain ⟨h8, _⟩ := h_irr 1 h7
    have h9 : Irreducible (Polynomial.X ^ p ^ 1 - Polynomial.C a) := by
      simp_all
    exact h8 h9
  let pol := Polynomial.X ^ p ^ 2 - Polynomial.C a
  have h10 : Irreducible pol := by
    have h11 : 2 ≠ 0 := Ne.symm (Nat.zero_ne_add_one 1)
    obtain ⟨_, h12⟩ := h_irr 2 h11
    exact h12 h6
  have h13 : pol.natDegree = p^2 := Polynomial.natDegree_X_pow_sub_C
  have h14 : pol.natDegree = pol.degree :=
    (Polynomial.degree_eq_natDegree (Irreducible.ne_zero h10)).symm
  have hc : ∃ c : K, Polynomial.aeval c pol = 0 := by
    have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ pol ?_
    exact FaithfulSMul.algebraMap_injective F K
    simp_all
    have h : pol.degree > 0 := by
      refine Polynomial.natDegree_pos_iff_degree_pos.mp ?_
      simp_all
      refine Nat.pow_pos ?_
      exact Nat.Prime.pos hp
    exact ne_of_gt h
  obtain ⟨c, hc⟩ := hc
  let f := minpoly F c
  have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  have h_fmon: f.Monic := minpoly.monic h_int
  have h_div : f ∣ pol := minpoly.dvd_iff.mpr hc
  have h_f : f.natDegree > 0 := minpoly.natDegree_pos h_int
  have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree := by
    refine divisor_of_irreducible_poly f pol h_div ?_
    subst pol
    apply h10
  cases h_deg
  · simp_all
  · have _ : f.natDegree ≤ finrank F K := minpoly.natDegree_le c
    simp_all
    rename_i hp2
    have h : p < p := by
      calc
        p < p^2 := hpp
        _ ≤ p := hp2
    exact (lt_self_iff_false p).mp h

lemma finite_separable_algebraic_closure_with_i
    [Algebra.IsSeparable F K]
      (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  have _ : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_5, to_normal := IsAlgClosure.normal F K })
  let G := Gal(K/F)
  let d := Nat.card G
  have hG : d = 1 := by
    by_contra
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp1a⟩ := hp
    have hp2 : Fact (Nat.Prime p) := fact_iff.mpr hp1
    have hg : ∃ g : G, orderOf g = p := by
      have h : d = Fintype.card G := Nat.card_eq_fintype_card
      apply exists_prime_orderOf_dvd_card
      rw [h] at hp1a
      exact hp1a
    obtain ⟨g, hg⟩ := hg
    let H := Subgroup.zpowers g
    let E := IntermediateField.fixedField H
    have h_ekrank : finrank E K = p := by
      calc
        finrank E K = Nat.card H := IntermediateField.finrank_fixedField_eq_card H
        _ = orderOf g := Nat.card_zpowers g
        _ = p := hg
    have _ : IsAlgClosure E K :=
      { isAlgClosed := IsAlgClosure.isAlgClosed F,
        isAlgebraic := IntermediateField.isAlgebraic_tower_top }
    have hgal: IsGalois E K := IsGalois.tower_top_intermediateField E
    have hp_is2 : p = 2 :=
      finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank hgal
    rw [hp_is2] at hp1
    rw [hp_is2] at h_ekrank
    have h_char2 : ringChar E ≠ 2 :=
      finite_algebraic_closure_cyclic_prime E K 2 hp1 h_ekrank hgal
    have h_sq : ∀ (a : E), IsSquare a := by
      have h_sq1 : ∀ (a : E), IsSquare a ∨ IsSquare (-a) :=
        quadratic_algebraic_closure_no_i E K h_ekrank
      intro a
      cases h_sq1 a with
      | inl ha =>
        exact even_ofMul_iff.mp ha
      | inr ha =>
        unfold IsSquare at ha
        obtain ⟨r, ha⟩ := ha
        unfold IsSquare
        obtain ⟨i, hi⟩ := h
        use r * (algebraMap F E) i
        have hj : (algebraMap F E) (i ^ 2) = (algebraMap F E) (-1) :=
          (algebraMap.coe_inj F ↥E).mpr hi
        grind
    have _ : FiniteDimensional E K := finiteDimensional_right E
    have h_sq3 : ∃ (a: E), ¬ IsSquare a :=
      nonsquare_in_quadratic_extension E K h_ekrank h_char2
    simp_all
  exact trivial_absolute_galois_group F K hG

lemma finite_inseparable_algebraic_closure_with_i [IsPurelyInseparable F K]
      (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  let p := ringChar F
  have hp1 : Nat.Prime p ∨ p = 0 :=
    CharP.char_is_prime_or_zero F p
  have hr : Field.finInsepDegree F K = 1 := by
    cases hp1 with
    | inl hp1 =>
      by_contra
      push Not at this
      let h_insep := this
      have h_E : ∃ (E : IntermediateField F K), finrank E K = ringChar F := by
        apply finite_inseparable_extension_intermediate
        have : Field.finSepDegree F K * Field.finInsepDegree F K = finrank F K :=
          Field.finSepDegree_mul_finInsepDegree F K
        have h_sep : Field.finSepDegree F K = 1 := by
          (expose_names;
            exact (isPurelyInseparable_iff_finSepDegree_eq_one F K).mp inst_5)
        have : Field.finInsepDegree F K ≥ 1 := by exact NeZero.one_le
        have : Field.finInsepDegree F K > 1 :=
          Nat.lt_of_le_of_ne this (id h_insep.symm)
        grind
      obtain ⟨E, h_E⟩ := h_E
      have : IsAlgClosure E K :=
        { isAlgClosed := IsAlgClosure.isAlgClosed F,
          isAlgebraic := isAlgebraic_tower_top }
      have h_charE : ringChar E = ringChar F := (Algebra.ringChar_eq F ↥E).symm
      have : ExpChar E p :=
        have : CharP E p := by
          refine ringChar.of_eq ?_
          calc
            ringChar E = ringChar F := h_charE
            _ = p := by rfl
        have : Fact (Nat.Prime p) := by exact fact_iff.mpr hp1
        expChar_prime E p
      have hx : ∃ x : K, x ∉ (algebraMap E K).range :=
        have h1 : ¬ Function.Surjective (algebraMap E K) := by
          apply finite_extension_degree_one E K
          rw [h_E]
          exact Nat.Prime.one_lt hp1
        not_forall.mp h1
      obtain ⟨x, hx⟩ := hx
      let e := IsPurelyInseparable.elemExponent E x
      let pol := minpoly E x
      let z := IsPurelyInseparable.elemReduct E x
      have hpol: pol = Polynomial.X ^ p ^ e - Polynomial.C z :=
        IsPurelyInseparable.minpoly_eq' E p x
      have hpoldeg : pol.natDegree ≤ finrank E K := minpoly.natDegree_le x
      have he1: e = 1 := by
        have hpe : p^e = pol.natDegree :=
          (IsPurelyInseparable.minpoly_natDegree_eq' (↥E) p x).symm
        have hpol1 : ¬ pol.natDegree = 1 := minpoly.natDegree_eq_one_iff.mp.mt hx
        have hp2 : p > 1 := Nat.Prime.one_lt hp1
        have he1b : e ≠ 0 := by
          by_contra
          have : pol.natDegree = 1 := by
            calc
            pol.natDegree = p ^ e := hpe.symm
            _ = p ^ 0 := by rw [this]
            _ = 1 := by simp
          grind
        have he1a : e ≤ 1 := by
          have : p ^ e ≤ p := by
            calc
            p^e = pol.natDegree := hpe
            _ ≤ finrank E K := minpoly.natDegree_le x
            _ = p := h_E
          have : 1 < p → 1 < e → p ^ 1 < p^e :=
            pow_lt_pow_right₀
          grind
        grind
      have :
      sorry
    | inr hp1 =>
      have : CharZero F :=
        (CharP.ringChar_zero_iff_CharZero F).mp hp1
      have : ringExpChar F = 1 := ringExpChar.eq_one F
      have hn : ∃ n : ℕ, Field.finInsepDegree F K = 1 ^ n := by
        apply finInsepDegree_eq_pow
      obtain ⟨n, hn⟩ := hn
      grind
  have : Algebra.IsSeparable F K :=
    (isSeparable_iff_finInsepDegree_eq_one F K).mpr hr
  exact finite_separable_algebraic_closure_with_i F K h

  have h_perf: PerfectField F := by
    cases hp1 with
    | inl hp1 =>
      have _ : ExpChar F p := ExpChar.prime hp1
      by_contra

      by_cases p > 2
      · rename_i hpgt2a
        have h_a : ∃ a : F, ¬∃ x : F, x^p = a := by
          have _ : ¬ PerfectRing F p := by
            by_contra
            have _ : ringChar F = ringChar K := Algebra.ringChar_eq F K
            have _ : PerfectField F := PerfectRing.toPerfectField F p
            grind
          have h_inj : Function.Injective (frobenius F p) := frobenius_inj F p
          have h_surj : ¬ Function.Surjective (frobenius F p) := by
            by_contra
            have h_bij : Function.Bijective (frobenius F p) := by
              unfold Function.Bijective
              constructor
              · exact h_inj
              · exact this
            have h_perf : PerfectRing F p := { bijective_frobenius := h_bij }
            (expose_names; exact (iff_false_intro h_2).mp h_perf)
          exact not_forall.mp h_surj
        obtain ⟨a, h_a⟩ := h_a
        have h_n : ∃ n : ℕ, p ^ n > finrank F K := by
          refine pow_unbounded_of_one_lt (finrank F K) ?_
          exact Nat.Prime.one_lt hp1
        obtain ⟨n, h_n⟩ := h_n
        let pol := Polynomial.X ^ p ^ (n + 1) - Polynomial.C a
        have h_pol_irr : Irreducible pol := by
          refine (X_pow_sub_C_irreducible_iff_of_prime_pow hp1 ?_ ?_).mpr ?_
          exact Nat.ne_of_lt' hpgt2a
          exact Ne.symm (Nat.zero_ne_add_one n)
          intro b
          push Not at h_a
          exact h_a b
        have _ : ∀ (b : F), b ^ p ≠ a := by
          refine (X_pow_sub_C_irreducible_iff_of_prime_pow hp1 ?_ ?_).mp h_pol_irr
          simp_all
          exact Nat.ne_of_lt' hpgt2a
          exact Ne.symm (Nat.zero_ne_add_one n)
        have h_poldeg : pol.natDegree = p ^ (n+1) := Polynomial.natDegree_X_pow_sub_C
        have hn : 0 < p ^ (n+1) := expChar_pow_pos F p (n + 1)
        have hn1 : p ^ (n+1) ≠ 0 := by
          grind
        have _ : pol.Monic := by
          have _ : (Polynomial.X ^ p ^ (n + 1) + Polynomial.C (-a)).Monic :=
            Polynomial.monic_X_pow_add_C (-a) hn1
          grind
        have _ : pol.natDegree ≤ finrank F K := by
          have hy : ∃ y : K, Polynomial.aeval y pol = 0 := by
            have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
            apply IsAlgClosed.exists_aeval_eq_zero K pol
            have _ : pol.degree = p ^ (n+1) ↔ pol.natDegree = p ^ (n+1) :=
              Polynomial.degree_eq_iff_natDegree_eq_of_pos hn
            simp_all
          obtain ⟨y, hy⟩ := hy
          let f := minpoly F y
          have h_int : IsIntegral F y := Algebra.IsIntegral.isIntegral y
          have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree := by
            have h_div : f ∣ pol := minpoly.dvd_iff.mpr hy
            refine divisor_of_irreducible_poly f pol h_div ?_
            subst pol
            apply h_pol_irr
          cases h_deg with
          | inl =>
            have h_f : f.natDegree > 0 := minpoly.natDegree_pos h_int
            simp_all
          | inr h_deg =>
            calc
              pol.natDegree = f.natDegree := h_deg.symm
              _ ≤ finrank F K := minpoly.natDegree_le y
        have _ : p ^ (n + 1) > p^n := by
          refine Nat.pow_lt_pow_of_lt ?_ ?_
          exact Nat.Prime.one_lt hp1
          exact lt_add_one n
        grind

      · rename_i h1
        have _ : finrank F K ≤ 1 := by
          by_contra
          push Not at this
          have h_E : ∃ (E : IntermediateField F K), finrank E K = ringChar F := by
            apply finite_inseparable_extension_intermediate
            apply this
          obtain ⟨E, h_E⟩ := h_E
          have _ : IsAlgClosure E K :=
            { isAlgClosed := IsAlgClosure.isAlgClosed F,
              isAlgebraic := isAlgebraic_tower_top }
          have h_charE : ringChar E = ringChar F := (Algebra.ringChar_eq F ↥E).symm
          have _ : ExpChar E p :=
            have _ : CharP E p := by
              refine ringChar.of_eq ?_
              calc
                ringChar E = ringChar F := h_charE
                _ = p := by rfl
            have : Fact (Nat.Prime p) := by exact fact_iff.mpr hp1
            expChar_prime E p
          have hp2 : p = 2 := by
              push Not at h1
              refine (Nat.le_antisymm ?_ h1).symm
              exact Nat.Prime.two_le hp1
          have h_frobsurj : Function.Surjective (frobenius E p) := by
            unfold Function.Surjective
            intro b
            have h_sq : ∀ (a : E), IsSquare a := by
              intro a
              have h_E1 : finrank E K = 2 := by
                calc
                  finrank E K = ringChar F := h_E
                  _ = 2 := hp2
              have h_sq1 : ∀ (a b : ↥E), IsSquare (a ^ 2 + b) ∨ IsSquare (-b) :=
                quadratic_algebraic_closure E K h_E1
              specialize h_sq1 0 a
              cases h_sq1
              · have _ : 0^2 = 0 := (Nat.eq_of_beq_eq_true rfl).symm
                simp_all
              · have h_minus1 : (-1 : E) = (1 : E) := by
                  refine neg_one_eq_one_iff.mpr ?_
                  simp_all
                have _ : (-1 : E) * a = (1 : E) * a := by
                  rw [h_minus1]
                have _ : -a = a := by
                  grind
                simp_all
            specialize h_sq b
            unfold IsSquare at h_sq
            obtain ⟨r, h_sq⟩ := h_sq
            use r
            unfold frobenius
            simp
            rw [hp2]
            grind
          have _ : PerfectField E := by
            have _ : ExpChar (↥E) p := expChar E p
            have _ : PerfectRing E p :=
              PerfectRing.ofSurjective E p h_frobsurj
            exact PerfectRing.toPerfectField E p
          have h1 : Field.finSepDegree E K = 1 :=
            have h_insep : IsPurelyInseparable E K :=
              isPurelyInseparable_tower_top F K E
            (isPurelyInseparable_iff_finSepDegree_eq_one (↥E) K).mp h_insep
          have h2 : Field.finInsepDegree E K = 1 :=
            have h_sep : Algebra.IsSeparable E K :=
              Algebra.IsAlgebraic.isSeparable_of_perfectField
            (isSeparable_iff_finInsepDegree_eq_one (↥E) K).mp h_sep
          have h_E1 : finrank E K = 1 := by
            calc
              finrank E K = Field.finSepDegree E K * Field.finInsepDegree E K :=
                (Field.finSepDegree_mul_finInsepDegree E K).symm
              _ = 1 * 1 := by rw [h1, h2]
              _ = 1 := by simp
          grind
        have _ : Field.finSepDegree F K * Field.finInsepDegree F K = 1 := by
          calc
          Field.finSepDegree F K * Field.finInsepDegree F K  = finrank F K :=
            Field.finSepDegree_mul_finInsepDegree F K
          _ = 1 := by
            (expose_names; refine Eq.symm (Nat.le_antisymm ?_ h_2))
            refine Nat.one_le_iff_ne_zero.mpr ?_
            refine Nat.ne_zero_iff_zero_lt.mpr ?_
            apply finrank_pos
        have h_insep1 : Field.finInsepDegree F K = 1 := by
          simp_all
        have _ :  Algebra.IsSeparable F K :=
          (isSeparable_iff_finInsepDegree_eq_one F K).mpr h_insep1
        have _ : IsAlgClosed F :=
          finite_separable_algebraic_closure_with_i F K h
        have _ : PerfectField F := IsAlgClosed.perfectField F
        grind

    | inr hp1 =>
      have _: CharZero F :=
        (CharP.ringChar_zero_iff_CharZero F).mp hp1
      have _: ringExpChar F = 1 := ringExpChar.eq_one F
      exact PerfectField.ofCharZero

  have _ : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact finite_separable_algebraic_closure_with_i F K h

lemma finite_algebraic_closure_with_i (F : Type) (K : Type) [Field F] [Field K]
  [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  obtain ⟨i, hi⟩ := h
  let E := separableClosure F K
  have _ : IsPurelyInseparable E K := separableClosure.isPurelyInseparable F K
  have _ : IsAlgClosure E K :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F,
      isAlgebraic := IntermediateField.isAlgebraic_tower_top }
  have _ : IsAlgClosed E := by
    apply finite_inseparable_algebraic_closure_with_i E K
    use (algebraMap F E) i
    have : (algebraMap F E) (i^2) = (algebraMap F E) (-1) := by
      grind
    grind
  have _ : IsAlgClosure F E :=
    { isAlgClosed := IsSepClosed.isAlgClosed_of_perfectField ↥E,
      isAlgebraic :=  separableClosure.isAlgebraic F K }
  apply finite_separable_algebraic_closure_with_i F E
  use i
