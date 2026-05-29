module

public import Mathlib.Algebra.CharP.Defs
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
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Relrank
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField
open Module

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
    (hp: Nat.Prime p) (hrank: finrank F K = p) (hgal: IsGalois F K): p = 2 := by
  have h_char : ¬ ringChar F = p :=
    finite_algebraic_closure_cyclic_prime F K p hp hrank hgal
  have hK : (primitiveRoots (finrank F K) F).Nonempty := by
    let cyclo := Polynomial.cyclotomic p F
    have : cyclo.degree = p.totient := Polynomial.degree_cyclotomic p F
    have : p.totient = p - 1 := Nat.totient_prime hp
    have h_cycloroot : ∃ y : K, Polynomial.aeval y cyclo = 0 := by
      have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      refine IsAlgClosed.exists_aeval_eq_zero K cyclo ?_
      aesop
    obtain ⟨y, h_cycloroot⟩ := h_cycloroot
    let f := minpoly F y
    have h_divcyclo : f ∣ cyclo := minpoly.dvd_iff.mpr h_cycloroot
    have _ : f.natDegree ≤ cyclo.natDegree := by
      refine Polynomial.natDegree_le_of_dvd h_divcyclo ?_
      exact Polynomial.cyclotomic_ne_zero p F
    have hf1 : f.natDegree ∣ p := by
      rw [←hrank]
      refine minpoly.degree_dvd ?_
      exact Algebra.IsIntegral.isIntegral y
    have _ : f.natDegree = 1 := by
      have hfd : f.natDegree = 1 ∨ f.natDegree = p :=
        Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree hf1
      cases hfd with
      | inl hfd => exact hfd
      | inr hfd =>
        exfalso
        simp_all only [dvd_refl]
        have _ : cyclo.natDegree = p - 1 := by
          (expose_names; exact Polynomial.natDegree_eq_of_degree_eq_some this_1)
        have _ : p > 0 := Nat.Prime.pos hp
        grind
    have hz : ∃ z : F, f.IsRoot z := by
      refine Polynomial.exists_root_of_degree_eq_one ?_
      have _ : f.degree = f.natDegree := by
        refine Polynomial.degree_eq_natDegree ?_
        exact minpoly.ne_zero_of_finite F y
      simp_all
    obtain ⟨z, hz⟩ := hz
    have hprim : IsPrimitiveRoot z p :=
      have hnz : NeZero (p: F) :=
        have h1 : (p : F) = 0 → CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr
        have h2 : ¬CharP F p := by
          by_contra
          have _ : ringChar F = p := ringChar.eq F p
          simp_all
        { out := h1.mt h2 }
      have h_cycloroot : cyclo.IsRoot z := Polynomial.IsRoot.dvd hz h_divcyclo
      Polynomial.isRoot_cyclotomic_iff.mp h_cycloroot
    refine Finset.nonempty_def.mpr ?_
    use z
    refine (mem_primitiveRoots finrank_pos).mpr ?_
    · subst p
      exact hprim
  let G := Gal(K/F)
  have h_ord : Nat.card G = p := by
    calc
      Nat.card G = finrank F K := IsGalois.card_aut_eq_finrank F K
      _ = p := hrank
  have h_cyc : IsCyclic G :=
    have _ : Fact p.Prime := fact_iff.mpr hp
    isCyclic_of_prime_card h_ord
  by_contra
  have h1 : ∃ (a : F), Irreducible (Polynomial.X ^ finrank F K - Polynomial.C a)
      ∧ Polynomial.IsSplittingField F K (Polynomial.X ^ finrank F K - Polynomial.C a) := by
    apply (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    constructor
    · exact hgal
    · exact h_cyc
  obtain ⟨a, h4, h5⟩ := h1
  have h_irr: ∀ (n : ℕ), n ≠ 0 → (Irreducible (Polynomial.X ^ p ^ n - Polynomial.C a) ↔ ∀ (b : F), b ^ p ≠ a) := by
    intro n hn
    apply X_pow_sub_C_irreducible_iff_of_prime_pow hp
    · push Not at this
      exact this
    · exact hn
  let pol := Polynomial.X ^ p ^ 2 - Polynomial.C a
  have h13 : pol.natDegree = p^2 := Polynomial.natDegree_X_pow_sub_C
  have hc : ∃ c : K, Polynomial.aeval c pol = 0 := by
    have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ pol ?_
    · exact FaithfulSMul.algebraMap_injective F K
    · simp_all
      have h : pol.degree > 0 := by
        refine Polynomial.natDegree_pos_iff_degree_pos.mp ?_
        rw [h13]
        exact Nat.pow_pos (Nat.Prime.pos hp)
      exact ne_of_gt h
  obtain ⟨c, hc⟩ := hc
  let f := minpoly F c
  have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree :=
    have h_div : f ∣ pol := minpoly.dvd_iff.mpr hc
    have h10 : Irreducible pol := by
      have h6 : ∀ (b : F), b ^ p ≠ a :=
        have h7 : 1 ≠ 0 := Nat.one_ne_zero
        have h9 : Irreducible (Polynomial.X ^ p ^ 1 - Polynomial.C a) := by simp_all
        (h_irr 1 h7).mp h9
      have h11 : 2 ≠ 0 := Ne.symm (Nat.zero_ne_add_one 1)
      exact (h_irr 2 h11).mpr h6
    divisor_of_irreducible_poly f pol h_div h10
  cases h_deg
  · have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
    have h_f : f.natDegree > 0 := minpoly.natDegree_pos h_int
    simp_all
  · have _ : f.natDegree ≤ finrank F K := minpoly.natDegree_le c
    simp_all only [Nat.card_eq_fintype_card]
    rename_i hp2
    have h : p < p := by
      calc
        p < p * p := Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hp)
        _ = p^2 := by ring
        _ ≤ p := hp2
    exact (lt_self_iff_false p).mp h

lemma finite_separable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] [IsAlgClosure F K]
      (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  have _ : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_4, to_normal := IsAlgClosure.normal F K })
  let G := Gal(K/F)
  have hG : Nat.card G = 1 := by
    by_contra
    let d := Nat.card G
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp1a⟩ := hp
    have : Fact (Nat.Prime p) := fact_iff.mpr hp1
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
    have : IsAlgClosure E K :=
      { isAlgClosed := IsAlgClosure.isAlgClosed F,
        isAlgebraic := IntermediateField.isAlgebraic_tower_top }
    have hgal: IsGalois E K := IsGalois.tower_top_intermediateField E
    have hp_is2 : p = 2 :=
      finite_algebraic_closure_cyclic_quadratic E K p hp1 h_ekrank hgal
    rw [hp_is2] at hp1
    rw [hp_is2] at h_ekrank
    have : ∃ (a: E), ¬ IsSquare a :=
      have h_char2 : ringChar E ≠ 2 :=
        finite_algebraic_closure_cyclic_prime E K 2 hp1 h_ekrank hgal
      nonsquare_in_quadratic_extension E K h_ekrank h_char2
    have : ∀ (a : E), IsSquare a := by
      have h_sq1 : ∀ (a : E), IsSquare a ∨ IsSquare (-a) :=
        quadratic_algebraic_closure_no_i E K h_ekrank
      intro a
      cases h_sq1 a with
      | inl ha =>
        exact even_ofMul_iff.mp ha
      | inr ha =>
        refine (isSquare_iff_exists_mul_self a).mpr ?_
        unfold IsSquare at ha
        obtain ⟨r, ha⟩ := ha
        obtain ⟨i, hi⟩ := h
        use r * (algebraMap F E) i
        have hj : (algebraMap F E) (i ^ 2) = (algebraMap F E) (-1) :=
          (algebraMap.coe_inj F ↥E).mpr hi
        grind
    simp_all only [ not_true_eq_false, exists_const]
  exact trivial_absolute_galois_group F K hG

lemma finite_inseparable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] [IsAlgClosure F K]
      (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  let p := ringChar F
  have hp1 : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
  have h_perf: PerfectField F := by
    cases hp1 with
    | inl hp1 =>
      have _ : ExpChar F p := ExpChar.prime hp1
      by_cases p > 2
      · by_contra
        rename_i hpgt2a
        have h_a : ∃ a : F, ¬∃ x : F, x^p = a := by
          have h_Fperf : ¬ PerfectRing F p := by
            by_contra
            have _ : ringChar F = ringChar K := Algebra.ringChar_eq F K
            have _ : PerfectField F := PerfectRing.toPerfectField F p
            grind
          have h_inj : Function.Injective (frobenius F p) := frobenius_inj F p
          have h_surj : ¬ Function.Surjective (frobenius F p) := by
            by_contra
            have h_bij : Function.Bijective (frobenius F p) := by
              unfold Function.Bijective
              exact ⟨h_inj, this⟩
            have h_perf : PerfectRing F p := { bijective_frobenius := h_bij }
            exact (iff_false_intro h_Fperf).mp h_perf
          exact not_forall.mp h_surj
        obtain ⟨a, h_a⟩ := h_a
        have h_n : ∃ n : ℕ, p ^ n > finrank F K := by
          refine pow_unbounded_of_one_lt (finrank F K) ?_
          exact Nat.Prime.one_lt hp1
        obtain ⟨n, h_n⟩ := h_n
        let pol := Polynomial.X ^ p ^ (n + 1) - Polynomial.C a
        have h_pol_irr : Irreducible pol := by
          refine (X_pow_sub_C_irreducible_iff_of_prime_pow hp1 ?_ ?_).mpr ?_
          · exact Nat.ne_of_lt' hpgt2a
          · exact Ne.symm (Nat.zero_ne_add_one n)
          · push Not at h_a
            exact h_a
        have h_poldeg : pol.natDegree = p ^ (n+1) := Polynomial.natDegree_X_pow_sub_C
        have : pol.natDegree ≤ finrank F K := by
          have hn : 0 < p ^ (n+1) := expChar_pow_pos F p (n + 1)
          have hn1 : p ^ (n+1) ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hn
          have hy : ∃ y : K, Polynomial.aeval y pol = 0 := by
            have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
            apply IsAlgClosed.exists_aeval_eq_zero K pol
            have : pol.degree = p ^ (n+1) :=
              (Polynomial.degree_eq_iff_natDegree_eq_of_pos hn).mpr h_poldeg
            simp_all only [gt_iff_lt, ne_eq, not_false_eq_true,
              Nat.add_eq_zero_iff, one_ne_zero, and_false, pow_eq_zero_iff, Nat.cast_eq_zero]
          obtain ⟨y, hy⟩ := hy
          let f := minpoly F y
          have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree := by
            have h_div : f ∣ pol := minpoly.dvd_iff.mpr hy
            refine divisor_of_irreducible_poly f pol h_div ?_
            subst pol
            apply h_pol_irr
          cases h_deg with
          | inl =>
            have h_int : IsIntegral F y := Algebra.IsIntegral.isIntegral y
            have : f.natDegree > 0 := minpoly.natDegree_pos h_int
            simp_all
          | inr h_deg =>
            calc
              pol.natDegree = f.natDegree := h_deg.symm
              _ ≤ finrank F K := minpoly.natDegree_le y
        have : p ^ (n + 1) > p^n := by
          refine Nat.pow_lt_pow_of_lt ?_ ?_
          exact Nat.Prime.one_lt hp1
          exact lt_add_one n
        grind
      · rename_i h1
        have h_rank : finrank F K ≤ 1 := by
          by_contra
          push Not at this
          have h_E : ∃ (E : IntermediateField F K), finrank E K = ringChar F := by
            apply finite_inseparable_extension_intermediate
            apply this
          obtain ⟨E, h_E⟩ := h_E
          have h_charE : ringChar E = ringChar F := (Algebra.ringChar_eq F ↥E).symm
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
                have : IsAlgClosure E K :=
                  { isAlgClosed := IsAlgClosure.isAlgClosed F,
                    isAlgebraic := isAlgebraic_tower_top }
                quadratic_algebraic_closure E K h_E1
              specialize h_sq1 0 a
              cases h_sq1
              · have : 0^2 = 0 := (Nat.eq_of_beq_eq_true rfl).symm
                simp_all
              · have h_minus1 : (-1 : E) = (1 : E) := by
                  refine neg_one_eq_one_iff.mpr ?_
                  simp_all
                have : (-1 : E) * a = (1 : E) * a := by rw [h_minus1]
                have : -a = a := by grind
                simp_all
            specialize h_sq b
            unfold IsSquare at h_sq
            obtain ⟨r, h_sq⟩ := h_sq
            use r
            unfold frobenius
            simp only [RingHom.coe_mk, powMonoidHom_apply]
            rw [hp2]
            grind
          have h_E1 : finrank E K = 1 := by
            have : PerfectField E :=
              have : ExpChar (↥E) p := expChar E p
              have : PerfectRing E p :=
                PerfectRing.ofSurjective E p h_frobsurj
              PerfectRing.toPerfectField E p
            have h1 : Field.finSepDegree E K = 1 :=
              have h_insep : IsPurelyInseparable E K := isPurelyInseparable_tower_top F K E
              (isPurelyInseparable_iff_finSepDegree_eq_one (↥E) K).mp h_insep
            have h2 : Field.finInsepDegree E K = 1 :=
              have h_sep : Algebra.IsSeparable E K :=
                Algebra.IsAlgebraic.isSeparable_of_perfectField
              (isSeparable_iff_finInsepDegree_eq_one (↥E) K).mp h_sep
            calc
              finrank E K = Field.finSepDegree E K * Field.finInsepDegree E K :=
                (Field.finSepDegree_mul_finInsepDegree E K).symm
              _ = 1 * 1 := by rw [h1, h2]
              _ = 1 := by simp
          grind
        have : IsAlgClosed F :=
          have : Field.finSepDegree F K * Field.finInsepDegree F K = 1 := by
            calc
            Field.finSepDegree F K * Field.finInsepDegree F K  = finrank F K :=
              Field.finSepDegree_mul_finInsepDegree F K
            _ = 1 := by
              refine (Nat.le_antisymm ?_ h_rank).symm
              refine Nat.one_le_iff_ne_zero.mpr ?_
              refine Nat.ne_zero_iff_zero_lt.mpr ?_
              apply finrank_pos
          have h_insep1 : Field.finInsepDegree F K = 1 := by simp_all
          have :  Algebra.IsSeparable F K :=
            (isSeparable_iff_finInsepDegree_eq_one F K).mpr h_insep1
          finite_separable_algebraic_closure_with_i F K h
        exact IsAlgClosed.perfectField F

    | inr hp1 =>
      have _: CharZero F :=
        (CharP.ringChar_zero_iff_CharZero F).mp hp1
      have _: ringExpChar F = 1 := ringExpChar.eq_one F
      exact PerfectField.ofCharZero

  have _ : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact finite_separable_algebraic_closure_with_i F K h

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
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
