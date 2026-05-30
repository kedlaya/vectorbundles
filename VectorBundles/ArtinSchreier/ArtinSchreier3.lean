module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Relrank
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField
open Module
open Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K]

lemma finite_algebraic_closure_cyclic_quadratic {p : ℕ} (hp: Nat.Prime p)
  (hrank: finrank F K = p) (hgal: IsGalois F K): p = 2 := by
  have h_char : ¬ ringChar F = p :=
    finite_algebraic_closure_cyclic_prime F K p hp hrank hgal
  have hK : (primitiveRoots (finrank F K) F).Nonempty := by
    let cyclo := cyclotomic p F
    have : cyclo.degree = p.totient := degree_cyclotomic p F
    have h_cycloroot : ∃ y : K, aeval y cyclo = 0 := by
      have _ : IsAlgClosed K := IsAlgClosure.isAlgClosed F
      refine IsAlgClosed.exists_aeval_eq_zero K cyclo ?_
      aesop
    obtain ⟨y, h_cycloroot⟩ := h_cycloroot
    let f := minpoly F y
    have h_divcyclo : f ∣ cyclo := minpoly.dvd_iff.mpr h_cycloroot
    have : f.natDegree = 1 := by
      have : f.natDegree ≤ cyclo.natDegree := by
        refine natDegree_le_of_dvd h_divcyclo ?_
        exact cyclotomic_ne_zero p F
      have hf1 : f.natDegree ∣ p := by
        rw [←hrank]
        refine minpoly.degree_dvd ?_
        exact Algebra.IsIntegral.isIntegral y
      have hfd : f.natDegree = 1 ∨ f.natDegree = p :=
        Nat.Prime.eq_one_or_self_of_dvd hp f.natDegree hf1
      cases hfd with
      | inl hfd => exact hfd
      | inr =>
        have : p > 0 := Nat.Prime.pos hp
        have : p.totient = p - 1 := Nat.totient_prime hp
        simp_all only [dvd_refl]
        have : cyclo.natDegree = p - 1 := by
          (expose_names; exact natDegree_eq_of_degree_eq_some this_1)
        grind
    have hz : ∃ z : F, f.IsRoot z := by
      refine exists_root_of_degree_eq_one ?_
      have : f.degree = f.natDegree := by
        refine degree_eq_natDegree ?_
        exact minpoly.ne_zero_of_finite F y
      simp_all
    obtain ⟨z, hz⟩ := hz
    have hprim : IsPrimitiveRoot z p :=
      have hnz : NeZero (p: F) :=
        have h2 : ¬CharP F p := by
          by_contra
          have : ringChar F = p := ringChar.eq F p
          simp_all
        have h1 : (p : F) = 0 → CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr
        { out := h1.mt h2 }
      have h_cycloroot : cyclo.IsRoot z := IsRoot.dvd hz h_divcyclo
      isRoot_cyclotomic_iff.mp h_cycloroot
    refine Finset.nonempty_def.mpr ?_
    use z
    subst p
    exact (mem_primitiveRoots finrank_pos).mpr hprim
  let G := Gal(K/F)
  have h_cyc : IsCyclic G :=
    have h_ord : Nat.card G = p := by
      calc
        Nat.card G = finrank F K := IsGalois.card_aut_eq_finrank F K
        _ = p := hrank
    have : Fact p.Prime := fact_iff.mpr hp
    isCyclic_of_prime_card h_ord
  have h1 : ∃ (a : F), Irreducible (X ^ finrank F K - C a)
      ∧ IsSplittingField F K (X ^ finrank F K - C a) := by
    apply (List.TFAE.out (isCyclic_tfae F K hK) 0 1).mp
    exact ⟨hgal, h_cyc⟩
  obtain ⟨a, h4, h5⟩ := h1
  by_contra
  have h_irr: ∀ (n : ℕ), n ≠ 0 → (Irreducible (X ^ p ^ n - C a) ↔ ∀ (b : F), b ^ p ≠ a) := by
    intro n hn
    push Not at this
    exact X_pow_sub_C_irreducible_iff_of_prime_pow hp this hn
  let pol := X ^ p ^ 2 - C a
  have h13 : pol.natDegree = p ^ 2 := natDegree_X_pow_sub_C
  have hc : ∃ c : K, aeval c pol = 0 := by
    have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
    refine IsAlgClosed.exists_aeval_eq_zero_of_injective K ?_ pol ?_
    · exact FaithfulSMul.algebraMap_injective F K
    · have h : pol.degree > 0 := by
        refine natDegree_pos_iff_degree_pos.mp ?_
        rw [h13]
        exact Nat.pow_pos (Nat.Prime.pos hp)
      exact ne_of_gt h
  obtain ⟨c, hc⟩ := hc
  let f := minpoly F c
  have h_deg : f.natDegree = 0 ∨ f.natDegree = pol.natDegree :=
    have h_div : f ∣ pol := minpoly.dvd_iff.mpr hc
    have h10 : Irreducible pol :=
      have h6 : ∀ (b : F), b ^ p ≠ a :=
        have h7 : 1 ≠ 0 := Nat.one_ne_zero
        have h9 : Irreducible (X ^ p ^ 1 - C a) := by simp_all only [pow_one]
        (h_irr 1 h7).mp h9
      have h11 : 2 ≠ 0 := Ne.symm (Nat.zero_ne_add_one 1)
      (h_irr 2 h11).mpr h6
    divisor_of_irreducible_poly h_div h10
  cases h_deg with
  | inl h_deg =>
    have h_int : IsIntegral F c := Algebra.IsIntegral.isIntegral c
    have h : 0 < 0 := by
      calc
        0 < f.natDegree := minpoly.natDegree_pos h_int
        _ = 0 := h_deg
    exact (lt_self_iff_false 0).mp h
  | inr h_deg =>
    have h : p < p := by
      calc
        p < p * p := Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hp)
        _ = p^2 := by ring
        _ = pol.natDegree := h13.symm
        _ = f.natDegree := h_deg.symm
        _ ≤ finrank F K := minpoly.natDegree_le c
        _ = p := hrank
    exact (lt_self_iff_false p).mp h

lemma finite_separable_algebraic_closure_with_i [Algebra.IsSeparable F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  have : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_5, to_normal := IsAlgClosure.normal F K })
  let G := Gal(K/F)
  have hG : Nat.card G = 1 := by
    by_contra
    let d := Nat.card G
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp1a⟩ := hp
    have hg : ∃ g : G, orderOf g = p := by
      have : Fact (Nat.Prime p) := fact_iff.mpr hp1
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
      finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank hgal
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
        let iota := algebraMap F E
        use r * iota i
        have hj : iota (i ^ 2) = iota (-1) :=
          (algebraMap.coe_inj F ↥E).mpr hi
        grind
    simp_all only [ not_true_eq_false, exists_const]
  have h_rank : finrank F K = 1 := by
    calc
    finrank F K = Nat.card Gal(K/F) := (IsGaloisGroup.card_eq_finrank Gal(K/F) F K).symm
    _ = 1 := hG
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  have h : algebraicClosure F K = ⊥ := by
    calc
    algebraicClosure F K = ⊤ := (algebraicClosure.eq_top_iff F K).mpr Algebra.IsIntegral.isAlgebraic
    _ = ⊥ := (IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr h_rank).symm
  exact (IsAlgClosed.algebraicClosure_eq_bot_iff F K).mp h

lemma finite_inseparable_algebraic_closure_with_i [IsPurelyInseparable F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  let p := ringChar F
  have hp1 : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
  have h_perf: Algebra.IsSeparable F K := by
    cases hp1 with
    | inl hp1 =>
      have : ExpChar F p := ExpChar.prime hp1
      have h_rank : finrank F K ≤ 1 := by
        by_contra
        push Not at this
        have h_E : ∃ (E : IntermediateField F K), finrank E K = ringChar F :=
          finite_inseparable_extension_intermediate F K this
        obtain ⟨E, h_E⟩ := h_E
        have h_frobsurj : Function.Surjective (frobenius E p) := by
          intro b
          let iota := algebraMap E K
          have hx : ∃ (x : K), x^(p^2) = iota b := by
            have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
            refine IsAlgClosed.exists_pow_nat_eq (iota b) ?_
            exact expChar_pow_pos F p 2
          obtain ⟨x, hx⟩ := hx
          let e := IsPurelyInseparable.elemExponent E x
          let c := IsPurelyInseparable.elemReduct E x
          let a := c ^ p ^ (1-e)
          have ha : x ^ p = iota a := by
            have : x ^ p ^ e = iota c := (IsPurelyInseparable.algebraMap_elemReduct_eq' E p x).symm
            have : e ≤ 1 := by
              have hp : 1 < p := Nat.Prime.one_lt hp1
              have hp2 : ¬ (p ^ e > p ^ 1) := by
                push Not
                let f := minpoly E x
                calc
                p ^ e = f.natDegree := (IsPurelyInseparable.minpoly_natDegree_eq' E p x).symm
                _ ≤ Module.finrank E K := minpoly.natDegree_le x
                _ = p := h_E
                _ = p ^ 1 := by simp
              have hp3 : ¬ (e > 1) := (pow_lt_pow_right₀ hp).mt hp2
              push Not at hp3
              exact hp3
            have h : e + (1-e) = 1 := Nat.add_sub_of_le this
            calc
            x ^ p = x ^ (p ^ 1) := by simp
            _ = x ^ p ^ (e + (1-e)) := by rw [h]
            _ = x ^ (p ^ e * p ^ (1-e)) := by grind
            _ = (x ^ p ^ e) ^ (p ^ (1-e)) := pow_mul x (p ^ e) (p ^ (1 - e))
            _ = iota a := by grind
          use a
          have : iota a ^ p = iota b := by
            calc
            iota a ^ p = (iota a) ^ p := by simp_all only [p, e, c, a]
            _ = (x ^ p) ^ p := by simp [ha]
            _ = x ^ (p * p) := by ring
            _ = x ^ (p ^ 2) := by grind
            _= iota b := hx
          exact SetLike.coe_eq_coe.mp this
        have : PerfectField E :=
          have : ExpChar (↥E) p := expChar E p
          have : PerfectRing E p := PerfectRing.ofSurjective E p h_frobsurj
          PerfectRing.toPerfectField E p
        have h2 : Field.finInsepDegree E K = 1 :=
          have h_sep : Algebra.IsSeparable E K := Algebra.IsAlgebraic.isSeparable_of_perfectField
          (isSeparable_iff_finInsepDegree_eq_one (↥E) K).mp h_sep
        have h_E1 : finrank E K = 1 := by
          have h1 : Field.finSepDegree E K = 1 :=
            have h_insep : IsPurelyInseparable E K := isPurelyInseparable_tower_top F K E
            (isPurelyInseparable_iff_finSepDegree_eq_one (↥E) K).mp h_insep
          calc
            finrank E K = Field.finSepDegree E K * Field.finInsepDegree E K :=
              (Field.finSepDegree_mul_finInsepDegree E K).symm
            _ = 1 * 1 := by rw [h1, h2]
            _ = 1 := by simp
        have : ringChar F = 1 := by rw [←h_E, h_E1]
        simp_all
      have : Field.finSepDegree F K * Field.finInsepDegree F K = 1 := by
        calc
        Field.finSepDegree F K * Field.finInsepDegree F K = finrank F K :=
          Field.finSepDegree_mul_finInsepDegree F K
        _ = 1 := by
          refine (Nat.le_antisymm ?_ h_rank).symm
          refine Nat.one_le_iff_ne_zero.mpr ?_
          refine Nat.ne_zero_iff_zero_lt.mpr ?_
          apply finrank_pos
      have h_insep1 : Field.finInsepDegree F K = 1 := by simp_all
      exact (isSeparable_iff_finInsepDegree_eq_one F K).mpr h_insep1
    | inr hp1 =>
      have : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hp1
      have : ringExpChar F = 1 := ringExpChar.eq_one F
      have : PerfectField F := PerfectField.ofCharZero
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact finite_separable_algebraic_closure_with_i F K h

include K in
lemma finite_algebraic_closure_with_i (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  obtain ⟨i, hi⟩ := h
  let E := separableClosure F K
  have : IsPurelyInseparable E K := separableClosure.isPurelyInseparable F K
  have : IsAlgClosure E K :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F,
      isAlgebraic := IntermediateField.isAlgebraic_tower_top }
  have : IsAlgClosed E := by
    apply finite_inseparable_algebraic_closure_with_i E K
    let iota := algebraMap F E
    use iota i
    have : iota (i^2) = iota (-1) := by grind
    grind
  have : IsAlgClosure F E :=
    { isAlgClosed := IsSepClosed.isAlgClosed_of_perfectField ↥E,
      isAlgebraic :=  separableClosure.isAlgebraic F K }
  apply finite_separable_algebraic_closure_with_i F E
  use i
