module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField IsPurelyInseparable Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] (h : ∃ (i : F), i^2 = -1)

include h in
lemma finite_separable_algebraic_closure_with_i [Algebra.IsSeparable F K] : IsAlgClosed F := by
  have : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_5, to_normal := IsAlgClosure.normal F K })
  have h_ac: IsAlgClosed K := IsAlgClosure.isAlgClosed F
  let G := Gal(K/F)
  have hG : Nat.card G = 1 := by
    by_contra
    let d := Nat.card G
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp1a⟩ := hp
    have hg : ∃ g : G, orderOf g = p := by
      have h : d = Fintype.card G := Nat.card_eq_fintype_card
      rw [h] at hp1a
      have : Fact (Nat.Prime p) := fact_iff.mpr hp1
      exact exists_prime_orderOf_dvd_card p hp1a
    obtain ⟨g, hg⟩ := hg
    let H := Subgroup.zpowers g
    let E := fixedField H
    have h_ekrank : finrank E K = p := by
      calc
        finrank E K = Nat.card H := finrank_fixedField_eq_card H
        _ = orderOf g := Nat.card_zpowers g
        _ = p := hg
    have : IsAlgClosure E K := { isAlgClosed := h_ac, isAlgebraic := isAlgebraic_tower_top }
    have : IsGalois E K := IsGalois.tower_top_intermediateField E
    have hp_is2 : p = 2 := finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank
    rw [hp_is2] at hp1 h_ekrank
    have : ∃ a : E, ¬ IsSquare a :=
      have h_char2 : ringChar E ≠ 2 := finite_algebraic_closure_cyclic_prime E K hp1 h_ekrank
      nonsquare_in_quadratic_extension E K h_ekrank h_char2
    have : ∀ a : E, IsSquare a := by
      intro a
      have h_sq1 : IsSquare a ∨ IsSquare (-a) := quadratic_algebraic_closure_no_i E K h_ekrank a
      cases h_sq1 with
      | inl ha =>
        exact ha
      | inr ha =>
        have h_sq2 : IsSquare (-1 : E) := by
          have h1 : (algebraMap F E) (-1 : F) = (-1 : E) := by simp
          rw [← h1]
          refine IsSquare.map (algebraMap F ↥E) ?_
          refine (isSquare_iff_exists_sq (-1)).mpr ?_
          obtain ⟨i, hi⟩ := h
          use i
          exact hi.symm
        have h_sq3 : IsSquare (-1 * -a) := IsSquare.mul h_sq2 ha
        simp_all only [neg_mul, one_mul, neg_neg]
    simp_all only [not_true_eq_false, exists_const]
  have h_rank : finrank F K = 1 := by
    calc
    finrank F K = Nat.card G := (IsGaloisGroup.card_eq_finrank G F K).symm
    _ = 1 := hG
  have h : algebraicClosure F K = ⊥ := by
    calc
    algebraicClosure F K = ⊤ := (algebraicClosure.eq_top_iff F K).mpr Algebra.IsIntegral.isAlgebraic
    _ = ⊥ := (bot_eq_top_iff_finrank_eq_one.mpr h_rank).symm
  exact (IsAlgClosed.algebraicClosure_eq_bot_iff F K).mp h

include h in
lemma finite_inseparable_algebraic_closure_with_i [IsPurelyInseparable F K] : IsAlgClosed F := by
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
          have hx : ∃ (x : K), x ^ p ^ 2 = iota b := by
            have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
            refine IsAlgClosed.exists_pow_nat_eq (iota b) ?_
            exact expChar_pow_pos F p 2
          obtain ⟨x, hx⟩ := hx
          let e := elemExponent E x
          let c := elemReduct E x
          let a := c ^ p ^ (1-e)
          have ha : x ^ p = iota a := by
            have : x ^ p ^ e = iota c := (algebraMap_elemReduct_eq' E p x).symm
            have : e ≤ 1 := by
              have hp2 : ¬ (p ^ e > p ^ 1) := by
                push Not
                calc
                p ^ e = (minpoly E x).natDegree := (minpoly_natDegree_eq' E p x).symm
                _ ≤ finrank E K := minpoly.natDegree_le x
                _ = p := h_E
                _ = p ^ 1 := by simp
              have hp3 : ¬ (e > 1) := (pow_lt_pow_right₀ (Nat.Prime.one_lt hp1)).mt hp2
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
            _ = x ^ p ^ 2 := by grind
            _= iota b := hx
          exact SetLike.coe_eq_coe.mp this
        have : PerfectField E :=
          have : ExpChar E p := expChar E p
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
        simp_all only [ringChar.ringChar_eq_one, finrank_subsingleton, lt_self_iff_false]
      have : Field.finSepDegree F K * Field.finInsepDegree F K = 1 := by
        calc
        Field.finSepDegree F K * Field.finInsepDegree F K = finrank F K :=
          Field.finSepDegree_mul_finInsepDegree F K
        _ = 1 :=
          have : finrank F K > 0 := finrank_pos
          (Nat.le_antisymm this h_rank).symm
      have h_insep1 : Field.finInsepDegree F K = 1 := by simp_all
      exact (isSeparable_iff_finInsepDegree_eq_one F K).mpr h_insep1
    | inr hp1 =>
      have : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hp1
      have : ringExpChar F = 1 := ringExpChar.eq_one F
      have : PerfectField F := PerfectField.ofCharZero
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact finite_separable_algebraic_closure_with_i F K h

include K h in
lemma finite_algebraic_closure_with_i : IsAlgClosed F := by
  obtain ⟨i, hi⟩ := h
  let E := separableClosure F K
  have : IsPurelyInseparable E K := separableClosure.isPurelyInseparable F K
  have : IsAlgClosure E K :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F,
      isAlgebraic := isAlgebraic_tower_top }
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
