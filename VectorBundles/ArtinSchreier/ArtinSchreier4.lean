module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import VectorBundles.ArtinSchreier.ArtinSchreier3

@[expose] public section

open IntermediateField

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] (h : IsSquare (-1 : F))

include h in
lemma finite_separable_algebraic_closure_with_i [Algebra.IsSeparable F K] : IsAlgClosed F := by
  have : IsGalois F K := { to_isSeparable := inferInstance, to_normal := IsAlgClosure.normal F K }
  have h_ac := IsAlgClosure.isAlgClosed F (K := K)
  let G := Gal(K/F)
  have : Fintype.card G = 1 := by
    by_contra
    have ⟨p, hp1, hp1a⟩ := Nat.exists_prime_and_dvd this; have := fact_iff.mpr hp1
    have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hp1a
    let E := fixedField (Subgroup.zpowers g)
    have h_ekrank := finrank_fixedField_eq_card (Subgroup.zpowers g)
    rw [Nat.card_zpowers g, hg] at h_ekrank
    have h1E : IsSquare (-1 : E) := by grind [IsSquare.map (algebraMap F ↥E) h]
    have : IsAlgClosure E K := { isAlgClosed := h_ac, isAlgebraic := isAlgebraic_tower_top }
    have ⟨hq1, ⟨a, ha⟩⟩ := finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank
    rw [hq1] at hp1 h_ekrank
    cases (quadratic_algebraic_closure E K h_ekrank 0 a) with
    | inl ha => simp_all only [mul_zero, zero_add]
    | inr ha => have := IsSquare.mul h1E ha; simp_all only [mul_neg, neg_mul, one_mul, neg_neg]
  rw [←Nat.card_eq_fintype_card, IsGaloisGroup.card_eq_finrank G F K] at this
  have := (bot_eq_top_iff_finrank_eq_one.mpr this).symm
  rw [←(algebraicClosure.eq_top_iff F K).mpr Algebra.IsIntegral.isAlgebraic] at this
  exact (IsAlgClosed.algebraicClosure_eq_bot_iff F K).mp this

include h in
lemma finite_inseparable_algebraic_closure_with_i [IsPurelyInseparable F K] : IsAlgClosed F :=
  open Function IsPurelyInseparable Module in
  have h_perf : PerfectField F := by
    let p := ringChar F
    cases CharP.char_is_prime_or_zero F p with
    | inl hp1 =>
      have := ExpChar.prime hp1 (R := F)
      have : Surjective (frobenius F p) := by
        intro b; let iota := algebraMap F K
        have ⟨n, hn⟩ := finrank_eq_pow F K p
        have := IsAlgClosure.isAlgClosed F (K := K)
        have ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (iota b) (expChar_pow_pos F p (n + 1))
        have := Nat.le_lt_asymm (minpoly.natDegree_le x (K := F))
        rw [minpoly_natDegree_eq' F p x, hn] at this
        let e := elemExponent F x
        have : ¬ (e > n) := (pow_lt_pow_right₀ (Nat.Prime.one_lt hp1)).mt this
        have h : e + (n-e) = n := by grind only
        let c := elemReduct F x; let a := c ^ p ^ (n-e)
        have := calc
          iota b = x ^ (p ^ n * p) := hx.symm
          _ = (x ^ p ^ n) ^ p := by ring
          _ = (x ^ (p ^ e * p ^ (n-e))) ^ p := by grind only
          _ = ((x ^ p ^ e) ^ (p ^ (n-e))) ^ p := by rw [pow_mul]
          _ = iota (a ^ p) := by rw [←algebraMap_elemReduct_eq' F p x, map_pow, map_pow]
        exact ⟨a, (Injective.eq_iff (FaithfulSMul.algebraMap_injective F K)).mp this.symm⟩
      have := PerfectRing.ofSurjective F p this
      exact PerfectRing.toPerfectField F p
    | inr hp1 =>
      have := (CharP.ringChar_zero_iff_CharZero F).mp hp1
      exact PerfectField.ofCharZero
  have : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  finite_separable_algebraic_closure_with_i F K h

include K h in
lemma finite_algebraic_closure_with_i : IsAlgClosed F := by
  let E := separableClosure F K; have : IsAlgClosure E K :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F, isAlgebraic := isAlgebraic_tower_top }
  have := IsSquare.map (algebraMap F E) h; rw [map_neg, map_one] at this
  have : IsAlgClosure F E :=
    { isAlgClosed := finite_inseparable_algebraic_closure_with_i E K this,
      isAlgebraic := separableClosure.isAlgebraic F K }
  exact finite_separable_algebraic_closure_with_i F E h
