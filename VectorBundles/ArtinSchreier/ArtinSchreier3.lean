module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent

public import VectorBundles.ArtinSchreier.FieldTheory
public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

open IntermediateField IsPurelyInseparable Module Polynomial

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] (h : ∃ i : F, i^2 = -1)

include h in
lemma finite_separable_algebraic_closure_with_i [Algebra.IsSeparable F K] : IsAlgClosed F := by
  have : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_5, to_normal := IsAlgClosure.normal F K })
  have h_ac: IsAlgClosed K := IsAlgClosure.isAlgClosed F
  let G := Gal(K/F)
  have : Fintype.card G = 1 := by
    by_contra
    let d := Fintype.card G
    obtain ⟨p, hp1, hp1a⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    obtain ⟨g, hg⟩ : ∃ g : G, orderOf g = p :=
      have : Fact (Nat.Prime p) := fact_iff.mpr hp1
      exists_prime_orderOf_dvd_card p hp1a
    let H := Subgroup.zpowers g
    let E := fixedField H
    have h_ekrank : finrank E K = p := by calc
      finrank E K = Nat.card H := finrank_fixedField_eq_card H
      _ = orderOf g := Nat.card_zpowers g
      _ = p := hg
    have : IsAlgClosure E K := { isAlgClosed := h_ac, isAlgebraic := isAlgebraic_tower_top }
    have : IsGalois E K := IsGalois.tower_top_intermediateField E
    have hp_is2 : p = 2 := finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank
    rw [hp_is2] at hp1 h_ekrank
    have : ∃ a : E, ¬ IsSquare a :=
      have : ringChar E ≠ 2 := finite_algebraic_closure_cyclic_prime E K hp1 h_ekrank
      nonsquare_in_quadratic_extension E K h_ekrank this
    have : ∀ a : E, IsSquare a := by
      intro a
      have h_sq1 : IsSquare a ∨ IsSquare (-a) := quadratic_algebraic_closure_no_i E K h_ekrank a
      cases h_sq1 with
      | inl ha => exact ha
      | inr ha =>
        have h_sq2 : IsSquare (-1 : E) := by
          have h1 : (algebraMap F E) (-1 : F) = (-1 : E) := by simp
          rw [← h1]
          apply IsSquare.map (algebraMap F ↥E)
          apply (isSquare_iff_exists_sq (-1)).mpr
          obtain ⟨i, hi⟩ := h
          use i
          exact hi.symm
        have : IsSquare (-1 * -a) := IsSquare.mul h_sq2 ha
        simp_all only [neg_mul, one_mul, neg_neg]
    simp_all only [not_true_eq_false, exists_const]
  have : finrank F K = 1 := by calc
    finrank F K = Nat.card G := (IsGaloisGroup.card_eq_finrank G F K).symm
    _ = Fintype.card G := Nat.card_eq_fintype_card
    _ = 1 := this
  have : algebraicClosure F K = ⊥ := by calc
    algebraicClosure F K = ⊤ := (algebraicClosure.eq_top_iff F K).mpr Algebra.IsIntegral.isAlgebraic
    _ = ⊥ := (bot_eq_top_iff_finrank_eq_one.mpr this).symm
  exact (IsAlgClosed.algebraicClosure_eq_bot_iff F K).mp this

include h in
lemma finite_inseparable_algebraic_closure_with_i [IsPurelyInseparable F K] : IsAlgClosed F := by
  have h_perf: PerfectField F := by
    let p := ringChar F
    have hp1 : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
    cases hp1 with
    | inl hp1 =>
      have : ExpChar F p := ExpChar.prime hp1
      have h_frobsurj : Function.Surjective (frobenius F p) := by
        intro b
        let iota := algebraMap F K
        obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow F K p
        obtain ⟨x, hx⟩ : ∃ x : K, x ^ p ^ (n + 1) = iota b := by
          have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
          refine IsAlgClosed.exists_pow_nat_eq (iota b) ?_
          exact expChar_pow_pos F p (n + 1)
        let e := elemExponent F x
        let c := elemReduct F x
        let a := c ^ p ^ (n-e)
        have : x ^ p ^ n = iota a := by
          have hp2 : p ^ e ≤ p ^ n := by
            calc
            p ^ e = (minpoly F x).natDegree := (minpoly_natDegree_eq' F p x).symm
            _ ≤ finrank F K := minpoly.natDegree_le x
            _ = p^n := hn
          have hp3 : ¬ (e > n) := by
            apply (pow_lt_pow_right₀ (Nat.Prime.one_lt hp1)).mt
            push Not
            exact hp2
          have h : e + (n-e) = n := by grind
          calc
          x ^ p ^ n = x ^ p ^ (e + (n-e)) := by rw [h]
          _ = x ^ (p ^ e * p ^ (n-e)) := by grind
          _ = (x ^ p ^ e) ^ (p ^ (n-e)) := pow_mul x (p ^ e) (p ^ (n - e))
          _ = (iota c) ^ (p ^ (n-e)) := by rw [← algebraMap_elemReduct_eq' F p x]
          _ = iota a := by grind
        have : iota (a ^ p) = iota b := by
          calc
          iota (a ^ p) = iota a ^ p := by simp_all only [map_pow]
          _ = (x ^ p ^ n) ^ p := by simp [this]
          _ = x ^ (p ^ n * p) := by ring
          _ = x ^ p ^ (n + 1) := by grind
          _= iota b := hx
        have : a ^ p = b := by
          have h1 : Function.Injective iota := by exact FaithfulSMul.algebraMap_injective F K
          apply (Function.Injective.eq_iff h1).mp this
        use a
        unfold frobenius
        simp_all
      have : PerfectRing F p := PerfectRing.ofSurjective F p h_frobsurj
      exact PerfectRing.toPerfectField F p
    | inr hp1 =>
      have : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hp1
      exact PerfectField.ofCharZero
  have : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
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
