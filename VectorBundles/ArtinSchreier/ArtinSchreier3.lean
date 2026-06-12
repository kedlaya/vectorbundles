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

open IntermediateField Module

variable (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] (h : ∃ i : F, -1 = i^2)

include h in
lemma finite_separable_algebraic_closure_with_i [Algebra.IsSeparable F K] : IsAlgClosed F :=
  have : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_5, to_normal := IsAlgClosure.normal F K })
  have h_ac : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  let G := Gal(K/F)
  have : Fintype.card G = 1 := by
    by_contra
    let d := Fintype.card G
    obtain ⟨p, hp1, hp1a⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := Nat.exists_prime_and_dvd this
    have := fact_iff.mpr hp1
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hp1a
    let H := Subgroup.zpowers g
    let E := fixedField H
    have h_ekrank := calc
      finrank E K = Nat.card H := finrank_fixedField_eq_card H
      _ = orderOf g := Nat.card_zpowers g
      _ = p := hg
    have : IsAlgClosure E K := { isAlgClosed := h_ac, isAlgebraic := isAlgebraic_tower_top }
    have : IsGalois E K := IsGalois.tower_top_intermediateField E
    have := finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank
    rw [this] at hp1 h_ekrank
    have : ringChar E ≠ 2 := finite_algebraic_closure_cyclic_prime E K hp1 h_ekrank
    obtain ⟨a, ha⟩ := nonsquare_in_quadratic_extension E K h_ekrank this
    cases (quadratic_algebraic_closure E K h_ekrank 0 a) with
    | inl ha => simp_all only [ne_eq, mul_zero, zero_add]
    | inr ha =>
      have h_sq2 : IsSquare (-1 : E) := by
        have h1 : (algebraMap F E) (-1 : F) = (-1 : E) := by simp
        rw [← h1]
        apply IsSquare.map (algebraMap F ↥E)
        apply (isSquare_iff_exists_sq (-1)).mpr
        obtain ⟨i, hi⟩ := h
        use i
      have : IsSquare (-1 * -a) := IsSquare.mul h_sq2 ha
      simp_all only [mul_neg, neg_mul, one_mul, neg_neg]
  have := calc
    finrank F K = Nat.card G := (IsGaloisGroup.card_eq_finrank G F K).symm
    _ = Fintype.card G := Nat.card_eq_fintype_card
    _ = 1 := this
  have := calc
    algebraicClosure F K = ⊤ := (algebraicClosure.eq_top_iff F K).mpr Algebra.IsIntegral.isAlgebraic
    _ = ⊥ := (bot_eq_top_iff_finrank_eq_one.mpr this).symm
  (IsAlgClosed.algebraicClosure_eq_bot_iff F K).mp this

include h in
lemma finite_inseparable_algebraic_closure_with_i [IsPurelyInseparable F K] : IsAlgClosed F :=
  open IsPurelyInseparable in
  have h_perf: PerfectField F := by
    let p := ringChar F
    have hp1 := CharP.char_is_prime_or_zero F p
    cases hp1 with
    | inl hp1 =>
      have : ExpChar F p := ExpChar.prime hp1
      have h_frobsurj : Function.Surjective (frobenius F p) := by
        intro b
        let iota := algebraMap F K
        obtain ⟨n, hn⟩ := finrank_eq_pow F K p
        obtain ⟨x, hx⟩ :=
          have : IsAlgClosed K := IsAlgClosure.isAlgClosed F
          IsAlgClosed.exists_pow_nat_eq (iota b) (expChar_pow_pos F p (n + 1))
        let e := elemExponent F x
        let c := elemReduct F x
        let a := c ^ p ^ (n-e)
        have :=
          have := calc
            p ^ e = (minpoly F x).natDegree := (minpoly_natDegree_eq' F p x).symm
            _ ≤ finrank F K := minpoly.natDegree_le x
            _ = p ^ n := hn
          have : ¬ (e > n) :=
            (pow_lt_pow_right₀ (Nat.Prime.one_lt hp1)).mt (Nat.le_lt_asymm this)
          have h : e + (n-e) = n := by grind only
          calc
          x ^ p ^ n = x ^ p ^ (e + (n-e)) := by rw [h]
          _ = x ^ (p ^ e * p ^ (n-e)) := by grind only
          _ = (x ^ p ^ e) ^ (p ^ (n-e)) := pow_mul x (p ^ e) (p ^ (n - e))
          _ = (iota c) ^ (p ^ (n-e)) := by rw [← algebraMap_elemReduct_eq' F p x]
          _ = iota a := by grind only [= map_pow]
        have := calc
          iota (a ^ p) = iota a ^ p := by simp_all only [map_pow]
          _ = (x ^ p ^ n) ^ p := by simp [this]
          _ = x ^ (p ^ n * p) := by ring
          _ = x ^ p ^ (n + 1) := by grind only
          _ = iota b := hx
        have :=
          have h1 := FaithfulSMul.algebraMap_injective F K
          (Function.Injective.eq_iff h1).mp this
        use a
        simp_all only [frobenius, RingHom.coe_mk, powMonoidHom_apply]
      have := PerfectRing.ofSurjective F p h_frobsurj
      exact PerfectRing.toPerfectField F p
    | inr hp1 =>
      have := (CharP.ringChar_zero_iff_CharZero F).mp hp1
      exact PerfectField.ofCharZero
  have : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  finite_separable_algebraic_closure_with_i F K h

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
    have : iota (i^2) = iota (-1) := by grind only
    grind only [= map_pow, = map_neg, = map_one]
  have : IsAlgClosure F E :=
    { isAlgClosed := IsSepClosed.isAlgClosed_of_perfectField ↥E,
      isAlgebraic := separableClosure.isAlgebraic F K }
  apply finite_separable_algebraic_closure_with_i F E
  use i
