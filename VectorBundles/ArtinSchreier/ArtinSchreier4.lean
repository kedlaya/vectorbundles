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
  have h_ac := IsAlgClosure.isAlgClosed F (K := K)
  have : Module.finrank F K = 1 := by
    have := isGalois_iff.mpr ⟨inferInstance, IsAlgClosure.normal F K⟩
    rw [←IsGaloisGroup.card_eq_finrank Gal(K/F) F K, Nat.card_eq_fintype_card]
    by_contra
    have ⟨p, hp1, hp1a⟩ := Nat.exists_prime_and_dvd this; have := fact_iff.mpr hp1
    obtain ⟨g, rfl⟩ := exists_prime_orderOf_dvd_card p hp1a
    let H := Subgroup.zpowers g; let E := fixedField H
    have : IsAlgClosure E K := ⟨h_ac, isAlgebraic_tower_top⟩
    have h_ekrank := finrank_fixedField_eq_card H; rw [Nat.card_zpowers] at h_ekrank
    have ⟨_, ⟨_, _, hs⟩⟩ := finite_algebraic_closure_cyclic_quadratic E K hp1 h_ekrank
    have := IsSquare.mul (IsSquare.map (algebraMap F ↥E) h) hs; simp_all
  have h1 := botEquiv F K; rw [bot_eq_top_iff_finrank_eq_one.mpr this] at h1
  exact IsAlgClosed.of_ringEquiv K F (topEquiv.symm.trans h1)

lemma finite_inseparable_algebraic_closure [IsPurelyInseparable F K] : PerfectField F := by
  let p := ringChar F; open Function IsPurelyInseparable in
  rcases CharP.char_is_prime_or_zero F p with hp | hp
  · have := ExpChar.prime hp (R := F); have : Surjective (frobenius F p) := by
      intro b; let iota := algebraMap F K; have ⟨n, hn⟩ := finrank_eq_pow F K p
      have := IsAlgClosure.isAlgClosed F (K := K)
      have ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (iota b) (expChar_pow_pos F p (n + 1))
      let e := elemExponent F x; have : e + (n-e) = n := by
        have := Nat.le_lt_asymm (minpoly.natDegree_le x (K := F))
        rw [minpoly_natDegree_eq' F p, hn] at this
        have := (pow_lt_pow_right₀ (Nat.Prime.one_lt hp)).mt this; grind only
      let c := elemReduct F x; let a := c ^ p ^ (n-e); have := calc
        iota b = (x ^ p ^ n) ^ p := by rw [←hx]; ring
        _ = (x ^ (p ^ e * p ^ (n-e))) ^ p := by grind only
        _ = iota (a ^ p) := by rw [pow_mul, ←algebraMap_elemReduct_eq', map_pow, map_pow]
      exact ⟨a, (Injective.eq_iff (FaithfulSMul.algebraMap_injective F K)).mp this.symm⟩
    have := PerfectRing.ofSurjective F p this; exact PerfectRing.toPerfectField F p
  · have := (CharP.ringChar_zero_iff_CharZero F).mp hp; exact PerfectField.ofCharZero

include K h in
lemma finite_algebraic_closure_with_i : IsAlgClosed F := by
  let E := separableClosure F K
  have : IsAlgClosure E K := ⟨IsAlgClosure.isAlgClosed F, isAlgebraic_tower_top⟩
  have := finite_inseparable_algebraic_closure E K
  have := IsSquare.map (algebraMap F E) h; rw [map_neg, map_one] at this
  have := finite_separable_algebraic_closure_with_i E K this
  have : IsAlgClosure F E := ⟨this, separableClosure.isAlgebraic F K⟩
  exact finite_separable_algebraic_closure_with_i F E h
