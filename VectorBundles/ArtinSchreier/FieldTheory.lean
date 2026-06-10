module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public import VectorBundles.ArtinSchreier.Polynomials

@[expose] public section

open IntermediateField Module Polynomial

variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

lemma cyclic_char_p_as_artin_schreier [IsGalois F K] {p : ℕ} (hp: Nat.Prime p)
  (hrank: finrank F K = p) (hchar: ringChar F = p) : ∃ a : F,
    ∃ x : K, minpoly F x = X ^ p - X - C a := by
  open minpoly in
  obtain ⟨y, hy⟩ := Set.mem_range.mp (Algebra.trace_surjective F K 1)
  have := (Algebra.charP_iff F K p).mp (ringChar.of_eq hchar)
  let G := Gal(K/F)
  have h_ord := calc
    Nat.card G = finrank F K := IsGalois.card_aut_eq_finrank F K
    _  = p := hrank
  have := fact_iff.mpr hp
  have := isCyclic_of_prime_card h_ord
  obtain ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp this
  have h_ordg := calc
    orderOf g = Nat.card G := orderOf_eq_card_of_zpowers_eq_top h_gen
    _ = p := h_ord
  let range := Finset.range p
  let z := ∑ i : range, (g^(i:ℕ)) y * i
  have : g z = z - 1 := calc
    g z = ∑ i : range, g ((g^(i:ℕ)) y * i) := by apply map_finset_sum
    _ = ∑ i : range, (g * (g^(i:ℕ))) y * i := by
      simp_all only [map_mul, map_natCast, AlgEquiv.mul_apply, G]
    _ = ∑ i : range, (g^(i+1:ℕ)) y * i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ' g ↑i]
    _ = ∑ i : range, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := by grind only
    _ = ∑ i : range, (g^(i+1:ℕ)) y * (i+1) - ∑ i : range, (g^(i+1:ℕ)) y := by
      apply Finset.sum_sub_distrib
    _ = z - ∑ i : range, (g^(i+1:ℕ)) y := by
      apply sub_left_inj.mpr
      have hp1 : p - 1 + 1 = p := Nat.succ_pred_prime hp
      let f (i : ℕ) : K := (g^i) y * i
      let f1 := fun i ↦ f (i+1)
      calc
      ∑ i : range, (g^(i+1:ℕ)) y * (i+1) = ∑ i : range, f (i+1) := by simp [f]
      _ = ∑ i ∈ range, f1 i := (Finset.sum_subtype (range) (fun x ↦ Iff.of_eq rfl) f1).symm
      _ = ∑ i ∈ Finset.range (p-1+1), f1 i := by rw [hp1]
      _ = ∑ i ∈ Finset.range (p-1), f1 i + f (p-1+1) := Finset.sum_range_succ f1 (p-1)
      _ = ∑ i ∈ Finset.range (p-1), f1 i + f 0 := by
        simp_all only [CharP.cast_eq_zero, mul_zero, Nat.cast_zero, f]
      _ = ∑ i ∈ Finset.range (p-1+1), f i := (Finset.sum_range_succ' f (p-1)).symm
      _ = ∑ i ∈ range, f i := by rw [hp1]
      _ = z := Finset.sum_subtype (range) (fun x ↦ Iff.of_eq rfl) f
    _ = z - 1 := by
      apply sub_right_inj.mpr
      calc
      ∑ i : range, (g^(i+1:ℕ)) y = ∑ σ : G, σ y := by
        let f : range → G := fun i ↦ g ^ (i+1:ℕ)
        have h_bij : Function.Bijective f := by
          apply (Nat.bijective_iff_surjective_and_card f).mpr
          constructor
          · intro b
            have : DecidableEq G := Classical.typeDecidableEq G
            have : g ^ (-1:ℤ) * b ∈ Finset.image (fun x ↦ g ^ x) (Finset.range p) := by
              rw [←h_ordg]
              refine (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf ?_).mp ?_
              · exact isOfFinOrder_of_finite g
              · rw [h_gen]
                exact Subgroup.mem_top (g ^ (-1) * b)
            simp_all only [Finset.mem_image, Subtype.exists, f]
            obtain ⟨i, hb1, hb2⟩ := this
            use i, hb1
            simp [pow_succ' g i, hb2]
          · calc
            Nat.card ↥range = Finset.card range := Nat.card_eq_finsetCard range
            _ = p := Finset.card_range p
            _ = Nat.card G := h_ord.symm
        apply Finset.sum_bijective f h_bij
        · simp
        · simp [f]
      _ = (algebraMap F K) (Algebra.trace F K y) := (trace_eq_sum_automorphisms y).symm
      _ = (algebraMap F K) 1 := by rw [hy]
      _ = 1 := algebraMap.coe_one
  let b := z^p - z
  have := open MulAction in
    have := calc
      g b = g (z^p - z) := AlgEquiv.congr_fun rfl b
      _ = g (z^p) - g z := map_sub g (z ^ p) z
      _ = z^p - 1^p - (z - 1) := by rw [map_pow g z p, this, sub_pow_char z 1]
      _ = z^p - 1 - (z - 1) := by simp
      _ = b := sub_sub_sub_cancel_right (z ^ p) z 1
    have := mem_fixedBy.mpr this
    have := mem_fixedBy_zpowers_iff_mem_fixedBy.mpr this
    have : ∀ h : G, h b = b := by
      intro h
      have h1 := (Subgroup.ext_iff.mp h_gen.symm h).mp (Subgroup.mem_top h)
      obtain ⟨n, h3⟩ := Subgroup.mem_zpowers_iff.mp h1
      rw [←h3, ←AlgEquiv.smul_def]
      exact mem_stabilizerSubmonoid_iff.mp (this n)
    (IsGalois.mem_bot_iff_fixed b).mpr this
  obtain ⟨a, ha⟩ := Set.mem_range.mp this
  use a, z
  obtain ⟨_, h_mon⟩ := artin_schreier_poly a hp
  have h_eval : aeval z (X ^ p - X - C a) = 0 := by aesop
  have h_int : IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have := polynomial_monic_divisor (monic h_int) h_mon (dvd_iff.mpr h_eval)
  have : (minpoly F z).natDegree = p := by
    have h : (minpoly F z).natDegree ∣ finrank F K := degree_dvd h_int
    rw [hrank] at h
    have := (Nat.dvd_prime hp).mp h
    by_contra
    have : (minpoly F z).natDegree = 1 := by simp_all only [or_false, ne_eq]
    have := natDegree_eq_one_iff.mp this
    have := (IsGalois.mem_range_algebraMap_iff_fixed z).mp this g
    grind only
  aesop

lemma finite_inseparable_extension_data [IsPurelyInseparable F K] (h: 1 < finrank F K) :
  Nat.Prime (ringChar F) ∧ ∃ n : ℕ, finrank F K = (ringChar F) ^ n := by
  let p := ringChar F
  let q := ringExpChar F
  have : ExpChar F q := ringExpChar.expChar F
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow F K q
  have hpp : Nat.Prime p := by
    have : q ≠ 1 := by
      by_contra
      rw [this] at hn
      grind only
    have h : ¬ p = 0 := (expChar_one_iff_char_zero F p q).mpr.mt this
    have : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
    simp_all only [ne_eq, or_false]
  refine ⟨hpp, ?_⟩
  have : p = q := (char_eq_expChar_iff F p q).mpr hpp
  rw [← this] at hn
  use n

lemma nonsquare_in_quadratic_extension (hrank: finrank F K = 2) (hchar: ringChar F ≠ 2) :
  ∃ a : F, ¬ IsSquare a := by
  have : Algebra.IsSeparable F K :=
    let e := Field.finSepDegree F K
    have : e ≠ 1 := by
      by_contra
      have := (isPurelyInseparable_iff_finSepDegree_eq_one F K).mpr this
      have := finite_inseparable_extension_data F K
      rw [hrank] at this
      obtain ⟨h1, n, h3⟩ := this Nat.one_lt_two
      have := Nat.prime_eq_prime_of_dvd_pow Nat.prime_two h1 h3.dvd
      grind only
    let d := Field.finInsepDegree F K
    have : d = 1 := by
      have := Field.finSepDegree_mul_finInsepDegree F K
      rw [hrank] at this
      have : e ∣ 2 := dvd_of_mul_right_eq d this
      have : e = 1 ∨ e = 2 := (Nat.dvd_prime Nat.prime_two).mp this
      grind only
    (isSeparable_iff_finInsepDegree_eq_one F K).mpr this
  let iota := algebraMap F K
  have prim : (primitiveRoots (finrank F K) F).Nonempty := by
    refine Finset.nonempty_def.mpr ?_
    use -1
    rw [hrank]
    apply (mem_primitiveRoots Nat.two_pos).mpr
    exact IsPrimitiveRoot.neg_one (ringChar F) hchar
  obtain ⟨b, hb1, hb2⟩ :=
    have : Algebra.IsQuadraticExtension F K :=
      { toFree := free_of_finite_type_torsion_free', finrank_eq_two' := hrank }
    have := Algebra.IsQuadraticExtension.isCyclic F K
    exists_root_adjoin_eq_top_of_isCyclic F K prim
  obtain ⟨a, hb1⟩ := hb1
  use a
  by_contra
  obtain ⟨c, this⟩ := this
  rw [hrank] at hb1
  have hb4 : b ∈ iota.range := by
    refine RingHom.mem_range.mpr ?_
    have hb3 : iota c = b ∨ iota (-c) = b := by grind only [= map_mul, = map_neg]
    cases hb3
    · use c
    · use -c
  have : finrank F K = 1 := by
    have h := adjoin_simple_eq_bot_iff.mpr hb4
    rw [h] at hb2
    exact bot_eq_top_iff_finrank_eq_one.mp hb2
  simp_all only [OfNat.one_ne_ofNat]
