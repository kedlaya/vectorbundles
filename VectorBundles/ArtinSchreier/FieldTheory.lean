module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

open Polynomial

lemma artin_schreier_poly {F : Type} [Field F] {p : ℕ} (c : F) (hp : 1 < p) :
  (X ^ p - X - C c).IsMonicOfDegree p := by
  rw [←natDegree_X_add_C c] at hp
  have : X ^ p - (X + C c) = X^p - X - C c := by grind only
  rw [← this]
  exact IsMonicOfDegree.sub (isMonicOfDegree_X_pow F p) hp

lemma cyclic_char_p_as_artin_schreier (F K : Type) [Field F] [Field K] [Algebra F K]
  [IsGalois F K] {p : ℕ} (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
    (hchar: ringChar F = p) : ∃ a : F, ∃ x : K, minpoly F x = X ^ p - X - C a := by
  open Algebra Finset MulAction Subgroup Nat in
  have := Prime.pos hp
  rw [←hrank] at this
  have := FiniteDimensional.of_finrank_pos this
  have := (Algebra.charP_iff F K p).mp (ringChar.of_eq hchar)
  let G := Gal(K/F)
  have h_ord := IsGalois.card_aut_eq_finrank F K
  rw [hrank] at h_ord
  have := fact_iff.mpr hp
  have := isCyclic_of_prime_card h_ord
  obtain ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp this
  have h_ordg := orderOf_eq_card_of_zpowers_eq_top h_gen
  rw [h_ord] at h_ordg
  obtain ⟨y, hy⟩ := Set.mem_range.mp (trace_surjective F K 1)
  let rp := range p
  let z := ∑ i : rp, (g^(i:ℕ)) y * i
  have := calc
    g z = ∑ i : rp, g ((g^(i:ℕ)) y * i) := by apply map_finset_sum
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * i := by
      apply sum_congr rfl
      simp [pow_succ' g]
    _ = ∑ i : rp, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := by grind only
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) - ∑ i : rp, (g^(i+1:ℕ)) y := by apply sum_sub_distrib
    _ = z - ∑ i : rp, (g^(i+1:ℕ)) y := by
      apply sub_left_inj.mpr
      have hp1 : p - 1 + 1 = p := succ_pred_prime hp
      let f := fun (i : ℕ) ↦ (g^i) y * i
      let f1 := fun i ↦ f (i+1)
      have : ∑ i ∈ range (p-1), f1 i + f (p-1+1) = ∑ i ∈ range (p-1), f1 i + f 0 := by simp_all [f]
      rw [←sum_range_succ f1 (p-1), ←sum_range_succ' f (p-1), hp1] at this
      calc
      ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) = ∑ i : rp, f (i+1) := by simp [f]
      _ = ∑ i ∈ rp, f1 i := (sum_subtype rp (fun x ↦ Iff.of_eq rfl) f1).symm
      _ = ∑ i ∈ rp, f i := this
      _ = z := sum_subtype rp (fun x ↦ Iff.of_eq rfl) f
    _ = z - 1 := by
      apply sub_right_inj.mpr
      calc
      ∑ i : rp, (g^(i+1:ℕ)) y = ∑ σ : G, σ y := by
        let f := fun (i : rp) ↦ g ^ (i+1:ℕ)
        have : Function.Bijective f := by open IsOfFinOrder in
          apply (Nat.bijective_iff_surjective_and_card f).mpr
          constructor
          · intro b
            have : DecidableEq G := Classical.typeDecidableEq G
            have := mem_top (g ^ (-1:ℤ) * b)
            rw [←h_gen] at this
            have := (mem_zpowers_iff_mem_range_orderOf (isOfFinOrder_of_finite g)).mp this
            rw [h_ordg, mem_image] at this
            obtain ⟨i, hb1, hb2⟩ := this
            simp_all only [Subtype.exists, f]
            use i, hb1
            simp only [pow_succ' g i, hb2, zpow_neg, zpow_one, mul_inv_cancel_left]
          · rw [card_eq_finsetCard rp, card_range p, ←h_ord]
        apply sum_bijective f this
        · simp only [univ_eq_attach, mem_attach, mem_univ, implies_true]
        · exact fun i _ ↦ rfl
      _ = (algebraMap F K) (trace F K y) := (trace_eq_sum_automorphisms y).symm
      _ = (algebraMap F K) 1 := by rw [hy]
      _ = 1 := algebraMap.coe_one
  let b := z^p - z
  have :=
    have := calc
      g b = g (z^p) - g z := map_sub g (z ^ p) z
      _ = z^p - 1 - (z - 1) := by simp [map_pow, this, sub_pow_char]
      _ = b := by ring
    have := mem_fixedBy_zpowers_iff_mem_fixedBy.mpr (mem_fixedBy.mpr this)
    have : ∀ h : G, h b = b := by
      intro h
      have h1 := (Subgroup.ext_iff.mp h_gen.symm h).mp (mem_top h)
      obtain ⟨n, h3⟩ := mem_zpowers_iff.mp h1
      rw [←h3, ←AlgEquiv.smul_def]
      exact mem_stabilizerSubmonoid_iff.mp (this n)
    (IsGalois.mem_bot_iff_fixed b).mpr this
  obtain ⟨a, ha⟩ := Set.mem_range.mp this
  use a, z
  obtain ⟨h_deg, h_mon⟩ := artin_schreier_poly a (Nat.Prime.one_lt hp)
  have h_eval : aeval z (X ^ p - X - C a) = 0 := by aesop
  have h_int := IsIntegral.isIntegral z (R := F)
  open minpoly in
  have h : (X ^ p - X - C a).natDegree ≤ (minpoly F z).natDegree := by
    have h := degree_dvd h_int
    rw [hrank] at h
    have := (dvd_prime hp).mp h
    by_contra
    have : (minpoly F z).natDegree = 1 := by aesop
    have := natDegree_eq_one_iff.mp this
    have := (IsGalois.mem_range_algebraMap_iff_fixed z).mp this g
    grind only
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic h_int) (dvd_iff.mpr h_eval) h
  simp only [Monic.def.mp h_mon, map_one, one_mul] at this
  exact this.symm
