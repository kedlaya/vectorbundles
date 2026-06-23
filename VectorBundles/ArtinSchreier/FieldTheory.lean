module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

open Polynomial

lemma artin_schreier_poly {F : Type} [Field F] {p : ℕ} (c : F) (hp : 1 < p) :
    (X ^ p - X - C c).IsMonicOfDegree p := by
  rw [←natDegree_X_add_C c] at hp
  have : X ^ p - (X + C c) = X^p - X - C c := by grind only
  rw [←this]; exact IsMonicOfDegree.sub (isMonicOfDegree_X_pow F p) hp

lemma cyclic_char_p_as_artin_schreier (F K : Type) [Field F] [Field K] [Algebra F K]
    [IsGalois F K] {p : ℕ} [CharP F p] (hp: Nat.Prime p) (hrank: Module.finrank F K = p) :
    ∃ a : F, ∃ x : K, minpoly F x = X ^ p - X - C a := by
  open Algebra Finset IsGalois MulAction Subgroup Nat minpoly in
  have := FiniteDimensional.of_finrank_pos (by rw [hrank]; exact Prime.pos hp)
  have := (Algebra.charP_iff F K p).mp ‹CharP F p›
  let G := Gal(K/F); have h_ord := card_aut_eq_finrank F K; rw [hrank] at h_ord
  have := fact_iff.mpr hp; have := isCyclic_of_prime_card h_ord
  have ⟨g, h_gen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp this
  have h_ordg := orderOf_eq_card_of_zpowers_eq_top h_gen; rw [h_ord] at h_ordg
  have ⟨y, hy⟩ := Set.mem_range.mp (trace_surjective F K 1)
  let rp := range p; let z := ∑ i : rp, (g^(i:ℕ)) y * i
  have hz1 := by
    have hp1 : p - 1 + 1 = p := succ_pred_prime hp
    let f := fun (i : ℕ) ↦ (g^i) y * i; let f1 := fun i ↦ f (i+1)
    have : ∑ i ∈ range (p-1), f1 i + f (p-1+1) = ∑ i ∈ range (p-1), f1 i + f 0 := by simp_all [f]
    rw [←sum_range_succ f1 (p-1), ←sum_range_succ' f (p-1), hp1] at this
    calc
    ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) = ∑ i : rp, f (i+1) := by simp [f]
    _ = ∑ i ∈ rp, f1 i := (sum_subtype rp (fun x ↦ Iff.of_eq rfl) f1).symm
    _ = ∑ i ∈ rp, f i := this
    _ = z := sum_subtype rp (fun x ↦ Iff.of_eq rfl) f
  have hz2 : ∑ i : rp, (g^(i+1:ℕ)) y = ∑ σ : G, σ y := by open IsOfFinOrder in
    let f := fun (i : rp) ↦ g ^ (i+1:ℕ)
    refine sum_bijective f ?_ ?_ (fun i _ ↦ rfl)
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨?_, ?_⟩
    · have : DecidableEq G := Classical.typeDecidableEq G
      intro b; have := mem_top (g ^ (-1:ℤ) * b); rw [←h_gen] at this
      have := (mem_zpowers_iff_mem_range_orderOf (isOfFinOrder_of_finite g)).mp this
      rw [h_ordg, mem_image] at this; obtain ⟨i, hb1, hb2⟩ := this
      use ⟨i, hb1⟩; simp only [f, pow_succ' g i, hb2, zpow_neg, zpow_one, mul_inv_cancel_left]
    · rw [card_eq_finsetCard rp, card_range p, ←h_ord]
    · simp only [univ_eq_attach, mem_attach, mem_univ, implies_true]
  have := calc
    g z = ∑ i : rp, g ((g^(i:ℕ)) y * i) := by apply map_finset_sum
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * i := by simp [pow_succ' g]
    _ = ∑ i : rp, ((g^(i+1:ℕ)) y * (i+1) - (g^(i+1:ℕ)) y) := by grind only
    _ = ∑ i : rp, (g^(i+1:ℕ)) y * (i+1) - ∑ i : rp, (g^(i+1:ℕ)) y := by simp
    _ = z - 1 := by rw [hz1, hz2, (trace_eq_sum_automorphisms y).symm, hy]; simp
  let b := z^p - z
  have : b ∈ (⊥ : IntermediateField F K) := by
    apply (mem_bot_iff_fixed b).mpr; intro h
    have ⟨n, h3⟩ := mem_zpowers_iff.mp ((Subgroup.ext_iff.mp h_gen.symm h).mp (mem_top h))
    rw [←h3, ←AlgEquiv.smul_def, ←mem_stabilizerSubmonoid_iff]
    have : g b = b := by rw [map_sub, map_pow, this, sub_pow_char]; simp [b]
    exact mem_fixedBy_zpowers_iff_mem_fixedBy.mpr (mem_fixedBy.mpr this) n
  have ⟨a, ha⟩ := Set.mem_range.mp this
  have ⟨h_deg, h_mon⟩ := artin_schreier_poly a (Prime.one_lt hp)
  have h_eval : aeval z (X ^ p - X - C a) = 0 := by aesop
  have h_int := IsIntegral.isIntegral z (R := F)
  have h : (X ^ p - X - C a).natDegree ≤ (minpoly F z).natDegree := by open minpoly in
    have h := degree_dvd h_int; rw [hrank] at h; have := (dvd_prime hp).mp h
    by_contra
    have := (mem_range_algebraMap_iff_fixed z).mp (natDegree_eq_one_iff.mp (by aesop)) g
    grind only
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic h_int) (dvd_iff.mpr h_eval) h
  exact ⟨a, z, by simp only [Monic.def.mp h_mon, map_one, one_mul] at this; exact this.symm⟩
